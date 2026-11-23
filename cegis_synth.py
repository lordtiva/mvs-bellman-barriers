"""
Adaptive CEGIS Log-PWL Synthesis Engine (Proposer-Verifier Architecture) for Article A.

Pure HiGHS Linear Programming Proposer + Adaptive Counterexample Knot Insertion +
100% Outward-Rounded Interval Verifier (no Adam in Cases 2-4, no manual 645-knot grid):
  - Case 1: Compressed 24-knot moving-knot staying barrier B_theta on M (T <= 9)
            + CEGIS-LP (Psi, W) + M0 sharpened witness audit (tau_.1 <= 9).
  - Case 2: Continuous ruin-hazard bands covering p in [0%, 2.0%] (60 bands),
            certifying d_ub_raw <= 0 before shift, uniform T*(p) and T*_CEGIS(p)
            across all 60 bands, W' >= m_G on M, <b/<h derivative bounds, and
            M/H1/H2 adverse exits in Intervals.
  - Case 3: Coupled 2-state Markov (B_G, B_B) via joint CEGIS-LP + unified 32-subbox
            x [beta_-, beta_+] continuous H1 certification in state B, <h in B,
            H2 = [0.80, inf) in B, exact Doob eps_0, and full beta-band export.
  - Case 4: Piecewise-continuous AK regime transferability stress test via pure
            CEGIS-LP with full [0.28, inf) adverse-exit certification and <b/<h checks.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from decimal import Decimal
import json
import lzma
import math
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import time
from typing import Callable, Dict, List, Optional, Sequence, Tuple
import numpy as np
from scipy import sparse as sp
from scipy.optimize import brentq, linprog

from progress_bar import ProgressBar

from interval_audit import (
    A_MIN,
    A_MAX,
    BETA_MIN,
    BETA_MAX,
    Q_MIN,
    Q_MAX,
    ETA_MIN,
    ETA_MAX,
    B_M,
    H_M,
    AB_MIN,
    AB_MAX,
    P_REC,
    F_A,
    dF_dL,
    box_worst_u,
    E_plus_exact,
    Interval,
    iv_F_A,
    iv_eval_logpwl,
    iv_deriv_bounds_logpwl,
)
from pwl_model import (
    LogReLUNetwork,
    make_pwl_from_knots,
    pwl_to_dict,
    pwl_from_dict,
    eval_logpwl,
)

from cegis_verifier import (
    prod_Y,
    verify_staying_barrier_bb,
    verify_super_barrier_bb,
    verify_witness_subsolution_bb,
    verify_adverse_exit_bb,
    verify_witness_slope_on_M,
    verify_derivative_below_bound,
    verify_H2_global_interval,
    verify_ak_witness_tail_interval,
    certify_case1_deadline_interval,
    certify_affine_deadline_interval,
    certify_staying_deadline_interval,
    certify_nonstationary_deadline_interval,
    compute_doob_eps0_interval,
    compute_doob_eps0_coupled_pwl_interval,
    iv_compute_R_hat_B_upper,
    iv_solve_markov_B_star,
    _iv_solve_ak_L_max,
)


def _safe_s_lo(eL: float, bL: float) -> float:
    """Directed downward rounding in 50-digit Interval for s <= eL / (1 - bL)."""
    iv_s = Interval(str(eL)) / (Interval("1") - Interval(str(bL)))
    return math.nextafter(iv_s.to_float_bounds()[0], -math.inf)


def _safe_D_hi(eU: float, bR: float) -> float:
    """Directed upward rounding in 50-digit Interval for D >= eU / (1 - bR)."""
    iv_D = Interval(str(eU)) / (Interval("1") - Interval(str(bR)))
    return math.nextafter(iv_D.to_float_bounds()[1], math.inf)


def _golden_L_vec(
    Av: float, qv: float, eL: float, eU: float, x_arr: np.ndarray, y_arr: np.ndarray,
    is_upper: bool, ak_mode: bool = False,
) -> Tuple[np.ndarray, np.ndarray]:
    lo = np.full_like(x_arr, 1e-8, dtype=np.float64)
    hi = np.full_like(x_arr, 1.0 - 1e-9, dtype=np.float64)
    inv_phi = (math.sqrt(5.0) - 1.0) / 2.0

    def _obj(Lv):
        c = qv * x_arr + prod_Y(Av, x_arr, Lv, ak_mode=ak_mode) - y_arr
        lc = np.log(np.maximum(c, 1e-300))
        ll = np.log(1.0 - Lv)
        u1 = eL * lc + (1.0 - eL) * ll
        u2 = eU * lc + (1.0 - eU) * ll
        uv = np.maximum(u1, u2) if is_upper else np.minimum(u1, u2)
        return np.where(c > 1e-15, uv, -1e9 + c)

    u0 = _obj(np.zeros_like(lo))
    x1 = hi - inv_phi * (hi - lo)
    x2 = lo + inv_phi * (hi - lo)
    f1, f2 = _obj(x1), _obj(x2)
    for _ in range(28):
        mr = f1 < f2
        lo = np.where(mr, x1, lo)
        hi = np.where(mr, hi, x2)
        x1n = np.where(mr, x2, hi - inv_phi * (hi - lo))
        x2n = np.where(mr, lo + inv_phi * (hi - lo), x1)
        f1n = np.where(mr, f2, _obj(x1n))
        f2n = np.where(mr, _obj(x2n), f1)
        x1, x2, f1, f2 = x1n, x2n, f1n, f2n
    Lb = 0.5 * (lo + hi)
    ub = _obj(Lb)
    use0 = u0 > ub
    return np.where(use0, 0.0, Lb), np.where(use0, u0, ub)


def _eval_pwl_basis_sparse(
    z_k: np.ndarray,
    z_q: np.ndarray,
    s_lo: float,
    s_hi: float,
) -> Tuple[sp.csr_matrix, np.ndarray]:
    """
    Exact sparse linear decomposition V(z_q) = M @ y_k + offset (2 nonzeros/row).
    """
    n_k = len(z_k)
    n_q = len(z_q)
    zc = np.clip(z_q, z_k[0], z_k[-1])
    idx = np.clip(np.searchsorted(z_k, zc, side="right") - 1, 0, n_k - 2)
    t = (zc - z_k[idx]) / (z_k[idx + 1] - z_k[idx])
    rows = np.repeat(np.arange(n_q, dtype=np.int32), 2)
    cols = np.empty(2 * n_q, dtype=np.int32)
    cols[0::2] = idx
    cols[1::2] = idx + 1
    data = np.empty(2 * n_q, dtype=np.float64)
    data[0::2] = 1.0 - t
    data[1::2] = t
    M = sp.csr_matrix((data, (rows, cols)), shape=(n_q, n_k))
    offset = np.zeros(n_q, dtype=np.float64)
    if s_lo != 0.0:
        below = z_q < z_k[0]
        if np.any(below):
            offset = np.where(below, s_lo * (z_q - z_k[0]), offset)
    if s_hi != 0.0:
        above = z_q > z_k[-1]
        if np.any(above):
            offset = np.where(above, s_hi * (z_q - z_k[-1]), offset)
    return M, offset


def _monotone_diff_sparse(n_k: int) -> sp.csr_matrix:
    """Sparse (n_k - 1, n_k) difference matrix enforcing y_i - y_{i+1} <= -rhs."""
    r = np.repeat(np.arange(n_k - 1, dtype=np.int32), 2)
    c = np.empty(2 * (n_k - 1), dtype=np.int32)
    c[0::2] = np.arange(n_k - 1, dtype=np.int32)
    c[1::2] = c[0::2] + 1
    d = np.tile(np.array([1.0, -1.0], dtype=np.float64), n_k - 1)
    return sp.csr_matrix((d, (r, c)), shape=(n_k - 1, n_k))


def _eval_pwl_basis_and_offset(
    z_k: np.ndarray,
    z_q: np.ndarray,
    s_lo: float,
    s_hi: float,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Exact linear decomposition V(z_q) = M @ y_k + offset for fixed knots z_k
    and fixed outer log-slopes (s_lo, s_hi).
    """
    n_k = len(z_k)
    n_q = len(z_q)
    zc = np.clip(z_q, z_k[0], z_k[-1])
    idx = np.clip(np.searchsorted(z_k, zc, side="right") - 1, 0, n_k - 2)
    t = (zc - z_k[idx]) / (z_k[idx + 1] - z_k[idx])
    M = np.zeros((n_q, n_k), dtype=np.float64)
    rows = np.arange(n_q)
    M[rows, idx] += 1.0 - t
    M[rows, idx + 1] += t
    offset = np.zeros(n_q, dtype=np.float64)
    if s_lo != 0.0:
        below = z_q < z_k[0]
        if np.any(below):
            offset = np.where(below, s_lo * (z_q - z_k[0]), offset)
    if s_hi != 0.0:
        above = z_q > z_k[-1]
        if np.any(above):
            offset = np.where(above, s_hi * (z_q - z_k[-1]), offset)
    return M, offset


# ---------------------------------------------------------------------------
# Fast Teacher VFI (Warm-Start Only; 100% of proofs depend only on Verifier)
# ---------------------------------------------------------------------------
def _solve_teacher_vfi(
    Av: float,
    qv: float,
    bv: float,
    eL: float,
    eU: float,
    is_upper: bool,
    k_grid: np.ndarray,
    ak_mode: bool = False,
    p_ruin: float = 0.0,
    v_ruin: float = 0.0,
    h_safe: float = H_M,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    lk_g = np.log(k_grid)
    b_lo_eff = bv * (1.0 - p_ruin)
    s_lo = eL / (1.0 - b_lo_eff)
    D_hi = eU / (1.0 - bv) if ak_mode else 2.5
    Ls = np.unique(np.concatenate([
        [0.0],
        np.geomspace(1e-7, 1e-4, 10, endpoint=False),
        np.geomspace(1e-4, 0.1, 16, endpoint=False),
        np.linspace(0.1, 0.997, 64),
    ]))
    ss = np.unique(np.concatenate([
        np.linspace(0.15, 0.90, 14, endpoint=False),
        1.0 - np.geomspace(2e-5, 0.10, 68),
    ]))

    Y_mat = qv * k_grid[:, None] + prod_Y(Av, k_grid[:, None], Ls[None, :], ak_mode=ak_mode)
    V_cake0 = (eL / (1.0 - bv)) * (math.log(max((1.0 - bv) * qv, 1e-12)) + (bv / (1.0 - bv)) * math.log(max(bv * qv, 1e-12)))
    V = np.where(k_grid > 0.0014, -35.0, V_cake0 + s_lo * lk_g)
    if ak_mode:
        V = np.where(
            k_grid >= H_M,
            240.0 + (eU / (1.0 - bv)) * np.log(k_grid / H_M),
            np.where(k_grid > 0.0014, -35.0 + 275.0 * (k_grid / H_M), V_cake0 + s_lo * lk_g),
        )

    def _interp(kp_arr, Va):
        lk = np.log(np.maximum(kp_arr, 1e-300))
        r = np.interp(np.clip(lk, lk_g[0], lk_g[-1]), lk_g, Va)
        r = np.where(kp_arr < k_grid[0], Va[0] + s_lo * (lk - lk_g[0]), r)
        return np.where(kp_arr > k_grid[-1], Va[-1] + D_hi * (lk - lk_g[-1]), r)

    c_3 = np.maximum(Y_mat[:, :, None] * (1.0 - ss[None, None, :]), 1e-30)
    y_3 = Y_mat[:, :, None] * ss[None, None, :]
    ec_3 = np.where(c_3 < 1.0, eL, eU)
    ua = ec_3 * np.log(c_3) + (1.0 - eL) * np.log(1.0 - Ls[None, :, None])
    ub = ec_3 * np.log(c_3) + (1.0 - eU) * np.log(1.0 - Ls[None, :, None])
    u_3 = np.maximum(ua, ub) if is_upper else np.minimum(ua, ub)
    if not ak_mode and not is_upper:
        u_3 = np.where(y_3 <= k_grid[-1] * 0.995, u_3, -1e9)

    ruin_mask_3 = (k_grid < h_safe)[:, None, None] if p_ruin > 0.0 else None
    ruin_mask_1 = (k_grid < h_safe) if p_ruin > 0.0 else None
    omp_r = 1.0 - p_ruin
    pv_r = p_ruin * v_ruin

    inv_phi_t = (math.sqrt(5.0) - 1.0) / 2.0
    Y_max_row = Y_mat[:, -1]
    pol_kp = np.zeros_like(k_grid)
    pol_L = np.zeros_like(k_grid)
    for it_v in range(140):
        ev_3 = _interp(y_3, V)
        if ruin_mask_3 is not None:
            ev_3 = np.where(ruin_mask_3, omp_r * ev_3 + pv_r, ev_3)
        tot = u_3 + bv * ev_3
        flat_tot = tot.reshape(len(k_grid), -1)
        idx = np.argmax(flat_tot, axis=1)
        iL = idx // len(ss)
        iS = idx % len(ss)
        Vn = flat_tot[np.arange(len(k_grid)), idx]
        pol_kp = y_3[np.arange(len(k_grid)), iL, iS]
        pol_L = Ls[iL]
        u_pol = u_3[np.arange(len(k_grid)), iL, iS]
        if not is_upper and it_v >= 20:
            kp_hi_cap = Y_max_row * (1.0 - 1e-7) if ak_mode else np.minimum(Y_max_row * (1.0 - 1e-7), k_grid[-1] * 0.995)
            lo_k = np.maximum(k_grid[0], 0.92 * pol_kp)
            hi_k = np.maximum(lo_k * (1.0 + 1e-9), np.minimum(kp_hi_cap, 1.08 * pol_kp))
            x1 = hi_k - inv_phi_t * (hi_k - lo_k)
            x2 = lo_k + inv_phi_t * (hi_k - lo_k)
            _, u1 = _golden_L_vec(Av, qv, eL, eU, k_grid, x1, is_upper=False, ak_mode=ak_mode)
            _, u2 = _golden_L_vec(Av, qv, eL, eU, k_grid, x2, is_upper=False, ak_mode=ak_mode)
            ev1 = _interp(x1, V); ev2 = _interp(x2, V)
            if ruin_mask_1 is not None:
                ev1 = np.where(ruin_mask_1, omp_r * ev1 + pv_r, ev1)
                ev2 = np.where(ruin_mask_1, omp_r * ev2 + pv_r, ev2)
            f1 = u1 + bv * ev1
            f2 = u2 + bv * ev2
            for _g in range(14):
                mr = f1 < f2
                lo_k = np.where(mr, x1, lo_k)
                hi_k = np.where(mr, hi_k, x2)
                x1n = np.where(mr, x2, hi_k - inv_phi_t * (hi_k - lo_k))
                x2n = np.where(mr, lo_k + inv_phi_t * (hi_k - lo_k), x1)
                _, u1n = _golden_L_vec(Av, qv, eL, eU, k_grid, x1n, is_upper=False, ak_mode=ak_mode)
                _, u2n = _golden_L_vec(Av, qv, eL, eU, k_grid, x2n, is_upper=False, ak_mode=ak_mode)
                ev1n = _interp(x1n, V); ev2n = _interp(x2n, V)
                if ruin_mask_1 is not None:
                    ev1n = np.where(ruin_mask_1, omp_r * ev1n + pv_r, ev1n)
                    ev2n = np.where(ruin_mask_1, omp_r * ev2n + pv_r, ev2n)
                f1n = np.where(mr, f2, u1n + bv * ev1n)
                f2n = np.where(mr, u2n + bv * ev2n, f1)
                x1, x2, f1, f2 = x1n, x2n, f1n, f2n
            kp_ref = np.where(f1 > f2, x1, x2)
            L_ref, u_ref = _golden_L_vec(Av, qv, eL, eU, k_grid, kp_ref, is_upper=False, ak_mode=ak_mode)
            evr = _interp(kp_ref, V)
            if ruin_mask_1 is not None:
                evr = np.where(ruin_mask_1, omp_r * evr + pv_r, evr)
            use_ref = (u_ref + bv * evr) > Vn
            pol_kp = np.where(use_ref, kp_ref, pol_kp)
            pol_L = np.where(use_ref, L_ref, pol_L)
            u_pol = np.where(use_ref, u_ref, u_pol)
            Vn = np.where(use_ref, u_ref + bv * evr, Vn)
        for _h in range(25):
            ev_p = _interp(pol_kp, Vn)
            if ruin_mask_1 is not None:
                ev_p = np.where(ruin_mask_1, omp_r * ev_p + pv_r, ev_p)
            Vn = u_pol + bv * ev_p
        if np.max(np.abs(Vn - V)) < 1e-8:
            V = Vn
            break
        V = Vn
    return V, pol_kp, pol_L


def _min_c_E_plus(Av: float, qv: float, K: float, a: float, l0: float, eL: float = ETA_MIN, eU: float = ETA_MAX) -> float:
    t = dF_dL(Av, K, l0)
    c_sup = qv * K + F_A(Av, K, l0) + (1.0 - l0) * t - a
    return min(c_sup - t * min(1.0, (1.0 - ev) * c_sup / t) for ev in (eL, eU))


# ---------------------------------------------------------------------------
# Pure CEGIS-LP Super-Barrier Synthesizer (HiGHS + Adaptive Knot Insertion)
# ---------------------------------------------------------------------------
def _cegis_lp_super_barrier(
    Av: float,
    bL: float,
    bR: float,
    q_hi: float,
    eL: float,
    eU: float,
    k_lo: float,
    k_hi: float,
    init_vals_fn: Callable[[np.ndarray], np.ndarray],
    ak_mode: bool = False,
    m_min_slope: float = 0.0,
    pre_b_slope: float = 0.0,
    pre_h_slope: float = 0.0,
    max_cegis_rounds: int = 12,
    tol_bb: float = 3e-4,
    p_ruin: float = 0.0,
    v_ruin: float = 0.0,
    h_safe: float = H_M,
    b_m_slope: float = B_M,
    pre_b_points: Optional[List[Tuple[float, float]]] = None,
) -> Tuple[Dict[str, object], Dict[str, object], List[Dict[str, object]]]:
    """
    Pure HiGHS-LP CEGIS loop synthesizing a global super-barrier Psi(log K) on
    (0, inf) x [bL, bR], with adaptive knot insertion at worst B&B counterexamples.
    Guarantees d_ub_raw <= 0 BEFORE any shift and 100% outward-rounded iv_certified.
    """
    b_lo_eff = bL * (1.0 - p_ruin)
    s_lo = _safe_s_lo(eL, b_lo_eff)
    D_hi = _safe_D_hi(eU, bR)

    # Compact initial knot set (~185 knots, >= 3x smaller than 645)
    extra_k = [B_M, H_M]
    if p_ruin > 0.0:
        extra_k.extend([h_safe * 0.996, h_safe])
    if b_m_slope < B_M:
        extra_k.extend([b_m_slope, 0.003, 0.006, 0.015, 0.04])
    k_knots = np.unique(np.concatenate([
        [k_lo],
        [k for k in extra_k if k_lo < k < k_hi],
        np.geomspace(k_lo, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.0040, 56, endpoint=False),
        np.geomspace(0.0040, 0.04, 48 if b_m_slope < B_M else 28, endpoint=False),
        np.geomspace(0.04, B_M, 20, endpoint=False),
        np.linspace(B_M, H_M, 16, endpoint=False),
        np.geomspace(H_M, 1.0, 16, endpoint=False),
        np.geomspace(1.0, min(6.0, k_hi * 0.85), 14, endpoint=False),
        np.geomspace(min(6.0, k_hi * 0.85), k_hi, 10),
        [k_hi],
    ]))
    if k_lo < 1.0 < k_hi:
        k_knots = np.unique(np.concatenate([k_knots, [1.0]]))

    ce_x = np.array([], dtype=np.float64)
    ce_L = np.array([], dtype=np.float64)
    ce_s = np.array([], dtype=np.float64)
    history: List[Dict[str, object]] = []

    Ls_act = np.concatenate([[0.0], np.geomspace(1e-7, 0.08, 16, endpoint=False), np.linspace(0.08, 0.996, 52)])
    ss_act = np.unique(np.concatenate([
        np.linspace(0.30, 0.70, 8, endpoint=False),
        np.linspace(0.70, 0.95, 45, endpoint=False),
        1.0 - np.geomspace(1.0e-4, 0.05, 30),
    ]))
    rng = np.random.default_rng(77)

    # Analytical tail constants (independent of y_knots)
    omp_r = 1.0 - p_ruin
    pv_r = p_ruin * v_ruin
    r_top = q_hi + F_A(Av, k_lo, 1.0) / k_lo
    tlo_consts = []
    for bv_t in (bL, bR):
        bv_t_eff = bv_t * omp_r if (p_ruin > 0.0 and k_lo <= h_safe) else bv_t
        c_slo = eL + bv_t_eff * s_lo
        s_lo_opt = (bv_t_eff * s_lo) / c_slo
        shift_lo = (bv_t * pv_r) if (p_ruin > 0.0 and k_lo <= h_safe) else 0.0
        tlo_consts.append((
            bv_t_eff,
            eL * math.log((1.0 - s_lo_opt) * k_lo) + bv_t_eff * s_lo * math.log(s_lo_opt) + c_slo * math.log(r_top) + shift_lo,
        ))

    if not ak_mode:
        Y_end = q_hi * k_hi + Av * (2.0 ** 1.5)
        thi_log_consts = []
        for bv_t in (bL, bR):
            c_dhi = eU + bv_t * D_hi
            s_hi_opt = (bv_t * D_hi) / c_dhi
            thi_log_consts.append((
                bv_t,
                eU * math.log(1.0 - s_hi_opt) + bv_t * D_hi * math.log(s_hi_opt) + c_dhi * math.log(Y_end / k_hi) + eU * math.log(k_hi),
            ))
    else:
        R_top_ak = q_hi + F_A(Av, H_M, 1.0) / H_M
        ak_consts = []
        for bv_t in (bL, bR):
            c_dhi = eU + bv_t * D_hi
            s_hi_opt = (bv_t * D_hi) / c_dhi
            ak_L_iv = _iv_solve_ak_L_max(Interval(str(c_dhi)), Interval(str(Av)), Interval(str(q_hi)), Interval(str(eU)))
            ak_L_hi = float(ak_L_iv.to_float_bounds()[1])
            ak_consts.append((
                bv_t,
                eU * math.log(1.0 - s_hi_opt) + bv_t * D_hi * math.log(s_hi_opt) + ak_L_hi + eU * math.log(k_hi),
            ))

    best_pwl = None
    last_pwl = None
    best_cert = None
    best_psi_h = float("inf")

    for rnd in range(1, max_cegis_rounds + 1):
        n_k = len(k_knots)
        z_knots = np.log(k_knots)
        dlk = np.diff(z_knots)

        # Build collocation points around knots, midpoints, and quarter-points across [k_lo, H_M]
        k_mids = np.sqrt(k_knots[:-1] * k_knots[1:])
        sk_mask = k_knots[1:] <= H_M + 1e-9
        k_q1 = np.exp(0.75 * z_knots[:-1][sk_mask] + 0.25 * z_knots[1:][sk_mask])
        k_q3 = np.exp(0.25 * z_knots[:-1][sk_mask] + 0.75 * z_knots[1:][sk_mask])
        k_eval = np.unique(np.concatenate([k_knots, k_mids, k_q1, k_q3]))
        # Active worst-(L, s) pairs based on current reference curve (last_pwl!)
        y_ref_eval = init_vals_fn(k_eval) if last_pwl is None else eval_logpwl(last_pwl, k_eval)
        Ya = q_hi * k_eval[:, None] + prod_Y(Av, k_eval[:, None], Ls_act[None, :], ak_mode=ak_mode)
        ca = np.maximum((1.0 - ss_act[None, None, :]) * Ya[:, :, None], 1e-18)
        ya = np.maximum(ss_act[None, None, :] * Ya[:, :, None], 1e-18)
        ua = np.where(ca < 1.0, eL, eU) * np.log(ca) + (1.0 - eU) * np.log(1.0 - Ls_act[None, :, None])
        if last_pwl is None:
            eva_raw = init_vals_fn(ya.ravel()).reshape(ya.shape)
        else:
            eva_raw = eval_logpwl(last_pwl, ya)
        eva = np.where((k_eval < h_safe)[:, None, None], omp_r * eva_raw + pv_r, eva_raw) if p_ruin > 0.0 else eva_raw
        ba = np.where(eva < 0.0, bL, bR)
        resa = (ua + ba * eva - y_ref_eval[:, None, None]).reshape(len(k_eval), -1)
        top_idx = np.argpartition(resa, -8, axis=1)[:, -8:].ravel()
        act_x = np.repeat(k_eval, 8)
        act_L = Ls_act[top_idx // len(ss_act)]
        act_s = ss_act[top_idx % len(ss_act)]

        # Also structured probes (including near-zero labor cake-eating probes on small K)
        xs_e = np.repeat(k_eval, 6)
        Ls_e = np.tile([0.0, 1e-6, 0.36, 0.58, 0.78, 0.95], len(k_eval))
        ss_e = np.tile([0.97, 0.92, 0.70, 0.88, 0.955, 0.9985], len(k_eval))

        xs_r = np.repeat(k_eval, 3)
        Ls_r = rng.uniform(0.0, 0.98, size=len(xs_r))
        ss_r = rng.uniform(0.25, 0.9995, size=len(xs_r))

        col_x = np.concatenate([act_x, xs_e, xs_r, ce_x]) if len(ce_x) > 0 else np.concatenate([act_x, xs_e, xs_r])
        col_L = np.concatenate([act_L, Ls_e, Ls_r, ce_L]) if len(ce_x) > 0 else np.concatenate([act_L, Ls_e, Ls_r])
        col_s = np.concatenate([act_s, ss_e, ss_r, ce_s]) if len(ce_x) > 0 else np.concatenate([act_s, ss_e, ss_r])

        Y_col = q_hi * col_x + prod_Y(Av, col_x, col_L, ak_mode=ak_mode)
        c_col = np.maximum((1.0 - col_s) * Y_col, 1e-18)
        y_col = np.maximum(col_s * Y_col, 1e-18)
        u_col = np.where(c_col < 1.0, eL, eU) * np.log(c_col) + (1.0 - eU) * np.log(1.0 - col_L)
        zx_col = np.log(col_x)
        zy_col = np.log(y_col)
        ruin_col = (col_x < h_safe) if p_ruin > 0.0 else np.zeros(len(col_x), dtype=bool)
        # Note: if h_safe is in col_x from B&B edge case [xL, h_safe], also include ruin-branch safety copy at h_safe
        col_omp = np.where(ruin_col, omp_r, 1.0)
        col_pv = np.where(ruin_col, pv_r, 0.0)

        Mx, _ = _eval_pwl_basis_sparse(z_knots, zx_col, s_lo, D_hi)
        My, oy = _eval_pwl_basis_sparse(z_knots, zy_col, s_lo, D_hi)

        # Solve pure HiGHS LP directly for y_knots (2 sign-update passes if values cross 0)
        y_cur = init_vals_fn(k_knots) if last_pwl is None else eval_logpwl(last_pwl, k_knots)
        req_s = np.where((k_knots[:-1] >= b_m_slope - 1e-9) & (k_knots[1:] <= H_M + 1e-9), m_min_slope, 0.0)
        if pre_b_slope > 0.0:
            req_s = np.where(k_knots[:-1] < B_M + 1e-9, np.maximum(req_s, pre_b_slope), req_s)
        if pre_h_slope > 0.0:
            req_s = np.where(k_knots[:-1] < H_M + 1e-9, np.maximum(req_s, pre_h_slope), req_s)
        if pre_b_points is not None:
            for kb_pt, sl_pt in pre_b_points:
                req_s = np.where(k_knots[:-1] < kb_pt + 1e-12, np.maximum(req_s, sl_pt), req_s)
        if not ak_mode:
            req_s = np.where(k_knots[:-1] >= 1.0, np.maximum(req_s, 0.135), req_s)

        A_mon = _monotone_diff_sparse(n_k)
        req_log_s = np.maximum(req_s * k_knots[1:], np.where(k_knots[1:] <= 0.0012, s_lo, 0.0))
        b_mon = -(req_log_s * dlk)

        # Sparse L1 log-slope total variation regularizer on lower asymptote & upper region
        tv_idx = np.where((k_knots[1:-1] >= 0.005) | (k_knots[1:-1] <= 0.0012))[0]
        n_tv = len(tv_idx)
        if n_tv > 0:
            j_arr = np.arange(n_tv, dtype=np.int32)
            inv_d0 = 1.0 / dlk[tv_idx]
            inv_d1 = 1.0 / dlk[tv_idx + 1]
            r_tv = np.concatenate([np.repeat(2 * j_arr, 4), np.repeat(2 * j_arr + 1, 4)])
            c_tv = np.concatenate([
                np.column_stack([tv_idx, tv_idx + 1, tv_idx + 2, n_k + j_arr]).ravel(),
                np.column_stack([tv_idx, tv_idx + 1, tv_idx + 2, n_k + j_arr]).ravel(),
            ]).astype(np.int32)
            d_tv = np.concatenate([
                np.column_stack([inv_d0, -(inv_d0 + inv_d1), inv_d1, np.full(n_tv, -1.0)]).ravel(),
                np.column_stack([-inv_d0, (inv_d0 + inv_d1), -inv_d1, np.full(n_tv, -1.0)]).ravel(),
            ])
            A_tv = sp.csr_matrix((d_tv, (r_tv, c_tv)), shape=(2 * n_tv, n_k + n_tv))
        else:
            A_tv = sp.csr_matrix((0, n_k), dtype=np.float64)
        b_tv = np.zeros(2 * n_tv, dtype=np.float64)

        # Objective: tighten Psi on [b_m_slope, H_M] union {h} with global regularizer + L1 log-slope TV
        c_obj_y = np.zeros(n_k, dtype=np.float64)
        m_mask = (k_knots >= b_m_slope - 1e-9) & (k_knots <= H_M + 1e-9)
        c_obj_y[m_mask] = 1.0 / max(1, int(np.sum(m_mask)))
        if b_m_slope < B_M:
            low_m = (k_knots >= b_m_slope - 1e-9) & (k_knots < B_M)
            c_obj_y[low_m] += 2.0 / max(1, int(np.sum(low_m)))
            i_bext = int(np.argmin(np.abs(k_knots - b_m_slope)))
            c_obj_y[i_bext] += 1.50
        c_obj_y += 1e-3 / n_k
        tv_w = 5e-5 if b_m_slope < B_M else 5e-4
        c_obj = np.concatenate([c_obj_y, np.full(n_tv, tv_w, dtype=np.float64)])
        lp_bounds = [(-2500.0, 2500.0)] * n_k + [(0.0, None)] * n_tv

        m_hi_c = 0.0045 if ak_mode else 0.0020
        if b_m_slope < B_M:
            m_base = np.where(
                col_x >= 0.05, m_hi_c,
                np.where(col_x >= 0.012, 0.0035, np.where(col_x >= b_m_slope - 1e-9, 0.0065, 0.018)),
            )
        else:
            m_base = np.where(col_x >= 0.05, m_hi_c, 0.018)
        solved = False
        for m_scale in (1.0, 0.65, 0.35, 0.15, 0.05):
            m_vec = m_scale * m_base
            m_t_lo = m_scale * 0.018
            m_t_hi = m_scale * 0.0020
            y_try = y_cur.copy()
            ok_pass = False
            for _sp in range(2):
                vy_est = col_omp * (My @ y_try + oy) + col_pv
                near0 = np.abs(vy_est) <= 1.5
                A_rows = [A_mon]
                b_rows = [b_mon]
                for bv_c, m_c in ((bL, (vy_est < 0.0) | near0), (bR, (vy_est >= 0.0) | near0)):
                    if np.any(m_c):
                        if p_ruin > 0.0:
                            A_rows.append(sp.diags(bv_c * col_omp[m_c]) @ My[m_c] - Mx[m_c])
                            b_rows.append(-(u_col[m_c] + bv_c * (col_omp[m_c] * oy[m_c] + col_pv[m_c]) + m_vec[m_c]))
                        else:
                            A_rows.append(bv_c * My[m_c] - Mx[m_c])
                            b_rows.append(-(u_col[m_c] + bv_c * oy[m_c] + m_vec[m_c]))
                # Tails
                for bv_t_eff, tc in tlo_consts:
                    A_rows.append(sp.csr_matrix(([-(1.0 - bv_t_eff)], ([0], [0])), shape=(1, n_k)))
                    b_rows.append(np.array([-(tc + m_t_lo)]))
                if not ak_mode:
                    M1, o1 = _eval_pwl_basis_sparse(z_knots, np.array([0.0]), s_lo, D_hi)
                    e_last = sp.csr_matrix(([-1.0], ([0], [n_k - 1])), shape=(1, n_k))
                    for bv_t, thc in thi_log_consts:
                        A_rows.append(bv_t * M1 + e_last)
                        b_rows.append(np.array([-(eU * math.log(Y_end) + bv_t * float(o1[0]) + m_t_hi)]))
                        A_rows.append(sp.csr_matrix(([-(1.0 - bv_t)], ([0], [n_k - 1])), shape=(1, n_k)))
                        b_rows.append(np.array([-(thc + m_t_hi)]))
                else:
                    for bv_t, akc in ak_consts:
                        A_rows.append(sp.csr_matrix(([-(1.0 - bv_t)], ([0], [n_k - 1])), shape=(1, n_k)))
                        b_rows.append(np.array([-(akc + m_t_hi)]))
                        A_rows.append(sp.csr_matrix(([-(1.0 - bv_t)], ([0], [n_k - 1])), shape=(1, n_k)))
                        b_rows.append(np.array([-(eU * math.log(R_top_ak * k_hi) + m_t_hi)]))

                A_y_blk = sp.vstack(A_rows, format="csr")
                b_y_blk = np.concatenate(b_rows)
                if n_tv > 0:
                    A_full = sp.vstack([
                        sp.hstack([A_y_blk, sp.csr_matrix((A_y_blk.shape[0], n_tv), dtype=np.float64)], format="csr"),
                        A_tv,
                    ], format="csc")
                    b_full = np.concatenate([b_y_blk, b_tv])
                else:
                    A_full = A_y_blk.tocsc()
                    b_full = b_y_blk

                res = linprog(c_obj, A_ub=A_full, b_ub=b_full, bounds=lp_bounds, method="highs")
                if res.success:
                    y_try = res.x[:n_k].copy()
                    ok_pass = True
                else:
                    ok_pass = False
                    break
            if ok_pass:
                y_knots = y_try
                solved = True
                break
        assert solved, f"CEGIS-LP failed to find feasible super-barrier at round {rnd}"

        pwl = make_pwl_from_knots(k_knots, y_knots, s_lo, D_hi)
        last_pwl = pwl
        cert = verify_super_barrier_bb(
            pwl, pwl, Av, bL, bR, q_hi=q_hi, eL=eL, eU=eU, tol=tol_bb, ak_mode=ak_mode,
            p_ruin=p_ruin, v_ruin=v_ruin, h_safe=h_safe,
        )
        d_ub_raw = float(cert["d_ub_iv"])
        psi_h = float(eval_logpwl(pwl, np.array([H_M]))[0])
        history.append({
            "round": rnd,
            "knots": int(n_k),
            "d_ub_raw": float(cert["d_ub"]),
            "d_ub_iv_raw": d_ub_raw,
            "d_lb_raw": float(cert["d_lb"]),
            "tail_max": float(cert["tail_max"]),
            "psi_h": psi_h,
        })
        if cert["certified"] and psi_h < best_psi_h:
            best_pwl = pwl
            best_cert = cert
            best_psi_h = psi_h
        if cert["certified"]:
            # Certified with d_ub_raw <= 0 and iv_certified == True BEFORE any shift!
            break

        # Adaptive CEGIS counterexample + knot insertion (preserve true sample CEs first!)
        ce_list = cert["counterexamples"][:24]
        new_x, new_L, new_s, ins_k = [], [], [], []
        for cx, cL, cs, c_val in ce_list:
            if c_val > -1e-4:
                ins_k.append(float(np.clip(cx, k_lo * 1.05, k_hi * 0.95)))
            for sc in (0.992, 1.0, 1.008):
                new_x.append(float(np.clip(cx * sc, k_lo, k_hi)))
                new_L.append(float(np.clip(cL, 0.0, 0.9999)))
                new_s.append(float(np.clip(cs, 1e-4, 0.99999)))
        if new_x:
            ce_x = np.concatenate([ce_x, np.array(new_x)])
            ce_L = np.concatenate([ce_L, np.array(new_L)])
            ce_s = np.concatenate([ce_s, np.array(new_s)])
        if ins_k and len(k_knots) < 320:
            cand_add = []
            for ck in ins_k:
                if np.min(np.abs(np.log(k_knots) - math.log(ck))) > 2.0e-3:
                    if not cand_add or min(abs(math.log(c) - math.log(ck)) for c in cand_add) > 2.0e-3:
                        cand_add.append(ck)
                if len(cand_add) >= 18:
                    break
            if cand_add:
                k_knots = np.unique(np.concatenate([k_knots, np.array(cand_add)]))

    assert best_pwl is not None and best_cert is not None and best_cert["certified"] and best_cert["iv_certified"], (
        f"CEGIS-LP super-barrier failed to reach d_ub_raw <= 0: last={history[-1]}"
    )
    return best_pwl, best_cert, history


# ---------------------------------------------------------------------------
# Pure CEGIS-LP Continuous Witness Synthesizer (with M-Monotonicity Check)
# ---------------------------------------------------------------------------
def _cegis_lp_witness(
    Av: float,
    qv: float,
    bL: float,
    bR: float,
    eL: float,
    eU: float,
    k_domain: Tuple[float, float],
    ak_mode: bool = False,
    m_req_M: float = 0.0,
    max_cegis_rounds: int = 8,
    p_ruin: float = 0.0,
    v_ruin: float = 0.0,
    h_safe: float = H_M,
    b_m_slope: float = B_M,
) -> Tuple[Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], List[Dict[str, object]]]:
    """
    Pure HiGHS-LP CEGIS loop synthesizing continuous feasible sub-solution witness
    (W, kp, L) on k_domain = [k_a, k_b], explicitly enforcing W'(x) >= m_req_M on [b_m_slope, H_M]
    and auditing 100% of leaf intervals in 50-digit Decimal Interval arithmetic.
    """
    k_a, k_b = k_domain
    extra_wg = []
    if k_a < H_M < k_b:
        extra_wg.extend([H_M * 0.996, H_M])
    if p_ruin > 0.0 and k_a < h_safe < k_b:
        extra_wg.extend([h_safe * 0.996, h_safe])
    if k_a < 0.04:
        k_grid = np.unique(np.concatenate([
            [k_a],
            extra_wg,
            np.geomspace(k_a, 0.02, 56, endpoint=False),
            np.geomspace(0.02, min(H_M, k_b), 44, endpoint=False),
            np.geomspace(min(H_M, k_b), min(0.80, k_b), 46, endpoint=False),
            np.geomspace(min(0.80, k_b), k_b, 50),
            [k_b],
        ]))
    else:
        k_grid = np.unique(np.concatenate([
            [k_a],
            extra_wg,
            np.geomspace(k_a, min(H_M, k_b), 52, endpoint=False),
            np.geomspace(min(H_M, k_b), min(0.80, k_b), 52, endpoint=False),
            np.geomspace(min(0.80, k_b), k_b, 56),
            [k_b],
        ]))
    V_t, kp_t, L_t = _solve_teacher_vfi(
        Av, qv, bR, eL, eU, False, k_grid, ak_mode=ak_mode,
        p_ruin=p_ruin, v_ruin=v_ruin, h_safe=h_safe,
    )
    kp_t = np.maximum(kp_t, k_a * 1.005) if ak_mode else np.clip(kp_t, k_a * 1.005, k_b * 0.995)
    L_t = np.clip(L_t, 0.0, 0.985)

    if k_a < 0.04:
        pol_lo = np.where(k_grid <= 0.04)[0]
        pol_hi = np.arange(0, len(k_grid), 2)
        pol_idx = np.unique(np.concatenate([pol_lo, pol_hi, [len(k_grid) - 1]]))
    else:
        pol_idx = np.unique(np.concatenate([np.arange(0, len(k_grid), 2), [len(k_grid) - 1]]))
    k_pol = k_grid[pol_idx]
    kp_pwl = make_pwl_from_knots(k_pol, kp_t[pol_idx], 0.0, 0.0)
    L_pwl = make_pwl_from_knots(k_pol, L_t[pol_idx], 0.0, 0.0)

    # Verify policy feasibility on dense grid; refine policy knots if needed
    chk_k = np.unique(np.concatenate([k_grid, np.sqrt(k_grid[:-1] * k_grid[1:])]))
    L_chk = eval_logpwl(L_pwl, chk_k)
    kp_chk = eval_logpwl(kp_pwl, chk_k)
    c_chk = qv * chk_k + prod_Y(Av, chk_k, np.clip(L_chk, 0.0, 0.999), ak_mode=ak_mode) - kp_chk
    if np.any(c_chk <= 1e-6) or np.any(L_chk >= 0.999) or np.any(L_chk < 0.0) or np.any(kp_chk < k_a) or (not ak_mode and np.any(kp_chk > k_b)):
        k_pol2 = np.unique(np.concatenate([[k_a], chk_k[1:-1:2], [k_b]]))
        kp_p2 = np.interp(np.log(k_pol2), np.log(k_grid), kp_t)
        kp_p2 = np.maximum(kp_p2, k_a * 1.005) if ak_mode else np.clip(kp_p2, k_a * 1.005, k_b * 0.995)
        L_p2 = np.clip(np.interp(np.log(k_pol2), np.log(k_grid), L_t), 0.0, 0.985)
        kp_pwl = make_pwl_from_knots(k_pol2, kp_p2, 0.0, 0.0)
        L_pwl = make_pwl_from_knots(k_pol2, L_p2, 0.0, 0.0)

    k_knots_raw = [
        [k_a],
        [H_M] if (k_a < H_M < k_b) else [],
        [0.80] if (k_a < 0.80 < k_b) else [],
        [h_safe * 0.996, h_safe] if (p_ruin > 0.0 and k_a < h_safe < k_b) else [],
        np.geomspace(k_a * 1.002, min(0.04, k_b * 0.995), 36, endpoint=False) if k_a < 0.04 else [],
        np.geomspace(max(k_a * 1.005, 0.04 if k_a < 0.04 else k_a * 1.005), min(H_M, k_b * 0.995), 24, endpoint=False) if max(k_a * 1.005, 0.04 if k_a < 0.04 else k_a * 1.005) < min(H_M, k_b * 0.995) else [],
        np.geomspace(max(k_a * 1.005, min(H_M, k_b * 0.995)), min(0.80, k_b * 0.995), 24, endpoint=False) if max(k_a * 1.005, min(H_M, k_b * 0.995)) < min(0.80, k_b * 0.995) else [],
        np.geomspace(max(k_a * 1.005, min(0.80, k_b * 0.995)), k_b * 0.995, 24) if max(k_a * 1.005, min(0.80, k_b * 0.995)) < k_b * 0.995 else [],
        [k_b],
    ]
    k_knots = np.unique(np.concatenate([arr for arr in k_knots_raw if len(arr) > 0]))
    s_hi_w = _safe_s_lo(eL, bL) if ak_mode else 0.0
    omp_r = 1.0 - p_ruin
    pv_r = p_ruin * v_ruin

    ce_k = np.array([], dtype=np.float64)
    history: List[Dict[str, object]] = []
    best_W = None
    best_cert = None

    for rnd in range(1, max_cegis_rounds + 1):
        n_w = len(k_knots)
        z_knots = np.log(k_knots)
        dlk = np.diff(z_knots)
        k_mids = np.sqrt(k_knots[:-1] * k_knots[1:])
        col_k = np.unique(np.concatenate([k_knots, k_mids, np.sqrt(k_knots[:-1] * k_mids), np.sqrt(k_mids * k_knots[1:]), ce_k]))
        L_col = np.clip(eval_logpwl(L_pwl, col_k), 0.0, 0.999)
        kp_col = np.maximum(eval_logpwl(kp_pwl, col_k), k_a)
        if not ak_mode:
            kp_col = np.minimum(kp_col, k_b)
        c_col = np.maximum(qv * col_k + prod_Y(Av, col_k, L_col, ak_mode=ak_mode) - kp_col, 1e-18)
        lc = np.log(c_col)
        ll = np.log(np.maximum(1.0 - L_col, 1e-18))
        u_col = np.minimum(eL * lc + (1.0 - eL) * ll, eU * lc + (1.0 - eU) * ll)

        ruin_col = (col_k < h_safe) if p_ruin > 0.0 else np.zeros(len(col_k), dtype=bool)
        # Note: if p_ruin > 0 and k_a < h_safe, continuous W at h_safe must satisfy ruin-branch too
        if p_ruin > 0.0 and k_a < h_safe:
            ruin_col = col_k <= h_safe + 1e-12
        col_omp = np.where(ruin_col, omp_r, 1.0)
        col_pv = np.where(ruin_col, pv_r, 0.0)

        Mx, _ = _eval_pwl_basis_sparse(z_knots, np.log(col_k), 0.0, s_hi_w)
        My, oy = _eval_pwl_basis_sparse(z_knots, np.log(kp_col), 0.0, s_hi_w)

        # Monotonicity on [b_m_slope, H_M] (Fix 5) and non-decreasing everywhere (+1e-4 margin for outward Interval check)
        req_val_M = (m_req_M + 1e-4) if m_req_M > 0.0 else 0.0
        req_s = np.where((k_knots[:-1] < H_M - 1e-12) & (k_knots[1:] > b_m_slope + 1e-12), req_val_M, 0.0)
        A_mon = _monotone_diff_sparse(n_w)
        b_mon = -(req_s * k_knots[1:] * dlk)

        c_w = -np.ones(n_w, dtype=np.float64) / n_w
        c_w[0] -= 0.85 if k_a < 0.04 else 0.40
        i_h = int(np.argmin(np.abs(k_knots - H_M)))
        c_w[i_h] -= 0.25

        y_try = np.interp(z_knots, np.log(k_grid), V_t)
        solved_w = False
        m_trgs = (1.5e-4, 6.0e-5, 2.0e-5) if k_a < 0.04 else (2.5e-4, 1.0e-4, 4.0e-5, 1.0e-5)
        for m_trg in m_trgs:
            yt = y_try.copy()
            ok_p = False
            for _sp in range(2):
                wy_est = col_omp * (My @ yt + oy) + col_pv
                near0 = np.abs(wy_est) <= 1.5
                A_rows = [A_mon]
                b_rows = [b_mon]
                for bv_c, m_c in ((bR, (wy_est < 0.0) | near0), (bL, (wy_est >= 0.0) | near0)):
                    if np.any(m_c):
                        if p_ruin > 0.0:
                            A_rows.append(Mx[m_c] - sp.diags(bv_c * col_omp[m_c]) @ My[m_c])
                            b_rows.append(u_col[m_c] + bv_c * (col_omp[m_c] * oy[m_c] + col_pv[m_c]) - m_trg)
                        else:
                            A_rows.append(Mx[m_c] - bv_c * My[m_c])
                            b_rows.append(u_col[m_c] + bv_c * oy[m_c] - m_trg)
                res = linprog(c_w, A_ub=sp.vstack(A_rows, format="csc"), b_ub=np.concatenate(b_rows), bounds=[(-500.0, 2000.0)] * n_w, method="highs")
                if res.success:
                    yt = res.x.copy()
                    ok_p = True
                else:
                    ok_p = False
                    break
            if ok_p:
                y_knots = yt
                solved_w = True
                break
        assert solved_w, f"Witness LP failed at round {rnd}"

        W_pwl = make_pwl_from_knots(k_knots, y_knots, 0.0, s_hi_w)
        cert = verify_witness_subsolution_bb(
            W_pwl, W_pwl, kp_pwl, L_pwl, Av, qv, bL, bR, eL=eL, eU=eU,
            k_domain=k_domain, ak_mode=ak_mode, tol=8e-5, interval_check=True,
            p_ruin=p_ruin, v_ruin=v_ruin, h_safe=h_safe,
        )
        history.append({"round": rnd, "knots_W": int(n_w), "d_ub": float(cert["d_ub"]), "d_ub_iv": float(cert["d_ub_iv"])})
        if cert["certified"] and cert["iv_certified"]:
            best_W = W_pwl
            best_cert = cert
            break

        ins_k, new_ce = [], []
        for cx, cval in cert["counterexamples"]:
            if cval > -5e-5:
                ins_k.append(float(np.clip(cx, k_a * 1.001, k_b * 0.999)))
            for f in (0.992, 1.0, 1.008):
                new_ce.append(float(np.clip(cx * f, k_a, k_b)))
        if new_ce:
            ce_k = np.unique(np.concatenate([ce_k, np.array(new_ce)]))
        if ins_k and len(k_knots) < 160 and rnd < max_cegis_rounds:
            cand_add = [ck for ck in ins_k if np.min(np.abs(np.log(k_knots) - math.log(ck))) > 1.5e-3]
            if cand_add:
                k_knots = np.unique(np.concatenate([k_knots, np.array(cand_add[:12])]))

    if best_W is None and len(k_knots) == len(y_knots) and 0.0 < float(cert["d_ub_iv"]) < 5.0e-4:
        shift_w = (float(cert["d_ub_iv"]) + 2.0e-5) / (1.0 - bL * (1.0 - p_ruin))
        W_sh = make_pwl_from_knots(k_knots, y_knots - shift_w, 0.0, s_hi_w)
        c_sh = verify_witness_subsolution_bb(
            W_sh, W_sh, kp_pwl, L_pwl, Av, qv, bL, bR, eL=eL, eU=eU,
            k_domain=k_domain, ak_mode=ak_mode, tol=8e-5, interval_check=True,
            p_ruin=p_ruin, v_ruin=v_ruin, h_safe=h_safe,
        )
        if c_sh["certified"] and c_sh["iv_certified"]:
            best_W, best_cert = W_sh, c_sh

    assert best_W is not None and best_cert is not None and best_cert["certified"] and best_cert["iv_certified"], (
        f"Witness CEGIS-LP failed certification: {history[-1]}"
    )
    if m_req_M > 0.0:
        sl_ok, min_sl = verify_witness_slope_on_M(best_W, m_req_M, b_m=b_m_slope, h_m=H_M)
        assert sl_ok, f"Witness slope on [{b_m_slope},{H_M}] failed: {min_sl:.4f} < {m_req_M:.4f}"
    return best_W, kp_pwl, L_pwl, best_cert, history


# ---------------------------------------------------------------------------
# Pure CEGIS-LP Staying Barrier + Adaptive Pruning (Zero PyTorch/Adam)
# ---------------------------------------------------------------------------
def _cegis_lp_staying_barrier(
    b_m: float,
    h_m: float,
    A_hi: float,
    q_hi: float,
    b_lo: float,
    b_hi: float,
    e_lo: float,
    e_hi: float,
    B_ev_pwl: Optional[Dict[str, object]] = None,
    p_ruin: float = 0.0,
    v_ruin: float = 0.0,
    n_knots: int = 36,
    max_rounds: int = 12,
    tol_bb: float = 2e-4,
    fixed_knots: Optional[np.ndarray] = None,
    target_W_pwl: Optional[Dict[str, object]] = None,
    min_slope_M: float = 0.0,
) -> Tuple[Dict[str, object], Dict[str, object], Tuple[np.ndarray, np.ndarray, np.ndarray]]:
    """
    Pure deterministic HiGHS-LP CEGIS synthesizer for a staying barrier B(log K) on
    [b_m, h_m] (with s_lo = s_hi = 0.0), or T_stay[B_ev_pwl] when B_ev_pwl is given.
    """
    if fixed_knots is not None:
        kB = np.asarray(fixed_knots, dtype=np.float64)
    else:
        kB = np.geomspace(b_m, h_m, n_knots)
    gx, gy = np.meshgrid(np.geomspace(b_m, h_m, 34), np.geomspace(b_m, h_m, 34), indexing="ij")
    fx0, fy0 = gx.ravel(), gy.ravel()
    # Include dense diagonal saving probes along the feasible frontier (essential on narrow/low bands)
    x_diag = np.geomspace(b_m, h_m, 48)
    y_lim = q_hi * x_diag + F_A(A_hi, x_diag, 0.9999)
    d_fx, d_fy = [], []
    for xd, yl in zip(x_diag, y_lim):
        for f in (0.0, 0.15, 0.4, 0.7, 0.85, 0.94, 0.98, 0.995):
            yv = xd + f * (yl - xd)
            if b_m <= yv <= h_m:
                d_fx.append(float(xd)); d_fy.append(float(yv))
        yv_top = min(h_m, float(yl) * 0.99999)
        if yv_top > b_m:
            for yv in np.geomspace(b_m, yv_top, 10):
                d_fx.append(float(xd)); d_fy.append(float(yv))
    fx = np.concatenate([fx0, np.array(d_fx, dtype=np.float64)]) if d_fx else fx0
    fy = np.concatenate([fy0, np.array(d_fy, dtype=np.float64)]) if d_fx else fy0
    feas = (q_hi * fx + F_A(A_hi, fx, 0.9999) - fy) > 1e-12
    fx, fy = fx[feas], fy[feas]
    _, fu = _golden_L_vec(A_hi, q_hi, e_lo, e_hi, fx, fy, is_upper=True)

    omp_r = 1.0 - p_ruin
    pv_r = p_ruin * v_ruin

    best_pwl = None
    best_cert = None
    for rnd in range(1, max_rounds + 1):
        zB = np.log(kB)
        dlB = np.diff(zB)
        nB = len(kB)
        A_mon = _monotone_diff_sparse(nB)
        b_mon = -(min_slope_M * kB[1:] * dlB)

        Mx, _ = _eval_pwl_basis_sparse(zB, np.log(fx), 0.0, 0.0)
        if B_ev_pwl is None:
            My, _ = _eval_pwl_basis_sparse(zB, np.log(fy), 0.0, 0.0)
            y_init = np.full(nB, -45.0, dtype=np.float64)
            solved = False
            for m_slk in (3.0e-3, 1.0e-3, 3.0e-4, 5.0e-5):
                yt = y_init.copy()
                ok_p = False
                for _sp in range(2):
                    cb_est = omp_r * (My @ yt) + pv_r if p_ruin > 0.0 else (My @ yt)
                    near0 = np.abs(cb_est) <= 1.5
                    A_rows = [A_mon]
                    b_rows = [b_mon]
                    for bv_c, mc in ((b_lo, (cb_est < 0.0) | near0), (b_hi, (cb_est >= 0.0) | near0)):
                        if np.any(mc):
                            A_rows.append(bv_c * omp_r * My[mc] - Mx[mc])
                            b_rows.append(-(fu[mc] + bv_c * pv_r + m_slk))
                    A_blk = sp.vstack(A_rows, format="csr")
                    b_blk = np.concatenate(b_rows)
                    if target_W_pwl is not None:
                        w_vals = eval_logpwl(target_W_pwl, kB)
                        # Maximize t_gap = min_i (w_vals[i] - B[i]) - eps * mean(B)
                        A_gap = sp.hstack([sp.eye(nB, format="csr"), np.ones((nB, 1), dtype=np.float64)], format="csr")
                        A_ext = sp.hstack([A_blk, sp.csr_matrix((A_blk.shape[0], 1), dtype=np.float64)], format="csr")
                        c_obj = np.concatenate([np.full(nB, 1e-3 / nB), np.array([-1.0])])
                        bds = [(-500.0, 500.0)] * nB + [(-50.0, 200.0)]
                        res = linprog(c_obj, A_ub=sp.vstack([A_ext, A_gap], format="csc"), b_ub=np.concatenate([b_blk, w_vals]), bounds=bds, method="highs")
                    else:
                        c_obj = np.ones(nB, dtype=np.float64) / nB
                        res = linprog(c_obj, A_ub=A_blk.tocsc(), b_ub=b_blk, bounds=[(-500.0, 500.0)] * nB, method="highs")
                    if res.success:
                        yt = res.x[:nB].copy()
                        ok_p = True
                    else:
                        ok_p = False
                        break
                if ok_p:
                    y_knots = yt
                    solved = True
                    break
            assert solved, f"Staying barrier LP failed on [{b_m},{h_m}]"
        else:
            # Fixed continuation B_ev_pwl -> non-stationary J_k = T_stay[J_{k-1}]
            bev_raw = eval_logpwl(B_ev_pwl, fy)
            cb_fy = omp_r * bev_raw + pv_r if p_ruin > 0.0 else bev_raw
            rhs_val = fu + np.where(cb_fy < 0.0, b_lo * cb_fy, b_hi * cb_fy)
            # Envelope per sample x: we take tighter upper bound on B(x) at collocation points
            for m_slk in (5e-4, 1e-4, 2e-5, 0.0):
                A_blk = sp.vstack([A_mon, -Mx], format="csc")
                b_blk = np.concatenate([b_mon, -(rhs_val + m_slk)])
                c_obj = np.ones(nB, dtype=np.float64) / nB
                res = linprog(c_obj, A_ub=A_blk, b_ub=b_blk, bounds=[(-500.0, 500.0)] * nB, method="highs")
                if res.success:
                    y_knots = res.x.copy()
                    break
            else:
                raise AssertionError(f"Non-stationary staying LP failed on [{b_m},{h_m}]")

        B_pwl = make_pwl_from_knots(kB, y_knots, 0.0, 0.0)
        cert = verify_staying_barrier_bb(
            B_pwl, A_hi=A_hi, q_hi=q_hi, b_lo=b_lo, b_hi=b_hi, e_lo=e_lo, e_hi=e_hi,
            tol=tol_bb, B_ev_pwl=B_ev_pwl, b_m=b_m, h_m=h_m, p_ruin=p_ruin, v_ruin=v_ruin,
        )
        if cert["certified"] and cert["iv_certified"]:
            best_pwl = B_pwl
            best_cert = cert
            break
        added = 0
        if rnd < max_rounds:
            for cx, cy, _, cval in cert["counterexamples"][:16]:
                _, cu = _golden_L_vec(A_hi, q_hi, e_lo, e_hi, np.array([cx]), np.array([cy]), is_upper=True)
                if cu[0] > -1e8:
                    fx = np.append(fx, cx); fy = np.append(fy, cy); fu = np.append(fu, float(cu[0]))
                    added += 1
                if fixed_knots is None and cval > -1e-4 and len(kB) < 60:
                    if np.min(np.abs(np.log(kB) - math.log(max(b_m, min(h_m, cx))))) > 5e-3:
                        kB = np.unique(np.concatenate([kB, [float(np.clip(cx, b_m, h_m))]]))
        if rnd == max_rounds and best_pwl is None:
            shift = (max(cert["d_ub"], cert["d_ub_iv"]) + 4e-4) / (1.0 if B_ev_pwl is not None else (1.0 - b_hi * omp_r))
            B_pwl = make_pwl_from_knots(kB, y_knots + shift, 0.0, 0.0)
            cert = verify_staying_barrier_bb(
                B_pwl, A_hi=A_hi, q_hi=q_hi, b_lo=b_lo, b_hi=b_hi, e_lo=e_lo, e_hi=e_hi,
                tol=tol_bb, B_ev_pwl=B_ev_pwl, b_m=b_m, h_m=h_m, p_ruin=p_ruin, v_ruin=v_ruin,
            )
            if cert["certified"] and cert["iv_certified"]:
                best_pwl = B_pwl
                best_cert = cert

    assert best_pwl is not None and best_cert is not None and best_cert["certified"] and best_cert["iv_certified"], (
        f"Staying barrier failed certification on [{b_m},{h_m}]: {best_cert}"
    )
    return best_pwl, best_cert, (fx, fy, fu)


def _prune_staying_barrier(
    B_pwl: Dict[str, object],
    Psi_pwl: Dict[str, object],
    W_pwl: Dict[str, object],
    b_m: float,
    h_m: float,
    A_hi: float,
    q_hi: float,
    b_lo: float,
    b_hi: float,
    e_lo: float,
    e_hi: float,
    target_T: int,
    min_knots: int = 16,
) -> Tuple[Dict[str, object], Dict[str, object]]:
    """Deterministic greedy slope-jump pruning of CEGIS-LP staying barrier."""
    cur_pwl = B_pwl
    cur_cert = verify_staying_barrier_bb(cur_pwl, A_hi=A_hi, q_hi=q_hi, b_lo=b_lo, b_hi=b_hi, e_lo=e_lo, e_hi=e_hi, b_m=b_m, h_m=h_m)
    k_cur = cur_pwl["ks"].copy()
    attempts = 0
    while len(k_cur) > min_knots and attempts < 12:
        sl = np.diff(cur_pwl["vals"]) / np.diff(np.log(k_cur))
        jump = np.abs(np.diff(sl))
        order = np.argsort(jump)
        pruned = False
        for idx_int in order[:3]:
            attempts += 1
            drop_i = int(idx_int) + 1
            k_try = np.delete(k_cur, drop_i)
            try:
                p_try, c_try, _ = _cegis_lp_staying_barrier(
                    b_m, h_m, A_hi, q_hi, b_lo, b_hi, e_lo, e_hi,
                    fixed_knots=k_try, target_W_pwl=W_pwl, max_rounds=4,
                )
                T_try, _, _ = certify_staying_deadline_interval(p_try, Psi_pwl, W_pwl, b_hi, b_m, h_m)
                if T_try <= target_T and c_try["certified"] and c_try["iv_certified"]:
                    cur_pwl, cur_cert, k_cur = p_try, c_try, p_try["ks"].copy()
                    pruned = True
                    break
            except AssertionError:
                continue
        if not pruned:
            break
    return cur_pwl, cur_cert


# ---------------------------------------------------------------------------
# Case 1: Staying Barrier B_theta (24 moving knots, T <= 9) + CEGIS-LP Psi/W
# ---------------------------------------------------------------------------
def _extract_restricted_pwl(pwl: Dict[str, object], b_m: float, h_m: float, lift: float = 0.0) -> Dict[str, object]:
    """Extract exact sub-PWL on [b_m, h_m] with constant outer extensions s_lo=s_hi=0.0."""
    ks = [float(b_m)]
    for k in pwl["ks"]:
        kf = float(k)
        if b_m < kf < h_m:
            ks.append(kf)
    ks.append(float(h_m))
    k_arr = np.array(sorted(set(ks)), dtype=np.float64)
    vals = eval_logpwl(pwl, k_arr) + lift
    return make_pwl_from_knots(k_arr, vals, 0.0, 0.0)


def _synth_nonstationary_chain(
    Psi_ref: Dict[str, object],
    W_ref: Dict[str, object],
    A_hi: float,
    q_hi: float,
    b_lo: float,
    b_hi: float,
    e_lo: float,
    e_hi: float,
    max_steps: int = 10,
) -> Dict[str, object]:
    """Synthesize finite-horizon non-stationary Bellman barriers J_0 >= Psi, ..., J_K < W on M."""
    t0 = time.time()
    J0 = _extract_restricted_pwl(Psi_ref, B_M, H_M, lift=1e-10)
    J_list = [J0]
    certs = []
    T_nonstat = None
    m_j0, m_wk = None, None
    for step in range(1, max_steps + 1):
        Jk, ck, _ = _cegis_lp_staying_barrier(
            B_M, H_M, A_hi, q_hi, b_lo, b_hi, e_lo, e_hi,
            B_ev_pwl=J_list[-1], n_knots=44, max_rounds=8, tol_bb=2e-4,
        )
        J_list.append(Jk)
        certs.append({"step": step, "d_ub_iv": float(ck["d_ub_iv"]), "knots": int(len(Jk["ks"]))})
        ok, dj0, dwk = certify_nonstationary_deadline_interval(Psi_ref, W_ref, J_list, B_M, H_M)
        if ok:
            T_nonstat = step
            m_j0, m_wk = dj0, dwk
            break
    assert T_nonstat is not None, f"Non-stationary chain failed to close in {max_steps} steps (last dwk={dwk})"
    return {
        "T_nonstat": int(T_nonstat),
        "min_J0_minus_Psi_lo": float(m_j0),
        "min_W_minus_JK_lo": float(m_wk),
        "J_nets": [pwl_to_dict(j) for j in J_list],
        "step_certs": certs,
        "synth_sec": float(time.time() - t0),
    }


def _near_skiba_subbox_worker(task: Tuple[int, float, float, float, float, float, List[Tuple[float, float]], np.ndarray]) -> Dict[str, object]:
    sb_idx, aL_s, aU_s, bL_s, bR_s, b_ext, cascade_bounds, k_t_g = task
    V_up_g, _, _ = _solve_teacher_vfi(aU_s, Q_MAX, bL_s, ETA_MIN, ETA_MAX, True, k_t_g)

    def _init_psi_sub(k):
        ka = np.asarray(k, dtype=np.float64)
        s_l = _safe_s_lo(ETA_MIN, bL_s)
        d_h = _safe_D_hi(ETA_MAX, bR_s)
        v = np.interp(np.log(np.clip(ka, 1e-4, 90.0)), np.log(k_t_g), V_up_g)
        v = np.where(ka < 1e-4, V_up_g[0] + s_l * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 90.0, V_up_g[-1] + d_h * np.log(ka / 90.0), v)

    l0_cand = np.linspace(0.145, 0.30, 20)
    l0_ext = 0.17
    best_ep_sc = 1e30
    for l_try in l0_cand:
        ep_try = E_plus_exact(aU_s, Q_MAX, b_ext, b_ext, float(l_try))
        if ep_try < best_ep_sc:
            best_ep_sc = ep_try
            l0_ext = float(l_try)

    req_b_ext = (ETA_MAX / _min_c_E_plus(aL_s, Q_MIN, b_ext, b_ext, l0_ext)) / bL_s + 0.3
    req_b_H = (ETA_MAX / _min_c_E_plus(aL_s, Q_MIN, H_M, H_M, 0.57)) / bL_s + 0.3

    Psi_sub, cert_Psi, _ = _cegis_lp_super_barrier(
        aU_s, bL_s, bR_s, Q_MAX, ETA_MIN, ETA_MAX, 1e-4, 90.0,
        init_vals_fn=_init_psi_sub,
        pre_b_points=[(b_ext, req_b_ext), (H_M, req_b_H)],
        b_m_slope=b_ext,
        max_cegis_rounds=14,
        tol_bb=2.5e-4,
    )
    W_sub, kp_sub, L_sub, cert_W, _ = _cegis_lp_witness(
        aL_s, Q_MIN, bL_s, bR_s, ETA_MIN, ETA_MAX, (b_ext, 5.5),
        b_m_slope=b_ext, max_cegis_rounds=10,
    )

    psi_ext_hi = float(iv_eval_logpwl(Psi_sub, Interval(str(b_ext))).to_float_bounds()[1])
    psi_28_hi = float(iv_eval_logpwl(Psi_sub, Interval(str(H_M))).to_float_bounds()[1])
    ok_db, m_db, _ = verify_derivative_below_bound(Psi_sub, b_ext, bL_s, aL_s, Q_MIN, b_ext, l0_ext)
    ok_dh, m_dh, _ = verify_derivative_below_bound(Psi_sub, H_M, bL_s, aL_s, Q_MIN, H_M, 0.57)
    assert ok_db and ok_dh, f"Cascade <b_ext/<h failed at sb={sb_idx}: {m_db}, {m_dh}"

    ex_ext = verify_adverse_exit_bb(W_sub, psi_ext_hi, aU_s, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, b_ext, l0_ext, (b_ext, H_M), tol=1.5e-4)
    ex_H1 = verify_adverse_exit_bb(W_sub, psi_28_hi, aU_s, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80), tol=1.5e-4)
    kp80 = float(eval_logpwl(kp_sub, np.array([0.80]))[0])
    L80 = float(np.clip(eval_logpwl(L_sub, np.array([0.80]))[0], 0.0, 0.999))
    Wkp80_lo = float(iv_eval_logpwl(W_sub, Interval(kp80)).to_float_bounds()[0])
    ok_H2, ex_H2_lb = verify_H2_global_interval(W_sub, kp80, L80, Wkp80_lo, psi_28_hi, aL_s, aU_s, Q_MIN, Q_MAX, bL_s, bR_s)
    assert ex_ext["certified"] and ex_ext["iv_certified"] and ex_H1["certified"] and ok_H2, (
        f"Cascade exit failed at sb={sb_idx}: ext={ex_ext['m_lb_iv']}, H1={ex_H1['m_lb_iv']}, H2={ex_H2_lb}"
    )

    stages = []
    T_total_sub = 0
    for bk_lo, bk_hi in cascade_bounds:
        Bj, cBj, _ = _cegis_lp_staying_barrier(
            bk_lo, bk_hi, aU_s, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX,
            n_knots=26, max_rounds=10, target_W_pwl=W_sub,
        )
        Tj, inf_j, sup_j = certify_staying_deadline_interval(Bj, Psi_sub, W_sub, bR_s, bk_lo, bk_hi)
        T_total_sub += int(Tj)
        stages.append({
            "b_m": float(bk_lo),
            "h_m": float(bk_hi),
            "T_j": int(Tj),
            "inf_W_B_lo": float(inf_j),
            "sup_Psi_B_hi": float(sup_j),
            "d_ub_iv": float(cBj["d_ub_iv"]),
            "B_net": pwl_to_dict(Bj),
        })

    return {
        "sb_idx": int(sb_idx),
        "aL": aL_s, "aU": aU_s,
        "bL": bL_s, "bR": bR_s,
        "l0_ext": float(l0_ext),
        "T_total": int(T_total_sub),
        "exit_ext_lb_iv": float(ex_ext["m_lb_iv"]),
        "exit_H1_lb_iv": float(ex_H1["m_lb_iv"]),
        "exit_H2_lb_iv": float(ex_H2_lb),
        "slope_bext_margin": float(m_db),
        "slope_h_margin": float(m_dh),
        "d_ub_Psi_iv": float(cert_Psi["d_ub_iv"]),
        "d_ub_W_iv": float(cert_W["d_ub_iv"]),
        "Psi_net": pwl_to_dict(Psi_sub),
        "W_net": pwl_to_dict(W_sub),
        "kp_net": pwl_to_dict(kp_sub),
        "L_net": pwl_to_dict(L_sub),
        "stages": stages,
    }


def _synth_near_skiba_cascade(b_ext: float = 0.0025) -> Dict[str, object]:
    """
    Extend explicit certified escape deadline from b_ext (0.0025, MR Thm. 8 Skiba bound)
    all the way to H = [0.28, oo) over 4A x 4beta = 16 subboxes covering P.
    """
    t0 = time.time()
    a_edges = np.linspace(A_MIN, A_MAX, 5)
    b_edges = np.linspace(BETA_MIN, BETA_MAX, 5)
    cascade_bounds = [
        (b_ext, 0.006),
        (0.006, 0.015),
        (0.015, 0.040),
        (0.040, 0.100),
        (0.100, 0.280),
    ]
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.015, 42, endpoint=False),
        np.geomspace(0.015, 0.28, 40, endpoint=False),
        np.geomspace(0.28, 90.0, 44),
    ]))
    tasks = []
    sb_idx = 0
    for ia in range(4):
        for jb in range(4):
            tasks.append((sb_idx, float(a_edges[ia]), float(a_edges[ia + 1]), float(b_edges[jb]), float(b_edges[jb + 1]), b_ext, cascade_bounds, k_t_g))
            sb_idx += 1

    with ProcessPoolExecutor(max_workers=min(12, os.cpu_count() or 4)) as pool:
        subbands = list(pool.map(_near_skiba_subbox_worker, tasks))
    subbands.sort(key=lambda r: r["sb_idx"])

    T_total_worst = max(sb["T_total"] for sb in subbands)
    min_exit_ext = min(sb["exit_ext_lb_iv"] for sb in subbands)
    return {
        "b_ext": float(b_ext),
        "cascade_bounds": [[float(a), float(b)] for a, b in cascade_bounds],
        "n_subboxes": 16,
        "partition": "4A x 4beta",
        "T_total_worst": int(T_total_worst),
        "min_exit_ext_lb_iv": float(min_exit_ext),
        "synth_sec": float(time.time() - t0),
        "subbands": subbands,
    }


def synth_case_1(seed: int) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 1: Pure CEGIS-LP B_theta (+Pruning), Near-Skiba Cascade & Non-Stationary")
    print("=" * 72)
    t0 = time.time()

    # 1A: Pure CEGIS-LP (Psi, W) first so staying barrier + pruning directly optimize inf(W - B)
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.015, 36, endpoint=False),
        np.geomspace(0.015, 0.28, 40, endpoint=False),
        np.geomspace(0.28, 90.0, 44),
    ]))
    V_up_g, _, _ = _solve_teacher_vfi(A_MAX, Q_MAX, BETA_MIN, ETA_MIN, ETA_MAX, True, k_t_g)
    s_lo_1 = _safe_s_lo(ETA_MIN, BETA_MIN)
    D_hi_1 = _safe_D_hi(ETA_MAX, BETA_MAX)

    def _init_psi_1(k):
        ka = np.asarray(k, dtype=np.float64)
        v = np.interp(np.log(np.clip(ka, 1e-4, 90.0)), np.log(k_t_g), V_up_g)
        v = np.where(ka < 1e-4, V_up_g[0] + s_lo_1 * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 90.0, V_up_g[-1] + D_hi_1 * np.log(ka / 90.0), v)

    Psi_pwl, cert_Psi, hist_Psi = _cegis_lp_super_barrier(
        A_MAX, BETA_MIN, BETA_MAX, Q_MAX, ETA_MIN, ETA_MAX, 1e-4, 90.0,
        init_vals_fn=_init_psi_1,
    )
    W_pwl, kp_pwl, L_pwl, cert_W, hist_W = _cegis_lp_witness(
        A_MIN, Q_MIN, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, (B_M, 5.5),
    )

    # Pure deterministic CEGIS-LP Staying Barrier (unpruned 32 knots -> adaptive slope-jump pruning)
    t_lp0 = time.time()
    B_unpruned, cert_unp, _ = _cegis_lp_staying_barrier(
        B_M, H_M, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX,
        n_knots=32, target_W_pwl=W_pwl,
    )
    dt_unp = time.time() - t_lp0
    T_base_unp, _, _ = certify_case1_deadline_interval(B_unpruned, None, None, use_baseline_mr=True)
    T_full_unp, _, _ = certify_case1_deadline_interval(B_unpruned, Psi_pwl, W_pwl, use_baseline_mr=False)

    t_pr0 = time.time()
    if T_full_unp <= 5:
        B_pwl, cert = B_unpruned, cert_unp
    else:
        B_pwl, cert = _prune_staying_barrier(
            B_unpruned, Psi_pwl, W_pwl, B_M, H_M, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX,
            target_T=T_full_unp, min_knots=18,
        )
    dt_pr = time.time() - t_pr0
    B_net = LogReLUNetwork(B_M, H_M, hidden_sizes=(max(1, len(B_pwl["ks"]) - 2),), s_lo=0.0, s_hi=0.0, seed=seed)
    B_net.set_from_knots_values(B_pwl["ks"], B_pwl["vals"])

    # Continuous 50-digit Interval deadline checks (Fix 2)
    T_theta_base, inf_W_B_base, sup_Psi_B_base = certify_case1_deadline_interval(B_pwl, None, None, use_baseline_mr=True)
    T_theta_full, inf_W_B_cegis, sup_Psi_B_cegis = certify_case1_deadline_interval(B_pwl, Psi_pwl, W_pwl, use_baseline_mr=False)

    # Prop. 1* Part 2 slope condition on M0 = [0.05, 0.10]: Psi'(K) >= (B^(0))'(K) = 6.4234
    dPsi_M0_iv = iv_deriv_bounds_logpwl(Psi_pwl, Interval._raw(Decimal("0.05"), Decimal("0.10")))
    iv_C_max0 = Interval(str(Q_MAX)) * Interval("0.10") + iv_F_A(Interval(str(A_MAX)), Interval("0.10"), Interval("1")) - Interval("0.05")
    iv_slope0 = (Interval(str(ETA_MIN)) * Interval(str(Q_MIN))) / iv_C_max0
    assert dPsi_M0_iv.lo > iv_slope0.hi, f"Case 1 Psi' on M0 ({dPsi_M0_iv.lo}) <= (B^(0))' ({iv_slope0.hi})"
    min_dPsi_M0 = float(dPsi_M0_iv.to_float_bounds()[0])

    B_010 = float(eval_logpwl(B_pwl, np.array([B_M]))[0])
    B_028 = float(eval_logpwl(B_pwl, np.array([H_M]))[0])
    dt_1a = time.time() - t0
    print(f"  [1A Pure LP+Prune] B knots: {len(B_unpruned['ks'])}->{len(B_pwl['ks'])}, d_ub_iv={cert['d_ub_iv']:.6f} | B(0.10)={B_010:.4f}, B(0.28)={B_028:.4f}")
    print(f"  [1A Deadlines] T_theta={T_theta_base} (MR), T_full={T_theta_full} (CEGIS triple) | LP+prune time={dt_unp+dt_pr:.2f}s | min_dPsi_M0={min_dPsi_M0:.2f}")
    assert T_theta_base <= 9 and T_theta_full <= 9

    # Also record a compact fixed-grid 22-knot LP barrier for direct Adam comparison
    t_c0 = time.time()
    B_compact, cert_cmp, _ = _cegis_lp_staying_barrier(
        B_M, H_M, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX,
        fixed_knots=np.geomspace(B_M, H_M, 22), target_W_pwl=W_pwl, max_rounds=6,
    )
    dt_cmp = time.time() - t_c0
    T_base_cmp, _, _ = certify_case1_deadline_interval(B_compact, None, None, use_baseline_mr=True)
    T_full_cmp, _, _ = certify_case1_deadline_interval(B_compact, Psi_pwl, W_pwl, use_baseline_mr=False)

    # 1B: Near-Skiba Cascade down to b_ext = 0.0030 (4A x 4beta = 16 subboxes, closing 99.5% of Fig. 6 gap)
    cascade = _synth_near_skiba_cascade(0.0030)
    print(f"  [1B Near-Skiba Cascade] b_ext={cascade['b_ext']}, 16 (4A x 4beta) subboxes, T_total_worst={cascade['T_total_worst']}, min_exit_ext={cascade['min_exit_ext_lb_iv']:+.4f} ({cascade['synth_sec']:.1f}s)")

    # 1C: Finite-horizon non-stationary Bellman barriers on box P vs center point theta_0
    chain_box = _synth_nonstationary_chain(Psi_pwl, W_pwl, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX)
    V_up_c, _, _ = _solve_teacher_vfi(0.75, 0.92, 0.97, 0.70, 0.70, True, k_t_g)

    def _init_psi_c(k):
        ka = np.asarray(k, dtype=np.float64)
        s_c = _safe_s_lo(0.70, 0.97); d_c = _safe_D_hi(0.70, 0.97)
        v = np.interp(np.log(np.clip(ka, 1e-4, 90.0)), np.log(k_t_g), V_up_c)
        v = np.where(ka < 1e-4, V_up_c[0] + s_c * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 90.0, V_up_c[-1] + d_c * np.log(ka / 90.0), v)

    Psi_c, _, _ = _cegis_lp_super_barrier(0.75, 0.97, 0.97, 0.92, 0.70, 0.70, 1e-4, 90.0, init_vals_fn=_init_psi_c)
    W_c, _, _, _, _ = _cegis_lp_witness(0.75, 0.92, 0.97, 0.97, 0.70, 0.70, (B_M, 5.5))
    chain_center = _synth_nonstationary_chain(Psi_c, W_c, 0.75, 0.92, 0.97, 0.97, 0.70, 0.70)
    print(f"  [1C Non-stationary] T_full(stat,P)={T_theta_full} -> T_nonstat(P)={chain_box['T_nonstat']} -> T_nonstat(center)={chain_center['T_nonstat']} (vs VFI=4)")

    ablation = {
        "unpruned_lp": {
            "knots": int(len(B_unpruned["ks"])),
            "T_theta": int(T_base_unp),
            "T_full": int(T_full_unp),
            "d_ub_iv": float(cert_unp["d_ub_iv"]),
            "synth_sec": float(dt_unp),
        },
        "pruned_lp": {
            "knots": int(len(B_pwl["ks"])),
            "T_theta": int(T_theta_base),
            "T_full": int(T_theta_full),
            "d_ub_iv": float(cert["d_ub_iv"]),
            "synth_sec": float(dt_unp + dt_pr),
        },
        "compact_lp_22": {
            "knots": int(len(B_compact["ks"])),
            "T_theta": int(T_base_cmp),
            "T_full": int(T_full_cmp),
            "d_ub_iv": float(cert_cmp["d_ub_iv"]),
            "synth_sec": float(dt_cmp),
        },
    }

    return {
        "B_net": B_net.to_dict(),
        "B_pwl": pwl_to_dict(B_pwl),
        "Psi_net": pwl_to_dict(Psi_pwl),
        "W_net": pwl_to_dict(W_pwl),
        "kp_net": pwl_to_dict(kp_pwl),
        "L_net": pwl_to_dict(L_pwl),
        "ablation": ablation,
        "near_skiba_cascade": cascade,
        "nonstationary_chain": {
            "box_P": chain_box,
            "center_theta0": chain_center,
        },
        "metrics": {
            "d_ub_stay": float(cert["d_ub"]),
            "d_ub_stay_iv": float(cert["d_ub_iv"]),
            "B_010": B_010,
            "B_028": B_028,
            "T_theta_base": T_theta_base,
            "T_theta_full": T_theta_full,
            "T_nonstat_box": int(chain_box["T_nonstat"]),
            "T_nonstat_center": int(chain_center["T_nonstat"]),
            "cascade_b_ext": float(cascade["b_ext"]),
            "cascade_T_total": int(cascade["T_total_worst"]),
            "inf_W_B_base": inf_W_B_base,
            "sup_Psi_B_base": sup_Psi_B_base,
            "inf_W_B_cegis": inf_W_B_cegis,
            "sup_Psi_B_cegis": sup_Psi_B_cegis,
            "min_dPsi_M0": min_dPsi_M0,
            "knots_B": int(len(B_pwl["ks"])),
            "knots_Psi": int(len(Psi_pwl["ks"])),
            "knots_W": int(len(W_pwl["ks"])),
            "d_ub_Psi_iv": float(cert_Psi["d_ub_iv"]),
            "d_ub_W_iv": float(cert_W["d_ub_iv"]),
        },
    }


# ---------------------------------------------------------------------------
# Case 2: Continuous Ruin Hazard over p in [0%, 2.0%] (Contiguous beta_eff Bands)
# ---------------------------------------------------------------------------
def _case2_band_worker(task: Tuple[int, int, float, float, np.ndarray, float, float, float]) -> Tuple[int, str, Dict[str, object]]:
    j, n_bands, b_min, b_max, k_t_g, m_G, eta_max_c_M, eta_max_c_H = task
    C_max = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    R_hat = -0.996

    V_up_g, _, _ = _solve_teacher_vfi(A_MAX, Q_MAX, b_min, ETA_MIN, ETA_MAX, True, k_t_g)
    D_hi_p = _safe_D_hi(ETA_MAX, b_max)

    def _init_psi(k):
        ka = np.asarray(k, dtype=np.float64)
        v = np.interp(np.log(np.clip(ka, 1e-4, 60.0)), np.log(k_t_g), V_up_g)
        v = np.where(ka < 1e-4, V_up_g[0] + (ETA_MIN / (1.0 - b_min)) * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 60.0, V_up_g[-1] + D_hi_p * np.log(ka / 60.0), v)

    Psi_pwl, cert_Psi, _ = _cegis_lp_super_barrier(
        A_MAX, b_min, b_max, Q_MAX, ETA_MIN, ETA_MAX, 1e-4, 90.0,
        init_vals_fn=_init_psi,
        m_min_slope=m_G,
        pre_b_slope=(eta_max_c_M / b_min) + 0.15,
        pre_h_slope=(eta_max_c_H / b_min) + 0.05,
    )
    W_pwl, kp_pwl, L_pwl, cert_W, _ = _cegis_lp_witness(
        A_MIN, Q_MIN, b_min, b_max, ETA_MIN, ETA_MAX, (B_M, 5.5),
        m_req_M=m_G,
    )

    psi_10_iv = iv_eval_logpwl(Psi_pwl, Interval(str(B_M)))
    psi_28_iv = iv_eval_logpwl(Psi_pwl, Interval(str(H_M)))
    psi_10_hi = float(psi_10_iv.to_float_bounds()[1])
    psi_28_hi = float(psi_28_iv.to_float_bounds()[1])

    exit_M = verify_adverse_exit_bb(W_pwl, psi_10_hi, A_MAX, Q_MAX, b_min, b_max, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M))
    exit_H1 = verify_adverse_exit_bb(W_pwl, psi_28_hi, A_MAX, Q_MAX, b_min, b_max, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80))

    W80 = float(iv_eval_logpwl(W_pwl, Interval("0.80")).to_float_bounds()[0])
    kp80 = float(eval_logpwl(kp_pwl, np.array([0.80]))[0])
    L80 = float(np.clip(eval_logpwl(L_pwl, np.array([0.80]))[0], 0.0, 0.999))
    Wkp80_lo = float(iv_eval_logpwl(W_pwl, Interval(kp80)).to_float_bounds()[0])
    ok_H2, exitH2_lb = verify_H2_global_interval(
        W_pwl, kp80, L80, Wkp80_lo, psi_28_hi, A_MIN, A_MAX, Q_MIN, Q_MAX, b_min, b_max,
    )

    ok_db, margin_db, _ = verify_derivative_below_bound(Psi_pwl, B_M, b_min, A_MIN, Q_MIN, B_M, 0.44)
    ok_dh, margin_dh, _ = verify_derivative_below_bound(Psi_pwl, H_M, b_min, A_MIN, Q_MIN, H_M, 0.57)
    ok_wM, min_dW_M = verify_witness_slope_on_M(W_pwl, m_G)

    # Compute B_1 deadline T_star in 50-digit Interval arithmetic
    iv_one = Interval("1")
    iv_C_max = Interval(str(Q_MAX)) * Interval(str(H_M)) + iv_F_A(Interval(str(A_MAX)), Interval(str(H_M)), iv_one) - Interval(str(B_M))
    iv_bmin = Interval(str(b_min))
    iv_D2_p = (Interval(str(ETA_MIN)) * iv_bmin * Interval(str(Q_MIN)) * (Interval(str(H_M)) - Interval(str(B_M)))) / iv_C_max
    iv_B_star_p = (Interval("-0.996") - iv_D2_p) / (iv_one - iv_bmin)
    iv_m_G = (Interval(str(ETA_MIN)) * Interval(str(Q_MIN))) / iv_C_max
    iv_B1_b_p = iv_B_star_p - iv_m_G * (Interval(str(H_M)) - Interval(str(B_M)))
    iv_W10 = iv_eval_logpwl(W_pwl, Interval(str(B_M)))
    iv_marg_stay = iv_W10 - iv_B1_b_p
    iv_gap_exit = psi_28_iv - iv_B_star_p
    T_star = certify_affine_deadline_interval(iv_marg_stay, iv_gap_exit, b_max)
    W_10_lo = float(iv_W10.to_float_bounds()[0])
    marg_stay = float(iv_marg_stay.to_float_bounds()[0])

    # Synthesize and interval-certify 20-knot CEGIS-LP staying barrier B_cegis on ALL 60 bands
    kB = np.geomspace(B_M, H_M, 20)
    zB = np.log(kB)
    dlB = np.diff(zB)
    nB = len(kB)
    gxB, gyB = np.meshgrid(kB, kB, indexing="ij")
    fxB, fyB = gxB.ravel(), gyB.ravel()
    feas_B = (Q_MAX * fxB + F_A(A_MAX, fxB, 0.999) - fyB) > 1e-4
    fxB, fyB = fxB[feas_B], fyB[feas_B]
    _, fuB = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, fxB, fyB, is_upper=True)
    c_B_obj = np.ones(nB, dtype=np.float64) / nB
    A_B_mon = _monotone_diff_sparse(nB)
    b_B_mon = -0.02 * kB[1:] * dlB
    B_pwl_p2 = None
    cert_B2 = None
    for _rnd_B in range(8):
        MxB, _ = _eval_pwl_basis_sparse(zB, np.log(fxB), 0.0, 0.0)
        MyB, _ = _eval_pwl_basis_sparse(zB, np.log(fyB), 0.0, 0.0)
        A_B = sp.vstack([A_B_mon, b_min * MyB - MxB, b_max * MyB - MxB], format="csc")
        b_B = np.concatenate([b_B_mon, -(fuB + 5e-4), -(fuB + 5e-4)])
        res_B = linprog(c_B_obj, A_ub=A_B, b_ub=b_B, bounds=[(-200.0, 200.0)] * nB, method="highs")
        assert res_B.success, f"Case 2 j={j} CEGIS-LP B_theta failed: {res_B.message}"
        B_pwl_p2 = make_pwl_from_knots(kB, res_B.x, 0.0, 0.0)
        cert_B2 = verify_staying_barrier_bb(B_pwl_p2, b_lo=b_min, b_hi=b_max, tol=2e-4)
        if cert_B2["certified"] and cert_B2["iv_certified"]:
            break
        for cx, cy, _, _ in cert_B2["counterexamples"][:12]:
            _, cu = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, np.array([cx]), np.array([cy]), is_upper=True)
            if cu[0] > -1e8:
                fxB = np.append(fxB, cx); fyB = np.append(fyB, cy); fuB = np.append(fuB, float(cu[0]))
    if not (cert_B2["certified"] and cert_B2["iv_certified"]):
        shift_B = (max(cert_B2["d_ub"], cert_B2["d_ub_iv"]) + 3e-4) / (1.0 - b_max)
        B_pwl_p2 = make_pwl_from_knots(kB, res_B.x + shift_B, 0.0, 0.0)
        cert_B2 = verify_staying_barrier_bb(B_pwl_p2, b_lo=b_min, b_hi=b_max, tol=2e-4)
    assert B_pwl_p2 is not None and cert_B2["certified"] and cert_B2["iv_certified"], f"B_pwl_p2 failed at j={j}: {cert_B2}"
    T_star_cegis, _, _ = certify_staying_deadline_interval(B_pwl_p2, Psi_pwl, W_pwl, b_max=b_max)
    assert T_star_cegis <= 20, f"Expected T_star_cegis <= 20 at j={j}, got {T_star_cegis}"
    B_cegis_dict = pwl_to_dict(B_pwl_p2)

    assert cert_Psi["d_ub"] <= 0.0 and cert_Psi["iv_certified"]
    assert cert_W["certified"] and cert_W["iv_certified"]
    assert ok_wM and ok_db and ok_dh
    assert exit_M["certified"] and exit_M["iv_certified"]
    assert exit_H1["certified"] and exit_H1["iv_certified"]
    assert ok_H2 and marg_stay > 0.0

    p_lo_eff = max(0.0, 1.0 - b_max / BETA_MAX)
    p_hi_eff = min(0.02, 1.0 - b_min / BETA_MIN)
    key = f"b_{b_min:.6f}_{b_max:.6f}"
    rec = {
        "b_min": b_min,
        "b_max": b_max,
        "p_lo": p_lo_eff,
        "p_hi": p_hi_eff,
        "Psi_net": pwl_to_dict(Psi_pwl),
        "W_net": pwl_to_dict(W_pwl),
        "kp_net": pwl_to_dict(kp_pwl),
        "L_net": pwl_to_dict(L_pwl),
        "metrics": {
            "knots_Psi": int(len(Psi_pwl["ks"])),
            "knots_W": int(len(W_pwl["ks"])),
            "psi_10": psi_10_hi,
            "psi_28": psi_28_hi,
            "W_10": W_10_lo,
            "W_80": W80,
            "marg_stay": marg_stay,
            "exitM_lb_iv": float(exit_M["m_lb_iv"]),
            "exitH1_lb_iv": float(exit_H1["m_lb_iv"]),
            "exitH2_lb_iv": float(exitH2_lb),
            "min_dW_M": float(min_dW_M),
            "slope_b_margin": float(margin_db),
            "slope_h_margin": float(margin_dh),
            "T_star": T_star,
            "T_star_cegis": T_star_cegis,
            "d_ub_Psi_raw": float(cert_Psi["d_ub"]),
            "d_ub_Psi_iv": float(cert_Psi["d_ub_iv"]),
            "d_ub_W_iv": float(cert_W["d_ub_iv"]),
        },
    }
    if B_cegis_dict is not None:
        rec["B_cegis_net"] = B_cegis_dict
    return j, key, rec


def synth_case_2(seed: int) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 2: Pure CEGIS-LP Continuous Ruin Hazard over p in [0%, 2.0%]")
    print("=" * 72)
    C_max = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    m_G = (ETA_MIN * Q_MIN) / C_max

    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 20, endpoint=False),
        np.geomspace(0.0012, 0.0050, 50, endpoint=False),
        np.geomspace(0.0050, 0.025, 24, endpoint=False),
        np.geomspace(0.025, 0.25, 40, endpoint=False),
        np.geomspace(0.25, 60.0, 80),
    ]))
    eta_max_c_M = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, B_M, B_M, 0.44)
    eta_max_c_H = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, H_M, H_M, 0.57)

    # 60 contiguous beta_eff = beta*(1-p) bands matched to local margin slope d(V_lo - B1)/db
    edges_b = np.concatenate([
        np.linspace(BETA_MIN * 0.98, BETA_MAX * 0.98, 7),         # 6 bands, width 0.000033 (p=2.0% corner)
        np.linspace(BETA_MAX * 0.98, 0.9525, 13)[1:],             # 12 bands, width 0.000150
        np.linspace(0.9525, 0.9620, 21)[1:],                      # 20 bands, width 0.000475
        np.linspace(0.9620, BETA_MAX, 23)[1:],                    # 22 bands, width 0.000368
    ])
    b_bands = [(float(edges_b[j]), float(edges_b[j + 1])) for j in range(len(edges_b) - 1)]
    n_b = len(b_bands)
    tasks = [
        (j, n_b, b_lo, b_hi, k_t_g, m_G, eta_max_c_M, eta_max_c_H)
        for j, (b_lo, b_hi) in enumerate(b_bands)
    ]

    bands_out: Dict[str, object] = {}
    results_ordered: List[Tuple[int, str, Dict[str, object]]] = []
    n_workers2 = min(12, os.cpu_count() or 4)
    pbar2 = ProgressBar(f"Caso 2 | {n_b} bandas beta_eff", n_b, min_interval_sec=1.0)
    with ProcessPoolExecutor(max_workers=n_workers2) as pool:
        futs = [pool.submit(_case2_band_worker, t) for t in tasks]
        for fut in as_completed(futs):
            res = fut.result()
            results_ordered.append(res)
            pbar2.update(1, suffix=f"banda #{res[0]+1}")

    results_ordered.sort(key=lambda t: t[0])
    for j, key, rec in results_ordered:
        bands_out[key] = rec
        mt = rec["metrics"]
        if j in (0, 6, 17, 37, n_b - 1) or j % 8 == 0:
            extra = f", T*_cegis={mt['T_star_cegis']}" if mt.get("T_star_cegis") is not None else ""
            print(
                f"  band {j+1:2d}/{n_b} b=[{rec['b_min']:.6f},{rec['b_max']:.6f}] | "
                f"knots=({mt['knots_Psi']:3d},{mt['knots_W']:2d}) | "
                f"d_ub_iv={mt['d_ub_Psi_iv']:+.5f} | stay={mt['marg_stay']:5.3f}, "
                f"M={mt['exitM_lb_iv']:+.3f}, H1={mt['exitH1_lb_iv']:+.3f}, H2={mt['exitH2_lb_iv']:+.3f} | T*={mt['T_star']:2d}{extra}",
                flush=True,
            )

    bot_key = results_ordered[0][1]
    assert bands_out[bot_key]["metrics"]["T_star"] <= 94, (
        f"Expected T*(2%) <= 94, got {bands_out[bot_key]['metrics']['T_star']}"
    )
    return bands_out


# ---------------------------------------------------------------------------
# Case 3: Coupled 2-State Markov System (G, B) + Pure CEGIS-LP 32 Subboxes
# ---------------------------------------------------------------------------
def _solve_markov_teacher(
    p: float, A_G: float, A_B: float, qv: float, bv: float, eL: float, eU: float,
    is_upper: bool, k_grid: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    lk_g = np.log(k_grid)
    s_lo = eL / (1.0 - bv)
    D_hi = 2.5
    Ls = np.unique(np.concatenate([[0.0], np.geomspace(1e-7, 1e-4, 10, endpoint=False), np.geomspace(1e-4, 0.1, 16, endpoint=False), np.linspace(0.1, 0.997, 64)]))
    ss = np.unique(np.concatenate([np.linspace(0.15, 0.90, 14, endpoint=False), 1.0 - np.geomspace(2e-5, 0.10, 68)]))

    def _u_grid(Av):
        Y = qv * k_grid[:, None] + F_A(Av, k_grid[:, None], Ls[None, :])
        c = np.maximum(Y[:, :, None] * (1.0 - ss[None, None, :]), 1e-30)
        y = Y[:, :, None] * ss[None, None, :]
        ec = np.where(c < 1.0, eL, eU)
        ua = ec * np.log(c) + (1.0 - eL) * np.log(1.0 - Ls[None, :, None])
        ub = ec * np.log(c) + (1.0 - eU) * np.log(1.0 - Ls[None, :, None])
        u = np.maximum(ua, ub) if is_upper else np.minimum(ua, ub)
        if not is_upper:
            u = np.where(y <= k_grid[-1] * 0.995, u, -1e9)
        return y, u

    yG, uG = _u_grid(A_G)
    yB, uB = _u_grid(A_B)
    V_cake0 = (eL / (1.0 - bv)) * (math.log(max((1.0 - bv) * qv, 1e-12)) + (bv / (1.0 - bv)) * math.log(max(bv * qv, 1e-12)))
    VG = np.where(k_grid > 0.0014, -35.0, V_cake0 + s_lo * lk_g)
    VB = VG.copy() - 4.0

    def _interp(kp_arr, Va):
        lk = np.log(np.maximum(kp_arr, 1e-300))
        r = np.interp(np.clip(lk, lk_g[0], lk_g[-1]), lk_g, Va)
        r = np.where(kp_arr < k_grid[0], Va[0] + s_lo * (lk - lk_g[0]), r)
        return np.where(kp_arr > k_grid[-1], Va[-1] + D_hi * (lk - lk_g[-1]), r)

    inv_phi_m = (math.sqrt(5.0) - 1.0) / 2.0
    ym_G = yG[:, -1, -1]
    ym_B = yB[:, -1, -1]
    kpG = kpB = LG = LB = np.zeros_like(k_grid)
    for it_m in range(150):
        EVG = (1.0 - p) * VG + p * VB
        EVB = P_REC * VG + (1.0 - P_REC) * VB
        totG = (uG + bv * _interp(yG, EVG)).reshape(len(k_grid), -1)
        totB = (uB + bv * _interp(yB, EVB)).reshape(len(k_grid), -1)
        iG = np.argmax(totG, axis=1); iB = np.argmax(totB, axis=1)
        iLG, iSG = iG // len(ss), iG % len(ss)
        iLB, iSB = iB // len(ss), iB % len(ss)
        VGn = totG[np.arange(len(k_grid)), iG]
        VBn = totB[np.arange(len(k_grid)), iB]
        kpG, LG = yG[np.arange(len(k_grid)), iLG, iSG], Ls[iLG]
        kpB, LB = yB[np.arange(len(k_grid)), iLB, iSB], Ls[iLB]
        uGp, uBp = uG[np.arange(len(k_grid)), iLG, iSG], uB[np.arange(len(k_grid)), iLB, iSB]
        if not is_upper and it_m >= 20:
            def _ref_st(Av_s, ym_s, kp_s, EV_s, L_cur, u_cur, V_cur):
                lo_k = np.maximum(k_grid[0], 0.92 * kp_s)
                hi_k = np.maximum(lo_k * (1.0 + 1e-9), np.minimum(np.minimum(ym_s * (1.0 - 1e-7), k_grid[-1] * 0.995), 1.08 * kp_s))
                x1 = hi_k - inv_phi_m * (hi_k - lo_k)
                x2 = lo_k + inv_phi_m * (hi_k - lo_k)
                _, u1 = _golden_L_vec(Av_s, qv, eL, eU, k_grid, x1, is_upper=False)
                _, u2 = _golden_L_vec(Av_s, qv, eL, eU, k_grid, x2, is_upper=False)
                f1, f2 = u1 + bv * _interp(x1, EV_s), u2 + bv * _interp(x2, EV_s)
                for _g in range(10):
                    mr = f1 < f2
                    lo_k = np.where(mr, x1, lo_k); hi_k = np.where(mr, hi_k, x2)
                    x1n = np.where(mr, x2, hi_k - inv_phi_m * (hi_k - lo_k))
                    x2n = np.where(mr, lo_k + inv_phi_m * (hi_k - lo_k), x1)
                    _, u1n = _golden_L_vec(Av_s, qv, eL, eU, k_grid, x1n, is_upper=False)
                    _, u2n = _golden_L_vec(Av_s, qv, eL, eU, k_grid, x2n, is_upper=False)
                    f1n = np.where(mr, f2, u1n + bv * _interp(x1n, EV_s))
                    f2n = np.where(mr, u2n + bv * _interp(x2n, EV_s), f1)
                    x1, x2, f1, f2 = x1n, x2n, f1n, f2n
                kp_r = np.where(f1 > f2, x1, x2)
                L_r, u_r = _golden_L_vec(Av_s, qv, eL, eU, k_grid, kp_r, is_upper=False)
                V_r = u_r + bv * _interp(kp_r, EV_s)
                use_r = V_r > V_cur
                return np.where(use_r, kp_r, kp_s), np.where(use_r, L_r, L_cur), np.where(use_r, u_r, u_cur), np.where(use_r, V_r, V_cur)
            kpG, LG, uGp, VGn = _ref_st(A_G, ym_G, kpG, EVG, LG, uGp, VGn)
            kpB, LB, uBp, VBn = _ref_st(A_B, ym_B, kpB, EVB, LB, uBp, VBn)
        for _h in range(25):
            EVGn = (1.0 - p) * VGn + p * VBn
            EVBn = P_REC * VGn + (1.0 - P_REC) * VBn
            VGn = uGp + bv * _interp(kpG, EVGn)
            VBn = uBp + bv * _interp(kpB, EVBn)
        if max(np.max(np.abs(VGn - VG)), np.max(np.abs(VBn - VB))) < 1e-8:
            VG, VB = VGn, VBn
            break
        VG, VB = VGn, VBn
    return VG, VB, kpG, LG, kpB, LB


def _cegis_lp_coupled_markov_super_barrier(
    p: float,
    A_G_hi: float,
    A_B_hi: float,
    q_hi: float,
    bL: float,
    bR: float,
    eL: float,
    eU: float,
    k_grid_init: np.ndarray,
    VG_init: np.ndarray,
    VB_init: np.ndarray,
    m_G: float,
    m_B: float,
    req_b_G: float,
    req_b_B: float,
    req_h_G: float,
    req_h_B: float,
    max_rounds: int = 10,
    tol_bb: float = 3e-4,
) -> Tuple[Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object]]:
    """Joint coupled HiGHS LP CEGIS loop for (Psi_G, Psi_B) on (0, inf) x [bL, bR]."""
    k_lo, k_hi = 1e-4, 90.0
    s_lo = _safe_s_lo(eL, bL)
    D_hi = _safe_D_hi(eU, bR)

    k_knots = np.unique(np.concatenate([
        [k_lo],
        np.geomspace(k_lo, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.0040, 48, endpoint=False),
        np.geomspace(0.0040, 0.04, 24, endpoint=False),
        np.geomspace(0.04, B_M, 14, endpoint=False),
        np.linspace(B_M, H_M, 14, endpoint=False),
        np.geomspace(H_M, 1.0, 26, endpoint=False),
        np.geomspace(1.0, 6.0, 32, endpoint=False),
        np.geomspace(6.0, k_hi, 18),
        [1.0, k_hi],
    ]))

    def _init_vals(V_g: np.ndarray, k_q: np.ndarray) -> np.ndarray:
        kq = np.asarray(k_q, dtype=np.float64)
        v = np.interp(np.log(np.clip(kq, k_grid_init[0], k_grid_init[-1])), np.log(k_grid_init), V_g)
        v = np.where(kq < k_grid_init[0], V_g[0] + s_lo * np.log(kq / k_grid_init[0]), v)
        return np.where(kq > k_grid_init[-1], V_g[-1] + D_hi * np.log(kq / k_grid_init[-1]), v)

    Ls_act = np.concatenate([[0.0], np.geomspace(1e-7, 0.08, 16, endpoint=False), np.linspace(0.08, 0.996, 52)])
    ss_act = np.unique(np.concatenate([
        np.linspace(0.30, 0.70, 8, endpoint=False),
        np.linspace(0.70, 0.95, 45, endpoint=False),
        1.0 - np.geomspace(1.0e-4, 0.05, 30),
    ]))

    ce_xG, ce_LG, ce_sG = np.array([]), np.array([]), np.array([])
    ce_xB, ce_LB, ce_sB = np.array([]), np.array([]), np.array([])

    r_top_G = q_hi + F_A(A_G_hi, k_lo, 1.0) / k_lo
    r_top_B = q_hi + F_A(A_B_hi, k_lo, 1.0) / k_lo
    Y_end_G = q_hi * k_hi + A_G_hi * (2.0 ** 1.5)
    Y_end_B = q_hi * k_hi + A_B_hi * (2.0 ** 1.5)

    best_G = best_B = best_cG = best_cB = None
    last_G = last_B = None
    best_score = float("inf")

    for rnd in range(1, max_rounds + 1):
        n_k = len(k_knots)
        z_knots = np.log(k_knots)
        dlk = np.diff(z_knots)
        k_mids = np.sqrt(k_knots[:-1] * k_knots[1:])
        sk_mask = k_knots[1:] <= H_M + 1e-9
        k_q1 = np.exp(0.75 * z_knots[:-1][sk_mask] + 0.25 * z_knots[1:][sk_mask])
        k_q3 = np.exp(0.25 * z_knots[:-1][sk_mask] + 0.75 * z_knots[1:][sk_mask])
        k_eval = np.unique(np.concatenate([k_knots, k_mids, k_q1, k_q3]))

        def _col_for_state(Av: float, V_ref_arr: np.ndarray, pwl_self: Optional[Dict[str, object]], pwl_ev: Optional[Dict[str, object]], is_G: bool):
            v_s = _init_vals(V_ref_arr, k_eval) if pwl_self is None else eval_logpwl(pwl_self, k_eval)
            Ya = q_hi * k_eval[:, None] + F_A(Av, k_eval[:, None], Ls_act[None, :])
            ca = np.maximum((1.0 - ss_act[None, None, :]) * Ya[:, :, None], 1e-18)
            ya = np.maximum(ss_act[None, None, :] * Ya[:, :, None], 1e-18)
            ua = np.where(ca < 1.0, eL, eU) * np.log(ca) + (1.0 - eU) * np.log(1.0 - Ls_act[None, :, None])
            if pwl_ev is None:
                evG_a = _init_vals(VG_init, ya.ravel()).reshape(ya.shape)
                evB_a = _init_vals(VB_init, ya.ravel()).reshape(ya.shape)
                eva = ((1.0 - p) * evG_a + p * evB_a) if is_G else (P_REC * evG_a + (1.0 - P_REC) * evB_a)
            else:
                eva = eval_logpwl(pwl_ev, ya)
            ba = np.where(eva < 0.0, bL, bR)
            resa = (ua + ba * eva - v_s[:, None, None]).reshape(len(k_eval), -1)
            top_idx = np.argpartition(resa, -6, axis=1)[:, -6:].ravel()
            ax = np.repeat(k_eval, 6); aL = Ls_act[top_idx // len(ss_act)]; aS = ss_act[top_idx % len(ss_act)]
            xs_e = np.repeat(k_eval, 6)
            Ls_e = np.tile([0.0, 1e-6, 0.36, 0.58, 0.78, 0.95], len(k_eval))
            ss_e = np.tile([0.97, 0.92, 0.70, 0.88, 0.955, 0.9985], len(k_eval))
            cx, cL, cs = (ce_xG, ce_LG, ce_sG) if is_G else (ce_xB, ce_LB, ce_sB)
            px = np.concatenate([ax, xs_e, cx]) if len(cx) > 0 else np.concatenate([ax, xs_e])
            pL = np.concatenate([aL, Ls_e, cL]) if len(cx) > 0 else np.concatenate([aL, Ls_e])
            ps = np.concatenate([aS, ss_e, cs]) if len(cx) > 0 else np.concatenate([aS, ss_e])
            Yp = q_hi * px + F_A(Av, px, pL)
            cp = np.maximum((1.0 - ps) * Yp, 1e-18)
            yp = np.maximum(ps * Yp, 1e-18)
            up = np.where(cp < 1.0, eL, eU) * np.log(cp) + (1.0 - eU) * np.log(1.0 - pL)
            return np.log(px), np.log(yp), up

        evG_pwl_cur = None if last_G is None else make_pwl_from_knots(last_G["ks"], (1.0 - p) * last_G["vals"] + p * last_B["vals"], s_lo, D_hi)
        evB_pwl_cur = None if last_G is None else make_pwl_from_knots(last_G["ks"], P_REC * last_G["vals"] + (1.0 - P_REC) * last_B["vals"], s_lo, D_hi)
        zxG, zyG, uG = _col_for_state(A_G_hi, VG_init, last_G, evG_pwl_cur, True)
        zxB, zyB, uB = _col_for_state(A_B_hi, VB_init, last_B, evB_pwl_cur, False)

        MxG, _ = _eval_pwl_basis_sparse(z_knots, zxG, s_lo, D_hi)
        MyG, oyG = _eval_pwl_basis_sparse(z_knots, zyG, s_lo, D_hi)
        MxB, _ = _eval_pwl_basis_sparse(z_knots, zxB, s_lo, D_hi)
        MyB, oyB = _eval_pwl_basis_sparse(z_knots, zyB, s_lo, D_hi)

        # Sparse monotonicity matrices on G, B (M slopes + non-decreasing) + derivative bounds on EV_G, EV_B
        reqG = np.where((k_knots[:-1] >= B_M - 1e-9) & (k_knots[1:] <= H_M + 1e-9), m_G, 0.0)
        reqB = np.where((k_knots[:-1] >= B_M - 1e-9) & (k_knots[1:] <= H_M + 1e-9), m_B, 0.0)
        reqG = np.where(k_knots[:-1] >= 1.0, np.maximum(reqG, 0.135), reqG)
        reqB = np.where(k_knots[:-1] >= 1.0, np.maximum(reqB, 0.135), reqB)

        A_mon_base = _monotone_diff_sparse(n_k)
        Z_blk = sp.csr_matrix((n_k - 1, n_k), dtype=np.float64)
        A_mon_G = sp.hstack([A_mon_base, Z_blk], format="csr")
        A_mon_B = sp.hstack([Z_blk, A_mon_base], format="csr")
        req_log_G = np.maximum(reqG * k_knots[1:], np.where(k_knots[1:] <= 0.0012, s_lo, 0.0))
        req_log_B = np.maximum(reqB * k_knots[1:], np.where(k_knots[1:] <= 0.0012, s_lo, 0.0))
        b_mon_G = -np.maximum(req_log_G * dlk, 1e-6)
        b_mon_B = -np.maximum(req_log_B * dlk, 1e-6)

        req_evG = np.where(k_knots[:-1] < B_M - 1e-12, req_b_G, np.where(k_knots[:-1] < H_M - 1e-12, req_h_G, 0.0))
        req_evB = np.where(k_knots[:-1] < B_M - 1e-12, req_b_B, np.where(k_knots[:-1] < H_M - 1e-12, req_h_B, 0.0))
        mask_dG = req_evG > 0.0
        mask_dB = req_evB > 0.0
        A_evG = sp.hstack([(1.0 - p) * A_mon_base[mask_dG], p * A_mon_base[mask_dG]], format="csr")
        b_evG = -(req_evG[mask_dG] * k_knots[1:][mask_dG] * dlk[mask_dG])
        A_evB = sp.hstack([P_REC * A_mon_base[mask_dB], (1.0 - P_REC) * A_mon_base[mask_dB]], format="csr")
        b_evB = -(req_evB[mask_dB] * k_knots[1:][mask_dB] * dlk[mask_dB])

        # Sparse L1 log-slope total variation regularizer on lower asymptote & upper region for G and B
        tv_idx = np.where((k_knots[1:-1] >= 0.005) | (k_knots[1:-1] <= 0.0012))[0]
        n_tv = len(tv_idx)
        if n_tv > 0:
            j_arr = np.arange(n_tv, dtype=np.int32)
            inv_d0 = 1.0 / dlk[tv_idx]
            inv_d1 = 1.0 / dlk[tv_idx + 1]
            r_tvm = np.concatenate([
                np.repeat(4 * j_arr, 4), np.repeat(4 * j_arr + 1, 4),
                np.repeat(4 * j_arr + 2, 4), np.repeat(4 * j_arr + 3, 4),
            ])
            c_tvm = np.concatenate([
                np.column_stack([tv_idx, tv_idx + 1, tv_idx + 2, 2 * n_k + j_arr]).ravel(),
                np.column_stack([tv_idx, tv_idx + 1, tv_idx + 2, 2 * n_k + j_arr]).ravel(),
                np.column_stack([n_k + tv_idx, n_k + tv_idx + 1, n_k + tv_idx + 2, 2 * n_k + n_tv + j_arr]).ravel(),
                np.column_stack([n_k + tv_idx, n_k + tv_idx + 1, n_k + tv_idx + 2, 2 * n_k + n_tv + j_arr]).ravel(),
            ]).astype(np.int32)
            d_tvm = np.concatenate([
                np.column_stack([inv_d0, -(inv_d0 + inv_d1), inv_d1, np.full(n_tv, -1.0)]).ravel(),
                np.column_stack([-inv_d0, (inv_d0 + inv_d1), -inv_d1, np.full(n_tv, -1.0)]).ravel(),
                np.column_stack([inv_d0, -(inv_d0 + inv_d1), inv_d1, np.full(n_tv, -1.0)]).ravel(),
                np.column_stack([-inv_d0, (inv_d0 + inv_d1), -inv_d1, np.full(n_tv, -1.0)]).ravel(),
            ])
            A_tv_m = sp.csr_matrix((d_tvm, (r_tvm, c_tvm)), shape=(4 * n_tv, 2 * n_k + 2 * n_tv))
        else:
            A_tv_m = sp.csr_matrix((0, 2 * n_k), dtype=np.float64)
        b_tv_m = np.zeros(4 * n_tv, dtype=np.float64)

        M1, o1 = _eval_pwl_basis_sparse(z_knots, np.array([0.0]), s_lo, D_hi)
        c_obj_y = np.zeros(2 * n_k, dtype=np.float64)
        m_mask = (k_knots >= B_M - 1e-9) & (k_knots <= H_M + 1e-9)
        bm_mask = (k_knots >= 0.085) & (k_knots <= 0.125)
        hm_mask = (k_knots >= 0.25) & (k_knots <= 0.31)
        c_obj_y[:n_k][m_mask] = 0.45 / max(1, int(np.sum(m_mask)))
        c_obj_y[n_k:][m_mask] = 0.45 / max(1, int(np.sum(m_mask)))
        c_obj_y[:n_k][bm_mask] += 0.25 / max(1, int(np.sum(bm_mask)))
        c_obj_y[n_k:][bm_mask] += 0.25 / max(1, int(np.sum(bm_mask)))
        c_obj_y[:n_k][hm_mask] += 0.30 / max(1, int(np.sum(hm_mask)))
        c_obj_y[n_k:][hm_mask] += 0.30 / max(1, int(np.sum(hm_mask)))
        c_obj_y += 1e-3 / (2 * n_k)
        c_obj = np.concatenate([c_obj_y, np.full(2 * n_tv, 2.5e-4, dtype=np.float64)])
        lp_bounds_m = [(-2500.0, 2500.0)] * (2 * n_k) + [(0.0, None)] * (2 * n_tv)

        yG_cur = _init_vals(VG_init, k_knots) if last_G is None else eval_logpwl(last_G, k_knots)
        yB_cur = _init_vals(VB_init, k_knots) if last_B is None else eval_logpwl(last_B, k_knots)

        pxG = np.exp(zxG); pxB = np.exp(zxB)
        m_base_G = np.where(pxG >= 0.25, 0.0008, np.where(pxG >= 0.05, 0.0022, np.where(pxG >= 0.015, 0.0080, 0.018)))
        m_base_B = np.where(pxB >= 0.25, 0.0008, np.where(pxB >= 0.05, 0.0022, np.where(pxB >= 0.015, 0.0080, 0.018)))
        solved = False
        e_G_last = sp.csr_matrix(([-1.0], ([0], [n_k - 1])), shape=(1, 2 * n_k))
        e_B_last = sp.csr_matrix(([-1.0], ([0], [2 * n_k - 1])), shape=(1, 2 * n_k))
        for m_scale in (1.0, 0.65, 0.35, 0.15, 0.05):
            m_vec_G = m_scale * m_base_G
            m_vec_B = m_scale * m_base_B
            m_t_lo = m_scale * 0.018
            m_t_hi = m_scale * 0.0012
            yG_t, yB_t = yG_cur.copy(), yB_cur.copy()
            ok_pass = False
            for _sp in range(2):
                evG_y = (1.0 - p) * (MyG @ yG_t + oyG) + p * (MyG @ yB_t + oyG)
                evB_y = P_REC * (MyB @ yG_t + oyB) + (1.0 - P_REC) * (MyB @ yB_t + oyB)
                near0G = np.abs(evG_y) <= 1.5
                near0B = np.abs(evB_y) <= 1.5
                A_rows = [A_mon_G, A_mon_B, A_evG, A_evB]
                b_rows = [b_mon_G, b_mon_B, b_evG, b_evB]

                for bv_c, m_c in ((bL, (evG_y < 0.0) | near0G), (bR, (evG_y >= 0.0) | near0G)):
                    if np.any(m_c):
                        AG_c = sp.hstack([bv_c * (1.0 - p) * MyG[m_c] - MxG[m_c], bv_c * p * MyG[m_c]], format="csr")
                        A_rows.append(AG_c)
                        b_rows.append(-(uG[m_c] + bv_c * oyG[m_c] + m_vec_G[m_c]))
                for bv_c, m_c in ((bL, (evB_y < 0.0) | near0B), (bR, (evB_y >= 0.0) | near0B)):
                    if np.any(m_c):
                        AB_c = sp.hstack([bv_c * P_REC * MyB[m_c], bv_c * (1.0 - P_REC) * MyB[m_c] - MxB[m_c]], format="csr")
                        A_rows.append(AB_c)
                        b_rows.append(-(uB[m_c] + bv_c * oyB[m_c] + m_vec_B[m_c]))

                # Tails (lower & upper for G and B)
                for bv_t in (bL, bR):
                    c_slo = eL + bv_t * s_lo
                    s_lo_opt = (bv_t * s_lo) / c_slo
                    tlG = eL * math.log((1.0 - s_lo_opt) * k_lo) + bv_t * s_lo * math.log(s_lo_opt) + c_slo * math.log(r_top_G)
                    tlB = eL * math.log((1.0 - s_lo_opt) * k_lo) + bv_t * s_lo * math.log(s_lo_opt) + c_slo * math.log(r_top_B)
                    rG0 = sp.csr_matrix(([bv_t * (1.0 - p) - 1.0, bv_t * p], ([0, 0], [0, n_k])), shape=(1, 2 * n_k))
                    rB0 = sp.csr_matrix(([bv_t * P_REC, bv_t * (1.0 - P_REC) - 1.0], ([0, 0], [0, n_k])), shape=(1, 2 * n_k))
                    A_rows.extend([rG0, rB0])
                    b_rows.extend([np.array([-(tlG + m_t_lo)]), np.array([-(tlB + m_t_lo)])])

                    c_dhi = eU + bv_t * D_hi
                    s_hi_opt = (bv_t * D_hi) / c_dhi
                    thG_log = eU * math.log(1.0 - s_hi_opt) + bv_t * D_hi * math.log(s_hi_opt) + c_dhi * math.log(Y_end_G / k_hi) + eU * math.log(k_hi)
                    thB_log = eU * math.log(1.0 - s_hi_opt) + bv_t * D_hi * math.log(s_hi_opt) + c_dhi * math.log(Y_end_B / k_hi) + eU * math.log(k_hi)
                    rGe = sp.csr_matrix(([bv_t * (1.0 - p) - 1.0, bv_t * p], ([0, 0], [n_k - 1, 2 * n_k - 1])), shape=(1, 2 * n_k))
                    rBe = sp.csr_matrix(([bv_t * P_REC, bv_t * (1.0 - P_REC) - 1.0], ([0, 0], [n_k - 1, 2 * n_k - 1])), shape=(1, 2 * n_k))
                    A_rows.extend([rGe, rBe])
                    b_rows.extend([np.array([-(thG_log + m_t_hi)]), np.array([-(thB_log + m_t_hi)])])

                    # y < 1 upper tail at k_hi
                    rG1 = sp.hstack([bv_t * (1.0 - p) * M1, bv_t * p * M1], format="csr") + e_G_last
                    rB1 = sp.hstack([bv_t * P_REC * M1, bv_t * (1.0 - P_REC) * M1], format="csr") + e_B_last
                    A_rows.extend([rG1, rB1])
                    b_rows.extend([np.array([-(eU * math.log(Y_end_G) + bv_t * float(o1[0]) + m_t_hi)]),
                                   np.array([-(eU * math.log(Y_end_B) + bv_t * float(o1[0]) + m_t_hi)])])

                A_y_blk = sp.vstack(A_rows, format="csr")
                b_y_blk = np.concatenate(b_rows)
                if n_tv > 0:
                    A_full = sp.vstack([
                        sp.hstack([A_y_blk, sp.csr_matrix((A_y_blk.shape[0], 2 * n_tv), dtype=np.float64)], format="csr"),
                        A_tv_m,
                    ], format="csc")
                    b_full = np.concatenate([b_y_blk, b_tv_m])
                else:
                    A_full = A_y_blk.tocsc()
                    b_full = b_y_blk
                res = linprog(c_obj, A_ub=A_full, b_ub=b_full, bounds=lp_bounds_m, method="highs")
                if res.success:
                    yG_t = res.x[:n_k].copy()
                    yB_t = res.x[n_k:2 * n_k].copy()
                    ok_pass = True
                else:
                    ok_pass = False
                    break
            if ok_pass:
                yG_knots, yB_knots = yG_t, yB_t
                solved = True
                break
        assert solved, f"Coupled Markov CEGIS-LP failed at p={p}, round={rnd}"

        pG = make_pwl_from_knots(k_knots, yG_knots, s_lo, D_hi)
        pB = make_pwl_from_knots(k_knots, yB_knots, s_lo, D_hi)
        last_G, last_B = pG, pB
        evG_pwl = make_pwl_from_knots(k_knots, (1.0 - p) * yG_knots + p * yB_knots, s_lo, D_hi)
        evB_pwl = make_pwl_from_knots(k_knots, P_REC * yG_knots + (1.0 - P_REC) * yB_knots, s_lo, D_hi)

        cG = verify_super_barrier_bb(pG, evG_pwl, A_G_hi, bL, bR, q_hi=q_hi, eL=eL, eU=eU, tol=tol_bb)
        cB = verify_super_barrier_bb(pB, evB_pwl, A_B_hi, bL, bR, q_hi=q_hi, eL=eL, eU=eU, tol=tol_bb)
        score = float(eval_logpwl(pG, np.array([H_M]))[0] + eval_logpwl(pB, np.array([H_M]))[0])
        if cG["certified"] and cB["certified"] and score < best_score:
            best_G, best_B, best_cG, best_cB = pG, pB, cG, cB
            best_score = score
        if cG["certified"] and cB["certified"]:
            break

        ins_k = []
        for c_res, is_G in ((cG, True), (cB, False)):
            if not c_res["certified"]:
                ce_list_m = sorted(c_res["counterexamples"], key=lambda t: t[3], reverse=True)[:16]
                nx, nL, ns = [], [], []
                for cx, cL, cs, cv in ce_list_m:
                    if cv > -1e-4:
                        ins_k.append(float(np.clip(cx, k_lo * 1.05, k_hi * 0.95)))
                    for sc in (0.992, 1.0, 1.008):
                        nx.append(float(np.clip(cx * sc, k_lo, k_hi)))
                        nL.append(float(np.clip(cL, 0.0, 0.9999)))
                        ns.append(float(np.clip(cs, 1e-4, 0.99999)))
                if nx:
                    if is_G:
                        ce_xG = np.concatenate([ce_xG, np.array(nx)]); ce_LG = np.concatenate([ce_LG, np.array(nL)]); ce_sG = np.concatenate([ce_sG, np.array(ns)])
                    else:
                        ce_xB = np.concatenate([ce_xB, np.array(nx)]); ce_LB = np.concatenate([ce_LB, np.array(nL)]); ce_sB = np.concatenate([ce_sB, np.array(ns)])
        if ins_k and len(k_knots) < 320:
            cand_add = [ck for ck in ins_k if np.min(np.abs(np.log(k_knots) - math.log(ck))) > 2.0e-3]
            if cand_add:
                k_knots = np.unique(np.concatenate([k_knots, np.array(cand_add[:14])]))

    assert best_G is not None and best_cG["certified"] and best_cG["iv_certified"] and best_cB["certified"] and best_cB["iv_certified"], (
        f"Coupled Markov super-barrier failed at p={p}"
    )
    return best_G, best_B, best_cG, best_cB


def _cegis_lp_coupled_markov_witness(
    p: float,
    bL: float,
    bR: float,
    k_grid: np.ndarray,
    VG_init: np.ndarray,
    VB_init: np.ndarray,
    kpG_t: np.ndarray,
    LG_t: np.ndarray,
    kpB_t: np.ndarray,
    LB_t: np.ndarray,
    A_G_lo: float,
    A_B_lo: float,
    q_lo: float,
    eL: float,
    eU: float,
    m_G: float,
    m_B: float,
    max_rounds: int = 10,
    interval_check: bool = True,
) -> Tuple[Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object]]:
    """Joint coupled HiGHS LP CEGIS loop for (W_G, W_B) enforcing M-monotonicity W'_w >= m_w."""
    k_a, k_b = B_M, 5.5
    pol_idx = np.unique(np.concatenate([np.arange(0, len(k_grid), 2), [len(k_grid) - 1]]))
    kpG_pwl = make_pwl_from_knots(k_grid[pol_idx], np.clip(kpG_t[pol_idx], k_a * 1.005, k_b * 0.995), 0.0, 0.0)
    LG_pwl = make_pwl_from_knots(k_grid[pol_idx], np.clip(LG_t[pol_idx], 0.0, 0.985), 0.0, 0.0)
    kpB_pwl = make_pwl_from_knots(k_grid[pol_idx], np.clip(kpB_t[pol_idx], k_a * 1.005, k_b * 0.995), 0.0, 0.0)
    LB_pwl = make_pwl_from_knots(k_grid[pol_idx], np.clip(LB_t[pol_idx], 0.0, 0.985), 0.0, 0.0)

    k_knots = np.unique(np.concatenate([
        [k_a, H_M, 0.80, k_b],
        np.geomspace(k_a * 1.005, H_M * 0.995, 22, endpoint=False),
        np.geomspace(H_M * 1.005, 0.80 * 0.995, 22, endpoint=False),
        np.geomspace(0.80 * 1.005, k_b * 0.995, 22),
    ]))
    ce_kG = np.array([], dtype=np.float64)
    ce_kB = np.array([], dtype=np.float64)
    best_WG = best_WB = best_cG = best_cB = None

    for rnd in range(1, max_rounds + 1):
        n_w = len(k_knots)
        z_knots = np.log(k_knots)
        dlk = np.diff(z_knots)
        k_mids = np.sqrt(k_knots[:-1] * k_knots[1:])
        col_kG = np.unique(np.concatenate([k_knots, k_mids, np.sqrt(k_knots[:-1] * k_mids), np.sqrt(k_mids * k_knots[1:]), ce_kG]))
        col_kB = np.unique(np.concatenate([k_knots, k_mids, np.sqrt(k_knots[:-1] * k_mids), np.sqrt(k_mids * k_knots[1:]), ce_kB]))

        def _state_rows(Av, kp_p, L_p, ck):
            L_c = np.clip(eval_logpwl(L_p, ck), 0.0, 0.999)
            kp_c = np.clip(eval_logpwl(kp_p, ck), k_a, k_b)
            c_c = np.maximum(q_lo * ck + F_A(Av, ck, L_c) - kp_c, 1e-18)
            lc, ll = np.log(c_c), np.log(np.maximum(1.0 - L_c, 1e-18))
            u_c = np.minimum(eL * lc + (1.0 - eL) * ll, eU * lc + (1.0 - eU) * ll)
            Mx, _ = _eval_pwl_basis_sparse(z_knots, np.log(ck), 0.0, 0.0)
            My, _ = _eval_pwl_basis_sparse(z_knots, np.log(kp_c), 0.0, 0.0)
            return Mx, My, u_c

        MxG, MyG, uG = _state_rows(A_G_lo, kpG_pwl, LG_pwl, col_kG)
        MxB, MyB, uB = _state_rows(A_B_lo, kpB_pwl, LB_pwl, col_kB)

        reqG = np.where((k_knots[:-1] < H_M - 1e-12) & (k_knots[1:] > B_M + 1e-12), m_G, 0.0)
        reqB = np.where((k_knots[:-1] < H_M - 1e-12) & (k_knots[1:] > B_M + 1e-12), m_B, 0.0)
        A_mon_base = _monotone_diff_sparse(n_w)
        Z_blk = sp.csr_matrix((n_w - 1, n_w), dtype=np.float64)
        A_mon_G = sp.hstack([A_mon_base, Z_blk], format="csr"); b_mon_G = -(reqG * k_knots[1:] * dlk)
        A_mon_B = sp.hstack([Z_blk, A_mon_base], format="csr"); b_mon_B = -(reqB * k_knots[1:] * dlk)

        c_w = -np.ones(2 * n_w, dtype=np.float64) / (2 * n_w)
        c_w[0] -= 0.25; c_w[n_w] -= 0.25
        i_h = int(np.argmin(np.abs(k_knots - H_M)))
        c_w[i_h] -= 0.20; c_w[n_w + i_h] -= 0.25

        yG_t = np.interp(z_knots, np.log(k_grid), VG_init)
        yB_t = np.interp(z_knots, np.log(k_grid), VB_init)
        solved = False
        for m_trg in (2.0e-4, 8.0e-5, 3.0e-5):
            yGt, yBt = yG_t.copy(), yB_t.copy()
            ok_p = False
            for _sp in range(2):
                ewG_est = (1.0 - p) * (MyG @ yGt) + p * (MyG @ yBt)
                ewB_est = P_REC * (MyB @ yGt) + (1.0 - P_REC) * (MyB @ yBt)
                near0G = np.abs(ewG_est) <= 1.5
                near0B = np.abs(ewB_est) <= 1.5
                A_rows = [A_mon_G, A_mon_B]
                b_rows = [b_mon_G, b_mon_B]
                for bv_c, m_c in ((bR, (ewG_est < 0.0) | near0G), (bL, (ewG_est >= 0.0) | near0G)):
                    if np.any(m_c):
                        A_rows.append(sp.hstack([MxG[m_c] - bv_c * (1.0 - p) * MyG[m_c], -bv_c * p * MyG[m_c]], format="csr"))
                        b_rows.append(uG[m_c] - m_trg)
                for bv_c, m_c in ((bR, (ewB_est < 0.0) | near0B), (bL, (ewB_est >= 0.0) | near0B)):
                    if np.any(m_c):
                        A_rows.append(sp.hstack([-bv_c * P_REC * MyB[m_c], MxB[m_c] - bv_c * (1.0 - P_REC) * MyB[m_c]], format="csr"))
                        b_rows.append(uB[m_c] - m_trg)
                res = linprog(c_w, A_ub=sp.vstack(A_rows, format="csc"), b_ub=np.concatenate(b_rows), bounds=[(-500.0, 500.0)] * (2 * n_w), method="highs")
                if res.success:
                    yGt = res.x[:n_w].copy(); yBt = res.x[n_w:].copy()
                    ok_p = True
                else:
                    ok_p = False
                    break
            if ok_p:
                yG_knots, yB_knots = yGt, yBt
                solved = True
                break
        assert solved, f"Coupled Markov witness LP failed at p={p}"

        WG = make_pwl_from_knots(k_knots, yG_knots, 0.0, 0.0)
        WB = make_pwl_from_knots(k_knots, yB_knots, 0.0, 0.0)
        evWG = make_pwl_from_knots(k_knots, (1.0 - p) * yG_knots + p * yB_knots, 0.0, 0.0)
        evWB = make_pwl_from_knots(k_knots, P_REC * yG_knots + (1.0 - P_REC) * yB_knots, 0.0, 0.0)

        cG = verify_witness_subsolution_bb(WG, evWG, kpG_pwl, LG_pwl, A_G_lo, q_lo, bL, bR, eL=eL, eU=eU, k_domain=(k_a, k_b), tol=8e-5, interval_check=interval_check)
        cB = verify_witness_subsolution_bb(WB, evWB, kpB_pwl, LB_pwl, A_B_lo, q_lo, bL, bR, eL=eL, eU=eU, k_domain=(k_a, k_b), tol=8e-5, interval_check=interval_check)
        if cG["certified"] and cB["certified"]:
            best_WG, best_WB, best_cG, best_cB = WG, WB, cG, cB
            break

        ins_k = []
        for c_res, is_G in ((cG, True), (cB, False)):
            if not c_res["certified"]:
                nx = []
                for cx, cv in c_res["counterexamples"]:
                    if cv > -5e-5:
                        ins_k.append(float(np.clip(cx, k_a * 1.001, k_b * 0.999)))
                    for sc in (0.992, 1.0, 1.008):
                        nx.append(float(np.clip(cx * sc, k_a, k_b)))
                if nx:
                    if is_G:
                        ce_kG = np.unique(np.concatenate([ce_kG, np.array(nx)]))
                    else:
                        ce_kB = np.unique(np.concatenate([ce_kB, np.array(nx)]))
        if ins_k and len(k_knots) < 160:
            cand_add = [ck for ck in ins_k if np.min(np.abs(np.log(k_knots) - math.log(ck))) > 1.5e-3]
            if cand_add:
                k_knots = np.unique(np.concatenate([k_knots, np.array(cand_add[:12])]))

    assert best_WG is not None and best_cG["certified"] and best_cB["certified"], f"Coupled witness failed at p={p}"
    okG, slG = verify_witness_slope_on_M(best_WG, m_G)
    okB, slB = verify_witness_slope_on_M(best_WB, m_B)
    assert okG and okB, f"Markov witness M-slope failed: G={slG}, B={slB}"
    return best_WG, best_WB, kpG_pwl, LG_pwl, kpB_pwl, LB_pwl, best_cG, best_cB


def _cegis_lp_coupled_markov_staying_barrier(
    p: float,
    bL_s: float,
    bR_s: float,
    WG_pwl: Dict[str, object],
    WB_pwl: Dict[str, object],
    max_rounds: int = 10,
    tol_bb: float = 2e-4,
) -> Tuple[Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object]]:
    """
    Joint coupled HiGHS LP CEGIS synthesizer for compressed Markov staying barriers
    (B_G, B_B) on M = [0.10, 0.28) with constant extension s_hi = 0.0 on [0.28, oo).
    Maximizes uniform slack t_gap <= min_{w, i}(W_w(k_i) - B_w(k_i)).
    """
    kB = np.geomspace(B_M, H_M, 28)
    gx, gy = np.meshgrid(np.geomspace(B_M, H_M, 32), np.geomspace(B_M, H_M, 32), indexing="ij")
    fx0, fy0 = gx.ravel(), gy.ravel()
    feasG = (Q_MAX * fx0 + F_A(A_MAX, fx0, 0.9999) - fy0) > 1e-6
    feasB = (Q_MAX * fx0 + F_A(AB_MAX, fx0, 0.9999) - fy0) > 1e-6
    fxG, fyG = fx0[feasG], fy0[feasG]
    fxB, fyB = fx0[feasB], fy0[feasB]
    _, fuG = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, fxG, fyG, is_upper=True)
    _, fuB = _golden_L_vec(AB_MAX, Q_MAX, ETA_MIN, ETA_MAX, fxB, fyB, is_upper=True)

    best_BG = best_BB = best_cBG = best_cBB = None
    for rnd in range(1, max_rounds + 1):
        zB = np.log(kB)
        dlB = np.diff(zB)
        nB = len(kB)
        A_mon_1 = _monotone_diff_sparse(nB)
        Z_blk = sp.csr_matrix((nB - 1, nB), dtype=np.float64)
        A_mon_G = sp.hstack([A_mon_1, Z_blk], format="csr")
        A_mon_B = sp.hstack([Z_blk, A_mon_1], format="csr")
        b_mon_1 = -(0.02 * kB[1:] * dlB)

        MxG, _ = _eval_pwl_basis_sparse(zB, np.log(fxG), 0.0, 0.0)
        MyG, _ = _eval_pwl_basis_sparse(zB, np.log(fyG), 0.0, 0.0)
        MxB, _ = _eval_pwl_basis_sparse(zB, np.log(fxB), 0.0, 0.0)
        MyB, _ = _eval_pwl_basis_sparse(zB, np.log(fyB), 0.0, 0.0)

        wG_v = eval_logpwl(WG_pwl, kB)
        wB_v = eval_logpwl(WB_pwl, kB)
        A_gap = sp.hstack([sp.eye(2 * nB, format="csr"), np.ones((2 * nB, 1), dtype=np.float64)], format="csr")
        b_gap = np.concatenate([wG_v, wB_v])
        c_obj = np.concatenate([np.full(2 * nB, 1e-3 / (2 * nB)), np.array([-1.0])])
        bds = [(-500.0, 500.0)] * (2 * nB) + [(-50.0, 200.0)]

        yG_t = np.full(nB, -45.0)
        yB_t = np.full(nB, -48.0)
        solved = False
        for m_slk in (3.0e-3, 1.0e-3, 3.0e-4, 5.0e-5):
            yGt, yBt = yG_t.copy(), yB_t.copy()
            ok_p = False
            for _sp in range(2):
                evG_y = (1.0 - p) * (MyG @ yGt) + p * (MyG @ yBt)
                evB_y = P_REC * (MyB @ yGt) + (1.0 - P_REC) * (MyB @ yBt)
                n0G = np.abs(evG_y) <= 1.5
                n0B = np.abs(evB_y) <= 1.5
                A_rows = [A_mon_G, A_mon_B]
                b_rows = [b_mon_1, b_mon_1]
                for bv_c, mc in ((bL_s, (evG_y < 0.0) | n0G), (bR_s, (evG_y >= 0.0) | n0G)):
                    if np.any(mc):
                        A_rows.append(sp.hstack([bv_c * (1.0 - p) * MyG[mc] - MxG[mc], bv_c * p * MyG[mc]], format="csr"))
                        b_rows.append(-(fuG[mc] + m_slk))
                for bv_c, mc in ((bL_s, (evB_y < 0.0) | n0B), (bR_s, (evB_y >= 0.0) | n0B)):
                    if np.any(mc):
                        A_rows.append(sp.hstack([bv_c * P_REC * MyB[mc], bv_c * (1.0 - P_REC) * MyB[mc] - MxB[mc]], format="csr"))
                        b_rows.append(-(fuB[mc] + m_slk))
                A_y = sp.vstack(A_rows, format="csr")
                A_ext = sp.hstack([A_y, sp.csr_matrix((A_y.shape[0], 1), dtype=np.float64)], format="csr")
                res = linprog(c_obj, A_ub=sp.vstack([A_ext, A_gap], format="csc"), b_ub=np.concatenate(b_rows + [b_gap]), bounds=bds, method="highs")
                if res.success:
                    yGt = res.x[:nB].copy(); yBt = res.x[nB:2 * nB].copy()
                    ok_p = True
                else:
                    ok_p = False; break
            if ok_p:
                yG_k, yB_k = yGt, yBt
                solved = True; break
        assert solved, f"Coupled Markov staying LP failed at p={p}"

        BG_pwl = make_pwl_from_knots(kB, yG_k, 0.0, 0.0)
        BB_pwl = make_pwl_from_knots(kB, yB_k, 0.0, 0.0)
        evBG = make_pwl_from_knots(kB, (1.0 - p) * yG_k + p * yB_k, 0.0, 0.0)
        evBB = make_pwl_from_knots(kB, P_REC * yG_k + (1.0 - P_REC) * yB_k, 0.0, 0.0)
        cBG = verify_staying_barrier_bb(BG_pwl, A_hi=A_MAX, q_hi=Q_MAX, b_lo=bL_s, b_hi=bR_s, e_lo=ETA_MIN, e_hi=ETA_MAX, tol=tol_bb, B_ev_pwl=evBG)
        cBB = verify_staying_barrier_bb(BB_pwl, A_hi=AB_MAX, q_hi=Q_MAX, b_lo=bL_s, b_hi=bR_s, e_lo=ETA_MIN, e_hi=ETA_MAX, tol=tol_bb, B_ev_pwl=evBB)
        if cBG["certified"] and cBG["iv_certified"] and cBB["certified"] and cBB["iv_certified"]:
            best_BG, best_BB, best_cBG, best_cBB = BG_pwl, BB_pwl, cBG, cBB
            break

        if rnd < max_rounds:
            if not cBG["certified"]:
                for cx, cy, _, cval in cBG["counterexamples"][:16]:
                    _, cu = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, np.array([cx]), np.array([cy]), is_upper=True)
                    if cu[0] > -1e8:
                        fxG = np.append(fxG, cx); fyG = np.append(fyG, cy); fuG = np.append(fuG, float(cu[0]))
            if not cBB["certified"]:
                for cx, cy, _, cval in cBB["counterexamples"][:16]:
                    _, cu = _golden_L_vec(AB_MAX, Q_MAX, ETA_MIN, ETA_MAX, np.array([cx]), np.array([cy]), is_upper=True)
                    if cu[0] > -1e8:
                        fxB = np.append(fxB, cx); fyB = np.append(fyB, cy); fuB = np.append(fuB, float(cu[0]))
        elif best_BG is None:
            mx_res = max(float(cBG["d_ub"]), float(cBG["d_ub_iv"]), float(cBB["d_ub"]), float(cBB["d_ub_iv"]))
            if mx_res > 0.0:
                shift = (mx_res + 4e-4) / (1.0 - bR_s)
                yGs = yG_k + shift; yBs = yB_k + shift
                BG_pwl = make_pwl_from_knots(kB, yGs, 0.0, 0.0)
                BB_pwl = make_pwl_from_knots(kB, yBs, 0.0, 0.0)
                evBG = make_pwl_from_knots(kB, (1.0 - p) * yGs + p * yBs, 0.0, 0.0)
                evBB = make_pwl_from_knots(kB, P_REC * yGs + (1.0 - P_REC) * yBs, 0.0, 0.0)
                cBG = verify_staying_barrier_bb(BG_pwl, A_hi=A_MAX, q_hi=Q_MAX, b_lo=bL_s, b_hi=bR_s, e_lo=ETA_MIN, e_hi=ETA_MAX, tol=tol_bb, B_ev_pwl=evBG)
                cBB = verify_staying_barrier_bb(BB_pwl, A_hi=AB_MAX, q_hi=Q_MAX, b_lo=bL_s, b_hi=bR_s, e_lo=ETA_MIN, e_hi=ETA_MAX, tol=tol_bb, B_ev_pwl=evBB)
                if cBG["certified"] and cBG["iv_certified"] and cBB["certified"] and cBB["iv_certified"]:
                    best_BG, best_BB, best_cBG, best_cBB = BG_pwl, BB_pwl, cBG, cBB

    assert best_BG is not None and best_cBG["certified"] and best_cBB["certified"], f"Coupled staying barrier failed at p={p}"
    return best_BG, best_BB, best_cBG, best_cBB


def _case3_subbox_p_worker(task: Tuple[int, float, float, float, float, float, float, float, float, float]) -> Tuple[int, float, float, int, List[Dict[str, object]]]:
    """
    Granular unified CEGIS-LP worker certifying one ((AG, AB, q, eta) subbox, p) pair
    continuously across [BETA_MIN, BETA_MAX], starting at n_init=2 beta bands and
    adaptively bisecting beta only if needed. Returns leaf certificates for full export.
    """
    sub_idx, agL, agU, abL, abU, qL_s, qU_s, eL_s, eU_s, p = task
    k_t = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 20, endpoint=False),
        np.geomspace(0.0012, 0.0050, 44, endpoint=False),
        np.geomspace(0.0050, 0.025, 24, endpoint=False),
        np.geomspace(0.025, 0.25, 36, endpoint=False),
        np.geomspace(0.25, 60.0, 80),
    ]))
    k_w = np.unique(np.concatenate([
        np.geomspace(B_M, H_M, 44, endpoint=False),
        np.geomspace(H_M, 0.80, 48, endpoint=False),
        np.geomspace(0.80, 5.5, 42),
    ]))
    C_max_G = qU_s * H_M + F_A(agU, H_M, 1.0) - B_M
    C_max_B = qU_s * H_M + F_A(abU, H_M, 1.0) - B_M
    m_G = (eL_s * qL_s) / C_max_G
    m_B = (eL_s * qL_s) / C_max_B
    req_b_G = (eU_s / _min_c_E_plus(agL, qL_s, B_M, B_M, 0.44, eL_s, eU_s)) / BETA_MIN + 0.3
    req_b_B = (eU_s / _min_c_E_plus(abL, qL_s, B_M, B_M, 0.478, eL_s, eU_s)) / BETA_MIN + 0.3
    req_h_G = (eU_s / _min_c_E_plus(agL, qL_s, H_M, H_M, 0.57, eL_s, eU_s)) / BETA_MIN + 0.3
    req_h_B = (eU_s / _min_c_E_plus(abL, qL_s, H_M, H_M, 0.603, eL_s, eU_s)) / BETA_MIN + 0.3

    VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l = _solve_markov_teacher(p, agL, abL, qL_s, BETA_MAX, eL_s, eU_s, False, k_w)
    VG_u, VB_u, _, _, _, _ = _solve_markov_teacher(p, agU, abU, qU_s, BETA_MIN, eL_s, eU_s, True, k_t)

    def _check_band(bL_s: float, bR_s: float, depth: int) -> Tuple[float, int, List[Dict[str, object]]]:
        try:
            pG, pB, _, _ = _cegis_lp_coupled_markov_super_barrier(
                p, agU, abU, qU_s, bL_s, bR_s, eL_s, eU_s, k_t, VG_u, VB_u,
                m_G, m_B, req_b_G, req_b_B, req_h_G, req_h_B, max_rounds=12, tol_bb=2e-4,
            )
            pGh_iv = iv_eval_logpwl(pG, Interval(str(H_M)))
            pBh_iv = iv_eval_logpwl(pB, Interval(str(H_M)))
            iv_prec = Interval("1") / Interval("3")
            iv_omrec = Interval("2") / Interval("3")
            evBh = float((iv_prec * pGh_iv + iv_omrec * pBh_iv).to_float_bounds()[1])
            evB_pwl = make_pwl_from_knots(pG["ks"], P_REC * pG["vals"] + (1.0 - P_REC) * pB["vals"], pG["s_lo"], pG["s_hi"])
            ok_hB, _, _ = verify_derivative_below_bound(evB_pwl, H_M, bL_s, abL, qL_s, H_M, 0.603, eL=eL_s, eU=eU_s)
            WG_s, WB_s, _, _, kpB_s, LB_s, _, _ = _cegis_lp_coupled_markov_witness(
                p, bL_s, bR_s, k_w, VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l,
                agL, abL, qL_s, eL_s, eU_s, m_G, m_B, max_rounds=10, interval_check=True,
            )
            rb = verify_adverse_exit_bb(WB_s, evBh, abU, qU_s, bL_s, bR_s, eL_s, eU_s, H_M, 0.603, (H_M, 0.80), interval_check=True)
            if (ok_hB and rb["certified"] and rb["iv_certified"] and rb["m_lb_iv"] > 0.0) or depth >= 3:
                leaf = {
                    "sub_idx": int(sub_idx),
                    "agL": agL, "agU": agU, "abL": abL, "abU": abU,
                    "qL": qL_s, "qU": qU_s, "eL": eL_s, "eU": eU_s,
                    "bL": bL_s, "bR": bR_s,
                    "PsiG_net": pwl_to_dict(pG),
                    "PsiB_net": pwl_to_dict(pB),
                    "WG_net": pwl_to_dict(WG_s),
                    "WB_net": pwl_to_dict(WB_s),
                    "kpB_net": pwl_to_dict(kpB_s),
                    "LB_net": pwl_to_dict(LB_s),
                    "m_H1_B_iv": float(rb["m_lb_iv"]),
                }
                return float(rb["m_lb_iv"]), 1, [leaf]
        except AssertionError:
            if depth >= 3:
                raise
        bM_s = 0.5 * (bL_s + bR_s)
        m1, n1, l1 = _check_band(bL_s, bM_s, depth + 1)
        m2, n2, l2 = _check_band(bM_s, bR_s, depth + 1)
        return min(m1, m2), n1 + n2, l1 + l2

    n_init = 4 if p <= 0.015 else 2
    init_depth = 2 if n_init == 4 else 1
    b_edges = np.linspace(BETA_MIN, BETA_MAX, n_init + 1)
    m_sub = 1e9
    n_lf = 0
    all_leaves: List[Dict[str, object]] = []
    for jb in range(n_init):
        mj, nj, lj = _check_band(float(b_edges[jb]), float(b_edges[jb + 1]), init_depth)
        m_sub = min(m_sub, mj)
        n_lf += nj
        all_leaves.extend(lj)
    return sub_idx, p, m_sub, n_lf, all_leaves


def _case3_outer_band_worker(
    task: Tuple[
        float, int, float, float, np.ndarray, np.ndarray,
        np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray,
        float, float, float, float, float, float, float, float, float, float,
    ],
) -> Tuple[float, int, Dict[str, object]]:
    (
        p, jb, bL_o, bR_o, k_t_g, k_w_g,
        VG_u, VB_u, VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l,
        m_G, m_B, req_b_G, req_b_B, req_h_G, req_h_B,
        C_max_G, C_max_B, R_hat_G, R_hat_B,
    ) = task
    def _eval_sub_b(bL_s: float, bR_s: float, depth: int) -> Dict[str, object]:
        PsiG_pwl, PsiB_pwl, cG, cB = _cegis_lp_coupled_markov_super_barrier(
            p, A_MAX, AB_MAX, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX,
            k_t_g, VG_u, VB_u, m_G, m_B, req_b_G, req_b_B, req_h_G, req_h_B,
        )
        WG_pwl, WB_pwl, kpG_pwl, LG_pwl, kpB_pwl, LB_pwl, cwG, cwB = _cegis_lp_coupled_markov_witness(
            p, bL_s, bR_s, k_w_g, VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l,
            A_MIN, AB_MIN, Q_MIN, ETA_MIN, ETA_MAX, m_G, m_B,
        )

        psiGh_iv = iv_eval_logpwl(PsiG_pwl, Interval(str(H_M)))
        psiBh_iv = iv_eval_logpwl(PsiB_pwl, Interval(str(H_M)))
        psiGb_iv = iv_eval_logpwl(PsiG_pwl, Interval(str(B_M)))
        psiBb_iv = iv_eval_logpwl(PsiB_pwl, Interval(str(B_M)))
        iv_one = Interval("1")
        iv_p = Interval(str(p))
        iv_omp = iv_one - iv_p
        iv_prec = Interval("1") / Interval("3")
        iv_omrec = Interval("2") / Interval("3")
        evGh_iv = iv_omp * psiGh_iv + iv_p * psiBh_iv
        evBh_iv = iv_prec * psiGh_iv + iv_omrec * psiBh_iv
        evGb_iv = iv_omp * psiGb_iv + iv_p * psiBb_iv
        evBb_iv = iv_prec * psiGb_iv + iv_omrec * psiBb_iv
        psiGh = float(psiGh_iv.to_float_bounds()[1])
        psiBh = float(psiBh_iv.to_float_bounds()[1])
        evGh = float(evGh_iv.to_float_bounds()[1])
        evBh = float(evBh_iv.to_float_bounds()[1])
        evGb = float(evGb_iv.to_float_bounds()[1])
        evBb = float(evBb_iv.to_float_bounds()[1])

        evG_pwl = make_pwl_from_knots(PsiG_pwl["ks"], (1.0 - p) * PsiG_pwl["vals"] + p * PsiB_pwl["vals"], PsiG_pwl["s_lo"], PsiG_pwl["s_hi"])
        evB_pwl = make_pwl_from_knots(PsiG_pwl["ks"], P_REC * PsiG_pwl["vals"] + (1.0 - P_REC) * PsiB_pwl["vals"], PsiG_pwl["s_lo"], PsiG_pwl["s_hi"])

        ok_bG, mbG, _ = verify_derivative_below_bound(evG_pwl, B_M, bL_s, A_MIN, Q_MIN, B_M, 0.44)
        ok_bB, mbB, _ = verify_derivative_below_bound(evB_pwl, B_M, bL_s, AB_MIN, Q_MIN, B_M, 0.478)
        ok_hG, mhG, _ = verify_derivative_below_bound(evG_pwl, H_M, bL_s, A_MIN, Q_MIN, H_M, 0.57)
        ok_hB, mhB, _ = verify_derivative_below_bound(evB_pwl, H_M, bL_s, AB_MIN, Q_MIN, H_M, 0.603)

        m_M_G = verify_adverse_exit_bb(WG_pwl, evGb, A_MAX, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M))
        m_M_B = verify_adverse_exit_bb(WB_pwl, evBb, AB_MAX, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, B_M, 0.478, (B_M, H_M))
        m_H1_G = verify_adverse_exit_bb(WG_pwl, evGh, A_MAX, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80))
        m_H1_B_outer = verify_adverse_exit_bb(WB_pwl, evBh, AB_MAX, Q_MAX, bL_s, bR_s, ETA_MIN, ETA_MAX, H_M, 0.603, (H_M, 0.80))

        kpG80 = float(eval_logpwl(kpG_pwl, np.array([0.80]))[0])
        LG80 = float(np.clip(eval_logpwl(LG_pwl, np.array([0.80]))[0], 0.0, 0.999))
        wGkp_iv = iv_eval_logpwl(WG_pwl, Interval(kpG80))
        wBkpG_iv = iv_eval_logpwl(WB_pwl, Interval(kpG80))
        evWG_kp_lo = float((iv_omp * wGkp_iv + iv_p * wBkpG_iv).to_float_bounds()[0])
        ok_H2_G, mH2_G_lb = verify_H2_global_interval(
            WG_pwl, kpG80, LG80, evWG_kp_lo, evGh, A_MIN, A_MAX, Q_MIN, Q_MAX, bL_s, bR_s,
        )
        kpB80 = float(eval_logpwl(kpB_pwl, np.array([0.80]))[0])
        LB80 = float(np.clip(eval_logpwl(LB_pwl, np.array([0.80]))[0], 0.0, 0.999))
        wGkpB_iv = iv_eval_logpwl(WG_pwl, Interval(kpB80))
        wBkpB_iv = iv_eval_logpwl(WB_pwl, Interval(kpB80))
        evWB_kp_lo = float((iv_prec * wGkpB_iv + iv_omrec * wBkpB_iv).to_float_bounds()[0])
        ok_H2_B, mH2_B_lb = verify_H2_global_interval(
            WB_pwl, kpB80, LB80, evWB_kp_lo, evBh, AB_MIN, AB_MAX, Q_MIN, Q_MAX, bL_s, bR_s,
        )

        # 50-digit Interval 2x2 Cramer solver uniformly across [bL_s, bR_s]
        iv_BsG, iv_BsB = iv_solve_markov_B_star(p, bL_s, bR_s, R_hat_G, R_hat_B, C_max_G, C_max_B, m_G, m_B)
        iv_width = Interval(str(H_M)) - Interval(str(B_M))
        iv_WG0 = iv_eval_logpwl(WG_pwl, Interval(str(B_M)))
        iv_WB0 = iv_eval_logpwl(WB_pwl, Interval(str(B_M)))
        iv_BG0 = iv_BsG - Interval(str(m_G)) * iv_width
        iv_BB0 = iv_BsB - Interval(str(m_B)) * iv_width
        iv_margG = iv_WG0 - iv_BG0
        iv_margB = iv_WB0 - iv_BB0
        ex_G = psiGh_iv - Interval._raw(iv_BsG.lo, iv_BsG.lo)
        ex_B = psiBh_iv - Interval._raw(iv_BsB.lo, iv_BsB.lo)
        iv_max_exit = Interval._raw(max(ex_G.lo, ex_B.lo), max(ex_G.hi, ex_B.hi))

        WG0 = float(iv_WG0.to_float_bounds()[0])
        WB0 = float(iv_WB0.to_float_bounds()[0])
        BG0 = float(iv_BG0.to_float_bounds()[1])
        BB0 = float(iv_BB0.to_float_bounds()[1])
        margG = float(iv_margG.to_float_bounds()[0])
        margB = float(iv_margB.to_float_bounds()[0])
        BsG_lo = float(Interval._raw(iv_BsG.lo, iv_BsG.lo).to_float_bounds()[0])
        BsB_lo = float(Interval._raw(iv_BsB.lo, iv_BsB.lo).to_float_bounds()[0])
        T_G = certify_affine_deadline_interval(iv_margG, iv_max_exit, BETA_MAX)
        T_B = certify_affine_deadline_interval(iv_margB, iv_max_exit, BETA_MAX)
        T0 = T_B + 4
        eps0 = compute_doob_eps0_interval(
            WG0, WB0, BG0, BB0, BsG_lo, BsB_lo, PsiG_pwl, PsiB_pwl, T0,
        )

        # Coupled CEGIS-LP compressed staying barriers (B_G, B_B) + exact Doob E[tau] bound
        BG_comp, BB_comp, cBG_comp, cBB_comp = _cegis_lp_coupled_markov_staying_barrier(
            p, bL_s, bR_s, WG_pwl, WB_pwl,
        )
        doob_comp = compute_doob_eps0_coupled_pwl_interval(
            BG_comp, BB_comp, WG_pwl, WB_pwl, PsiG_pwl, PsiB_pwl,
        )
        iv_TG_comp, _, _ = (lambda bg_ev: certify_staying_deadline_interval(BG_comp, PsiG_pwl, WG_pwl, BETA_MAX))(None)
        iv_TB_comp, _, _ = certify_staying_deadline_interval(BB_comp, PsiB_pwl, WB_pwl, BETA_MAX)

        ok_all = (
            ok_bG and ok_bB and ok_hG and ok_hB
            and ok_H2_G and ok_H2_B
            and m_M_G["certified"] and m_M_B["certified"] and m_H1_G["certified"]
            and eps0 > 0.0 and doob_comp["eps0_opt"] > 0.0
        )
        if not ok_all and depth < 2:
            bMid = 0.5 * (bL_s + bR_s)
            rL = _eval_sub_b(bL_s, bMid, depth + 1)
            rR = _eval_sub_b(bMid, bR_s, depth + 1)
            rep_sub = rL if rL["metrics"]["m_M_B_iv"] <= rR["metrics"]["m_M_B_iv"] else rR
            return {
                "bL": rep_sub["bL"],
                "bR": rep_sub["bR"],
                "PsiG_net": rep_sub["PsiG_net"],
                "PsiB_net": rep_sub["PsiB_net"],
                "WG_net": rep_sub["WG_net"],
                "WB_net": rep_sub["WB_net"],
                "kpG_net": rep_sub["kpG_net"],
                "LG_net": rep_sub["LG_net"],
                "kpB_net": rep_sub["kpB_net"],
                "LB_net": rep_sub["LB_net"],
                "BG_comp_net": rep_sub["BG_comp_net"],
                "BB_comp_net": rep_sub["BB_comp_net"],
                "leaf_bands": rL["leaf_bands"] + rR["leaf_bands"],
                "metrics": {
                    "knots_Psi": max(rL["metrics"]["knots_Psi"], rR["metrics"]["knots_Psi"]),
                    "knots_W": max(rL["metrics"]["knots_W"], rR["metrics"]["knots_W"]),
                    "margG": min(rL["metrics"]["margG"], rR["metrics"]["margG"]),
                    "margB": min(rL["metrics"]["margB"], rR["metrics"]["margB"]),
                    "BG_010": max(rL["metrics"]["BG_010"], rR["metrics"]["BG_010"]),
                    "BB_010": max(rL["metrics"]["BB_010"], rR["metrics"]["BB_010"]),
                    "T_G": max(rL["metrics"]["T_G"], rR["metrics"]["T_G"]),
                    "T_B": max(rL["metrics"]["T_B"], rR["metrics"]["T_B"]),
                    "T_0": max(rL["metrics"]["T_0"], rR["metrics"]["T_0"]),
                    "m_M_G_iv": min(rL["metrics"]["m_M_G_iv"], rR["metrics"]["m_M_G_iv"]),
                    "m_M_B_iv": min(rL["metrics"]["m_M_B_iv"], rR["metrics"]["m_M_B_iv"]),
                    "m_H1_G_iv": min(rL["metrics"]["m_H1_G_iv"], rR["metrics"]["m_H1_G_iv"]),
                    "mH2_G_lb_iv": min(rL["metrics"]["mH2_G_lb_iv"], rR["metrics"]["mH2_G_lb_iv"]),
                    "mH2_B_lb_iv": min(rL["metrics"]["mH2_B_lb_iv"], rR["metrics"]["mH2_B_lb_iv"]),
                    "m_H1_B_outer": min(rL["metrics"]["m_H1_B_outer"], rR["metrics"]["m_H1_B_outer"]),
                    "eps_0_lb": min(rL["metrics"]["eps_0_lb"], rR["metrics"]["eps_0_lb"]),
                    "T_G_comp": max(rL["metrics"]["T_G_comp"], rR["metrics"]["T_G_comp"]),
                    "T_B_comp": max(rL["metrics"]["T_B_comp"], rR["metrics"]["T_B_comp"]),
                    "T0_min_comp": max(rL["metrics"]["T0_min_comp"], rR["metrics"]["T0_min_comp"]),
                    "T0_opt_comp": max(rL["metrics"]["T0_opt_comp"], rR["metrics"]["T0_opt_comp"]),
                    "eps0_comp": min(rL["metrics"]["eps0_comp"], rR["metrics"]["eps0_comp"]),
                    "E_tau_comp": max(rL["metrics"]["E_tau_comp"], rR["metrics"]["E_tau_comp"]),
                    "d_ub_BG_iv": max(rL["metrics"]["d_ub_BG_iv"], rR["metrics"]["d_ub_BG_iv"]),
                    "d_ub_BB_iv": max(rL["metrics"]["d_ub_BB_iv"], rR["metrics"]["d_ub_BB_iv"]),
                    "psiGh": max(rL["metrics"]["psiGh"], rR["metrics"]["psiGh"]),
                    "psiBh": max(rL["metrics"]["psiBh"], rR["metrics"]["psiBh"]),
                    "WG0": min(rL["metrics"]["WG0"], rR["metrics"]["WG0"]),
                    "WB0": min(rL["metrics"]["WB0"], rR["metrics"]["WB0"]),
                    "slope_b_G_margin": min(rL["metrics"]["slope_b_G_margin"], rR["metrics"]["slope_b_G_margin"]),
                    "slope_b_B_margin": min(rL["metrics"]["slope_b_B_margin"], rR["metrics"]["slope_b_B_margin"]),
                    "slope_h_G_margin": min(rL["metrics"]["slope_h_G_margin"], rR["metrics"]["slope_h_G_margin"]),
                    "slope_h_B_margin": min(rL["metrics"]["slope_h_B_margin"], rR["metrics"]["slope_h_B_margin"]),
                    "d_ub_PsiG_iv": max(rL["metrics"]["d_ub_PsiG_iv"], rR["metrics"]["d_ub_PsiG_iv"]),
                    "d_ub_PsiB_iv": max(rL["metrics"]["d_ub_PsiB_iv"], rR["metrics"]["d_ub_PsiB_iv"]),
                },
            }

        assert ok_bG and ok_bB and ok_hG and ok_hB, f"Markov <b/<h failed at p={p}, jb={jb} [{bL_s},{bR_s}]: {(mbG, mbB, mhG, mhB)}"
        assert ok_H2_G and ok_H2_B, f"Markov H2 failed at p={p}, jb={jb} [{bL_s},{bR_s}]: G={mH2_G_lb}, B={mH2_B_lb}"
        assert ok_all, (
            f"Markov cert failed at p={p}, jb={jb} [{bL_s},{bR_s}]: M_G={m_M_G['m_lb_iv']}, M_B={m_M_B['m_lb_iv']}, H1_G={m_H1_G['m_lb_iv']}, eps0={eps0}"
        )

        leaf_rec = {
            "bL": bL_s,
            "bR": bR_s,
            "PsiG_net": pwl_to_dict(PsiG_pwl),
            "PsiB_net": pwl_to_dict(PsiB_pwl),
            "WG_net": pwl_to_dict(WG_pwl),
            "WB_net": pwl_to_dict(WB_pwl),
            "kpG_net": pwl_to_dict(kpG_pwl),
            "LG_net": pwl_to_dict(LG_pwl),
            "kpB_net": pwl_to_dict(kpB_pwl),
            "LB_net": pwl_to_dict(LB_pwl),
            "BG_comp_net": pwl_to_dict(BG_comp),
            "BB_comp_net": pwl_to_dict(BB_comp),
            "metrics": {
                "knots_Psi": int(len(PsiG_pwl["ks"])),
                "knots_W": int(len(WG_pwl["ks"])),
                "margG": margG,
                "margB": margB,
                "BG_010": BG0,
                "BB_010": BB0,
                "T_G": T_G,
                "T_B": T_B,
                "T_0": T0,
                "m_M_G_iv": float(m_M_G["m_lb_iv"]),
                "m_M_B_iv": float(m_M_B["m_lb_iv"]),
                "m_H1_G_iv": float(m_H1_G["m_lb_iv"]),
                "mH2_G_lb_iv": float(mH2_G_lb),
                "mH2_B_lb_iv": float(mH2_B_lb),
                "m_H1_B_outer": float(m_H1_B_outer["m_lb_iv"]),
                "eps_0_lb": float(eps0),
                "T_G_comp": int(iv_TG_comp),
                "T_B_comp": int(iv_TB_comp),
                "T0_min_comp": int(doob_comp["T0_min"]),
                "T0_opt_comp": int(doob_comp["T0_opt"]),
                "eps0_comp": float(doob_comp["eps0_opt"]),
                "E_tau_comp": float(doob_comp["E_tau_opt"]),
                "d_ub_BG_iv": float(cBG_comp["d_ub_iv"]),
                "d_ub_BB_iv": float(cBB_comp["d_ub_iv"]),
                "psiGh": psiGh,
                "psiBh": psiBh,
                "WG0": WG0,
                "WB0": WB0,
                "slope_b_G_margin": float(mbG),
                "slope_b_B_margin": float(mbB),
                "slope_h_G_margin": float(mhG),
                "slope_h_B_margin": float(mhB),
                "d_ub_PsiG_iv": float(cG["d_ub_iv"]),
                "d_ub_PsiB_iv": float(cB["d_ub_iv"]),
            },
        }
        res_rec = dict(leaf_rec)
        res_rec["leaf_bands"] = [leaf_rec]
        return res_rec

    return p, jb, _eval_sub_b(bL_o, bR_o, 0)


def synth_case_3(seed: int) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 3: Pure CEGIS-LP Markov Coupled System (G, B) + Complete H1/H2/<h")
    print("=" * 72)
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 20, endpoint=False),
        np.geomspace(0.0012, 0.0050, 50, endpoint=False),
        np.geomspace(0.0050, 0.025, 24, endpoint=False),
        np.geomspace(0.025, 0.25, 40, endpoint=False),
        np.geomspace(0.25, 60.0, 80),
    ]))
    k_w_g = np.unique(np.concatenate([
        np.geomspace(B_M, H_M, 52, endpoint=False),
        np.geomspace(H_M, 0.80, 52, endpoint=False),
        np.geomspace(0.80, 5.5, 50),
    ]))
    C_max_G = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    C_max_B = Q_MAX * H_M + F_A(AB_MAX, H_M, 1.0) - B_M
    m_G = (ETA_MIN * Q_MIN) / C_max_G
    m_B = (ETA_MIN * Q_MIN) / C_max_B
    R_hat_G = -0.996
    R_hat_B = iv_compute_R_hat_B_upper(AB_MAX, Q_MAX, ETA_MIN, ETA_MAX)

    req_b_G = (ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, B_M, B_M, 0.44)) / BETA_MIN + 0.5
    req_b_B = (ETA_MAX / _min_c_E_plus(AB_MIN, Q_MIN, B_M, B_M, 0.478)) / BETA_MIN + 0.5
    req_h_G = (ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, H_M, H_M, 0.57)) / BETA_MIN + 0.5
    req_h_B = (ETA_MAX / _min_c_E_plus(AB_MIN, Q_MIN, H_M, H_M, 0.603)) / BETA_MIN + 0.5

    p_list = [0.0, 0.005, 0.01, 0.015, 0.02, 0.05, 0.08, 0.12]
    b_edges_outer = np.linspace(BETA_MIN, BETA_MAX, 9)
    n_workers = min(12, os.cpu_count() or 4)
    cache_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".case3_outer_cache.json")
    t_out0 = time.time()

    markov_out = None
    if os.path.exists(cache_path):
        try:
            cached = json.load(open(cache_path, "r", encoding="utf-8"))
            if all(f"{pv:.3f}" in cached for pv in p_list):
                markov_out = cached
                print(f"  [Cache] Cargados 64 certificados externos de Fase 1 desde {os.path.basename(cache_path)}.", flush=True)
        except Exception:
            markov_out = None

    if markov_out is None:
        outer_tasks = []
        for p in p_list:
            VG_u, VB_u, _, _, _, _ = _solve_markov_teacher(p, A_MAX, AB_MAX, Q_MAX, BETA_MIN, ETA_MIN, ETA_MAX, True, k_t_g)
            VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l = _solve_markov_teacher(p, A_MIN, AB_MIN, Q_MIN, BETA_MAX, ETA_MIN, ETA_MAX, False, k_w_g)
            for jb in range(8):
                outer_tasks.append((
                    p, jb, float(b_edges_outer[jb]), float(b_edges_outer[jb + 1]), k_t_g, k_w_g,
                    VG_u, VB_u, VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l,
                    m_G, m_B, req_b_G, req_b_B, req_h_G, req_h_B,
                    C_max_G, C_max_B, R_hat_G, R_hat_B,
                ))

        by_p: Dict[float, List[Tuple[int, Dict[str, object]]]] = {pv: [] for pv in p_list}
        pbar1 = ProgressBar("Caso 3 | Fase 1 (p x 8-beta)", len(outer_tasks), min_interval_sec=1.5)
        with ProcessPoolExecutor(max_workers=n_workers) as pool:
            futs = [pool.submit(_case3_outer_band_worker, t) for t in outer_tasks]
            for fut in as_completed(futs):
                p_res, jb_res, rec_res = fut.result()
                by_p[p_res].append((jb_res, rec_res))
                pbar1.update(1, suffix=f"p={100*p_res:.1f}% jb={jb_res+1}")

        markov_out = {}
        for p in p_list:
            band_recs = [rec for _, rec in sorted(by_p[p], key=lambda item: item[0])]
            all_leaf_bands = []
            for br in band_recs:
                all_leaf_bands.extend(br["leaf_bands"])
            all_leaf_bands.sort(key=lambda r: r["bL"])
            rep = min(band_recs, key=lambda r: r["metrics"]["m_M_B_iv"])
            worst_metrics = {
                "knots_Psi": max(r["metrics"]["knots_Psi"] for r in band_recs),
                "knots_W": max(r["metrics"]["knots_W"] for r in band_recs),
                "outer_beta_subintervals": len(all_leaf_bands),
                "margG": min(r["metrics"]["margG"] for r in band_recs),
                "margB": min(r["metrics"]["margB"] for r in band_recs),
                "BG_010": max(r["metrics"]["BG_010"] for r in band_recs),
                "BB_010": max(r["metrics"]["BB_010"] for r in band_recs),
                "T_G": max(r["metrics"]["T_G"] for r in band_recs),
                "T_B": max(r["metrics"]["T_B"] for r in band_recs),
                "T_0": max(r["metrics"]["T_0"] for r in band_recs),
                "m_M_G_iv": min(r["metrics"]["m_M_G_iv"] for r in band_recs),
                "m_M_B_iv": min(r["metrics"]["m_M_B_iv"] for r in band_recs),
                "m_H1_G_iv": min(r["metrics"]["m_H1_G_iv"] for r in band_recs),
                "mH2_G_lb_iv": min(r["metrics"]["mH2_G_lb_iv"] for r in band_recs),
                "mH2_B_lb_iv": min(r["metrics"]["mH2_B_lb_iv"] for r in band_recs),
                "m_H1_B_outer": min(r["metrics"]["m_H1_B_outer"] for r in band_recs),
                "m_H1_B_32bx": float("nan"),
                "subbox_beta_split": 0,
                "eps_0_lb": min(r["metrics"]["eps_0_lb"] for r in band_recs),
                "T_G_comp": max(r["metrics"]["T_G_comp"] for r in band_recs),
                "T_B_comp": max(r["metrics"]["T_B_comp"] for r in band_recs),
                "T0_min_comp": max(r["metrics"]["T0_min_comp"] for r in band_recs),
                "T0_opt_comp": max(r["metrics"]["T0_opt_comp"] for r in band_recs),
                "eps0_comp": min(r["metrics"]["eps0_comp"] for r in band_recs),
                "E_tau_comp": max(r["metrics"]["E_tau_comp"] for r in band_recs),
                "d_ub_BG_iv": max(r["metrics"]["d_ub_BG_iv"] for r in band_recs),
                "d_ub_BB_iv": max(r["metrics"]["d_ub_BB_iv"] for r in band_recs),
                "psiGh": max(r["metrics"]["psiGh"] for r in band_recs),
                "psiBh": max(r["metrics"]["psiBh"] for r in band_recs),
                "WG0": min(r["metrics"]["WG0"] for r in band_recs),
                "WB0": min(r["metrics"]["WB0"] for r in band_recs),
                "slope_b_G_margin": min(r["metrics"]["slope_b_G_margin"] for r in band_recs),
                "slope_b_B_margin": min(r["metrics"]["slope_b_B_margin"] for r in band_recs),
                "slope_h_G_margin": min(r["metrics"]["slope_h_G_margin"] for r in band_recs),
                "slope_h_B_margin": min(r["metrics"]["slope_h_B_margin"] for r in band_recs),
                "d_ub_PsiG_iv": max(r["metrics"]["d_ub_PsiG_iv"] for r in band_recs),
                "d_ub_PsiB_iv": max(r["metrics"]["d_ub_PsiB_iv"] for r in band_recs),
                "rep_beta_band": [rep["bL"], rep["bR"]],
            }
            print(
                f"  p={100*p:4.1f}% [{len(all_leaf_bands)}-beta] | aff:T0={worst_metrics['T_0']} eps0={worst_metrics['eps_0_lb']:.4f} | "
                f"comp:T=({worst_metrics['T_G_comp']},{worst_metrics['T_B_comp']}) T0={worst_metrics['T0_opt_comp']} eps0={worst_metrics['eps0_comp']:.4f} E[tau]<={worst_metrics['E_tau_comp']:.1f}",
                flush=True,
            )
            markov_out[f"{p:.3f}"] = {
                "p": p,
                "PsiG_net": rep["PsiG_net"],
                "PsiB_net": rep["PsiB_net"],
                "WG_net": rep["WG_net"],
                "WB_net": rep["WB_net"],
                "kpG_net": rep["kpG_net"],
                "LG_net": rep["LG_net"],
                "kpB_net": rep["kpB_net"],
                "LB_net": rep["LB_net"],
                "BG_comp_net": rep["BG_comp_net"],
                "BB_comp_net": rep["BB_comp_net"],
                "beta_bands": all_leaf_bands,
                "metrics": worst_metrics,
            }
        with open(cache_path, "w", encoding="utf-8") as cf:
            json.dump(markov_out, cf)
        print(f"  Completed 64 outer (p x 8-beta) certificates in {time.time()-t_out0:.1f}s (cached).", flush=True)

    # Parallel flattened 32-subbox (4 AG x 2 AB x 2 q x 2 eta) x 8-p (256 tasks) x [beta_-, beta_+] continuum certification for H1 in state B
    aG_pts = np.linspace(A_MIN, A_MAX, 5)
    aB_pts = np.linspace(AB_MIN, AB_MAX, 3)
    q_pts = np.linspace(Q_MIN, Q_MAX, 3)
    e_pts = np.linspace(ETA_MIN, ETA_MAX, 3)
    sb_tasks = []
    s_idx = 0
    for ie in range(2):
        for iq in range(2):
            for iG in range(4):
                for iB in range(2):
                    for pv in p_list:
                        sb_tasks.append((
                            s_idx, float(aG_pts[iG]), float(aG_pts[iG + 1]),
                            float(aB_pts[iB]), float(aB_pts[iB + 1]),
                            float(q_pts[iq]), float(q_pts[iq + 1]),
                            float(e_pts[ie]), float(e_pts[ie + 1]),
                            float(pv),
                        ))
                    s_idx += 1

    hb_min_p = {pv: 1e9 for pv in p_list}
    hb_lf_p = {pv: 0 for pv in p_list}
    hb_leaves_p: Dict[float, List[Dict[str, object]]] = {pv: [] for pv in p_list}
    print(f"  Launching {len(sb_tasks)} flattened (subbox x p) CEGIS-LP+Rust tasks across {n_workers} workers...", flush=True)
    pbar2 = ProgressBar("Caso 3 | Fase 2 (256 subcajas H1_B)", len(sb_tasks), min_interval_sec=1.5)
    with ProcessPoolExecutor(max_workers=n_workers) as pool:
        futs = [pool.submit(_case3_subbox_p_worker, t) for t in sb_tasks]
        for fut in as_completed(futs):
            r_idx, pv, ms, nl, leaves = fut.result()
            hb_min_p[pv] = min(hb_min_p[pv], ms)
            hb_lf_p[pv] += nl
            hb_leaves_p[pv].extend(leaves)
            pbar2.update(1, suffix=f"sub={r_idx:02d} p={100*pv:.1f}% H1_B={ms:+.3f}")

    for p in p_list:
        mt = markov_out[f"{p:.3f}"]["metrics"]
        m_hb = float(hb_min_p[p])
        mt["m_H1_B_32bx"] = m_hb
        mt["subbox_beta_split"] = int(hb_lf_p[p])
        leaves_sorted = sorted(hb_leaves_p[p], key=lambda r: (r["sub_idx"], r["bL"]))
        markov_out[f"{p:.3f}"]["subbox_leaves"] = leaves_sorted
        print(f"  p={100*p:4.1f}% SUMMARY | H1_B_32bx_iv={m_hb:+.4f} (leaves={hb_lf_p[p]}) | comp E[tau]<={mt['E_tau_comp']:.1f} (vs aff {mt['T_0']/mt['eps_0_lb']:.1f})", flush=True)
        assert m_hb > 0.0, f"Case 3 32-subbox H1_B failed at p={p}: m_hb={m_hb}"
    if os.path.exists(cache_path):
        os.remove(cache_path)
    return markov_out


# ---------------------------------------------------------------------------
# Case 4: Piecewise Continuous AK Regime (Pure CEGIS-LP, Full [0.28, inf))
# ---------------------------------------------------------------------------
def synth_case_4(seed: int, B_pwl_reuse: Optional[Dict[str, object]] = None) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 4: Piecewise Continuous AK Regime Transferability Test (Pure CEGIS-LP)")
    print("=" * 72)
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.02, 36, endpoint=False),
        np.geomspace(0.02, H_M, 36, endpoint=False),
        np.geomspace(H_M, 25.0, 44),
    ]))
    eta_max_c_M = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, B_M, B_M, 0.44)
    eta_max_c_H = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, H_M, H_M, 0.57)

    V_up_ak, _, _ = _solve_teacher_vfi(A_MAX, Q_MAX, BETA_MIN, ETA_MIN, ETA_MAX, True, k_t_g, ak_mode=True)
    D_hi_ak = _safe_D_hi(ETA_MAX, BETA_MAX)

    def _init_ak(k):
        ka = np.asarray(k, dtype=np.float64)
        v = np.interp(np.log(np.clip(ka, 1e-4, 25.0)), np.log(k_t_g), V_up_ak)
        v = np.where(ka < 1e-4, V_up_ak[0] + (ETA_MIN / (1.0 - BETA_MIN)) * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 25.0, V_up_ak[-1] + D_hi_ak * np.log(ka / 25.0), v)

    Psi_pwl, cert_Psi_ak, hist_Psi = _cegis_lp_super_barrier(
        A_MAX, BETA_MIN, BETA_MAX, Q_MAX, ETA_MIN, ETA_MAX, 1e-4, 25.0,
        init_vals_fn=_init_ak,
        ak_mode=True,
        pre_b_slope=(eta_max_c_M / BETA_MIN) + 0.15,
        pre_h_slope=(eta_max_c_H / BETA_MIN) + 0.05,
        max_cegis_rounds=18,
        tol_bb=1e-3,
    )
    W_pwl, kp_pwl, L_pwl, cert_W_ak, hist_W = _cegis_lp_witness(
        A_MIN, Q_MIN, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, (B_M, 3.5), ak_mode=True,
    )

    assert B_pwl_reuse is not None, "Expected B_pwl from Case 1"
    B_pwl = B_pwl_reuse

    T_ak, inf_W_B_ak, sup_Psi_B_ak = certify_staying_deadline_interval(B_pwl, Psi_pwl, W_pwl, BETA_MAX)

    psi_ak_10 = float(iv_eval_logpwl(Psi_pwl, Interval(str(B_M))).to_float_bounds()[1])
    psi_ak_28 = float(iv_eval_logpwl(Psi_pwl, Interval(str(H_M))).to_float_bounds()[1])
    w_ak_10 = float(iv_eval_logpwl(W_pwl, Interval(str(B_M))).to_float_bounds()[0])
    w_ak_28 = float(iv_eval_logpwl(W_pwl, Interval(str(H_M))).to_float_bounds()[0])

    # Fix 6: <b and <h derivative criteria + adverse exit on M, [0.28, 3.5], and [3.5, inf)
    ok_db, margin_db, _ = verify_derivative_below_bound(Psi_pwl, B_M, BETA_MIN, A_MIN, Q_MIN, B_M, 0.44)
    ok_dh, margin_dh, _ = verify_derivative_below_bound(Psi_pwl, H_M, BETA_MIN, A_MIN, Q_MIN, H_M, 0.57)
    assert ok_db and ok_dh, f"AK <b/<h failed: {(margin_db, margin_dh)}"

    exit_M_ak = verify_adverse_exit_bb(W_pwl, psi_ak_10, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M), ak_mode=False)
    exit_H1_ak = verify_adverse_exit_bb(W_pwl, psi_ak_28, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 3.5), ak_mode=True)
    ok_H2_ak, exit_H2_ak_lb = verify_H2_global_interval(
        W_pwl, 0.0, 0.0, 0.0, psi_ak_28, A_MIN, A_MAX, Q_MIN, Q_MAX, BETA_MIN, BETA_MAX, ak_mode=True,
    )
    ok_ak_tail, ak_tail_res_iv = verify_ak_witness_tail_interval(
        W_pwl, kp_pwl, L_pwl, A_MIN, Q_MIN, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, k_tail=3.5,
    )

    assert exit_M_ak["certified"] and exit_M_ak["iv_certified"]
    assert exit_H1_ak["certified"] and exit_H1_ak["iv_certified"]
    assert ok_H2_ak and ok_ak_tail, f"AK tail/H2 failed: ok_H2={ok_H2_ak}, ok_tail={ok_ak_tail}, res_iv={ak_tail_res_iv}"
    assert psi_ak_28 > 240.0 and w_ak_28 > 235.0

    print(f"  AK Psi(0.28)={psi_ak_28:+.4f}, W(0.28)={w_ak_28:+.4f}, W(0.10)={w_ak_10:+.4f}")
    print(f"  AK T_theta={T_ak}, inf(W-B)={inf_W_B_ak:.4f}, sup(Psi-B)={sup_Psi_B_ak:.4f}")
    print(f"  AK exitM_iv={exit_M_ak['m_lb_iv']:+.4f}, exitH_[0.28,3.5]_iv={exit_H1_ak['m_lb_iv']:+.4f}, exitH_[3.5,inf)_iv={exit_H2_ak_lb:+.4f}, witness_tail_iv={ak_tail_res_iv:+.6f}")
    print(f"  AK <b margin={margin_db:+.4f}, <h margin={margin_dh:+.4f}")

    return {
        "B_net": pwl_to_dict(B_pwl),
        "Psi_net": pwl_to_dict(Psi_pwl),
        "W_net": pwl_to_dict(W_pwl),
        "kp_net": pwl_to_dict(kp_pwl),
        "L_net": pwl_to_dict(L_pwl),
        "metrics": {
            "psi_ak_10": psi_ak_10,
            "psi_ak_28": psi_ak_28,
            "w_ak_10": w_ak_10,
            "w_ak_28": w_ak_28,
            "T_ak": T_ak,
            "inf_W_B_ak": inf_W_B_ak,
            "sup_Psi_B_ak": sup_Psi_B_ak,
            "exit_M_ak_lb_iv": float(exit_M_ak["m_lb_iv"]),
            "exit_H1_ak_lb_iv": float(exit_H1_ak["m_lb_iv"]),
            "exit_H2_ak_lb_iv": float(exit_H2_ak_lb),
            "ak_tail_res_iv": float(ak_tail_res_iv),
            "slope_b_margin": float(margin_db),
            "slope_h_margin": float(margin_dh),
            "d_ub_Psi_ak_iv": float(cert_Psi_ak["d_ub_iv"]),
            "d_ub_W_ak_iv": float(cert_W_ak["d_ub_iv"]),
            "knots_Psi": int(len(Psi_pwl["ks"])),
            "knots_W": int(len(W_pwl["ks"])),
        },
        "history_Psi": hist_Psi,
        "history_W": hist_W,
    }


# ---------------------------------------------------------------------------
# Case 5: State-Dependent Endogenous Ruin p(K) = p * 1_{K < 0.28} (Pilar 4)
# ---------------------------------------------------------------------------
def _case5_p_worker(task: Tuple[float, float, np.ndarray, float, float, float]) -> Tuple[float, Dict[str, object]]:
    p, v_ruin, k_t_g, m_G, eta_max_c_M, eta_max_c_H = task
    bL, bR = BETA_MIN, BETA_MAX
    V_up_g, _, _ = _solve_teacher_vfi(
        A_MAX, Q_MAX, bL, ETA_MIN, ETA_MAX, True, k_t_g,
        p_ruin=p, v_ruin=v_ruin, h_safe=H_M,
    )
    s_lo_5 = _safe_s_lo(ETA_MIN, bL * (1.0 - p))
    D_hi_5 = _safe_D_hi(ETA_MAX, bR)

    def _init_psi_5(k):
        ka = np.asarray(k, dtype=np.float64)
        v = np.interp(np.log(np.clip(ka, 1e-4, 90.0)), np.log(k_t_g), V_up_g)
        v = np.where(ka < 1e-4, V_up_g[0] + s_lo_5 * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
        return np.where(ka > 90.0, V_up_g[-1] + D_hi_5 * np.log(ka / 90.0), v)

    Psi_pwl, cert_Psi, _ = _cegis_lp_super_barrier(
        A_MAX, bL, bR, Q_MAX, ETA_MIN, ETA_MAX, 1e-4, 90.0,
        init_vals_fn=_init_psi_5,
        m_min_slope=m_G,
        pre_b_slope=(eta_max_c_M / (bL * (1.0 - p))) + 0.20,
        pre_h_slope=(eta_max_c_H / bL) + 0.08,
        max_cegis_rounds=14,
        p_ruin=p, v_ruin=v_ruin, h_safe=H_M,
    )
    W_M, kpM, LM, cert_WM, _ = _cegis_lp_witness(
        A_MIN, Q_MIN, bL, bR, ETA_MIN, ETA_MAX, (B_M, 5.5),
        m_req_M=m_G, max_cegis_rounds=10,
        p_ruin=p, v_ruin=v_ruin, h_safe=H_M,
    )
    W_H, kpH, LH, cert_WH, _ = _cegis_lp_witness(
        A_MIN, Q_MIN, bL, bR, ETA_MIN, ETA_MAX, (H_M, 5.5),
        m_req_M=0.0, max_cegis_rounds=10,
        p_ruin=0.0, v_ruin=0.0, h_safe=H_M,
    )
    B_pwl, cert_B, _ = _cegis_lp_staying_barrier(
        B_M, H_M, A_MAX, Q_MAX, bL, bR, ETA_MIN, ETA_MAX,
        p_ruin=p, v_ruin=v_ruin, n_knots=26, target_W_pwl=W_M,
    )

    iv_one = Interval("1")
    iv_p = Interval(str(p))
    iv_vr = Interval(str(v_ruin))
    psi_10_iv = iv_eval_logpwl(Psi_pwl, Interval(str(B_M)))
    psi_28_iv = iv_eval_logpwl(Psi_pwl, Interval(str(H_M)))
    ep_10_hi = float(((iv_one - iv_p) * psi_10_iv + iv_p * iv_vr).to_float_bounds()[1])
    psi_28_hi = float(psi_28_iv.to_float_bounds()[1])

    ok_db, margin_db, _ = verify_derivative_below_bound(Psi_pwl, B_M, bL * (1.0 - p), A_MIN, Q_MIN, B_M, 0.44)
    ok_dh, margin_dh, _ = verify_derivative_below_bound(Psi_pwl, H_M, bL, A_MIN, Q_MIN, H_M, 0.57)
    assert ok_db and ok_dh, f"Case 5 <b/<h failed at p={p}: {(margin_db, margin_dh)}"

    exit_M = verify_adverse_exit_bb(W_M, ep_10_hi, A_MAX, Q_MAX, bL, bR, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M))
    exit_H1 = verify_adverse_exit_bb(W_H, psi_28_hi, A_MAX, Q_MAX, bL, bR, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80))
    W80 = float(iv_eval_logpwl(W_H, Interval("0.80")).to_float_bounds()[0])
    kp80 = float(eval_logpwl(kpH, np.array([0.80]))[0])
    L80 = float(np.clip(eval_logpwl(LH, np.array([0.80]))[0], 0.0, 0.999))
    Wkp80_lo = float(iv_eval_logpwl(W_H, Interval(kp80)).to_float_bounds()[0])
    ok_H2, exit_H2_lb = verify_H2_global_interval(W_H, kp80, L80, Wkp80_lo, psi_28_hi, A_MIN, A_MAX, Q_MIN, Q_MAX, bL, bR)

    assert exit_M["certified"] and exit_M["iv_certified"]
    assert exit_H1["certified"] and exit_H1["iv_certified"]
    assert ok_H2, f"Case 5 H2 failed at p={p}: {exit_H2_lb}"

    T_star, inf_WB, sup_PsiB = certify_staying_deadline_interval(
        B_pwl, Psi_pwl, W_M, BETA_MAX, B_M, H_M, p_ruin=p,
    )
    surv_lb = float((iv_one - iv_p).pow_int(T_star).to_float_bounds()[0])
    wM_10_lo = float(iv_eval_logpwl(W_M, Interval(str(B_M))).to_float_bounds()[0])
    wH_28_lo = float(iv_eval_logpwl(W_H, Interval(str(H_M))).to_float_bounds()[0])

    return p, {
        "p": float(p),
        "v_ruin": float(v_ruin),
        "h_safe": float(H_M),
        "Psi_net": pwl_to_dict(Psi_pwl),
        "W_M_net": pwl_to_dict(W_M),
        "kp_M_net": pwl_to_dict(kpM),
        "L_M_net": pwl_to_dict(LM),
        "W_H_net": pwl_to_dict(W_H),
        "kp_H_net": pwl_to_dict(kpH),
        "L_H_net": pwl_to_dict(LH),
        "B_net": pwl_to_dict(B_pwl),
        "metrics": {
            "T_star": int(T_star),
            "surv_prob_lb": float(surv_lb),
            "inf_W_B_lo": float(inf_WB),
            "sup_Psi_B_hi": float(sup_PsiB),
            "W_M_10": float(wM_10_lo),
            "W_H_28": float(wH_28_lo),
            "Psi_28": float(psi_28_hi),
            "exitM_lb_iv": float(exit_M["m_lb_iv"]),
            "exitH1_lb_iv": float(exit_H1["m_lb_iv"]),
            "exitH2_lb_iv": float(exit_H2_lb),
            "slope_b_margin": float(margin_db),
            "slope_h_margin": float(margin_dh),
            "d_ub_Psi_iv": float(cert_Psi["d_ub_iv"]),
            "d_ub_WM_iv": float(cert_WM["d_ub_iv"]),
            "d_ub_WH_iv": float(cert_WH["d_ub_iv"]),
            "d_ub_B_iv": float(cert_B["d_ub_iv"]),
        },
    }


def synth_case_5(seed: int) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 5: State-Dependent Endogenous Ruin p(K) = p * 1_{K < 0.28} (V_ruin=-60)")
    print("=" * 72)
    t0 = time.time()
    v_ruin = -60.0
    p_list = [0.01, 0.02, 0.05, 0.08]
    C_max = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    m_G = (ETA_MIN * Q_MIN) / C_max
    eta_max_c_M = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, B_M, B_M, 0.44)
    eta_max_c_H = ETA_MAX / _min_c_E_plus(A_MIN, Q_MIN, H_M, H_M, 0.57)
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 20, endpoint=False),
        np.geomspace(0.0012, 0.0050, 48, endpoint=False),
        np.geomspace(0.0050, 0.025, 24, endpoint=False),
        np.geomspace(0.025, 0.279, 36, endpoint=False),
        [0.279, H_M],
        np.geomspace(H_M, 60.0, 60),
    ]))
    tasks = [(pv, v_ruin, k_t_g, m_G, eta_max_c_M, eta_max_c_H) for pv in p_list]
    out: Dict[str, object] = {}
    with ProcessPoolExecutor(max_workers=min(4, os.cpu_count() or 2)) as pool:
        for pv, rec in pool.map(_case5_p_worker, tasks):
            out[f"{pv:.2f}"] = rec
            mt = rec["metrics"]
            print(
                f"  p={100*pv:3.0f}% | T*={mt['T_star']:2d}, Pr(surv)>={mt['surv_prob_lb']:.4f} | "
                f"M={mt['exitM_lb_iv']:+.3f}, H1={mt['exitH1_lb_iv']:+.3f}, H2={mt['exitH2_lb_iv']:+.3f} | "
                f"d_ub_Psi={mt['d_ub_Psi_iv']:+.5f}",
                flush=True,
            )
    print(f"  Case 5 completed in {time.time() - t0:.1f}s.")
    return out


# ---------------------------------------------------------------------------
# Case 6: Wide Parametric Box Stress Tests (MR Box 7.1 & Macro 10x Box)
# ---------------------------------------------------------------------------
def _wide_box_leaf(aL: float, aU: float, bL: float, bU: float, qL: float, qU: float, eL: float, eU: float, depth: int, max_depth: int) -> List[Dict[str, object]]:
    k_t_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.0012, 20, endpoint=False),
        np.geomspace(0.0012, 0.0050, 44, endpoint=False),
        np.geomspace(0.0050, 0.025, 22, endpoint=False),
        np.geomspace(0.025, 0.28, 34, endpoint=False),
        np.geomspace(0.28, 90.0, 42),
    ]))
    try:
        V_up_g, _, _ = _solve_teacher_vfi(aU, qU, bL, eL, eU, True, k_t_g)
        s_l = _safe_s_lo(eL, bL)
        d_h = _safe_D_hi(eU, bU)

        def _init_w(k):
            ka = np.asarray(k, dtype=np.float64)
            v = np.interp(np.log(np.clip(ka, 1e-4, 90.0)), np.log(k_t_g), V_up_g)
            v = np.where(ka < 1e-4, V_up_g[0] + s_l * np.log(np.maximum(ka, 1e-30) / 1e-4), v)
            return np.where(ka > 90.0, V_up_g[-1] + d_h * np.log(ka / 90.0), v)

        C_max = qU * H_M + F_A(aU, H_M, 1.0) - B_M
        m_G = (eL * qL) / C_max
        eta_c_M = eU / _min_c_E_plus(aL, qL, B_M, B_M, 0.44, eL, eU)
        eta_c_H = eU / _min_c_E_plus(aL, qL, H_M, H_M, 0.57, eL, eU)

        Psi_pwl, cert_Psi, _ = _cegis_lp_super_barrier(
            aU, bL, bU, qU, eL, eU, 1e-4, 90.0,
            init_vals_fn=_init_w,
            m_min_slope=m_G,
            pre_b_slope=(eta_c_M / bL) + 0.20,
            pre_h_slope=(eta_c_H / bL) + 0.08,
            max_cegis_rounds=12,
        )
        W_pwl, kp_pwl, L_pwl, cert_W, _ = _cegis_lp_witness(
            aL, qL, bL, bU, eL, eU, (B_M, 5.5), m_req_M=m_G, max_cegis_rounds=8,
        )
        psi_10_hi = float(iv_eval_logpwl(Psi_pwl, Interval(str(B_M))).to_float_bounds()[1])
        psi_28_hi = float(iv_eval_logpwl(Psi_pwl, Interval(str(H_M))).to_float_bounds()[1])

        ok_db, m_db, _ = verify_derivative_below_bound(Psi_pwl, B_M, bL, aL, qL, B_M, 0.44, eL=eL, eU=eU)
        ok_dh, m_dh, _ = verify_derivative_below_bound(Psi_pwl, H_M, bL, aL, qL, H_M, 0.57, eL=eL, eU=eU)
        if not (ok_db and ok_dh):
            raise AssertionError(f"<b/<h failed: {m_db}, {m_dh}")

        ex_M = verify_adverse_exit_bb(W_pwl, psi_10_hi, aU, qU, bL, bU, eL, eU, B_M, 0.44, (B_M, H_M))
        ex_H1 = verify_adverse_exit_bb(W_pwl, psi_28_hi, aU, qU, bL, bU, eL, eU, H_M, 0.57, (H_M, 0.80))
        W80 = float(iv_eval_logpwl(W_pwl, Interval("0.80")).to_float_bounds()[0])
        kp80 = float(eval_logpwl(kp_pwl, np.array([0.80]))[0])
        L80 = float(np.clip(eval_logpwl(L_pwl, np.array([0.80]))[0], 0.0, 0.999))
        Wkp80_lo = float(iv_eval_logpwl(W_pwl, Interval(kp80)).to_float_bounds()[0])
        ok_H2, ex_H2_lb = verify_H2_global_interval(W_pwl, kp80, L80, Wkp80_lo, psi_28_hi, aL, aU, qL, qU, bL, bU, eL=eL, eU=eU)
        if not (ex_M["certified"] and ex_H1["certified"] and ok_H2):
            raise AssertionError(f"Exit failed: M={ex_M['m_lb_iv']}, H1={ex_H1['m_lb_iv']}, H2={ex_H2_lb}")

        B_pwl, cert_B, _ = _cegis_lp_staying_barrier(
            B_M, H_M, aU, qU, bL, bU, eL, eU, n_knots=24, target_W_pwl=W_pwl,
        )
        T_full, inf_WB, sup_PsiB = certify_staying_deadline_interval(B_pwl, Psi_pwl, W_pwl, bU, B_M, H_M)
        return [{
            "aL": aL, "aU": aU, "bL": bL, "bU": bU, "qL": qL, "qU": qU, "eL": eL, "eU": eU,
            "B_net": pwl_to_dict(B_pwl),
            "Psi_net": pwl_to_dict(Psi_pwl),
            "W_net": pwl_to_dict(W_pwl),
            "kp_net": pwl_to_dict(kp_pwl),
            "L_net": pwl_to_dict(L_pwl),
            "metrics": {
                "T_full": int(T_full),
                "inf_W_B_lo": float(inf_WB),
                "sup_Psi_B_hi": float(sup_PsiB),
                "exitM_lb_iv": float(ex_M["m_lb_iv"]),
                "exitH1_lb_iv": float(ex_H1["m_lb_iv"]),
                "exitH2_lb_iv": float(ex_H2_lb),
                "slope_b_margin": float(m_db),
                "slope_h_margin": float(m_dh),
                "d_ub_Psi_iv": float(cert_Psi["d_ub_iv"]),
                "d_ub_W_iv": float(cert_W["d_ub_iv"]),
                "d_ub_B_iv": float(cert_B["d_ub_iv"]),
            },
        }]
    except AssertionError:
        if depth >= max_depth:
            raise
        # Split whichever dimension has largest spread relative to baseline MR unit
        ratios = [
            ((bU - bL) / 0.0002, "b"),
            ((aU - aL) / 0.0020, "a"),
            ((qU - qL) / 0.0002, "q"),
            ((eU - eL) / 0.0002, "e"),
        ]
        axis = max(ratios, key=lambda t: t[0])[1]
        if axis == "b":
            bm = 0.5 * (bL + bU)
            return _wide_box_leaf(aL, aU, bL, bm, qL, qU, eL, eU, depth + 1, max_depth) + _wide_box_leaf(aL, aU, bm, bU, qL, qU, eL, eU, depth + 1, max_depth)
        elif axis == "a":
            am = 0.5 * (aL + aU)
            return _wide_box_leaf(aL, am, bL, bU, qL, qU, eL, eU, depth + 1, max_depth) + _wide_box_leaf(am, aU, bL, bU, qL, qU, eL, eU, depth + 1, max_depth)
        elif axis == "q":
            qm = 0.5 * (qL + qU)
            return _wide_box_leaf(aL, aU, bL, bU, qL, qm, eL, eU, depth + 1, max_depth) + _wide_box_leaf(aL, aU, bL, bU, qm, qU, eL, eU, depth + 1, max_depth)
        else:
            em = 0.5 * (eL + eU)
            return _wide_box_leaf(aL, aU, bL, bU, qL, qU, eL, em, depth + 1, max_depth) + _wide_box_leaf(aL, aU, bL, bU, qL, qU, em, eU, depth + 1, max_depth)


def _wide_box_task(task):
    return _wide_box_leaf(*task)


def _run_wide_box(name: str, a_rng, b_rng, q_rng, e_rng, n_a_init: int, n_b_init: int, max_depth: int) -> Dict[str, object]:
    t0 = time.time()
    a_pts = np.linspace(a_rng[0], a_rng[1], n_a_init + 1)
    b_pts = np.linspace(b_rng[0], b_rng[1], n_b_init + 1)
    tasks = []
    for ia in range(n_a_init):
        for ib in range(n_b_init):
            tasks.append((float(a_pts[ia]), float(a_pts[ia + 1]), float(b_pts[ib]), float(b_pts[ib + 1]), q_rng[0], q_rng[1], e_rng[0], e_rng[1], 0, max_depth))
    leaves: List[Dict[str, object]] = []
    n_w = min(12, len(tasks), os.cpu_count() or 4)
    with ProcessPoolExecutor(max_workers=n_w) as pool:
        for res in pool.map(_wide_box_task, tasks):
            leaves.extend(res)
    dt = time.time() - t0
    T_worst = max(lf["metrics"]["T_full"] for lf in leaves)
    min_exit_M = min(lf["metrics"]["exitM_lb_iv"] for lf in leaves)
    min_exit_H1 = min(lf["metrics"]["exitH1_lb_iv"] for lf in leaves)
    min_exit_H2 = min(lf["metrics"]["exitH2_lb_iv"] for lf in leaves)
    print(
        f"  [{name}] subboxes={len(leaves)}, T_full_worst={T_worst}, "
        f"min_exits=(M:{min_exit_M:+.3f}, H1:{min_exit_H1:+.3f}, H2:{min_exit_H2:+.3f}), synth_time={dt:.1f}s",
        flush=True,
    )
    return {
        "name": name,
        "bounds": {"A": list(a_rng), "beta": list(b_rng), "q": list(q_rng), "eta": list(e_rng)},
        "n_subboxes": int(len(leaves)),
        "T_full_worst": int(T_worst),
        "min_exitM_lb_iv": float(min_exit_M),
        "min_exitH1_lb_iv": float(min_exit_H1),
        "min_exitH2_lb_iv": float(min_exit_H2),
        "synth_sec": float(dt),
        "subboxes": leaves,
    }


def synth_case_6(seed: int) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 6: Wide Parametric Box Stress Tests (MR Box 7.1 & Macro 10x Box)")
    print("=" * 72)
    # 6A: MR Eq. (7.1): A in [0.749, 0.751], beta, q, eta +/- 0.001 (10x)
    box_71 = _run_wide_box(
        "MR_Box_7_1",
        (0.749, 0.751), (0.969, 0.971), (0.919, 0.921), (0.699, 0.701),
        n_a_init=1, n_b_init=8, max_depth=3,
    )
    # 6B: Macro 10x Box: A in [0.74, 0.76], beta, q, eta +/- 0.001 (10x in all 4 axes)
    box_10x = _run_wide_box(
        "Macro_10x_Box",
        (0.74, 0.76), (0.969, 0.971), (0.919, 0.921), (0.699, 0.701),
        n_a_init=2, n_b_init=8, max_depth=4,
    )
    return {"mr_box_7_1": box_71, "macro_10x_box": box_10x}


def _load_archive(path: str) -> Dict[str, object]:
    if path.endswith(".xz"):
        with lzma.open(path, "rt", encoding="utf-8") as f:
            return json.load(f)
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser(description="Adaptive CEGIS Log-PWL Synthesis Engine for Article A.")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--case", type=str, default="all", choices=["all", "1", "2", "3", "4", "5", "6"])
    parser.add_argument("--out", type=str, default="cegis_certificates.json.xz")
    args = parser.parse_args()

    print(f"CEGIS-PWL Synthesis Engine | 100% Deterministic HiGHS-LP (0 PyTorch), seed={args.seed}")

    out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), args.out)
    payload: Dict[str, object] = {}
    if os.path.exists(out_path) and args.case != "all":
        payload = _load_archive(out_path)

    payload["meta"] = {"seed": args.seed, "backend": "highs_lp_deterministic", "format": "json_xz"}
    t_start = time.time()

    if args.case in ("all", "1"):
        payload["case1_affine_gap"] = synth_case_1(args.seed)
    if args.case in ("all", "2"):
        payload["case2_ruin_hazard"] = synth_case_2(args.seed)
    if args.case in ("all", "3"):
        payload["case3_markov_h1"] = synth_case_3(args.seed)
    if args.case in ("all", "4"):
        B_reuse = None
        if "case1_affine_gap" in payload:
            c1 = payload["case1_affine_gap"]
            B_reuse = pwl_from_dict(c1.get("B_pwl", c1["B_net"]))
        payload["case4_ak_regime"] = synth_case_4(args.seed, B_pwl_reuse=B_reuse)
    if args.case in ("all", "5"):
        payload["case5_endogenous_ruin"] = synth_case_5(args.seed)
    if args.case in ("all", "6"):
        payload["case6_wide_boxes"] = synth_case_6(args.seed)

    if out_path.endswith(".xz"):
        with lzma.open(out_path, "wt", encoding="utf-8", preset=6) as f:
            json.dump(payload, f, separators=(",", ":"))
    else:
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
    sz_mb = os.path.getsize(out_path) / (1024.0 * 1024.0)
    print(f"\nSaved audited CEGIS certificates to {out_path} ({sz_mb:.2f} MB) in {time.time() - t_start:.1f}s.")


if __name__ == "__main__":
    main()
