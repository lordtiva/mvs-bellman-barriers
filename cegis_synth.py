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
    HAS_TORCH,
    LogReLUNetwork,
    make_pwl_from_knots,
    pwl_to_dict,
    eval_logpwl,
    optimize_numpy_adam,
)
if HAS_TORCH:
    import torch
    from pwl_model import TorchLogReLUModule

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
    compute_doob_eps0_interval,
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


def _select_backend(requested: str) -> str:
    if requested == "torch" and HAS_TORCH:
        return "torch"
    return "numpy"


def _torch_device(backend: str) -> str:
    if backend == "torch" and HAS_TORCH:
        return "cuda" if torch.cuda.is_available() else "cpu"
    return "cpu"


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
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    lk_g = np.log(k_grid)
    s_lo = eL / (1.0 - bv)
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

    inv_phi_t = (math.sqrt(5.0) - 1.0) / 2.0
    Y_max_row = Y_mat[:, -1]
    pol_kp = np.zeros_like(k_grid)
    pol_L = np.zeros_like(k_grid)
    for it_v in range(140):
        tot = u_3 + bv * _interp(y_3, V)
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
            f1 = u1 + bv * _interp(x1, V)
            f2 = u2 + bv * _interp(x2, V)
            for _g in range(14):
                mr = f1 < f2
                lo_k = np.where(mr, x1, lo_k)
                hi_k = np.where(mr, hi_k, x2)
                x1n = np.where(mr, x2, hi_k - inv_phi_t * (hi_k - lo_k))
                x2n = np.where(mr, lo_k + inv_phi_t * (hi_k - lo_k), x1)
                _, u1n = _golden_L_vec(Av, qv, eL, eU, k_grid, x1n, is_upper=False, ak_mode=ak_mode)
                _, u2n = _golden_L_vec(Av, qv, eL, eU, k_grid, x2n, is_upper=False, ak_mode=ak_mode)
                f1n = np.where(mr, f2, u1n + bv * _interp(x1n, V))
                f2n = np.where(mr, u2n + bv * _interp(x2n, V), f1)
                x1, x2, f1, f2 = x1n, x2n, f1n, f2n
            kp_ref = np.where(f1 > f2, x1, x2)
            L_ref, u_ref = _golden_L_vec(Av, qv, eL, eU, k_grid, kp_ref, is_upper=False, ak_mode=ak_mode)
            use_ref = (u_ref + bv * _interp(kp_ref, V)) > Vn
            pol_kp = np.where(use_ref, kp_ref, pol_kp)
            pol_L = np.where(use_ref, L_ref, pol_L)
            u_pol = np.where(use_ref, u_ref, u_pol)
            Vn = np.where(use_ref, u_ref + bv * _interp(kp_ref, V), Vn)
        for _h in range(25):
            Vn = u_pol + bv * _interp(pol_kp, Vn)
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
) -> Tuple[Dict[str, object], Dict[str, object], List[Dict[str, object]]]:
    """
    Pure HiGHS-LP CEGIS loop synthesizing a global super-barrier Psi(log K) on
    (0, inf) x [bL, bR], with adaptive knot insertion at worst B&B counterexamples.
    Guarantees d_ub_raw <= 0 BEFORE any shift and 100% outward-rounded iv_certified.
    """
    s_lo = _safe_s_lo(eL, bL)
    D_hi = _safe_D_hi(eU, bR)

    # Compact initial knot set (~185 knots, >= 3x smaller than 645)
    k_knots = np.unique(np.concatenate([
        [k_lo],
        np.geomspace(k_lo, 0.0012, 24, endpoint=False),
        np.geomspace(0.0012, 0.0040, 56, endpoint=False),
        np.geomspace(0.0040, 0.04, 28, endpoint=False),
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
    r_top = q_hi + F_A(Av, k_lo, 1.0) / k_lo
    tlo_consts = []
    for bv_t in (bL, bR):
        c_slo = eL + bv_t * s_lo
        s_lo_opt = (bv_t * s_lo) / c_slo
        tlo_consts.append((
            bv_t,
            eL * math.log((1.0 - s_lo_opt) * k_lo) + bv_t * s_lo * math.log(s_lo_opt) + c_slo * math.log(r_top),
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
            eva = init_vals_fn(ya.ravel()).reshape(ya.shape)
        else:
            eva = eval_logpwl(last_pwl, ya)
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

        Mx, _ = _eval_pwl_basis_sparse(z_knots, zx_col, s_lo, D_hi)
        My, oy = _eval_pwl_basis_sparse(z_knots, zy_col, s_lo, D_hi)

        # Solve pure HiGHS LP directly for y_knots (2 sign-update passes if values cross 0)
        y_cur = init_vals_fn(k_knots) if last_pwl is None else eval_logpwl(last_pwl, k_knots)
        req_s = np.where((k_knots[:-1] >= B_M - 1e-9) & (k_knots[1:] <= H_M + 1e-9), m_min_slope, 0.0)
        if pre_b_slope > 0.0:
            req_s = np.where(k_knots[:-1] < B_M + 1e-9, np.maximum(req_s, pre_b_slope), req_s)
        if pre_h_slope > 0.0:
            req_s = np.where(k_knots[:-1] < H_M + 1e-9, np.maximum(req_s, pre_h_slope), req_s)
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

        # Objective: tighten Psi on M union {h} with global regularizer + L1 log-slope TV
        c_obj_y = np.zeros(n_k, dtype=np.float64)
        m_mask = (k_knots >= B_M - 1e-9) & (k_knots <= H_M + 1e-9)
        c_obj_y[m_mask] = 1.0 / max(1, int(np.sum(m_mask)))
        c_obj_y += 1e-3 / n_k
        c_obj = np.concatenate([c_obj_y, np.full(n_tv, 5e-4, dtype=np.float64)])
        lp_bounds = [(-2500.0, 2500.0)] * n_k + [(0.0, None)] * n_tv

        m_hi_c = 0.0045 if ak_mode else 0.0020
        m_base = np.where(col_x >= 0.05, m_hi_c, 0.018)
        solved = False
        for m_scale in (1.0, 0.65, 0.35, 0.15, 0.05):
            m_vec = m_scale * m_base
            m_t_lo = m_scale * 0.018
            m_t_hi = m_scale * 0.0020
            y_try = y_cur.copy()
            ok_pass = False
            for _sp in range(2):
                vy_est = My @ y_try + oy
                near0 = np.abs(vy_est) <= 1.5
                A_rows = [A_mon]
                b_rows = [b_mon]
                for bv_c, m_c in ((bL, (vy_est < 0.0) | near0), (bR, (vy_est >= 0.0) | near0)):
                    if np.any(m_c):
                        A_rows.append(bv_c * My[m_c] - Mx[m_c])
                        b_rows.append(-(u_col[m_c] + bv_c * oy[m_c] + m_vec[m_c]))
                # Tails
                for bv_t, tc in tlo_consts:
                    A_rows.append(sp.csr_matrix(([-(1.0 - bv_t)], ([0], [0])), shape=(1, n_k)))
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
        cert = verify_super_barrier_bb(pwl, pwl, Av, bL, bR, q_hi=q_hi, eL=eL, eU=eU, tol=tol_bb, ak_mode=ak_mode)
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
) -> Tuple[Dict[str, object], Dict[str, object], Dict[str, object], Dict[str, object], List[Dict[str, object]]]:
    """
    Pure HiGHS-LP CEGIS loop synthesizing continuous feasible sub-solution witness
    (W, kp, L) on k_domain = [k_a, k_b], explicitly enforcing W'(x) >= m_req_M on M
    and auditing 100% of leaf intervals in 50-digit Decimal Interval arithmetic.
    """
    k_a, k_b = k_domain
    k_grid = np.unique(np.concatenate([
        np.geomspace(k_a, min(H_M, k_b), 52, endpoint=False),
        np.geomspace(min(H_M, k_b), min(0.80, k_b), 52, endpoint=False),
        np.geomspace(min(0.80, k_b), k_b, 56),
    ]))
    V_t, kp_t, L_t = _solve_teacher_vfi(Av, qv, bR, eL, eU, False, k_grid, ak_mode=ak_mode)
    kp_t = np.maximum(kp_t, k_a * 1.005) if ak_mode else np.clip(kp_t, k_a * 1.005, k_b * 0.995)
    L_t = np.clip(L_t, 0.0, 0.985)

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

    k_knots = np.unique(np.concatenate([
        [k_a],
        [H_M, 0.80] if (k_a < H_M < 0.80 < k_b) else [],
        np.geomspace(k_a * 1.005, min(H_M, k_b * 0.995), 24, endpoint=False),
        np.geomspace(min(H_M, k_b * 0.995), min(0.80, k_b * 0.995), 24, endpoint=False),
        np.geomspace(min(0.80, k_b * 0.995), k_b * 0.995, 24),
        [k_b],
    ]))
    s_hi_w = _safe_s_lo(eL, bL) if ak_mode else 0.0

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

        Mx, _ = _eval_pwl_basis_sparse(z_knots, np.log(col_k), 0.0, s_hi_w)
        My, oy = _eval_pwl_basis_sparse(z_knots, np.log(kp_col), 0.0, s_hi_w)

        # Monotonicity on M (Fix 5) and non-decreasing everywhere
        req_s = np.where((k_knots[:-1] < H_M - 1e-12) & (k_knots[1:] > B_M + 1e-12), m_req_M, 0.0)
        A_mon = _monotone_diff_sparse(n_w)
        b_mon = -(req_s * k_knots[1:] * dlk)

        c_w = -np.ones(n_w, dtype=np.float64) / n_w
        c_w[0] -= 0.40
        i_h = int(np.argmin(np.abs(k_knots - H_M)))
        c_w[i_h] -= 0.25

        y_try = np.interp(z_knots, np.log(k_grid), V_t)
        solved_w = False
        for m_trg in (2.5e-4, 1.0e-4, 4.0e-5):
            yt = y_try.copy()
            ok_p = False
            for _sp in range(2):
                wy_est = My @ yt + oy
                near0 = np.abs(wy_est) <= 1.5
                A_rows = [A_mon]
                b_rows = [b_mon]
                for bv_c, m_c in ((bR, (wy_est < 0.0) | near0), (bL, (wy_est >= 0.0) | near0)):
                    if np.any(m_c):
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
        if ins_k and len(k_knots) < 160:
            cand_add = [ck for ck in ins_k if np.min(np.abs(np.log(k_knots) - math.log(ck))) > 1.5e-3]
            if cand_add:
                k_knots = np.unique(np.concatenate([k_knots, np.array(cand_add[:12])]))

    assert best_W is not None and best_cert is not None and best_cert["certified"] and best_cert["iv_certified"], (
        f"Witness CEGIS-LP failed certification: {history[-1]}"
    )
    if m_req_M > 0.0:
        sl_ok, min_sl = verify_witness_slope_on_M(best_W, m_req_M)
        assert sl_ok, f"Witness slope on M failed: {min_sl:.4f} < {m_req_M:.4f}"
    return best_W, kp_pwl, L_pwl, best_cert, history


# ---------------------------------------------------------------------------
# Case 1: Staying Barrier B_theta (24 moving knots, T <= 9) + CEGIS-LP Psi/W
# ---------------------------------------------------------------------------
def synth_case_1(seed: int, backend: str) -> Dict[str, object]:
    print("\n" + "=" * 72)
    print("CASE 1: Adaptive Log-PWL Staying Barrier B_theta (T <= 9) & M0 Check")
    print("=" * 72)
    t0 = time.time()

    M_g = np.linspace(B_M, H_M, 65)
    B_dp = np.full_like(M_g, -40.0)
    Ls_w = np.linspace(0.0, 0.99, 40)
    Y_w = Q_MAX * M_g[:, None] + F_A(A_MAX, M_g[:, None], Ls_w[None, :])
    c_w = Y_w[:, :, None] - M_g[None, None, :]
    ec_w = np.where(c_w < 1.0, ETA_MIN, ETA_MAX)
    u_w = np.where(c_w > 1e-12, ec_w * np.log(np.maximum(c_w, 1e-30)) + (1.0 - ETA_MAX) * np.log(1.0 - Ls_w[None, :, None]), -1e9)
    rho_w = np.max(u_w, axis=1)
    for _ in range(500):
        Bn = np.max(rho_w + BETA_MIN * B_dp[None, :], axis=1)
        if np.max(np.abs(Bn - B_dp)) < 1e-9:
            B_dp = Bn
            break
        B_dp = Bn

    B_net = LogReLUNetwork(B_M, H_M, hidden_sizes=(24,), seed=seed)
    B_net.fit_linear_head_lstsq(M_g, B_dp, ridge=1e-8)

    gx, gy = np.meshgrid(np.linspace(B_M, H_M, 30), np.linspace(B_M, H_M, 30), indexing="ij")
    col_x, col_y = gx.ravel(), gy.ravel()
    col_L, col_u = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, col_x, col_y, is_upper=True)
    ok = col_u > -1e8
    col_x, col_y, col_L, col_u = col_x[ok], col_y[ok], col_L[ok], col_u[ok]

    history: List[Dict[str, object]] = []
    dev = _torch_device(backend)

    for rnd in range(1, 7):
        zx, zy, zm = np.log(col_x), np.log(col_y), np.log(M_g)
        if backend == "torch" and HAS_TORCH:
            mod = TorchLogReLUModule(B_net, device=dev)
            zxt = torch.tensor(zx, dtype=torch.float64, device=dev)
            zyt = torch.tensor(zy, dtype=torch.float64, device=dev)
            ut = torch.tensor(col_u, dtype=torch.float64, device=dev)
            zmt = torch.tensor(zm, dtype=torch.float64, device=dev)
            opt = torch.optim.Adam(mod.parameters(), lr=5e-3)
            for _ in range(280):
                opt.zero_grad()
                bx = mod.forward_log(zxt)
                by = mod.forward_log(zyt)
                be = torch.where(by < 0.0, BETA_MIN, BETA_MAX)
                viol = torch.relu(ut + be * by - bx + 1e-3)
                loss = 60.0 * torch.mean(viol ** 2) + 8.0 * torch.max(viol ** 2) + 2e-3 * torch.mean(mod.forward_log(zmt))
                loss.backward()
                opt.step()
            mod.sync_to_numpy(B_net)
        else:
            def l_g():
                bx, Jx = B_net.forward_and_grad_params(zx)
                by, Jy = B_net.forward_and_grad_params(zy)
                be = np.where(by < 0.0, BETA_MIN, BETA_MAX)
                viol = np.maximum(col_u + be * by - bx + 1e-3, 0.0)
                dv = (120.0 / len(zx)) * viol
                im = int(np.argmax(viol))
                dv[im] += 16.0 * viol[im]
                _, Jm = B_net.forward_and_grad_params(zm)
                grad = Jx.T @ (-dv) + Jy.T @ (dv * be) + (2e-3 / len(zm)) * np.sum(Jm, axis=0)
                loss = float(60.0 * np.mean(viol ** 2) + 8.0 * np.max(viol) ** 2 + 2e-3 * np.mean(B_net.forward_log(zm)))
                return loss, [grad]
            optimize_numpy_adam([B_net], l_g, steps=280, lr=8e-3)

        B_pwl = B_net.extract_exact_log_pwl()
        cert = verify_staying_barrier_bb(B_pwl, tol=2e-4)
        history.append({"round": rnd, "knots": int(len(B_pwl["ks"])), "d_ub": float(cert["d_ub"]), "d_ub_iv": float(cert["d_ub_iv"])})
        if cert["certified"] and cert["iv_certified"]:
            break
        for cx, cy, _, _ in cert["counterexamples"]:
            _, cu = _golden_L_vec(A_MAX, Q_MAX, ETA_MIN, ETA_MAX, np.array([cx]), np.array([cy]), is_upper=True)
            if cu[0] > -1e8:
                col_x = np.append(col_x, cx); col_y = np.append(col_y, cy); col_u = np.append(col_u, float(cu[0]))

    B_pwl = B_net.extract_exact_log_pwl()
    cert = verify_staying_barrier_bb(B_pwl, tol=2e-4)
    if not cert["certified"]:
        B_net.c0 += (max(cert["d_ub"], cert["d_ub_iv"]) + 3e-4) / (1.0 - BETA_MIN)
        B_pwl = B_net.extract_exact_log_pwl()
        cert = verify_staying_barrier_bb(B_pwl, tol=2e-4)
    assert cert["certified"] and cert["iv_certified"], f"Case 1 staying barrier failed: {cert}"

    # Pure CEGIS-LP (Psi, W) for Case 1 + sharpened M0 tau_.1 <= 9 check
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

    # Continuous 50-digit Interval deadline checks (Fix 2: eliminates discrete m_fine)
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
    dt = time.time() - t0
    print(f"  B_theta knots={len(B_pwl['ks'])}, d_ub_iv={cert['d_ub_iv']:.6f} (leaves={cert['leaf_count']}) | B(0.10)={B_010:.4f}, B(0.28)={B_028:.4f}")
    print(f"  Interval vs MR-Table 4 / Psi#: inf(W-B)={inf_W_B_base:.4f}, sup(Psi#-B)={sup_Psi_B_base:.4f} -> T_theta = {T_theta_base}")
    print(f"  Interval CEGIS-LP triple: knots(Psi,W)=({len(Psi_pwl['ks'])},{len(W_pwl['ks'])}), inf={inf_W_B_cegis:.4f}, sup={sup_Psi_B_cegis:.4f} -> T_full = {T_theta_full}, min_dPsi_M0={min_dPsi_M0:.2f} ({dt:.1f}s)")
    assert T_theta_base <= 9 and T_theta_full <= 9

    return {
        "B_net": B_net.to_dict(),
        "Psi_net": pwl_to_dict(Psi_pwl),
        "W_net": pwl_to_dict(W_pwl),
        "kp_net": pwl_to_dict(kp_pwl),
        "L_net": pwl_to_dict(L_pwl),
        "metrics": {
            "d_ub_stay": float(cert["d_ub"]),
            "d_ub_stay_iv": float(cert["d_ub_iv"]),
            "B_010": B_010,
            "B_028": B_028,
            "T_theta_base": T_theta_base,
            "T_theta_full": T_theta_full,
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
        "history": history,
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


def _case3_subbox_p_worker(task: Tuple[int, float, float, float, float, float, float, float, float, float]) -> Tuple[int, float, float, int]:
    """
    Granular unified CEGIS-LP worker certifying one ((AG, AB, q, eta) subbox, p) pair
    continuously across [BETA_MIN, BETA_MAX], starting at n_init=2 beta bands and
    adaptively bisecting beta only if needed.
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

    def _check_band(bL_s: float, bR_s: float, depth: int) -> Tuple[float, int]:
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
            _, WB_s, _, _, _, _, _, _ = _cegis_lp_coupled_markov_witness(
                p, bL_s, bR_s, k_w, VG_l, VB_l, kpG_l, LG_l, kpB_l, LB_l,
                agL, abL, qL_s, eL_s, eU_s, m_G, m_B, max_rounds=10, interval_check=True,
            )
            rb = verify_adverse_exit_bb(WB_s, evBh, abU, qU_s, bL_s, bR_s, eL_s, eU_s, H_M, 0.603, (H_M, 0.80), interval_check=True)
            if (ok_hB and rb["certified"] and rb["iv_certified"] and rb["m_lb_iv"] > 0.0) or depth >= 3:
                return float(rb["m_lb_iv"]), 1
        except AssertionError:
            if depth >= 3:
                raise
        bM_s = 0.5 * (bL_s + bR_s)
        m1, n1 = _check_band(bL_s, bM_s, depth + 1)
        m2, n2 = _check_band(bM_s, bR_s, depth + 1)
        return min(m1, m2), n1 + n2

    n_init = 4 if p <= 0.015 else 2
    init_depth = 2 if n_init == 4 else 1
    b_edges = np.linspace(BETA_MIN, BETA_MAX, n_init + 1)
    m_sub = 1e9
    n_lf = 0
    for jb in range(n_init):
        mj, nj = _check_band(float(b_edges[jb]), float(b_edges[jb + 1]), init_depth)
        m_sub = min(m_sub, mj)
        n_lf += nj
    return sub_idx, p, m_sub, n_lf


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

        ok_all = (
            ok_bG and ok_bB and ok_hG and ok_hB
            and ok_H2_G and ok_H2_B
            and m_M_G["certified"] and m_M_B["certified"] and m_H1_G["certified"]
            and eps0 > 0.0
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
                f"  p={100*p:4.1f}% [{len(all_leaf_bands)}-beta] | stay=({worst_metrics['margG']:.2f},{worst_metrics['margB']:.2f}) "
                f"T*=({worst_metrics['T_G']},{worst_metrics['T_B']}) | "
                f"M:G/B={worst_metrics['m_M_G_iv']:+.2f}/{worst_metrics['m_M_B_iv']:+.3f} "
                f"H1_G={worst_metrics['m_H1_G_iv']:+.2f} H2:G/B={worst_metrics['mH2_G_lb_iv']:+.2f}/{worst_metrics['mH2_B_lb_iv']:+.2f} | "
                f"eps0={worst_metrics['eps_0_lb']:.4f}",
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
    print(f"  Launching {len(sb_tasks)} flattened (subbox x p) CEGIS-LP+Rust tasks across {n_workers} workers...", flush=True)
    pbar2 = ProgressBar("Caso 3 | Fase 2 (256 subcajas H1_B)", len(sb_tasks), min_interval_sec=1.5)
    with ProcessPoolExecutor(max_workers=n_workers) as pool:
        futs = [pool.submit(_case3_subbox_p_worker, t) for t in sb_tasks]
        for fut in as_completed(futs):
            r_idx, pv, ms, nl = fut.result()
            hb_min_p[pv] = min(hb_min_p[pv], ms)
            hb_lf_p[pv] += nl
            pbar2.update(1, suffix=f"sub={r_idx:02d} p={100*pv:.1f}% H1_B={ms:+.3f}")

    for p in p_list:
        mt = markov_out[f"{p:.3f}"]["metrics"]
        m_hb = float(hb_min_p[p])
        mt["m_H1_B_32bx"] = m_hb
        mt["subbox_beta_split"] = int(hb_lf_p[p])
        print(f"  p={100*p:4.1f}% SUMMARY | H1_B_32bx_iv={m_hb:+.4f} (leaves={hb_lf_p[p]}) | eps0={mt['eps_0_lb']:.4f}", flush=True)
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


def main():
    parser = argparse.ArgumentParser(description="Adaptive CEGIS Log-PWL Synthesis Engine for Article A.")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--case", type=str, default="all", choices=["all", "1", "2", "3", "4"])
    parser.add_argument("--backend", type=str, default="torch", choices=["numpy", "torch"])
    parser.add_argument("--out", type=str, default="cegis_certificates.json")
    args = parser.parse_args()

    backend = _select_backend(args.backend)
    print(f"CEGIS-PWL Synthesis Engine | backend={backend} (case 1 only), seed={args.seed}")

    out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), args.out)
    payload: Dict[str, object] = {}
    if os.path.exists(out_path) and args.case != "all":
        with open(out_path, "r", encoding="utf-8") as f:
            payload = json.load(f)

    payload["meta"] = {"seed": args.seed, "backend": backend, "device": _torch_device(backend)}
    t_start = time.time()

    if args.case in ("all", "1"):
        payload["case1_affine_gap"] = synth_case_1(args.seed, backend)
    if args.case in ("all", "2"):
        payload["case2_ruin_hazard"] = synth_case_2(args.seed)
    if args.case in ("all", "3"):
        payload["case3_markov_h1"] = synth_case_3(args.seed)
    if args.case in ("all", "4"):
        B_reuse = None
        if "case1_affine_gap" in payload:
            from pwl_model import pwl_from_dict
            B_reuse = pwl_from_dict(payload["case1_affine_gap"]["B_net"])
        payload["case4_ak_regime"] = synth_case_4(args.seed, B_pwl_reuse=B_reuse)

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)
    print(f"\nSaved audited CEGIS certificates to {out_path} in {time.time() - t_start:.1f}s.")


if __name__ == "__main__":
    main()
