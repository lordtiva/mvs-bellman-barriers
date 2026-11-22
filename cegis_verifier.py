"""
Exact Branch-and-Bound (B&B) and 100% Outward-Rounded Interval Auditor
for Adaptive CEGIS Log-PWL Barriers and Witnesses.

Implements all 6 mandatory soundness & completeness guarantees:
  1. Exact dE_plus/dK in `verify_adverse_exit_bb` using the Proposition 1**
     identity (and full envelope term when omega* = 1).
  2. 100% outward-rounded interval terminal audit on ALL 4 verifiers:
       - Numba IEEE-754 outward-rounded leaf audit for 3D B&B (Staying & Super)
       - 50-digit Decimal Interval leaf audit for 1D B&B (Witness & Adverse Exit)
       - 50-digit Decimal Interval audit for all analytical tails and Case 1 deadlines
  3. Continuous p-band certification support for Case 2 (p in [0, 0.02]).
  4. Full Case 3 (Markov) checks: exact Doob eps_0, <h derivative in state B,
     global H2 = [0.80, inf) in state B, and worst-case beta_+ reporting.
  5. Explicit segment-by-segment Interval monotonicity check W'(x) >= m_omega on M.
  6. Complete Case 4 (AK) certification on [0.28, inf), <b/<h derivative checks,
     EV monotonicity check, and 1D Interval B&B on L in [0, 1) for the AK upper tail.
"""

from __future__ import annotations

import ctypes
from decimal import Decimal
import math
import os
import platform
from typing import Dict, List, Optional, Tuple
import numpy as np

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
    F_A,
    dF_dK,
    dF_dL,
    E_plus_exact,
    box_worst_u,
    Interval,
    iv_F_A,
    iv_prod_Y,
    iv_prod_dY_dK,
    iv_prod_dY_dL,
    iv_box_worst_u,
    iv_E_plus_exact,
    iv_dE_plus_dK,
    iv_eval_logpwl,
    iv_deriv_bounds_logpwl,
    audit_staying_boxes_ivf,
    audit_super_boxes_ivf,
)
from pwl_model import (
    build_slope_tables,
    eval_logpwl,
    deriv_bounds_logpwl,
    range_bounds_logpwl,
)


# ---------------------------------------------------------------------------
# Optional Native Rust B&B + Outward-Rounded IEEE-754 Interval Verifier
# ---------------------------------------------------------------------------
class _RustBbOut(ctypes.Structure):
    _fields_ = [
        ("certified", ctypes.c_int32),
        ("iv_certified", ctypes.c_int32),
        ("d_ub", ctypes.c_double),
        ("d_ub_iv", ctypes.c_double),
        ("d_lb", ctypes.c_double),
        ("leaf_count", ctypes.c_size_t),
        ("n_ce", ctypes.c_size_t),
    ]


def _load_rust_verifier():
    if os.environ.get("MVS_USE_RUST", "1") == "0":
        return None
    sysname = platform.system()
    lib_name = (
        "mvs_verifier.dll" if sysname == "Windows"
        else ("libmvs_verifier.dylib" if sysname == "Darwin" else "libmvs_verifier.so")
    )
    lib_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rust_verifier", lib_name)
    if not os.path.exists(lib_path):
        return None
    try:
        lib = ctypes.CDLL(lib_path)
        c_dbl_p = ctypes.POINTER(ctypes.c_double)
        c_dbl = ctypes.c_double
        c_sz = ctypes.c_size_t
        c_i32 = ctypes.c_int32

        lib.rs_verify_staying_barrier_bb.argtypes = [
            c_dbl_p, c_dbl_p, c_dbl_p, c_dbl_p, c_sz, c_dbl, c_dbl,
            c_dbl, c_dbl, c_dbl, c_dbl, c_dbl, c_dbl,
            c_dbl, c_sz, c_dbl_p, c_sz,
        ]
        lib.rs_verify_staying_barrier_bb.restype = _RustBbOut

        lib.rs_verify_super_barrier_bb.argtypes = [
            c_dbl_p, c_dbl_p, c_dbl_p, c_dbl_p, c_sz, c_dbl, c_dbl,
            c_dbl_p, c_dbl_p, c_dbl_p, c_dbl_p, c_sz, c_dbl, c_dbl,
            c_dbl, c_dbl, c_dbl, c_dbl, c_dbl, c_dbl,
            c_dbl, c_dbl, c_i32, c_sz, c_sz, c_dbl_p, c_sz,
        ]
        lib.rs_verify_super_barrier_bb.restype = _RustBbOut

        lib.rs_verify_adverse_exit_bb.argtypes = [
            c_dbl_p, c_dbl_p, c_dbl_p, c_dbl_p, c_sz, c_dbl, c_dbl,
            c_dbl, c_dbl, c_dbl, c_dbl, c_dbl, c_dbl, c_dbl,
            c_dbl, c_dbl, c_dbl, c_dbl, c_i32,
            c_dbl, c_sz, c_i32, c_dbl_p, c_sz,
        ]
        lib.rs_verify_adverse_exit_bb.restype = _RustBbOut
        return lib
    except Exception:
        return None


_RUST_LIB = _load_rust_verifier()


def using_rust_verifier() -> bool:
    return _RUST_LIB is not None and os.environ.get("MVS_USE_RUST", "1") != "0"


# ---------------------------------------------------------------------------
# Float64 Production Helpers (used ONLY for B&B pruning; audited in intervals)
# ---------------------------------------------------------------------------
def prod_Y(A: float, K: np.ndarray, L: np.ndarray, ak_mode: bool = False) -> np.ndarray:
    if not ak_mode:
        return F_A(A, K, L)
    return np.where(K < H_M, F_A(A, K, L), (K / H_M) * F_A(A, H_M, L))


def prod_dY_dK_bounds(
    A: float, xL: np.ndarray, xR: np.ndarray, LL: np.ndarray, LR: np.ndarray, ak_mode: bool = False,
) -> Tuple[np.ndarray, np.ndarray]:
    px_hi = np.clip(LR / 4.0, xL, xR)
    lo_ces = np.minimum(dF_dK(A, xL, LL), dF_dK(A, xR, LL))
    hi_ces = np.maximum(np.maximum(dF_dK(A, xL, LR), dF_dK(A, xR, LR)), dF_dK(A, px_hi, LR))
    if not ak_mode:
        return lo_ces, hi_ces
    ak_lo = F_A(A, H_M, LL) / H_M
    ak_hi = F_A(A, H_M, LR) / H_M
    only_ak = xL >= H_M
    only_ces = xR <= H_M
    lo = np.where(only_ak, ak_lo, np.where(only_ces, lo_ces, np.minimum(lo_ces, ak_lo)))
    hi = np.where(only_ak, ak_hi, np.where(only_ces, hi_ces, np.maximum(hi_ces, ak_hi)))
    return lo, hi


def prod_dY_dL_bounds(
    A: float, xL: np.ndarray, xR: np.ndarray, LL: np.ndarray, LR: np.ndarray, ak_mode: bool = False,
) -> Tuple[np.ndarray, np.ndarray]:
    pL_hi = np.clip(xR / 4.0, LL, LR)
    lo_ces = np.minimum(dF_dL(A, xL, LL), dF_dL(A, xL, LR))
    hi_ces = np.maximum(np.maximum(dF_dL(A, xR, LL), dF_dL(A, xR, LR)), dF_dL(A, xR, pL_hi))
    if not ak_mode:
        return lo_ces, hi_ces
    pL_h = np.clip(H_M / 4.0, LL, LR)
    dFh_lo = np.minimum(dF_dL(A, H_M, LL), dF_dL(A, H_M, LR))
    dFh_hi = np.maximum(np.maximum(dF_dL(A, H_M, LL), dF_dL(A, H_M, LR)), dF_dL(A, H_M, pL_h))
    ak_lo = (xL / H_M) * dFh_lo
    ak_hi = (xR / H_M) * dFh_hi
    only_ak = xL >= H_M
    only_ces = xR <= H_M
    lo = np.where(only_ak, ak_lo, np.where(only_ces, lo_ces, np.minimum(lo_ces, ak_lo)))
    hi = np.where(only_ak, ak_hi, np.where(only_ces, hi_ces, np.maximum(hi_ces, ak_hi)))
    return lo, hi


# ---------------------------------------------------------------------------
# 1. Staying Barrier Verifier on M = [0.10, 0.28) (Case 1 & Case 4)
# ---------------------------------------------------------------------------
def verify_staying_barrier_bb(
    B_pwl: Dict[str, object],
    A_hi: float = A_MAX,
    q_hi: float = Q_MAX,
    b_lo: float = BETA_MIN,
    b_hi: float = BETA_MAX,
    e_lo: float = ETA_MIN,
    e_hi: float = ETA_MAX,
    tol: float = 2e-4,
    max_iter: int = 45,
) -> Dict[str, object]:
    """
    Certify staying Bellman inequality on ALL (x, y, L) in [B_M, H_M]^2 x [0, 1)
    and full parameter box, followed by 100% Numba IEEE-754 outward-rounded audit
    of EVERY leaf box.
    """
    if using_rust_verifier():
        ks_b = np.ascontiguousarray(B_pwl["ks"], dtype=np.float64)
        lks_b = np.ascontiguousarray(B_pwl["lks"], dtype=np.float64)
        vals_b = np.ascontiguousarray(B_pwl["vals"], dtype=np.float64)
        sl_b = np.ascontiguousarray(B_pwl["slopes"], dtype=np.float64)
        c_dbl_p = ctypes.POINTER(ctypes.c_double)
        ce_buf = np.empty(64 * 4, dtype=np.float64)
        res = _RUST_LIB.rs_verify_staying_barrier_bb(
            ks_b.ctypes.data_as(c_dbl_p), lks_b.ctypes.data_as(c_dbl_p),
            vals_b.ctypes.data_as(c_dbl_p), sl_b.ctypes.data_as(c_dbl_p),
            len(ks_b), float(B_pwl["s_lo"]), float(B_pwl["s_hi"]),
            float(A_hi), float(q_hi), float(b_lo), float(b_hi), float(e_lo), float(e_hi),
            float(tol), int(max_iter), ce_buf.ctypes.data_as(c_dbl_p), 64,
        )
        ces = [(float(ce_buf[4 * i]), float(ce_buf[4 * i + 1]), float(ce_buf[4 * i + 2]), float(ce_buf[4 * i + 3])) for i in range(res.n_ce)]
        return {
            "certified": bool(res.certified),
            "d_ub": float(res.d_ub),
            "d_ub_iv": float(res.d_ub_iv),
            "d_lb": float(res.d_lb),
            "leaf_count": int(res.leaf_count),
            "counterexamples": ces,
            "iv_certified": bool(res.iv_certified),
        }

    smin_B, smax_B = build_slope_tables(B_pwl["slopes"])

    xg = np.linspace(B_M, H_M, 45)
    yg = np.linspace(B_M, H_M, 45)
    Lg = np.concatenate([[0.0], np.linspace(0.05, 0.999, 30)])
    best_lb = -1e9
    worst_pt = (B_M, B_M, 0.5)
    Bx_g = eval_logpwl(B_pwl, xg)
    By_g = eval_logpwl(B_pwl, yg)
    by_term = np.where(By_g < 0.0, b_lo, b_hi) * By_g
    for ix, xv in enumerate(xg):
        Y = q_hi * xv + F_A(A_hi, xv, Lg)
        c = Y[:, None] - yg[None, :]
        ok = c > 1e-15
        lc = np.log(np.maximum(c, 1e-300))
        ll = np.log(1.0 - Lg)[:, None]
        ec = np.where(c < 1.0, e_lo, e_hi)
        val = np.where(ok, ec * lc + (1.0 - e_hi) * ll + by_term[None, :] - Bx_g[ix], -1e9)
        m_v = float(np.max(val))
        if m_v > best_lb:
            best_lb = m_v
            il, iy = np.unravel_index(np.argmax(val), val.shape)
            worst_pt = (float(xv), float(yg[iy]), float(Lg[il]))

    target = best_lb + tol

    ks_m = B_pwl["ks"]
    xs = np.unique(np.concatenate([[B_M], ks_m[(ks_m > B_M) & (ks_m < H_M)], [H_M], np.linspace(B_M, H_M, 19)]))
    ys = np.unique(np.concatenate([[B_M], ks_m[(ks_m > B_M) & (ks_m < H_M)], [H_M], np.linspace(B_M, H_M, 19)]))
    Ls = np.concatenate([[0.0, 0.15, 0.35, 0.55, 0.72, 0.85, 0.94, 0.985, 0.998, 1.0]])

    gxL, gyL, gLL = np.meshgrid(xs[:-1], ys[:-1], Ls[:-1], indexing="ij")
    gxR, gyR, gLR = np.meshgrid(xs[1:], ys[1:], Ls[1:], indexing="ij")
    bxL, bxR = gxL.ravel(), gxR.ravel()
    byL, byR = gyL.ravel(), gyR.ravel()
    bLL, bLR = gLL.ravel(), gLR.ravel()

    d_ub = None
    rem_appended = False
    counterexamples: List[Tuple[float, float, float, float]] = [(*worst_pt, best_lb)]
    leaf_xL: List[np.ndarray] = []
    leaf_xR: List[np.ndarray] = []
    leaf_yL: List[np.ndarray] = []
    leaf_yR: List[np.ndarray] = []
    leaf_LL: List[np.ndarray] = []
    leaf_LR: List[np.ndarray] = []

    for _it in range(max_iter):
        Y_min = q_hi * bxL + F_A(A_hi, bxL, bLL)
        Y_max = q_hi * bxR + F_A(A_hi, bxR, bLR)
        c_max = Y_max - byL
        c_min = Y_min - byR
        infeasible = c_max <= 1e-15

        ec_max = np.where(c_max < 1.0, e_lo, e_hi)
        Bx_min, _ = range_bounds_logpwl(B_pwl, bxL, bxR)
        By_min, By_max = range_bounds_logpwl(B_pwl, byL, byR)
        b_By_max = np.maximum(np.where(By_min < 0.0, b_lo * By_min, b_hi * By_min),
                              np.where(By_max < 0.0, b_lo * By_max, b_hi * By_max))
        ub_mono = np.where(
            infeasible,
            -1e9,
            ec_max * np.log(np.maximum(c_max, 1e-300))
            + (1.0 - e_hi) * np.log(np.maximum(1.0 - bLL, 1e-300))
            + b_By_max
            - Bx_min,
        )

        xm = 0.5 * (bxL + bxR)
        ym = 0.5 * (byL + byR)
        Lm = 0.5 * (bLL + bLR)
        hx = 0.5 * (bxR - bxL)
        hy = 0.5 * (byR - byL)
        hL = 0.5 * (bLR - bLL)
        Ym = q_hi * xm + F_A(A_hi, xm, Lm)
        cm = Ym - ym
        valid_c = (~infeasible) & (bLR < 1.0) & (c_min > 1e-10)
        ub_cent = np.full_like(ub_mono, 1e9)

        if np.any(valid_c):
            xLv, xRv = bxL[valid_c], bxR[valid_c]
            yLv, yRv = byL[valid_c], byR[valid_c]
            LLv, LRv = bLL[valid_c], bLR[valid_c]
            xmv, ymv, Lmv = xm[valid_c], ym[valid_c], Lm[valid_c]
            hxv, hyv, hLv = hx[valid_c], hy[valid_c], hL[valid_c]
            c_min_v, c_max_v = c_min[valid_c], c_max[valid_c]
            cmv = cm[valid_c]

            Yx_lo, Yx_hi = prod_dY_dK_bounds(A_hi, xLv, xRv, LLv, LRv, ak_mode=False)
            Yx_lo = q_hi + Yx_lo
            Yx_hi = q_hi + Yx_hi
            YL_lo, YL_hi = prod_dY_dL_bounds(A_hi, xLv, xRv, LLv, LRv, ak_mode=False)

            dBx_lo, dBx_hi = deriv_bounds_logpwl(B_pwl, smin_B, smax_B, xLv, xRv)
            dBy_lo, dBy_hi = deriv_bounds_logpwl(B_pwl, smin_B, smax_B, yLv, yRv)

            Bx_m = eval_logpwl(B_pwl, xmv)
            By_m = eval_logpwl(B_pwl, ymv)
            By_v_min, By_v_max = By_min[valid_c], By_max[valid_c]
            b_lo_v = np.where(By_v_max < 0.0, b_lo, b_hi)
            b_hi_v = np.where(By_v_min >= 0.0, b_hi, b_lo)
            b_eff_lo = np.minimum(b_lo_v, b_hi_v)
            b_eff_hi = np.maximum(b_lo_v, b_hi_v)

            cross_c1 = (c_min_v < 1.0) & (c_max_v >= 1.0)
            best_eta_ub = np.full(np.sum(valid_c), -1e9)
            for ec in (e_lo, e_hi):
                mask_ec = (c_min_v < 1.0) if ec == e_lo else (c_max_v >= 1.0)
                ec_lo = np.where(cross_c1, e_lo, ec)
                ec_hi = np.where(cross_c1, e_hi, ec)
                b_m_ec = np.where(By_m < 0.0, b_lo, b_hi)
                hm = ec * np.log(cmv) + (1.0 - e_hi) * np.log(1.0 - Lmv) + b_m_ec * By_m - Bx_m
                inv_c_lo = 1.0 / c_max_v
                inv_c_hi = 1.0 / c_min_v
                dx_lo = ec_lo * inv_c_lo * Yx_lo - dBx_hi
                dx_hi = ec_hi * inv_c_hi * Yx_hi - dBx_lo
                bdBy_lo = np.minimum(b_eff_lo * dBy_lo, b_eff_hi * dBy_lo)
                bdBy_hi = np.maximum(b_eff_lo * dBy_hi, b_eff_hi * dBy_hi)
                dy_lo = -ec_hi * inv_c_hi + bdBy_lo
                dy_hi = -ec_lo * inv_c_lo + bdBy_hi
                dL_lo = ec_lo * inv_c_lo * YL_lo - (1.0 - e_hi) / (1.0 - LRv)
                dL_hi = ec_hi * inv_c_hi * YL_hi - (1.0 - e_hi) / (1.0 - LLv)
                ub_ec = (
                    hm
                    + np.maximum(np.abs(dx_lo), np.abs(dx_hi)) * hxv
                    + np.maximum(np.abs(dy_lo), np.abs(dy_hi)) * hyv
                    + np.maximum(np.abs(dL_lo), np.abs(dL_hi)) * hLv
                )
                best_eta_ub = np.where(mask_ec, np.maximum(best_eta_ub, ub_ec), best_eta_ub)
            ub_cent[valid_c] = best_eta_ub

        ub = np.minimum(ub_mono, ub_cent)
        keep = ub > target
        if np.any(~keep):
            leaf_xL.append(bxL[~keep]); leaf_xR.append(bxR[~keep])
            leaf_yL.append(byL[~keep]); leaf_yR.append(byR[~keep])
            leaf_LL.append(bLL[~keep]); leaf_LR.append(bLR[~keep])
        n_keep = int(np.sum(keep))
        if n_keep == 0:
            d_ub = target
            break

        bxL, bxR = bxL[keep], bxR[keep]
        byL, byR = byL[keep], byR[keep]
        bLL, bLR = bLL[keep], bLR[keep]
        xm, ym, Lm = xm[keep], ym[keep], Lm[keep]

        cm_k = q_hi * xm + F_A(A_hi, xm, Lm) - ym
        ok_k = (cm_k > 1e-15) & (Lm < 1.0)
        ecm_k = np.where(cm_k < 1.0, e_lo, e_hi)
        Bym_k = eval_logpwl(B_pwl, ym)
        lb_k = np.where(
            ok_k,
            ecm_k * np.log(np.maximum(cm_k, 1e-300))
            + (1.0 - e_hi) * np.log(np.maximum(1.0 - Lm, 1e-300))
            + np.where(Bym_k < 0.0, b_lo, b_hi) * Bym_k
            - eval_logpwl(B_pwl, xm),
            -1e9,
        )
        i_best = int(np.argmax(lb_k))
        if lb_k[i_best] > best_lb:
            best_lb = float(lb_k[i_best])
            target = best_lb + tol
            counterexamples.append((float(xm[i_best]), float(ym[i_best]), float(Lm[i_best]), best_lb))

        if len(bxL) > 80_000:
            leaf_xL.append(bxL); leaf_xR.append(bxR)
            leaf_yL.append(byL); leaf_yR.append(byR)
            leaf_LL.append(bLL); leaf_LR.append(bLR)
            rem_appended = True
            break
        ex = bxR - bxL
        ey = byR - byL
        eL_s = (bLR - bLL) / np.maximum(1.0 - bLR, 1e-3)
        m1 = (ex >= ey) & (ex >= eL_s)
        m2 = (~m1) & (ey >= eL_s)
        m3 = (~m1) & (~m2)
        axL, axR, ayL, ayR, aLL, aLR = bxL.copy(), bxR.copy(), byL.copy(), byR.copy(), bLL.copy(), bLR.copy()
        cxL, cxR, cyL, cyR, cLL, cLR = bxL.copy(), bxR.copy(), byL.copy(), byR.copy(), bLL.copy(), bLR.copy()
        axR[m1] = xm[m1]; cxL[m1] = xm[m1]
        ayR[m2] = ym[m2]; cyL[m2] = ym[m2]
        aLR[m3] = Lm[m3]; cLL[m3] = Lm[m3]
        bxL = np.concatenate([axL, cxL]); bxR = np.concatenate([axR, cxR])
        byL = np.concatenate([ayL, cyL]); byR = np.concatenate([ayR, cyR])
        bLL = np.concatenate([aLL, cLL]); bLR = np.concatenate([aLR, cLR])

    if d_ub is None:
        d_ub = float(np.max(ub[keep])) if np.any(keep) else float(np.max(ub))
        if not rem_appended and len(bxL) > 0:
            leaf_xL.append(bxL); leaf_xR.append(bxR)
            leaf_yL.append(byL); leaf_yR.append(byR)
            leaf_LL.append(bLL); leaf_LR.append(bLR)
        for j in range(min(8, len(xm))):
            counterexamples.append((float(xm[j]), float(ym[j]), float(Lm[j]), float(ub[j])))

    # 100% outward-rounded IEEE-754 terminal audit over ALL leaf boxes
    all_xL = np.concatenate(leaf_xL); all_xR = np.concatenate(leaf_xR)
    all_yL = np.concatenate(leaf_yL); all_yR = np.concatenate(leaf_yR)
    all_LL = np.concatenate(leaf_LL); all_LR = np.concatenate(leaf_LR)
    d_ub_iv = float(audit_staying_boxes_ivf(
        B_pwl["ks"], B_pwl["lks"], B_pwl["vals"], B_pwl["slopes"],
        float(B_pwl["s_lo"]), float(B_pwl["s_hi"]),
        all_xL, all_xR, all_yL, all_yR, all_LL, all_LR,
        float(A_hi), float(q_hi), float(b_lo), float(b_hi), float(e_lo), float(e_hi),
    ))
    iv_certified = bool(d_ub_iv <= 0.0)

    return {
        "certified": bool(d_ub <= 0.0 and iv_certified),
        "d_ub": float(d_ub),
        "d_ub_iv": float(d_ub_iv),
        "d_lb": float(best_lb),
        "leaf_count": int(len(all_xL)),
        "counterexamples": counterexamples,
        "iv_certified": iv_certified,
    }


# ---------------------------------------------------------------------------
# 2. Global Super-Barrier Verifier on (0, inf) x [bL, bR] (Cases 1, 2, 3, 4)
# ---------------------------------------------------------------------------
def _iv_solve_ak_L_max(
    c_dhi_iv: Interval,
    Av_iv: Interval,
    q_hi_iv: Interval,
    eU_iv: Interval,
) -> Interval:
    """
    100% outward-rounded 1D Interval B&B over L in [0, 1) maximizing:
        g(L) = c_dhi * log(q_hi + F_A(A_hi, h, L) / h) + (1 - eU) * log(1 - L)
    Replaces discrete 2000-point grid in Case 4 upper tail.
    """
    one = Interval("1")
    h_iv = Interval(str(H_M))
    edges = [Decimal("0"), Decimal("0.5"), Decimal("0.75"), Decimal("0.88"), Decimal("0.96"), Decimal("0.9999")]
    boxes = [(Interval._raw(edges[i], edges[i]), Interval._raw(edges[i + 1], edges[i + 1])) for i in range(len(edges) - 1)]

    def _eval_L_pt(L_pt: Interval) -> Interval:
        R_pt = q_hi_iv + iv_F_A(Av_iv, h_iv, L_pt) / h_iv
        return c_dhi_iv * R_pt.ln() + (one - eU_iv) * (one - L_pt).ln()

    best_lb = Decimal("-1e9")
    for a, b in boxes:
        mid = Interval._raw((a.lo + b.lo) / Decimal("2"), (a.lo + b.lo) / Decimal("2"))
        best_lb = max(best_lb, _eval_L_pt(mid).lo)

    for _ in range(25):
        next_boxes = []
        max_ub = Decimal("-1e9")
        for a, b in boxes:
            L_iv = Interval._raw(a.lo, b.hi)
            R_iv = q_hi_iv + iv_F_A(Av_iv, h_iv, L_iv) / h_iv
            ub_mono = (c_dhi_iv * R_iv.ln() + (one - eU_iv) * (one - L_iv).ln()).hi
            mid = Interval._raw((a.lo + b.hi) / Decimal("2"), (a.lo + b.hi) / Decimal("2"))
            hl = (b.hi - a.lo) / Decimal("2")
            dR = iv_prod_dY_dL(Av_iv, h_iv, L_iv, ak_mode=False) / h_iv
            dg = c_dhi_iv * (dR / R_iv) - (one - eU_iv) / (one - L_iv)
            g_m = _eval_L_pt(mid)
            best_lb = max(best_lb, g_m.lo)
            ub_cent = (g_m + Interval._raw(Decimal("0"), dg.max_abs() * hl)).hi
            ub = min(ub_mono, ub_cent)
            max_ub = max(max_ub, ub)
            if ub > best_lb + Decimal("1e-8"):
                next_boxes.append((a, mid))
                next_boxes.append((mid, b))
        if not next_boxes or max_ub - best_lb < Decimal("1e-7"):
            break
        boxes = next_boxes

    # Tail L in [0.9999, 1): g(L) <= c_dhi * log(q_hi + F_A(h, 1)/h) + (1 - eU) * log(1 - 0.9999)
    R_1 = q_hi_iv + iv_F_A(Av_iv, h_iv, one) / h_iv
    tail_hi = (c_dhi_iv * R_1.ln() + (one - eU_iv) * Interval("0.0001").ln()).hi
    final_hi = max(tail_hi, best_lb + Decimal("1e-7"))
    for a, b in boxes:
        L_iv = Interval._raw(a.lo, b.hi)
        R_iv = q_hi_iv + iv_F_A(Av_iv, h_iv, L_iv) / h_iv
        mid = Interval._raw((a.lo + b.hi) / Decimal("2"), (a.lo + b.hi) / Decimal("2"))
        hl = (b.hi - a.lo) / Decimal("2")
        dR = iv_prod_dY_dL(Av_iv, h_iv, L_iv, ak_mode=False) / h_iv
        dg = c_dhi_iv * (dR / R_iv) - (one - eU_iv) / (one - L_iv)
        ub_cent = (_eval_L_pt(mid) + Interval._raw(Decimal("0"), dg.max_abs() * hl)).hi
        ub_mono = (c_dhi_iv * R_iv.ln() + (one - eU_iv) * (one - L_iv).ln()).hi
        final_hi = max(final_hi, min(ub_mono, ub_cent))
    return Interval._raw(best_lb, final_hi)


def verify_super_barrier_bb(
    V_self_pwl: Dict[str, object],
    EV_pwl: Dict[str, object],
    Av: float,
    bL: float,
    bR: float,
    q_hi: float = Q_MAX,
    eL: float = ETA_MIN,
    eU: float = ETA_MAX,
    tol: float = 3e-4,
    ak_mode: bool = False,
    max_iter: int = 55,
    max_boxes: int = 350_000,
) -> Dict[str, object]:
    """
    Continuously certify log-PWL super-barrier V_self(K) with continuation EV(K)
    on ALL (0, infinity) x [bL, bR], with:
      - Explicit check that EV_pwl is non-decreasing everywhere,
      - 50-digit Decimal Interval audit of lower and upper analytical tails,
      - 100% Numba IEEE-754 outward-rounded audit of EVERY 3D leaf box.
    """
    ks_s = V_self_pwl["ks"]
    ks_e = EV_pwl["ks"]
    x_lo = float(ks_s[0])
    x_cut = float(ks_s[-1])
    s_tail = float(V_self_pwl["s_lo"])
    D_hi = float(V_self_pwl["s_hi"])
    s_tail_e = float(EV_pwl["s_lo"])
    D_hi_e = float(EV_pwl["s_hi"])

    # Mandatory check (Fix 6): EV must be non-decreasing everywhere
    assert float(np.min(EV_pwl["slopes"])) >= -1e-12 and s_tail_e >= 0.0 and D_hi_e >= 0.0, (
        f"EV_pwl is not non-decreasing: min_slope={np.min(EV_pwl['slopes'])}, s_lo={s_tail_e}, s_hi={D_hi_e}"
    )
    assert float(np.min(V_self_pwl["slopes"])) >= -1e-12 and s_tail >= 0.0 and D_hi >= 0.0, (
        "V_self_pwl must be non-decreasing"
    )

    smin_self, smax_self = build_slope_tables(V_self_pwl["slopes"])
    smin_EV, smax_EV = build_slope_tables(EV_pwl["slopes"])

    # 50-digit Decimal Interval analytical tails on (0, x_lo] and [x_cut, inf)
    iv_Av = Interval(str(Av))
    iv_q = Interval(str(q_hi))
    iv_eL = Interval(str(eL))
    iv_eU = Interval(str(eU))
    iv_one = Interval("1")
    iv_xlo = Interval(x_lo)
    iv_xcut = Interval(x_cut)
    iv_s_tail = Interval(s_tail)
    iv_D_hi = Interval(D_hi)
    iv_s_tail_e = Interval(s_tail_e)
    iv_D_hi_e = Interval(D_hi_e)
    iv_vs0 = Interval(float(V_self_pwl["vals"][0]))
    iv_ve0 = Interval(float(EV_pwl["vals"][0]))
    iv_vs_end = Interval(float(V_self_pwl["vals"][-1]))
    iv_ve_end = Interval(float(EV_pwl["vals"][-1]))
    iv_h = Interval(str(H_M))

    iv_r_top = iv_q + iv_F_A(iv_Av, iv_xlo, iv_one) / iv_xlo
    assert iv_r_top.hi < Decimal("1"), f"Lower tail contraction failed at x_lo={x_lo}: r_top={iv_r_top.hi}"

    def iv_tails_for_b(bv_float: float) -> Tuple[Interval, Interval]:
        iv_b = Interval(str(bv_float))
        iv_c_slo = iv_eL + iv_b * iv_s_tail_e
        assert (iv_c_slo - iv_s_tail).lo >= Decimal("0"), (
            f"Lower tail log(x) coeff negative at b={bv_float}: {(iv_c_slo - iv_s_tail).lo}"
        )
        iv_s_lo_opt = (iv_b * iv_s_tail_e) / iv_c_slo
        iv_tail_lo = (
            iv_eL * ((iv_one - iv_s_lo_opt) * iv_xlo).ln()
            + iv_b * iv_s_tail_e * iv_s_lo_opt.ln()
            + iv_c_slo * iv_r_top.ln()
            + iv_b * iv_ve0
            - iv_vs0
        )

        if not ak_mode:
            iv_F_inf = iv_Av * Interval("2").pow_half_int(3)
            iv_Y_end = iv_q * iv_xcut + iv_F_inf
            assert iv_Y_end.hi < iv_xcut.lo, f"Upper tail cut x_cut={x_cut} too small"
            iv_V1 = iv_eval_logpwl(EV_pwl, iv_one)
            idx1 = max(0, int(np.searchsorted(ks_e, 1.0)) - 1)
            # Outward-rounded lower bound on linear slope dEV/dy on [ks_e[idx1], x_cut]
            sl_min_dec = Decimal("1e30")
            for ii in range(idx1, len(ks_e) - 1):
                seg_sl = (Interval(float(EV_pwl["vals"][ii + 1])) - Interval(float(EV_pwl["vals"][ii]))) / (
                    Interval(float(ks_e[ii + 1])).ln() - Interval(float(ks_e[ii])).ln()
                ) / Interval(float(ks_e[ii + 1]))
                sl_min_dec = min(sl_min_dec, seg_sl.lo)
            iv_sl_min = Interval._raw(sl_min_dec, sl_min_dec)
            iv_tail_hi_lt1 = iv_eU * iv_Y_end.ln() + iv_b * iv_V1 - iv_vs_end

            # 100% 50-digit Interval enclosure across all x in [x_cut, inf) and y in [1, x_cut]:
            # Regime 1: x in [x_cut, x_cross] -> g1(x) is strictly convex (g1''(x) = D_hi/x^2 > 0),
            #   so sup over [x_cut, x_cross] is attained at endpoints x_cut or x_cross.
            # Regime 2: x in [x_cross, inf) subset (x_zero, inf) -> g2(x) is unimodal with unique
            #   global maximum at x_peak = D_hi * (x_cut - F_inf) / ((D_hi - eU) * q_hi).
            assert sl_min_dec > Decimal("0"), f"Non-positive EV slope on [1, x_cut]: {sl_min_dec}"
            assert iv_D_hi.lo > iv_eU.hi and iv_xcut.lo > iv_F_inf.hi
            iv_c_star = iv_eU / (iv_b * iv_sl_min)
            iv_x_zero = (iv_xcut - iv_F_inf) / iv_q
            iv_x_cross = (iv_xcut + iv_c_star - iv_F_inf) / iv_q
            iv_x_peak = (iv_D_hi * (iv_xcut - iv_F_inf)) / ((iv_D_hi - iv_eU) * iv_q)
            assert iv_x_cross.lo > iv_xcut.hi and iv_x_peak.lo > iv_x_zero.hi

            def _iv_g1(iv_x: Interval) -> Interval:
                iv_Yt = iv_q * iv_x + iv_F_inf
                return (
                    iv_eU * iv_c_star.ln()
                    + iv_b * (iv_ve_end + iv_sl_min * (iv_Yt - iv_c_star - iv_xcut))
                    - (iv_vs_end + iv_D_hi * (iv_x / iv_xcut).ln())
                )

            iv_g2_peak = (
                iv_eU * (iv_q * iv_x_peak + iv_F_inf - iv_xcut).ln()
                + iv_b * iv_ve_end
                - (iv_vs_end + iv_D_hi * (iv_x_peak / iv_xcut).ln())
            )
            tail_mid_hi = max(_iv_g1(iv_xcut).hi, _iv_g1(iv_x_cross).hi, iv_g2_peak.hi)
            iv_c_dhi = iv_eU + iv_b * iv_D_hi_e
            assert (iv_c_dhi - iv_D_hi).hi <= Decimal("0"), (
                f"Upper tail log(x) coeff positive: {(iv_c_dhi - iv_D_hi).hi}"
            )
            iv_s_hi_opt = (iv_b * iv_D_hi_e) / iv_c_dhi
            iv_tail_hi_log = (
                iv_eU * (iv_one - iv_s_hi_opt).ln()
                + iv_b * iv_D_hi_e * iv_s_hi_opt.ln()
                + iv_c_dhi * (iv_Y_end / iv_xcut).ln()
                + iv_eU * iv_xcut.ln()
                + iv_b * iv_ve_end
                - iv_vs_end
            )
            hi_all = max(iv_tail_hi_lt1.hi, tail_mid_hi, iv_tail_hi_log.hi)
            lo_all = max(iv_tail_hi_lt1.lo, iv_tail_hi_log.lo)
            return iv_tail_lo, Interval._raw(lo_all, hi_all)

        # AK upper tail [x_cut, inf)
        iv_R_top = iv_q + iv_F_A(iv_Av, iv_h, iv_one) / iv_h
        iv_c_dhi = iv_eU + iv_b * iv_D_hi_e
        assert (iv_c_dhi - iv_D_hi).hi <= Decimal("0"), (
            f"AK upper tail log(x) coeff positive: {(iv_c_dhi - iv_D_hi).hi}"
        )
        iv_s_hi_opt = (iv_b * iv_D_hi_e) / iv_c_dhi
        # Exact 1D Interval B&B maximization over L in [0, 1) (replaces 2000-pt grid)
        iv_ak_L_term = _iv_solve_ak_L_max(iv_c_dhi, iv_Av, iv_q, iv_eU)
        iv_tail_hi_log = (
            iv_eU * (iv_one - iv_s_hi_opt).ln()
            + iv_b * iv_D_hi_e * iv_s_hi_opt.ln()
            + iv_ak_L_term
            + (iv_eU + iv_b * iv_D_hi_e - iv_D_hi) * iv_xcut.ln()
            + iv_b * (iv_ve_end - iv_D_hi_e * iv_xcut.ln())
            - (iv_vs_end - iv_D_hi * iv_xcut.ln())
        )
        # Drop y < x_cut: since EV non-decreasing, EV(y) <= ve_end; eU - D_hi < 0 => max at x = x_cut
        iv_ve_pos = Interval._raw(max(Decimal("0"), iv_ve_end.lo), max(Decimal("0"), iv_ve_end.hi))
        iv_tail_hi_drop = iv_eU * (iv_R_top * iv_xcut).ln() + iv_b * iv_ve_pos - iv_vs_end
        return iv_tail_lo, Interval._raw(
            max(iv_tail_hi_log.lo, iv_tail_hi_drop.lo),
            max(iv_tail_hi_log.hi, iv_tail_hi_drop.hi),
        )

    iv_t_lo_L, iv_t_hi_L = iv_tails_for_b(bL)
    iv_t_lo_R, iv_t_hi_R = iv_tails_for_b(bR)
    tail_iv_hi = float(Interval._raw(
        max(iv_t_lo_L.lo, iv_t_hi_L.lo, iv_t_lo_R.lo, iv_t_hi_R.lo),
        max(iv_t_lo_L.hi, iv_t_hi_L.hi, iv_t_lo_R.hi, iv_t_hi_R.hi),
    ).to_float_bounds()[1])
    tail_lo_hi = float(Interval._raw(iv_t_lo_L.lo, max(iv_t_lo_L.hi, iv_t_lo_R.hi)).to_float_bounds()[1])
    tail_hi_hi = float(Interval._raw(iv_t_hi_L.lo, max(iv_t_hi_L.hi, iv_t_hi_R.hi)).to_float_bounds()[1])
    tail_max = tail_iv_hi

    if using_rust_verifier():
        ks_s_c = np.ascontiguousarray(V_self_pwl["ks"], dtype=np.float64)
        lks_s_c = np.ascontiguousarray(V_self_pwl["lks"], dtype=np.float64)
        vals_s_c = np.ascontiguousarray(V_self_pwl["vals"], dtype=np.float64)
        sl_s_c = np.ascontiguousarray(V_self_pwl["slopes"], dtype=np.float64)
        ks_e_c = np.ascontiguousarray(EV_pwl["ks"], dtype=np.float64)
        lks_e_c = np.ascontiguousarray(EV_pwl["lks"], dtype=np.float64)
        vals_e_c = np.ascontiguousarray(EV_pwl["vals"], dtype=np.float64)
        sl_e_c = np.ascontiguousarray(EV_pwl["slopes"], dtype=np.float64)
        c_dbl_p = ctypes.POINTER(ctypes.c_double)
        ce_buf = np.empty(64 * 4, dtype=np.float64)
        res = _RUST_LIB.rs_verify_super_barrier_bb(
            ks_s_c.ctypes.data_as(c_dbl_p), lks_s_c.ctypes.data_as(c_dbl_p),
            vals_s_c.ctypes.data_as(c_dbl_p), sl_s_c.ctypes.data_as(c_dbl_p),
            len(ks_s_c), float(s_tail), float(D_hi),
            ks_e_c.ctypes.data_as(c_dbl_p), lks_e_c.ctypes.data_as(c_dbl_p),
            vals_e_c.ctypes.data_as(c_dbl_p), sl_e_c.ctypes.data_as(c_dbl_p),
            len(ks_e_c), float(s_tail_e), float(D_hi_e),
            float(Av), float(q_hi), float(bL), float(bR), float(eL), float(eU),
            float(tail_max), float(tol), 1 if ak_mode else 0, int(max_iter), int(max_boxes),
            ce_buf.ctypes.data_as(c_dbl_p), 64,
        )
        ces = [(float(ce_buf[4 * i]), float(ce_buf[4 * i + 1]), float(ce_buf[4 * i + 2]), float(ce_buf[4 * i + 3])) for i in range(res.n_ce)]
        return {
            "certified": bool(res.certified),
            "d_ub": float(res.d_ub),
            "d_ub_iv": float(res.d_ub_iv),
            "d_lb": float(res.d_lb),
            "tail_max": float(tail_iv_hi),
            "tail_lo": float(tail_lo_hi),
            "tail_hi": float(tail_hi_hi),
            "leaf_count": int(res.leaf_count),
            "counterexamples": ces,
            "iv_certified": bool(res.iv_certified),
        }

    # Grid search lower bound on [x_lo, x_cut]
    xg = np.unique(np.concatenate([np.geomspace(x_lo, x_cut, 64), ks_s]))
    Lg = np.concatenate([[0.0], np.geomspace(1e-5, 0.999, 24)])
    sg = np.linspace(0.05, 0.998, 24)
    Y_g = q_hi * xg[:, None] + prod_Y(Av, xg[:, None], Lg[None, :], ak_mode=ak_mode)
    c_g = Y_g[:, :, None] * (1.0 - sg[None, None, :])
    y_g = Y_g[:, :, None] * sg[None, None, :]
    ec_g = np.where(c_g < 1.0, eL, eU)
    ev_g = eval_logpwl(EV_pwl, y_g)
    b_g = np.where(ev_g < 0.0, bL, bR)
    val_g = ec_g * np.log(c_g) + (1.0 - eU) * np.log(1.0 - Lg[None, :, None]) + b_g * ev_g - eval_logpwl(V_self_pwl, xg[:, None, None])

    ix, iL, is_ = np.unravel_index(np.argmax(val_g), val_g.shape)
    best_lb = float(val_g[ix, iL, is_])
    worst_pt = (float(xg[ix]), float(Lg[iL]), float(sg[is_]))
    if len(ks_s) > 1:
        xm_s = np.sqrt(ks_s[:-1] * ks_s[1:])[:, None, None]
        Lm_s = np.array([0.0, 0.37, 0.50, 0.62, 0.72, 0.85])[None, :, None]
        sm_s = np.array([0.82, 0.90, 0.955, 0.985, 0.9979])[None, None, :]
        Ym_s = q_hi * xm_s + prod_Y(Av, xm_s, Lm_s, ak_mode=ak_mode)
        cm_s = np.maximum(Ym_s * (1.0 - sm_s), 1e-300)
        ecm_s = np.where(cm_s < 1.0, eL, eU)
        ev_ms = eval_logpwl(EV_pwl, Ym_s * sm_s)
        b_ms = np.where(ev_ms < 0.0, bL, bR)
        val_ms = ecm_s * np.log(cm_s) + (1.0 - eU) * np.log(1.0 - Lm_s) + b_ms * ev_ms - eval_logpwl(V_self_pwl, xm_s)
        imx, imL, ims = np.unravel_index(np.argmax(val_ms), val_ms.shape)
        if float(val_ms[imx, imL, ims]) > best_lb:
            best_lb = float(val_ms[imx, imL, ims])
            worst_pt = (float(xm_s[imx, 0, 0]), float(Lm_s[0, imL, 0]), float(sm_s[0, 0, ims]))
    best_lb = max(tail_max, best_lb)
    target = max(best_lb + tol, -1.0e-4) if best_lb < -tol else (best_lb + tol)

    stride = max(1, len(ks_s) // 80)
    skiba_ks = ks_s[(ks_s >= 0.0008) & (ks_s <= 0.006)]
    xs_b = np.unique(np.concatenate([np.geomspace(x_lo, x_cut, 28), ks_s[::stride], skiba_ks, [x_cut]]))
    Ls_b = np.concatenate([[0.0, 0.2, 0.5, 0.7], np.linspace(0.8, 0.99, 6, endpoint=False), [0.99, 0.999, 1.0]])
    ss_b = np.concatenate([[0.0, 0.3, 0.65], np.linspace(0.75, 0.99, 8, endpoint=False), [0.99, 0.996, 0.998, 0.999, 1.0]])
    if ak_mode:
        xs_b = np.unique(np.concatenate([xs_b, [H_M]]))
    gxL, gLL, gsL = np.meshgrid(xs_b[:-1], Ls_b[:-1], ss_b[:-1], indexing="ij")
    gxR, gLR, gsR = np.meshgrid(xs_b[1:], Ls_b[1:], ss_b[1:], indexing="ij")
    bxL, bxR, bLL, bLR, bsL, bsR = gxL.ravel(), gxR.ravel(), gLL.ravel(), gLR.ravel(), gsL.ravel(), gsR.ravel()

    counterexamples: List[Tuple[float, float, float, float]] = [(*worst_pt, best_lb)]
    d_ub = None
    rem_appended = False
    leaf_xL: List[np.ndarray] = []
    leaf_xR: List[np.ndarray] = []
    leaf_LL: List[np.ndarray] = []
    leaf_LR: List[np.ndarray] = []
    leaf_sL: List[np.ndarray] = []
    leaf_sR: List[np.ndarray] = []

    for _it in range(max_iter):
        Y_min = q_hi * bxL + prod_Y(Av, bxL, bLL, ak_mode=ak_mode)
        Y_max = q_hi * bxR + prod_Y(Av, bxR, bLR, ak_mode=ak_mode)
        c_max = np.maximum((1.0 - bsL) * Y_max, 1e-300)
        ec_max = np.where(c_max < 1.0, eL, eU)
        Vs_min = eval_logpwl(V_self_pwl, bxL)
        ev_min = eval_logpwl(EV_pwl, bsL * Y_min)
        ev_max = eval_logpwl(EV_pwl, bsR * Y_max)
        b_ev_max = np.maximum(np.where(ev_min < 0.0, bL * ev_min, bR * ev_min),
                              np.where(ev_max < 0.0, bL * ev_max, bR * ev_max))
        ub_mono = (
            np.where(bsL >= 1.0, -1e9, ec_max * np.log(c_max))
            + (1.0 - eU) * np.log(np.maximum(1.0 - bLL, 1e-300))
            + np.where(bsR <= 0.0, -1e9, b_ev_max)
            - Vs_min
        )

        xm = 0.5 * (bxL + bxR)
        Lm = 0.5 * (bLL + bLR)
        sm = 0.5 * (bsL + bsR)
        hx = 0.5 * (bxR - bxL)
        hL = 0.5 * (bLR - bLL)
        hs = 0.5 * (bsR - bsL)
        Ym = q_hi * xm + prod_Y(Av, xm, Lm, ak_mode=ak_mode)
        cm = (1.0 - sm) * Ym
        c_min = np.maximum((1.0 - bsR) * Y_min, 1e-300)
        valid_c = (ub_mono > target) & (bLR < 1.0) & (bsL > 0.0) & (bsR < 1.0) & (c_min > 1e-30)
        if ak_mode:
            valid_c = valid_c & ((bxR <= H_M) | (bxL >= H_M))

        ub_cent = np.full_like(ub_mono, 1e9)
        ex, eL_err, es = (bxR - bxL) / bxL, hL, hs
        if np.any(valid_c):
            xLv, xRv = bxL[valid_c], bxR[valid_c]
            LLv, LRv = bLL[valid_c], bLR[valid_c]
            sLv, sRv = bsL[valid_c], bsR[valid_c]
            xmv, Lmv, smv = xm[valid_c], Lm[valid_c], sm[valid_c]
            hxv, hLv, hsv = hx[valid_c], hL[valid_c], hs[valid_c]
            Y_min_v, Y_max_v, Ymv = Y_min[valid_c], Y_max[valid_c], Ym[valid_c]
            y_min_v, y_max_v = sLv * Y_min_v, sRv * Y_max_v

            Yx_lo, Yx_hi = prod_dY_dK_bounds(Av, xLv, xRv, LLv, LRv, ak_mode=ak_mode)
            Yx_lo = q_hi + Yx_lo
            Yx_hi = q_hi + Yx_hi
            YL_lo, YL_hi = prod_dY_dL_bounds(Av, xLv, xRv, LLv, LRv, ak_mode=ak_mode)

            dEV_lo, dEV_hi = deriv_bounds_logpwl(EV_pwl, smin_EV, smax_EV, y_min_v, y_max_v)
            dVs_lo, dVs_hi = deriv_bounds_logpwl(V_self_pwl, smin_self, smax_self, xLv, xRv)

            ev_v_min, ev_v_max = ev_min[valid_c], ev_max[valid_c]
            b_lo_v = np.where(ev_v_max < 0.0, bL, bR)
            b_hi_v = np.where(ev_v_min >= 0.0, bR, bL)
            b_eff_lo = np.minimum(b_lo_v, b_hi_v)
            b_eff_hi = np.maximum(b_lo_v, b_hi_v)

            bdEV_lo = np.minimum(b_eff_lo * dEV_lo, b_eff_hi * dEV_lo)
            bdEV_hi = np.maximum(b_eff_lo * dEV_hi, b_eff_hi * dEV_hi)

            cross_c1 = (c_min[valid_c] < 1.0) & (c_max[valid_c] >= 1.0)
            best_eta_ub = np.full(np.sum(valid_c), -1e9)
            err_x_v = np.zeros(np.sum(valid_c))
            err_L_v = np.zeros(np.sum(valid_c))
            err_s_v = np.zeros(np.sum(valid_c))
            ev_m_v = eval_logpwl(EV_pwl, smv * Ymv)
            Vs_m_v = eval_logpwl(V_self_pwl, xmv)
            bm_v = np.where(ev_m_v < 0.0, bL, bR)

            for ec in (eL, eU):
                mask_ec = (c_min[valid_c] < 1.0) if ec == eL else (c_max[valid_c] >= 1.0)
                ec_lo = np.where(cross_c1, eL, ec)
                ec_hi = np.where(cross_c1, eU, ec)
                hm = ec * np.log(cm[valid_c]) + (1.0 - eU) * np.log(1.0 - Lmv) + bm_v * ev_m_v - Vs_m_v
                A_lo_t = ec_lo / Y_max_v + np.minimum(sLv * bdEV_lo, sRv * bdEV_lo)
                A_hi_t = ec_hi / Y_min_v + np.maximum(sLv * bdEV_hi, sRv * bdEV_hi)
                p_Yx = np.array([A_lo_t * Yx_lo, A_lo_t * Yx_hi, A_hi_t * Yx_lo, A_hi_t * Yx_hi])
                hx_lo = np.min(p_Yx, axis=0) - dVs_hi
                hx_hi = np.max(p_Yx, axis=0) - dVs_lo
                p_YL = np.array([A_lo_t * YL_lo, A_lo_t * YL_hi, A_hi_t * YL_lo, A_hi_t * YL_hi])
                hL_lo = np.min(p_YL, axis=0) - (1.0 - eU) / (1.0 - LRv)
                hL_hi = np.max(p_YL, axis=0) - (1.0 - eU) / (1.0 - LLv)
                p_Ys = np.array([Y_min_v * bdEV_lo, Y_min_v * bdEV_hi, Y_max_v * bdEV_lo, Y_max_v * bdEV_hi])
                hs_lo = -ec_hi / (1.0 - sRv) + np.min(p_Ys, axis=0)
                hs_hi = -ec_lo / (1.0 - sLv) + np.max(p_Ys, axis=0)
                sx_e = np.maximum(np.abs(hx_lo), np.abs(hx_hi)) * hxv
                sL_e = np.maximum(np.abs(hL_lo), np.abs(hL_hi)) * hLv
                ss_e = np.maximum(np.abs(hs_lo), np.abs(hs_hi)) * hsv
                ub_ec = hm + sx_e + sL_e + ss_e
                best_eta_ub = np.where(mask_ec, np.maximum(best_eta_ub, ub_ec), best_eta_ub)
                err_x_v = np.where(mask_ec, np.maximum(err_x_v, sx_e), err_x_v)
                err_L_v = np.where(mask_ec, np.maximum(err_L_v, sL_e), err_L_v)
                err_s_v = np.where(mask_ec, np.maximum(err_s_v, ss_e), err_s_v)
            ub_cent[valid_c] = best_eta_ub
            ex[valid_c], eL_err[valid_c], es[valid_c] = err_x_v, err_L_v, err_s_v

        ub = np.minimum(ub_mono, ub_cent)
        keep = ub > target
        if np.any(~keep):
            leaf_xL.append(bxL[~keep]); leaf_xR.append(bxR[~keep])
            leaf_LL.append(bLL[~keep]); leaf_LR.append(bLR[~keep])
            leaf_sL.append(bsL[~keep]); leaf_sR.append(bsR[~keep])
        n_keep = int(np.sum(keep))
        if n_keep == 0:
            d_ub = target
            if best_lb > -1e-4 and len(xm) > 0:
                order_end = np.argsort(ub)[::-1]
                added_lxs = []
                for idx_e in order_end:
                    x_cand = float(xm[idx_e])
                    lx_cand = math.log(max(x_cand, 1e-30))
                    if not added_lxs or min(abs(lx_cand - lx0) for lx0 in added_lxs) > 3e-3:
                        counterexamples.append((x_cand, float(Lm[idx_e]), float(sm[idx_e]), float(ub[idx_e])))
                        added_lxs.append(lx_cand)
                    if len(added_lxs) >= 24:
                        break
            break

        bxL, bxR, bLL, bLR, bsL, bsR = bxL[keep], bxR[keep], bLL[keep], bLR[keep], bsL[keep], bsR[keep]
        xm, Lm, sm = xm[keep], Lm[keep], sm[keep]
        ex, eL_err, es = ex[keep], eL_err[keep], es[keep]
        Ym_k = q_hi * xm + prod_Y(Av, xm, Lm, ak_mode=ak_mode)
        cm_k = (1.0 - sm) * Ym_k
        ecm_k = np.where(cm_k < 1.0, eL, eU)
        ev_k = eval_logpwl(EV_pwl, sm * Ym_k)
        b_k = np.where(ev_k < 0.0, bL, bR)
        lb_k = np.where(
            (Lm < 1.0) & (sm > 0.0) & (sm < 1.0) & (cm_k > 1e-30),
            ecm_k * np.log(np.maximum(cm_k, 1e-300))
            + (1.0 - eU) * np.log(np.maximum(1.0 - Lm, 1e-300))
            + b_k * ev_k
            - eval_logpwl(V_self_pwl, xm),
            -1e9,
        )
        i_best = int(np.argmax(lb_k))
        if lb_k[i_best] > best_lb:
            best_lb = float(lb_k[i_best])
            target = max(best_lb + tol, -1.0e-4) if best_lb < -tol else (best_lb + tol)
            counterexamples.append((float(xm[i_best]), float(Lm[i_best]), float(sm[i_best]), best_lb))
        if len(lb_k) >= 4 and best_lb > 0.0 and len(counterexamples) < 40:
            top4 = np.argpartition(lb_k, -4)[-4:]
            for j4 in top4:
                if lb_k[j4] > 0.0:
                    counterexamples.append((float(xm[j4]), float(Lm[j4]), float(sm[j4]), float(lb_k[j4])))

        max_boxes_eff = max(max_boxes, 2_000_000) if ak_mode else max_boxes
        if n_keep > max_boxes_eff:
            if len(counterexamples) < 8:
                ub_k = ub[keep]
                order = np.argsort(ub_k)[::-1][:16]
                for idx_w in order:
                    counterexamples.append((float(xm[idx_w]), float(Lm[idx_w]), float(sm[idx_w]), float(ub_k[idx_w])))
            leaf_xL.append(bxL); leaf_xR.append(bxR)
            leaf_LL.append(bLL); leaf_LR.append(bLR)
            leaf_sL.append(bsL); leaf_sR.append(bsR)
            rem_appended = True
            break
        if n_keep <= 800:
            bxL = np.concatenate([bxL, xm, bxL, xm, bxL, xm, bxL, xm])
            bxR = np.concatenate([xm, bxR, xm, bxR, xm, bxR, xm, bxR])
            bLL = np.concatenate([bLL, bLL, Lm, Lm, bLL, bLL, Lm, Lm])
            bLR = np.concatenate([Lm, Lm, bLR, bLR, Lm, Lm, bLR, bLR])
            bsL = np.concatenate([bsL, bsL, bsL, bsL, sm, sm, sm, sm])
            bsR = np.concatenate([sm, sm, sm, sm, bsR, bsR, bsR, bsR])
        else:
            m1 = (ex >= eL_err) & (ex >= es)
            m2 = (~m1) & (eL_err >= es)
            m3 = (~m1) & (~m2)
            axL, axR, aLL, aLR, asL, asR = bxL.copy(), bxR.copy(), bLL.copy(), bLR.copy(), bsL.copy(), bsR.copy()
            cxL, cxR, cLL, cLR, csL, csR = bxL.copy(), bxR.copy(), bLL.copy(), bLR.copy(), bsL.copy(), bsR.copy()
            axR[m1] = xm[m1]; cxL[m1] = xm[m1]
            aLR[m2] = Lm[m2]; cLL[m2] = Lm[m2]
            asR[m3] = sm[m3]; csL[m3] = sm[m3]
            bxL = np.concatenate([axL, cxL]); bxR = np.concatenate([axR, cxR])
            bLL = np.concatenate([aLL, cLL]); bLR = np.concatenate([aLR, cLR])
            bsL = np.concatenate([asL, csL]); bsR = np.concatenate([asR, csR])

    if d_ub is None:
        d_ub = max(tail_iv_hi, float(np.max(ub[keep])) if np.any(keep) else float(np.max(ub)))
        if not rem_appended and len(bxL) > 0:
            leaf_xL.append(bxL); leaf_xR.append(bxR)
            leaf_LL.append(bLL); leaf_LR.append(bLR)
            leaf_sL.append(bsL); leaf_sR.append(bsR)
        ub_k = ub[keep] if np.any(keep) else ub
        order = np.argsort(ub_k)[::-1][:24]
        for j in order:
            if j < len(xm):
                counterexamples.append((float(xm[j]), float(Lm[j]), float(sm[j]), float(ub_k[j])))
    else:
        d_ub = max(float(d_ub), tail_iv_hi)

    # 100% outward-rounded IEEE-754 terminal audit over ALL 3D leaf boxes
    all_xL = np.concatenate(leaf_xL); all_xR = np.concatenate(leaf_xR)
    all_LL = np.concatenate(leaf_LL); all_LR = np.concatenate(leaf_LR)
    all_sL = np.concatenate(leaf_sL); all_sR = np.concatenate(leaf_sR)
    boxes_iv_hi = float(audit_super_boxes_ivf(
        V_self_pwl["ks"], V_self_pwl["lks"], V_self_pwl["vals"], V_self_pwl["slopes"], s_tail, D_hi,
        EV_pwl["ks"], EV_pwl["lks"], EV_pwl["vals"], EV_pwl["slopes"], s_tail_e, D_hi_e,
        all_xL, all_xR, all_LL, all_LR, all_sL, all_sR,
        float(Av), float(q_hi), float(bL), float(bR), float(eL), float(eU),
        bool(ak_mode), float(H_M),
    ))
    d_ub_iv = max(tail_iv_hi, boxes_iv_hi)
    iv_certified = bool(d_ub_iv <= 0.0)

    return {
        "certified": bool(d_ub <= 0.0 and iv_certified),
        "d_ub": float(d_ub),
        "d_ub_iv": float(d_ub_iv),
        "d_lb": float(best_lb),
        "tail_max": float(tail_iv_hi),
        "tail_lo": float(tail_lo_hi),
        "tail_hi": float(tail_hi_hi),
        "leaf_count": int(len(all_xL)),
        "counterexamples": counterexamples,
        "iv_certified": iv_certified,
    }


# ---------------------------------------------------------------------------
# 3. Continuous Witness Sub-Solution Verifier (100% 50-digit Interval Audit)
# ---------------------------------------------------------------------------
def verify_witness_subsolution_bb(
    W_pwl: Dict[str, object],
    EW_pwl: Dict[str, object],
    kp_pwl: Dict[str, object],
    L_pwl: Dict[str, object],
    A_lo: float,
    q_lo: float,
    bL: float,
    bR: float,
    eL: float = ETA_MIN,
    eU: float = ETA_MAX,
    k_domain: Tuple[float, float] = (B_M, 3.0),
    ak_mode: bool = False,
    tol: float = 2e-4,
    max_iter: int = 35,
    interval_check: bool = True,
) -> Dict[str, object]:
    """
    Certifies via 1D adaptive B&B + 100% 50-digit Decimal Interval audit
    (zero float(iv.lo), zero 1+1e-9) that on K in [k_a, k_b]:
      1) L(K) in [0, 1 - 1e-6], kp(K) >= k_a (and <= k_b if not ak_mode)
      2) c_min(K) = q_lo*K + Y(A_lo, K, L(K)) - kp(K) > 0
      3) W(K) - [ u_min(c_min(K), L(K)) + beta_eff * EW(kp(K)) ] <= 0
    """
    k_a, k_b = k_domain
    all_ks = np.unique(np.concatenate([
        [k_a, k_b],
        W_pwl["ks"],
        kp_pwl["ks"],
        L_pwl["ks"],
        np.geomspace(k_a, k_b, 96),
    ]))
    all_ks = all_ks[(all_ks >= k_a) & (all_ks <= k_b)]
    if ak_mode and k_a < H_M < k_b:
        all_ks = np.unique(np.concatenate([all_ks, [H_M]]))

    L_grid = np.clip(eval_logpwl(L_pwl, all_ks), 0.0, 0.999)
    kp_grid = eval_logpwl(kp_pwl, all_ks)
    c_grid = q_lo * all_ks + prod_Y(A_lo, all_ks, L_grid, ak_mode=ak_mode) - kp_grid
    if np.any(c_grid <= 1e-12) or np.any(kp_grid < k_a - 1e-12) or (not ak_mode and np.any(kp_grid > k_b + 1e-12)):
        bad_idx = int(np.argmin(np.minimum(c_grid, kp_grid - k_a if ak_mode else np.minimum(kp_grid - k_a, k_b - kp_grid))))
        return {
            "certified": False,
            "d_ub": 1e9,
            "d_ub_iv": 1e9,
            "d_lb": 1e9,
            "counterexamples": [(float(all_ks[bad_idx]), 1e9)],
            "iv_certified": False,
        }

    lc_g = np.log(c_grid)
    ll_g = np.log(1.0 - L_grid)
    u_g = np.minimum(eL * lc_g + (1.0 - eL) * ll_g, eU * lc_g + (1.0 - eU) * ll_g)
    ew_g = eval_logpwl(EW_pwl, kp_grid)
    b_g = np.where(ew_g < 0.0, bR, bL)
    res_g = eval_logpwl(W_pwl, all_ks) - (u_g + b_g * ew_g)
    i_w = int(np.argmax(res_g))
    best_lb = float(res_g[i_w])
    counterexamples: List[Tuple[float, float]] = [(float(all_ks[i_w]), best_lb)]
    target = best_lb + tol

    bxL, bxR = all_ks[:-1].copy(), all_ks[1:].copy()
    d_ub = None
    rem_appended = False
    done_L: List[np.ndarray] = []
    done_R: List[np.ndarray] = []

    smin_W, smax_W = build_slope_tables(W_pwl["slopes"])
    smin_EW, smax_EW = build_slope_tables(EW_pwl["slopes"])
    smin_kp, smax_kp = build_slope_tables(kp_pwl["slopes"])
    smin_L, smax_L = build_slope_tables(L_pwl["slopes"])

    def _iv_prod(aL: np.ndarray, aH: np.ndarray, bL_v: np.ndarray, bH_v: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        p1, p2, p3, p4 = aL * bL_v, aL * bH_v, aH * bL_v, aH * bH_v
        return np.minimum(np.minimum(p1, p2), np.minimum(p3, p4)), np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))

    for _it in range(max_iter):
        LL_lo, LL_hi = range_bounds_logpwl(L_pwl, bxL, bxR)
        LL_lo_c = np.clip(LL_lo, 0.0, 0.9999)
        LL_hi_c = np.clip(LL_hi, 0.0, 0.9999)
        kp_lo, kp_hi = range_bounds_logpwl(kp_pwl, bxL, bxR)

        if np.any(LL_hi >= 0.9999) or np.any(kp_lo < k_a) or (not ak_mode and np.any(kp_hi > k_b)):
            return {
                "certified": False,
                "d_ub": 1e6,
                "d_ub_iv": 1e6,
                "d_lb": best_lb,
                "counterexamples": counterexamples,
                "iv_certified": False,
            }

        Y_min = q_lo * bxL + prod_Y(A_lo, bxL, LL_lo_c, ak_mode=ak_mode)
        Y_max = q_lo * bxR + prod_Y(A_lo, bxR, LL_hi_c, ak_mode=ak_mode)
        c_min_box = Y_min - kp_hi
        c_max_box = Y_max - kp_lo
        infeasible = c_min_box <= 1e-12
        lc_min = np.log(np.maximum(c_min_box, 1e-300))
        ll_min = np.log(np.maximum(1.0 - LL_hi_c, 1e-300))
        u_min_box = np.minimum(eL * lc_min + (1.0 - eL) * ll_min, eU * lc_min + (1.0 - eU) * ll_min)

        ew_lo, ew_hi = range_bounds_logpwl(EW_pwl, kp_lo, kp_hi)
        bew_lb = np.minimum(
            np.where(ew_lo < 0.0, bR * ew_lo, bL * ew_lo),
            np.where(ew_hi < 0.0, bR * ew_hi, bL * ew_hi),
        )
        _, W_max_box = range_bounds_logpwl(W_pwl, bxL, bxR)
        ub_mono = np.where(infeasible, 1e6, W_max_box - (u_min_box + bew_lb))

        xm = 0.5 * (bxL + bxR)
        Lm = np.clip(eval_logpwl(L_pwl, xm), 0.0, 0.9999)
        kpm = eval_logpwl(kp_pwl, xm)
        cm = q_lo * xm + prod_Y(A_lo, xm, Lm, ak_mode=ak_mode) - kpm
        ewm = eval_logpwl(EW_pwl, kpm)
        bm = np.where(ewm < 0.0, bR, bL)
        um = np.minimum(eL * np.log(np.maximum(cm, 1e-300)) + (1.0 - eL) * np.log(1.0 - Lm),
                        eU * np.log(np.maximum(cm, 1e-300)) + (1.0 - eU) * np.log(1.0 - Lm))
        res_m = np.where(cm > 1e-12, eval_logpwl(W_pwl, xm) - (um + bm * ewm), 1e6)

        dW_lo, dW_hi = deriv_bounds_logpwl(W_pwl, smin_W, smax_W, bxL, bxR)
        dL_lo, dL_hi = deriv_bounds_logpwl(L_pwl, smin_L, smax_L, bxL, bxR)
        dkp_lo, dkp_hi = deriv_bounds_logpwl(kp_pwl, smin_kp, smax_kp, bxL, bxR)
        dEW_lo, dEW_hi = deriv_bounds_logpwl(EW_pwl, smin_EW, smax_EW, kp_lo, kp_hi)
        YK_lo, YK_hi = prod_dY_dK_bounds(A_lo, bxL, bxR, LL_lo_c, LL_hi_c, ak_mode=ak_mode)
        YK_lo = q_lo + YK_lo; YK_hi = q_lo + YK_hi
        YL_lo, YL_hi = prod_dY_dL_bounds(A_lo, bxL, bxR, LL_lo_c, LL_hi_c, ak_mode=ak_mode)
        YLdL_lo, YLdL_hi = _iv_prod(YL_lo, YL_hi, dL_lo, dL_hi)
        dc_lo = YK_lo + YLdL_lo - dkp_hi
        dc_hi = YK_hi + YLdL_hi - dkp_lo
        ec_lo = np.where(c_min_box >= 1.0, eU, eL)
        ec_hi = np.where(c_max_box < 1.0, eL, eU)
        duc_lo, duc_hi = _iv_prod(ec_lo / np.maximum(c_max_box, 1e-300), ec_hi / np.maximum(c_min_box, 1e-300), dc_lo, dc_hi)
        dul_lo, dul_hi = _iv_prod((1.0 - ec_hi) / np.maximum(1.0 - LL_lo_c, 1e-300), (1.0 - ec_lo) / np.maximum(1.0 - LL_hi_c, 1e-300), dL_lo, dL_hi)
        du_lo = duc_lo - dul_hi
        du_hi = duc_hi - dul_lo
        dEWz_lo, dEWz_hi = _iv_prod(dEW_lo, dEW_hi, dkp_lo, dkp_hi)
        bv_lo = np.where(ew_lo >= 0.0, bL, np.where(ew_hi < 0.0, bR, bL))
        bv_hi = np.where(ew_lo >= 0.0, bL, np.where(ew_hi < 0.0, bR, bR))
        dbEW_lo, dbEW_hi = _iv_prod(bv_lo, bv_hi, dEWz_lo, dEWz_hi)
        df_lo = dW_lo - du_hi - dbEW_hi
        df_hi = dW_hi - du_lo - dbEW_lo
        ub_cent = np.where(infeasible, 1e6, res_m + np.maximum(np.abs(df_lo), np.abs(df_hi)) * 0.5 * (bxR - bxL))
        ub = np.minimum(ub_mono, ub_cent)

        ib = int(np.argmax(res_m))
        if res_m[ib] > best_lb:
            best_lb = float(res_m[ib])
            target = best_lb + tol
            counterexamples.append((float(xm[ib]), best_lb))

        keep = ub > target
        if np.any(~keep):
            done_L.append(bxL[~keep])
            done_R.append(bxR[~keep])
        if not np.any(keep):
            d_ub = target
            break

        bxL, bxR = bxL[keep], bxR[keep]
        xm = xm[keep]
        if len(bxL) > 80_000:
            done_L.append(bxL); done_R.append(bxR)
            rem_appended = True
            break
        bxL = np.concatenate([bxL, xm])
        bxR = np.concatenate([xm, bxR])

    if d_ub is None:
        d_ub = float(np.max(ub))
        if not rem_appended and len(bxL) > 0:
            done_L.append(bxL); done_R.append(bxR)
        xm = 0.5 * (bxL + bxR)
        for j in range(min(6, len(xm))):
            counterexamples.append((float(xm[j]), float(ub[j])))

    iv_certified = False
    d_ub_iv = float(d_ub)
    if interval_check and d_ub <= 0.0 and len(done_L) > 0:
        iv_A = Interval(str(A_lo))
        iv_q = Interval(str(q_lo))
        iv_bL = Interval(str(bL))
        iv_bR = Interval(str(bR))
        iv_eL = Interval(str(eL))
        iv_eU = Interval(str(eU))
        iv_one = Interval("1")
        iv_ka = Interval(str(k_a))
        iv_kb = Interval(str(k_b))
        term_L = np.concatenate(done_L)
        term_R = np.concatenate(done_R)
        iv_max_res = Decimal("-1e9")
        ok_all = True

        def _audit_seg(kL_d: Decimal, kR_d: Decimal, depth: int = 0) -> Decimal:
            nonlocal ok_all
            k_iv = Interval._raw(kL_d, kR_d)
            L_iv = iv_eval_logpwl(L_pwl, k_iv)
            kp_iv = iv_eval_logpwl(kp_pwl, k_iv)
            if L_iv.lo < 0 or L_iv.hi >= 1 or kp_iv.lo < iv_ka.lo or (not ak_mode and kp_iv.hi > iv_kb.hi):
                ok_all = False
                return Decimal("1e9")
            c_iv = iv_q * k_iv + iv_prod_Y(iv_A, k_iv, L_iv, ak_mode=ak_mode) - kp_iv
            if c_iv.lo <= 0:
                if depth < 8:
                    mid_d = (kL_d + kR_d) / Decimal("2")
                    return max(_audit_seg(kL_d, mid_d, depth + 1), _audit_seg(mid_d, kR_d, depth + 1))
                ok_all = False
                return Decimal("1e9")
            lc_iv = c_iv.ln()
            ll_iv = (iv_one - L_iv).ln()
            u1 = iv_eL * lc_iv + (iv_one - iv_eL) * ll_iv
            u2 = iv_eU * lc_iv + (iv_one - iv_eU) * ll_iv
            u_iv = Interval._raw(min(u1.lo, u2.lo), min(u1.hi, u2.hi))
            ew_iv = iv_eval_logpwl(EW_pwl, kp_iv)
            bew_lo = min(
                (iv_bR * ew_iv).lo if ew_iv.lo < 0 else (iv_bL * ew_iv).lo,
                (iv_bR * ew_iv).lo if ew_iv.hi < 0 else (iv_bL * ew_iv).lo,
            )
            W_iv = iv_eval_logpwl(W_pwl, k_iv)
            res_hi = W_iv.hi - (u_iv.lo + bew_lo)
            if res_hi <= Decimal("0"):
                return res_hi

            # Pure 50-digit Interval centered-form evaluation around midpoint
            xm_d = (kL_d + kR_d) / Decimal("2")
            xm_iv = Interval._raw(xm_d, xm_d)
            hx_iv = Interval._raw((kR_d - kL_d) / Decimal("2"), (kR_d - kL_d) / Decimal("2"))
            Lm_iv = iv_eval_logpwl(L_pwl, xm_iv)
            kpm_iv = iv_eval_logpwl(kp_pwl, xm_iv)
            cm_iv = iv_q * xm_iv + iv_prod_Y(iv_A, xm_iv, Lm_iv, ak_mode=ak_mode) - kpm_iv
            if cm_iv.lo <= 0:
                ok_all = False
                return Decimal("1e9")
            lcm_iv = cm_iv.ln()
            llm_iv = (iv_one - Lm_iv).ln()
            um1 = iv_eL * lcm_iv + (iv_one - iv_eL) * llm_iv
            um2 = iv_eU * lcm_iv + (iv_one - iv_eU) * llm_iv
            um_lo = min(um1.lo, um2.lo)
            ewm_iv = iv_eval_logpwl(EW_pwl, kpm_iv)
            bewm_lo = min(
                (iv_bR * ewm_iv).lo if ewm_iv.lo < 0 else (iv_bL * ewm_iv).lo,
                (iv_bR * ewm_iv).lo if ewm_iv.hi < 0 else (iv_bL * ewm_iv).lo,
            )
            res_m_hi = iv_eval_logpwl(W_pwl, xm_iv).hi - (um_lo + bewm_lo)

            dW_iv = iv_deriv_bounds_logpwl(W_pwl, k_iv)
            dL_iv = iv_deriv_bounds_logpwl(L_pwl, k_iv)
            dkp_iv = iv_deriv_bounds_logpwl(kp_pwl, k_iv)
            dEW_iv = iv_deriv_bounds_logpwl(EW_pwl, kp_iv)
            YK_iv = iv_q + iv_prod_dY_dK(iv_A, k_iv, L_iv, ak_mode=ak_mode)
            YL_iv = iv_prod_dY_dL(iv_A, k_iv, L_iv, ak_mode=ak_mode)
            dc_iv = YK_iv + YL_iv * dL_iv - dkp_iv

            ec_iv = iv_eU if c_iv.lo >= Decimal("1") else (iv_eL if c_iv.hi < Decimal("1") else iv_eL.hull(iv_eU))
            du_iv = (ec_iv / c_iv) * dc_iv - ((iv_one - ec_iv) / (iv_one - L_iv)) * dL_iv
            if ew_iv.lo >= Decimal("0"):
                bv_iv = iv_bL
            elif ew_iv.hi < Decimal("0"):
                bv_iv = iv_bR
            else:
                bv_iv = iv_bL.hull(iv_bR)
            df_iv = dW_iv - du_iv - bv_iv * dEW_iv * dkp_iv
            cent_hi = res_m_hi + (Interval._raw(df_iv.max_abs(), df_iv.max_abs()) * hx_iv).hi
            ub_seg = min(res_hi, cent_hi)
            if ub_seg > Decimal("0") and depth < 8:
                return max(_audit_seg(kL_d, xm_d, depth + 1), _audit_seg(xm_d, kR_d, depth + 1))
            return ub_seg

        for i in range(len(term_L)):
            kL_d = Interval(float(term_L[i])).lo
            kR_d = Interval(float(term_R[i])).hi
            r_seg = _audit_seg(kL_d, kR_d, 0)
            iv_max_res = max(iv_max_res, r_seg)
            if not ok_all:
                break
        iv_certified = bool(ok_all and iv_max_res <= Decimal("0"))
        d_ub_iv = float(Interval._raw(iv_max_res, iv_max_res).to_float_bounds()[1])

    return {
        "certified": bool(d_ub <= 0.0 and (not interval_check or iv_certified)),
        "d_ub": float(d_ub),
        "d_ub_iv": float(d_ub_iv),
        "d_lb": float(best_lb),
        "counterexamples": counterexamples,
        "iv_certified": iv_certified,
    }


# ---------------------------------------------------------------------------
# 4. Continuous Adverse-Exit Verifier (Exact dE_plus/dK + 50-digit Interval)
# ---------------------------------------------------------------------------
def verify_adverse_exit_bb(
    W_pwl: Dict[str, object],
    E_Psi_cont_val: float,
    A_hi: float,
    q_hi: float,
    bL: float,
    bR: float,
    eL: float,
    eU: float,
    a_exit: float,
    l0_exit: float,
    k_range: Tuple[float, float],
    ak_mode: bool = False,
    tol: float = 2e-4,
    max_iter: int = 35,
    interval_check: bool = True,
) -> Dict[str, object]:
    """
    Continuously certifies via 1D centered-form B&B + 100% 50-digit Decimal Interval
    audit on K in [k_a, k_b] (both standard CES and Footnote 2 AK):
        W(K) - ( E_plus_exact(A_hi, q_hi, K, a_exit, l0_exit) + beta * E_Psi_cont_val ) >= m_lb > 0
    Fixes the dE_lo soundness bug by using the exact Proposition 1** identity
    when interior leisure omega^* < 1 is certified on the interval (and including
    the negative -(eta/c_opt)*t'(K)*omega^* envelope term otherwise).
    """
    k_a, k_b = k_range
    if using_rust_verifier():
        ks_w = np.ascontiguousarray(W_pwl["ks"], dtype=np.float64)
        lks_w = np.ascontiguousarray(W_pwl["lks"], dtype=np.float64)
        vals_w = np.ascontiguousarray(W_pwl["vals"], dtype=np.float64)
        sl_w = np.ascontiguousarray(W_pwl["slopes"], dtype=np.float64)
        c_dbl_p = ctypes.POINTER(ctypes.c_double)
        ce_buf = np.empty(64 * 2, dtype=np.float64)
        res = _RUST_LIB.rs_verify_adverse_exit_bb(
            ks_w.ctypes.data_as(c_dbl_p), lks_w.ctypes.data_as(c_dbl_p),
            vals_w.ctypes.data_as(c_dbl_p), sl_w.ctypes.data_as(c_dbl_p),
            len(ks_w), float(W_pwl["s_lo"]), float(W_pwl["s_hi"]),
            float(E_Psi_cont_val), float(A_hi), float(q_hi), float(bL), float(bR), float(eL), float(eU),
            float(a_exit), float(l0_exit), float(k_a), float(k_b), 1 if ak_mode else 0,
            float(tol), int(max_iter), 1 if interval_check else 0,
            ce_buf.ctypes.data_as(c_dbl_p), 64,
        )
        ces = [(float(ce_buf[2 * i]), float(ce_buf[2 * i + 1])) for i in range(res.n_ce)]
        return {
            "certified": bool(res.certified),
            "m_lb": float(res.d_ub),
            "m_lb_iv": float(res.d_ub_iv),
            "m_ub": float(res.d_lb),
            "counterexamples": ces,
            "iv_certified": bool(res.iv_certified),
        }

    beta_ep = bL if E_Psi_cont_val < 0.0 else bR
    cont_term = beta_ep * E_Psi_cont_val

    smin_W, smax_W = build_slope_tables(W_pwl["slopes"])

    def eval_exit_gap(k_arr: np.ndarray) -> np.ndarray:
        wk = eval_logpwl(W_pwl, k_arr)
        if not ak_mode:
            t = dF_dL(A_hi, k_arr, l0_exit)
            c_sup = q_hi * k_arr + F_A(A_hi, k_arr, l0_exit) + (1.0 - l0_exit) * t - a_exit
        else:
            t_ces = dF_dL(A_hi, k_arr, l0_exit)
            S_ces = q_hi * k_arr + F_A(A_hi, k_arr, l0_exit) + (1.0 - l0_exit) * t_ces
            t_h = dF_dL(A_hi, H_M, l0_exit)
            F_h = F_A(A_hi, H_M, l0_exit)
            t_ak = (k_arr / H_M) * t_h
            S_ak = q_hi * k_arr + (k_arr / H_M) * F_h + (1.0 - l0_exit) * t_ak
            t = np.where(k_arr <= H_M, t_ces, t_ak)
            c_sup = np.where(k_arr <= H_M, S_ces, S_ak) - a_exit
        vals = []
        for eta_v in (eL, eU):
            om_L = np.minimum(1.0, (1.0 - eta_v) * c_sup / t)
            c_opt = c_sup - t * om_L
            vals.append(eta_v * np.log(c_opt) + (1.0 - eta_v) * np.log(om_L))
        ep = np.maximum(vals[0], vals[1])
        return wk - (ep + cont_term)

    ks_scan = np.unique(np.concatenate([np.linspace(k_a, k_b, 81), W_pwl["ks"]]))
    ks_scan = ks_scan[(ks_scan >= k_a) & (ks_scan <= k_b)]
    if ak_mode and k_a < H_M < k_b:
        ks_scan = np.unique(np.concatenate([ks_scan, [H_M]]))
    gaps_scan = eval_exit_gap(ks_scan)
    i_min = int(np.argmin(gaps_scan))
    best_ub = float(gaps_scan[i_min])
    target = best_ub - tol
    counterexamples = [(float(ks_scan[i_min]), best_ub)]

    bxL, bxR = ks_scan[:-1].copy(), ks_scan[1:].copy()
    m_lb = None
    rem_appended = False
    done_L: List[np.ndarray] = []
    done_R: List[np.ndarray] = []

    for _it in range(max_iter):
        xm = 0.5 * (bxL + bxR)
        hx = 0.5 * (bxR - bxL)
        gap_m = eval_exit_gap(xm)

        dW_lo, dW_hi = deriv_bounds_logpwl(W_pwl, smin_W, smax_W, bxL, bxR)
        if not ak_mode or np.all(bxR <= H_M):
            t_L = dF_dL(A_hi, bxL, l0_exit)
            c_sup_L = q_hi * bxL + F_A(A_hi, bxL, l0_exit) + (1.0 - l0_exit) * t_L - a_exit
            t_R = dF_dL(A_hi, bxR, l0_exit)
            c_sup_R = q_hi * bxR + F_A(A_hi, bxR, l0_exit) + (1.0 - l0_exit) * t_R - a_exit
            dFK_hi = 1.5 * A_hi * (2.0 ** 1.5) * (bxR ** 0.5) * (l0_exit ** 2.5) * ((bxL + l0_exit) ** -2.5)
            dFK_lo = 1.5 * A_hi * (2.0 ** 1.5) * (bxL ** 0.5) * (l0_exit ** 2.5) * ((bxR + l0_exit) ** -2.5)
            tp_hi = 1.5 * A_hi * (2.0 ** 1.5) * 2.5 * (bxR ** 1.5) * (l0_exit ** 1.5) * ((bxL + l0_exit) ** -3.5)
            tp_lo = 1.5 * A_hi * (2.0 ** 1.5) * 2.5 * (bxL ** 1.5) * (l0_exit ** 1.5) * ((bxR + l0_exit) ** -3.5)
            dS_hi = q_hi + dFK_hi + (1.0 - l0_exit) * tp_hi
            dS_lo = q_hi + dFK_lo + (1.0 - l0_exit) * tp_lo
            t_log_hi = (2.5 * l0_exit) / (bxL * (bxL + l0_exit))
            t_log_lo = (2.5 * l0_exit) / (bxR * (bxR + l0_exit))
        else:
            # AK mode on [H_M, inf) (split guarantees bxL >= H_M)
            t_h = dF_dL(A_hi, H_M, l0_exit)
            F_h = F_A(A_hi, H_M, l0_exit)
            R_tan = q_hi + F_h / H_M + (1.0 - l0_exit) * (t_h / H_M)
            t_L = (bxL / H_M) * t_h
            t_R = (bxR / H_M) * t_h
            c_sup_L = bxL * R_tan - a_exit
            c_sup_R = bxR * R_tan - a_exit
            dS_hi = np.full_like(bxL, R_tan)
            dS_lo = np.full_like(bxL, R_tan)
            tp_hi = np.full_like(bxL, t_h / H_M)
            tp_lo = np.full_like(bxL, t_h / H_M)
            t_log_hi = 1.0 / bxL
            t_log_lo = 1.0 / bxR

        ep_R = np.maximum(
            eL * np.log(c_sup_R - t_R * np.minimum(1.0, (1.0 - eL) * c_sup_R / t_R))
            + (1.0 - eL) * np.log(np.minimum(1.0, (1.0 - eL) * c_sup_R / t_R)),
            eU * np.log(c_sup_R - t_R * np.minimum(1.0, (1.0 - eU) * c_sup_R / t_R))
            + (1.0 - eU) * np.log(np.minimum(1.0, (1.0 - eU) * c_sup_R / t_R)),
        )
        W_lo, _ = range_bounds_logpwl(W_pwl, bxL, bxR)
        lb_mono = W_lo - (ep_R + cont_term)

        # Exact Prop. 1** derivative enclosure when interior (om_max < 1), else full envelope
        om_max = (1.0 - eL) * c_sup_R / np.maximum(t_L, 1e-15)
        is_int = om_max < 1.0
        dE_hi_int = dS_hi / np.maximum(c_sup_L, 1e-12) - (1.0 - eU) * t_log_lo
        dE_lo_int = dS_lo / np.maximum(c_sup_R, 1e-12) - (1.0 - eL) * t_log_hi

        c_opt_L = np.minimum(
            c_sup_L - t_R * np.minimum(1.0, (1.0 - eL) * c_sup_R / t_L),
            c_sup_L - t_R * np.minimum(1.0, (1.0 - eU) * c_sup_R / t_L),
        )
        c_opt_R = np.maximum(
            c_sup_R - t_L * np.minimum(1.0, (1.0 - eL) * c_sup_L / t_R),
            c_sup_R - t_L * np.minimum(1.0, (1.0 - eU) * c_sup_L / t_R),
        )
        om_min_box = np.minimum(1.0, (1.0 - eU) * c_sup_L / np.maximum(t_R, 1e-15))
        om_max_box = np.minimum(1.0, om_max)
        # dE/dK = eta * (S'(K) - t'(K)*om) / c_opt
        dE_hi_gen = eU * np.maximum(0.0, dS_hi - tp_lo * om_min_box) / np.maximum(c_opt_L, 1e-12)
        dE_lo_gen = eL * (dS_lo - tp_hi * om_max_box) / np.where(dS_lo - tp_hi * om_max_box >= 0.0, np.maximum(c_opt_R, 1e-12), np.maximum(c_opt_L, 1e-12))

        dE_hi = np.where(is_int, dE_hi_int, dE_hi_gen)
        dE_lo = np.where(is_int, dE_lo_int, dE_lo_gen)

        dg_lo = dW_lo - dE_hi
        dg_hi = dW_hi - dE_lo
        lb_cent = gap_m - np.maximum(np.abs(dg_lo), np.abs(dg_hi)) * hx
        lb = np.maximum(lb_mono, lb_cent)

        keep = lb < target
        if np.any(~keep):
            done_L.append(bxL[~keep]); done_R.append(bxR[~keep])
        if not np.any(keep):
            m_lb = target
            break

        bxL, bxR, xm = bxL[keep], bxR[keep], xm[keep]
        gm_k = eval_exit_gap(xm)
        iw = int(np.argmin(gm_k))
        if gm_k[iw] < best_ub:
            best_ub = float(gm_k[iw])
            target = best_ub - tol
            counterexamples.append((float(xm[iw]), best_ub))

        if len(bxL) > 80_000:
            done_L.append(bxL); done_R.append(bxR)
            rem_appended = True
            break
        bxL = np.concatenate([bxL, xm])
        bxR = np.concatenate([xm, bxR])

    if m_lb is None:
        m_lb = float(np.min(lb))
        if not rem_appended and len(bxL) > 0:
            done_L.append(bxL); done_R.append(bxR)

    # 100% 50-digit Decimal Interval leaf audit
    iv_certified = False
    m_lb_iv = float(m_lb)
    if interval_check and m_lb > 0.0 and len(done_L) > 0:
        iv_A = Interval(str(A_hi))
        iv_q = Interval(str(q_hi))
        iv_a = Interval(str(a_exit))
        iv_l0 = Interval(str(l0_exit))
        iv_eL = Interval(str(eL))
        iv_eU = Interval(str(eU))
        iv_cont = Interval(str(beta_ep)) * Interval(str(E_Psi_cont_val))
        term_L = np.concatenate(done_L)
        term_R = np.concatenate(done_R)
        iv_min_gap = Decimal("1e9")

        def _audit_exit_seg(kL_d: Decimal, kR_d: Decimal, depth: int = 0) -> Decimal:
            k_iv = Interval._raw(kL_d, kR_d)
            W_iv = iv_eval_logpwl(W_pwl, k_iv)
            E_iv = iv_E_plus_exact(iv_A, iv_q, k_iv, iv_a, iv_l0, iv_eL, iv_eU, ak_mode=ak_mode)
            gap_mono_lo = (W_iv - (E_iv + iv_cont)).lo
            if gap_mono_lo > Decimal("0"):
                return gap_mono_lo
            xm_d = (kL_d + kR_d) / Decimal("2")
            xm_iv = Interval._raw(xm_d, xm_d)
            hx_iv = Interval._raw((kR_d - kL_d) / Decimal("2"), (kR_d - kL_d) / Decimal("2"))
            gap_m_iv = iv_eval_logpwl(W_pwl, xm_iv) - (
                iv_E_plus_exact(iv_A, iv_q, xm_iv, iv_a, iv_l0, iv_eL, iv_eU, ak_mode=ak_mode) + iv_cont
            )
            dW_iv = iv_deriv_bounds_logpwl(W_pwl, k_iv)
            dE_iv = iv_dE_plus_dK(iv_A, iv_q, k_iv, iv_a, iv_l0, iv_eL, iv_eU, ak_mode=ak_mode)
            dg_iv = dW_iv - dE_iv
            gap_cent_lo = (gap_m_iv - Interval._raw(dg_iv.max_abs(), dg_iv.max_abs()) * hx_iv).lo
            lb_seg = max(gap_mono_lo, gap_cent_lo)
            if lb_seg <= Decimal("0") and depth < 8:
                return min(_audit_exit_seg(kL_d, xm_d, depth + 1), _audit_exit_seg(xm_d, kR_d, depth + 1))
            return lb_seg

        for i in range(len(term_L)):
            kL_d = Interval(float(term_L[i])).lo
            kR_d = Interval(float(term_R[i])).hi
            iv_min_gap = min(iv_min_gap, _audit_exit_seg(kL_d, kR_d, 0))
        iv_certified = bool(iv_min_gap > Decimal("0"))
        m_lb_iv = float(Interval._raw(iv_min_gap, iv_min_gap).to_float_bounds()[0])

    return {
        "certified": bool(m_lb > 0.0 and (not interval_check or iv_certified)),
        "m_lb": float(m_lb),
        "m_lb_iv": float(m_lb_iv),
        "m_ub": float(best_ub),
        "counterexamples": counterexamples,
        "iv_certified": iv_certified,
    }


# ---------------------------------------------------------------------------
# 5. Additional 50-digit Interval Verification Helpers (Fixes 2, 4, 5, 6)
# ---------------------------------------------------------------------------
def verify_witness_slope_on_M(W_pwl: Dict[str, object], m_req: float) -> Tuple[bool, float]:
    """
    Fix 5: Certify in 50-digit Interval arithmetic that W'(x) >= m_req on every
    segment overlapping M = [0.10, 0.28), validating inf_M [W(x) - B(x)] = W(0.10) - B(0.10).
    """
    ks = W_pwl["ks"]
    vals = W_pwl["vals"]
    iv_m = Interval(str(m_req))
    min_d_lo = Decimal("1e30")
    for i in range(len(ks) - 1):
        if ks[i + 1] <= B_M or ks[i] >= H_M:
            continue
        kR_eff = min(float(ks[i + 1]), H_M)
        sl_log = (Interval(float(vals[i + 1])) - Interval(float(vals[i]))) / (
            Interval(float(ks[i + 1])).ln() - Interval(float(ks[i])).ln()
        )
        if sl_log.lo <= Decimal("0"):
            return False, float(sl_log.lo)
        dW_seg = sl_log / Interval(kR_eff)
        min_d_lo = min(min_d_lo, dW_seg.lo)
        if dW_seg.lo < iv_m.hi:
            return False, float(Interval._raw(dW_seg.lo, dW_seg.lo).to_float_bounds()[0])
    return True, float(Interval._raw(min_d_lo, min_d_lo).to_float_bounds()[0])


def verify_derivative_below_bound(
    EV_pwl: Dict[str, object],
    K_bound: float,
    beta_lo: float,
    A_lo: float,
    q_lo: float,
    a_exit: float,
    l0_exit: float,
    eL: float = ETA_MIN,
    eU: float = ETA_MAX,
) -> Tuple[bool, float, float]:
    """
    Certify in 50-digit Interval arithmetic that:
        beta_lo * min_{(0, K_bound]} dE[Psi]/dy > eta_hi / c_opt(K_bound)
    """
    iv_A = Interval(str(A_lo))
    iv_q = Interval(str(q_lo))
    iv_K = Interval(str(K_bound))
    iv_a = Interval(str(a_exit))
    iv_l0 = Interval(str(l0_exit))
    iv_eL = Interval(str(eL))
    iv_eU = Interval(str(eU))
    iv_one = Interval("1")

    two_3_2 = Interval("2").pow_half_int(3)
    t_iv = Interval("1.5") * iv_A * two_3_2 * iv_K.pow_half_int(5) * iv_l0.pow_half_int(1) * (iv_K + iv_l0).pow_half_int(-5)
    c_sup_iv = iv_q * iv_K + iv_F_A(iv_A, iv_K, iv_l0) + (iv_one - iv_l0) * t_iv - iv_a
    c_opt_lo = Decimal("1e30")
    for eta_iv in (iv_eL, iv_eU):
        om_raw = (iv_one - eta_iv) * c_sup_iv / t_iv
        om_L = Interval._raw(min(om_raw.lo, Decimal(1)), min(om_raw.hi, Decimal(1)))
        c_opt_lo = min(c_opt_lo, (c_sup_iv - t_iv * om_L).lo)
    req_rhs = iv_eU / Interval._raw(c_opt_lo, c_opt_lo)

    ks = EV_pwl["ks"]
    vals = EV_pwl["vals"]
    s_lo = float(EV_pwl["s_lo"])
    min_d_lo = (Interval(s_lo) / Interval(float(ks[0]))).lo
    for i in range(len(ks) - 1):
        if ks[i] >= K_bound:
            break
        k_right = min(float(ks[i + 1]), K_bound)
        sl_log = (Interval(float(vals[i + 1])) - Interval(float(vals[i]))) / (
            Interval(float(ks[i + 1])).ln() - Interval(float(ks[i])).ln()
        )
        if sl_log.lo <= Decimal("0"):
            return False, -1e9, float(req_rhs.hi)
        min_d_lo = min(min_d_lo, (sl_log / Interval(k_right)).lo)

    lhs_iv = Interval(str(beta_lo)) * Interval._raw(min_d_lo, min_d_lo)
    margin_iv = lhs_iv - req_rhs
    return bool(margin_iv.lo > Decimal("0")), float(margin_iv.to_float_bounds()[0]), float(lhs_iv.to_float_bounds()[0])


def verify_H2_global_interval(
    W_pwl: Dict[str, object],
    kp80: float,
    L80: float,
    EW_at_kp80_lo: float,
    E_Psi_h_hi: float,
    A_lo: float,
    A_hi: float,
    q_lo: float,
    q_hi: float,
    bL: float,
    bR: float,
    eL: float = ETA_MIN,
    eU: float = ETA_MAX,
    ak_mode: bool = False,
) -> Tuple[bool, float]:
    """
    Certify adverse exit on H2 = [0.80, inf) (CES) or [3.5, inf) (AK) 100% in
    50-digit Decimal Interval arithmetic.
    """
    iv_Al = Interval(str(A_lo)); iv_Ah = Interval(str(A_hi))
    iv_ql = Interval(str(q_lo)); iv_qh = Interval(str(q_hi))
    iv_bL = Interval(str(bL)); iv_bR = Interval(str(bR))
    iv_eL = Interval(str(eL)); iv_eU = Interval(str(eU))
    iv_one = Interval("1")
    iv_h = Interval(str(H_M))
    iv_ep_cont = (iv_bL if E_Psi_h_hi < 0 else iv_bR) * Interval(str(E_Psi_h_hi))

    if not ak_mode:
        from scipy.optimize import brentq as _brentq
        kp_plus = float(_brentq(lambda K: F_A(A_hi, K, 1.0) - (1.0 - q_hi) * K, 1.0, 100.0))
        iv_kp80 = Interval(kp80)
        iv_L80 = Interval(L80)
        iv_ew = Interval(EW_at_kp80_lo)
        iv_tail_W = (iv_bR if iv_ew.lo < 0 else iv_bL) * iv_ew

        Ks_H2 = np.geomspace(0.80, kp_plus, 31)
        min_gap_lo = Decimal("1e30")
        for j in range(30):
            kL_iv = Interval(float(Ks_H2[j]))
            kR_iv = Interval(float(Ks_H2[j + 1]))
            cW_iv = iv_ql * kL_iv + iv_F_A(iv_Al, kL_iv, iv_L80) - iv_kp80
            uW_iv = iv_box_worst_u(cW_iv, iv_L80, iv_eL, iv_eU)
            cE_iv = iv_qh * kR_iv + iv_F_A(iv_Ah, kR_iv, iv_one) - iv_h
            ec_iv = iv_eL if cE_iv.hi < 1 else (iv_eU if cE_iv.lo >= 1 else iv_eL.hull(iv_eU))
            gap_iv = (uW_iv + iv_tail_W) - (ec_iv * cE_iv.ln() + iv_ep_cont)
            min_gap_lo = min(min_gap_lo, gap_iv.lo)

        iv_kpp = Interval(kp_plus)
        iv_cW_inf = iv_ql * iv_kpp + iv_F_A(iv_Al, iv_kpp, iv_L80) - iv_kp80
        iv_cE_inf = iv_qh * iv_kpp + iv_Ah * Interval("2").pow_half_int(3) - iv_h
        ratio_c = iv_cW_inf / iv_cE_inf
        ratio_q = iv_ql / iv_qh
        min_rat = Interval._raw(min(ratio_c.lo, ratio_q.lo), min(ratio_c.hi, ratio_q.hi))
        gap_inf_iv = iv_eU * min_rat.ln() + (iv_one - iv_eU) * (iv_one - iv_L80).ln() + iv_tail_W - iv_ep_cont
        min_gap_lo = min(min_gap_lo, gap_inf_iv.lo)
        return bool(min_gap_lo > Decimal("0")), float(Interval._raw(min_gap_lo, min_gap_lo).to_float_bounds()[0])

    # AK mode on [3.5, inf): homogeneous ray check
    k_tail = Interval("3.5")
    l0_iv = Interval("0.57")
    W_35 = iv_eval_logpwl(W_pwl, k_tail)
    E_35 = iv_E_plus_exact(iv_Ah, iv_qh, k_tail, iv_h, l0_iv, iv_eL, iv_eU, ak_mode=True)
    gap_35 = W_35 - (E_35 + iv_ep_cont)
    # Check slope in log(K): dW/d(log K) = s_hi_W vs max dE_AK/d(log K) on [3.5, inf)
    s_hi_W = Interval(float(W_pwl["s_hi"]))
    t_h = Interval("1.5") * iv_Ah * Interval("2").pow_half_int(3) * iv_h.pow_half_int(5) * l0_iv.pow_half_int(1) * (iv_h + l0_iv).pow_half_int(-5)
    R_tan = iv_qh + iv_F_A(iv_Ah, iv_h, l0_iv) / iv_h + (iv_one - l0_iv) * (t_h / iv_h)
    om_ak_inf = (iv_one - iv_eL) * R_tan / (t_h / iv_h)
    assert om_ak_inf.hi < Decimal("1"), f"AK interior leisure violated: om_ak_inf.hi={om_ak_inf.hi}"
    # On [3.5, inf), since omega^* < 1 is certified above, dE_AK/d(log K) = K*R_tan / (K*R_tan - h) - (1 - eta)
    # <= 3.5*R_tan / (3.5*R_tan - h) - (1 - eU)
    dE_log_max = (k_tail * R_tan) / (k_tail * R_tan - iv_h) - (iv_one - iv_eU)
    slope_ok = s_hi_W.lo >= dE_log_max.hi
    ok_ak = bool(slope_ok and gap_35.lo > Decimal("0"))
    return ok_ak, float(gap_35.to_float_bounds()[0])


def verify_ak_witness_tail_interval(
    W_pwl: Dict[str, object],
    kp_pwl: Dict[str, object],
    L_pwl: Dict[str, object],
    A_lo: float,
    q_lo: float,
    bL: float,
    bR: float,
    eL: float = ETA_MIN,
    eU: float = ETA_MAX,
    k_tail: float = 3.5,
) -> Tuple[bool, float]:
    """
    Certify in 50-digit Interval arithmetic the homogeneous ray prolongation of
    the AK witness W_AK on [k_tail, inf): scaling (K, kp, L) -> (lam*K, lam*kp, L)
    for all lam >= 1 preserves feasibility and satisfies the Bellman sub-solution
    inequality globally provided kp(k_tail) >= k_tail, W(kp) > 0, (1 - bL)*s_hi <= eL,
    and W(k_tail) <= u_worst(c_tail, L_tail) + bL * W(kp(k_tail)).
    """
    kp_tail = float(eval_logpwl(kp_pwl, np.array([k_tail]))[0])
    L_tail = float(np.clip(eval_logpwl(L_pwl, np.array([k_tail]))[0], 0.0, 0.999))

    iv_Al = Interval(str(A_lo))
    iv_ql = Interval(str(q_lo))
    iv_bL = Interval(str(bL))
    iv_eL = Interval(str(eL))
    iv_eU = Interval(str(eU))
    iv_one = Interval("1")
    iv_h = Interval(str(H_M))
    iv_kt = Interval(str(k_tail))
    iv_kpt = Interval(kp_tail)
    iv_Lt = Interval(L_tail)

    iv_c = iv_ql * iv_kt + (iv_kt / iv_h) * iv_F_A(iv_Al, iv_h, iv_Lt) - iv_kpt
    if iv_c.lo <= Decimal("0") or iv_kpt.lo < iv_kt.hi:
        return False, 1e9
    iv_u = iv_box_worst_u(iv_c, iv_Lt, iv_eL, iv_eU)
    iv_w_t = iv_eval_logpwl(W_pwl, iv_kt)
    iv_w_kpt = iv_eval_logpwl(W_pwl, iv_kpt)
    iv_s_hi = Interval(float(W_pwl["s_hi"]))
    # Note: log(lam) >= 0 for lam >= 1 => (1 - bL)*s_hi <= eL ensures d/d(log lam) <= 0 everywhere
    slope_ok = ((iv_one - iv_bL) * iv_s_hi - iv_eL).hi <= Decimal("0")
    iv_res = iv_w_t - (iv_u + iv_bL * iv_w_kpt)
    ok = bool(iv_w_kpt.lo > Decimal("0") and slope_ok and iv_res.hi <= Decimal("0"))
    return ok, float(iv_res.to_float_bounds()[1])


def iv_compute_R_hat_B_upper(
    ab_hi: float,
    q_hi: float = Q_MAX,
    e_lo: float = ETA_MIN,
    e_hi: float = ETA_MAX,
) -> float:
    """
    Rigorous 1D 50-digit Interval B&B upper bound on
      sup_{L in [0, 1)} u_up(q_+ * h + F_{AB,+}(h, L) - b, L)
    replacing the discrete 1500-pt grid for R_hat_B.
    """
    iv_ab = Interval(str(ab_hi))
    iv_qh = Interval(str(q_hi))
    iv_h = Interval(str(H_M))
    iv_b = Interval(str(B_M))
    iv_eL = Interval(str(e_lo))
    iv_eU = Interval(str(e_hi))
    iv_one = Interval("1")
    iv_ome = iv_one - iv_eU

    def _ub_L(L0_d: Decimal, L1_d: Decimal) -> Tuple[Decimal, Decimal]:
        L0_iv = Interval._raw(L0_d, L0_d)
        L1_iv = Interval._raw(L1_d, L1_d)
        Lm_d = (L0_d + L1_d) / Decimal("2")
        Lm_iv = Interval._raw(Lm_d, Lm_d)
        c_lo = (iv_qh * iv_h + iv_F_A(iv_ab, iv_h, L0_iv) - iv_b).lo
        c_hi = (iv_qh * iv_h + iv_F_A(iv_ab, iv_h, L1_iv) - iv_b).hi
        if c_hi <= Decimal("0"):
            return Decimal("-1e30"), Decimal("-1e30")
        c_hi_iv = Interval._raw(c_hi, c_hi)
        ec_iv = iv_eL if c_hi < Decimal("1") else (iv_eU if c_lo >= Decimal("1") else iv_eL.hull(iv_eU))
        ub = (ec_iv * c_hi_iv.ln() + iv_ome * (iv_one - L0_iv).ln()).hi
        cm = iv_qh * iv_h + iv_F_A(iv_ab, iv_h, Lm_iv) - iv_b
        if cm.lo > Decimal("0"):
            ec_m = iv_eL if cm.hi < Decimal("1") else (iv_eU if cm.lo >= Decimal("1") else iv_eL)
            lb = (ec_m * cm.ln() + iv_ome * (iv_one - Lm_iv).ln()).lo
        else:
            lb = Decimal("-1e30")
        return lb, ub

    grid = [Decimal(i) / Decimal("64") for i in range(64)] + [Decimal("0.999999")]
    segs = [(grid[i], grid[i + 1]) for i in range(len(grid) - 1)]
    best_lb = Decimal("-1e30")
    for _ in range(48):
        next_segs = []
        max_ub = Decimal("-1e30")
        ubs = []
        for l0, l1 in segs:
            lb, ub = _ub_L(l0, l1)
            if lb > best_lb:
                best_lb = lb
            ubs.append(ub)
            if ub > max_ub:
                max_ub = ub
        for (l0, l1), ub in zip(segs, ubs):
            if ub > best_lb + Decimal("1e-10"):
                lm = (l0 + l1) / Decimal("2")
                next_segs.append((l0, lm))
                next_segs.append((lm, l1))
        if not next_segs:
            return math.nextafter(float(Interval._raw(max_ub, max_ub).to_float_bounds()[1]), math.inf)
        segs = next_segs
        if len(segs) > 4096:
            break
    final_ub = max(_ub_L(l0, l1)[1] for l0, l1 in segs)
    return math.nextafter(float(Interval._raw(final_ub, final_ub).to_float_bounds()[1]), math.inf)


def iv_solve_markov_B_star(
    p: float,
    bL_s: float,
    bR_s: float,
    R_hat_G: float,
    R_hat_B: float,
    C_max_G: float,
    C_max_B: float,
    m_G: float,
    m_B: float,
) -> Tuple[Interval, Interval]:
    """
    Exact 50-digit Interval 2x2 Cramer solver for Markov affine barrier anchors
    (B_star_G, B_star_B) uniformly over b in [bL_s, bR_s].
    """
    iv_one = Interval("1")
    iv_p = Interval(str(p))
    iv_omp = iv_one - iv_p
    iv_prec = Interval("1") / Interval("3")
    iv_omrec = Interval("2") / Interval("3")
    iv_b = Interval._raw(Interval(str(bL_s)).lo, Interval(str(bR_s)).hi)
    iv_b_min = Interval(str(BETA_MIN))
    iv_e_min = Interval(str(ETA_MIN))
    iv_width = Interval(str(H_M)) - Interval(str(B_M))

    iv_mG = Interval(str(m_G))
    iv_mB = Interval(str(m_B))
    iv_mbar_G = iv_omp * iv_mG + iv_p * iv_mB
    iv_mbar_B = iv_prec * iv_mG + iv_omrec * iv_mB

    d_G1 = iv_e_min / Interval(str(C_max_G))
    d_G2 = iv_b_min * iv_mbar_G
    iv_Delta_G = iv_width * Interval._raw(min(d_G1.lo, d_G2.lo), min(d_G1.hi, d_G2.hi))

    d_B1 = iv_e_min / Interval(str(C_max_B))
    d_B2 = iv_b_min * iv_mbar_B
    iv_Delta_B = iv_width * Interval._raw(min(d_B1.lo, d_B2.lo), min(d_B1.hi, d_B2.hi))

    rhs_G = Interval(str(R_hat_G)) - iv_Delta_G
    rhs_B = Interval(str(R_hat_B)) - iv_Delta_B

    a11 = iv_one - iv_b * iv_omp
    a12 = -(iv_b * iv_p)
    a21 = -(iv_b * iv_prec)
    a22 = iv_one - iv_b * iv_omrec
    det = a11 * a22 - a12 * a21
    assert det.lo > Decimal("0"), f"Singular Markov Cramer system: det={det}"
    iv_BG = (rhs_G * a22 - a12 * rhs_B) / det
    iv_BB = (a11 * rhs_B - rhs_G * a21) / det
    return iv_BG, iv_BB


def certify_affine_deadline_interval(
    iv_marg_stay: Interval,
    iv_max_exit: Interval,
    b_max: float,
) -> int:
    """Minimal integer T >= 1 with (b_max^T * iv_max_exit).hi < iv_marg_stay.lo in 50-digit Interval."""
    iv_bH = Interval(str(b_max))
    assert iv_marg_stay.lo > Decimal("0") and iv_max_exit.hi > Decimal("0")
    T = 1
    while T < 500:
        if (iv_bH.pow_int(T) * iv_max_exit).hi < iv_marg_stay.lo:
            return T
        T += 1
    raise AssertionError(f"Deadline failed to converge in 500 steps: marg={iv_marg_stay}, exit={iv_max_exit}")


def certify_staying_deadline_interval(
    B_pwl: Dict[str, object],
    Psi_pwl: Dict[str, object],
    W_pwl: Dict[str, object],
    b_max: float = BETA_MAX,
) -> Tuple[int, float, float]:
    """
    Bound inf_M [W - B] and sup_M [Psi - B] continuously in 50-digit Interval arithmetic
    over M = [0.10, 0.28], returning (T_star, inf_W_B_lo, sup_Psi_B_hi).
    """
    ks = [Decimal("0.10"), Decimal("0.28")]
    for p in (B_pwl, Psi_pwl, W_pwl):
        for k in p["ks"]:
            kd = Decimal.from_float(float(k))
            if Decimal("0.10") < kd < Decimal("0.28"):
                ks.append(kd)
    for i in range(1, 40):
        ks.append(Decimal("0.10") + Decimal(i) * Decimal("0.0045"))
    ks = sorted(set(ks))

    inf_W_B_lo = Decimal("1e30")
    sup_Psi_B_hi = Decimal("-1e30")
    for kL_d, kR_d in zip(ks[:-1], ks[1:]):
        k_iv = Interval._raw(kL_d, kR_d)
        B_iv = iv_eval_logpwl(B_pwl, k_iv)
        W_iv = iv_eval_logpwl(W_pwl, k_iv)
        Psi_iv = iv_eval_logpwl(Psi_pwl, k_iv)
        inf_W_B_lo = min(inf_W_B_lo, (W_iv - B_iv).lo)
        sup_Psi_B_hi = max(sup_Psi_B_hi, (Psi_iv - B_iv).hi)

    iv_inf = Interval._raw(inf_W_B_lo, inf_W_B_lo)
    iv_sup = Interval._raw(sup_Psi_B_hi, sup_Psi_B_hi)
    T = certify_affine_deadline_interval(iv_inf, iv_sup, b_max)
    return T, float(iv_inf.to_float_bounds()[0]), float(iv_sup.to_float_bounds()[1])


def certify_case1_deadline_interval(
    B_pwl: Dict[str, object],
    Psi_pwl: Optional[Dict[str, object]],
    W_pwl: Optional[Dict[str, object]],
    use_baseline_mr: bool = True,
) -> Tuple[int, float, float]:
    """
    Fix 2 (Case 1): Bound inf_M [W - B] and sup_M [Psi - B] in continuous 50-digit
    Interval arithmetic over M = [0.10, 0.28), replacing the discrete 2001-pt m_fine grid.
    """
    ks = [Decimal("0.10"), Decimal("0.28")]
    for p in (B_pwl, Psi_pwl, W_pwl):
        if p is not None:
            for k in p["ks"]:
                kd = Decimal.from_float(float(k))
                if Decimal("0.10") < kd < Decimal("0.28"):
                    ks.append(kd)
    # Refine with 40 uniform points on M so intervals are super tight
    for i in range(1, 40):
        ks.append(Decimal("0.10") + Decimal(i) * Decimal("0.0045"))
    ks = sorted(set(ks))

    iv_A_MIN = Interval(str(A_MIN))
    iv_Q_MIN = Interval(str(Q_MIN))
    iv_B_MAX = Interval(str(BETA_MAX))
    iv_lM = Interval("0.68")
    iv_sM = Interval("0.135")
    iv_TM = Interval("-33.103")
    iv_04 = Interval("0.4")
    iv_5 = Interval("5")
    iv_185 = Interval("18.5")
    iv_shift = Interval("10") / Interval("301")

    inf_W_B_lo = Decimal("1e30")
    sup_Psi_B_hi = Decimal("-1e30")
    for kL_d, kR_d in zip(ks[:-1], ks[1:]):
        k_iv = Interval._raw(kL_d, kR_d)
        B_iv = iv_eval_logpwl(B_pwl, k_iv)
        if use_baseline_mr:
            c_iv = iv_Q_MIN * k_iv + iv_F_A(iv_A_MIN, k_iv, iv_lM) - iv_sM
            W_iv = iv_box_worst_u(c_iv, iv_lM) + iv_B_MAX * iv_TM
            Psi_iv = iv_04 * k_iv - iv_5 * k_iv.pow_half_int(-1) - iv_185 - iv_shift
        else:
            W_iv = iv_eval_logpwl(W_pwl, k_iv)
            Psi_iv = iv_eval_logpwl(Psi_pwl, k_iv)
        inf_W_B_lo = min(inf_W_B_lo, (W_iv - B_iv).lo)
        sup_Psi_B_hi = max(sup_Psi_B_hi, (Psi_iv - B_iv).hi)

    iv_inf = Interval._raw(inf_W_B_lo, inf_W_B_lo)
    iv_sup = Interval._raw(sup_Psi_B_hi, sup_Psi_B_hi)
    # Find minimal integer T such that beta_max^T * sup_Psi_B_hi < inf_W_B_lo
    T = 1
    while T < 200:
        if (iv_B_MAX.pow_int(T) * iv_sup).hi < iv_inf.lo:
            break
        T += 1
    return T, float(iv_inf.to_float_bounds()[0]), float(iv_sup.to_float_bounds()[1])


def compute_doob_eps0_interval(
    WG0: float,
    WB0: float,
    BG0: float,
    BB0: float,
    B_star_G_min: float,
    B_star_B_min: float,
    PsiG_pwl: Dict[str, object],
    PsiB_pwl: Dict[str, object],
    T0: int,
) -> float:
    """
    Fix 4: Exact p. 31 Doob uniform escape lower bound in 50-digit Interval arithmetic:
      eps_0 = min_{w in {G,B}} [W_w(0.10) - B_w(0.10) - beta_+^T0 * max_{w'} (Psi_{w'}(0.28) - B_{*,w'})]
              / [max_{w'} (Psi_{w'}(y_max) - B_{*,w'}) - beta_+^T0 * max_{w'} (Psi_{w'}(0.28) - B_{*,w'})]
    where y_max = q_+ * h + F_{A_+}(h, 1).
    """
    iv_Ah = Interval(str(A_MAX))
    iv_qh = Interval(str(Q_MAX))
    iv_h = Interval(str(H_M))
    iv_bH = Interval(str(BETA_MAX))
    iv_one = Interval("1")
    iv_ymax = iv_qh * iv_h + iv_F_A(iv_Ah, iv_h, iv_one)

    psiGh = iv_eval_logpwl(PsiG_pwl, iv_h)
    psiBh = iv_eval_logpwl(PsiB_pwl, iv_h)
    psiGy = iv_eval_logpwl(PsiG_pwl, iv_ymax)
    psiBy = iv_eval_logpwl(PsiB_pwl, iv_ymax)

    iv_BsG = Interval(str(B_star_G_min))
    iv_BsB = Interval(str(B_star_B_min))
    d28 = Interval._raw(max((psiGh - iv_BsG).lo, (psiBh - iv_BsB).lo),
                        max((psiGh - iv_BsG).hi, (psiBh - iv_BsB).hi))
    dym = Interval._raw(max((psiGy - iv_BsG).lo, (psiBy - iv_BsB).lo),
                        max((psiGy - iv_BsG).hi, (psiBy - iv_BsB).hi))
    bT0 = iv_bH.pow_int(T0)
    tail = bT0 * d28

    num_G = (Interval(WG0) - Interval(BG0)) - tail
    num_B = (Interval(WB0) - Interval(BB0)) - tail
    num = Interval._raw(min(num_G.lo, num_B.lo), min(num_G.hi, num_B.hi))
    den = dym - tail
    eps0 = num / den
    return float(eps0.to_float_bounds()[0])
