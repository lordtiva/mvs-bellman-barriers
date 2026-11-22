"""
Reproducible analytical interval & VFI verification script for Article A:
  "Barreras de Bellman Afiladas, Equivalencia Asintotica y Supervivencia
   Estocastica Certificada bajo Rendimientos Crecientes" (Marcelo Segura, 2026)

Verifies:
  1. Section 3: Lemma 1, Theorem 9*, Proposition 1* (with c < 1 - L = 0.25 check),
     sharpened M0 witness (tau_.1 <= 9 with CEGIS super-barrier), restricted-M slack
     decomposition (46 -> 23 -> 9 -> 4), and Proposition 1** & Table 2 (outward-rounded
     50-digit Decimal interval arithmetic & Wronskian monotonicity).
  2. Section 4: Theorem 3*, Corollary 2* & Table 3 (exact FOC scaling + log-k interpolated
     continuous-state VFI up to A = 10^8 verifying 0 < dW_pi_plus <= dW_plus -> 0+,
     L_ss = 7/9, and O(A^-1) harmonic decay of dW_minus).
  3. Section 5: Stochastic VFI (Table 5 + p_rec sensitivity) & independent interval
     re-audit of cegis_certificates.json.

Usage:
  python verify_article_a.py
"""

from __future__ import annotations

import argparse
from decimal import Decimal
import json
import math
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
from scipy.interpolate import PchipInterpolator
from scipy.optimize import brentq

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
    dF_dK,
    d2F_dK2,
    dF_dL,
    exact_kappa,
    box_worst_u,
    E_plus_exact,
    Interval,
    iv_F_A,
    iv_box_worst_u,
    iv_E_plus_exact,
    iv_eval_logpwl,
    iv_deriv_bounds_logpwl,
)
from pwl_model import pwl_from_dict, eval_logpwl


# ---------------------------------------------------------------------------
# 1. Section 3: Lemma 1, Theorem 9*, Proposition 1*, M0 Sharp Witness, Slack
# ---------------------------------------------------------------------------
def verify_section3_barriers(cegis_data: dict | None = None):
    print("=" * 72)
    print("1. SECTION 3: AFFINE BARRIERS (LEMMA 1, THM 9*, PROP 1*, M0 SHARP)")
    print("=" * 72)

    C_max_plus = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    R_hat = -0.996
    Delta_2 = 0.2997
    Delta_2_exact = (ETA_MIN * BETA_MIN * Q_MIN * (H_M - B_M)) / C_max_plus

    B_star = (R_hat - Delta_2) / (1.0 - BETA_MIN)
    slope = (ETA_MIN * Q_MIN) / C_max_plus
    B1_b = B_star - slope * (H_M - B_M)

    c_M_10 = Q_MIN * B_M + F_A(A_MIN, B_M, 0.68) - 0.135
    W_M_10_exact = float(box_worst_u(c_M_10, 0.68) + BETA_MAX * (-33.103))
    W_M_floor = -35.58
    margin_unif = W_M_floor - B_star
    margin_state = W_M_floor - B1_b

    J_T24 = B_star + (BETA_MAX ** 24) * (-27.83 - B_star)
    slack_T23 = (W_M_floor - B1_b) - (BETA_MAX ** 23) * (-27.83 - B_star)

    # Anchor band M0 = [0.05, 0.10) (Proposition 1*)
    b0, h0 = 0.05, 0.10
    C_max0 = Q_MAX * h0 + F_A(A_MAX, h0, 1.0) - b0
    Delta_0 = 0.3115
    Delta_0_exact = (ETA_MIN * BETA_MIN * Q_MIN * (h0 - b0)) / C_max0
    R_hat0 = -1.827
    Ls_chk = np.linspace(0.01, 0.999, 5000)
    cs_chk = Q_MAX * h0 + F_A(A_MAX, h0, Ls_chk) - b0
    R_hat0_exact = float(np.max(np.maximum(
        ETA_MIN * np.log(cs_chk) + (1.0 - ETA_MIN) * np.log(1.0 - Ls_chk),
        ETA_MAX * np.log(cs_chk) + (1.0 - ETA_MAX) * np.log(1.0 - Ls_chk),
    )))
    B0_star = (R_hat0 - Delta_0) / (1.0 - BETA_MIN)
    B0_star_exact = (R_hat0_exact - Delta_0_exact) / (1.0 - BETA_MIN)

    # Proposition 1* 3-step witness (0.05 -> 0.065 -> 0.0845 -> 0.100, L=0.75)
    # Note: c < 1 - L = 0.25 => du/d(eta) = log(c / (1 - L)) < 0 (worst eta = eta_+)
    orig_steps = [(0.05, 0.065, 0.75), (0.065, 0.0845, 0.75), (0.0845, 0.100, 0.75)]
    orig_cs = [Q_MIN * k + F_A(A_MIN, k, L) - kp for k, kp, L in orig_steps]
    assert all(c < 1.0 - 0.75 for c in orig_cs), "Expected c < 1 - L = 0.25 on all M0 steps"
    orig_us = [float(box_worst_u(c, L)) for c, (_, _, L) in zip(orig_cs, orig_steps)]
    W_M0_orig = sum((BETA_MAX ** t) * u for t, u in enumerate(orig_us)) + (BETA_MAX ** 3) * W_M_10_exact

    c1_max_L1 = Q_MIN * 0.05 + F_A(A_MIN, 0.05, 1.0) - 0.065
    u1_max_L = max(float(box_worst_u(Q_MIN * 0.05 + F_A(A_MIN, 0.05, L) - 0.065, L)) for L in np.linspace(0.50, 0.90, 2000))

    Psi_h0 = -34.271388
    J_M0_T10 = B0_star + (BETA_MAX ** 10) * (Psi_h0 - B0_star)

    # Sharpened M0 witness: (0.05 -> 0.0595 -> 0.0755 -> 0.100), L = (0.45, 0.50, 0.60)
    u1_steps = [(0.05, 0.0595, 0.45), (0.0595, 0.0755, 0.50), (0.0755, 0.100, 0.60)]
    u1_cs = [Q_MIN * k + F_A(A_MIN, k, L) - kp for k, kp, L in u1_steps]
    assert all(c < 1.0 - L for c, (_, _, L) in zip(u1_cs, u1_steps)), "Expected c < 1 - L on sharpened M0 steps"
    u1_us = [float(box_worst_u(c, L)) for c, (_, _, L) in zip(u1_cs, u1_steps)]
    W_M0_sharp = sum((BETA_MAX ** t) * u for t, u in enumerate(u1_us)) + (BETA_MAX ** 3) * W_M_10_exact

    # Check on full K0 in [0.05, 0.10) via temporary liquidation
    k0_grid = np.linspace(0.05, 0.09999, 200)
    W_M0_k0_grid = np.array([
        float(box_worst_u(Q_MIN * K0 + F_A(A_MIN, K0, 0.45) - 0.0595, 0.45))
        + BETA_MAX * u1_us[1]
        + (BETA_MAX ** 2) * u1_us[2]
        + (BETA_MAX ** 3) * W_M_10_exact
        for K0 in k0_grid
    ])

    # Outward-rounded 50-digit Interval cross-certification
    iv_A_MIN, iv_A_MAX = Interval("0.749"), Interval("0.751")
    iv_B_MIN, iv_B_MAX = Interval("0.9699"), Interval("0.9701")
    iv_Q_MIN, iv_Q_MAX = Interval("0.9199"), Interval("0.9201")
    iv_E_MIN, iv_E_MAX = Interval("0.6999"), Interval("0.7001")
    iv_B_M, iv_H_M = Interval("0.10"), Interval("0.28")
    iv_one = Interval("1")

    iv_C_max_plus = iv_Q_MAX * iv_H_M + iv_F_A(iv_A_MAX, iv_H_M, iv_one) - iv_B_M
    iv_Delta_2_exact = (iv_E_MIN * iv_B_MIN * iv_Q_MIN * (iv_H_M - iv_B_M)) / iv_C_max_plus
    iv_B_star = (Interval("-0.996") - Interval("0.2997")) / (iv_one - iv_B_MIN)
    iv_slope = (iv_E_MIN * iv_Q_MIN) / iv_C_max_plus
    iv_B1_b = iv_B_star - iv_slope * (iv_H_M - iv_B_M)
    iv_c_M_10 = iv_Q_MIN * iv_B_M + iv_F_A(iv_A_MIN, iv_B_M, Interval("0.68")) - Interval("0.135")
    iv_W_M_10 = iv_box_worst_u(iv_c_M_10, Interval("0.68")) + iv_B_MAX * Interval("-33.103")
    iv_margin_unif = Interval("-35.58") - iv_B_star
    iv_margin_state = Interval("-35.58") - iv_B1_b
    iv_J_T24 = iv_B_star + iv_B_MAX.pow_int(24) * (Interval("-27.83") - iv_B_star)
    iv_slack_T23 = (Interval("-35.58") - iv_B1_b) - iv_B_MAX.pow_int(23) * (Interval("-27.83") - iv_B_star)

    iv_b0, iv_h0 = Interval("0.05"), Interval("0.10")
    iv_C_max0 = iv_Q_MAX * iv_h0 + iv_F_A(iv_A_MAX, iv_h0, iv_one) - iv_b0
    iv_Delta_0_exact = (iv_E_MIN * iv_B_MIN * iv_Q_MIN * (iv_h0 - iv_b0)) / iv_C_max0
    iv_B0_star = (Interval("-1.827") - Interval("0.3115")) / (iv_one - iv_B_MIN)
    iv_slope0 = (iv_E_MIN * iv_Q_MIN) / iv_C_max0
    iv_B0_b0 = iv_B0_star - iv_slope0 * (iv_h0 - iv_b0)

    iv_orig_us = [
        iv_box_worst_u(iv_Q_MIN * Interval(str(k)) + iv_F_A(iv_A_MIN, Interval(str(k)), Interval(str(L))) - Interval(str(kp)), Interval(str(L)))
        for k, kp, L in orig_steps
    ]
    iv_W_M0_orig = iv_orig_us[0] + iv_B_MAX * iv_orig_us[1] + iv_B_MAX.pow_int(2) * iv_orig_us[2] + iv_B_MAX.pow_int(3) * iv_W_M_10

    iv_u1_us = [
        iv_box_worst_u(iv_Q_MIN * Interval(str(k)) + iv_F_A(iv_A_MIN, Interval(str(k)), Interval(str(L))) - Interval(str(kp)), Interval(str(L)))
        for k, kp, L in u1_steps
    ]
    iv_W_M0_sharp = iv_u1_us[0] + iv_B_MAX * iv_u1_us[1] + iv_B_MAX.pow_int(2) * iv_u1_us[2] + iv_B_MAX.pow_int(3) * iv_W_M_10

    assert iv_Delta_2_exact.lo > Decimal("0.2997")
    assert iv_B_star.hi <= Decimal("-43.0465115") and iv_B1_b.hi <= Decimal("-43.355593")
    assert iv_W_M_10.lo > Decimal("-35.58")
    assert iv_margin_unif.lo > Decimal("7.4665") and iv_margin_state.lo > Decimal("7.77559")
    assert iv_J_T24.hi < Decimal("-35.58") and iv_slack_T23.lo > Decimal("0.2056")
    assert iv_Delta_0_exact.lo > Decimal("0.3115") and iv_B0_star.hi <= Decimal("-71.0465115")
    assert iv_W_M0_orig.lo > Decimal("-43.845") and iv_W_M0_sharp.lo > Decimal("-43.541")

    print(f"  C_max+          = {C_max_plus:.8f}")
    print(f"  Delta_2 exact   = {Delta_2_exact:.7f} (> {Delta_2})")
    print(f"  B_*             = {B_star:.7f} (<= -43.0465116)")
    print(f"  B_1(0.10)       = {B1_b:.6f} (<= -43.355594)")
    print(f"  W_M(0.10) exact = {W_M_10_exact:.8f} (> -35.58)")
    print(f"  Margin (unif.)  = {margin_unif:.4f} (> 7.4665), Margin (state) = {margin_state:.6f} (> 7.7755)")
    print(f"  T=24 uniform    = {J_T24:.5f} (< -35.58), T=23 slack = +{slack_T23:.6f} (> 0)")
    print(f"  M0 C_max0       = {C_max0:.6f}, Delta_0 exact = {Delta_0_exact:.6f}")
    print(f"  M0 B_0*         = {B0_star:.6f} (exact R_hat0={R_hat0_exact:.6f} -> B_0*={B0_star_exact:.6f})")
    print(f"  M0 orig path u  = {[round(x, 6) for x in orig_us]} -> W_M0(0.05)={W_M0_orig:.6f} (> -43.845)")
    print(f"    (c < 1-L=0.25 verified: {[round(c, 6) for c in orig_cs]}; T0=10 prefix = {J_M0_T10:.6f})")
    print(f"  M0 sharp path u = {[round(x, 6) for x in u1_us]} -> W_M0_sharp(0.05)={W_M0_sharp:.6f}")

    # Check sharpened M0 witness against CEGIS Psi_net(0.10) if supplied
    if cegis_data is not None and "case1_affine_gap" in cegis_data:
        c1 = cegis_data["case1_affine_gap"]
        Psi_pwl = pwl_from_dict(c1["Psi_net"])
        W_pwl = pwl_from_dict(c1["W_net"])
        iv_dPsi_M0 = iv_deriv_bounds_logpwl(Psi_pwl, Interval._raw(Decimal("0.05"), Decimal("0.10")))
        assert iv_dPsi_M0.lo > iv_slope0.hi, f"Case 1 Psi' on M0 ({iv_dPsi_M0.lo}) <= (B^(0))' ({iv_slope0.hi})"
        iv_Psi_10 = iv_eval_logpwl(Psi_pwl, Interval("0.10"))
        iv_W10_cegis = iv_eval_logpwl(W_pwl, Interval("0.10"))
        iv_W_M0_cegis = iv_u1_us[0] + iv_B_MAX * iv_u1_us[1] + iv_B_MAX.pow_int(2) * iv_u1_us[2] + iv_B_MAX.pow_int(3) * iv_W10_cegis
        iv_J9_cegis = iv_B0_b0 + iv_B_MAX.pow_int(9) * (iv_Psi_10 - iv_B0_star)
        iv_gap_tau9_base = iv_W_M0_sharp - iv_J9_cegis
        iv_gap_tau9_cegis = iv_W_M0_cegis - iv_J9_cegis
        assert iv_gap_tau9_base.lo > 0 and iv_gap_tau9_cegis.lo > 0
        print(f"  M0 sharp tau_.1 <= 9 (with CEGIS Psi(0.10)={iv_Psi_10.to_float_bounds()[1]:.6f}, min dPsi/dK={float(iv_dPsi_M0.to_float_bounds()[0]):.2f} > {float(iv_slope0.hi):.4f}):")
        print(f"    J(9; 0.05)={iv_J9_cegis.to_float_bounds()[1]:.6f}, slack(MR-T4 tail)={float(iv_gap_tau9_base.lo):+.6f}, slack(CEGIS W tail)={float(iv_gap_tau9_cegis.lo):+.6f}")

    assert abs(C_max_plus - 0.37495167) < 1e-6
    assert B_star <= -43.0465115 and B1_b <= -43.355593
    assert W_M_10_exact > -35.58 and abs(W_M_10_exact - (-35.579855)) < 1e-5
    assert margin_unif > 7.4665 and margin_state > 7.77559
    assert J_T24 < W_M_floor and slack_T23 > 0.2056
    assert abs(B0_star - (-71.046512)) < 1e-6 and B0_star_exact <= B0_star
    assert abs(orig_us[0] - (-4.611772)) < 2e-6 and abs(orig_us[1] - (-3.964892)) < 2e-6 and abs(orig_us[2] - (-3.085659)) < 2e-6
    assert W_M0_orig > -43.845 and abs(W_M0_orig - (-43.844826)) < 2e-5
    assert c1_max_L1 < 0.00301 and u1_max_L < -4.59
    assert J_M0_T10 < W_M0_orig
    assert abs(W_M0_sharp - (-43.540132)) < 2e-5
    assert np.all(np.diff(W_M0_k0_grid) > 0.0) and W_M0_k0_grid[0] == W_M0_sharp


def _golden_solve_L(k_arr, kp_arr, f_norm, q, eta):
    lo_L = np.full_like(k_arr, 1e-7)
    hi_L = np.full_like(k_arr, 1.0 - 1e-9)
    inv_phi = (np.sqrt(5.0) - 1.0) / 2.0
    x1 = hi_L - inv_phi * (hi_L - lo_L)
    x2 = lo_L + inv_phi * (hi_L - lo_L)

    def obj(L_v):
        c_v = q * k_arr + f_norm(k_arr, L_v) - kp_arr
        return np.where(
            c_v > 1e-15,
            eta * np.log(np.maximum(c_v, 1e-30)) + (1.0 - eta) * np.log(1.0 - L_v),
            -1e9 + c_v,
        )

    f1, f2 = obj(x1), obj(x2)
    for _ in range(28):
        move_r = f1 < f2
        lo_L = np.where(move_r, x1, lo_L)
        hi_L = np.where(move_r, hi_L, x2)
        x1_new = np.where(move_r, x2, hi_L - inv_phi * (hi_L - lo_L))
        x2_new = np.where(move_r, lo_L + inv_phi * (hi_L - lo_L), x1)
        f1_new = np.where(move_r, f2, obj(x1_new))
        f2_new = np.where(move_r, obj(x2_new), f1)
        x1, x2, f1, f2 = x1_new, x2_new, f1_new, f2_new
    L_best = 0.5 * (lo_L + hi_L)
    return L_best, obj(L_best)


def verify_restricted_M_vfi():
    """Slack decomposition on M = [0.10, 0.28): B_1 (23) -> B_opt/CEGIS (9) -> VFI (4)."""
    print("\n  [Slack decomposition on M = [0.10, 0.28): B_1 vs B_opt / Restricted DP / VFI]")
    M_grid = np.linspace(B_M, H_M - 1e-5, 181)
    inv_phi = (np.sqrt(5.0) - 1.0) / 2.0

    def _rho_mat(A_v, q_v, e_v=None):
        lo = np.full((len(M_grid), len(M_grid)), 1e-8)
        hi = np.full((len(M_grid), len(M_grid)), 1.0 - 1e-9)

        def _gu(La):
            c = q_v * M_grid[:, None] + F_A(A_v, M_grid[:, None], La) - M_grid[None, :]
            lc = np.log(np.maximum(c, 1e-30))
            ll = np.log(1.0 - La)
            if e_v is None:
                uv = np.maximum(ETA_MIN * lc + (1.0 - ETA_MIN) * ll, ETA_MAX * lc + (1.0 - ETA_MAX) * ll)
            else:
                uv = e_v * lc + (1.0 - e_v) * ll
            return np.where(c > 1e-15, uv, -1e9 + c)

        u0 = _gu(np.zeros_like(lo))
        x1 = hi - inv_phi * (hi - lo)
        x2 = lo + inv_phi * (hi - lo)
        f1, f2 = _gu(x1), _gu(x2)
        for _ in range(20):
            mr = f1 < f2
            lo = np.where(mr, x1, lo)
            hi = np.where(mr, hi, x2)
            x1n = np.where(mr, x2, hi - inv_phi * (hi - lo))
            x2n = np.where(mr, lo + inv_phi * (hi - lo), x1)
            f1n = np.where(mr, f2, _gu(x1n))
            f2n = np.where(mr, _gu(x2n), f1)
            x1, x2, f1, f2 = x1n, x2n, f1n, f2n
        return np.maximum(u0, _gu(0.5 * (lo + hi)))

    Psi_sharp = 0.4 * M_grid - 5.0 * (M_grid ** (-0.5)) - 18.5 - 10.0 / 301.0
    c_M = Q_MIN * M_grid + F_A(A_MIN, M_grid, 0.68) - 0.135
    W_M_lb = box_worst_u(c_M, 0.68) + BETA_MAX * (-33.103)
    rho_up = _rho_mat(A_MAX, Q_MAX, e_v=None)

    J_dp = Psi_sharp.copy()
    gaps_dp = {}
    for T in range(1, 12):
        J_dp = np.max(rho_up + BETA_MAX * J_dp[None, :], axis=1)
        gaps_dp[T] = float(np.max(J_dp - W_M_lb))

    B_opt = np.full_like(M_grid, -40.0)
    for _ in range(1000):
        Bn = np.max(rho_up + BETA_MIN * B_opt[None, :], axis=1)
        if np.max(np.abs(Bn - B_opt)) < 1e-10:
            B_opt = Bn
            break
        B_opt = Bn
    inf_W_B = float(np.min(W_M_lb - B_opt))
    sup_Psi_B = float(np.max(Psi_sharp - B_opt))
    gap_Bopt_T8 = inf_W_B - (BETA_MAX ** 8) * sup_Psi_B
    gap_Bopt_T9 = inf_W_B - (BETA_MAX ** 9) * sup_Psi_B

    A_c, b_c, q_c, e_c = 0.75, 0.97, 0.92, 0.70
    K_g = np.unique(np.concatenate([
        np.geomspace(1e-4, 0.095, 100, endpoint=False),
        np.linspace(0.095, 0.285, 190, endpoint=False),
        np.geomspace(0.285, 4.0, 220),
    ]))
    log_K_g = np.log(K_g)
    solve_L_c = lambda ka, kpa: _golden_solve_L(ka, kpa, lambda k, L: F_A(A_c, k, L), q_c, e_c)

    def _iv(kp, Va):
        r = np.interp(np.log(np.clip(kp, K_g[0], K_g[-1])), log_K_g, Va)
        return np.where(kp < K_g[0], Va[0] + (e_c / (1.0 - b_c)) * np.log(np.maximum(kp, 1e-30) / K_g[0]), r)

    y_max = q_c * K_g + F_A(A_c, K_g, 0.9999)
    s_cand = 1.0 - np.geomspace(1e-5, 0.25, 65)
    kp_c = y_max[:, None] * s_cand[None, :]
    u_c = np.zeros_like(kp_c)
    for j in range(len(s_cand)):
        _, u_c[:, j] = solve_L_c(K_g, kp_c[:, j])
    V_cake0 = (e_c / (1.0 - b_c)) * (np.log((1.0 - b_c) * q_c) + (b_c / (1.0 - b_c)) * np.log(b_c * q_c))
    V_c = np.where(K_g > 0.002, -30.0, V_cake0 + (e_c / (1.0 - b_c)) * np.log(K_g))
    for _ in range(120):
        Vn = np.max(u_c + b_c * _iv(kp_c, V_c), axis=1)
        if np.max(np.abs(Vn - V_c)) < 1e-7:
            V_c = Vn
            break
        V_c = Vn
    for _ in range(80):
        idx = np.argmax(u_c + b_c * _iv(kp_c, V_c), axis=1)
        lo = y_max * s_cand[np.maximum(0, idx - 1)]
        hi = y_max * s_cand[np.minimum(len(s_cand) - 1, idx + 1)]
        x1 = hi - inv_phi * (hi - lo)
        x2 = lo + inv_phi * (hi - lo)
        _, u1 = solve_L_c(K_g, x1)
        _, u2 = solve_L_c(K_g, x2)
        f1 = u1 + b_c * _iv(x1, V_c)
        f2 = u2 + b_c * _iv(x2, V_c)
        for _g in range(26):
            mr = f1 < f2
            lo = np.where(mr, x1, lo)
            hi = np.where(mr, hi, x2)
            x1 = np.where(mr, x2, hi - inv_phi * (hi - lo))
            x2 = np.where(mr, lo + inv_phi * (hi - lo), x1)
            _, u1n = solve_L_c(K_g, x1)
            _, u2n = solve_L_c(K_g, x2)
            f1 = np.where(mr, f2, u1n + b_c * _iv(x1, V_c))
            f2 = np.where(mr, u2n + b_c * _iv(x2, V_c), f1)
        pol_c = 0.5 * (lo + hi)
        _, up = solve_L_c(K_g, pol_c)
        Vn = up + b_c * _iv(pol_c, V_c)
        for _h in range(40):
            Vh = up + b_c * _iv(pol_c, Vn)
            if np.max(np.abs(Vh - Vn)) < 1e-10:
                Vn = Vh
                break
            Vn = Vh
        if np.max(np.abs(Vn - V_c)) < 1e-9:
            V_c = Vn
            break
        V_c = Vn

    max_tau_vfi = 0
    for k0 in M_grid:
        k = float(k0)
        t = 0
        while k < H_M and t < 50:
            k = float(np.interp(np.log(k), log_K_g, pol_c))
            t += 1
        max_tau_vfi = max(max_tau_vfi, t)

    V_M_true = np.interp(np.log(M_grid), log_K_g, V_c)
    rho_c = _rho_mat(A_c, q_c, e_v=e_c)
    J_true = V_M_true.copy()
    gaps_true = {}
    for T in range(1, 7):
        J_true = np.max(rho_c + b_c * J_true[None, :], axis=1)
        gaps_true[T] = (float(np.max(J_true - V_M_true)), float(J_true[0] - V_M_true[0]))

    print(f"    Box-upper restricted DP (Psi^sharp vs W_M): T=8 gap={gaps_dp[8]:+.6f}, T=9 gap={gaps_dp[9]:+.6f} (tau_H^DP = 9)")
    print(f"    Optimal regional barrier B_opt on M: [{B_opt[0]:.6f}, {B_opt[-1]:.6f}] -> T=8 gap={gap_Bopt_T8:+.6f}, T=9 gap={gap_Bopt_T9:+.6f}")
    print(f"    Center VFI (A=0.75, beta=0.97): V(0.10)={V_M_true[0]:.6f}, max_{{K0 in M}} tau_H^VFI = {max_tau_vfi}")
    print(f"    True restricted DP vs V(K): T=1..6 max = {[round(gaps_true[t][0], 6) for t in range(1, 7)]}")
    assert gaps_dp[8] > 0.0 and gaps_dp[9] < -0.50
    assert abs(B_opt[0] - (-56.794979)) < 1e-4 and abs(B_opt[-1] - (-52.457990)) < 1e-4
    assert gap_Bopt_T8 < 0.0 and gap_Bopt_T9 > 0.45
    assert max_tau_vfi == 4
    assert gaps_true[4][0] < -0.15 and gaps_true[5][0] < -0.70


# ---------------------------------------------------------------------------
# 2. Section 3.4: Proposition 1** & Table 2
# ---------------------------------------------------------------------------
def t_func(K, l0):
    return dF_dL(A_MAX, K, l0)


def t_prime(K, l0):
    return 1.5 * A_MAX * (2.0 ** 1.5) * 2.5 * (K ** 1.5) * (l0 ** 1.5) * ((K + l0) ** (-3.5))


def t_double_prime(K, l0):
    return 1.5 * A_MAX * (2.0 ** 1.5) * 2.5 * (l0 ** 1.5) * (K ** 0.5) * ((K + l0) ** (-4.5)) * (1.5 * l0 - 2.0 * K)


def verify_prop1_double_star():
    print("\n" + "=" * 72)
    print("2. PROPOSITION 1** & TABLE 2 (ANALYTICAL INTERVAL CERTIFICATE)")
    print("=" * 72)

    regions = {
        "M": dict(l_X=0.68, s_X=0.135, T_X=-33.103, a=0.10, l0=0.44, k_min=0.10, k_max=0.28, n_q=4, n_d2=8),
        "H1": dict(l_X=0.72, s_X=0.375, T_X=-27.164, a=0.28, l0=0.57, k_min=0.28, k_max=0.80, n_q=6, n_d2=10),
        "H1_060": dict(l_X=0.72, s_X=0.375, T_X=-27.164, a=0.28, l0=0.60, k_min=0.28, k_max=0.80, n_q=6, n_d2=10),
    }

    def S_val(K, l0):
        return Q_MAX * K + F_A(A_MAX, K, l0) + (1.0 - l0) * t_func(K, l0)

    def S_prime(K, l0):
        return Q_MAX + dF_dK(A_MAX, K, l0) + (1.0 - l0) * t_prime(K, l0)

    def c_val(K, l_X, s_X):
        return Q_MIN * K + F_A(A_MIN, K, l_X) - s_X

    def c_prime(K, l_X):
        return Q_MIN + dF_dK(A_MIN, K, l_X)

    def d1_exact(K, cfg):
        l_X, s_X, a, l0 = cfg["l_X"], cfg["s_X"], cfg["a"], cfg["l0"]
        S = S_val(K, l0)
        Sp = S_prime(K, l0)
        c = c_val(K, l_X, s_X)
        cp = c_prime(K, l_X)
        R = (S - a) / c
        return (ETA_MIN * cp * R - Sp) / (S - a) + (1.0 - ETA_MAX) * 2.5 * l0 / (K * (K + l0))

    iv_A_MIN, iv_A_MAX = Interval("0.749"), Interval("0.751")
    iv_Q_MIN, iv_Q_MAX = Interval("0.9199"), Interval("0.9201")
    iv_E_MIN, iv_E_MAX = Interval("0.6999"), Interval("0.7001")
    iv_B_MIN, iv_B_MAX = Interval("0.9699"), Interval("0.9701")
    iv_one = Interval("1")
    iv_two32 = Interval("2").pow_half_int(3)
    iv_sq73 = Interval("73").sqrt()
    iv_sq63 = Interval("63").sqrt()

    def iv_dFdK(A, K, L):
        return Interval("1.5") * A * iv_two32 * K.pow_half_int(1) * L.pow_half_int(5) * (K + L).pow_half_int(-5)

    def iv_d2FdK2(A, K, L):
        return Interval("0.75") * A * iv_two32 * L.pow_half_int(5) * (L - Interval("4") * K) * K.pow_half_int(-1) * (K + L).pow_half_int(-7)

    def iv_dFdL(A, K, L):
        return Interval("1.5") * A * iv_two32 * K.pow_half_int(5) * L.pow_half_int(1) * (K + L).pow_half_int(-5)

    def iv_tp(K, l0):
        return Interval("1.5") * iv_A_MAX * iv_two32 * Interval("2.5") * K.pow_half_int(3) * l0.pow_half_int(3) * (K + l0).pow_half_int(-7)

    def iv_tpp(K, l0):
        return Interval("1.5") * iv_A_MAX * iv_two32 * Interval("2.5") * l0.pow_half_int(3) * K.pow_half_int(1) * (K + l0).pow_half_int(-9) * (Interval("1.5") * l0 - Interval("2") * K)

    def iv_clip_pt(kc, kL, kR):
        if kc.hi <= kL.lo or kc.lo >= kR.hi:
            return None
        return Interval._raw(max(kc.lo, kL.lo), min(kc.hi, kR.hi))

    for name, cfg in regions.items():
        l_X, s_X, _, a, l0 = cfg["l_X"], cfg["s_X"], cfg["T_X"], cfg["a"], cfg["l0"]
        assert l0 >= cfg["k_max"] / 2.0
        if name == "M":
            edges_q_str = ["0.10", "0.145", "0.19", "0.235", "0.28"]
            edges_d2_str = [str(Decimal("0.10") + Decimal(i) * Decimal("0.0225")) for i in range(9)]
        else:
            edges_q_str = ["0.28", "0.36", "0.45", "0.54", "0.63", "0.72", "0.80"]
            edges_d2_str = [str(Decimal("0.28") + Decimal(i) * Decimal("0.052")) for i in range(11)]

        iv_lX, iv_sX, iv_a, iv_l0 = Interval(str(l_X)), Interval(str(s_X)), Interval(str(a)), Interval(str(l0))
        iv_S = lambda K: iv_Q_MAX * K + iv_F_A(iv_A_MAX, K, iv_l0) + (iv_one - iv_l0) * iv_dFdL(iv_A_MAX, K, iv_l0)
        iv_Sp = lambda K: iv_Q_MAX + iv_dFdK(iv_A_MAX, K, iv_l0) + (iv_one - iv_l0) * iv_tp(K, iv_l0)
        iv_c = lambda K: iv_Q_MIN * K + iv_F_A(iv_A_MIN, K, iv_lX) - iv_sX
        iv_cp = lambda K: iv_Q_MIN + iv_dFdK(iv_A_MIN, K, iv_lX)

        iv_Q_bounds, iv_d1_bounds, iv_d2_bounds = [], [], []
        for kLs, kRs in zip(edges_q_str[:-1], edges_q_str[1:]):
            ikL, ikR = Interval(kLs), Interval(kRs)
            ikm = Interval("0.5") * (ikL + ikR)
            iQm = iv_Sp(ikm) * iv_c(ikm) - iv_cp(ikm) * (iv_S(ikm) - iv_a)
            id2F = [ikL, ikR]
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_l0 * (Interval("7") + sgn * iv_sq73) / Interval("24"), ikL, ikR)) is not None:
                    id2F.append(pt_c)
            ikc_q = iv_l0 / Interval("4")
            if (pt_q := iv_clip_pt(ikc_q, ikL, ikR)) is not None:
                id2F.append(pt_q)
            itpp = [ikL, ikR]
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_l0 * (Interval("9") + sgn * iv_sq63) / Interval("12"), ikL, ikR)) is not None:
                    itpp.append(pt_c)
            ikc_t = Interval("0.75") * iv_l0
            if (pt_t := iv_clip_pt(ikc_t, ikL, ikR)) is not None:
                itpp.append(pt_t)
            id2Fc = [ikL, ikR]
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_lX * (Interval("7") + sgn * iv_sq73) / Interval("24"), ikL, ikR)) is not None:
                    id2Fc.append(pt_c)
            if (pt_c := iv_clip_pt(iv_lX / Interval("4"), ikL, ikR)) is not None:
                id2Fc.append(pt_c)
            iSpp_hi = max(iv_d2FdK2(iv_A_MAX, pt, iv_l0).abs().hi for pt in id2F) + (iv_one - iv_l0).hi * max(iv_tpp(pt, iv_l0).abs().hi for pt in itpp)
            icpp_hi = max(iv_d2FdK2(iv_A_MIN, pt, iv_lX).abs().hi for pt in id2Fc)
            iQp_max = Interval(iSpp_hi) * iv_c(ikR) + Interval(icpp_hi) * (iv_S(ikR) - iv_a)
            iQ_ub = iQm + Interval("0.5") * (ikR - ikL) * iQp_max
            iv_Q_bounds.append(iQ_ub.to_float_bounds()[1])
            assert iQ_ub.hi < 0

            icp_min = Interval(min(iv_cp(ikL).lo, iv_cp(ikR).lo))
            ic_dFk = [ikL, ikR] + ([pt_q] if (pt_q := iv_clip_pt(ikc_q, ikL, ikR)) is not None else [])
            ic_tp = [ikL, ikR] + ([pt_t] if (pt_t := iv_clip_pt(ikc_t, ikL, ikR)) is not None else [])
            iSp_max = iv_Q_MAX + Interval(max(iv_dFdK(iv_A_MAX, p, iv_l0).hi for p in ic_dFk)) + (iv_one - iv_l0) * Interval(max(iv_tp(p, iv_l0).hi for p in ic_tp))
            iR_lb = (iv_S(ikR) - iv_a) / iv_c(ikR)
            inum_lb = iv_E_MIN * icp_min * iR_lb - iSp_max
            iS_aL, iS_aR = iv_S(ikL) - iv_a, iv_S(ikR) - iv_a
            idenom = iS_aR if inum_lb.lo >= 0 else (iS_aL if inum_lb.hi <= 0 else iS_aL.hull(iS_aR))
            id1_lb = inum_lb / idenom + (iv_one - iv_E_MAX) * Interval("2.5") * iv_l0 / (ikR * (ikR + iv_l0))
            iv_d1_bounds.append(id1_lb.to_float_bounds()[0])
            assert id1_lb.lo > 0

        for kLs, kRs in zip(edges_d2_str[:-1], edges_d2_str[1:]):
            ikL, ikR = Interval(kLs), Interval(kRs)
            ikc_q, ikc_t = iv_l0 / Interval("4"), Interval("0.75") * iv_l0
            ic_dFk = [ikL, ikR] + ([pt_q] if (pt_q := iv_clip_pt(ikc_q, ikL, ikR)) is not None else [])
            ic_tp = [ikL, ikR] + ([pt_t] if (pt_t := iv_clip_pt(ikc_t, ikL, ikR)) is not None else [])
            iSp_ub = iv_Q_MAX + Interval(max(iv_dFdK(iv_A_MAX, p, iv_l0).hi for p in ic_dFk)) + (iv_one - iv_l0) * Interval(max(iv_tp(p, iv_l0).hi for p in ic_tp))
            icp_lb = Interval(min(iv_cp(ikL).lo, iv_cp(ikR).lo))
            iR_lb = (iv_S(ikR) - iv_a) / iv_c(ikR)
            it1_num = iSp_ub.pow_int(2) - iv_E_MIN * (icp_lb * iR_lb).pow_int(2)
            iSaL2, iSaR2 = (iv_S(ikL) - iv_a).pow_int(2), (iv_S(ikR) - iv_a).pow_int(2)
            it1_ub = it1_num / (iSaL2 if it1_num.lo >= 0 else (iSaR2 if it1_num.hi <= 0 else iSaL2.hull(iSaR2)))

            icands_cpp = [ikL, ikR]
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_lX * (Interval("7") + sgn * iv_sq73) / Interval("24"), ikL, ikR)) is not None:
                    icands_cpp.append(pt_c)
            if (pt_c := iv_clip_pt(iv_lX / Interval("4"), ikL, ikR)) is not None:
                icands_cpp.append(pt_c)
            icpp_ub = Interval(max(iv_d2FdK2(iv_A_MIN, p, iv_lX).hi for p in icands_cpp))
            if icpp_ub.lo >= 0:
                it2_ub = iv_E_MAX * icpp_ub / iv_c(ikL)
            elif icpp_ub.hi <= 0:
                it2_ub = iv_E_MIN * icpp_ub / iv_c(ikR)
            else:
                it2_ub = (iv_E_MAX * Interval._raw(Decimal(0), icpp_ub.hi) / iv_c(ikL)) + (iv_E_MIN * Interval._raw(icpp_ub.lo, Decimal(0)) / iv_c(ikR))

            iSpp_L = [ikL, ikR] + ([pt_q] if (pt_q := iv_clip_pt(ikc_q, ikL, ikR)) is not None else [])
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_l0 * (Interval("7") + sgn * iv_sq73) / Interval("24"), ikL, ikR)) is not None:
                    iSpp_L.append(pt_c)
            iSpp_t = [ikL, ikR] + ([pt_t] if (pt_t := iv_clip_pt(ikc_t, ikL, ikR)) is not None else [])
            for sgn in (Interval("-1"), Interval("1")):
                if (pt_c := iv_clip_pt(iv_l0 * (Interval("9") + sgn * iv_sq63) / Interval("12"), ikL, ikR)) is not None:
                    iSpp_t.append(pt_c)
            iSpp_lb = Interval(min(iv_d2FdK2(iv_A_MAX, p, iv_l0).lo for p in iSpp_L)) + (iv_one - iv_l0) * Interval(min(iv_tpp(p, iv_l0).lo for p in iSpp_t))
            imSpp = -iSpp_lb
            iSaL, iSaR = iv_S(ikL) - iv_a, iv_S(ikR) - iv_a
            it3_ub = imSpp / (iSaL if imSpp.lo >= 0 else (iSaR if imSpp.hi <= 0 else iSaL.hull(iSaR)))
            it4_ub = (iv_one - iv_E_MAX) * (Interval("-2.5") * iv_l0 * (Interval("2") * ikR + iv_l0)) / (ikR.pow_int(2) * (ikR + iv_l0).pow_int(2))
            id2_ub = it1_ub + it2_ub + it3_ub + it4_ub
            iv_d2_bounds.append(id2_ub.to_float_bounds()[1])
            assert id2_ub.hi < 0

        # 50-digit Interval enclosure of interior leisure omega*(K, eta) < 1 and (F.20) s=0 branch
        iv_k0_d = Decimal(str(cfg["k_min"]))
        iv_k1_d = Decimal(str(cfg["k_max"]))
        iv_step = (iv_k1_d - iv_k0_d) / Decimal("40")
        u_lo_iv = Decimal("1e30")
        u_hi_iv = Decimal("-1e30")
        iv_Psi_s_005 = (
            Interval("0.4") * Interval("0.05")
            - Interval("5") * Interval("0.05").pow_half_int(-1)
            - Interval("18.5")
            - Interval("10") / Interval("301")
        )
        s0_min_iv = Decimal("1e30")
        iv_zero = Interval("0")
        iv_TX_c = Interval(str(cfg["T_X"]))
        for jj in range(40):
            ka = Interval._raw(iv_k0_d + Decimal(jj) * iv_step, iv_k0_d + Decimal(jj) * iv_step)
            kb = Interval._raw(iv_k0_d + Decimal(jj + 1) * iv_step, iv_k0_d + Decimal(jj + 1) * iv_step)
            iv_S_rng = Interval._raw(iv_S(ka).lo, iv_S(kb).hi)
            iv_t_rng = Interval._raw(iv_dFdL(iv_A_MAX, ka, iv_l0).lo, iv_dFdL(iv_A_MAX, kb, iv_l0).hi)
            iv_om_box = (iv_one - Interval._raw(iv_E_MIN.lo, iv_E_MAX.hi)) * (iv_S_rng - iv_a) / iv_t_rng
            u_lo_iv = min(u_lo_iv, iv_om_box.lo)
            u_hi_iv = max(u_hi_iv, iv_om_box.hi)
            W_lo_seg = iv_box_worst_u(iv_c(ka), iv_lX) + iv_B_MAX * iv_TX_c
            E0_hi_seg = iv_E_plus_exact(iv_A_MAX, iv_Q_MAX, kb, iv_zero, iv_l0) + iv_B_MIN * iv_Psi_s_005
            s0_min_iv = min(s0_min_iv, (W_lo_seg - E0_hi_seg).lo)
        u_lo = float(Interval._raw(u_lo_iv, u_lo_iv).to_float_bounds()[0])
        u_hi = float(Interval._raw(u_hi_iv, u_hi_iv).to_float_bounds()[1])
        s0_lb = float(Interval._raw(s0_min_iv, s0_min_iv).to_float_bounds()[0])
        d1_right = d1_exact(cfg["k_max"], cfg)
        print(f"  Region {name}:")
        print(f"    Wronskian Q_{name} <= {[round(x, 5) for x in iv_Q_bounds]} (max {max(iv_Q_bounds):.5f})")
        print(f"    Delta'_{name}     >= {[round(x, 4) for x in iv_d1_bounds]} (min {min(iv_d1_bounds):+.4f})")
        print(f"    Delta''_{name}    <= {[round(x, 4) for x in iv_d2_bounds[:4]]} ... (max {max(iv_d2_bounds):.4f} < 0)")
        print(f"    Delta'_{name}(right) = +{d1_right:.6f} | omega*_iv in [{u_lo:.4f}, {u_hi:.4f}] < 1 | (F.20) s=0 min_iv = +{s0_lb:.4f}")
        assert u_hi_iv < Decimal("1") and s0_min_iv > Decimal("0")

    def iv_margin_left(K_s, lX_s, sX_s, TX_s, a_s, l0_s, iv_Psi_a):
        K_iv, lX_iv, sX_iv, a_iv, l0_iv = Interval(K_s), Interval(lX_s), Interval(sX_s), Interval(a_s), Interval(l0_s)
        c_iv = iv_Q_MIN * K_iv + iv_F_A(iv_A_MIN, K_iv, lX_iv) - sX_iv
        W_iv = iv_box_worst_u(c_iv, lX_iv) + iv_B_MAX * Interval(TX_s)
        E_iv = iv_E_plus_exact(iv_A_MAX, iv_Q_MAX, K_iv, a_iv, l0_iv)
        return W_iv - (E_iv + iv_B_MIN * iv_Psi_a)

    iv_Psi_010 = Interval("0.4") * Interval("0.10") - Interval("5") * Interval("0.10").pow_half_int(-1) - Interval("18.5")
    iv_Psi_s_010 = iv_Psi_010 - Interval("10") / Interval("301")
    iv_Psi_028 = Interval("0.4") * Interval("0.28") - Interval("5") * Interval("0.28").pow_half_int(-1) - Interval("18.5")
    iv_Psi_s_028 = iv_Psi_028 - Interval("10") / Interval("301")

    iv_m_M_sharp = iv_margin_left("0.10", "0.68", "0.135", "-33.103", "0.10", "0.44", iv_Psi_s_010)
    iv_m_M_psi = iv_margin_left("0.10", "0.68", "0.135", "-33.103", "0.10", "0.44", iv_Psi_010)
    iv_m_H_60 = iv_margin_left("0.28", "0.72", "0.375", "-27.164", "0.28", "0.60", iv_Psi_s_028)
    iv_m_H_57 = iv_margin_left("0.28", "0.72", "0.375", "-27.164", "0.28", "0.57", iv_Psi_s_028)
    iv_m_H_57_psi = iv_margin_left("0.28", "0.72", "0.375", "-27.164", "0.28", "0.57", iv_Psi_028)

    print(f"  K=0.10 (l0=0.44): Interval lb(Psi#)={iv_m_M_sharp.to_float_bounds()[0]:.6f}, lb(Psi)={iv_m_M_psi.to_float_bounds()[0]:.6f}")
    print(f"  K=0.28 (l0=0.60): Interval lb(Psi#)={iv_m_H_60.to_float_bounds()[0]:.6f}")
    print(f"  K=0.28 (l0=0.57): Interval lb(Psi#)={iv_m_H_57.to_float_bounds()[0]:.6f}, lb(Psi)={iv_m_H_57_psi.to_float_bounds()[0]:.6f}")
    assert iv_m_M_sharp.lo > Decimal("0.0947") and iv_m_M_psi.lo > Decimal("0.0624")
    assert iv_m_H_60.lo > Decimal("0.0561") and iv_m_H_57.lo > Decimal("0.0571") and iv_m_H_57_psi.lo > Decimal("0.0249")


# ---------------------------------------------------------------------------
# 3. Section 4: Depurated Log-k VFI, Theorem 3*, Corollary 2*, Table 3
# ---------------------------------------------------------------------------
def solve_vfi_frontiers(A_val, beta=0.97, k_band=(0.00078, 0.00102), return_policy=False):
    """
    Continuous-state normalized VFI in k = A^2 K with log(k) value interpolation
    (eliminating Jensen concavity bias on geometric upper grids) and exact
    same-point Skiba evaluation of dW_plus and dW_pi_plus.
    """
    theta, rho, w, delta, eta = 1.5, -1.0, 0.5, 0.08, 0.70
    q = 1.0 - delta
    c_K = w ** (theta / rho)
    D = 1.0 / beta - q
    V_cake_const = (eta / (1.0 - beta)) * (
        np.log((1.0 - beta) * q) + (beta / (1.0 - beta)) * np.log(beta * q)
    )

    def f_norm(k_arr, L_arr):
        return c_K * (k_arr ** 1.5) * ((1.0 + k_arr / ((A_val ** 2) * L_arr)) ** (-1.5))

    def df_dk(k):
        return 1.5 * c_K * (k ** 0.5) * ((1.0 + k / (A_val ** 2)) ** (-2.5))

    lo_ss = 0.25 * (A_val ** 2)
    while df_dk(lo_ss) <= D and lo_ss > 1e-6:
        lo_ss *= 0.5
    hi_ss = max(1e10, 10.0 * np.sqrt(1.5 * c_K / D) * (A_val ** 2.5))
    while df_dk(hi_ss) >= D:
        hi_ss *= 10.0
    k_ss = brentq(lambda k: df_dk(k) - D, lo_ss, hi_ss)
    k_lo, k_hi = 1e-6, 1.15 * k_ss

    k_b0, k_b1 = k_band
    if k_hi > 150.0:
        k_grid = np.unique(np.concatenate([
            np.geomspace(k_lo, k_b0, 100, endpoint=False),
            np.linspace(k_b0, k_b1, 800, endpoint=False),
            np.geomspace(k_b1, 0.05, 650, endpoint=False),
            np.geomspace(0.05, 100.0, 250, endpoint=False),
            np.geomspace(100.0, k_hi, 450),
        ]))
    elif k_hi > 0.10:
        k_grid = np.unique(np.concatenate([
            np.geomspace(k_lo, k_b0, 100, endpoint=False),
            np.linspace(k_b0, k_b1, 800, endpoint=False),
            np.geomspace(k_b1, min(0.05, 0.5 * k_hi), 650, endpoint=False),
            np.geomspace(min(0.05, 0.5 * k_hi), k_hi, 600),
        ]))
    else:
        k_grid = np.unique(np.concatenate([
            np.geomspace(k_lo, k_b0, 100, endpoint=False),
            np.linspace(k_b0, k_b1, 800, endpoint=False),
            np.geomspace(k_b1, k_hi, 1000),
        ]))
    log_k_grid = np.log(k_grid)
    n_k = len(k_grid)

    def make_interp_V(V_curr):
        pchip = PchipInterpolator(log_k_grid, V_curr, extrapolate=False)

        def _fn(kp_arr):
            kp = np.asarray(kp_arr, dtype=np.float64)
            lk = np.log(np.clip(kp, k_lo, k_hi))
            v = pchip(lk)
            below = kp < k_lo
            if np.any(below):
                v = np.where(
                    below,
                    V_curr[0] + (eta / (1.0 - beta)) * np.log(np.maximum(kp, 1e-30) / k_lo),
                    v,
                )
            return v

        return _fn

    def solve_L_vec(k_arr, kp_arr):
        return _golden_solve_L(k_arr, kp_arr, f_norm, q, eta)

    def refine_skiba(i_jump, V_sol, endo=False):
        iv_fn = make_interp_V(V_sol)
        k_sub = np.linspace(k_grid[i_jump - 1], k_grid[i_jump], 35)
        y_sub = q * k_sub + f_norm(k_sub, 1.0)
        diffs = np.empty_like(k_sub)
        for ii, (ks, ys) in enumerate(zip(k_sub, y_sub)):
            kp_d = np.linspace(max(1e-7, 0.90 * ks), ks, 35)
            kp_u = np.linspace(ks, ys - 1e-12, 35) if ys > ks + 1e-12 else np.array([ks])
            if not endo:
                vd = np.max(eta * np.log(np.maximum(ys - kp_d, 1e-30)) + beta * iv_fn(kp_d))
                vu = (
                    np.max(eta * np.log(np.maximum(ys - kp_u, 1e-30)) + beta * iv_fn(kp_u))
                    if ys > ks + 1e-12
                    else -1e9
                )
            else:
                _, ud = solve_L_vec(np.full_like(kp_d, ks), kp_d)
                vd = np.max(ud + beta * iv_fn(kp_d))
                if ys > ks + 1e-12:
                    _, uu = solve_L_vec(np.full_like(kp_u, ks), kp_u)
                    vu = np.max(uu + beta * iv_fn(kp_u))
                else:
                    vu = -1e9
            diffs[ii] = vu - vd
        pos = np.where(diffs >= 0)[0]
        if len(pos) > 0 and pos[0] > 0:
            idx0 = pos[0]
            d0, d1 = diffs[idx0 - 1], diffs[idx0]
            w0 = abs(d0) / max(abs(d0) + abs(d1), 1e-15)
            return float(k_sub[idx0 - 1] + w0 * (k_sub[idx0] - k_sub[idx0 - 1]))
        return float(0.5 * (k_grid[i_jump - 1] + k_grid[i_jump]))

    inv_phi = (np.sqrt(5.0) - 1.0) / 2.0

    # --- 1. Fixed labor L = 1 ---
    y_fix = q * k_grid + f_norm(k_grid, 1.0)
    k_init = 0.00082 if abs(k_b0 - 0.00078) < 1e-8 else 0.5 * (k_b0 + k_b1)
    V_fix = np.where(
        k_grid > k_init,
        eta * np.log(f_norm(k_ss, 1.0) - delta * k_ss) / (1.0 - beta),
        V_cake_const + (eta / (1.0 - beta)) * np.log(k_grid),
    )

    s_cand = 1.0 - np.geomspace(1e-5, 0.15, 70)
    kp_mat_tail = y_fix[:, None] * s_cand[None, :]
    u_mat_tail = eta * np.log(y_fix[:, None] * (1.0 - s_cand[None, :]))
    c_mat_grid = y_fix[:, None] - k_grid[None, :]
    u_mat_grid = np.where(c_mat_grid > 1e-15, eta * np.log(np.maximum(c_mat_grid, 1e-30)), -1e9)

    for _ in range(250):
        iv_fix = make_interp_V(V_fix)
        v_grid = u_mat_grid + beta * V_fix[None, :]
        j_best = np.argmax(v_grid, axis=1)
        best_g = v_grid[np.arange(n_k), j_best]

        v_tail = u_mat_tail + beta * iv_fix(kp_mat_tail)
        s_best = np.argmax(v_tail, axis=1)
        best_t = v_tail[np.arange(n_k), s_best]

        use_t = best_t > best_g
        lo_t = kp_mat_tail[np.arange(n_k), np.maximum(0, s_best - 1)]
        hi_t = kp_mat_tail[np.arange(n_k), np.minimum(len(s_cand) - 1, s_best + 1)]
        lo = np.where(use_t, np.minimum(lo_t, hi_t), k_grid[np.maximum(0, j_best - 1)])
        hi = np.where(
            use_t,
            np.minimum(np.maximum(lo_t, hi_t), y_fix * (1.0 - 1e-12)),
            np.minimum(k_grid[np.minimum(n_k - 1, j_best + 1)], y_fix * (1.0 - 1e-12)),
        )

        x1 = hi - inv_phi * (hi - lo)
        x2 = lo + inv_phi * (hi - lo)
        f1 = eta * np.log(np.maximum(y_fix - x1, 1e-30)) + beta * iv_fix(x1)
        f2 = eta * np.log(np.maximum(y_fix - x2, 1e-30)) + beta * iv_fix(x2)
        for _g in range(20):
            mr = f1 < f2
            lo = np.where(mr, x1, lo)
            hi = np.where(mr, hi, x2)
            x1_n = np.where(mr, x2, hi - inv_phi * (hi - lo))
            x2_n = np.where(mr, lo + inv_phi * (hi - lo), x1)
            f1_n = np.where(mr, f2, eta * np.log(np.maximum(y_fix - x1_n, 1e-30)) + beta * iv_fix(x1_n))
            f2_n = np.where(mr, eta * np.log(np.maximum(y_fix - x2_n, 1e-30)) + beta * iv_fix(x2_n), f1)
            x1, x2, f1, f2 = x1_n, x2_n, f1_n, f2_n
        pol_fix = np.where(f1 > f2, x1, x2)
        u_pol = eta * np.log(np.maximum(y_fix - pol_fix, 1e-30))
        V_eval = np.maximum(f1, f2)
        for _h in range(120):
            Ve_n = u_pol + beta * make_interp_V(V_eval)(pol_fix)
            if np.max(np.abs(Ve_n - V_eval)) < 1e-11:
                V_eval = Ve_n
                break
            V_eval = Ve_n
        if np.max(np.abs(V_eval - V_fix)) < 1e-10:
            V_fix = V_eval
            break
        V_fix = V_eval

    idx_m = np.where((k_grid >= k_b0) & (k_grid <= k_b1))[0]
    jump = np.where((pol_fix - k_grid)[idx_m] > 0)[0][0]
    k_S_fix = refine_skiba(idx_m[jump], V_fix, endo=False)

    # --- 2. Endogenous labor L in [0, 1) ---
    L_grid = np.unique(np.concatenate([
        np.geomspace(1e-5, 0.05, 24, endpoint=False),
        np.linspace(0.05, 0.999, 44),
    ]))
    f_kL = c_K * (k_grid[:, None] ** 1.5) * ((1.0 + k_grid[:, None] / ((A_val ** 2) * L_grid[None, :])) ** (-1.5))
    y_kL = q * k_grid[:, None] + f_kL
    dis_L = (1.0 - eta) * np.log(1.0 - L_grid[None, :])

    u_endo_grid = np.full((n_k, n_k), -1e9)
    chunk = 100
    for start in range(0, n_k, chunk):
        end = min(n_k, start + chunk)
        c_blk = y_kL[start:end, None, :] - k_grid[None, :, None]
        u_blk = np.where(c_blk > 1e-15, eta * np.log(np.maximum(c_blk, 1e-30)) + dis_L[:, None, :], -1e9)
        u_endo_grid[start:end, :] = np.max(u_blk, axis=2)

    s_cand_e = 1.0 - np.geomspace(1e-5, 0.15, 70)
    kp_tail_e = y_kL[:, -1][:, None] * s_cand_e[None, :]
    u_tail_e = np.full((n_k, len(s_cand_e)), -1e9)
    for j in range(len(s_cand_e)):
        _, u_tail_e[:, j] = solve_L_vec(k_grid, kp_tail_e[:, j])

    V_endo = V_fix.copy() - 0.5
    y_max_row = y_kL[:, -1]
    for _ in range(250):
        iv_endo = make_interp_V(V_endo)
        v_g = u_endo_grid + beta * V_endo[None, :]
        j_best = np.argmax(v_g, axis=1)
        best_g = v_g[np.arange(n_k), j_best]

        v_t = u_tail_e + beta * iv_endo(kp_tail_e)
        s_best = np.argmax(v_t, axis=1)
        best_t = v_t[np.arange(n_k), s_best]

        use_t = best_t > best_g
        lo_t = kp_tail_e[np.arange(n_k), np.maximum(0, s_best - 1)]
        hi_t = kp_tail_e[np.arange(n_k), np.minimum(len(s_cand_e) - 1, s_best + 1)]
        lo = np.where(use_t, np.minimum(lo_t, hi_t), k_grid[np.maximum(0, j_best - 1)])
        hi = np.where(
            use_t,
            np.minimum(np.maximum(lo_t, hi_t), y_max_row * (1.0 - 1e-12)),
            np.minimum(k_grid[np.minimum(n_k - 1, j_best + 1)], y_max_row * (1.0 - 1e-12)),
        )

        x1 = hi - inv_phi * (hi - lo)
        x2 = lo + inv_phi * (hi - lo)
        _, u1 = solve_L_vec(k_grid, x1)
        _, u2 = solve_L_vec(k_grid, x2)
        f1 = u1 + beta * iv_endo(x1)
        f2 = u2 + beta * iv_endo(x2)
        for _g in range(20):
            mr = f1 < f2
            lo = np.where(mr, x1, lo)
            hi = np.where(mr, hi, x2)
            x1_n = np.where(mr, x2, hi - inv_phi * (hi - lo))
            x2_n = np.where(mr, lo + inv_phi * (hi - lo), x1)
            _, u1_n = solve_L_vec(k_grid, x1_n)
            _, u2_n = solve_L_vec(k_grid, x2_n)
            f1_n = np.where(mr, f2, u1_n + beta * iv_endo(x1_n))
            f2_n = np.where(mr, u2_n + beta * iv_endo(x2_n), f1)
            x1, x2, f1, f2 = x1_n, x2_n, f1_n, f2_n
        pol_endo = np.where(f1 > f2, x1, x2)
        _, u_pol_e = solve_L_vec(k_grid, pol_endo)
        V_eval = np.maximum(f1, f2)
        for _h in range(120):
            Ve_n = u_pol_e + beta * make_interp_V(V_eval)(pol_endo)
            if np.max(np.abs(Ve_n - V_eval)) < 1e-11:
                V_eval = Ve_n
                break
            V_eval = Ve_n
        if np.max(np.abs(V_eval - V_endo)) < 1e-10:
            V_endo = V_eval
            break
        V_endo = V_eval

    diff_endo = pol_endo - k_grid
    jump_e = np.where(diff_endo[idx_m] > 0)[0][0]
    k_S_endo = refine_skiba(idx_m[jump_e], V_endo, endo=True)

    idx_hi_f = idx_m[jump]
    idx_hi = idx_m[jump_e]
    pc_rf = PchipInterpolator(log_k_grid[idx_hi_f:], V_fix[idx_hi_f:], extrapolate=True)
    pc_re = PchipInterpolator(log_k_grid[idx_hi:], V_endo[idx_hi:], extrapolate=True)
    iv_fix_right = lambda kp: pc_rf(np.log(np.maximum(kp, k_lo)))
    iv_endo_right = lambda kp: pc_re(np.log(np.maximum(kp, k_lo)))

    def opt_right_step_fix(k_pt: float, force_right: bool = False) -> Tuple[float, float]:
        y_p = q * k_pt + float(f_norm(k_pt, 1.0))
        lo_c = k_pt * (1.0 + 1e-12) if force_right else k_grid[idx_hi_f]
        hi_c = min(y_p * (1.0 - 1e-12), k_hi)
        if lo_c >= hi_c:
            lo_c = min(k_lo, 0.5 * hi_c)
        parts = [
            k_grid[(k_grid > lo_c) & (k_grid < hi_c)],
            y_p * (1.0 - np.geomspace(1e-5, 0.25, 36)),
        ]
        if force_right and hi_c > lo_c * 1.001:
            parts.append(np.geomspace(lo_c, min(hi_c, max(lo_c * 1.05, min(hi_c, 2.0 * k_pt))), 32))
        cands = np.unique(np.concatenate(parts))
        cands = cands[(cands > lo_c) & (cands < hi_c)]
        if len(cands) == 0:
            cands = np.linspace(lo_c, hi_c, 16)
        vals = eta * np.log(np.maximum(y_p - cands, 1e-30 * max(1.0, y_p))) + beta * iv_fix_right(cands)
        ib = int(np.argmax(vals))
        lo_r = float(cands[max(0, ib - 1)])
        hi_r = float(cands[min(len(cands) - 1, ib + 1)])
        for _ in range(30):
            m1 = hi_r - inv_phi * (hi_r - lo_r)
            m2 = lo_r + inv_phi * (hi_r - lo_r)
            v1r = float(eta * np.log(max(y_p - m1, 1e-30 * max(1.0, y_p))) + beta * iv_fix_right(np.array([m1]))[0])
            v2r = float(eta * np.log(max(y_p - m2, 1e-30 * max(1.0, y_p))) + beta * iv_fix_right(np.array([m2]))[0])
            if v1r < v2r:
                lo_r = m1
            else:
                hi_r = m2
        kp_b = float(0.5 * (lo_r + hi_r))
        val_b = float(eta * np.log(max(y_p - kp_b, 1e-30 * max(1.0, y_p))) + beta * iv_fix_right(np.array([kp_b]))[0])
        return kp_b, val_b

    def opt_right_step_endo(k_pt: float, force_right: bool = False) -> Tuple[float, float]:
        y_p = q * k_pt + float(f_norm(k_pt, 1.0))
        lo_c = k_pt * (1.0 + 1e-12) if force_right else k_grid[idx_hi]
        hi_c = min(y_p * (1.0 - 1e-12), k_hi)
        if lo_c >= hi_c:
            lo_c = min(k_lo, 0.5 * hi_c)
        parts = [
            k_grid[(k_grid > lo_c) & (k_grid < hi_c)],
            y_p * (1.0 - np.geomspace(1e-5, 0.25, 36)),
        ]
        if force_right and hi_c > lo_c * 1.001:
            parts.append(np.geomspace(lo_c, min(hi_c, max(lo_c * 1.05, min(hi_c, 2.0 * k_pt))), 32))
        cands = np.unique(np.concatenate(parts))
        cands = cands[(cands > lo_c) & (cands < hi_c)]
        if len(cands) == 0:
            cands = np.linspace(lo_c, hi_c, 16)
        _, us = solve_L_vec(np.full_like(cands, k_pt), cands)
        vals = us + beta * iv_endo_right(cands)
        ib = int(np.argmax(vals))
        lo_r = float(cands[max(0, ib - 1)])
        hi_r = float(cands[min(len(cands) - 1, ib + 1)])
        for _ in range(30):
            m1 = hi_r - inv_phi * (hi_r - lo_r)
            m2 = lo_r + inv_phi * (hi_r - lo_r)
            _, u1r = solve_L_vec(np.array([k_pt, k_pt]), np.array([m1, m2]))
            v1r = float(u1r[0] + beta * iv_endo_right(np.array([m1]))[0])
            v2r = float(u1r[1] + beta * iv_endo_right(np.array([m2]))[0])
            if v1r < v2r:
                lo_r = m1
            else:
                hi_r = m2
        kp_b = float(0.5 * (lo_r + hi_r))
        _, ub_ = solve_L_vec(np.array([k_pt]), np.array([kp_b]))
        val_b = float(ub_[0] + beta * iv_endo_right(np.array([kp_b]))[0])
        return kp_b, val_b

    _, V_fix_RHS = opt_right_step_fix(float(k_S_endo), force_right=True)
    _, V_endo_RHS = opt_right_step_endo(float(k_S_endo), force_right=True)

    # Initial VFI policy rollout over t = 0..219 for pi^+ and pi_fix
    N_HOR = 220
    k_seq_endo = np.zeros(N_HOR + 1, dtype=np.float64)
    k_seq_endo[0] = float(k_S_endo)
    for t in range(N_HOR):
        kp_e, _ = opt_right_step_endo(float(k_seq_endo[t]), force_right=(t == 0))
        k_seq_endo[t + 1] = kp_e

    # Coordinate-ascent Euler refinement on k_seq_endo[1..N_HOR-1]
    for _sw in range(6):
        max_rel = 0.0
        for t in range(1, N_HOR):
            km, k_now, kp = float(k_seq_endo[t - 1]), float(k_seq_endo[t]), float(k_seq_endo[t + 1])
            ym = q * km + float(f_norm(km, 1.0))
            hi_b = min(ym * (1.0 - 1e-12), k_hi, 1.25 * k_now)
            lo_b = max(k_lo, 0.78 * k_now)
            if t == 1:
                lo_b = max(lo_b, km * (1.0 + 1e-12))
            if hi_b <= lo_b * (1.0 + 1e-12):
                continue
            grid_c = np.unique(np.concatenate([np.linspace(lo_b, hi_b, 9), [k_now]]))
            _, u_prev = solve_L_vec(np.full_like(grid_c, km), grid_c)
            _, u_next = solve_L_vec(grid_c, np.full_like(grid_c, kp))
            obj_c = u_prev + beta * u_next
            ib = int(np.argmax(obj_c))
            lo_g = float(grid_c[max(0, ib - 1)])
            hi_g = float(grid_c[min(len(grid_c) - 1, ib + 1)])
            for _g in range(16):
                m1 = hi_g - inv_phi * (hi_g - lo_g)
                m2 = lo_g + inv_phi * (hi_g - lo_g)
                _, up12 = solve_L_vec(np.array([km, km]), np.array([m1, m2]))
                _, un12 = solve_L_vec(np.array([m1, m2]), np.array([kp, kp]))
                if float(up12[0] + beta * un12[0]) < float(up12[1] + beta * un12[1]):
                    lo_g = m1
                else:
                    hi_g = m2
            k_best = 0.5 * (lo_g + hi_g)
            _, upb = solve_L_vec(np.array([km]), np.array([k_best]))
            _, unb = solve_L_vec(np.array([k_best]), np.array([kp]))
            if float(upb[0] + beta * unb[0]) > float(obj_c[grid_c == k_now][0]):
                max_rel = max(max_rel, abs(k_best - k_now) / max(k_now, 1e-30))
                k_seq_endo[t] = k_best
        if max_rel < 1e-8:
            break

    # Rollout pi_fix and warm-start against refined k_seq_endo if higher J_fix
    k_seq_fix = np.zeros(N_HOR + 1, dtype=np.float64)
    k_seq_fix[0] = float(k_S_endo)
    for t in range(N_HOR):
        kp_f, _ = opt_right_step_fix(float(k_seq_fix[t]), force_right=(t == 0))
        k_seq_fix[t + 1] = kp_f

    def _eval_fix_tail(k_arr: np.ndarray) -> float:
        j_val = 0.0
        for tt in range(N_HOR):
            ct = q * k_arr[tt] + float(f_norm(k_arr[tt], 1.0)) - k_arr[tt + 1]
            if ct <= 0.0:
                return -1e12
            j_val += (beta ** tt) * eta * math.log(ct)
        c_ss_t = float(f_norm(k_arr[N_HOR], 1.0) - delta * k_arr[N_HOR])
        return j_val + (beta ** N_HOR) / (1.0 - beta) * eta * math.log(max(c_ss_t, 1e-30))

    if _eval_fix_tail(k_seq_endo) > _eval_fix_tail(k_seq_fix):
        k_seq_fix = k_seq_endo.copy()

    # Exact 40-sweep Euler coordinate ascent on k_seq_fix[1..N_HOR-1] (pure math, <0.2s)
    for _sw in range(40):
        max_rel_f = 0.0
        for t in range(1, N_HOR):
            km, k_now, kp = float(k_seq_fix[t - 1]), float(k_seq_fix[t]), float(k_seq_fix[t + 1])
            ym = q * km + float(f_norm(km, 1.0))
            hi_b = min(ym * (1.0 - 1e-12), k_hi, 1.30 * k_now)
            lo_b = max(k_lo, 0.72 * k_now)
            if t == 1:
                lo_b = max(lo_b, km * (1.0 + 1e-12))
            if hi_b <= lo_b * (1.0 + 1e-12):
                continue
            def _f2(kt: float) -> float:
                c1 = ym - kt
                c2 = q * kt + float(f_norm(kt, 1.0)) - kp
                if c1 <= 0.0 or c2 <= 0.0:
                    return -1e12
                return eta * math.log(c1) + beta * eta * math.log(c2)
            base_v = _f2(k_now)
            grid_f = np.unique(np.concatenate([np.linspace(lo_b, hi_b, 9), [k_now]]))
            vals_f = [_f2(float(gv)) for gv in grid_f]
            ib = int(np.argmax(vals_f))
            lo_g, hi_g = float(grid_f[max(0, ib - 1)]), float(grid_f[min(len(grid_f) - 1, ib + 1)])
            for _g in range(22):
                m1 = hi_g - inv_phi * (hi_g - lo_g)
                m2 = lo_g + inv_phi * (hi_g - lo_g)
                if _f2(m1) < _f2(m2):
                    lo_g = m1
                else:
                    hi_g = m2
            k_best = 0.5 * (lo_g + hi_g)
            if _f2(k_best) > base_v:
                max_rel_f = max(max_rel_f, abs(k_best - k_now) / max(k_now, 1e-30))
                k_seq_fix[t] = k_best
        if max_rel_f < 1e-10:
            break

    s_fix = pol_fix / y_fix
    J_fix_opt = 0.0
    k_cur_f = float(k_S_endo)
    for t in range(1100):
        kp_f = float(k_seq_fix[t + 1]) if t < N_HOR else float(
            np.interp(np.log(k_cur_f), log_k_grid[idx_hi_f:], s_fix[idx_hi_f:])
            * (q * k_cur_f + float(f_norm(k_cur_f, 1.0)))
        )
        c_f = q * k_cur_f + float(f_norm(k_cur_f, 1.0)) - kp_f
        J_fix_opt += (beta ** t) * eta * np.log(max(c_f, 1e-30))
        k_cur_f = kp_f

    s_endo = pol_endo / y_max_row
    k_cur = float(k_S_endo)
    J_fix_pi = 0.0
    J_endo_pi = 0.0
    T_esc = None
    L_ss_obs = None
    for t in range(1100):
        kp = float(k_seq_endo[t + 1]) if t < N_HOR else float(
            np.interp(np.log(k_cur), log_k_grid[idx_hi:], s_endo[idx_hi:])
            * (q * k_cur + float(f_norm(k_cur, 1.0)))
        )
        L_opt, u_et = solve_L_vec(np.array([k_cur]), np.array([kp]))
        c_ft = q * k_cur + float(f_norm(k_cur, 1.0)) - kp
        J_fix_pi += (beta ** t) * eta * np.log(max(c_ft, 1e-30))
        J_endo_pi += (beta ** t) * float(u_et[0])
        if T_esc is None and (k_cur / (A_val ** 2)) >= 0.01:
            T_esc = t
        k_cur = kp
        L_ss_obs = float(L_opt[0])

    assert abs(J_fix_opt - V_fix_RHS) < 0.05, f"J_fix_opt vs V_fix_RHS: {J_fix_opt} vs {V_fix_RHS}"
    assert abs(J_endo_pi - V_endo_RHS) < 0.05, f"J_endo_pi vs V_endo_RHS: {J_endo_pi} vs {V_endo_RHS}"
    V_fix_at_S = float(J_fix_opt)
    V_endo_at_S = float(J_endo_pi)
    dW_plus = V_fix_at_S - V_endo_at_S
    dW_pi_plus = float(J_fix_pi - J_endo_pi)

    if return_policy:
        return k_S_fix, k_S_endo, dW_plus, dW_pi_plus, T_esc, L_ss_obs, J_endo_pi, V_endo_at_S, pol_endo, k_grid, solve_L_vec, f_norm
    return k_S_fix, k_S_endo, dW_plus, dW_pi_plus, T_esc, L_ss_obs, J_endo_pi, V_endo_at_S


def verify_section4_theorem3_star():
    print("\n" + "=" * 72)
    print("3. SECTION 4: THEOREM 3*, COROLLARY 2* & TABLE 3 (LOG-K VFI TO A=1e8)")
    print("=" * 72)

    theta, rho, w, delta, beta, eta = 1.5, -1.0, 0.5, 0.08, 0.97, 0.70
    nu = (1.0 - eta) / eta
    c_K = w ** (theta / rho)
    L_ss_exact = (theta * eta) / (theta * eta + (1.0 - eta))  # 7/9 = 0.777778
    k_b, c_b = 0.002, 0.0001

    print(f"  Limit (delta/c_K)^2 = {(delta / c_K)**2:.6f}, beta*theta = {beta*theta:.4f} > 1, L_ss = {L_ss_exact:.6f} (7/9)")
    print("  A         kappa_A      A^2*kappa   A*L*     Gap_FA   A^2*S_fix  A^2*S_endo  Ratio(VFI)  dW_pi+   dW+     T_esc  L_ss")
    prev_ratio = 2.0
    prev_dWp = 1e9
    rows = []
    for A_val in [0.75, 1.50, 3.00, 10.0, 30.0, 100.0, 1000.0, 1e6, 1e8]:
        kap = exact_kappa(A_val, delta)
        K_v = k_b / (A_val ** 2)
        C_v = c_b / (A_val ** 2)
        L_s = brentq(lambda L: dF_dL(A_val, K_v, L) - nu * C_v / (1.0 - L), K_v / 3.0, 1.0 - 1e-12)
        gap_FA = (c_K * (k_b ** 1.5) - (A_val ** 2) * F_A(A_val, K_v, L_s)) / (c_K * (k_b ** 1.5))
        kS_fix, kS_endo, dWp, dW_pip, T_esc, L_ss_obs, J_endo_pi, V_endo_S = solve_vfi_frontiers(A_val)
        ratio = kS_endo / kS_fix
        A_lbl = f"{A_val:8.2f}" if A_val <= 1000.0 else f"{A_val:8.1e}"
        print(
            f"  {A_lbl}  {kap:10.3e}  {A_val**2*kap:9.6f}  {A_val*L_s:8.5f}  "
            f"{100*gap_FA:6.3f}%  {kS_fix:9.6f}  {kS_endo:10.6f}  {ratio:10.5f}  "
            f"{dW_pip:6.3f}  {dWp:6.3f}  {T_esc:4d}  {L_ss_obs:.4f}"
        )
        assert kS_fix < kS_endo
        assert 0.0 < dW_pip <= dWp + 1e-4, f"Contradiction dW_pi+ > dW+ at A={A_val}: {dW_pip} vs {dWp}"
        assert abs(J_endo_pi - V_endo_S) < 5e-3, f"J_endo(pi+) mismatch at A={A_val}: {J_endo_pi} vs {V_endo_S}"
        assert dWp < prev_dWp, f"dW+ not decreasing at A={A_val}"
        if A_val >= 1000.0:
            assert abs(L_ss_obs - L_ss_exact) < 1e-3, f"L_ss mismatch at A={A_val}: {L_ss_obs}"
        if A_val <= 1000.0:
            assert ratio < prev_ratio
        prev_ratio = ratio
        prev_dWp = dWp
        rows.append((A_val, kap, L_s, gap_FA, kS_fix, kS_endo, ratio, dW_pip, dWp, T_esc, L_ss_obs))

    assert kS_fix < 0.000836 and kS_endo < 0.000837 and abs(ratio - 1.0) < 0.002

    # Weak patience check: beta = 0.90 (beta*(q+theta*delta) = 0.936 < 1 < beta*theta = 1.35)
    beta_wk = 0.90
    D_wk = 1.0 / beta_wk - (1.0 - delta)
    print(f"\n  [Corollary 2* Weak Patience: beta={beta_wk:.2f}, beta*theta={beta_wk*theta:.2f} > 1, (D/c_K)^2={(D_wk/c_K)**2:.6f}]")
    prev_fix_wk = 1.0
    prev_rat_wk = 2.0
    for A_val in [1.5, 100.0, 1e8]:
        kSf_wk, kSe_wk, dWp_wk, dW_pip_wk, _, _, _, _ = solve_vfi_frontiers(A_val, beta=beta_wk, k_band=(0.0014, 0.0026))
        rat_wk = kSe_wk / kSf_wk
        print(f"    A={A_val:8.1e}: A^2*S_fix={kSf_wk:.6f}, A^2*S_endo={kSe_wk:.6f}, ratio={rat_wk:.5f}, dW_pi+={dW_pip_wk:.3f}, dW+={dWp_wk:.3f}")
        assert kSf_wk < kSe_wk < (D_wk / c_K) ** 2
        assert 0.0 < dW_pip_wk <= dWp_wk + 5e-4
        assert kSf_wk < prev_fix_wk and rat_wk < prev_rat_wk
        prev_fix_wk, prev_rat_wk = kSf_wk, rat_wk
    assert kSe_wk < 0.00180 and rat_wk < 1.005

    # Harmonic rate check: dW_minus = O(A^{-1}) vs beta^{T_esc(A)}
    print("\n  [Harmonic Scaling: beta^{T_esc(A)} vs O(A^{-1})]")
    for A_val, _, _, _, _, _, _, dW_pip, dWp, T_esc, _ in rows:
        if A_val in (1.0, 1.5, 10.0, 100.0, 1000.0, 1e6, 1e8):
            print(f"    A={A_val:8.1e}: T_esc={T_esc:3d}, beta^T_esc={beta**T_esc:.5f}, A^-1={A_val**-1:.1e}, (beta^T_esc)*A={(beta**T_esc)*A_val:.2f}")
    return rows


# ---------------------------------------------------------------------------
# 4. Section 5: Stochastic VFI (Continuous Golden-Section Ruin & Markov)
# ---------------------------------------------------------------------------
def verify_section5_stochastic_vfi():
    """
    Port of Section 5 forward-looking Stochastic VFI (Ruin vs Persistent
    Markov Recession, Table 5 & p_rec sensitivity at p=8%), highlighting the
    economic dichotomy: investment contraction & rising S^ruin(p) under ruin
    vs 'flight to safety' (rising K'_G, L_G) under recoverable recession.
    """
    print("\n" + "=" * 72)
    print("4. SECTION 5: STOCHASTIC VFI (RUIN VS PERSISTENT MARKOV RECESSION)")
    print("=" * 72)

    theta, rho, w, delta, beta, eta = 1.5, -1.0, 0.5, 0.08, 0.97, 0.70
    q = 1.0 - delta
    A_G, A_B = 0.75, 0.35
    r_rec = P_REC
    inv_phi = (np.sqrt(5.0) - 1.0) / 2.0

    K_ss = brentq(lambda K: dF_dK(A_G, K, 1.0) - (1.0 / beta - q), 0.25, 25.0)
    k_lo, k_hi = 1e-5 / (A_G ** 2), 1.15 * K_ss
    k_grid = np.unique(np.concatenate([
        np.geomspace(k_lo, 0.00138, 130, endpoint=False),
        np.linspace(0.00138, 0.00650, 320, endpoint=False),
        np.geomspace(0.00650, 0.08, 110, endpoint=False),
        np.linspace(0.08, 0.34, 160, endpoint=False),
        np.geomspace(0.34, k_hi, 160),
    ]))
    n_k = len(k_grid)
    L_grid = np.unique(np.concatenate([np.geomspace(1e-4, 0.08, 24, endpoint=False), np.linspace(0.08, 0.995, 64)]))
    dis_L = (1.0 - eta) * np.log(1.0 - L_grid[None, :])

    def build_u_bench(A_v: float):
        y_kL = q * k_grid[:, None] + F_A(A_v, k_grid[:, None], L_grid[None, :])
        um = np.full((n_k, n_k), -1e9)
        for i in range(n_k):
            cm = y_kL[i, None, :] - k_grid[:, None]
            u = np.where(cm > 1e-15, eta * np.log(np.maximum(cm, 1e-30)) + dis_L, -1e9)
            um[i, :] = np.max(u, axis=1)
        return um, y_kL

    u_G, y_kL_G = build_u_bench(A_G)
    u_B, y_kL_B = build_u_bench(A_B)

    def solve_L_p(k_arr, kp_arr, A_v: float = A_G):
        return _golden_solve_L(k_arr, kp_arr, lambda k, L: F_A(A_v, k, L), q, eta)

    s_cand = 1.0 - np.geomspace(1e-5, 0.15, 22)
    kp_tail_G = y_kL_G[:, -1][:, None] * s_cand[None, :]
    kp_tail_B = y_kL_B[:, -1][:, None] * s_cand[None, :]
    u_tail_G = np.full((n_k, len(s_cand)), -1e9)
    u_tail_B = np.full((n_k, len(s_cand)), -1e9)
    for j in range(len(s_cand)):
        _, u_tail_G[:, j] = solve_L_p(k_grid, kp_tail_G[:, j], A_G)
        _, u_tail_B[:, j] = solve_L_p(k_grid, kp_tail_B[:, j], A_B)

    def interp_Vs(V, kp, b_eff):
        r = np.interp(np.clip(kp, k_lo, k_hi), k_grid, V)
        return np.where(kp < k_lo, V[0] + (eta / (1.0 - b_eff)) * np.log(np.maximum(kp, 1e-30) / k_lo), r)

    def refine_skiba_state(pol_arr, V_cont, A_v: float, b_eff: float) -> float:
        idx_m = np.where((k_grid >= 0.00138) & (k_grid <= 0.0065))[0]
        i0 = idx_m[np.where((pol_arr - k_grid)[idx_m] > 0)[0][0]]
        k_sub = np.linspace(k_grid[i0 - 1], k_grid[i0], 25)
        diffs = []
        for ks in k_sub:
            ys = q * ks + F_A(A_v, ks, 1.0)
            kd = np.linspace(max(1e-5, 0.90 * ks), ks, 30)
            _, ud = solve_L_p(np.full_like(kd, ks), kd, A_v)
            vd = np.max(ud + b_eff * interp_Vs(V_cont, kd, b_eff))
            if ys > ks + 1e-12:
                ku = np.linspace(ks, ys - 1e-12, 30)
                _, uu = solve_L_p(np.full_like(ku, ks), ku, A_v)
                vu = np.max(uu + b_eff * interp_Vs(V_cont, ku, b_eff))
            else:
                vu = -1e9
            diffs.append(vu - vd)
        pos = np.where(np.array(diffs) >= 0)[0]
        if len(pos) > 0 and pos[0] > 0:
            return float(
                k_sub[pos[0] - 1]
                + abs(diffs[pos[0] - 1]) / (abs(diffs[pos[0] - 1]) + abs(diffs[pos[0]])) * (k_sub[pos[0]] - k_sub[pos[0] - 1])
            )
        return float(0.5 * (k_grid[i0 - 1] + k_grid[i0]))

    def smooth_policy_at(K_val: float, EV_arr, A_v: float, b_eff: float):
        pchip = PchipInterpolator(k_grid, EV_arr)
        Ls = np.linspace(0.30, 0.95, 300)
        Y_L = q * K_val + F_A(A_v, K_val, Ls)
        dL = (1.0 - eta) * np.log(1.0 - Ls)
        kps = np.linspace(max(1e-4, 0.9 * K_val), np.max(Y_L) - 1e-6, 350)
        cm = Y_L[:, None] - kps[None, :]
        rhs = np.where(cm > 1e-12, eta * np.log(np.maximum(cm, 1e-30)) + dL[:, None] + b_eff * pchip(kps)[None, :], -1e9)
        il, ik = np.unravel_index(np.argmax(rhs), rhs.shape)
        dk = kps[1] - kps[0]
        kp0 = kps[ik]
        kps_f = np.linspace(max(1e-4, kp0 - 2 * dk), min(np.max(Y_L) - 1e-7, kp0 + 2 * dk), 200)
        Ls_f = np.linspace(max(0.01, Ls[il] - 0.03), min(0.998, Ls[il] + 0.03), 200)
        Yf = q * K_val + F_A(A_v, K_val, Ls_f)
        dLf = (1.0 - eta) * np.log(1.0 - Ls_f)
        cm_f = Yf[:, None] - kps_f[None, :]
        rhs_f = np.where(cm_f > 1e-12, eta * np.log(np.maximum(cm_f, 1e-30)) + dLf[:, None] + b_eff * pchip(kps_f)[None, :], -1e9)
        il2, ik2 = np.unravel_index(np.argmax(rhs_f), rhs_f.shape)
        return float(kps_f[ik2]), float(Ls_f[il2]), float(Yf[il2])

    V_ss_est = eta * np.log(F_A(A_G, K_ss, 0.7) - delta * K_ss)

    def solve_cont_markov_vfi(p_val: float, r_rec_val: float):
        Vc0 = (eta / (1.0 - beta)) * (np.log((1.0 - beta) * q) + (beta / (1.0 - beta)) * np.log(beta * q))
        VG = np.where(k_grid > 0.00145, V_ss_est / (1.0 - beta), Vc0 + (eta / (1.0 - beta)) * np.log(k_grid))
        VB = VG.copy() - 5.0
        ym_G, ym_B = y_kL_G[:, -1], y_kL_B[:, -1]
        for _ in range(55):
            EVG = (1.0 - p_val) * VG + p_val * VB
            EVB = r_rec_val * VG + (1.0 - r_rec_val) * VB
            pols, ups = [], []
            for uM, EV, Av, ym, kpt, ut in [
                (u_G, EVG, A_G, ym_G, kp_tail_G, u_tail_G),
                (u_B, EVB, A_B, ym_B, kp_tail_B, u_tail_B),
            ]:
                vg = uM + beta * EV[None, :]
                jb = np.argmax(vg, axis=1)
                bg = vg[np.arange(n_k), jb]
                vt = ut + beta * interp_Vs(EV, kpt, beta)
                sb = np.argmax(vt, axis=1)
                bt = vt[np.arange(n_k), sb]
                uset = bt > bg
                lot = kpt[np.arange(n_k), np.maximum(0, sb - 1)]
                hit = kpt[np.arange(n_k), np.minimum(len(s_cand) - 1, sb + 1)]
                lo = np.where(uset, np.minimum(lot, hit), k_grid[np.maximum(0, jb - 1)])
                hi = np.where(uset, np.minimum(np.maximum(lot, hit), ym - 1e-12), np.minimum(k_grid[np.minimum(n_k - 1, jb + 1)], ym - 1e-12))
                x1 = hi - inv_phi * (hi - lo)
                x2 = lo + inv_phi * (hi - lo)
                _, u1 = solve_L_p(k_grid, x1, Av)
                _, u2 = solve_L_p(k_grid, x2, Av)
                f1 = u1 + beta * interp_Vs(EV, x1, beta)
                f2 = u2 + beta * interp_Vs(EV, x2, beta)
                for _g in range(12):
                    mr = f1 < f2
                    lo = np.where(mr, x1, lo)
                    hi = np.where(mr, hi, x2)
                    x1n = np.where(mr, x2, hi - inv_phi * (hi - lo))
                    x2n = np.where(mr, lo + inv_phi * (hi - lo), x1)
                    _, u1n = solve_L_p(k_grid, x1n, Av)
                    _, u2n = solve_L_p(k_grid, x2n, Av)
                    f1n = np.where(mr, f2, u1n + beta * interp_Vs(EV, x1n, beta))
                    f2n = np.where(mr, u2n + beta * interp_Vs(EV, x2n, beta), f1)
                    x1, x2, f1, f2 = x1n, x2n, f1n, f2n
                pol = np.where(f1 > f2, x1, x2)
                _, up = solve_L_p(k_grid, pol, Av)
                pols.append(pol)
                ups.append(up)
            polG, polB = pols
            upG, upB = ups
            VGe, VBe = VG.copy(), VB.copy()
            for _h in range(100):
                EVGe = (1.0 - p_val) * VGe + p_val * VBe
                EVBe = r_rec_val * VGe + (1.0 - r_rec_val) * VBe
                VGn = upG + beta * interp_Vs(EVGe, polG, beta)
                VBn = upB + beta * interp_Vs(EVBe, polB, beta)
                if max(np.max(np.abs(VGn - VGe)), np.max(np.abs(VBn - VBe))) < 1e-9:
                    VGe, VBe = VGn, VBn
                    break
                VGe, VBe = VGn, VBn
            if max(np.max(np.abs(VGe - VG)), np.max(np.abs(VBe - VB))) < 1e-8:
                VG, VB = VGe, VBe
                break
            VG, VB = VGe, VBe
        EVG = (1.0 - p_val) * VG + p_val * VB
        kp_m, L_m, _ = smooth_policy_at(B_M, EVG, A_G, beta)
        S_G = refine_skiba_state(polG, EVG, A_G, beta)
        idx_sk = np.where((k_grid >= 0.00138) & (k_grid <= 0.005))[0]
        j_kink = idx_sk[int(np.argmax(np.diff(polB[idx_sk] / k_grid[idx_sk])))]
        S_Bkink = float(0.5 * (k_grid[j_kink] + k_grid[j_kink + 1]))
        idx_kb = np.where((k_grid >= 0.005) & (k_grid <= 0.03))[0]
        j_kb = idx_kb[np.where((polB - k_grid)[idx_kb] > 0)[0][0]]
        KB_star = float(0.5 * (k_grid[j_kb - 1] + k_grid[j_kb]))
        return S_G, S_Bkink, KB_star, kp_m, L_m

    p_tests = [0.0, 0.005, 0.010, 0.015, 0.020, 0.050, 0.080]
    ruin_S, ruin_kp, ruin_L = [], [], []
    markov_SG, markov_SBk, markov_KBs, markov_kp, markov_L = [], [], [], [], []
    y_max_row = y_kL_G[:, -1]
    pbar_vfi = ProgressBar("Sec. 5 | VFI Estocastica + p_rec", len(p_tests) + 3, min_interval_sec=0.5)

    for p in p_tests:
        b_eff = beta * (1.0 - p)
        Vc = (eta / (1.0 - b_eff)) * (np.log((1.0 - b_eff) * q) + (b_eff / (1.0 - b_eff)) * np.log(b_eff * q))
        V = np.where(k_grid > 0.00145, V_ss_est / (1.0 - b_eff), Vc + (eta / (1.0 - b_eff)) * np.log(k_grid))
        for _ in range(55):
            vg = u_G + b_eff * V[None, :]
            jb = np.argmax(vg, axis=1)
            bg = vg[np.arange(n_k), jb]
            vt = u_tail_G + b_eff * interp_Vs(V, kp_tail_G, b_eff)
            sb = np.argmax(vt, axis=1)
            bt = vt[np.arange(n_k), sb]
            ut = bt > bg
            lo_t = kp_tail_G[np.arange(n_k), np.maximum(0, sb - 1)]
            hi_t = kp_tail_G[np.arange(n_k), np.minimum(len(s_cand) - 1, sb + 1)]
            lo = np.where(ut, np.minimum(lo_t, hi_t), k_grid[np.maximum(0, jb - 1)])
            hi = np.where(ut, np.minimum(np.maximum(lo_t, hi_t), y_max_row - 1e-12), np.minimum(k_grid[np.minimum(n_k - 1, jb + 1)], y_max_row - 1e-12))
            x1 = hi - inv_phi * (hi - lo)
            x2 = lo + inv_phi * (hi - lo)
            _, u1 = solve_L_p(k_grid, x1)
            _, u2 = solve_L_p(k_grid, x2)
            f1 = u1 + b_eff * interp_Vs(V, x1, b_eff)
            f2 = u2 + b_eff * interp_Vs(V, x2, b_eff)
            for _g in range(12):
                mr = f1 < f2
                lo = np.where(mr, x1, lo)
                hi = np.where(mr, hi, x2)
                x1n = np.where(mr, x2, hi - inv_phi * (hi - lo))
                x2n = np.where(mr, lo + inv_phi * (hi - lo), x1)
                _, u1n = solve_L_p(k_grid, x1n)
                _, u2n = solve_L_p(k_grid, x2n)
                f1n = np.where(mr, f2, u1n + b_eff * interp_Vs(V, x1n, b_eff))
                f2n = np.where(mr, u2n + b_eff * interp_Vs(V, x2n, b_eff), f1)
                x1, x2, f1, f2 = x1n, x2n, f1n, f2n
            pol = np.where(f1 > f2, x1, x2)
            _, upol = solve_L_p(k_grid, pol)
            Ve = np.maximum(f1, f2)
            for _h in range(60):
                Vn = upol + b_eff * interp_Vs(Ve, pol, b_eff)
                if np.max(np.abs(Vn - Ve)) < 1e-9:
                    Ve = Vn
                    break
                Ve = Vn
            if np.max(np.abs(Ve - V)) < 1e-8:
                V = Ve
                break
            V = Ve
        kS = refine_skiba_state(pol, V, A_G, b_eff)
        kp_r, L_r, _ = smooth_policy_at(B_M, V, A_G, b_eff)
        ruin_S.append(kS)
        ruin_kp.append(kp_r)
        ruin_L.append(L_r)

        S_G, S_Bkink, KB_star, kp_m, L_m = solve_cont_markov_vfi(p, r_rec)
        markov_SG.append(S_G)
        markov_SBk.append(S_Bkink)
        markov_KBs.append(KB_star)
        markov_kp.append(kp_m)
        markov_L.append(L_m)
        print(
            f"    p={100*p:4.1f}% | Ruin: S_p={kS:.6f}, K'={kp_r:.5f}, L={L_r:.4f} | "
            f"Markov: S_G={S_G:.6f}, S_B_kink={S_Bkink:.5f}, K_B*={KB_star:.5f}, K'_G={kp_m:.5f}, L_G={L_m:.4f}"
        )
        pbar_vfi.update(1, suffix=f"p={100*p:.1f}%")

    assert abs(ruin_S[0] - markov_SG[0]) < 2e-6
    assert abs(ruin_kp[0] - markov_kp[0]) < 2e-5 and abs(ruin_L[0] - markov_L[0]) < 5e-4
    assert all(ruin_S[i] < ruin_S[i + 1] for i in range(len(p_tests) - 1))
    assert all(ruin_kp[i] > ruin_kp[i + 1] and ruin_L[i] > ruin_L[i + 1] for i in range(len(p_tests) - 1))
    assert all(markov_SG[i] <= markov_SG[i + 1] for i in range(len(p_tests) - 1))
    assert markov_SG[-1] > markov_SG[0] and markov_SBk[-1] > markov_SBk[0] and markov_KBs[-1] < markov_KBs[0]
    assert all(markov_kp[i] <= markov_kp[i + 1] and markov_L[i] <= markov_L[i + 1] for i in range(len(p_tests) - 1))
    assert markov_kp[-1] > markov_kp[0] and markov_L[-1] > markov_L[0]

    print("\n  [Recovery Sensitivity] Recovery probability p_rec sensitivity at p=8.0%:")
    rec_sens = []
    for r_val in (0.20, 1.0 / 3.0, 0.50):
        sg_r, sbk_r, kbs_r, kpm_r, lm_r = solve_cont_markov_vfi(0.08, r_val)
        rec_sens.append((r_val, sg_r, sbk_r, kbs_r, kpm_r, lm_r))
        print(f"    r_rec={r_val:.4f}: S_G={sg_r:.6f}, S_B_kink={sbk_r:.5f}, K_B*={kbs_r:.5f}, K'_G(0.10)={kpm_r:.5f}, L_G={lm_r:.4f}")
        pbar_vfi.update(1, suffix=f"r_rec={r_val:.2f}")

    return {
        "p_tests": p_tests,
        "ruin_S": ruin_S,
        "ruin_kp": ruin_kp,
        "ruin_L": ruin_L,
        "markov_SG": markov_SG,
        "markov_SBk": markov_SBk,
        "markov_KBs": markov_KBs,
        "markov_kp": markov_kp,
        "markov_L": markov_L,
        "rec_sens": rec_sens,
    }


# ---------------------------------------------------------------------------
# 5. Independent Re-Audit of Exported CEGIS-PWL Certificates
# ---------------------------------------------------------------------------
def _audit_case2_band_worker(args: tuple) -> int:
    idx_b, rec, m_G = args
    from cegis_verifier import (
        verify_staying_barrier_bb,
        verify_super_barrier_bb,
        verify_witness_subsolution_bb,
        verify_adverse_exit_bb,
        verify_witness_slope_on_M,
        verify_derivative_below_bound,
        verify_H2_global_interval,
        certify_affine_deadline_interval,
        certify_staying_deadline_interval,
    )
    blo, bhi = rec["b_min"], rec["b_max"]
    Psib = pwl_from_dict(rec["Psi_net"]); Wb = pwl_from_dict(rec["W_net"])
    kpb = pwl_from_dict(rec["kp_net"]); Lb = pwl_from_dict(rec["L_net"])
    cP = verify_super_barrier_bb(Psib, Psib, A_MAX, blo, bhi, tol=3e-4)
    cW = verify_witness_subsolution_bb(Wb, Wb, kpb, Lb, A_MIN, Q_MIN, blo, bhi, k_domain=(B_M, 5.5), tol=8e-5)
    p10 = float(iv_eval_logpwl(Psib, Interval(str(B_M))).to_float_bounds()[1])
    p28_iv = iv_eval_logpwl(Psib, Interval(str(H_M)))
    p28 = float(p28_iv.to_float_bounds()[1])
    exM = verify_adverse_exit_bb(Wb, p10, A_MAX, Q_MAX, blo, bhi, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M))
    exH = verify_adverse_exit_bb(Wb, p28, A_MAX, Q_MAX, blo, bhi, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80))
    ok_db, _, _ = verify_derivative_below_bound(Psib, B_M, blo, A_MIN, Q_MIN, B_M, 0.44)
    ok_dh, _, _ = verify_derivative_below_bound(Psib, H_M, blo, A_MIN, Q_MIN, H_M, 0.57)
    okW, _ = verify_witness_slope_on_M(Wb, m_G)
    kp80 = float(eval_logpwl(kpb, np.array([0.80]))[0])
    L80 = float(np.clip(eval_logpwl(Lb, np.array([0.80]))[0], 0.0, 0.999))
    wkp80 = float(iv_eval_logpwl(Wb, Interval(kp80)).to_float_bounds()[0])
    okH2, _ = verify_H2_global_interval(Wb, kp80, L80, wkp80, p28, A_MIN, A_MAX, Q_MIN, Q_MAX, blo, bhi)

    iv_one = Interval("1")
    iv_Cmax = Interval(str(Q_MAX)) * Interval(str(H_M)) + iv_F_A(Interval(str(A_MAX)), Interval(str(H_M)), iv_one) - Interval(str(B_M))
    iv_blo = Interval(str(blo))
    iv_D2 = (Interval(str(ETA_MIN)) * iv_blo * Interval(str(Q_MIN)) * (Interval(str(H_M)) - Interval(str(B_M)))) / iv_Cmax
    iv_Bs = (Interval("-0.996") - iv_D2) / (iv_one - iv_blo)
    iv_B1b = iv_Bs - ((Interval(str(ETA_MIN)) * Interval(str(Q_MIN))) / iv_Cmax) * (Interval(str(H_M)) - Interval(str(B_M)))
    iv_W10 = iv_eval_logpwl(Wb, Interval(str(B_M)))
    T_b1 = certify_affine_deadline_interval(iv_W10 - iv_B1b, p28_iv - iv_Bs, bhi)
    assert T_b1 == rec["metrics"]["T_star"]

    assert "B_cegis_net" in rec, f"Missing B_cegis_net on Case 2 band {idx_b}"
    B2 = pwl_from_dict(rec["B_cegis_net"])
    rB2 = verify_staying_barrier_bb(B2, b_lo=blo, b_hi=bhi, tol=2e-4)
    T_ceg, _, _ = certify_staying_deadline_interval(B2, Psib, Wb, b_max=bhi)
    assert rB2["certified"] and rB2["iv_certified"] and T_ceg == rec["metrics"]["T_star_cegis"]
    assert cP["certified"] and cP["iv_certified"] and cW["certified"] and cW["iv_certified"]
    assert exM["certified"] and exH["certified"] and ok_db and ok_dh and okW and okH2
    return idx_b


def _audit_case3_band_worker(args: tuple) -> Tuple[str, int]:
    p_key, jb, p_v, brec, C_max_G, C_max_B, R_hat_G, R_hat_B, m_G, m_B = args
    from pwl_model import make_pwl_from_knots
    from cegis_verifier import (
        verify_super_barrier_bb,
        verify_witness_subsolution_bb,
        verify_adverse_exit_bb,
        verify_witness_slope_on_M,
        verify_derivative_below_bound,
        verify_H2_global_interval,
        iv_solve_markov_B_star,
        certify_affine_deadline_interval,
        compute_doob_eps0_interval,
    )
    blo, bhi = brec["bL"], brec["bR"]
    pG = pwl_from_dict(brec["PsiG_net"]); pB = pwl_from_dict(brec["PsiB_net"])
    wG = pwl_from_dict(brec["WG_net"]); wB = pwl_from_dict(brec["WB_net"])
    kpG = pwl_from_dict(brec["kpG_net"]); LG = pwl_from_dict(brec["LG_net"])
    kpB = pwl_from_dict(brec["kpB_net"]); LB = pwl_from_dict(brec["LB_net"])

    evG = make_pwl_from_knots(pG["ks"], (1.0 - p_v) * pG["vals"] + p_v * pB["vals"], pG["s_lo"], pG["s_hi"])
    evB = make_pwl_from_knots(pG["ks"], P_REC * pG["vals"] + (1.0 - P_REC) * pB["vals"], pG["s_lo"], pG["s_hi"])
    evWG = make_pwl_from_knots(wG["ks"], (1.0 - p_v) * wG["vals"] + p_v * wB["vals"], 0.0, 0.0)
    evWB = make_pwl_from_knots(wG["ks"], P_REC * wG["vals"] + (1.0 - P_REC) * wB["vals"], 0.0, 0.0)

    cG = verify_super_barrier_bb(pG, evG, A_MAX, blo, bhi, tol=3e-4)
    cB = verify_super_barrier_bb(pB, evB, AB_MAX, blo, bhi, tol=3e-4)
    cwG = verify_witness_subsolution_bb(wG, evWG, kpG, LG, A_MIN, Q_MIN, blo, bhi, k_domain=(B_M, 5.5), tol=8e-5)
    cwB = verify_witness_subsolution_bb(wB, evWB, kpB, LB, AB_MIN, Q_MIN, blo, bhi, k_domain=(B_M, 5.5), tol=8e-5)
    okWG, _ = verify_witness_slope_on_M(wG, m_G)
    okWB, _ = verify_witness_slope_on_M(wB, m_B)

    ok_bG, _, _ = verify_derivative_below_bound(evG, B_M, blo, A_MIN, Q_MIN, B_M, 0.44)
    ok_bB, _, _ = verify_derivative_below_bound(evB, B_M, blo, AB_MIN, Q_MIN, B_M, 0.478)
    ok_hG, _, _ = verify_derivative_below_bound(evG, H_M, blo, A_MIN, Q_MIN, H_M, 0.57)
    ok_hB, _, _ = verify_derivative_below_bound(evB, H_M, blo, AB_MIN, Q_MIN, H_M, 0.603)

    psiGh_iv = iv_eval_logpwl(pG, Interval(str(H_M)))
    psiBh_iv = iv_eval_logpwl(pB, Interval(str(H_M)))
    psiGb_iv = iv_eval_logpwl(pG, Interval(str(B_M)))
    psiBb_iv = iv_eval_logpwl(pB, Interval(str(B_M)))
    iv_one = Interval("1"); iv_p = Interval(str(p_v)); iv_omp = iv_one - iv_p
    iv_prec = Interval("1") / Interval("3"); iv_omrec = Interval("2") / Interval("3")
    evGh = float((iv_omp * psiGh_iv + iv_p * psiBh_iv).to_float_bounds()[1])
    evBh = float((iv_prec * psiGh_iv + iv_omrec * psiBh_iv).to_float_bounds()[1])
    evGb = float((iv_omp * psiGb_iv + iv_p * psiBb_iv).to_float_bounds()[1])
    evBb = float((iv_prec * psiGb_iv + iv_omrec * psiBb_iv).to_float_bounds()[1])

    exMG = verify_adverse_exit_bb(wG, evGb, A_MAX, Q_MAX, blo, bhi, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M))
    exMB = verify_adverse_exit_bb(wB, evBb, AB_MAX, Q_MAX, blo, bhi, ETA_MIN, ETA_MAX, B_M, 0.478, (B_M, H_M))
    exH1G = verify_adverse_exit_bb(wG, evGh, A_MAX, Q_MAX, blo, bhi, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 0.80))

    kpG80 = float(eval_logpwl(kpG, np.array([0.80]))[0])
    LG80 = float(np.clip(eval_logpwl(LG, np.array([0.80]))[0], 0.0, 0.999))
    evWG_kp = float((iv_omp * iv_eval_logpwl(wG, Interval(kpG80)) + iv_p * iv_eval_logpwl(wB, Interval(kpG80))).to_float_bounds()[0])
    okH2G, _ = verify_H2_global_interval(wG, kpG80, LG80, evWG_kp, evGh, A_MIN, A_MAX, Q_MIN, Q_MAX, blo, bhi)

    kpB80 = float(eval_logpwl(kpB, np.array([0.80]))[0])
    LB80 = float(np.clip(eval_logpwl(LB, np.array([0.80]))[0], 0.0, 0.999))
    evWB_kp = float((iv_prec * iv_eval_logpwl(wG, Interval(kpB80)) + iv_omrec * iv_eval_logpwl(wB, Interval(kpB80))).to_float_bounds()[0])
    okH2B, _ = verify_H2_global_interval(wB, kpB80, LB80, evWB_kp, evBh, AB_MIN, AB_MAX, Q_MIN, Q_MAX, blo, bhi)

    iv_BsG, iv_BsB = iv_solve_markov_B_star(p_v, blo, bhi, R_hat_G, R_hat_B, C_max_G, C_max_B, m_G, m_B)
    iv_w = Interval(str(H_M)) - Interval(str(B_M))
    iv_WG0 = iv_eval_logpwl(wG, Interval(str(B_M))); iv_WB0 = iv_eval_logpwl(wB, Interval(str(B_M)))
    iv_BG0 = iv_BsG - Interval(str(m_G)) * iv_w; iv_BB0 = iv_BsB - Interval(str(m_B)) * iv_w
    ex_G = psiGh_iv - Interval._raw(iv_BsG.lo, iv_BsG.lo)
    ex_B = psiBh_iv - Interval._raw(iv_BsB.lo, iv_BsB.lo)
    iv_max_ex = Interval._raw(max(ex_G.lo, ex_B.lo), max(ex_G.hi, ex_B.hi))
    T_B = certify_affine_deadline_interval(iv_WB0 - iv_BB0, iv_max_ex, BETA_MAX)
    eps0 = compute_doob_eps0_interval(
        float(iv_WG0.to_float_bounds()[0]), float(iv_WB0.to_float_bounds()[0]),
        float(iv_BG0.to_float_bounds()[1]), float(iv_BB0.to_float_bounds()[1]),
        float(Interval._raw(iv_BsG.lo, iv_BsG.lo).to_float_bounds()[0]),
        float(Interval._raw(iv_BsB.lo, iv_BsB.lo).to_float_bounds()[0]),
        pG, pB, T_B + 4,
    )
    assert cG["certified"] and cG["iv_certified"] and cB["certified"] and cB["iv_certified"]
    assert cwG["certified"] and cwG["iv_certified"] and cwB["certified"] and cwB["iv_certified"]
    assert okWG and okWB and ok_bG and ok_bB and ok_hG and ok_hB
    assert exMG["certified"] and exMB["certified"] and exH1G["certified"] and okH2G and okH2B and eps0 > 0.0
    return p_key, jb


def audit_cegis_certificates(json_path: str, full_audit: bool = False):
    """Independently reload and interval-audit all 4 cases in cegis_certificates.json."""
    print("\n" + "=" * 72)
    print(f"5. INDEPENDENT INTERVAL RE-AUDIT OF cegis_certificates.json ({'FULL' if full_audit else 'SPOT-CHECK'})")
    print("=" * 72)
    from cegis_verifier import (
        verify_staying_barrier_bb,
        verify_super_barrier_bb,
        verify_witness_subsolution_bb,
        verify_adverse_exit_bb,
        verify_derivative_below_bound,
        verify_H2_global_interval,
        verify_ak_witness_tail_interval,
        certify_case1_deadline_interval,
        certify_staying_deadline_interval,
        iv_compute_R_hat_B_upper,
    )
    from pwl_model import LogReLUNetwork

    data = json.load(open(json_path, "r", encoding="utf-8"))
    assert all(k in data for k in ("case1_affine_gap", "case2_ruin_hazard", "case3_markov_h1", "case4_ak_regime")), (
        f"Missing case keys in {json_path}: {list(data.keys())}"
    )

    # Case 1
    c1 = data["case1_affine_gap"]
    B1 = LogReLUNetwork.from_dict(c1["B_net"]).extract_exact_log_pwl()
    Psi1 = pwl_from_dict(c1["Psi_net"])
    W1 = pwl_from_dict(c1["W_net"])
    rB1 = verify_staying_barrier_bb(B1, tol=2e-4)
    rP1 = verify_super_barrier_bb(Psi1, Psi1, A_MAX, BETA_MIN, BETA_MAX, tol=3e-4)
    rW1 = verify_witness_subsolution_bb(W1, W1, pwl_from_dict(c1["kp_net"]), pwl_from_dict(c1["L_net"]), A_MIN, Q_MIN, BETA_MIN, BETA_MAX, k_domain=(B_M, 5.5), tol=8e-5)
    T_b1, _, _ = certify_case1_deadline_interval(B1, None, None, use_baseline_mr=True)
    T_f1, _, _ = certify_case1_deadline_interval(B1, Psi1, W1, use_baseline_mr=False)
    iv_Cmax0 = Interval(str(Q_MAX)) * Interval("0.10") + iv_F_A(Interval(str(A_MAX)), Interval("0.10"), Interval("1")) - Interval("0.05")
    iv_slope0 = (Interval(str(ETA_MIN)) * Interval(str(Q_MIN))) / iv_Cmax0
    dPsi_M0 = iv_deriv_bounds_logpwl(Psi1, Interval._raw(Decimal("0.05"), Decimal("0.10")))
    assert rB1["certified"] and rB1["iv_certified"] and rP1["certified"] and rP1["iv_certified"] and rW1["certified"] and rW1["iv_certified"]
    assert T_b1 <= 9 and T_f1 <= 9 and dPsi_M0.lo > iv_slope0.hi
    print(f"  [Case 1] B_theta d_ub_iv={rB1['d_ub_iv']:.6f}, Psi d_ub_iv={rP1['d_ub_iv']:.6f}, min dPsi_M0={float(dPsi_M0.to_float_bounds()[0]):.2f}, T_base={T_b1}, T_full={T_f1} -> PASS")

    # Case 2
    c2 = data["case2_ruin_hazard"]
    band_items = sorted(c2.items(), key=lambda kv: kv[1]["b_min"])
    assert len(band_items) >= 40
    C_max = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    m_G = (ETA_MIN * Q_MIN) / C_max
    for _, rec in band_items:
        mt = rec["metrics"]
        assert mt["d_ub_Psi_raw"] <= 0.0 and mt["d_ub_Psi_iv"] <= 0.0 and mt["marg_stay"] > 0.0
        assert mt["exitM_lb_iv"] > 0.0 and mt["exitH1_lb_iv"] > 0.0 and mt["exitH2_lb_iv"] > 0.0
    assert band_items[0][1]["metrics"]["T_star"] <= 94
    assert band_items[0][1]["metrics"]["T_star_cegis"] <= 20
    c2_indices = list(range(len(band_items))) if full_audit else [0, len(band_items) // 2, len(band_items) - 1]
    if full_audit:
        from concurrent.futures import ProcessPoolExecutor, as_completed
        pbar_c2 = ProgressBar("Audit | Caso 2 bandas", len(c2_indices), min_interval_sec=1.0)
        n_w = min(12, os.cpu_count() or 4, len(c2_indices))
        with ProcessPoolExecutor(max_workers=n_w) as pool:
            futs = [pool.submit(_audit_case2_band_worker, (idx_b, band_items[idx_b][1], m_G)) for idx_b in c2_indices]
            for fut in as_completed(futs):
                ib = fut.result()
                pbar_c2.update(1, suffix=f"band={ib+1}/{len(c2_indices)}")
    else:
        for idx_b in c2_indices:
            _audit_case2_band_worker((idx_b, band_items[idx_b][1], m_G))
    print(f"  [Case 2] Audited {len(c2_indices)}/{len(band_items)} bands incl. B_cegis, H2, <b/<h, T* (T*_B1(2%)={band_items[0][1]['metrics']['T_star']}, T*_CEGIS(2%)={band_items[0][1]['metrics']['T_star_cegis']}) -> PASS")

    # Case 3
    c3 = data["case3_markov_h1"]
    c3_keys = sorted(c3.keys()) if full_audit else ["0.000", "0.020", "0.080", "0.120"]
    C_max_G = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    C_max_B = Q_MAX * H_M + F_A(AB_MAX, H_M, 1.0) - B_M
    m_B = (ETA_MIN * Q_MIN) / C_max_B
    R_hat_G = -0.996
    R_hat_B = iv_compute_R_hat_B_upper(AB_MAX, Q_MAX, ETA_MIN, ETA_MAX)
    c3_tasks = []
    for p_key, rec3 in sorted(c3.items()):
        mt3 = rec3["metrics"]
        assert mt3["margG"] > 0.0 and mt3["margB"] > 0.0
        assert mt3["m_M_G_iv"] > 0.0 and mt3["m_M_B_iv"] > 0.0 and mt3["m_H1_G_iv"] > 0.0
        assert mt3["mH2_G_lb_iv"] > 0.0 and mt3["mH2_B_lb_iv"] > 0.0 and mt3["m_H1_B_32bx"] > 0.0
        assert mt3["eps_0_lb"] > 0.0
        if p_key in c3_keys:
            p_v = float(rec3["p"])
            bands3 = rec3.get("beta_bands", [])
            assert len(bands3) >= 8, f"Expected exported beta_bands for Case 3 p={p_key}"
            assert abs(bands3[0]["bL"] - BETA_MIN) < 1e-12 and abs(bands3[-1]["bR"] - BETA_MAX) < 1e-12
            for ii in range(len(bands3) - 1):
                assert abs(bands3[ii]["bR"] - bands3[ii + 1]["bL"]) < 1e-12
            for jb, brec in enumerate(bands3):
                c3_tasks.append((p_key, jb, p_v, brec, C_max_G, C_max_B, R_hat_G, R_hat_B, m_G, m_B))
    if full_audit:
        from concurrent.futures import ProcessPoolExecutor, as_completed
        pbar_c3 = ProgressBar("Audit | Caso 3 bandas beta", len(c3_tasks), min_interval_sec=1.0)
        n_w = min(12, os.cpu_count() or 4, len(c3_tasks))
        with ProcessPoolExecutor(max_workers=n_w) as pool:
            futs = [pool.submit(_audit_case3_band_worker, t) for t in c3_tasks]
            for fut in as_completed(futs):
                pk, jb = fut.result()
                pbar_c3.update(1, suffix=f"p={pk} jb={jb+1}")
    else:
        for t in c3_tasks:
            _audit_case3_band_worker(t)
    print(f"  [Case 3] Audited {len(c3_keys)}/{len(c3)} Markov p values ({len(c3_tasks)} contiguous beta bands + Doob eps_0) -> PASS")

    # Case 4
    c4 = data["case4_ak_regime"]
    P4 = pwl_from_dict(c4["Psi_net"]); W4 = pwl_from_dict(c4["W_net"])
    kp4 = pwl_from_dict(c4["kp_net"]); L4 = pwl_from_dict(c4["L_net"])
    B4 = pwl_from_dict(c4["B_net"]) if "B_net" in c4 else B1
    kp80_4 = float(eval_logpwl(kp4, np.array([0.80]))[0])
    L80_4 = float(np.clip(eval_logpwl(L4, np.array([0.80]))[0], 0.0, 0.999))
    wkp4 = float(iv_eval_logpwl(W4, Interval(kp80_4)).to_float_bounds()[0])
    cP4 = verify_super_barrier_bb(P4, P4, A_MAX, BETA_MIN, BETA_MAX, ak_mode=True, tol=1e-3)
    cW4 = verify_witness_subsolution_bb(W4, W4, kp4, L4, A_MIN, Q_MIN, BETA_MIN, BETA_MAX, k_domain=(B_M, 3.5), ak_mode=True, tol=8e-5)
    p10_4 = float(iv_eval_logpwl(P4, Interval(str(B_M))).to_float_bounds()[1])
    p28_4 = float(iv_eval_logpwl(P4, Interval(str(H_M))).to_float_bounds()[1])
    ok_db4, _, _ = verify_derivative_below_bound(P4, B_M, BETA_MIN, A_MIN, Q_MIN, B_M, 0.44)
    ok_dh4, _, _ = verify_derivative_below_bound(P4, H_M, BETA_MIN, A_MIN, Q_MIN, H_M, 0.57)
    exM4 = verify_adverse_exit_bb(W4, p10_4, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, B_M, 0.44, (B_M, H_M), ak_mode=False)
    exH1_4 = verify_adverse_exit_bb(W4, p28_4, A_MAX, Q_MAX, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, H_M, 0.57, (H_M, 3.5), ak_mode=True)
    okH2_4, gap35 = verify_H2_global_interval(W4, kp80_4, L80_4, wkp4, p28_4, A_MIN, A_MAX, Q_MIN, Q_MAX, BETA_MIN, BETA_MAX, ak_mode=True)
    okTail_4, res_tail_4 = verify_ak_witness_tail_interval(W4, kp4, L4, A_MIN, Q_MIN, BETA_MIN, BETA_MAX, ETA_MIN, ETA_MAX, k_tail=3.5)
    T_ak4, _, _ = certify_staying_deadline_interval(B4, P4, W4, BETA_MAX)
    assert cP4["certified"] and cP4["iv_certified"] and cW4["certified"] and cW4["iv_certified"]
    assert ok_db4 and ok_dh4 and exM4["certified"] and exM4["iv_certified"] and exH1_4["certified"] and exH1_4["iv_certified"]
    assert okH2_4 and okTail_4 and T_ak4 == c4["metrics"]["T_ak"] and T_ak4 <= 9
    print(f"  [Case 4] AK Psi(0.28)={p28_4:+.4f}, exitM={exM4['m_lb_iv']:+.4f}, exitH1={exH1_4['m_lb_iv']:+.4f}, H2_[3.5,inf)_iv={gap35:+.4f}, tail={res_tail_4:+.6f}, T_ak={T_ak4} -> PASS")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Reproducible analytical, VFI and CEGIS-PWL verifier for Article A.")
    parser.add_argument("--full-audit", action="store_true", help="Re-audit all 60 Case 2 bands and all 8 Case 3 p values (instead of spot-check).")
    parser.add_argument("--audit-only", action="store_true", help="Skip Sec. 3-5 VFI and only run JSON interval re-audit.")
    parser.add_argument("--json", type=str, default="cegis_certificates.json")
    args = parser.parse_args()

    c_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), args.json)
    cdata = json.load(open(c_path, "r", encoding="utf-8")) if os.path.exists(c_path) else None
    has_all = cdata is not None and all(k in cdata for k in ("case1_affine_gap", "case2_ruin_hazard", "case3_markov_h1", "case4_ak_regime"))
    if args.audit_only:
        assert has_all, f"All 4 cases required in {c_path} for --audit-only"
        audit_cegis_certificates(c_path, full_audit=args.full_audit)
    else:
        pbar_main = ProgressBar("verify_article_a | Suite", 6 if has_all else 5, min_interval_sec=0.0)
        verify_section3_barriers(cdata); pbar_main.update(1, suffix="Sec. 3 barreras", force=True)
        verify_restricted_M_vfi(); pbar_main.update(1, suffix="Sec. 3 M restr.", force=True)
        verify_prop1_double_star(); pbar_main.update(1, suffix="Prop. 1** + Tabla 2", force=True)
        verify_section4_theorem3_star(); pbar_main.update(1, suffix="Sec. 4 Teo. 3*", force=True)
        verify_section5_stochastic_vfi(); pbar_main.update(1, suffix="Sec. 5 VFI Estoc.", force=True)
        if has_all:
            audit_cegis_certificates(c_path, full_audit=args.full_audit); pbar_main.update(1, suffix="Auditoria JSON 1-4", force=True)
        else:
            print("\n[Note] Full JSON re-audit skipped until Cases 1-4 are all present in cegis_certificates.json.")
    print("\nPASS: All verification checks completed cleanly.")
