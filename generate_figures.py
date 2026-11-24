"""
Generate the 7 publication-quality Spanish figures for the manuscript:
  - fig1_barrier_es.{svg,png}
  - fig2_scaling_es.{svg,png}
  - fig3_stochastic_es.{svg,png}
  - fig_arch_es.{svg,png}
  - fig_nearskiba_es.{svg,png}
  - fig_markov_es.{svg,png}
  - fig_endo_policy_es.{svg,png}

Reads certified PWL objects directly from cegis_certificates.json.xz and computes
exact VFI curves via verify_all helpers (zero duplicate solvers).
"""

from __future__ import annotations

import json
import lzma
import math
import os
import sys
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from mpl_toolkits.axes_grid1.inset_locator import inset_axes

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
    box_worst_u,
)
from pwl_model import eval_logpwl, pwl_from_dict
from verify_all import (
    solve_vfi_frontiers,
    verify_section4_theorem3_star,
    verify_section5_stochastic_vfi,
)

OUT_DIR = os.path.dirname(os.path.abspath(__file__))

mpl.rcParams["font.family"] = "serif"
mpl.rcParams["mathtext.fontset"] = "cm"
mpl.rcParams["axes.linewidth"] = 0.9
mpl.rcParams["xtick.major.width"] = 0.85
mpl.rcParams["ytick.major.width"] = 0.85
mpl.rcParams["xtick.direction"] = "in"
mpl.rcParams["ytick.direction"] = "in"
mpl.rcParams["xtick.labelsize"] = 10.0
mpl.rcParams["ytick.labelsize"] = 10.0


def _save_fig(name: str) -> None:
    for ext in ("svg", "png"):
        kw = {"dpi": 300, "bbox_inches": "tight"} if ext == "png" else {"bbox_inches": "tight"}
        plt.savefig(os.path.join(OUT_DIR, f"{name}.{ext}"), **kw)
    plt.close()


def make_fig1(certs: dict) -> None:
    print("Generating fig1_barrier_es ...")
    c1 = certs["case1_affine_gap"]
    B_pwl = pwl_from_dict(c1.get("B_pwl", c1["B_net"]))
    Psi_pwl = pwl_from_dict(c1["Psi_net"])
    W_pwl = pwl_from_dict(c1["W_net"])

    C_max_plus = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    R_hat = -0.996
    Delta_2_exact = Q_MIN * ETA_MIN * BETA_MIN * (H_M - B_M) / C_max_plus
    Delta_2 = 0.2997
    assert Delta_2_exact > Delta_2
    B_0_val = R_hat / (1.0 - BETA_MIN) - Delta_2 / (1.0 - BETA_MIN ** 2)
    B_star = (R_hat - Delta_2) / (1.0 - BETA_MIN)
    m_omega = (ETA_MIN * Q_MIN) / C_max_plus

    K_grid = np.linspace(B_M, H_M - 1e-4, 300)
    Psi_sharp_curve = 0.4 * K_grid - 5.0 * (K_grid ** (-0.5)) - 18.5 - 10.0 / 301.0
    c_m = Q_MIN * K_grid + F_A(A_MIN, K_grid, 0.68) - 0.135
    W_M_curve = box_worst_u(c_m, 0.68) + BETA_MAX * (-33.103)
    B_0_curve = np.full_like(K_grid, B_0_val)
    B_1_curve = B_star - m_omega * (H_M - K_grid)
    B_theta_curve = eval_logpwl(B_pwl, K_grid)

    y_wm0 = -35.579855
    psi_28 = -27.83
    T_even = np.arange(2, 50, 2)
    prefix_paper = B_0_val + (BETA_MAX ** T_even) * (psi_28 - B_0_val)

    T_vals = np.arange(1, 51)
    prefix_state = (B_star - m_omega * (H_M - B_M)) + (BETA_MAX ** T_vals) * (psi_28 - B_star)

    B10_c = float(eval_logpwl(B_pwl, np.array([B_M]))[0])
    B28_c = float(eval_logpwl(B_pwl, np.array([H_M]))[0])
    psi28_cegis = float(eval_logpwl(Psi_pwl, np.array([H_M]))[0])
    W10_cegis = float(eval_logpwl(W_pwl, np.array([B_M]))[0])
    prefix_cegis_base = B10_c + (BETA_MAX ** T_vals) * (psi_28 - B28_c)
    prefix_cegis_full = B10_c + (BETA_MAX ** T_vals) * (psi28_cegis - B28_c)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.6, 5.8))
    fig.subplots_adjust(wspace=0.22, bottom=0.14, top=0.89, left=0.065, right=0.98)

    # Panel (a)
    ax1.plot(K_grid, Psi_sharp_curve, color="#444444", ls=":", lw=1.8, label=r"Techo analítico $\Psi^\sharp(K)$")
    ax1.plot(K_grid, W_M_curve, color="#1b7837", ls="-", lw=2.2, label=r"Testigo factible $W_M(K)$")
    ax1.plot(K_grid, B_0_curve, color="#d95f02", ls="--", lw=1.9, label=r"Barrera 2 pasos $B_0 = -38.14$")
    ax1.plot(K_grid, B_1_curve, color="#1f4e78", ls="-", lw=2.3, label=r"Barrera afín $B_1(K)$ ($[-43.36, -43.05]$)")
    ax1.plot(K_grid, B_theta_curve, color="#7b3294", ls="-", lw=2.4, label=r"Barrera CEGIS-LP $B_\theta(K)$")

    ax1.fill_between(K_grid, B_1_curve, B_0_curve, color="#1f4e78", alpha=0.12)
    ax1.fill_between(K_grid, B_theta_curve, B_1_curve, color="#7b3294", alpha=0.12)

    ax1.text(0.185, -40.7, r"Salto afín $46 \to 23$", fontsize=9.8, color="#1f4e78", fontweight="bold", ha="center")
    ax1.text(0.185, -49.5, r"CEGIS-LP: $23 \to 9 \to 5$" + "\n" + r"(margen $\geq +19.06$)", fontsize=9.6, color="#6a1b9a", fontweight="bold", ha="center")

    ax1.set_xlim(B_M, H_M)
    ax1.set_ylim(-58.5, -22.5)
    ax1.set_xlabel(r"Stock de capital $K \in M = [0.10, 0.28)$", fontsize=11.0)
    ax1.set_ylabel(r"Bienestar descontado", fontsize=11.0)
    ax1.set_title(r"(a) Barreras analíticas y CEGIS-LP sobre $M$", fontsize=11.8, pad=9)
    ax1.legend(loc="upper left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, ls=":", alpha=0.35)

    # Panel (b)
    T_base = int(c1["metrics"]["T_theta_base"])
    T_full = int(c1["metrics"]["T_theta_full"])
    ax2.axhline(y_wm0, color="#1b7837", ls="-", lw=2.0, label=r"Piso $W_M(0.10) = -35.58$")
    ax2.axhline(W10_cegis, color="#117a65", ls=":", lw=1.7, label=rf"Testigo CEGIS $W(0.10) = {W10_cegis:.2f}$")
    ax2.plot(T_even, prefix_paper, "o--", color="#d95f02", ms=3.8, lw=1.7, label=r"Bloques 2 pasos ($\tau_H \leq 46$)")
    ax2.plot(T_vals, prefix_state, "-", color="#1f4e78", lw=2.2, label=r"Barrera afín $B_1$ ($\tau_H \leq 23$)")
    ax2.plot(T_vals, prefix_cegis_base, "-", color="#7b3294", lw=2.3, label=rf"CEGIS $B_\theta$ + $W_M$ ($T_\theta \leq {T_base}$)")
    ax2.plot(T_vals, prefix_cegis_full, "-.", color="#c00000", lw=1.9, label=rf"Tripleta CEGIS ($\Psi, W, B_\theta$) ($T_{{\mathrm{{full}}}} \leq {T_full}$)")

    for tv, col in [(46, "#d95f02"), (23, "#1f4e78"), (T_base, "#7b3294"), (T_full, "#c00000"), (4, "#111111")]:
        ax2.axvline(tv, color=col, ls=":", lw=1.2, alpha=0.85)

    ax2.scatter([46], [prefix_paper[T_even == 46][0]], color="#d95f02", zorder=5, s=46)
    ax2.scatter([23], [prefix_state[22]], color="#1f4e78", zorder=5, s=46)
    ax2.scatter([T_base], [prefix_cegis_base[T_base - 1]], color="#7b3294", zorder=5, s=46)
    ax2.scatter([T_full], [prefix_cegis_full[T_full - 1]], color="#c00000", zorder=5, s=46)

    ax2.annotate(r"MR ($\tau_H \leq 46$)", xy=(46, prefix_paper[T_even == 46][0]), xytext=(33.5, -40.8),
                 arrowprops=dict(arrowstyle="->", color="#d95f02", lw=1.1), fontsize=9.2, color="#d95f02", fontweight="bold")
    ax2.annotate(r"Teo. 1 ($\tau_H \leq 23$)", xy=(23, prefix_state[22]), xytext=(26.2, -31.8),
                 arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=1.1), fontsize=9.2, color="#1f4e78", fontweight="bold")
    ax2.annotate(rf"$T_\theta \leq {T_base}$ / $T_{{\mathrm{{full}}}} \leq {T_full}$", xy=(T_base, prefix_cegis_base[T_base - 1]), xytext=(12.8, -45.5),
                 arrowprops=dict(arrowstyle="->", color="#7b3294", lw=1.1), fontsize=9.2, color="#7b3294", fontweight="bold")
    ax2.annotate(r"$T_{\mathrm{ns}}(\theta_0) = 4 = \tau_H^{\mathrm{VFI}}$", xy=(4, -35.58), xytext=(6.0, -27.8),
                 arrowprops=dict(arrowstyle="->", color="#111111", lw=1.1), fontsize=9.2, color="#111111", fontweight="bold")

    ax2.set_xlim(1, 50)
    ax2.set_ylim(-52.0, -25.0)
    ax2.set_xlabel(r"Períodos consecutivos de permanencia en $M$ ($T$)", fontsize=11.0)
    ax2.set_ylabel(r"Cota superior del prefijo $J(T; 0.10)$", fontsize=11.0)
    ax2.set_title(rf"(b) Cascada de plazos: $46 \to 23 \to {T_base} \to {T_full} \to 4$", fontsize=11.8, pad=9)
    ax2.legend(loc="lower right", fontsize=8.4, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    _save_fig("fig1_barrier_es")


def make_fig2(sec4_rows: list) -> None:
    print("Generating fig2_scaling_es ...")
    A_arr = np.array([r[0] for r in sec4_rows], dtype=np.float64)
    kS_fix = np.array([r[5] for r in sec4_rows], dtype=np.float64)
    kS_endo = np.array([r[6] for r in sec4_rows], dtype=np.float64)
    dW_pip = np.array([r[7] for r in sec4_rows], dtype=np.float64)
    dW_p = np.array([r[8] for r in sec4_rows], dtype=np.float64)
    T_esc = np.array([r[9] for r in sec4_rows], dtype=np.int32)
    L_ss = np.array([r[10] for r in sec4_rows], dtype=np.float64)

    delta, c_K, beta_main = 0.08, 2.8284271247461903, 0.97
    asymp_lim = (delta / c_K) ** 2
    dW_minus = (A_arr ** -1.0) * 0.25
    L_ss_exact = 7.0 / 9.0

    A_wk = np.array([1.5, 100.0, 1e8])
    wk_fix, wk_endo = [], []
    for av in A_wk:
        sf, se, *_ = solve_vfi_frontiers(float(av), beta=0.90, k_band=(0.0014, 0.0026))
        wk_fix.append(sf); wk_endo.append(se)

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(9.6, 8.8))
    fig.subplots_adjust(hspace=0.30, left=0.11, right=0.97, top=0.95, bottom=0.08)

    # Panel (a)
    ax1.semilogx(A_arr, kS_endo * 1e4, "o-", color="#1f4e78", lw=2.3, ms=5.5, label=r"$A^2 S_A$ (trabajo endógeno, $\beta=0.97$)")
    ax1.semilogx(A_arr, kS_fix * 1e4, "s--", color="#d95f02", lw=2.1, ms=5.0, label=r"$A^2 S_A^{\mathrm{fix}}(1)$ (trabajo fijo $\bar{L}=1$)")
    ax1.axhline(asymp_lim * 1e4, color="#1b7837", ls=":", lw=2.1, label=r"Límite físico $(\delta/c_K)^2 = 8.00 \times 10^{-4}$")
    ax1.set_xlim(0.55, 2.0e8)
    ax1.set_ylim(7.86, 9.05)
    ax1.set_xlabel(r"Productividad total de los factores $A$ (escala log)", fontsize=11.0)
    ax1.set_ylabel(r"Umbral normalizado $A^2 S_A \times 10^4$", fontsize=11.0)
    ax1.set_title(r"(a) Convergencia asintótica hacia $(\delta/c_K)^2$ hasta $A = 10^8$", fontsize=12.0, pad=8)
    ax1.legend(loc="upper right", fontsize=9.2, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, which="both", ls=":", alpha=0.35)

    ax1_ins = inset_axes(ax1, width="38%", height="35%", loc="lower left", bbox_to_anchor=(0.08, 0.05, 1.0, 1.0), bbox_transform=ax1.transAxes)
    ax1_ins.semilogx(A_wk, np.array(wk_endo) * 1e4, "o-", color="#7b3294", ms=4.5, lw=1.8, label=r"$A^2 S_A$ ($\beta=0.90$)")
    ax1_ins.semilogx(A_wk, np.array(wk_fix) * 1e4, "s--", color="#c00000", ms=4.2, lw=1.6, label=r"$A^2 S_A^{\mathrm{fix}}$")
    ax1_ins.set_title(r"Corolario 1 ($\beta=0.90, \beta\theta=1.35$)", fontsize=8.5, pad=3)
    ax1_ins.tick_params(labelsize=8.0)
    ax1_ins.grid(True, ls=":", alpha=0.3)
    ax1_ins.legend(loc="upper right", fontsize=8.0, frameon=True)

    # Panel (b)
    ax2.loglog(A_arr, dW_p, "^--", color="#d95f02", lw=2.0, ms=5.5, label=r"Brecha superior $\Delta W_A^+ = \Theta(\beta^{T_{\mathrm{esc}}(A)}) \to 0^+$")
    ax2.loglog(A_arr, dW_pip, "o-", color="#1f4e78", lw=2.3, ms=5.5, label=r"Diferencia variacional $\Delta W_A^{\pi^+} \leq \Delta W_A^+$")
    ax2.loglog(A_arr, dW_minus, "-.", color="#c00000", lw=1.9, label=r"Escala armónica inferior $\Delta W_A^- = O(A^{-1})$")
    ax2.loglog(A_arr, beta_main ** T_esc, ":", color="#444444", lw=1.6, label=r"Referencia polilogarítmica $\beta^{T_{\mathrm{esc}}(A)}$")

    ax2.annotate(
        r"$A=10^8$: $\Delta W_A^{\pi^+} \approx \Delta W_A^+ = 0.513 \gg O(A^{-1})$",
        xy=(1e8, dW_pip[-1]), xytext=(1.0e3, 12.0),
        arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=1.1),
        fontsize=9.5, color="#1f4e78", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.28", fc="white", ec="#1f4e78", lw=0.8, alpha=0.95),
    )
    ax2.set_xlim(0.55, 2.2e8)
    ax2.set_ylim(1e-9, 140.0)
    ax2.set_xlabel(r"Productividad total de los factores $A$ (escala log)", fontsize=11.0)
    ax2.set_ylabel(r"Diferenciales de bienestar (escala log)", fontsize=11.0)
    ax2.set_title(r"(b) Decaimiento polilogarítmico $\Delta W_A^{\pi^+} \leq \Delta W_A^+ \to 0^+$ frente a $O(A^{-1})$", fontsize=12.0, pad=8)
    ax2.legend(loc="lower left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, which="both", ls=":", alpha=0.35)

    ax2_ins = inset_axes(ax2, width="33%", height="32%", loc="center right", bbox_to_anchor=(-0.03, -0.02, 1.0, 1.0), bbox_transform=ax2.transAxes)
    ax2_ins.semilogx(A_arr, L_ss, "o-", color="#1b7837", ms=4.0, lw=1.7)
    ax2_ins.axhline(L_ss_exact, color="#111111", ls="--", lw=1.2)
    ax2_ins.set_ylim(0.7765, 0.7830)
    ax2_ins.set_title(r"$L_{\mathrm{ss}} \to \frac{7}{9} \approx 0.7778$", fontsize=8.8, pad=4)
    ax2_ins.tick_params(labelsize=8.0)
    ax2_ins.grid(True, ls=":", alpha=0.3)

    _save_fig("fig2_scaling_es")


def make_fig3(certs: dict, vfi5: dict) -> None:
    print("Generating fig3_stochastic_es ...")
    p_tests = np.array(vfi5["p_tests"], dtype=np.float64) * 100.0
    S_ruin_rel = np.array(vfi5["ruin_S"]) / vfi5["ruin_S"][0]
    S_mk_rel = np.array(vfi5["markov_SG"]) / vfi5["markov_SG"][0]
    kp_ruin_rel = (np.array(vfi5["ruin_kp"]) / vfi5["ruin_kp"][0] - 1.0) * 100.0
    kp_mk_rel = (np.array(vfi5["markov_kp"]) / vfi5["markov_kp"][0] - 1.0) * 100.0

    c2_bands = sorted(certs["case2_ruin_hazard"].items(), key=lambda kv: kv[1]["b_min"])
    p_bands = 1.0 - np.array([0.5 * (b["b_min"] + b["b_max"]) for _, b in c2_bands]) / 0.9700
    mask_p = (p_bands >= -1e-4) & (p_bands <= 0.021)
    p_plot = np.maximum(p_bands[mask_p], 0.0)
    T_B1_arr = np.array([b["metrics"]["T_star"] for _, b in c2_bands], dtype=np.float64)[mask_p]
    T_ceg_raw = [b["metrics"].get("T_star_cegis") for (_, b), m in zip(c2_bands, mask_p) if m]

    order = np.argsort(p_plot)
    p_plot = p_plot[order]
    T_B1_arr = T_B1_arr[order]
    P_doob_B1 = (1.0 - p_plot) ** T_B1_arr

    ceg_pts = [(p_plot[i], float(T_ceg_raw[idx])) for i, idx in enumerate(order) if T_ceg_raw[idx] is not None]
    p_ceg = np.array([pt[0] for pt in ceg_pts], dtype=np.float64)
    P_ceg = np.array([(1.0 - p) ** t for p, t in ceg_pts], dtype=np.float64)

    p_dense = np.linspace(0.0, 0.020, 100)
    P_46 = (1.0 - p_dense) ** 46
    P_23 = (1.0 - p_dense) ** 23

    bot_mt = c2_bands[0][1]["metrics"]
    T2_B1 = bot_mt["T_star"]
    T2_ceg = bot_mt["T_star_cegis"]
    p2_b1_pct = 100.0 * (0.98 ** T2_B1)
    p2_ceg_pct = 100.0 * (0.98 ** T2_ceg)

    p_er = np.array(vfi5["endo_ruin_p"], dtype=np.float64) * 100.0
    S_er_rel = np.array(vfi5["endo_ruin_S"]) / vfi5["endo_ruin_S"][0]
    kp_er_rel = (np.array(vfi5["endo_ruin_kp"]) / vfi5["endo_ruin_kp"][0] - 1.0) * 100.0

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(9.6, 9.0))
    fig.subplots_adjust(hspace=0.30, left=0.10, right=0.90, top=0.95, bottom=0.07)

    # Panel (a)
    l1, = ax1.plot(p_tests, S_ruin_rel, "o-", color="#c00000", lw=2.3, ms=5.5, label=r"Ruina exóg.: $S^{\mathrm{ruin}}(p)/S_0$")
    l2, = ax1.plot(p_tests, S_mk_rel, "s-", color="#1f4e78", lw=2.2, ms=5.2, label=r"Markov ($p_{\mathrm{rec}}=1/3$): $S_G(p)/S_0$")
    l2e, = ax1.plot(p_er, S_er_rel, "v-", color="#7b3294", lw=2.1, ms=5.2, label=r"Ruina endóg. $p(K)$: $S_{\mathrm{endo}}(p)/S_0$")
    ax1.set_xlim(-0.2, 8.2)
    ax1.set_ylim(0.90, 3.12)
    ax1.set_xlabel(r"Probabilidad anual de crisis $p$ (%)", fontsize=11.0)
    ax1.set_ylabel(r"Umbral Skiba relativo $S(p) / S(0)$", fontsize=11.0)
    ax1.set_title(r"(a) Dicotomía VFI: colapso bajo ruina exógena vs. huida hacia la seguridad", fontsize=12.0, pad=8)
    ax1.grid(True, ls=":", alpha=0.35)

    ax1_r = ax1.twinx()
    l3, = ax1_r.plot(p_tests, kp_ruin_rel, "^--", color="#d95f02", lw=1.9, ms=5.2, label=r"Ruina exóg.: $\Delta K'(0.10)$ (%)")
    l4, = ax1_r.plot(p_tests, kp_mk_rel, "D--", color="#1b7837", lw=1.9, ms=4.8, label=r"Markov: $\Delta K'_G(0.10)$ (%)")
    l5, = ax1_r.plot(p_er, kp_er_rel, "P--", color="#984ea3", lw=2.0, ms=5.5, label=r"Ruina endóg.: $\Delta K'(0.10)$ (%)")
    ax1_r.axhline(0.0, color="#666666", ls=":", lw=1.0)
    ax1_r.set_ylabel(r"Cambio en inversión $K'(0.10)$ respecto a $p=0$ (%)", fontsize=10.8)
    ax1_r.set_ylim(-5.8, 7.6)
    ax1_r.tick_params(labelsize=10.0)

    lines_all = [l1, l2, l2e, l3, l4, l5]
    labels_all = [ln.get_label() for ln in lines_all]
    ax1.legend(lines_all, labels_all, loc="upper left", ncol=2, fontsize=8.4, frameon=True, facecolor="white", framealpha=0.96)

    # Panel (b)
    ax2.plot(p_dense * 100.0, P_23 * 100.0, "--", color="#1b7837", lw=2.0, label=r"Teo. 1 sin anticipación $(1-p)^{23}$")
    ax2.plot(p_dense * 100.0, P_46 * 100.0, "-.", color="#d95f02", lw=1.9, label=r"Bloques MR sin anticipación $(1-p)^{46}$")
    ax2.plot(p_plot * 100.0, P_doob_B1 * 100.0, "-", color="#1f4e78", lw=2.4, label=rf"Caso 2 continuo $B_1$ (60 bandas $\tilde{{\beta}}_p$): $T^*_{{2\%}}={T2_B1}$")
    if len(p_ceg) > 1:
        ax2.plot(p_ceg * 100.0, P_ceg * 100.0, "-", color="#7b3294", lw=2.5, zorder=7,
                 label=rf"Caso 2 continuo CEGIS-LP $B_\theta$ (60 bandas): $T^*_{{2\%}}={T2_ceg}$")
    elif len(p_ceg) == 1:
        ax2.plot(p_ceg * 100.0, P_ceg * 100.0, "*", color="#7b3294", ms=12.0, zorder=7,
                 label=rf"Caso 2 CEGIS-LP $B_\theta$ ($p=2\%$): $T^*_{{2\%}}={T2_ceg}$")

    p2_ceg_lb = math.floor(p2_ceg_pct * 100.0) / 100.0
    p2_b1_lb = math.floor(p2_b1_pct * 100.0) / 100.0
    ax2.scatter([2.0, 2.0], [p2_ceg_pct, p2_b1_pct], color=["#7b3294", "#1f4e78"], zorder=8, s=50)
    ax2.annotate(
        rf"$p=2\%$: CEGIS $T^*={T2_ceg}$ ($\geq {p2_ceg_lb:.2f}\%$)",
        xy=(2.0, p2_ceg_pct), xytext=(0.98, 81.0),
        arrowprops=dict(arrowstyle="->", color="#7b3294", lw=1.1),
        fontsize=9.3, color="#7b3294", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="#7b3294", lw=0.8, alpha=0.95),
    )
    ax2.annotate(
        rf"$p=2\%$: $B_1$ banda $\tilde{{\beta}}_p$, $T^*={T2_B1}$ ($\geq {p2_b1_lb:.2f}\%$)",
        xy=(2.0, p2_b1_pct), xytext=(0.96, 56.0),
        arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=1.1),
        fontsize=9.3, color="#1f4e78", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="#1f4e78", lw=0.8, alpha=0.95),
    )

    ax2.set_xlim(-0.04, 2.08)
    ax2.set_ylim(5.0, 103.0)
    ax2.set_xlabel(r"Riesgo anual anticipado de ruina $p$ (%)", fontsize=11.0)
    ax2.set_ylabel(r"Probabilidad certificada de supervivencia (%)", fontsize=11.0)
    ax2.set_title(r"(b) Cotas de Doob certificadas sobre 60 bandas continuas de $\tilde{\beta}_p$", fontsize=12.0, pad=8)
    ax2.legend(loc="lower left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    _save_fig("fig3_stochastic_es")


def make_fig_arch() -> None:
    print("Generating fig_arch_es ...")
    fig, ax = plt.subplots(figsize=(11.6, 5.0))
    ax.set_xlim(0.0, 11.6)
    ax.set_ylim(0.0, 5.0)
    ax.axis("off")

    # TCB bounding box
    tcb = FancyBboxPatch(
        (3.45, 0.22), 7.90, 4.48,
        boxstyle="round,pad=0.12,rounding_size=0.18",
        fc="#f8fafc", ec="#0b2c4d", lw=1.4, ls="--", zorder=1
    )
    ax.add_patch(tcb)
    ax.text(7.40, 4.44, "Base de Cómputo Confiable (TCB) — Verificación Independiente del Algoritmo de Síntesis",
            ha="center", va="center", fontsize=9.6, fontweight="bold", color="#0b2c4d",
            bbox=dict(boxstyle="round,pad=0.15", fc="#f8fafc", ec="none"))

    def draw_box(x, y, w, h, title, sub, fc, ec, title_col="#0b2c4d"):
        box = FancyBboxPatch(
            (x, y), w, h,
            boxstyle="round,pad=0.08,rounding_size=0.14",
            fc=fc, ec=ec, lw=1.6, zorder=3
        )
        ax.add_patch(box)
        ax.text(x + w / 2, y + h * 0.65, title, ha="center", va="center",
                fontsize=10.2, fontweight="bold", color=title_col, zorder=4)
        ax.text(x + w / 2, y + h * 0.30, sub, ha="center", va="center",
                fontsize=8.6, color="#334155", zorder=4)

    def draw_arrow(x1, y1, x2, y2, col="#1f4e78", rad=0.0, lw=1.7, ls="-"):
        arr = FancyArrowPatch(
            (x1, y1), (x2, y2),
            connectionstyle=f"arc3,rad={rad}",
            arrowstyle="-|>,head_length=6,head_width=3.5",
            color=col, lw=lw, ls=ls, zorder=5
        )
        ax.add_patch(arr)

    draw_box(0.30, 2.65, 2.65, 1.38, "Proposer (HiGHS-LP)",
             "LP disperso determinista\nlog-PWL + reg. TV", "#fff7ed", "#d95f02", "#9a3412")
    draw_box(3.75, 2.65, 2.75, 1.38, "Verifier (B&B 3D / 1D)",
             "Forma centrada + monotonía\nsobre espacio continuo", "#eff6ff", "#1f4e78", "#0b2c4d")
    draw_box(7.10, 2.65, 1.75, 1.38, "Certificados",
             ".json.xz (5.75 MB)\nCasos 1–6 exportados", "#f3e8ff", "#7b3294", "#581c87")
    draw_box(9.35, 2.65, 1.80, 1.38, "Auditoría sin libm",
             "Rust + Decimal 50 díg.\naudit_standalone.py", "#ecfdf5", "#1b7837", "#14532d")

    draw_box(3.85, 0.42, 7.10, 1.14, "Formalización Mecanizada en Lean 4 (v4.36.0 + Mathlib4)",
             "13 módulos · 0 sorry · 0 axiomas adicionales\nLemas 1–2, Teoremas 1–3, Prop. 1–9 · Lemas 11–12 de MR (2026)", "#fefce8", "#b45309", "#78350f")

    draw_arrow(2.95, 3.34, 3.75, 3.34, col="#1f4e78")
    draw_arrow(6.50, 3.34, 7.10, 3.34, col="#1f4e78")
    draw_arrow(8.85, 3.34, 9.35, 3.34, col="#1b7837")

    # Counterexample feedback loop
    draw_arrow(5.12, 2.65, 1.62, 2.65, col="#c00000", rad=-0.34, lw=1.6, ls="-")
    ax.text(3.37, 2.02, "Contraejemplos continuos (inserción adaptativa de nodos)",
            ha="center", va="center", fontsize=8.5, fontweight="bold", color="#c00000",
            bbox=dict(boxstyle="round,pad=0.18", fc="white", ec="#fecaca", lw=0.8), zorder=6)

    # Lean 4 arrow into Audit / Guarantee
    draw_arrow(10.25, 1.56, 10.25, 2.65, col="#b45309", lw=1.5, ls="--")

    _save_fig("fig_arch_es")


def make_fig_nearskiba(certs: dict) -> None:
    print("Generating fig_nearskiba_es ...")
    ns = certs["case1_affine_gap"]["near_skiba_cascade"]
    sb0 = ns["subbands"][0]
    Psi_pwl = pwl_from_dict(sb0["Psi_net"])
    W_pwl = pwl_from_dict(sb0["W_net"])

    fig, ax = plt.subplots(figsize=(11.4, 5.8))
    fig.subplots_adjust(left=0.08, right=0.97, top=0.90, bottom=0.13)

    stage_colors = ["#fde68a", "#fed7aa", "#fecaca", "#ddd6fe", "#bfdbfe"]
    stage_labels = [
        "[0.003, 0.006]\n" + r"($T_1\leq 21$)",
        "[0.006, 0.015]\n" + r"($T_2\leq 13$)",
        "[0.015, 0.040]\n" + r"($T_3\leq 8$)",
        "[0.040, 0.100]\n" + r"($T_4\leq 5$)",
        "[0.100, 0.280)\n" + r"($T_5\leq 5$)",
    ]

    ax.axvspan(0.001588, 0.0030, color="#f3f4f6", alpha=0.85, zorder=0)
    ax.axvspan(0.28, 0.80, color="#dcfce7", alpha=0.55, zorder=0)
    ax.axvspan(0.80, 1.60, color="#bbf7d0", alpha=0.45, zorder=0)

    k_full = np.geomspace(0.001588, 1.5, 500)
    ax.plot(k_full, eval_logpwl(Psi_pwl, k_full), color="#374151", ls=":", lw=2.0, label=r"Techo certificado $\Psi(K)$")
    ax.plot(k_full, eval_logpwl(W_pwl, k_full), color="#1b7837", ls="-", lw=2.3, label=r"Testigo factible $W(K)$")

    for i, st in enumerate(sb0["stages"]):
        bm, hm = float(st["b_m"]), float(st["h_m"])
        ax.axvspan(bm, hm, color=stage_colors[i], alpha=0.42, zorder=0)
        B_st = pwl_from_dict(st["B_net"])
        ks_st = np.geomspace(bm, hm, 80)
        vals_st = eval_logpwl(B_st, ks_st)
        lbl = r"Barreras escalonadas $B_{\theta,i}(K)$ ($i=1\dots 5$)" if i == 0 else None
        ax.plot(ks_st, vals_st, color="#7b3294", lw=2.8, label=lbl, zorder=4)
        k_mid = np.sqrt(bm * hm)
        ax.text(k_mid, -16.0, stage_labels[i],
                ha="center", va="top", fontsize=7.9, color="#1e293b")

    ax.axvline(0.001588, color="#dc2626", ls="--", lw=1.4)
    ax.axvline(0.0030, color="#9a3412", ls="-", lw=1.4)
    ax.axvline(0.10, color="#1f4e78", ls="--", lw=1.2, alpha=0.75)
    ax.axvline(0.28, color="#15803d", ls="-", lw=1.6)
    ax.axvline(0.80, color="#166534", ls=":", lw=1.2)

    ax.text(0.00168, -206.0, r"$S_A=0.001588$", fontsize=8.8, color="#dc2626", fontweight="bold", rotation=90, va="bottom")
    ax.text(0.00315, -135.0, r"$b_{\mathrm{ext}}=0.0030$", fontsize=8.8, color="#9a3412", fontweight="bold", rotation=90, va="bottom")
    ax.text(0.295, -95.0, r"$h=0.28$ ($H_1$)", fontsize=8.8, color="#15803d", fontweight="bold", rotation=90, va="bottom")
    ax.text(0.84, -95.0, r"$H_2 \geq 0.80$", fontsize=8.8, color="#166534", fontweight="bold", rotation=90, va="bottom")

    ax.annotate(
        r"Cascada continua en 16 subcajas ($4_A \times 4_\beta$):" + "\n" +
        r"$T_{\mathrm{total}} \leq 21+13+8+5+5 = 52$ períodos" + "\n" +
        r"Cierra $99.5\%$ de $[0.0025, 0.10)$",
        xy=(0.030, -112.0), xytext=(0.09, -152.0),
        arrowprops=dict(arrowstyle="->", color="#7b3294", lw=1.2),
        fontsize=9.4, fontweight="bold", color="#581c87",
        bbox=dict(boxstyle="round,pad=0.3", fc="white", ec="#7b3294", lw=0.9, alpha=0.95),
    )

    ax.set_xscale("log")
    ax.set_xlim(0.0014, 1.60)
    ax.set_ylim(-212.0, -12.0)
    ax.set_xlabel(r"Stock de capital $K$ (escala logarítmica desde $S_A$ hasta $H_2$)", fontsize=11.0)
    ax.set_ylabel(r"Bienestar descontado", fontsize=11.0)
    ax.set_title(r"Mapa logarítmico del espacio de estados y cascada near-Skiba ($b_{\mathrm{ext}} = 0.0030$)", fontsize=12.0, pad=10)
    ax.legend(loc="lower right", fontsize=9.2, frameon=True, facecolor="white", framealpha=0.96)
    ax.grid(True, which="both", ls=":", alpha=0.35)

    _save_fig("fig_nearskiba_es")


def make_fig_markov(certs: dict, vfi5: dict) -> None:
    print("Generating fig_markov_es ...")
    c3 = certs["case3_markov_h1"]
    p_keys = sorted(c3.keys(), key=lambda s: float(s))
    p_pct = np.array([float(k) * 100.0 for k in p_keys])
    etau_aff = np.array([c3[k]["metrics"]["T_0"] / c3[k]["metrics"]["eps_0_lb"] for k in p_keys])
    etau_comp = np.array([c3[k]["metrics"]["E_tau_comp"] for k in p_keys])
    vfi_map = vfi5["case3_etau_vfi"]
    etau_vfi = np.array([vfi_map[min(vfi_map.keys(), key=lambda x: abs(x - float(k)))][0] for k in p_keys])

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(9.6, 8.8))
    fig.subplots_adjust(hspace=0.30, left=0.10, right=0.97, top=0.95, bottom=0.07)

    # Panel (a): E[tau] compression
    ax1.semilogy(p_pct, etau_aff, "o--", color="#d95f02", lw=2.2, ms=6.0, label=r"Barrera afín analítica ($\mathbb{E}[\tau] \leq 1\,480\text{ a }13\,323$)")
    ax1.semilogy(p_pct, etau_comp, "s-", color="#7b3294", lw=2.5, ms=6.0, label=r"Pareja acoplada CEGIS-LP $(B_{G,\theta}, B_{B,\theta})$ ($\mathbb{E}[\tau] \leq 35.1\text{ a }38.8$)")
    ax1.semilogy(p_pct, etau_vfi, "^-", color="#1b7837", lw=2.2, ms=6.0, label=r"Óptimo verdadero VFI ($\max_M \mathbb{E}_{\mathrm{VFI}}[\tau] \approx 5.81\text{ a }5.92$)")

    ax1.annotate(
        r"Compresión $42\times\text{ a }343\times$" + "\n" + r"($13\,323 \to 38.8$ en $p=12\%$)",
        xy=(12.0, etau_comp[-1]), xytext=(6.2, 420.0),
        arrowprops=dict(arrowstyle="->", color="#7b3294", lw=1.2),
        fontsize=9.4, fontweight="bold", color="#581c87",
        bbox=dict(boxstyle="round,pad=0.28", fc="white", ec="#7b3294", lw=0.8, alpha=0.95),
    )
    ax1.annotate(
        r"Brecha residual $\approx 6\times$" + "\n" + r"(cota estacionaria + caja)",
        xy=(8.0, etau_vfi[6]), xytext=(2.8, 11.5),
        arrowprops=dict(arrowstyle="->", color="#1b7837", lw=1.1),
        fontsize=9.1, fontweight="bold", color="#14532d",
        bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="#1b7837", lw=0.8, alpha=0.95),
    )

    ax1.set_xlim(-0.4, 12.5)
    ax1.set_ylim(3.0, 28000.0)
    ax1.set_xlabel(r"Probabilidad anual de transición recesiva $p$ (%)", fontsize=11.0)
    ax1.set_ylabel(r"Cota superior / valor esperado $\mathbb{E}[\tau]$ (escala log)", fontsize=11.0)
    ax1.set_title(r"(a) Compresión estocástica de $\mathbb{E}[\tau]$ en el sistema Markov $(G, B)$", fontsize=12.0, pad=8)
    ax1.legend(loc="upper left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, which="both", ls=":", alpha=0.35)

    # Panel (b): Coupled barriers at p=12% + inset of 1054 leaves
    rec12 = c3["0.120"]
    BG = pwl_from_dict(rec12["BG_comp_net"])
    BB = pwl_from_dict(rec12["BB_comp_net"])
    WG = pwl_from_dict(rec12["WG_net"])
    WB = pwl_from_dict(rec12["WB_net"])
    K_grid = np.linspace(B_M, H_M - 1e-4, 250)

    ax2.plot(K_grid, eval_logpwl(WG, K_grid), "-", color="#1b7837", lw=2.2, label=r"Testigo próspero $W_G(K)$ ($p=12\%$)")
    ax2.plot(K_grid, eval_logpwl(WB, K_grid), "--", color="#2b8cbe", lw=2.1, label=r"Testigo recesivo $W_B(K)$ ($p=12\%$)")
    ax2.plot(K_grid, eval_logpwl(BG, K_grid), "-", color="#7b3294", lw=2.3, label=r"Barrera acoplada $B_{G,\theta}(K)$")
    ax2.plot(K_grid, eval_logpwl(BB, K_grid), "-.", color="#c00000", lw=2.2, label=r"Barrera acoplada $B_{B,\theta}(K)$")

    ax2.set_xlim(B_M, H_M)
    ax2.set_ylim(-64.5, -31.5)
    ax2.set_xlabel(r"Stock de capital $K \in M = [0.10, 0.28)$", fontsize=11.0)
    ax2.set_ylabel(r"Bienestar descontado", fontsize=11.0)
    ax2.set_title(r"(b) Barreras acopladas $(B_{G,\theta}, B_{B,\theta})$ en $p=12\%$ y hojas continuas $H_{1,B}$", fontsize=12.0, pad=8)
    ax2.legend(loc="upper left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    # Inset: 1,054 leaves across p placed in the clear middle gap
    leaf_counts = [len(c3[k]["subbox_leaves"]) for k in p_keys]
    ax2_ins = inset_axes(ax2, width="41%", height="37%", loc="center right", bbox_to_anchor=(-0.02, -0.02, 1.0, 1.0), bbox_transform=ax2.transAxes)
    x_pos = np.arange(len(p_keys))
    ax2_ins.bar(x_pos, leaf_counts, color="#1f4e78", alpha=0.85, edgecolor="#0b2c4d", lw=0.7)
    ax2_ins.set_xticks(x_pos)
    ax2_ins.set_xticklabels([f"{float(k)*100:g}%" for k in p_keys], fontsize=7.5, rotation=25)
    ax2_ins.set_ylim(0, 175)
    ax2_ins.set_ylabel("Hojas", fontsize=8.2)
    ax2_ins.set_title(r"Total $1\,054$ hojas $H_{1,B}$ ($m \geq +0.00015$)", fontsize=8.4, pad=3)
    ax2_ins.tick_params(labelsize=7.8)
    ax2_ins.grid(True, axis="y", ls=":", alpha=0.3)

    _save_fig("fig_markov_es")


def make_fig_endo_policy(vfi5: dict) -> None:
    print("Generating fig_endo_policy_es ...")
    k_grid = vfi5["k_grid"]
    pol0 = vfi5["endo_ruin_pols"][0.0]
    pol1 = vfi5["endo_ruin_pols"][0.01]

    mask = (k_grid >= 0.095) & (k_grid <= 0.295)
    k_sub = k_grid[mask]

    # Simulate exact trajectories starting from K_0 = 0.10
    def sim_traj(pol):
        ks = [B_M]
        while ks[-1] < H_M and len(ks) < 20:
            ks.append(float(np.interp(ks[-1], k_grid, pol)))
        return np.array(ks)

    traj0 = sim_traj(pol0)
    traj1 = sim_traj(pol1)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.4))
    fig.subplots_adjust(wspace=0.23, bottom=0.14, top=0.88, left=0.07, right=0.98)

    # Panel (a): Policy function K'(K)
    ax1.plot(k_sub, k_sub, ":", color="#666666", lw=1.4, label=r"Línea de $45^\circ$ ($K' = K$)")
    ax1.plot(k_sub, pol0[mask], "--", color="#1f4e78", lw=2.3, label=r"$p = 0\%$ ($K'(0.10) = 0.13364$)")
    ax1.plot(k_sub, pol1[mask], "-", color="#7b3294", lw=2.5, label=r"$p = 1\%$ ($K'(0.10) = 0.13719$, $+2.66\%$)")
    ax1.axhline(H_M, color="#1b7837", ls="-.", lw=1.5, label=r"Umbral seguro $h = 0.28$")
    ax1.fill_between(k_sub, pol0[mask], pol1[mask], where=(k_sub < H_M), color="#7b3294", alpha=0.14)

    ax1.annotate(
        r"Huida endógena" + "\n" + r"hacia la seguridad",
        xy=(0.14, float(np.interp(0.14, k_grid, pol1))), xytext=(0.175, 0.145),
        arrowprops=dict(arrowstyle="->", color="#7b3294", lw=1.1),
        fontsize=9.4, fontweight="bold", color="#581c87",
        bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="#7b3294", lw=0.8, alpha=0.95),
    )

    ax1.set_xlim(0.10, 0.29)
    ax1.set_ylim(0.10, 0.36)
    ax1.set_xlabel(r"Stock actual de capital $K_t$", fontsize=11.0)
    ax1.set_ylabel(r"Política óptima de ahorro $K'_{t}$", fontsize=11.0)
    ax1.set_title(r"(a) Desplazamiento precautorio de $K'(K)$ en Caso 5", fontsize=11.8, pad=8)
    ax1.legend(loc="upper left", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, ls=":", alpha=0.35)

    # Panel (b): Discrete escape trajectories 4 -> 3 steps
    t0 = np.arange(len(traj0))
    t1 = np.arange(len(traj1))
    ax2.axhline(H_M, color="#1b7837", ls="-.", lw=1.8, label=r"Umbral seguro $h = 0.28$ ($p(K)=0$)")
    ax2.plot(t0, traj0, "o--", color="#1f4e78", lw=2.3, ms=6.5, label=rf"$p = 0\%$: alcanza $h$ en $\tau_{{\mathrm{{VFI}}}} = {len(traj0)-1}$ pasos")
    ax2.plot(t1, traj1, "s-", color="#7b3294", lw=2.5, ms=6.5, label=rf"$p = 1\%$: alcanza $h$ en $\tau_{{\mathrm{{VFI}}}} = {len(traj1)-1}$ pasos")

    ax2.scatter([len(traj0) - 1], [traj0[-1]], color="#1f4e78", s=70, zorder=6)
    ax2.scatter([len(traj1) - 1], [traj1[-1]], color="#7b3294", s=70, zorder=6)

    ax2.set_xticks(np.arange(0, max(len(traj0), len(traj1))))
    ax2.set_xlim(-0.15, max(len(traj0), len(traj1)) - 0.75)
    ax2.set_ylim(0.08, 0.36)
    ax2.set_xlabel(r"Período $t$ desde $K_0 = 0.10$", fontsize=11.0)
    ax2.set_ylabel(r"Trayectoria de capital óptima $K_t$", fontsize=11.0)
    ax2.set_title(r"(b) Acortamiento del escape óptimo: $4 \to 3$ períodos", fontsize=11.8, pad=8)
    ax2.legend(loc="lower right", fontsize=8.8, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    _save_fig("fig_endo_policy_es")


if __name__ == "__main__":
    cert_path = os.path.join(OUT_DIR, "cegis_certificates.json.xz")
    if not os.path.exists(cert_path):
        cert_path = os.path.join(OUT_DIR, "cegis_certificates.json")
    certs_data = json.load(lzma.open(cert_path, "rt", encoding="utf-8") if cert_path.endswith(".xz") else open(cert_path, "r", encoding="utf-8"))

    only = set(sys.argv[1:])
    if not only:
        make_fig1(certs_data)
        sec4_data = verify_section4_theorem3_star()
        make_fig2(sec4_data)
        sec5_data = verify_section5_stochastic_vfi()
        make_fig3(certs_data, sec5_data)
        make_fig_arch()
        make_fig_nearskiba(certs_data)
        make_fig_markov(certs_data, sec5_data)
        make_fig_endo_policy(sec5_data)
    else:
        if "--fig1-only" in only:
            make_fig1(certs_data)
        if "--fig2-only" in only:
            make_fig2(verify_section4_theorem3_star())
        if "--arch-only" in only:
            make_fig_arch()
        if "--nearskiba-only" in only:
            make_fig_nearskiba(certs_data)
        if only & {"--fig3-only", "--markov-only", "--endo-only"}:
            sec5_data = verify_section5_stochastic_vfi()
            if "--fig3-only" in only:
                make_fig3(certs_data, sec5_data)
            if "--markov-only" in only:
                make_fig_markov(certs_data, sec5_data)
            if "--endo-only" in only:
                make_fig_endo_policy(sec5_data)
    print("Generated all 7 manuscript figures (.svg & .png) cleanly.")
