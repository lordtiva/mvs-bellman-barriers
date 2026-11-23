"""
Generate the 3 publication-quality Spanish figures for Article A:
  - fig1_barrier_es.{svg,png}
  - fig2_scaling_es.{svg,png}
  - fig3_stochastic_es.{svg,png}

Reads certified PWL objects directly from cegis_certificates.json and computes
exact VFI curves via verify_article_a helpers (zero duplicate solvers).
"""

from __future__ import annotations

import json
import lzma
import os
import sys
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
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
from verify_article_a import (
    solve_vfi_frontiers,
    verify_section4_theorem3_star,
    verify_section5_stochastic_vfi,
)

OUT_DIR = os.path.dirname(os.path.abspath(__file__))

mpl.rcParams["font.family"] = "serif"
mpl.rcParams["mathtext.fontset"] = "cm"
mpl.rcParams["axes.linewidth"] = 0.8
mpl.rcParams["xtick.major.width"] = 0.8
mpl.rcParams["ytick.major.width"] = 0.8
mpl.rcParams["xtick.direction"] = "in"
mpl.rcParams["ytick.direction"] = "in"


def make_fig1(certs: dict) -> None:
    print("Generating fig1_barrier_es ...")
    c1 = certs["case1_affine_gap"]
    B_pwl = pwl_from_dict(c1.get("B_pwl", c1["B_net"]))
    Psi_pwl = pwl_from_dict(c1["Psi_net"])
    W_pwl = pwl_from_dict(c1["W_net"])

    C_max_plus = Q_MAX * H_M + F_A(A_MAX, H_M, 1.0) - B_M
    R_hat = -0.996
    Delta_2_exact = Q_MIN * ETA_MIN * BETA_MIN * (H_M - B_M) / C_max_plus
    Delta_2 = 0.2997  # Analytical rounded constant validated by Delta_2_exact > 0.2997
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

    # Panel (b) prefix curves (worst-case discount BETA_MAX ** T)
    y_wm0 = -35.579855
    psi_28 = -27.83
    T_even = np.arange(2, 50, 2)
    prefix_paper = B_0_val + (BETA_MAX ** T_even) * (psi_28 - B_0_val)

    T_vals = np.arange(1, 51)
    prefix_unif = B_star + (BETA_MAX ** T_vals) * (psi_28 - B_star)
    prefix_state = (B_star - m_omega * (H_M - B_M)) + (BETA_MAX ** T_vals) * (psi_28 - B_star)

    # Case 1 CEGIS B_theta with MR-Table 4 tail vs CEGIS (Psi, W)
    B10_c = float(eval_logpwl(B_pwl, np.array([B_M]))[0])
    B28_c = float(eval_logpwl(B_pwl, np.array([H_M]))[0])
    psi28_cegis = float(eval_logpwl(Psi_pwl, np.array([H_M]))[0])
    W10_cegis = float(eval_logpwl(W_pwl, np.array([B_M]))[0])
    prefix_cegis_base = B10_c + (BETA_MAX ** T_vals) * (psi_28 - B28_c)
    prefix_cegis_full = B10_c + (BETA_MAX ** T_vals) * (psi28_cegis - B28_c)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.4))
    fig.subplots_adjust(wspace=0.23, bottom=0.14, top=0.88, left=0.065, right=0.975)

    # Panel (a)
    ax1.plot(K_grid, Psi_sharp_curve, color="#444444", ls=":", lw=1.6, label=r"Techo analítico $\Psi^\sharp(K)$")
    ax1.plot(K_grid, W_M_curve, color="#1b7837", ls="-", lw=2.0, label=r"Testigo factible $W_M(K)$ (MR-Tabla 4)")
    ax1.plot(K_grid, B_0_curve, color="#d95f02", ls="--", lw=1.7, label=r"Barrera 2 pasos $B_0 = -38.14$ (MR)")
    ax1.plot(K_grid, B_1_curve, color="#1f4e78", ls="-", lw=2.1, label=r"Barrera afín 1 paso $B_1(K)$ ($-43.36$ a $-43.05$)")
    ax1.plot(K_grid, B_theta_curve, color="#7b3294", ls="-", lw=2.3, label=r"Barrera CEGIS-LP $B_\theta(K)$ (57 nodos)")

    ax1.fill_between(K_grid, B_1_curve, B_0_curve, color="#1f4e78", alpha=0.12)
    ax1.fill_between(K_grid, B_theta_curve, B_1_curve, color="#7b3294", alpha=0.12)

    ax1.annotate(
        r"Salto afín $46 \to 23$" + "\n" + r"($+4.90$ a $+5.21$)",
        xy=(0.175, -40.7), xytext=(0.175, -40.7),
        fontsize=8.3, color="#1f4e78", fontweight="bold", ha="center",
    )
    ax1.annotate(
        r"Afilamiento CEGIS-LP $23 \to 9 \to 5$" + "\n" + r"(margen $\geq +19.06$; cascada $b_{\mathrm{ext}}=0.003 \Rightarrow T \leq 52$)",
        xy=(0.180, -49.2), xytext=(0.180, -49.2),
        fontsize=7.9, color="#6a1b9a", fontweight="bold", ha="center",
    )
    ax1.set_xlim(B_M, H_M)
    ax1.set_ylim(-58.5, -23.0)
    ax1.set_xlabel(r"Stock de capital en región de tránsito $K \in M = [0.10, 0.28)$", fontsize=9.5)
    ax1.set_ylabel(r"Bienestar descontado", fontsize=9.5)
    ax1.set_title(r"(a) Calibración analítica y CEGIS-PWL sobre $M$", fontsize=10.2, pad=8)
    ax1.legend(loc="upper left", fontsize=7.3, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, ls=":", alpha=0.35)

    # Panel (b)
    ax2.axhline(y_wm0, color="#1b7837", ls="-", lw=1.8, label=r"Piso $W_M(0.10) = -35.58$ (MR-Tabla 4)")
    ax2.axhline(W10_cegis, color="#117a65", ls=":", lw=1.4, label=rf"Testigo CEGIS $W(0.10) = {W10_cegis:.2f}$")
    ax2.plot(T_even, prefix_paper, "o--", color="#d95f02", ms=3.2, lw=1.5, label=r"Bloques originales MR ($\tau_H \leq 46$)")
    T_base = int(c1["metrics"]["T_theta_base"])
    T_full = int(c1["metrics"]["T_theta_full"])
    ax2.plot(T_vals, prefix_state, "-", color="#1f4e78", lw=2.0, label=r"Barrera afín $B_1$ estado-a-estado ($\tau_H \leq 23$)")
    ax2.plot(T_vals, prefix_cegis_base, "-", color="#7b3294", lw=2.2, label=rf"CEGIS $B_\theta$ + MR-Tabla 4 ($T_\theta \leq {T_base}$)")
    ax2.plot(T_vals, prefix_cegis_full, "-.", color="#c00000", lw=1.7, label=rf"Tripleta CEGIS ($\Psi, W, B_\theta$) ($T_{{\mathrm{{full}}}} \leq {T_full}$)")

    for tv, col in [(46, "#d95f02"), (23, "#1f4e78"), (T_base, "#7b3294"), (T_full, "#c00000"), (4, "#111111")]:
        ax2.axvline(tv, color=col, ls=":", lw=1.1, alpha=0.85)

    ax2.scatter([46], [prefix_paper[T_even == 46][0]], color="#d95f02", zorder=5, s=38)
    ax2.scatter([23], [prefix_state[22]], color="#1f4e78", zorder=5, s=38)
    ax2.scatter([T_base], [prefix_cegis_base[T_base - 1]], color="#7b3294", zorder=5, s=40)
    ax2.scatter([T_full], [prefix_cegis_full[T_full - 1]], color="#c00000", zorder=5, s=40)

    ax2.annotate(r"MR ($\tau_H \leq 46$)", xy=(46, prefix_paper[T_even == 46][0]), xytext=(34.5, -40.8),
                 arrowprops=dict(arrowstyle="->", color="#d95f02", lw=0.9), fontsize=8.0, color="#d95f02", fontweight="bold")
    ax2.annotate(r"Teo. 1 ($\tau_H \leq 23$)", xy=(23, prefix_state[22]), xytext=(26.0, -32.2),
                 arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=0.9), fontsize=8.0, color="#1f4e78", fontweight="bold")
    ax2.annotate(rf"CEGIS $T_\theta \leq {T_base}$" + "\n" + rf"($T_{{\mathrm{{full}}}} \leq {T_full}$, no estac. $\mathcal{{P}}: 5$)", xy=(T_base, prefix_cegis_base[T_base - 1]), xytext=(12.2, -45.5),
                 arrowprops=dict(arrowstyle="->", color="#7b3294", lw=0.9), fontsize=7.8, color="#7b3294", fontweight="bold")
    ax2.annotate(r"No estac. $\theta_0$: $T_{\mathrm{ns}} = 4 = \tau_H^{\mathrm{VFI}}$", xy=(4, -35.58), xytext=(5.5, -28.0),
                 arrowprops=dict(arrowstyle="->", color="#111111", lw=0.9), fontsize=7.9, color="#111111", fontweight="bold")

    ax2.set_xlim(1, 50)
    ax2.set_ylim(-51.5, -25.0)
    ax2.set_xlabel(r"Períodos consecutivos de permanencia en $M$ ($T$)", fontsize=9.5)
    ax2.set_ylabel(r"Cota superior del prefijo $J(T; 0.10)$", fontsize=9.5)
    ax2.set_title(rf"(b) Cascada completa de plazos: $46 \to 23 \to {T_base} \to {T_full} \to 4$", fontsize=10.2, pad=8)
    ax2.legend(loc="lower right", fontsize=7.0, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    for ext in ("svg", "png"):
        kw = {"dpi": 300} if ext == "png" else {}
        plt.savefig(os.path.join(OUT_DIR, f"fig1_barrier_es.{ext}"), **kw)
    plt.close()


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
    asymp_lim = (delta / c_K) ** 2  # 0.000800
    dW_minus = (A_arr ** -1.0) * 0.25  # O(A^{-1}) reference slope normalized nicely on log-log
    L_ss_exact = 7.0 / 9.0

    # Weak patience beta=0.90 points
    A_wk = np.array([1.5, 100.0, 1e8])
    wk_fix, wk_endo = [], []
    for av in A_wk:
        sf, se, *_ = solve_vfi_frontiers(float(av), beta=0.90, k_band=(0.0014, 0.0026))
        wk_fix.append(sf); wk_endo.append(se)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.4))
    fig.subplots_adjust(wspace=0.24, bottom=0.14, top=0.88, left=0.075, right=0.975)

    # Panel (a)
    ax1.semilogx(A_arr, kS_endo * 1e4, "o-", color="#1f4e78", lw=2.1, ms=4.2, label=r"$A^2 S_A$ (trabajo endógeno, $\beta=0.97$)")
    ax1.semilogx(A_arr, kS_fix * 1e4, "s--", color="#d95f02", lw=1.9, ms=4.0, label=r"$A^2 S_A^{\mathrm{fix}}(1)$ (trabajo fijo $\bar{L}=1$)")
    ax1.axhline(asymp_lim * 1e4, color="#1b7837", ls=":", lw=1.8, label=r"Límite $(\delta/c_K)^2 = 8.00 \times 10^{-4}$")
    ax1.set_xlim(0.6, 1.8e8)
    ax1.set_ylim(7.88, 9.05)
    ax1.set_xlabel(r"Productividad total de los factores $A$ (escala log)", fontsize=9.5)
    ax1.set_ylabel(r"Umbral normalizado $A^2 S_A \times 10^4$", fontsize=9.5)
    ax1.set_title(r"(a) Convergencia asintótica a $(\delta/c_K)^2$ hasta $A = 10^8$", fontsize=10.2, pad=8)
    ax1.legend(loc="upper right", fontsize=7.4, frameon=True, facecolor="white", framealpha=0.96)
    ax1.grid(True, which="both", ls=":", alpha=0.35)

    ax1_ins = inset_axes(ax1, width="43%", height="34%", loc="lower left", bbox_to_anchor=(0.09, 0.08, 1.0, 1.0), bbox_transform=ax1.transAxes)
    ax1_ins.semilogx(A_wk, np.array(wk_endo) * 1e4, "o-", color="#7b3294", ms=3.5, lw=1.5, label=r"$A^2 S_A$ ($\beta=0.90$)")
    ax1_ins.semilogx(A_wk, np.array(wk_fix) * 1e4, "s--", color="#c00000", ms=3.3, lw=1.4, label=r"$A^2 S_A^{\mathrm{fix}}$")
    ax1_ins.set_title(r"Corolario 1 ($\beta=0.90, \beta\theta=1.35$)", fontsize=7.2, pad=2)
    ax1_ins.tick_params(labelsize=6.8)
    ax1_ins.grid(True, ls=":", alpha=0.3)
    ax1_ins.legend(loc="upper right", fontsize=6.2, frameon=True)

    # Panel (b)
    ax2.loglog(A_arr, dW_p, "^--", color="#d95f02", lw=1.8, ms=4.5, label=r"Brecha superior $\Delta W_A^+ = \Theta(\beta^{T_{\mathrm{esc}}(A)}) \to 0^+$")
    ax2.loglog(A_arr, dW_pip, "o-", color="#1f4e78", lw=2.2, ms=4.5, label=r"Diferencia variacional $\Delta W_A^{\pi^+} \leq \Delta W_A^+$")
    ax2.loglog(A_arr, dW_minus, "-.", color="#c00000", lw=1.7, label=r"Escala armónica inferior $\Delta W_A^- = O(A^{-1})$")
    ax2.loglog(A_arr, beta_main ** T_esc, ":", color="#444444", lw=1.3, label=r"Referencia polilogarítmica $\beta^{T_{\mathrm{esc}}(A)}$")

    ax2.annotate(
        r"$A=10^8: \Delta W_A^{\pi^+} \approx \Delta W_A^+ = 0.513$" + "\n" + r"Prueba analítica pura: $T_M = O(\ln\ln A),\ \beta^{T_M}g_{T_M} \gg A^{-1}$" + "\n" + r"2.º orden: $\Delta_k \asymp (\ln\ln A / (\ln A)^{1-\kappa})^{1/\mu_K}$",
        xy=(1e8, dW_pip[-1]), xytext=(1.5e3, 3.2),
        arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=0.9),
        fontsize=7.1, color="#1f4e78", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.22", fc="white", ec="#1f4e78", lw=0.6, alpha=0.95),
    )
    ax2.set_xlim(0.6, 2.0e8)
    ax2.set_ylim(1e-9, 120.0)
    ax2.set_xlabel(r"Productividad $A$ (escala log)", fontsize=9.5)
    ax2.set_ylabel(r"Diferenciales de bienestar (escala log)", fontsize=9.5)
    ax2.set_title(r"(b) Decaimiento $\Delta W_A^{\pi^+} \leq \Delta W_A^+ \to 0^+$ vs. $O(A^{-1})$", fontsize=10.2, pad=8)
    ax2.legend(loc="lower left", fontsize=7.0, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, which="both", ls=":", alpha=0.35)

    ax2_ins = inset_axes(ax2, width="34%", height="27%", loc="center left", bbox_to_anchor=(0.06, 0.04, 1.0, 1.0), bbox_transform=ax2.transAxes)
    ax2_ins.semilogx(A_arr, L_ss, "o-", color="#1b7837", ms=3.0, lw=1.4)
    ax2_ins.axhline(L_ss_exact, color="#111111", ls="--", lw=1.0)
    ax2_ins.set_ylim(0.7765, 0.7830)
    ax2_ins.set_title(r"$L_{\mathrm{ss}} \to \frac{7}{9} \approx 0.7778$", fontsize=7.2, pad=2)
    ax2_ins.tick_params(labelsize=6.6)
    ax2_ins.grid(True, ls=":", alpha=0.3)

    for ext in ("svg", "png"):
        kw = {"dpi": 300} if ext == "png" else {}
        plt.savefig(os.path.join(OUT_DIR, f"fig2_scaling_es.{ext}"), **kw)
    plt.close()


def make_fig3(certs: dict, vfi5: dict) -> None:
    print("Generating fig3_stochastic_es ...")
    p_tests = np.array(vfi5["p_tests"], dtype=np.float64) * 100.0
    S_ruin_rel = np.array(vfi5["ruin_S"]) / vfi5["ruin_S"][0]
    S_mk_rel = np.array(vfi5["markov_SG"]) / vfi5["markov_SG"][0]
    kp_ruin_rel = (np.array(vfi5["ruin_kp"]) / vfi5["ruin_kp"][0] - 1.0) * 100.0
    kp_mk_rel = (np.array(vfi5["markov_kp"]) / vfi5["markov_kp"][0] - 1.0) * 100.0

    # Panel (b) Doob certificates across p in [0, 2.0%]
    c2_bands = sorted(certs["case2_ruin_hazard"].items(), key=lambda kv: kv[1]["b_min"])
    # Only plot the p in [0, 2%] monotone envelope (b_min in [BETA_MIN*0.98, 0.97])
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

    # Exact 2% corner numbers from Case 2 JSON and worst Markov eps0 from Case 3 JSON
    bot_mt = c2_bands[0][1]["metrics"]
    T2_B1 = bot_mt["T_star"]
    T2_ceg = bot_mt["T_star_cegis"]
    p2_b1_pct = 100.0 * (0.98 ** T2_B1)
    p2_ceg_pct = 100.0 * (0.98 ** T2_ceg)
    eps0_min_c3 = min(rec["metrics"]["eps0_comp"] for rec in certs["case3_markov_h1"].values())
    etau_max_c3 = max(rec["metrics"]["E_tau_comp"] for rec in certs["case3_markov_h1"].values())

    p_er = np.array(vfi5["endo_ruin_p"], dtype=np.float64) * 100.0
    S_er_rel = np.array(vfi5["endo_ruin_S"]) / vfi5["endo_ruin_S"][0]
    kp_er_rel = (np.array(vfi5["endo_ruin_kp"]) / vfi5["endo_ruin_kp"][0] - 1.0) * 100.0

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.4))
    fig.subplots_adjust(wspace=0.26, bottom=0.14, top=0.88, left=0.07, right=0.93)

    # Panel (a)
    l1, = ax1.plot(p_tests, S_ruin_rel, "o-", color="#c00000", lw=2.2, ms=4.5, label=r"Ruina exóg.: $S^{\mathrm{ruin}}(p)/S_0$ ($2.89\times$ en 8%)")
    l2, = ax1.plot(p_tests, S_mk_rel, "s-", color="#1f4e78", lw=2.1, ms=4.5, label=r"Markov ($p_{\mathrm{rec}}=1/3$): $S_G(p)/S_0$ ($+11.7\%$)")
    l2e, = ax1.plot(p_er, S_er_rel, "v-", color="#7b3294", lw=1.9, ms=4.2, label=r"Ruina endóg. $p(K)$: $S_{\mathrm{endo}}(p)/S_0$")
    ax1.set_xlim(-0.2, 8.2)
    ax1.set_ylim(0.90, 3.08)
    ax1.set_xlabel(r"Probabilidad anual de crisis $p$ (%)", fontsize=9.5)
    ax1.set_ylabel(r"Umbral Skiba relativo $S(p) / S(0)$", fontsize=9.5)
    ax1.set_title(r"(a) Dicotomía VFI: colapso vs. «huida hacia la seguridad»", fontsize=10.2, pad=8)
    ax1.grid(True, ls=":", alpha=0.35)

    ax1_r = ax1.twinx()
    l3, = ax1_r.plot(p_tests, kp_ruin_rel, "^--", color="#d95f02", lw=1.7, ms=4.2, label=r"Ruina exóg.: $\Delta K'(0.10)$ (% caída inv.)")
    l4, = ax1_r.plot(p_tests, kp_mk_rel, "D--", color="#1b7837", lw=1.7, ms=4.0, label=r"Markov: $\Delta K'_G(0.10)$ (% suba precautoria)")
    l5, = ax1_r.plot(p_er, kp_er_rel, "P--", color="#984ea3", lw=1.8, ms=4.5, label=r"Ruina endóg. $p(K)$: $\Delta K'(0.10)$ (huida endóg.)")
    ax1_r.axhline(0.0, color="#666666", ls=":", lw=0.9)
    ax1_r.set_ylabel(r"Cambio en inversión $K'(0.10)$ respecto a $p=0$ (%)", fontsize=9.2)
    ax1_r.set_ylim(-5.8, 7.6)

    lines_all = [l1, l2, l2e, l3, l4, l5]
    labels_all = [ln.get_label() for ln in lines_all]
    ax1.legend(lines_all, labels_all, loc="upper left", fontsize=6.4, frameon=True, facecolor="white", framealpha=0.96)

    # Panel (b)
    ax2.plot(p_dense * 100.0, P_23 * 100.0, "--", color="#1b7837", lw=1.8, label=r"Teo. 1 sin anticipación $(1-p)^{23}$ ($p=0$ fijo)")
    ax2.plot(p_dense * 100.0, P_46 * 100.0, "-.", color="#d95f02", lw=1.7, label=r"Bloques MR sin anticipación $(1-p)^{46}$")
    ax2.plot(p_plot * 100.0, P_doob_B1 * 100.0, "-", color="#1f4e78", lw=2.3, label=rf"Caso 2 continuo $B_1$ (60 bandas $\tilde{{\beta}}_p$): $T^*_{{2\%}}={T2_B1}$")
    if len(p_ceg) > 1:
        ax2.plot(
            p_ceg * 100.0, P_ceg * 100.0, "-", color="#7b3294", lw=2.3, zorder=7,
            label=rf"Caso 2 continuo CEGIS-LP $B_\theta$ (60 bandas): $T^*_{{2\%}}={T2_ceg}$"
        )
    elif len(p_ceg) == 1:
        ax2.plot(
            p_ceg * 100.0, P_ceg * 100.0, "*", color="#7b3294", ms=11.0, zorder=7,
            label=rf"Caso 2 CEGIS-LP $B_\theta$ ($p=2\%$): $(1-p)^{{T^*_{{\mathrm{{CEGIS}}}}}}$ ($T^*_{{2\%}}={T2_ceg}$)"
        )

    ax2.scatter([2.0, 2.0], [p2_ceg_pct, p2_b1_pct], color=["#7b3294", "#1f4e78"], zorder=8, s=42)
    ax2.annotate(
        rf"$p=2\%$: CEGIS $T^*={T2_ceg}$ ({p2_ceg_pct:.1f}%)",
        xy=(2.0, p2_ceg_pct), xytext=(0.72, 82.0),
        arrowprops=dict(arrowstyle="->", color="#7b3294", lw=0.9),
        fontsize=7.6, color="#7b3294", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="#7b3294", lw=0.6, alpha=0.95),
    )
    ax2.annotate(
        rf"$p=2\%$: $B_1$ banda $\tilde{{\beta}}_p$ $T^*={T2_B1}$ ({p2_b1_pct:.1f}%)" + "\n" +
        rf"Markov Caso 3 ($B_{{G,\theta}},B_{{B,\theta}}$): $\mathbb{{E}}[\tau]\leq {etau_max_c3:.1f}$ ($\varepsilon_0\geq {eps0_min_c3:.3f}$)",
        xy=(2.0, p2_b1_pct), xytext=(0.25, 25.0),
        arrowprops=dict(arrowstyle="->", color="#1f4e78", lw=0.9),
        fontsize=7.3, color="#1f4e78", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.22", fc="white", ec="#1f4e78", lw=0.6, alpha=0.95),
    )

    ax2.set_xlim(-0.05, 2.08)
    ax2.set_ylim(5.0, 103.0)
    ax2.set_xlabel(r"Riesgo anual anticipado de colapso $p$ (%)", fontsize=9.5)
    ax2.set_ylabel(r"Probabilidad certificada de escapar a $H$ (%)", fontsize=9.5)
    ax2.set_title(r"(b) Cotas de Doob certificadas: bandas continuas y CEGIS-LP", fontsize=10.2, pad=8)
    ax2.legend(loc="lower left", fontsize=6.9, frameon=True, facecolor="white", framealpha=0.96)
    ax2.grid(True, ls=":", alpha=0.35)

    for ext in ("svg", "png"):
        kw = {"dpi": 300} if ext == "png" else {}
        plt.savefig(os.path.join(OUT_DIR, f"fig3_stochastic_es.{ext}"), **kw)
    plt.close()


if __name__ == "__main__":
    cert_path = os.path.join(OUT_DIR, "cegis_certificates.json.xz")
    if not os.path.exists(cert_path):
        cert_path = os.path.join(OUT_DIR, "cegis_certificates.json")
    certs_data = json.load(lzma.open(cert_path, "rt", encoding="utf-8") if cert_path.endswith(".xz") else open(cert_path, "r", encoding="utf-8"))
    fig1_only = "--fig1-only" in sys.argv
    fig2_only = "--fig2-only" in sys.argv
    fig3_only = "--fig3-only" in sys.argv
    if fig1_only:
        make_fig1(certs_data)
    elif fig2_only:
        sec4_data = verify_section4_theorem3_star()
        make_fig2(sec4_data)
    elif fig3_only:
        sec5_data = verify_section5_stochastic_vfi()
        make_fig3(certs_data, sec5_data)
    else:
        make_fig1(certs_data)
        sec4_data = verify_section4_theorem3_star()
        make_fig2(sec4_data)
        sec5_data = verify_section5_stochastic_vfi()
        make_fig3(certs_data, sec5_data)
    print("Generated fig1_barrier_es, fig2_scaling_es, fig3_stochastic_es (.svg & .png) cleanly.")
