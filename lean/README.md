# Formalización en Lean 4 — MVS Bellman Barriers

Formalización mecanizada en **Lean 4 (`v4.36.0` + Mathlib4)** de la arquitectura matemática completa del artículo *«Barreras de Bellman Afiladas, Equivalencia Asintótica y Supervivencia Estocástica Certificada bajo Rendimientos Crecientes»*.

* **0 `sorry`** en los 13 módulos de `MVS/`.
* **0 axiomas adicionales**: todos los teoremas principales dependen exclusivamente de los tres axiomas estándar de Lean 4 (`[propext, Classical.choice, Quot.sound]`), sin `native_decide`.

---

## Mapa de módulos (`MVS/`)

| Módulo | Resultado del artículo | Teoremas principales |
| :--- | :--- | :--- |
| `MVS/Lemma11.lean` | **Lema 11 (MR)** — envoltura certificada de $\log$ sin `libm` | `atanh_log_bounds`, `log_bounds_of_ge_one`, `log_bounds_of_pow_enclosure`, `log_two_bounds` |
| `MVS/Lemma12.lean` | **Lema 12 (MR)** — núcleo analítico y colas de $\Psi^\#$ | `Psi_sharp_le_tangent`, `bellman_elim_Kp`, `lemma12_small_K` ($K \le 1/25000$), `lemma12_large_K` ($K \ge 50$), `lemma12_global_super_barrier`, `lemma12_value_le_Psi_sharp` |
| `MVS/Lemma12Cert.lean` | **Lema 12 (MR)** — cierre certificado de $[1/25000, 50]$ y global $(0,\infty)$ | 131 segmentos racionales en 5 bandas (`bandA_ok`–`bandD_ok`), `lemma12_mid_certified`, **`lemma12_global_certified`** |
| `MVS/Theorem1.lean` | **Lema 1 & Teorema 1** — barrera afín de 1 paso ($\tau_H \le 23$) | `R_hat_valid`, `W_M_b_ge`, **`theorem1_state_by_state_23_closed`** |
| `MVS/Proposition1.lean` | **Proposición 1** — región $M_0 = [0.05, 0.10)$ y condición $c < 0.25$ | `R_hat0_valid`, `W_M0_orig_ge`, `W_M0_sharp_ge`, **`prop1_uniform_10`** |
| `MVS/Proposition2.lean` | **Proposición 2** — dominancia tangente, envolvente $E^+$ y Wronskiano $Q_X$ | `tangent_dominance`, `adverse_exit_le_E_plus`, `hasDerivAt_F_K`, `hasDerivAt_FK_K` |
| `MVS/Proposition2Cert.lean` | **Proposición 2** — certificación racional completa de la Tabla 2 | `prop2_M_positive`, `prop2_H1_positive` |
| `MVS/Theorem2.lean` | **Teorema 2 (Partes 1 y 2) & Corolario 1** — convergencia uniforme y $S_A^{\text{fix}}(1) < S_A$ analítico puro | `f_norm_eq`, `F_ces_homog`, `phase2_step_bound`, `link4_dichotomy`, **`theorem2_part2_assembled`**, `corollary2_fixed_labor_invariance`, `corollary2_ratio_tendsto_one`, `harmonicBenchmark_exact_constants`, `weakPatience_local_vs_global` |
| `MVS/Theorem2SecondOrder.lean` | **Teorema de segundo orden** (elevación de Observación 1 Parte 1 + cota superior Parte 2) | `piece1_exact_rescaling`, `piece1_lower_exact`, `piece1_sum_split_upper`, `piece2_explicit_policy`, `piece2_delta_k_upper`, `phi_sublinear_exact`, `piece3_telescoping_budget`, `piece3_c0_bound`, `piece3_log_sum_upper`, `piece3_delta_k_lower`, `part2_free_relative_gap_bound`, `part2_delta_W_plus_rate`, `harmonic_second_order_exact_constants` |
| `MVS/Stochastic.lean` | **Lema 2, Corolario 2 & Teorema 3** — parada opcional de Doob y converso FPBB | `lemma2_doob_escape_prob`, `corollary2_geometric_tail`, `corollary2_expected_time_tsum`, **`theorem3_fpbb_converse_exact`**, `theorem3_fpbb_converse_approx`, `markov_2state_B_star_exact` |
| `MVS/CEGIS.lean` | **Capa de solidez (*soundness*) CEGIS-PWL** | `LogPWL`, `cegis_staying_deadline_sound`, `cegis_ruin_deadline_sound`, `staying_cover_sound`, `super_barrier_finite_sound`, `witness_subsolution_finite_sound` |
| `MVS/CEGISCert.lean` | **Proposición 3 (Caso 1A)** — certificación en kernel de $B_\theta$ (22 nodos, $T_\theta \le 9$) | `case1_B_chain_ok`, `case1_B_margins`, **`case1_deadline_9_certified`** |
| `MVS/Section5Theory.lean` | **Proposiciones 3–9** — teoría estructural completa de las Secciones 5 y 6 | `nonstationary_chain_deadline` (Prop. 3), `cascade_multi_stage` / `cascade_5stage_52` (Prop. 4), `F_AK_homog_ray` / `AK_tail_ray_invariance` (Prop. 5), `subbox_cover_deadline` (Prop. 6), `exog_ruin_bellman_invariance` (Prop. 7), `markov2_coupled_doob_gap` (Prop. 8), `endo_ruin_survival_premium` / `table7_survival_bounds_exact` (Prop. 9) |

---

## Compilación y auditoría reproducible

Requiere [`elan`](https://github.com/leanprover/elan) instalado (el archivo `lean-toolchain` fija `leanprover/lean4:v4.36.0`).

```bash
cd lean

# 1. Descargar caché precompilada de Mathlib4 (evita compilar Mathlib desde cero)
lake exe cache get

# 2. Compilar y verificar todos los módulos en el kernel de Lean 4
lake build
```

### Auditoría de axiomas y ausencia de `sorry`

```bash
# Comprobar axiomas de los teoremas principales:
lake env lean --stdin <<'EOF'
import MVS
#print axioms MVS.Lemma12Cert.lemma12_global_certified
#print axioms MVS.Theorem1.theorem1_state_by_state_23_closed
#print axioms MVS.Proposition1.prop1_uniform_10
#print axioms MVS.Proposition2Cert.prop2_M_positive
#print axioms MVS.Proposition2Cert.prop2_H1_positive
#print axioms MVS.Theorem2.CESParams.theorem2_part2_assembled
#print axioms MVS.Theorem2.CESParams.piece2_delta_k_upper
#print axioms MVS.Theorem2.CESParams.piece3_delta_k_lower
#print axioms MVS.Theorem2.CESParams.part2_free_relative_gap_bound
#print axioms MVS.Stochastic.theorem3_fpbb_converse_exact
#print axioms MVS.CEGISCert.case1_deadline_9_certified
#print axioms MVS.Section5Theory.cascade_5stage_52
EOF
```

Salida esperada para cada teorema: exclusivamente `[propext, Classical.choice, Quot.sound]` (o un subconjunto de ellos).
