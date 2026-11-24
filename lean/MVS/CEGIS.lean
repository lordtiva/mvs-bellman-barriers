import MVS.Theorem1
import MVS.Proposition1
import MVS.Lemma11
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Verificador Formal CEGIS-PWL (`MVS.CEGIS`)

Formalización completa y sin `sorry` de la capa de corrección (*soundness*) del
auditor CEGIS-PWL de la Sección 5 de `verify_article_a.py` / `cegis_verifier.py`:

1. **Representación exacta `LogPWL`**: interpolación lineal en `log K` por segmentos,
   cotas de intervalo exactas (`segEval_mem_Icc`, `segEval_mono`, `segEval_endpoints`).
2. **Teorema de plazo por barrera de permanencia** (`cegis_staying_deadline_sound`) y su
   versión estocástica con riesgo de ruina (`cegis_ruin_deadline_sound`).
3. **Corrección del auditor Branch-and-Bound 3D por cajas** (`staying_box_infeasible_sound`,
   `staying_box_feasible_sound`, `staying_cover_sound`) que fundamenta la verificación
   por intervalos de `verify_staying_barrier_bb` / `rs_verify_staying_barrier_bb_ext`.
4. **Corrección de super-barreras y subsoluciones testigo** (`super_barrier_finite_sound`,
   `witness_subsolution_finite_sound`).
5. **Certificación en el kernel de la compresión de horizontes**:
   - Caso 1 (testigo MR + `B_net`): $\tau_H \le 9$ (`case1_deadline_9`),
   - Caso 1 completo (CEGIS `W_net`, `Psi_net`, `B_net`): $\tau_H \le 6$ (`case1_deadline_6`),
   - Caso 4 (régimen AK): $\tau_H \le 4$ (`case4_ak_deadline_4`).
-/

open Finset Real Set MVS.Theorem1

namespace MVS.CEGIS

noncomputable section

/-! ## 1. Representación exacta `LogPWL` y cotas de segmento -/

/-- Interpolación lineal en `log x` sobre un segmento `[kL, kR]` con valores `(vL, vR)`. -/
def segEval (kL vL kR vR x : ℝ) : ℝ :=
  vL + (vR - vL) * ((Real.log x - Real.log kL) / (Real.log kR - Real.log kL))

lemma segEval_left {kL vL kR vR : ℝ} :
    segEval kL vL kR vR kL = vL := by
  unfold segEval; simp

lemma segEval_right {kL vL kR vR : ℝ} (hkL : 0 < kL) (hlt : kL < kR) :
    segEval kL vL kR vR kR = vR := by
  unfold segEval
  have hden : Real.log kR - Real.log kL ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.log_lt_log hkL hlt))
  rw [div_self hden]; ring

/-- Peso normalizado $t(x) = \frac{\log x - \log k_L}{\log k_R - \log k_L} \in [0, 1]$ en $[k_L, k_R]$. -/
lemma log_weight_mem_Icc {kL kR x : ℝ} (hkL : 0 < kL) (hlt : kL < kR)
    (hx : x ∈ Icc kL kR) :
    0 ≤ (Real.log x - Real.log kL) / (Real.log kR - Real.log kL) ∧
    (Real.log x - Real.log kL) / (Real.log kR - Real.log kL) ≤ 1 := by
  have hden : 0 < Real.log kR - Real.log kL := sub_pos.mpr (Real.log_lt_log hkL hlt)
  have hx_pos : 0 < x := lt_of_lt_of_le hkL hx.1
  have h1 : Real.log kL ≤ Real.log x := Real.log_le_log hkL hx.1
  have h2 : Real.log x ≤ Real.log kR := Real.log_le_log hx_pos hx.2
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hden)
  · rw [div_le_one hden]; linarith

/-- Encierro exacto de un segmento `LogPWL`: todo valor en `[kL, kR]` cae en `[min vL vR, max vL vR]`. -/
theorem segEval_mem_Icc {kL vL kR vR x : ℝ} (hkL : 0 < kL) (hlt : kL < kR)
    (hx : x ∈ Icc kL kR) :
    min vL vR ≤ segEval kL vL kR vR x ∧ segEval kL vL kR vR x ≤ max vL vR := by
  obtain ⟨ht0, ht1⟩ := log_weight_mem_Icc hkL hlt hx
  set t := (Real.log x - Real.log kL) / (Real.log kR - Real.log kL)
  have hconv : segEval kL vL kR vR x = (1 - t) * vL + t * vR := by
    unfold segEval; dsimp [t]; ring
  rw [hconv]
  have h1m : 0 ≤ 1 - t := by linarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left vL vR) h1m
    have h2 := mul_le_mul_of_nonneg_left (min_le_right vL vR) ht0
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (le_max_left vL vR) h1m
    have h2 := mul_le_mul_of_nonneg_left (le_max_right vL vR) ht0
    linarith

/-- Monotonicidad de un segmento `LogPWL` creciente ($v_L \le v_R$). -/
theorem segEval_mono {kL vL kR vR x y : ℝ} (hkL : 0 < kL) (hlt : kL < kR)
    (hv : vL ≤ vR) (hx : 0 < x) (hxy : x ≤ y) :
    segEval kL vL kR vR x ≤ segEval kL vL kR vR y := by
  unfold segEval
  have hden : 0 < Real.log kR - Real.log kL := sub_pos.mpr (Real.log_lt_log hkL hlt)
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hdiv : (Real.log x - Real.log kL) / (Real.log kR - Real.log kL) ≤
      (Real.log y - Real.log kL) / (Real.log kR - Real.log kL) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)
  have := mul_le_mul_of_nonneg_left hdiv (by linarith : 0 ≤ vR - vL)
  linarith

/-- Nodo `(k, v)` de una función `LogPWL`. -/
structure Knot where
  k : ℝ
  v : ℝ

/-- Evaluación recursiva de una tabla `LogPWL` ordenada sobre nodos `ks`. -/
def evalLogPWLCore (s_hi : ℝ) : List Knot → ℝ → ℝ
  | [], _ => 0
  | [p], x => p.v + s_hi * (Real.log x - Real.log p.k)
  | p :: q :: rest, x =>
    if x ≤ q.k then segEval p.k p.v q.k q.v x
    else evalLogPWLCore s_hi (q :: rest) x

/-- Evaluación global de una función `LogPWL` (idéntica a `eval_logpwl` de `pwl_model.py`). -/
def evalLogPWL (knots : List Knot) (s_lo s_hi x : ℝ) : ℝ :=
  match knots with
  | [] => 0
  | p :: rest =>
    if x < p.k then p.v + s_lo * (Real.log x - Real.log p.k)
    else evalLogPWLCore s_hi (p :: rest) x

/-! ## 2. Teoremas de plazo por barrera de permanencia (determinista y con ruina) -/

/-- Teorema maestro de plazo CEGIS-PWL (determinista):
    si `B` satisface la desigualdad de Bellman de un paso en `[b_m, h_m)`,
    `m_inf ≤ W(x) - B(x)` y `Psi(x) - B(x) ≤ M_sup` en `[b_m, h_m)`,
    con `beta_max ^ T * M_sup < m_inf`, entonces toda trayectoria que permanezca
    `T` períodos en `[b_m, h_m)` es estrictamente dominada por `W(x 0)`. -/
theorem cegis_staying_deadline_sound (θ : Params) (T : ℕ)
    (b_m h_m m_inf M_sup : ℝ) (B W Psi : ℝ → ℝ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ T, b_m ≤ x t ∧ x t < h_m)
    (hL : ∀ t < T, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < T, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi (x T))
    (hB_stay : ∀ t < T,
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t) + θ.β * B (x (t + 1)) ≤ B (x t))
    (hm_inf : ∀ y, b_m ≤ y ∧ y < h_m → m_inf ≤ W y - B y)
    (hM_sup : ∀ y, b_m ≤ y ∧ y < h_m → Psi y - B y ≤ M_sup)
    (hM_nn : 0 ≤ M_sup)
    (hdead : beta_max ^ T * M_sup < m_inf) :
    (∑ t ∈ range T, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ T * V_cont < W (x 0) := by
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have htel := telescoping_bellman hβ0 B
    (fun t => u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) x T hB_stay
  have hβT_nn : 0 ≤ θ.β ^ T := pow_nonneg hβ0 T
  have hpow_le : θ.β ^ T ≤ beta_max ^ T := pow_le_pow_left₀ hβ0 θ.hβ.2 T
  have hcont : V_cont - B (x T) ≤ M_sup := by
    linarith [hM_sup (x T) (hx T le_rfl)]
  have hmul1 : θ.β ^ T * (V_cont - B (x T)) ≤ θ.β ^ T * M_sup :=
    mul_le_mul_of_nonneg_left hcont hβT_nn
  have hmul2 : θ.β ^ T * M_sup ≤ beta_max ^ T * M_sup :=
    mul_le_mul_of_nonneg_right hpow_le hM_nn
  have hm0 : m_inf ≤ W (x 0) - B (x 0) := hm_inf (x 0) (hx 0 (Nat.zero_le T))
  have hdist : θ.β ^ T * (V_cont - B (x T)) = θ.β ^ T * V_cont - θ.β ^ T * B (x T) := by ring
  linarith

/-- Teorema de plazo CEGIS-PWL con riesgo de ruina `p_ruin ∈ [0, 1)` (Caso 2):
    con descuento efectivo `β_eff = β * (1 - p_ruin) ≤ b_hi * (1 - p_ruin)` y pago de ruina
    `p_ruin * V_ruin` que se cancela en `V - B`, el plazo `T` certificado en
    `certify_staying_deadline_interval` es exacto. -/
theorem cegis_ruin_deadline_sound {β b_hi p_ruin V_ruin m_inf M_sup : ℝ} (T : ℕ)
    (hβ0 : 0 ≤ β) (hβ_le : β ≤ b_hi) (hp0 : 0 ≤ p_ruin) (hp1 : p_ruin ≤ 1)
    (B W Psi : ℝ → ℝ) (u_seq x : ℕ → ℝ) (V_cont : ℝ)
    (hB_stay : ∀ t < T,
      u_seq t + β * ((1 - p_ruin) * B (x (t + 1)) + p_ruin * V_ruin) ≤ B (x t))
    (hm0 : m_inf ≤ W (x 0) - B (x 0))
    (hMT : V_cont - B (x T) ≤ M_sup)
    (hM_nn : 0 ≤ M_sup)
    (hdead : (b_hi * (1 - p_ruin)) ^ T * M_sup < m_inf) :
    (∑ t ∈ range T, (β * (1 - p_ruin)) ^ t * (u_seq t + β * p_ruin * V_ruin)) +
      (β * (1 - p_ruin)) ^ T * V_cont < W (x 0) := by
  have hβeff0 : 0 ≤ β * (1 - p_ruin) := mul_nonneg hβ0 (by linarith)
  have hstep : ∀ t < T,
      (u_seq t + β * p_ruin * V_ruin) + (β * (1 - p_ruin)) * B (x (t + 1)) ≤ B (x t) := by
    intro t ht
    linarith [hB_stay t ht]
  have htel := telescoping_bellman hβeff0 B (fun t => u_seq t + β * p_ruin * V_ruin) x T hstep
  have hβeff_le : β * (1 - p_ruin) ≤ b_hi * (1 - p_ruin) :=
    mul_le_mul_of_nonneg_right hβ_le (by linarith)
  have hpow_le : (β * (1 - p_ruin)) ^ T ≤ (b_hi * (1 - p_ruin)) ^ T :=
    pow_le_pow_left₀ hβeff0 hβeff_le T
  have hmul1 : (β * (1 - p_ruin)) ^ T * (V_cont - B (x T)) ≤ (β * (1 - p_ruin)) ^ T * M_sup :=
    mul_le_mul_of_nonneg_left hMT (pow_nonneg hβeff0 T)
  have hmul2 : (β * (1 - p_ruin)) ^ T * M_sup ≤ (b_hi * (1 - p_ruin)) ^ T * M_sup :=
    mul_le_mul_of_nonneg_right hpow_le hM_nn
  have hdist : (β * (1 - p_ruin)) ^ T * (V_cont - B (x T)) =
      (β * (1 - p_ruin)) ^ T * V_cont - (β * (1 - p_ruin)) ^ T * B (x T) := by ring
  linarith

/-! ## 3. Corrección del auditor Branch-and-Bound 3D por cajas (`verify_staying_barrier_bb`) -/

/-- Caja 3D `[xL, xR] × [yL, yR] × [LL, LR]` para la auditoría de permanencia. -/
structure Box3D where
  xL : ℝ
  xR : ℝ
  yL : ℝ
  yR : ℝ
  LL : ℝ
  LR : ℝ

/-- Pertenencia de un punto `(x, y, L)` a una caja 3D. -/
def Box3D.mem (box : Box3D) (x y L : ℝ) : Prop :=
  box.xL ≤ x ∧ x ≤ box.xR ∧ box.yL ≤ y ∧ y ≤ box.yR ∧ box.LL ≤ L ∧ L ≤ box.LR

/-- Cota superior monótona del consumo sobre una caja 3D. -/
lemma consumption_le_box_corner (θ : Params) (box : Box3D) {x y L : ℝ}
    (hxL : 0 < box.xL) (hLL : 0 ≤ box.LL) (hmem : box.mem x y L) :
    θ.q * x + F θ.A x L - y ≤ q_max * box.xR + F A_max box.xR box.LR - box.yL := by
  have hx_pos : 0 < x := lt_of_lt_of_le hxL hmem.1
  have hxR_pos : 0 < box.xR := lt_of_lt_of_le hx_pos hmem.2.1
  have hL_nn : 0 ≤ L := le_trans hLL hmem.2.2.2.2.1
  have hA_nn : 0 ≤ A_max := by unfold A_max; norm_num
  have hq_nn : 0 ≤ q_max := by unfold q_max; norm_num
  have hq_le : θ.q * x ≤ q_max * box.xR :=
    mul_le_mul θ.hq.2 hmem.2.1 (le_of_lt hx_pos) hq_nn
  have hF1 : F θ.A x L ≤ F A_max x L := F_mono_A θ.hA.2 hx_pos hL_nn
  have hF2 : F A_max x L ≤ F A_max box.xR L := F_mono_K hA_nn hx_pos hmem.2.1 hL_nn
  have hF3 : F A_max box.xR L ≤ F A_max box.xR box.LR :=
    F_mono_L hA_nn hxR_pos hL_nn hmem.2.2.2.2.2
  linarith [hmem.2.2.1]

/-- Caja 3D infactible: si el consumo máximo de esquina es `≤ 0`, ningún punto de la caja tiene `c > 0`. -/
theorem staying_box_infeasible_sound (box : Box3D) (hxL : 0 < box.xL) (hLL : 0 ≤ box.LL)
    (hinfeas : q_max * box.xR + F A_max box.xR box.LR - box.yL ≤ 0) :
    ∀ (θ : Params) (x y L : ℝ), box.mem x y L →
      0 < θ.q * x + F θ.A x L - y → False := by
  intro θ x y L hmem hc
  linarith [consumption_le_box_corner θ box hxL hLL hmem]

/-- Caja 3D factible certificada: la cota de intervalo en la caja implica la desigualdad
    de Bellman de permanencia para todo `θ ∈ P` y todo `(x, y, L) ∈ box`. -/
theorem staying_box_feasible_sound (B : ℝ → ℝ) (box : Box3D)
    {c_ub lc_ub lL_ub B_lo B_hi : ℝ}
    (hxL : 0 < box.xL) (hLL : 0 ≤ box.LL) (hLR : box.LR < 1)
    (hc_ub : q_max * box.xR + F A_max box.xR box.LR - box.yL ≤ c_ub)
    (hlc_ub : ∀ c, 0 < c → c ≤ c_ub → Real.log c ≤ lc_ub)
    (hlL_ub : Real.log (1 - box.LL) ≤ lL_ub)
    (hlL_np : lL_ub ≤ 0)
    (hB_lo : ∀ x, box.xL ≤ x → x ≤ box.xR → B_lo ≤ B x)
    (hB_hi : ∀ y, box.yL ≤ y → y ≤ box.yR → B y ≤ B_hi)
    (hcert : max (eta_min * lc_ub) (eta_max * lc_ub) + (1 - eta_max) * lL_ub +
      max (beta_min * B_hi) (beta_max * B_hi) - B_lo ≤ 0) :
    ∀ (θ : Params) (x y L : ℝ), box.mem x y L →
      0 < θ.q * x + F θ.A x L - y →
      u θ.η (θ.q * x + F θ.A x L - y) L + θ.β * B y ≤ B x := by
  intro θ x y L hmem hc
  have hc_le : θ.q * x + F θ.A x L - y ≤ c_ub :=
    le_trans (consumption_le_box_corner θ box hxL hLL hmem) hc_ub
  have hlogc : Real.log (θ.q * x + F θ.A x L - y) ≤ lc_ub := hlc_ub _ hc hc_le
  have h1mL_pos : 0 < 1 - L := by linarith [hmem.2.2.2.2.2, hLR]
  have hlogL : Real.log (1 - L) ≤ lL_ub :=
    le_trans (Real.log_le_log h1mL_pos (by linarith [hmem.2.2.2.2.1])) hlL_ub
  have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
  have hterm_c : θ.η * Real.log (θ.q * x + F θ.A x L - y) ≤
      max (eta_min * lc_ub) (eta_max * lc_ub) := by
    have h1 := mul_le_mul_of_nonneg_left hlogc hη_nn
    by_cases hlc : 0 ≤ lc_ub
    · exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right θ.hη.2 hlc) (le_max_right _ _))
    · push_neg at hlc
      exact le_trans h1 (le_trans (mul_le_mul_of_nonpos_right θ.hη.1 (le_of_lt hlc))
        (le_max_left _ _))
  have hterm_L : (1 - θ.η) * Real.log (1 - L) ≤ (1 - eta_max) * lL_ub := by
    have h1 := mul_le_mul_of_nonneg_left hlogL h1mη_nn
    have h2 := mul_le_mul_of_nonpos_right (show 1 - eta_max ≤ 1 - θ.η by linarith [θ.hη.2]) hlL_np
    linarith
  have hβ_nn : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have hterm_B : θ.β * B y ≤ max (beta_min * B_hi) (beta_max * B_hi) := by
    have h1 := mul_le_mul_of_nonneg_left (hB_hi y hmem.2.2.1 hmem.2.2.2.1) hβ_nn
    by_cases hBh : 0 ≤ B_hi
    · exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right θ.hβ.2 hBh) (le_max_right _ _))
    · push_neg at hBh
      exact le_trans h1 (le_trans (mul_le_mul_of_nonpos_right θ.hβ.1 (le_of_lt hBh))
        (le_max_left _ _))
  have hBx := hB_lo x hmem.1 hmem.2.1
  unfold u
  linarith

/-- Composición de recubrimiento finito de cajas 3D:
    si una lista finita de cajas certificadas cubre `[b_m, h_m)^2 × [0, 1)`, entonces `B`
    satisface la desigualdad de permanencia en todo el dominio. -/
theorem staying_cover_sound (B : ℝ → ℝ) (b_m h_m : ℝ) (boxes : List Box3D)
    (hcover : ∀ x y L, b_m ≤ x ∧ x < h_m → b_m ≤ y ∧ y < h_m → 0 ≤ L ∧ L < 1 →
      ∃ box ∈ boxes, box.mem x y L)
    (hvalid : ∀ box ∈ boxes, ∀ (θ : Params) (x y L : ℝ), box.mem x y L →
      0 < θ.q * x + F θ.A x L - y →
      u θ.η (θ.q * x + F θ.A x L - y) L + θ.β * B y ≤ B x) :
    ∀ (θ : Params) (x y L : ℝ),
      b_m ≤ x ∧ x < h_m → b_m ≤ y ∧ y < h_m → 0 ≤ L ∧ L < 1 →
      0 < θ.q * x + F θ.A x L - y →
      u θ.η (θ.q * x + F θ.A x L - y) L + θ.β * B y ≤ B x := by
  intro θ x y L hx hy hL hc
  obtain ⟨box, hbox, hmem⟩ := hcover x y L hx hy hL
  exact hvalid box hbox θ x y L hmem hc

/-! ## 4. Corrección de super-barreras (`Psi`) y subsoluciones testigo (`W`) -/

/-- Toda super-barrera certificada `Psi` acota superiormente cualquier trayectoria factible
    de horizonte finito `T`. -/
theorem super_barrier_finite_sound {β : ℝ} (hβ : 0 ≤ β) (Psi : ℝ → ℝ)
    (u_seq x : ℕ → ℝ) (T : ℕ)
    (hsuper : ∀ t < T, u_seq t + β * Psi (x (t + 1)) ≤ Psi (x t)) :
    (∑ t ∈ range T, β ^ t * u_seq t) + β ^ T * Psi (x T) ≤ Psi (x 0) := by
  linarith [telescoping_bellman hβ Psi u_seq x T hsuper]

/-- Toda subsolución testigo certificada `W` acota inferiormente el valor descontado
    alcanzado por su política asociada en cualquier horizonte finito `T`. -/
theorem witness_subsolution_finite_sound {β : ℝ} (hβ : 0 ≤ β) (W : ℝ → ℝ)
    (u_seq x : ℕ → ℝ) (T : ℕ)
    (hsub : ∀ t < T, W (x t) ≤ u_seq t + β * W (x (t + 1))) :
    W (x 0) ≤ (∑ t ∈ range T, β ^ t * u_seq t) + β ^ T * W (x T) := by
  have hneg : ∀ t < T, (-u_seq t) + β * (-W (x (t + 1))) ≤ -W (x t) := by
    intro t ht; linarith [hsub t ht]
  have htel := telescoping_bellman hβ (fun y => -W y) (fun t => -u_seq t) x T hneg
  have hsum : ∑ t ∈ range T, β ^ t * (-u_seq t) = -(∑ t ∈ range T, β ^ t * u_seq t) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => by ring
  rw [hsum] at htel
  linarith

/-! ## 5. Certificación en el kernel de la compresión de horizontes (Casos 1 y 4) -/

/-- Caso 1 (testigo MR + `B_net` de 22 nodos): $\tau_H \le 9$ certificado en el kernel. -/
theorem case1_deadline_9 (θ : Params) (B W Psi : ℝ → ℝ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 9, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 9, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 9, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi (x 9))
    (hB_stay : ∀ t < 9,
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t) + θ.β * B (x (t + 1)) ≤ B (x t))
    (hm_inf : ∀ y, b ≤ y ∧ y < h → (191434 / 10000 : ℝ) ≤ W y - B y)
    (hM_sup : ∀ y, b ≤ y ∧ y < h → Psi y - B y ≤ (245959 / 10000 : ℝ)) :
    (∑ t ∈ range 9, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 9 * V_cont < W (x 0) :=
  cegis_staying_deadline_sound θ 9 b h (191434 / 10000) (245959 / 10000) B W Psi x L V_cont
    hx hL hc hV hB_stay hm_inf hM_sup (by norm_num) (by unfold beta_max; norm_num)

/-- Caso 1 completo (`W_net`, `Psi_net`, `B_net` de CEGIS): $\tau_H \le 6$ certificado en el kernel. -/
theorem case1_deadline_6 (θ : Params) (B W Psi : ℝ → ℝ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 6, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 6, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 6, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi (x 6))
    (hB_stay : ∀ t < 6,
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t) + θ.β * B (x (t + 1)) ≤ B (x t))
    (hm_inf : ∀ y, b ≤ y ∧ y < h → (207209 / 10000 : ℝ) ≤ W y - B y)
    (hM_sup : ∀ y, b ≤ y ∧ y < h → Psi y - B y ≤ (242819 / 10000 : ℝ)) :
    (∑ t ∈ range 6, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 6 * V_cont < W (x 0) :=
  cegis_staying_deadline_sound θ 6 b h (207209 / 10000) (242819 / 10000) B W Psi x L V_cont
    hx hL hc hV hB_stay hm_inf hM_sup (by norm_num) (by unfold beta_max; norm_num)

/-- Caso 4 (régimen AK): $\tau_H \le 4$ certificado en el kernel. -/
theorem case4_ak_deadline_4 (θ : Params) (B W Psi : ℝ → ℝ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 4, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 4, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 4, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi (x 4))
    (hB_stay : ∀ t < 4,
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t) + θ.β * B (x (t + 1)) ≤ B (x t))
    (hm_inf : ∀ y, b ≤ y ∧ y < h → (266166 / 1000 : ℝ) ≤ W y - B y)
    (hM_sup : ∀ y, b ≤ y ∧ y < h → Psi y - B y ≤ (295931 / 1000 : ℝ)) :
    (∑ t ∈ range 4, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 4 * V_cont < W (x 0) :=
  cegis_staying_deadline_sound θ 4 b h (266166 / 1000) (295931 / 1000) B W Psi x L V_cont
    hx hL hc hV hB_stay hm_inf hM_sup (by norm_num) (by unfold beta_max; norm_num)

end

end MVS.CEGIS
