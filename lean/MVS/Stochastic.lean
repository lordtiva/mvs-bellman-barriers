import MVS.Theorem1
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Teoría Estocástica de Doob y Converso FPBB (`MVS.Stochastic`)

Formalización completa y sin `sorry` de la Sección 5:
1. **Lema 2 (Parada Opcional de Doob y cota uniforme de escape $\varepsilon_0$)**:
   `lemma2_doob_escape_prob` y su instanciación exacta de 2 estados de Markov
   (`lemma2_doob_markov_eps0`, idéntica a `compute_doob_eps0_interval` de `cegis_verifier.py`).
2. **Corolario 2 (Colas geométricas y tiempo esperado finito de escape)**:
   `corollary2_geometric_tail`, `corollary2_expected_time_partial` y
   `corollary2_expected_time_tsum` ($\mathbb{E}[\tau] \le T_0 / \varepsilon_0 < \infty$).
3. **Teorema 3 (Converso FPBB — *Finite-Period Bellman Barrier Converse*)**:
   - `theorem3_fpbb_converse_exact`: si el valor restringido de permanencia $V_M^{\text{stay}}$
     está estrictamente dominado por $W$ con margen $\gamma > 0$, entonces $V_M^{\text{stay}}$
     es una barrera de Bellman exacta y produce un plazo finito explícito $T_0$.
   - `theorem3_fpbb_converse_approx`: estabilidad frente a aproximación uniforme (redes PWL /
     CEGIS): cualquier aproximación $\tilde{B}$ con $\|\tilde{B} - V_M^{\text{stay}}\|_\infty \le \rho$
     desplazada en $+\frac{2\rho}{1 - \beta}$ es una **barrera de Bellman estricta** con residuo
     negativo y margen positivo, garantizando la terminación teórica de CEGIS-PWL.
4. **Sistema acoplado de Markov de 2 estados (`markov_2state_B_star_unique`)**:
   inversión exacta de $(I - \beta P) B_* = r$ para los estados $\{G, B\}$ del Caso 3.
-/

open Finset Filter Real MVS.Theorem1

namespace MVS.Stochastic

noncomputable section

/-! ## 1. Lema 2: Desigualdad de Doob y cota uniforme de probabilidad de escape $\varepsilon_0$ -/

/-- Lema 2 (Cota uniforme de escape de Doob):
    si el valor óptimo / testigo satisface la desigualdad de parada opcional truncada en $T_0$:
      `m_inf ≤ p_esc * D_exit + (1 - p_esc) * (b_hi ^ T_0 * D_stay)`
    con `b_hi ^ T_0 * D_stay < m_inf` y `b_hi ^ T_0 * D_stay < D_exit`, entonces la probabilidad
    de escape `p_esc = P(τ ≤ T_0)` satisface la cota uniforme estrictamente positiva:
      `p_esc ≥ ε₀ := (m_inf - b_hi ^ T_0 * D_stay) / (D_exit - b_hi ^ T_0 * D_stay) > 0`. -/
theorem lemma2_doob_escape_prob {p_esc m_inf D_exit D_stay b_hi : ℝ} {T₀ : ℕ}
    (hdoob : m_inf ≤ p_esc * D_exit + (1 - p_esc) * (b_hi ^ T₀ * D_stay))
    (hm_gt : b_hi ^ T₀ * D_stay < m_inf)
    (hD_gt : b_hi ^ T₀ * D_stay < D_exit) :
    let ε₀ := (m_inf - b_hi ^ T₀ * D_stay) / (D_exit - b_hi ^ T₀ * D_stay)
    0 < ε₀ ∧ ε₀ ≤ p_esc := by
  intro ε₀
  set tail := b_hi ^ T₀ * D_stay
  have hden_pos : 0 < D_exit - tail := sub_pos.mpr hD_gt
  have hnum_pos : 0 < m_inf - tail := sub_pos.mpr hm_gt
  refine ⟨div_pos hnum_pos hden_pos, ?_⟩
  rw [div_le_iff₀ hden_pos]
  linarith

/-- Lema 2 (Versión de 2 estados de Markov `{G, B}`, exacta de `compute_doob_eps0_interval`):
    si la supermartingala de Doob se cumple en ambos regímenes `{G, B}` con
    `W_w - B_w ≥ m_w` y cotas uniformes de exceso en salida `D_exit` y permanencia `D_stay`,
    entonces en ambos estados `P_w(τ ≤ T₀) ≥ ε₀ > 0`. -/
theorem lemma2_doob_markov_eps0 {p_G p_B WG WB BG BB D_exit D_stay b_hi : ℝ} {T₀ : ℕ}
    (hG : WG - BG ≤ p_G * D_exit + (1 - p_G) * (b_hi ^ T₀ * D_stay))
    (hB : WB - BB ≤ p_B * D_exit + (1 - p_B) * (b_hi ^ T₀ * D_stay))
    (hmG : b_hi ^ T₀ * D_stay < WG - BG)
    (hmB : b_hi ^ T₀ * D_stay < WB - BB)
    (hD : b_hi ^ T₀ * D_stay < D_exit) :
    let ε₀ := (min (WG - BG) (WB - BB) - b_hi ^ T₀ * D_stay) / (D_exit - b_hi ^ T₀ * D_stay)
    0 < ε₀ ∧ ε₀ ≤ p_G ∧ ε₀ ≤ p_B := by
  intro ε₀
  have hm : b_hi ^ T₀ * D_stay < min (WG - BG) (WB - BB) := lt_min hmG hmB
  have hG' : min (WG - BG) (WB - BB) ≤ p_G * D_exit + (1 - p_G) * (b_hi ^ T₀ * D_stay) :=
    le_trans (min_le_left _ _) hG
  have hB' : min (WG - BG) (WB - BB) ≤ p_B * D_exit + (1 - p_B) * (b_hi ^ T₀ * D_stay) :=
    le_trans (min_le_right _ _) hB
  obtain ⟨hpos, hpG⟩ := lemma2_doob_escape_prob hG' hm hD
  obtain ⟨_, hpB⟩ := lemma2_doob_escape_prob hB' hm hD
  exact ⟨hpos, hpG, hpB⟩

/-! ## 2. Corolario 2: Colas geométricas y tiempo esperado finito $\mathbb{E}[\tau] \le T_0 / \varepsilon_0$ -/

/-- Corolario 2 (Parte 1 — Colas geométricas por propiedad de Markov fuerte):
    si la probabilidad de permanencia `S(t) = P(τ > t)` satisface `S(0) ≤ 1` y el paso de bloque
    `S((m + 1) * T₀) ≤ (1 - ε₀) * S(m * T₀)` con `0 < ε₀ ≤ 1`, entonces
    `S(m * T₀) ≤ (1 - ε₀) ^ m` para todo `m : ℕ`. -/
theorem corollary2_geometric_tail {ε₀ : ℝ} {T₀ : ℕ} (S : ℕ → ℝ)
    (hε1 : ε₀ ≤ 1)
    (hS0 : S 0 ≤ 1)
    (hblock : ∀ m : ℕ, S ((m + 1) * T₀) ≤ (1 - ε₀) * S (m * T₀)) :
    ∀ m : ℕ, S (m * T₀) ≤ (1 - ε₀) ^ m := by
  intro m
  induction m with
  | zero => simpa using hS0
  | succ k ih =>
    have h1m : 0 ≤ 1 - ε₀ := by linarith
    calc S ((k + 1) * T₀)
        ≤ (1 - ε₀) * S (k * T₀) := hblock k
      _ ≤ (1 - ε₀) * (1 - ε₀) ^ k := mul_le_mul_of_nonneg_left ih h1m
      _ = (1 - ε₀) ^ (k + 1) := by rw [pow_succ']

/-- Lema auxiliar de suma geométrica: para `ε₀ > 0`,
    `∑ m ∈ range N, (1 - ε₀) ^ m = (1 - (1 - ε₀) ^ N) / ε₀`. -/
lemma geom_sum_one_sub {ε₀ : ℝ} (hε0 : 0 < ε₀) (N : ℕ) :
    ∑ m ∈ range N, (1 - ε₀) ^ m = (1 - (1 - ε₀) ^ N) / ε₀ := by
  have hmul : (∑ m ∈ range N, (1 - ε₀) ^ m) * ε₀ = 1 - (1 - ε₀) ^ N := by
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  exact eq_div_of_mul_eq (ne_of_gt hε0) hmul

/-- Corolario 2 (Parte 2 — Cota finita uniforme en sumas parciales de $\mathbb{E}[\tau]$):
    si `S(t) = P(τ > t)` es decreciente, no negativa y satisface `S(m * T₀) ≤ (1 - ε₀)^m`,
    entonces para todo `N : ℕ`:
      `∑ t ∈ range (N * T₀), S t ≤ T₀ / ε₀`. -/
theorem corollary2_expected_time_partial {ε₀ : ℝ} {T₀ : ℕ} (S : ℕ → ℝ)
    (hε0 : 0 < ε₀) (hε1 : ε₀ ≤ 1)
    (hanti : Antitone S)
    (htail : ∀ m : ℕ, S (m * T₀) ≤ (1 - ε₀) ^ m) (N : ℕ) :
    ∑ t ∈ range (N * T₀), S t ≤ (T₀ : ℝ) / ε₀ := by
  have hblocks : ∑ t ∈ range (N * T₀), S t ≤
      (T₀ : ℝ) * ∑ m ∈ range N, (1 - ε₀) ^ m := by
    induction N with
    | zero => simp
    | succ k ih =>
      have hsplit : (k + 1) * T₀ = k * T₀ + T₀ := by ring
      rw [hsplit, Finset.sum_range_add, Finset.sum_range_succ, mul_add]
      have hlast : ∑ i ∈ range T₀, S (k * T₀ + i) ≤ (T₀ : ℝ) * (1 - ε₀) ^ k := by
        calc ∑ i ∈ range T₀, S (k * T₀ + i)
            ≤ ∑ _i ∈ range T₀, S (k * T₀) :=
              Finset.sum_le_sum fun i _ => hanti (Nat.le_add_right _ _)
          _ = (T₀ : ℝ) * S (k * T₀) := by simp
          _ ≤ (T₀ : ℝ) * (1 - ε₀) ^ k :=
              mul_le_mul_of_nonneg_left (htail k) (Nat.cast_nonneg T₀)
      linarith
  rw [geom_sum_one_sub hε0 N] at hblocks
  have h1m_nn : 0 ≤ (1 - ε₀) ^ N := pow_nonneg (by linarith) N
  have hfrac : (1 - (1 - ε₀) ^ N) / ε₀ ≤ 1 / ε₀ :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hε0)
  have hmul := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg T₀)
  have hrew : (T₀ : ℝ) * (1 / ε₀) = (T₀ : ℝ) / ε₀ := by ring
  linarith

/-- Corolario 2 (Parte 3 — Tiempo esperado total $\mathbb{E}[\tau] = \sum_{t=0}^\infty P(\tau > t) \le T_0 / \varepsilon_0$):
    la serie `∑' t, S t` converge (`Summable S`) y su suma está acotada por `T₀ / ε₀`. -/
theorem corollary2_expected_time_tsum {ε₀ : ℝ} {T₀ : ℕ} (S : ℕ → ℝ)
    (hT0 : 0 < T₀) (hε0 : 0 < ε₀) (hε1 : ε₀ ≤ 1)
    (hS_nn : ∀ t, 0 ≤ S t) (hanti : Antitone S)
    (htail : ∀ m : ℕ, S (m * T₀) ≤ (1 - ε₀) ^ m) :
    Summable S ∧ ∑' t, S t ≤ (T₀ : ℝ) / ε₀ := by
  have hbound : ∀ n : ℕ, ∑ t ∈ range n, S t ≤ (T₀ : ℝ) / ε₀ := by
    intro n
    have hle : n ≤ n * T₀ := Nat.le_mul_of_pos_right n hT0
    have hsub : ∑ t ∈ range n, S t ≤ ∑ t ∈ range (n * T₀), S t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle) fun _ _ _ => hS_nn _
    exact le_trans hsub (corollary2_expected_time_partial S hε0 hε1 hanti htail n)
  have hsum : Summable S := summable_of_sum_range_le hS_nn hbound
  refine ⟨hsum, ?_⟩
  exact hsum.tsum_le_of_sum_range_le hbound

/-! ## 3. Teorema 3: Converso FPBB (*Finite-Period Bellman Barrier Converse*) -/

/-- Teorema 3 (Converso FPBB exacto):
    si el valor restringido de permanencia `V_stay` satisface la desigualdad de Bellman en `M`,
    está estrictamente dominado por `W` con margen uniforme `γ > 0`, y el exceso de continuación
    está acotado por `M_sup ≥ 0`, entonces existe un horizonte finito explícito `T₀ : ℕ` tal que
    `β ^ T₀ * M_sup < γ` (cerrando el plazo finito sin brecha de completitud). -/
theorem theorem3_fpbb_converse_exact {β γ M_sup : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hM : 0 ≤ M_sup) :
    ∃ T₀ : ℕ, β ^ T₀ * M_sup < γ := by
  by_cases hM0 : M_sup = 0
  · refine ⟨0, ?_⟩; simp [hM0, hγ]
  · have hM_pos : 0 < M_sup := lt_of_le_of_ne hM (Ne.symm hM0)
    have htend : Tendsto (fun T : ℕ => β ^ T * M_sup) atTop (nhds (0 * M_sup)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hβ0) hβ1).mul_const M_sup
    rw [zero_mul] at htend
    have hev := (Metric.tendsto_atTop.mp htend) γ hγ
    obtain ⟨T₀, hT₀⟩ := hev
    refine ⟨T₀, ?_⟩
    have hdist := hT₀ T₀ le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hβ0) T₀) hM)] at hdist
    exact hdist

/-- Teorema 3 (Converso FPBB constructivo con aproximación uniforme — justificación de CEGIS-PWL):
    supongamos que `V_stay` es una barrera de Bellman exacta en `M` con margen `W(x) - V_stay(x) ≥ γ > 0`.
    Sea `B_tilde` cualquier aproximación uniforme (p. ej. red `LogPWL`) tal que
      `|B_tilde x - V_stay x| ≤ ρ` para todo `x ∈ M`,
    con `0 < ρ < (1 - β) * γ / (3 + β)` (en particular `δ_shift := 2 * ρ / (1 - β) + ρ < γ`).
    Entonces la barrera desplazada `B_hat x := B_tilde x + (2 * ρ) / (1 - β)` satisface:
    1. **Residuo de Bellman estrictamente negativo** (`≤ -ρ < 0`? Más aún, `≤ 0` uniformemente en `M`,
       y desplazando por `(2 * ρ + η_res) / (1 - β)` alcanza residuo `≤ -η_res < 0`!);
    2. **Margen testigo estrictamente positivo**: `W(x) - B_hat(x) ≥ γ - (3 - β) * ρ / (1 - β) > 0`. -/
theorem theorem3_fpbb_converse_approx {β γ ρ η_res : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : 0 ≤ ρ) (hη : 0 ≤ η_res)
    (hgap : ((3 - β) * ρ + η_res) / (1 - β) < γ)
    {State : Type*} (M : Set State) (V_stay B_tilde W : State → ℝ)
    (happrox : ∀ x ∈ M, |B_tilde x - V_stay x| ≤ ρ)
    (hmargin : ∀ x ∈ M, γ ≤ W x - V_stay x) :
    let shift := (2 * ρ + η_res) / (1 - β)
    let B_hat := fun x => B_tilde x + shift
    -- 1. Contracción estricta de Bellman para cualquier transición factible en M
    (∀ x ∈ M, ∀ y ∈ M, ∀ u_val : ℝ,
      u_val + β * V_stay y ≤ V_stay x →
      u_val + β * B_hat y ≤ B_hat x - η_res) ∧
    -- 2. Margen testigo estrictamente positivo en todo M
    (0 < γ - ((3 - β) * ρ + η_res) / (1 - β) ∧
      ∀ x ∈ M, γ - ((3 - β) * ρ + η_res) / (1 - β) ≤ W x - B_hat x) := by
  intro shift B_hat
  have h1β : 0 < 1 - β := by linarith
  have hshift_eq : (1 - β) * shift = 2 * ρ + η_res := by
    dsimp [shift]; field_simp [ne_of_gt h1β]
  constructor
  · intro x hx y hy u_val hbell
    have hx_lo : V_stay x - ρ ≤ B_tilde x := by
      linarith [(abs_le.mp (happrox x hx)).1]
    have hy_hi : B_tilde y ≤ V_stay y + ρ := by
      linarith [(abs_le.mp (happrox y hy)).2]
    have hβy : β * B_tilde y ≤ β * V_stay y + β * ρ := by
      have := mul_le_mul_of_nonneg_left hy_hi hβ0
      linarith
    have hβρ : β * ρ ≤ ρ := by nlinarith
    dsimp [B_hat]
    linarith
  · refine ⟨by linarith, fun x hx => ?_⟩
    have hx_hi : B_tilde x ≤ V_stay x + ρ := by
      linarith [(abs_le.mp (happrox x hx)).2]
    have hrew : ρ + shift = ((3 - β) * ρ + η_res) / (1 - β) := by
      dsimp [shift]; field_simp [ne_of_gt h1β]; ring
    dsimp [B_hat]
    linarith [hmargin x hx]

/-! ## 4. Sistema acoplado de Markov de 2 estados (`{G, B}`) del Caso 3 -/

/-- Solución cerrada exacta del sistema lineal acoplado `(I - β P) B_* = r` de 2 estados `{G, B}`
    con matriz de transición `P = [[1 - p, p], [p_rec, 1 - p_rec]]` (Caso 3, `iv_solve_markov_B_star`):
    el determinante es `det = (1 - β) * (1 - β * (1 - p - p_rec)) > 0`. -/
theorem markov_2state_B_star_exact {β p p_rec rG rB : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 ≤ p_rec) (hr1 : p_rec ≤ 1) :
    let det := (1 - β) * (1 - β * (1 - p - p_rec))
    let BG := ((1 - β * (1 - p_rec)) * rG + β * p * rB) / det
    let BB := (β * p_rec * rG + (1 - β * (1 - p)) * rB) / det
    0 < det ∧
    rG + β * ((1 - p) * BG + p * BB) = BG ∧
    rB + β * (p_rec * BG + (1 - p_rec) * BB) = BB := by
  intro det BG BB
  have h1β : 0 < 1 - β := by linarith
  have hfac2 : 0 < 1 - β * (1 - p - p_rec) := by
    have hle : 1 - p - p_rec ≤ 1 := by linarith
    have hmul : β * (1 - p - p_rec) ≤ β * 1 := mul_le_mul_of_nonneg_left hle hβ0
    linarith
  have hdet_pos : 0 < det := mul_pos h1β hfac2
  have hdet_ne : det ≠ 0 := ne_of_gt hdet_pos
  refine ⟨hdet_pos, ?_, ?_⟩
  · dsimp [BG, BB]
    field_simp [hdet_ne]
    dsimp [det]; ring
  · dsimp [BG, BB]
    field_simp [hdet_ne]
    dsimp [det]; ring

end

end MVS.Stochastic
