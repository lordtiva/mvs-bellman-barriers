import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.style.header false

open Finset Filter Real

namespace MVS.Theorem2

/-! ## 1. Parámetros CES generales y función de producción reescalada -/

/-- Parámetros primitivos generales de la Sección 4 (régimen paciente β θ > 1). -/
structure CESParams where
  d : ℝ          -- d = -ρ > 0
  r : ℝ          -- r = θ - 1 ∈ (0, 1)
  w : ℝ          -- peso CES w ∈ (0, 1)
  β : ℝ          -- factor de descuento ∈ (0, 1)
  δ : ℝ          -- depreciación ∈ (0, 1)
  η : ℝ          -- peso del consumo ∈ (0, 1)
  hd : 0 < d
  hr0 : 0 < r
  hr1 : r < 1
  hw0 : 0 < w
  hw1 : w < 1
  hβ0 : 0 < β
  hβ1 : β < 1
  hβθ : 1 < β * (1 + r)
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hη0 : 0 < η
  hη1 : η < 1

namespace CESParams

variable (p : CESParams)

def θ : ℝ := 1 + p.r
def q : ℝ := 1 - p.δ
noncomputable def cw : ℝ := (1 - p.w) / p.w
noncomputable def cK : ℝ := p.w ^ (-p.θ / p.d)
noncomputable def k_star : ℝ := (p.δ / p.cK) ^ (1 / p.r)

lemma hθ_gt1 : 1 < p.θ := by unfold θ; linarith [p.hr0]
lemma hθ_pos : 0 < p.θ := by linarith [p.hθ_gt1]
lemma hq_pos : 0 < p.q := by unfold q; linarith [p.hδ1]
lemma hcw_pos : 0 < p.cw := div_pos (by linarith [p.hw1]) p.hw0
lemma hcK_pos : 0 < p.cK := Real.rpow_pos_of_pos p.hw0 _
lemma hk_star_pos : 0 < p.k_star := Real.rpow_pos_of_pos (div_pos p.hδ0 p.hcK_pos) _

/-- Producción CES general F_A(K, L) = A * cK * K^θ * (1 + cw * (K / L)^d)^(-θ / d). -/
noncomputable def F_ces (A K L : ℝ) : ℝ :=
  A * p.cK * K ^ p.θ * (1 + p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d)

/-- Producción normalizada f_A(k, L) = A^(1/r) * F_A(A^(-1/r) * k, L). -/
noncomputable def f_norm (A k L : ℝ) : ℝ :=
  A ^ (1 / p.r) * p.F_ces A (A ^ (-1 / p.r) * k) L

/-- Identidad exacta del producto normalizado (pág. 10). -/
theorem f_norm_eq {A k L : ℝ} (hA : 0 < A) (hk : 0 < k) (hL : 0 < L) :
    p.f_norm A k L =
      p.cK * k ^ p.θ * (1 + p.cw * (k / (A ^ (1 / p.r) * L)) ^ p.d) ^ (-p.θ / p.d) := by
  unfold f_norm F_ces
  have hAr_pos : 0 < A ^ (1 / p.r) := Real.rpow_pos_of_pos hA _
  have hAnr_pos : 0 < A ^ (-1 / p.r) := Real.rpow_pos_of_pos hA _
  have hratio : A ^ (-1 / p.r) * k / L = k / (A ^ (1 / p.r) * L) := by
    have hinv : A ^ (-1 / p.r) = (A ^ (1 / p.r))⁻¹ := by
      rw [show (-1 / p.r : ℝ) = -(1 / p.r) by ring, Real.rpow_neg (le_of_lt hA)]
    rw [hinv]; field_simp [ne_of_gt hAr_pos, ne_of_gt hL]
  rw [hratio, Real.mul_rpow (le_of_lt hAnr_pos) (le_of_lt hk),
      ← Real.rpow_mul (le_of_lt hA)]
  have hexp : 1 / p.r + 1 + (-1 / p.r) * p.θ = 0 := by
    unfold θ; field_simp [ne_of_gt p.hr0]; ring
  have hA_cancel : A ^ (1 / p.r) * A * A ^ ((-1 / p.r) * p.θ) = 1 := by
    calc A ^ (1 / p.r) * A * A ^ ((-1 / p.r) * p.θ)
        = A ^ (1 / p.r) * A ^ (1 : ℝ) * A ^ ((-1 / p.r) * p.θ) := by rw [Real.rpow_one]
      _ = A ^ (1 / p.r + 1) * A ^ ((-1 / p.r) * p.θ) := by rw [← Real.rpow_add hA]
      _ = A ^ (1 / p.r + 1 + (-1 / p.r) * p.θ) := by rw [← Real.rpow_add hA]
      _ = A ^ (0 : ℝ) := by rw [hexp]
      _ = 1 := Real.rpow_zero A
  calc A ^ (1 / p.r) * (A * p.cK * (A ^ ((-1 / p.r) * p.θ) * k ^ p.θ) *
          (1 + p.cw * (k / (A ^ (1 / p.r) * L)) ^ p.d) ^ (-p.θ / p.d))
      = (A ^ (1 / p.r) * A * A ^ ((-1 / p.r) * p.θ)) *
          (p.cK * k ^ p.θ * (1 + p.cw * (k / (A ^ (1 / p.r) * L)) ^ p.d) ^ (-p.θ / p.d)) := by ring
    _ = p.cK * k ^ p.θ * (1 + p.cw * (k / (A ^ (1 / p.r) * L)) ^ p.d) ^ (-p.θ / p.d) := by
          rw [hA_cancel, one_mul]

/-! ## 2. Teorema 2 (Parte 2.1): Isomorfismo finito de oferta laboral fija -/

/-- Homogeneidad de grado θ = 1 + r: F_A(L̄ K̃, L̄) = L̄ * F_{A L̄^r}(K̃, 1). -/
theorem F_ces_homog {A Ktilde Lbar : ℝ} (hK : 0 < Ktilde) (hL : 0 < Lbar) :
    p.F_ces A (Lbar * Ktilde) Lbar = Lbar * p.F_ces (A * Lbar ^ p.r) Ktilde 1 := by
  unfold F_ces
  have hratio : Lbar * Ktilde / Lbar = Ktilde / 1 := by field_simp [ne_of_gt hL]
  rw [hratio, Real.mul_rpow (le_of_lt hL) (le_of_lt hK)]
  have hLpow : Lbar ^ p.θ = Lbar * Lbar ^ p.r := by
    unfold θ; rw [Real.rpow_add hL, Real.rpow_one]
  rw [hLpow]; ring

/-- Desplazamiento constante exacto de la utilidad finita en horizonte T bajo reescalamiento C_t = L̄ C̃_t. -/
theorem fixed_labor_utility_shift {Lbar : ℝ} (hL : 0 < Lbar) (Ctilde : ℕ → ℝ)
    (hC : ∀ t, 0 < Ctilde t) (T : ℕ) :
    ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (Lbar * Ctilde t)) =
      (∑ t ∈ range T, p.β ^ t * (p.η * Real.log (Ctilde t))) +
      (1 - p.β ^ T) / (1 - p.β) * (p.η * Real.log Lbar) := by
  have hterm : ∀ t, p.β ^ t * (p.η * Real.log (Lbar * Ctilde t)) =
      p.β ^ t * (p.η * Real.log (Ctilde t)) + p.β ^ t * (p.η * Real.log Lbar) := by
    intro t
    rw [Real.log_mul (ne_of_gt hL) (ne_of_gt (hC t))]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  have hgeom : (∑ t ∈ range T, p.β ^ t) * (1 - p.β) = 1 - p.β ^ T := by
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  have h1β : 1 - p.β ≠ 0 := by linarith [p.hβ1]
  have hsum : ∑ t ∈ range T, p.β ^ t = (1 - p.β ^ T) / (1 - p.β) :=
    eq_div_of_mul_eq h1β hgeom
  rw [hsum]

/-! ## 3. Teorema 2 (Parte 1): Expansión en 3 fases y convergencia A^(1/r) S_A → (δ/cK)^(1/r) -/

/-- Cota inferior uniforme del producto normalizado en K ≤ K_esc (independiente de A). -/
theorem f_norm_lower_bound {L₀ ε₁ : ℝ} (hL₀ : 0 < L₀) (hε0 : 0 < ε₁) (hε1 : ε₁ < 1) :
    ∃ K_esc > 0, ∀ {A k : ℝ}, 0 < A → 0 < k → A ^ (-1 / p.r) * k ≤ K_esc →
      p.cK * (1 - ε₁ / 2) * k ^ p.θ ≤ p.f_norm A k L₀ := by
  have h1m_pos : 0 < 1 - ε₁ / 2 := by linarith
  have h1m_lt1 : 1 - ε₁ / 2 < 1 := by linarith
  have hpow_gt1 : 1 < (1 - ε₁ / 2) ^ (-p.d / p.θ) := by
    have hexp_neg : -p.d / p.θ < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr p.hd) p.hθ_pos
    calc (1 : ℝ) = 1 ^ (-p.d / p.θ) := (Real.one_rpow _).symm
      _ < (1 - ε₁ / 2) ^ (-p.d / p.θ) := Real.rpow_lt_rpow_of_neg h1m_pos h1m_lt1 hexp_neg
  -- Elegimos K_esc tal que cw * (K_esc / L₀)^d = (1 - ε₁/2)^(-d/θ) - 1
  let B := ((1 - ε₁ / 2) ^ (-p.d / p.θ) - 1) / p.cw
  have hB_pos : 0 < B := div_pos (by linarith) p.hcw_pos
  refine ⟨L₀ * B ^ (1 / p.d), mul_pos hL₀ (Real.rpow_pos_of_pos hB_pos _), ?_⟩
  intro A k hA hk hK_le
  rw [p.f_norm_eq hA hk hL₀]
  have hAr_pos : 0 < A ^ (1 / p.r) := Real.rpow_pos_of_pos hA _
  have hratio_eq : k / (A ^ (1 / p.r) * L₀) = (A ^ (-1 / p.r) * k) / L₀ := by
    have hinv : A ^ (-1 / p.r) = (A ^ (1 / p.r))⁻¹ := by
      rw [show (-1 / p.r : ℝ) = -(1 / p.r) by ring, Real.rpow_neg (le_of_lt hA)]
    rw [hinv]; field_simp [ne_of_gt hAr_pos, ne_of_gt hL₀]
  have hratio_le : k / (A ^ (1 / p.r) * L₀) ≤ B ^ (1 / p.d) := by
    rw [hratio_eq, div_le_iff₀ hL₀]
    linarith
  have hratio_nn : 0 ≤ k / (A ^ (1 / p.r) * L₀) := by positivity
  have hd_le : (k / (A ^ (1 / p.r) * L₀)) ^ p.d ≤ B := by
    calc (k / (A ^ (1 / p.r) * L₀)) ^ p.d
        ≤ (B ^ (1 / p.d)) ^ p.d := Real.rpow_le_rpow hratio_nn hratio_le (le_of_lt p.hd)
      _ = B ^ ((1 / p.d) * p.d) := (Real.rpow_mul (le_of_lt hB_pos) _ _).symm
      _ = B ^ (1 : ℝ) := by rw [one_div_mul_cancel (ne_of_gt p.hd)]
      _ = B := Real.rpow_one B
  have h1p_le : 1 + p.cw * (k / (A ^ (1 / p.r) * L₀)) ^ p.d ≤ (1 - ε₁ / 2) ^ (-p.d / p.θ) := by
    have hmul := mul_le_mul_of_nonneg_left hd_le (le_of_lt p.hcw_pos)
    have hcwB : p.cw * B = (1 - ε₁ / 2) ^ (-p.d / p.θ) - 1 := by
      dsimp [B]; field_simp [ne_of_gt p.hcw_pos]
    linarith
  have h1p_pos : 0 < 1 + p.cw * (k / (A ^ (1 / p.r) * L₀)) ^ p.d := by
    have := p.hcw_pos; positivity
  have hpow_ge : 1 - ε₁ / 2 ≤
      (1 + p.cw * (k / (A ^ (1 / p.r) * L₀)) ^ p.d) ^ (-p.θ / p.d) := by
    have hneg : -p.θ / p.d ≤ 0 := le_of_lt (div_neg_of_neg_of_pos (neg_lt_zero.mpr p.hθ_pos) p.hd)
    have hstep := Real.rpow_le_rpow_of_nonpos h1p_pos h1p_le hneg
    have hcancel : ((1 - ε₁ / 2) ^ (-p.d / p.θ)) ^ (-p.θ / p.d) = 1 - ε₁ / 2 := by
      rw [← Real.rpow_mul (le_of_lt h1m_pos)]
      have : (-p.d / p.θ) * (-p.θ / p.d) = 1 := by
        field_simp [ne_of_gt p.hθ_pos, ne_of_gt p.hd]
      rw [this, Real.rpow_one]
    linarith
  have hfac : 0 ≤ p.cK * k ^ p.θ := mul_nonneg (le_of_lt p.hcK_pos) (Real.rpow_nonneg (le_of_lt hk) _)
  have := mul_le_mul_of_nonneg_left hpow_ge hfac
  linarith

/-- Fase I (escape lineal del cuello de botella): si k_{t+1} ≥ k_t + γ/2 con γ > 0,
    se alcanza cualquier nivel objetivo k₁ en a lo sumo T₁ = ⌈2(k₁ - k₀)/γ⌉ pasos. -/
theorem phase1_linear_escape {k₀ k₁ γ : ℝ} (hγ : 0 < γ) (k_seq : ℕ → ℝ)
    (h0 : k₀ ≤ k_seq 0) (hstep : ∀ t, k_seq t + γ / 2 ≤ k_seq (t + 1)) :
    let T₁ := Nat.ceil (2 * (k₁ - k₀) / γ)
    k₁ ≤ k_seq T₁ := by
  intro T₁
  have hind : ∀ t : ℕ, k₀ + (t : ℝ) * (γ / 2) ≤ k_seq t := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ n ih =>
      push_cast
      linarith [hstep n]
  have hceil : 2 * (k₁ - k₀) / γ ≤ (T₁ : ℝ) := Nat.le_ceil _
  have hmul : k₁ - k₀ ≤ (T₁ : ℝ) * (γ / 2) := by
    have := mul_le_mul_of_nonneg_right hceil (show 0 ≤ γ / 2 by linarith)
    have hrew : 2 * (k₁ - k₀) / γ * (γ / 2) = k₁ - k₀ := by field_simp [ne_of_gt hγ]
    linarith
  linarith [hind T₁]

/-- Fase II (crecimiento superexponencial): si k₀ ≥ 2 y k_{j+1} ≥ k_j^θ̃, entonces k_j ≥ 2^(θ̃^j). -/
theorem phase2_superexp {θ_tilde : ℝ} (hθt : 0 < θ_tilde) (k_seq : ℕ → ℝ)
    (h0 : 2 ≤ k_seq 0) (hstep : ∀ j, (k_seq j) ^ θ_tilde ≤ k_seq (j + 1)) :
    ∀ j : ℕ, (2 : ℝ) ^ (θ_tilde ^ j) ≤ k_seq j := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ n ih =>
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (θ_tilde ^ n) := Real.rpow_nonneg (by norm_num) _
    calc (2 : ℝ) ^ (θ_tilde ^ (n + 1))
        = (2 : ℝ) ^ (θ_tilde ^ n * θ_tilde) := by rw [pow_succ]
      _ = ((2 : ℝ) ^ (θ_tilde ^ n)) ^ θ_tilde := Real.rpow_mul (by norm_num) _ _
      _ ≤ (k_seq n) ^ θ_tilde := Real.rpow_le_rpow h2pos ih (le_of_lt hθt)
      _ ≤ k_seq (n + 1) := hstep n

/-- Cota log-logarítmica explícita del número de pasos J(A) de la Fase II para alcanzar A^(1/r) * K_esc. -/
theorem phase2_step_bound {θ_tilde K_esc : ℝ} (hθt : 1 < θ_tilde) (hK : 0 < K_esc) :
    ∃ C_J : ℝ, ∃ A_min > 1, ∀ A ≥ A_min,
      ∃ J : ℕ,
        A ^ (1 / p.r) * K_esc ≤ (2 : ℝ) ^ (θ_tilde ^ J) ∧
        (J : ℝ) ≤ Real.log (Real.log A) / Real.log θ_tilde + C_J := by
  have hlogθ : 0 < Real.log θ_tilde := Real.log_pos hθt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c0 := max 0 (Real.log (2 / (p.r * Real.log 2)) / Real.log θ_tilde)
  refine ⟨c0 + 1, Real.exp (max 2 (p.r * |Real.log K_esc|)), ?_, ?_⟩
  · exact Real.one_lt_exp_iff.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · intro A hA
    have hlogA_ge : max 2 (p.r * |Real.log K_esc|) ≤ Real.log A := by
      have hA_pos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
      rw [← Real.log_exp (max 2 (p.r * |Real.log K_esc|))]
      exact Real.log_le_log (Real.exp_pos _) hA
    have hlogA_ge2 : 2 ≤ Real.log A := le_trans (le_max_left _ _) hlogA_ge
    have hlogA_pos : 0 < Real.log A := by linarith
    have hloglogA_nn : 0 ≤ Real.log (Real.log A) := Real.log_nonneg (by linarith)
    have hA_pos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
    let x := Real.log (Real.log A) / Real.log θ_tilde + c0
    have hx_nn : 0 ≤ x := add_nonneg (div_nonneg hloglogA_nn (le_of_lt hlogθ)) (le_max_left _ _)
    let J := Nat.ceil x
    refine ⟨J, ?_, ?_⟩
    · -- Probamos log(A^(1/r) * K_esc) ≤ θ̃^J * log 2
      have hJ_ge : x ≤ (J : ℝ) := Nat.le_ceil x
      have h1 : Real.log (Real.log A) + Real.log (2 / (p.r * Real.log 2)) ≤
          (J : ℝ) * Real.log θ_tilde := by
        have hc0_ge : Real.log (2 / (p.r * Real.log 2)) / Real.log θ_tilde ≤ c0 := le_max_right _ _
        have hle : Real.log (Real.log A) / Real.log θ_tilde +
            Real.log (2 / (p.r * Real.log 2)) / Real.log θ_tilde ≤ (J : ℝ) := by
          dsimp [x] at hJ_ge; linarith
        have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hlogθ)
        have hrew : (Real.log (Real.log A) / Real.log θ_tilde +
            Real.log (2 / (p.r * Real.log 2)) / Real.log θ_tilde) * Real.log θ_tilde =
            Real.log (Real.log A) + Real.log (2 / (p.r * Real.log 2)) := by
          field_simp [ne_of_gt hlogθ]
        linarith
      have h2 : (2 / (p.r * Real.log 2)) * Real.log A ≤ θ_tilde ^ J := by
        have hpos_fac : 0 < 2 / (p.r * Real.log 2) := by have := p.hr0; positivity
        rw [← Real.exp_log (mul_pos hpos_fac hlogA_pos), Real.log_mul (ne_of_gt hpos_fac)
          (ne_of_gt hlogA_pos)]
        have hθJ : θ_tilde ^ J = Real.exp ((J : ℝ) * Real.log θ_tilde) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]; ring_nf
        rw [hθJ]
        exact Real.exp_le_exp.mpr (by linarith)
      have h3 : (1 / p.r) * Real.log A + Real.log K_esc ≤ θ_tilde ^ J * Real.log 2 := by
        have hK_le : Real.log K_esc ≤ (1 / p.r) * Real.log A := by
          have habs := le_trans (le_max_right _ _) hlogA_ge
          have hle := le_trans (le_abs_self (Real.log K_esc)) (by
            have := div_le_div_of_nonneg_right habs (le_of_lt p.hr0)
            have hrew : p.r * |Real.log K_esc| / p.r = |Real.log K_esc| := by
              field_simp [ne_of_gt p.hr0]
            linarith)
          have hrew : (1 / p.r) * Real.log A = Real.log A / p.r := by ring
          linarith
        have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hlog2)
        have hrew : 2 / (p.r * Real.log 2) * Real.log A * Real.log 2 = (2 / p.r) * Real.log A := by
          field_simp [ne_of_gt hlog2, ne_of_gt p.hr0]
        have h2r : (2 / p.r) * Real.log A = (1 / p.r) * Real.log A + (1 / p.r) * Real.log A := by ring
        linarith
      -- Exponenciamos para concluir A^(1/r) * K_esc ≤ 2^(θ̃^J)
      have hL : A ^ (1 / p.r) * K_esc = Real.exp ((1 / p.r) * Real.log A + Real.log K_esc) := by
        rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos hA_pos]; ring_nf
      have hR : (2 : ℝ) ^ (θ_tilde ^ J) = Real.exp (θ_tilde ^ J * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
      rw [hL, hR]
      exact Real.exp_le_exp.mpr h3
    · have hlt := Nat.ceil_lt_add_one hx_nn
      dsimp [J, x] at *
      linarith

/-- Cota clave de descuento en la Fase II/III (corazón de la Parte 1 y del Eslabón 2):
    si β θ̃ > 1 y J ≤ log(log A)/log θ̃ + C_J, entonces β^J * log A ≥ c₁ * (log A)^(1 - κ̃). -/
theorem discount_times_logA_lower {θ_tilde C_J : ℝ} {J : ℕ} {A : ℝ}
    (hθt : 1 < θ_tilde) (hβθt : 1 < p.β * θ_tilde) (hA : Real.exp 1 < A)
    (hJ : (J : ℝ) ≤ Real.log (Real.log A) / Real.log θ_tilde + C_J) :
    let κ_tilde := (-Real.log p.β) / Real.log θ_tilde
    0 < 1 - κ_tilde ∧
    p.β ^ C_J * (Real.log A) ^ (1 - κ_tilde) ≤ p.β ^ J * Real.log A := by
  intro κ_tilde
  have hlogθ : 0 < Real.log θ_tilde := Real.log_pos hθt
  have hlogβ : Real.log p.β < 0 := Real.log_neg p.hβ0 p.hβ1
  have hlogA_gt1 : 1 < Real.log A := by
    have := Real.log_lt_log (Real.exp_pos 1) hA
    rwa [Real.log_exp] at this
  have hlogA_pos : 0 < Real.log A := by linarith
  have hκ_lt1 : κ_tilde < 1 := by
    dsimp [κ_tilde]
    rw [div_lt_one hlogθ]
    have hlog_prod : 0 < Real.log (p.β * θ_tilde) := Real.log_pos hβθt
    rw [Real.log_mul (ne_of_gt p.hβ0) (by linarith)] at hlog_prod
    linarith
  refine ⟨by linarith, ?_⟩
  have hexp_le : (Real.log (Real.log A) / Real.log θ_tilde + C_J) * Real.log p.β ≤
      (J : ℝ) * Real.log p.β :=
    mul_le_mul_of_nonpos_right hJ (le_of_lt hlogβ)
  have hβJ : p.β ^ J = Real.exp ((J : ℝ) * Real.log p.β) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos p.hβ0]; ring_nf
  have hβCJ : p.β ^ C_J = Real.exp (C_J * Real.log p.β) := by
    rw [Real.rpow_def_of_pos p.hβ0]; ring_nf
  have hpow_logA : (Real.log A) ^ (1 - κ_tilde) =
      Real.exp (Real.log (Real.log A) * (1 - κ_tilde)) :=
    Real.rpow_def_of_pos hlogA_pos _
  have hlogA_exp : Real.log A = Real.exp (Real.log (Real.log A)) := (Real.exp_log hlogA_pos).symm
  rw [hβJ, hβCJ, hpow_logA, ← Real.exp_add]
  conv_rhs => rw [hlogA_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hrew : C_J * Real.log p.β + Real.log (Real.log A) * (1 - κ_tilde) =
      (Real.log (Real.log A) / Real.log θ_tilde + C_J) * Real.log p.β + Real.log (Real.log A) := by
    dsimp [κ_tilde]; field_simp [ne_of_gt hlogθ]; ring
  linarith

/-- Cota física inferior: si A^(1/r) * K ≤ k_*, entonces F_A(K, 1) < δ K (trampa física). -/
theorem physical_trap_below_kstar {A K : ℝ} (hA : 0 < A) (hK : 0 < K)
    (hle : A ^ (1 / p.r) * K ≤ p.k_star) :
    p.F_ces A K 1 < p.δ * K := by
  unfold F_ces
  have h1p : 1 < 1 + p.cw * (K / 1) ^ p.d := by
    have : 0 < p.cw * (K / 1) ^ p.d := mul_pos p.hcw_pos (Real.rpow_pos_of_pos (by linarith) _)
    linarith
  have hces_lt1 : (1 + p.cw * (K / 1) ^ p.d) ^ (-p.θ / p.d) < 1 := by
    have hneg : -p.θ / p.d < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr p.hθ_pos) p.hd
    have := Real.rpow_lt_rpow_of_neg (by norm_num) h1p hneg
    simpa using this
  have hK_pow : A * p.cK * K ^ p.θ ≤ p.δ * K := by
    have hpow_r : (A ^ (1 / p.r) * K) ^ p.r ≤ p.k_star ^ p.r :=
      Real.rpow_le_rpow (by positivity) hle (le_of_lt p.hr0)
    have hL : (A ^ (1 / p.r) * K) ^ p.r = A * K ^ p.r := by
      rw [Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos hA _)) (le_of_lt hK),
          ← Real.rpow_mul (le_of_lt hA), one_div_mul_cancel (ne_of_gt p.hr0), Real.rpow_one]
    have hR : p.k_star ^ p.r = p.δ / p.cK := by
      unfold k_star
      rw [← Real.rpow_mul (le_of_lt (div_pos p.hδ0 p.hcK_pos)),
          one_div_mul_cancel (ne_of_gt p.hr0), Real.rpow_one]
    rw [hL, hR] at hpow_r
    have hAKr : A * p.cK * K ^ p.r ≤ p.δ := by
      have := mul_le_mul_of_nonneg_left hpow_r (le_of_lt p.hcK_pos)
      rw [mul_div_cancel₀ _ (ne_of_gt p.hcK_pos)] at this
      linarith
    have hKθ : K ^ p.θ = K ^ p.r * K := by
      unfold θ; rw [add_comm, Real.rpow_add hK, Real.rpow_one]
    rw [hKθ]
    have := mul_le_mul_of_nonneg_right hAKr (le_of_lt hK)
    linarith
  have hpos : 0 < A * p.cK * K ^ p.θ := mul_pos (mul_pos hA p.hcK_pos) (Real.rpow_pos_of_pos hK _)
  have hstrict : A * p.cK * K ^ p.θ * (1 + p.cw * (K / 1) ^ p.d) ^ (-p.θ / p.d) <
      A * p.cK * K ^ p.θ * 1 := mul_lt_mul_of_pos_left hces_lt1 hpos
  linarith

/-- Cierre del Teorema 2 (Parte 1): convergencia A^(1/r) * S(A) → k_* = (δ/cK)^(1/r). -/
theorem theorem2_part1_tendsto (S : ℝ → ℝ)
    (hlb : ∀ ε > 0, ∃ A₀, ∀ A ≥ A₀, p.k_star - ε ≤ A ^ (1 / p.r) * S A)
    (hub : ∀ k₀ > p.k_star, ∃ A₀, ∀ A ≥ A₀, A ^ (1 / p.r) * S A ≤ k₀) :
    Tendsto (fun A => A ^ (1 / p.r) * S A) atTop (nhds p.k_star) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A₁, hA₁⟩ := hlb (ε / 2) (by linarith)
  obtain ⟨A₂, hA₂⟩ := hub (p.k_star + ε / 2) (by linarith)
  refine ⟨max A₁ A₂, fun A hA => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hA₁ A (le_trans (le_max_left _ _) hA)
  have h2 := hA₂ A (le_trans (le_max_right _ _) hA)
  constructor <;> linarith

/-! ## 4. Teorema 2 (Parte 2.2): Los 4 eslabones analíticos puros -/

/-- Lema técnico explícito: para todo y > 0 y α > 0, log y ≤ (2 / α) * y^(α / 2). -/
lemma log_le_rpow_half {y α : ℝ} (hy : 0 < y) (hα : 0 < α) :
    Real.log y ≤ (2 / α) * y ^ (α / 2) := by
  have h1 : Real.log (y ^ (α / 2)) ≤ y ^ (α / 2) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy _)
  rw [Real.log_rpow hy] at h1
  have hmul := mul_le_mul_of_nonneg_left (show (α / 2) * Real.log y ≤ y ^ (α / 2) by linarith)
    (show 0 ≤ 2 / α by positivity)
  have hrew : (2 / α) * ((α / 2) * Real.log y) = Real.log y := by field_simp [ne_of_gt hα]
  linarith

/-- Eslabón 1: acotación pura de β^(T_ε) ≥ 1 / (C₀ log A + C₁) a partir de Bellman en (k_*, k_* + ε]. -/
theorem link1_exit_time_T_eps {T_ε : ℕ} {A v_cake C₀ C₀' : ℝ}
    (hC₀ : 0 < C₀) (hlogA : 1 ≤ Real.log A)
    (hbell : v_cake ≤ (1 - p.β ^ T_ε) * (v_cake - 1 / (1 - p.β)) + p.β ^ T_ε * (C₀ * Real.log A + C₀')) :
    1 / ((C₀ + |C₀' - v_cake| + 1) * Real.log A) ≤ p.β ^ T_ε := by
  set D := C₀ + |C₀' - v_cake| + 1
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hdenom_pos : 0 < D * Real.log A := mul_pos hD_pos (by linarith)
  have hD_ge : C₀ * Real.log A + (C₀' - v_cake) ≤ D * Real.log A := by
    have h1 : C₀' - v_cake ≤ |C₀' - v_cake| := le_abs_self _
    have h2 : |C₀' - v_cake| ≤ |C₀' - v_cake| * Real.log A :=
      le_mul_of_one_le_right (abs_nonneg _) hlogA
    dsimp [D]; nlinarith
  rcases Nat.eq_zero_or_pos T_ε with rfl | hT_pos
  · simp only [pow_zero]
    rw [div_le_one hdenom_pos]
    dsimp [D]; nlinarith [abs_nonneg (C₀' - v_cake)]
  · have hβT_le : p.β ^ T_ε ≤ p.β := by
      have : p.β ^ T_ε ≤ p.β ^ 1 := pow_le_pow_of_le_one (le_of_lt p.hβ0) (le_of_lt p.hβ1) hT_pos
      simpa using this
    have hfrac_ge1 : 1 ≤ (1 - p.β ^ T_ε) / (1 - p.β) := by
      rw [one_le_div (by linarith [p.hβ1])]; linarith
    have hkey : (1 - p.β ^ T_ε) / (1 - p.β) ≤ p.β ^ T_ε * (C₀ * Real.log A + (C₀' - v_cake)) := by
      have hrew : (1 - p.β ^ T_ε) * (v_cake - 1 / (1 - p.β)) =
          v_cake - p.β ^ T_ε * v_cake - (1 - p.β ^ T_ε) / (1 - p.β) := by ring
      linarith
    have hβT_nn : 0 ≤ p.β ^ T_ε := pow_nonneg (le_of_lt p.hβ0) T_ε
    have hprod : 1 ≤ p.β ^ T_ε * (D * Real.log A) := by
      have := mul_le_mul_of_nonneg_left hD_ge hβT_nn
      linarith
    exact (div_le_iff₀ hdenom_pos).mpr (by linarith)

/-- Eslabón 3: acotación pura de β^(T_M) ≥ c₆ * (log A)^(-(1 + κ̃)) combinando Eslabones 1 y 2. -/
theorem link3_bound_TM {κ_tilde c₁ C₂ C₃ C₄ M_exp c_eps : ℝ} {T_ε T_M : ℕ} {A : ℝ}
    (hκ0 : 0 < κ_tilde) (hκ1 : κ_tilde < 1)
    (hc₁ : 0 < c₁) (hC₄ : 0 < C₄) (hc_eps : 0 < c_eps) (hM : 0 ≤ M_exp)
    (hT_le : T_ε ≤ T_M)
    (hlink1 : c_eps / Real.log A ≤ p.β ^ T_ε)
    (hbell : c₁ * (Real.log A) ^ (1 - κ_tilde) - C₂ ≤
      (p.η * p.θ * M_exp * Real.log (Real.log A) + C₃) / (1 - p.β) +
        p.β ^ (T_M - T_ε) * (C₄ * Real.log A))
    -- Umbral explícito en log A para que (c₁/2) (log A)^(1-κ̃) domine al término O(log log A) + O(1)
    (hA_large : 1 < Real.log A ∧
      C₂ + (p.η * p.θ * M_exp * Real.log (Real.log A) + C₃) / (1 - p.β) ≤
        (c₁ / 2) * (Real.log A) ^ (1 - κ_tilde)) :
    (c_eps * c₁ / (2 * C₄)) * (Real.log A) ^ (-(1 + κ_tilde)) ≤ p.β ^ T_M := by
  have hlogA_pos : 0 < Real.log A := by linarith [hA_large.1]
  have hstep1 : (c₁ / 2) * (Real.log A) ^ (1 - κ_tilde) ≤
      p.β ^ (T_M - T_ε) * (C₄ * Real.log A) := by linarith [hbell, hA_large.2]
  have hstep2 : (c₁ / (2 * C₄)) * (Real.log A) ^ (-κ_tilde) ≤ p.β ^ (T_M - T_ε) := by
    have hdiv : (c₁ / 2) * (Real.log A) ^ (1 - κ_tilde) / (C₄ * Real.log A) ≤ p.β ^ (T_M - T_ε) :=
      (div_le_iff₀ (mul_pos hC₄ hlogA_pos)).mpr hstep1
    have hrew : (c₁ / 2) * (Real.log A) ^ (1 - κ_tilde) / (C₄ * Real.log A) =
        (c₁ / (2 * C₄)) * (Real.log A) ^ (-κ_tilde) := by
      have hpow : (Real.log A) ^ (1 - κ_tilde) = Real.log A * (Real.log A) ^ (-κ_tilde) := by
        rw [show (1 - κ_tilde : ℝ) = 1 + (-κ_tilde) by ring, Real.rpow_add hlogA_pos, Real.rpow_one]
      rw [hpow]; field_simp [ne_of_gt hC₄, ne_of_gt hlogA_pos]
    linarith
  have hpow_split : p.β ^ T_M = p.β ^ T_ε * p.β ^ (T_M - T_ε) := by
    rw [← pow_add, Nat.add_sub_of_le hT_le]
  rw [hpow_split]
  have hmul := mul_le_mul hlink1 hstep2 (by positivity) (pow_nonneg (le_of_lt p.hβ0) T_ε)
  have hrew : c_eps / Real.log A * (c₁ / (2 * C₄) * (Real.log A) ^ (-κ_tilde)) =
      c_eps * c₁ / (2 * C₄) * (Real.log A) ^ (-(1 + κ_tilde)) := by
    have hpow : (Real.log A) ^ (-(1 + κ_tilde)) = (Real.log A)⁻¹ * (Real.log A) ^ (-κ_tilde) := by
      rw [show (-(1 + κ_tilde) : ℝ) = (-1 : ℝ) + (-κ_tilde) by ring,
          Real.rpow_add hlogA_pos, Real.rpow_neg_one]
    rw [hpow]; field_simp [ne_of_gt hC₄, ne_of_gt hlogA_pos]
  linarith

/-- Eslabón 4 (Rama A, L ≥ L_cut): suprimir el ocio aporta ganancia ≥ (1 - η) L_cut. -/
theorem link4_leisure_gain {L L_cut : ℝ} (hL1 : L < 1) (hge : L_cut ≤ L) :
    (1 - p.η) * L_cut ≤ -(1 - p.η) * Real.log (1 - L) := by
  have hconc : Real.log (1 - L) ≤ -L := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - L by linarith)
    linarith
  have h1mη : 0 ≤ 1 - p.η := by linarith [p.hη1]
  nlinarith

/-- Desigualdad elemental para todo r ∈ (0, 1] y α > 0: 1 - r^α ≥ (α / (1 + α)) * (1 - r). -/
lemma one_sub_rpow_ge {r α : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hα : 0 < α) :
    (α / (1 + α)) * (1 - r) ≤ 1 - r ^ α := by
  have hlog : Real.log r ≤ -(1 - r) := by
    have := Real.log_le_sub_one_of_pos hr0; linarith
  have hexp : r ^ α ≤ Real.exp (-(α * (1 - r))) := by
    rw [Real.rpow_def_of_pos hr0]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hinv : Real.exp (-(α * (1 - r))) ≤ 1 / (1 + α * (1 - r)) := by
    rw [Real.exp_neg, one_div]
    have h1 : 1 + α * (1 - r) ≤ Real.exp (α * (1 - r)) := by
      linarith [Real.add_one_le_exp (α * (1 - r))]
    have hpos : 0 < 1 + α * (1 - r) := by nlinarith
    exact inv_anti₀ hpos h1
  have hstep : α * (1 - r) / (1 + α * (1 - r)) ≤ 1 - r ^ α := by
    have h1 : 1 - 1 / (1 + α * (1 - r)) = α * (1 - r) / (1 + α * (1 - r)) := by
      have hne : 1 + α * (1 - r) ≠ 0 := by nlinarith
      field_simp [hne]; ring
    linarith
  have hden : 1 + α * (1 - r) ≤ 1 + α := by nlinarith
  have hden_pos : 0 < 1 + α * (1 - r) := by nlinarith
  have hnum_nn : 0 ≤ α * (1 - r) := by nlinarith
  have hcmp := div_le_div_of_nonneg_left hnum_nn hden_pos hden
  have hrew : α * (1 - r) / (1 + α) = (α / (1 + α)) * (1 - r) := by ring
  linarith

/-- Eslabón 4 (Rama B, L < L_cut ≤ 1/2): ganancia productiva relativa CES
    (F_A(K, 1) - F_A(K, L)) / F_A(K, 1) ≥ c₈ * min{1, cw * (K/L)^d}. -/
theorem link4_ces_output_gain {A K L : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hL0 : 0 < L) (hL_half : L ≤ 1 / 2) :
    let α := p.θ / p.d
    let c₈ := (α / (1 + α)) * ((1 - (2 : ℝ) ^ (-p.d)) / 2)
    c₈ * min 1 (p.cw * (K / L) ^ p.d) ≤
      (p.F_ces A K 1 - p.F_ces A K L) / p.F_ces A K 1 := by
  intro α c₈
  set u := p.cw * (K / L) ^ p.d
  set v := p.cw * (K / 1) ^ p.d
  have hu_pos : 0 < u := mul_pos p.hcw_pos (Real.rpow_pos_of_pos (div_pos hK hL0) _)
  have hv_pos : 0 < v := mul_pos p.hcw_pos (Real.rpow_pos_of_pos (by linarith) _)
  -- Como L ≤ 1/2, K/L ≥ 2 K, luego v ≤ 2^(-d) * u
  have h2K : 2 * K ≤ K / L := by
    rw [le_div_iff₀ hL0]; nlinarith
  have hv_le : v ≤ (2 : ℝ) ^ (-p.d) * u := by
    have hpow : (2 * K) ^ p.d ≤ (K / L) ^ p.d :=
      Real.rpow_le_rpow (by positivity) h2K (le_of_lt p.hd)
    rw [Real.mul_rpow (by norm_num) (le_of_lt hK)] at hpow
    have hmul := mul_le_mul_of_nonneg_left hpow (le_of_lt p.hcw_pos)
    have hinv : (2 : ℝ) ^ (-p.d) * (2 : ℝ) ^ p.d = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    dsimp [u, v]; rw [div_one]
    have h2neg_nn : 0 ≤ (2 : ℝ) ^ (-p.d) := Real.rpow_nonneg (by norm_num) _
    have hstep := mul_le_mul_of_nonneg_left hmul h2neg_nn
    have hrew : (2 : ℝ) ^ (-p.d) * (p.cw * ((2 : ℝ) ^ p.d * K ^ p.d)) = p.cw * K ^ p.d := by
      calc (2 : ℝ) ^ (-p.d) * (p.cw * ((2 : ℝ) ^ p.d * K ^ p.d))
          = ((2 : ℝ) ^ (-p.d) * (2 : ℝ) ^ p.d) * (p.cw * K ^ p.d) := by ring
        _ = p.cw * K ^ p.d := by rw [hinv, one_mul]
    linarith
  set r := (1 + v) / (1 + u)
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have h2d_lt1 : (2 : ℝ) ^ (-p.d) < 1 := by
    have := Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num : (1 : ℝ) < 2) (neg_lt_zero.mpr p.hd)
    simpa using this
  have hr1 : r ≤ 1 := by
    rw [div_le_one (by linarith)]; nlinarith
  have h1mr : ((1 - (2 : ℝ) ^ (-p.d)) / 2) * min 1 u ≤ 1 - r := by
    have h1u : 1 + u ≠ 0 := by linarith
    have hsub : 1 - r = (u - v) / (1 + u) := by dsimp [r]; field_simp [h1u]; ring
    rw [hsub]
    have hnum : (1 - (2 : ℝ) ^ (-p.d)) * u ≤ u - v := by linarith
    have hu_over : min 1 u / 2 ≤ u / (1 + u) := by
      by_cases h1 : u ≤ 1
      · rw [min_eq_right h1]
        exact div_le_div_of_nonneg_left (le_of_lt hu_pos) (by linarith) (by linarith)
      · push_neg at h1
        rw [min_eq_left (le_of_lt h1)]
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    have hpos_coef : 0 ≤ 1 - (2 : ℝ) ^ (-p.d) := by linarith
    calc ((1 - (2 : ℝ) ^ (-p.d)) / 2) * min 1 u
        = (1 - (2 : ℝ) ^ (-p.d)) * (min 1 u / 2) := by ring
      _ ≤ (1 - (2 : ℝ) ^ (-p.d)) * (u / (1 + u)) := mul_le_mul_of_nonneg_left hu_over hpos_coef
      _ = ((1 - (2 : ℝ) ^ (-p.d)) * u) / (1 + u) := by ring
      _ ≤ (u - v) / (1 + u) := div_le_div_of_nonneg_right hnum (by linarith)
  have hratio_F : (p.F_ces A K 1 - p.F_ces A K L) / p.F_ces A K 1 = 1 - r ^ α := by
    unfold F_ces
    have hfac_pos : 0 < A * p.cK * K ^ p.θ := mul_pos (mul_pos hA p.hcK_pos) (Real.rpow_pos_of_pos hK _)
    have h1v_pos : 0 < (1 + v) ^ (-p.θ / p.d) := Real.rpow_pos_of_pos (by linarith) _
    have hF1_ne : A * p.cK * K ^ p.θ * (1 + v) ^ (-p.θ / p.d) ≠ 0 := ne_of_gt (mul_pos hfac_pos h1v_pos)
    have hratio_pow : (1 + u) ^ (-p.θ / p.d) / (1 + v) ^ (-p.θ / p.d) = r ^ α := by
      have hrew : (-p.θ / p.d : ℝ) = -α := by dsimp [α]; ring
      rw [hrew, Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
          div_eq_mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv,
          ← Real.div_rpow (by linarith) (by linarith)]
    have hsplit : (A * p.cK * K ^ p.θ * (1 + v) ^ (-p.θ / p.d) -
        A * p.cK * K ^ p.θ * (1 + u) ^ (-p.θ / p.d)) /
        (A * p.cK * K ^ p.θ * (1 + v) ^ (-p.θ / p.d)) =
        1 - (1 + u) ^ (-p.θ / p.d) / (1 + v) ^ (-p.θ / p.d) := by
      field_simp [ne_of_gt hA, ne_of_gt p.hcK_pos, ne_of_gt (Real.rpow_pos_of_pos hK p.θ),
        ne_of_gt h1v_pos]
    rw [hsplit, hratio_pow]
  rw [hratio_F]
  have hα_pos : 0 < α := div_pos p.hθ_pos p.hd
  have hbase := one_sub_rpow_ge hr0 hr1 hα_pos
  have hmul := mul_le_mul_of_nonneg_left h1mr (show 0 ≤ α / (1 + α) by positivity)
  dsimp [c₈]; linarith

/-! ## 5. Cierre analítico puro del Teorema 2 (Parte 2.2): ΔW_A^+ > ΔW_A^- para todo A ≥ A₀ -/

/-- Umbral explícito A₀ tal que para todo A ≥ A₀,
    c₁₀ * A^(-d/(r(1+d))) * (log A)^(1+κ̃) > C_minus * A^(-d/(r(1+d))),
    cerrando analíticamente ΔW_A^+ > ΔW_A^- y S_A^fix(1) < S_A. -/
theorem theorem2_part2_strict_dominance {κ_tilde c₁₀ C_minus : ℝ}
    (hκ0 : 0 < κ_tilde) (hc₁₀ : 0 < c₁₀) (hCm : 0 ≤ C_minus) :
    ∃ A₀ > 1, ∀ A ≥ A₀,
      C_minus * A ^ (-p.d / (p.r * (1 + p.d))) <
      c₁₀ * A ^ (-p.d / (p.r * (1 + p.d))) * (Real.log A) ^ (1 + κ_tilde) := by
  let L₀ := max 1 ((C_minus / c₁₀ + 1) ^ (1 / (1 + κ_tilde)))
  refine ⟨Real.exp L₀, Real.one_lt_exp_iff.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro A hA
  have hA_pos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  have hApow_pos : 0 < A ^ (-p.d / (p.r * (1 + p.d))) := Real.rpow_pos_of_pos hA_pos _
  have hlogA_ge : L₀ ≤ Real.log A := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) hA
  have h1pκ_pos : 0 < 1 + κ_tilde := by linarith
  have hpow_gt : C_minus / c₁₀ < (Real.log A) ^ (1 + κ_tilde) := by
    have hge_base : (C_minus / c₁₀ + 1) ^ (1 / (1 + κ_tilde)) ≤ Real.log A :=
      le_trans (le_max_right _ _) hlogA_ge
    have hbase_pos : 0 < C_minus / c₁₀ + 1 := by positivity
    have hstep : ((C_minus / c₁₀ + 1) ^ (1 / (1 + κ_tilde))) ^ (1 + κ_tilde) ≤
        (Real.log A) ^ (1 + κ_tilde) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hbase_pos) _) hge_base (le_of_lt h1pκ_pos)
    rw [← Real.rpow_mul (le_of_lt hbase_pos), one_div_mul_cancel (ne_of_gt h1pκ_pos),
        Real.rpow_one] at hstep
    linarith
  have hmul : C_minus < c₁₀ * (Real.log A) ^ (1 + κ_tilde) := by
    have := mul_lt_mul_of_pos_left hpow_gt hc₁₀
    field_simp [ne_of_gt hc₁₀] at this; linarith
  have hfinal := mul_lt_mul_of_pos_right hmul hApow_pos
  linarith

/-! ## 6. Ensamblado final del Teorema 2 (Parte 2.2) y Corolario 2* (Sección 4) -/

/-- Rama unificada del Eslabón 4: para todo `L ∈ (0, 1)` y `L_cut ∈ (0, 1/2]`,
    o bien `L ≥ L_cut` (ganancia de ocio `≥ (1 - η) L_cut`), o bien `L < L_cut`
    (ganancia productiva relativa CES `≥ c₈ * min 1 (cw * (K / L)^d)`). -/
theorem link4_dichotomy {A K L L_cut : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hL0 : 0 < L) (hL1 : L < 1) (hLcut_half : L_cut ≤ 1 / 2) :
    let α := p.θ / p.d
    let c₈ := (α / (1 + α)) * ((1 - (2 : ℝ) ^ (-p.d)) / 2)
    (1 - p.η) * L_cut ≤ -(1 - p.η) * Real.log (1 - L) ∨
    c₈ * min 1 (p.cw * (K / L) ^ p.d) ≤
      (p.F_ces A K 1 - p.F_ces A K L) / p.F_ces A K 1 := by
  intro α c₈
  by_cases hge : L_cut ≤ L
  · exact Or.inl (p.link4_leisure_gain hL1 hge)
  · have hL_half : L ≤ 1 / 2 := by linarith
    exact Or.inr (p.link4_ces_output_gain hA hK hL0 hL_half)

/-- Ensamblado end-to-end del Teorema 2 (Parte 2.2):
    si el beneficio de la desviación `ΔW_plus A` domina la cota inferior de los Eslabones 3–4
    y el costo `ΔW_minus A` está acotado por `C_minus * A^(-d/(r(1+d)))`, entonces existe
    un umbral explícito `A₀ > 1` tal que para todo `A ≥ A₀`, `ΔW_minus A < ΔW_plus A`,
    y por tanto `S_fix A < S_endo A`. -/
theorem theorem2_part2_assembled {κ_tilde c₁₀ C_minus : ℝ}
    (ΔW_plus ΔW_minus S_fix S_endo : ℝ → ℝ)
    (hκ0 : 0 < κ_tilde) (hc₁₀ : 0 < c₁₀) (hCm : 0 ≤ C_minus)
    (hplus : ∀ A > 1,
      c₁₀ * A ^ (-p.d / (p.r * (1 + p.d))) * (Real.log A) ^ (1 + κ_tilde) ≤ ΔW_plus A)
    (hminus : ∀ A > 1,
      ΔW_minus A ≤ C_minus * A ^ (-p.d / (p.r * (1 + p.d))))
    (hmon : ∀ A > 1, ΔW_minus A < ΔW_plus A → S_fix A < S_endo A) :
    ∃ A₀ > 1, ∀ A ≥ A₀, ΔW_minus A < ΔW_plus A ∧ S_fix A < S_endo A := by
  obtain ⟨A₀, hA₀, hdom⟩ := p.theorem2_part2_strict_dominance hκ0 hc₁₀ hCm
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 < A := lt_of_lt_of_le hA₀ hA
  have hlt : ΔW_minus A < ΔW_plus A :=
    lt_of_le_of_lt (hminus A hA1) (lt_of_lt_of_le (hdom A hA) (hplus A hA1))
  exact ⟨hlt, hmon A hA1 hlt⟩

/-- Corolario 2* (Invarianza asintótica respecto a la oferta laboral fija `L̄ > 0`):
    bajo el isomorfismo finito `S_fix(A, L̄) = L̄ * S_fix(A L̄^r, 1)`, si
    `A^(1/r) * S_fix(A, 1) → k_*`, entonces `A^(1/r) * S_fix(A, L̄) → k_*`
    con el mismo límite `k_*` independiente de `L̄`. -/
theorem corollary2_fixed_labor_invariance (S_fix1 : ℝ → ℝ) {Lbar : ℝ} (hL : 0 < Lbar)
    (htend : Tendsto (fun A => A ^ (1 / p.r) * S_fix1 A) atTop (nhds p.k_star)) :
    Tendsto (fun A => A ^ (1 / p.r) * (Lbar * S_fix1 (A * Lbar ^ p.r))) atTop (nhds p.k_star) := by
  have hLr_pos : 0 < Lbar ^ p.r := Real.rpow_pos_of_pos hL _
  have hmul_top : Tendsto (fun A => A * Lbar ^ p.r) atTop atTop :=
    Tendsto.atTop_mul_const hLr_pos tendsto_id
  have hcomp := htend.comp hmul_top
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  dsimp [Function.comp]
  rw [Real.mul_rpow (le_of_lt hA) (le_of_lt hLr_pos),
      ← Real.rpow_mul (le_of_lt hL), mul_one_div_cancel (ne_of_gt p.hr0), Real.rpow_one]
  ring

/-- Corolario 2* (Convergencia de la razón de fronteras):
    si tanto la frontera de trabajo fijo `S_fix` como la endógena `S_endo` satisfacen
    la Parte 1 del Teorema 2 (`A^(1/r) S_fix → k_*` y `A^(1/r) S_endo → k_*`),
    entonces `S_endo A / S_fix A → 1`. -/
theorem corollary2_ratio_tendsto_one (S_fix S_endo : ℝ → ℝ)
    (hfix : Tendsto (fun A => A ^ (1 / p.r) * S_fix A) atTop (nhds p.k_star))
    (hendo : Tendsto (fun A => A ^ (1 / p.r) * S_endo A) atTop (nhds p.k_star)) :
    Tendsto (fun A => S_endo A / S_fix A) atTop (nhds 1) := by
  have hdiv : Tendsto (fun A => (A ^ (1 / p.r) * S_endo A) / (A ^ (1 / p.r) * S_fix A))
      atTop (nhds (p.k_star / p.k_star)) :=
    hendo.div hfix (ne_of_gt p.hk_star_pos)
  rw [div_self (ne_of_gt p.hk_star_pos)] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  have hAr_ne : A ^ (1 / p.r) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA _)
  exact mul_div_mul_left (S_endo A) (S_fix A) hAr_ne

end CESParams

/-! ## 7. Instanciación exacta de la calibración armónica y régimen de paciencia débil -/

/-- Calibración armónica de referencia (`d = 1`, `r = 1/2`, `w = 1/2`, `β = 0.97`, `δ = 0.08`, `η = 0.70`). -/
noncomputable def harmonicBenchmark : CESParams where
  d := 1
  r := 1 / 2
  w := 1 / 2
  β := 97 / 100
  δ := 8 / 100
  η := 7 / 10
  hd := by norm_num
  hr0 := by norm_num
  hr1 := by norm_num
  hw0 := by norm_num
  hw1 := by norm_num
  hβ0 := by norm_num
  hβ1 := by norm_num
  hβθ := by norm_num
  hδ0 := by norm_num
  hδ1 := by norm_num
  hη0 := by norm_num
  hη1 := by norm_num

/-- Régimen de paciencia débil del Corolario 2* (`β = 0.90`):
    satisface `β * θ = 1.35 > 1` aunque el autovalor local cumple `β * (q + θ * δ) = 0.936 < 1`. -/
noncomputable def weakPatienceBenchmark : CESParams where
  d := 1
  r := 1 / 2
  w := 1 / 2
  β := 90 / 100
  δ := 8 / 100
  η := 7 / 10
  hd := by norm_num
  hr0 := by norm_num
  hr1 := by norm_num
  hw0 := by norm_num
  hw1 := by norm_num
  hβ0 := by norm_num
  hβ1 := by norm_num
  hβθ := by norm_num
  hδ0 := by norm_num
  hδ1 := by norm_num
  hη0 := by norm_num
  hη1 := by norm_num

/-- En el régimen de paciencia débil (`β = 0.90`), `β (q + θ δ) < 1 < β θ`. -/
theorem weakPatience_local_vs_global :
    weakPatienceBenchmark.β * (weakPatienceBenchmark.q +
      weakPatienceBenchmark.θ * weakPatienceBenchmark.δ) < 1 ∧
    1 < weakPatienceBenchmark.β * weakPatienceBenchmark.θ := by
  unfold weakPatienceBenchmark CESParams.q CESParams.θ
  norm_num

/-- Identidades exactas de la calibración armónica (Tabla 3):
    `k_* = 1 / 1250 = 0.0008`, tasa armónica `-d / (r * (1 + d)) = -1`,
    y trabajo estacionario `L_ss = (θ η) / (θ η + 1 - η) = 7 / 9`. -/
theorem harmonicBenchmark_exact_constants :
    harmonicBenchmark.k_star = 1 / 1250 ∧
    -harmonicBenchmark.d / (harmonicBenchmark.r * (1 + harmonicBenchmark.d)) = -1 ∧
    (harmonicBenchmark.θ * harmonicBenchmark.η) /
      (harmonicBenchmark.θ * harmonicBenchmark.η + (1 - harmonicBenchmark.η)) = 7 / 9 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold CESParams.k_star CESParams.cK CESParams.θ harmonicBenchmark
    have hcK_sq : ((1 / 2 : ℝ) ^ (-(1 + 1 / 2) / 1 : ℝ)) ^ (2 : ℝ) = 8 := by
      rw [← Real.rpow_mul (by norm_num)]
      have hexp : (-(1 + 1 / 2) / 1 : ℝ) * 2 = (-3 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg (by norm_num)]
      norm_num
    have hpow2 : (1 / (1 / 2 : ℝ) : ℝ) = 2 := by norm_num
    rw [hpow2, Real.div_rpow (by norm_num) (Real.rpow_nonneg (by norm_num) _), hcK_sq]
    norm_num
  · unfold harmonicBenchmark; norm_num
  · unfold harmonicBenchmark CESParams.θ; norm_num

end MVS.Theorem2
