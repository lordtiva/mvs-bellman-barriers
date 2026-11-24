import MVS.Theorem1
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Proposición 2 (MR): Dominancia tangente, envolvente E⁺ y Wronskiano Q_X

Formalización del núcleo analítico de la Proposición 2 y el Apéndice A.2
(sin `sorry`).
-/

open Real Set MVS.Theorem1

namespace MVS.Proposition2

noncomputable section

/-! ## 1. Definiciones exactas de la Proposición 2 y Apéndice A.2 -/

/-- Argumento armónico g(l, K) = 2 K l / (K + l). -/
def g (l K : ℝ) : ℝ := 2 * K * l / (K + l)

/-- Derivada ∂F/∂L(A, K, l₀) en forma cerrada sin `rpow`. -/
def t_gen (A l₀ K : ℝ) : ℝ :=
  3 * A * K ^ 2 * Real.sqrt (g l₀ K) / (K + l₀) ^ 2

/-- Valor marginal del trabajo en A₊: t(K) = ∂F_{A₊}/∂L(K, l₀). -/
def t_val (l₀ K : ℝ) : ℝ := t_gen A_max l₀ K

/-- Primera derivada t'(K) = t(K) * 5 l₀ / (2 K (K + l₀)). -/
def t_deriv (l₀ K : ℝ) : ℝ :=
  t_val l₀ K * (5 * l₀ / (2 * K * (K + l₀)))

/-- Segunda derivada t''(K) = t(K) * 5 l₀ (3 l₀ - 4 K) / (4 K² (K + l₀)²). -/
def t_deriv2 (l₀ K : ℝ) : ℝ :=
  t_val l₀ K * (5 * l₀ * (3 * l₀ - 4 * K) / (4 * K ^ 2 * (K + l₀) ^ 2))

/-- Primera y segunda derivadas en K de F_A(K, l). -/
def FK (A l K : ℝ) : ℝ :=
  3 * A * l ^ 2 * Real.sqrt (g l K) / (K + l) ^ 2

def FKK (A l K : ℝ) : ℝ :=
  3 * A * l ^ 3 * (l - 4 * K) / (Real.sqrt (g l K) * (K + l) ^ 4)

/-- Recurso virtual mayorante S(K) y sus derivadas S'(K), S''(K). -/
def S_val (l₀ K : ℝ) : ℝ :=
  q_max * K + F A_max K l₀ + (1 - l₀) * t_val l₀ K

def S_deriv (l₀ K : ℝ) : ℝ :=
  q_max + FK A_max l₀ K + (1 - l₀) * t_deriv l₀ K

def S_deriv2 (l₀ K : ℝ) : ℝ :=
  FKK A_max l₀ K + (1 - l₀) * t_deriv2 l₀ K

/-- Consumo del testigo c_X(K) y sus derivadas c_X'(K), c_X''(K). -/
def cX (lX sX K : ℝ) : ℝ :=
  q_min * K + F A_min K lX - sX

def cX_deriv (lX K : ℝ) : ℝ :=
  q_min + FK A_min lX K

def cX_deriv2 (lX K : ℝ) : ℝ :=
  FKK A_min lX K

/-- Demanda óptima de ocio acotada ω*(c_sup, t, η) = min{1, (1-η) c_sup / t}. -/
def omega_star (η c_sup t : ℝ) : ℝ :=
  min 1 ((1 - η) * c_sup / t)

/-- Rama η de la envolvente exacta de salida adversa E⁺_η. -/
def E_plus_branch (η a l₀ K : ℝ) : ℝ :=
  let c_sup := S_val l₀ K - a
  let tv := t_val l₀ K
  let ω := omega_star η c_sup tv
  η * Real.log (c_sup - tv * ω) + (1 - η) * Real.log ω

/-- Envolvente global E⁺(K, a; l₀) = max_{η ∈ {η₋, η₊}} E⁺_η(K, a; l₀). -/
def E_plus (a l₀ K : ℝ) : ℝ :=
  max (E_plus_branch eta_min a l₀ K) (E_plus_branch eta_max a l₀ K)

/-- Cociente R_X(K) = (S(K) - a) / c_X(K) y Wronskiano Q_X(K) y Q_X'(K). -/
def RX (a l₀ lX sX K : ℝ) : ℝ :=
  (S_val l₀ K - a) / cX lX sX K

def QX (a l₀ lX sX K : ℝ) : ℝ :=
  S_deriv l₀ K * cX lX sX K - cX_deriv lX K * (S_val l₀ K - a)

def QX_deriv (a l₀ lX sX K : ℝ) : ℝ :=
  S_deriv2 l₀ K * cX lX sX K - cX_deriv2 lX K * (S_val l₀ K - a)

/-- Rama suave (η_W, η_E) de la ventaja puntual del testigo Δ_X(K). -/
def delta_branch (a l₀ lX sX TX Ψ_a ηW ηE K : ℝ) : ℝ :=
  (ηW * Real.log (cX lX sX K) + (1 - ηW) * Real.log (1 - lX) + beta_max * TX) -
    (E_plus_branch ηE a l₀ K + beta_min * Ψ_a)

/-- Ventaja puntual completa Δ_X(K) = W_X(K) - [E⁺(K, a; l₀) + β₋ Ψ(a)]. -/
def delta_X (a l₀ lX sX TX Ψ_a K : ℝ) : ℝ :=
  min (min (delta_branch a l₀ lX sX TX Ψ_a eta_min eta_min K)
           (delta_branch a l₀ lX sX TX Ψ_a eta_min eta_max K))
      (min (delta_branch a l₀ lX sX TX Ψ_a eta_max eta_min K)
           (delta_branch a l₀ lX sX TX Ψ_a eta_max eta_max K))

/-! ## 2. Dominancia global de la tangente (l₀ ≥ K / 2) sin cálculo -/

/-- Si l₀ ≥ K / 2, la tangente en L = l₀ domina globalmente a F_A(K, L) para todo L ≥ 0. -/
theorem tangent_dominance {A K l₀ L : ℝ}
    (hA : 0 ≤ A) (hK : 0 < K) (hl₀ : K / 2 ≤ l₀) (hL : 0 ≤ L) :
    F A K L ≤ F A K l₀ + t_gen A l₀ K * (L - l₀) := by
  have hl₀_pos : 0 < l₀ := by linarith
  have hKL_pos : 0 < K + L := by linarith
  have hKl₀_pos : 0 < K + l₀ := by linarith
  set y := L / (K + L)
  set y₀ := l₀ / (K + l₀)
  set u := Real.sqrt y
  set u₀ := Real.sqrt y₀
  set s2K := Real.sqrt (2 * K)
  have hy_nn : 0 ≤ y := div_nonneg hL (le_of_lt hKL_pos)
  have hy₀_nn : 0 ≤ y₀ := div_nonneg (le_of_lt hl₀_pos) (le_of_lt hKl₀_pos)
  have hu_sq : u ^ 2 = y := Real.sq_sqrt hy_nn
  have hu₀_sq : u₀ ^ 2 = y₀ := Real.sq_sqrt hy₀_nn
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg y
  have hu₀_nn : 0 ≤ u₀ := Real.sqrt_nonneg y₀
  have hs2K_nn : 0 ≤ s2K := Real.sqrt_nonneg (2 * K)
  -- 1 - u^2 = K / (K + L) > 0,  1 - u₀^2 = K / (K + l₀) > 0
  have h1mu : 1 - u ^ 2 = K / (K + L) := by
    rw [hu_sq]; dsimp [y]; field_simp [ne_of_gt hKL_pos]; ring
  have h1mu₀ : 1 - u₀ ^ 2 = K / (K + l₀) := by
    rw [hu₀_sq]; dsimp [y₀]; field_simp [ne_of_gt hKl₀_pos]; ring
  have h1mu_pos : 0 < 1 - u ^ 2 := by rw [h1mu]; positivity
  have h1mu₀_pos : 0 < 1 - u₀ ^ 2 := by rw [h1mu₀]; positivity
  -- Condición crítica l₀ ≥ K / 2  <=>  3 u₀² - 1 ≥ 0
  have hcrit : 0 ≤ 3 * u₀ ^ 2 - 1 := by
    rw [hu₀_sq]; dsimp [y₀]
    have : 3 * (l₀ / (K + l₀)) - 1 = (2 * l₀ - K) / (K + l₀) := by
      field_simp [ne_of_gt hKl₀_pos]; ring
    rw [this]; exact div_nonneg (by linarith) (le_of_lt hKl₀_pos)
  -- Reescritura de F y t_gen en términos de (u, u₀, s2K)
  have hF_L : F A K L = A * (2 * K) * s2K * u ^ 3 := by
    unfold F; dsimp only
    have harg : 2 * K * L / (K + L) = (2 * K) * y := by dsimp [y]; ring
    rw [harg, Real.sqrt_mul (by linarith : 0 ≤ 2 * K)]
    change A * (2 * K * y) * (s2K * u) = A * (2 * K) * s2K * u ^ 3
    rw [← hu_sq]; ring
  have hF_l₀ : F A K l₀ = A * (2 * K) * s2K * u₀ ^ 3 := by
    unfold F; dsimp only
    have harg : 2 * K * l₀ / (K + l₀) = (2 * K) * y₀ := by dsimp [y₀]; ring
    rw [harg, Real.sqrt_mul (by linarith : 0 ≤ 2 * K)]
    change A * (2 * K * y₀) * (s2K * u₀) = A * (2 * K) * s2K * u₀ ^ 3
    rw [← hu₀_sq]; ring
  have ht_eq : t_gen A l₀ K = 3 * A * s2K * u₀ * (1 - u₀ ^ 2) ^ 2 := by
    unfold t_gen g
    have harg : 2 * K * l₀ / (K + l₀) = (2 * K) * y₀ := by dsimp [y₀]; ring
    rw [harg, Real.sqrt_mul (by linarith : 0 ≤ 2 * K), h1mu₀]
    dsimp [u₀, s2K]; field_simp [ne_of_gt hKl₀_pos]
  have hL_sub : L - l₀ = K * (u ^ 2 - u₀ ^ 2) / ((1 - u ^ 2) * (1 - u₀ ^ 2)) := by
    rw [h1mu, h1mu₀, hu_sq, hu₀_sq]; dsimp [y, y₀]
    field_simp [ne_of_gt hKL_pos, ne_of_gt hKl₀_pos, ne_of_gt hK]; ring
  -- Identidad polinomial exacta:
  -- P(u) = (u - u₀)^2 * (2 u^3 + 4 u₀ u^2 + (3 u₀^2 - 1)(2 u + u₀)) ≥ 0
  have hpoly : 0 ≤ 2 * (1 - u ^ 2) * u₀ ^ 3 +
      3 * u₀ * (1 - u₀ ^ 2) * (u ^ 2 - u₀ ^ 2) - 2 * (1 - u ^ 2) * u ^ 3 := by
    have hfac : 2 * (1 - u ^ 2) * u₀ ^ 3 +
        3 * u₀ * (1 - u₀ ^ 2) * (u ^ 2 - u₀ ^ 2) - 2 * (1 - u ^ 2) * u ^ 3 =
        (u - u₀) ^ 2 * (2 * u ^ 3 + 4 * u₀ * u ^ 2 + (3 * u₀ ^ 2 - 1) * (2 * u + u₀)) := by ring
    rw [hfac]
    have hbrack : 0 ≤ 2 * u ^ 3 + 4 * u₀ * u ^ 2 + (3 * u₀ ^ 2 - 1) * (2 * u + u₀) := by
      positivity
    positivity
  -- Concluir dividiendo por 2 * (1 - u^2) > 0 y multiplicando por A * (2 * K) * s2K ≥ 0
  have hdiff : F A K l₀ + t_gen A l₀ K * (L - l₀) - F A K L =
      A * (2 * K) * s2K *
        (2 * (1 - u ^ 2) * u₀ ^ 3 +
         3 * u₀ * (1 - u₀ ^ 2) * (u ^ 2 - u₀ ^ 2) - 2 * (1 - u ^ 2) * u ^ 3) /
        (2 * (1 - u ^ 2)) := by
    rw [hF_L, hF_l₀, ht_eq, hL_sub]
    field_simp [ne_of_gt h1mu_pos, ne_of_gt h1mu₀_pos]
  have hnn : 0 ≤ F A K l₀ + t_gen A l₀ K * (L - l₀) - F A K L := by
    rw [hdiff]
    exact div_nonneg (by positivity) (by linarith)
  linarith

/-! ## 3. Optimalidad cerrada de la envolvente E⁺ sin cálculo -/

/-- Para todo ocio factible ω ∈ (0, 1] con c_sup - t ω > 0, ω* maximiza la utilidad instantánea. -/
theorem envelope_optimality {η c_sup t ω : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hc_sup : 0 < c_sup) (ht : 0 < t)
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hc : 0 < c_sup - t * ω) :
    η * Real.log (c_sup - t * ω) + (1 - η) * Real.log ω ≤
    η * Real.log (c_sup - t * omega_star η c_sup t) +
      (1 - η) * Real.log (omega_star η c_sup t) := by
  set ωs := omega_star η c_sup t
  have hωs_pos : 0 < ωs := lt_min zero_lt_one (div_pos (mul_pos (by linarith) hc_sup) ht)
  have hωs_le_int : ωs ≤ (1 - η) * c_sup / t := min_le_right _ _
  have hcs_pos : 0 < c_sup - t * ωs := by
    have hmul : t * ωs ≤ (1 - η) * c_sup := by
      have := mul_le_mul_of_nonneg_left hωs_le_int (le_of_lt ht)
      field_simp [ne_of_gt ht] at this; linarith
    nlinarith
  -- Concavidad de log en ambos términos
  have hlog_c : Real.log (c_sup - t * ω) - Real.log (c_sup - t * ωs) ≤
      -t * (ω - ωs) / (c_sup - t * ωs) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hc hcs_pos)
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hcs_pos)] at h1
    have h2 : (c_sup - t * ω) / (c_sup - t * ωs) - 1 = -t * (ω - ωs) / (c_sup - t * ωs) := by
      field_simp [ne_of_gt hcs_pos]; ring
    linarith
  have hlog_ω : Real.log ω - Real.log ωs ≤ (ω - ωs) / ωs := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hω0 hωs_pos)
    rw [Real.log_div (ne_of_gt hω0) (ne_of_gt hωs_pos)] at h1
    have h2 : ω / ωs - 1 = (ω - ωs) / ωs := by field_simp [ne_of_gt hωs_pos]
    linarith
  have hcomb : η * (Real.log (c_sup - t * ω) - Real.log (c_sup - t * ωs)) +
      (1 - η) * (Real.log ω - Real.log ωs) ≤
      (ω - ωs) * (((1 - η) * c_sup - t * ωs) / (ωs * (c_sup - t * ωs))) := by
    have h1 := mul_le_mul_of_nonneg_left hlog_c (le_of_lt hη0)
    have h2 := mul_le_mul_of_nonneg_left hlog_ω (show 0 ≤ 1 - η by linarith)
    have hrew : η * (-t * (ω - ωs) / (c_sup - t * ωs)) + (1 - η) * ((ω - ωs) / ωs) =
        (ω - ωs) * (((1 - η) * c_sup - t * ωs) / (ωs * (c_sup - t * ωs))) := by
      field_simp [ne_of_gt hcs_pos, ne_of_gt hωs_pos]; ring
    linarith
  -- Ambos casos de min{1, (1-η) c_sup / t} rinden RHS ≤ 0
  have hrhs : (ω - ωs) * (((1 - η) * c_sup - t * ωs) / (ωs * (c_sup - t * ωs))) ≤ 0 := by
    by_cases hcase : (1 - η) * c_sup / t ≤ 1
    · have hωs_eq : ωs = (1 - η) * c_sup / t := min_eq_right hcase
      have hzero : (1 - η) * c_sup - t * ωs = 0 := by
        rw [hωs_eq]; field_simp [ne_of_gt ht]; ring
      rw [hzero]; simp
    · push Not at hcase
      have hωs_eq : ωs = 1 := min_eq_left (le_of_lt hcase)
      have hnum_pos : 0 ≤ (1 - η) * c_sup - t * ωs := by
        rw [hωs_eq, mul_one]
        have := (lt_div_iff₀ ht).mp hcase; linarith
      have hfrac_nn : 0 ≤ ((1 - η) * c_sup - t * ωs) / (ωs * (c_sup - t * ωs)) :=
        div_nonneg hnum_pos (mul_nonneg (le_of_lt hωs_pos) (le_of_lt hcs_pos))
      have hω_le : ω - ωs ≤ 0 := by rw [hωs_eq]; linarith
      exact mul_nonpos_of_nonpos_of_nonneg hω_le hfrac_nn
  linarith

/-- Cota global de salida adversa: para todo θ ∈ P, a ≤ K', L ∈ [0, 1) con l₀ ≥ K/2,
    u(θ.η, θ.q K + F(θ.A, K, L) - K', L) ≤ E⁺(K, a; l₀). -/
theorem adverse_exit_le_E_plus (θ : Params) {a l₀ K K' L : ℝ}
    (hK : 0 < K) (hl₀ : K / 2 ≤ l₀) (hK' : a ≤ K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L ≤ E_plus a l₀ K := by
  have hA_max_nn : 0 ≤ A_max := by unfold A_max; norm_num
  have hF_A : F θ.A K L ≤ F A_max K L := F_mono_A θ.hA.2 hK hL.1
  have htan : F A_max K L ≤ F A_max K l₀ + t_val l₀ K * (L - l₀) :=
    tangent_dominance hA_max_nn hK hl₀ hL.1
  have hqK : θ.q * K ≤ q_max * K := mul_le_mul_of_nonneg_right θ.hq.2 (le_of_lt hK)
  set c_sup := S_val l₀ K - a
  set tv := t_val l₀ K
  set ω := 1 - L
  have hc_le : θ.q * K + F θ.A K L - K' ≤ c_sup - tv * ω := by
    calc θ.q * K + F θ.A K L - K'
        ≤ q_max * K + F A_max K L - a := sub_le_sub (add_le_add hqK hF_A) hK'
      _ ≤ q_max * K + (F A_max K l₀ + t_val l₀ K * (L - l₀)) - a :=
        sub_le_sub_right (add_le_add (le_refl (q_max * K)) htan) a
      _ = c_sup - tv * ω := by dsimp [c_sup, tv, ω]; unfold S_val; ring
  have hc_ub_pos : 0 < c_sup - tv * ω := lt_of_lt_of_le hc hc_le
  have hω0 : 0 < ω := by dsimp [ω]; linarith [hL.2]
  have hω1 : ω ≤ 1 := by dsimp [ω]; linarith [hL.1]
  have htv_pos : 0 < tv := by
    dsimp [tv]; unfold t_val t_gen A_max g
    have hl₀_pos : 0 < l₀ := by linarith
    have hg_pos : 0 < 2 * K * l₀ / (K + l₀) := by positivity
    have hsq_pos : 0 < Real.sqrt (2 * K * l₀ / (K + l₀)) := Real.sqrt_pos.mpr hg_pos
    positivity
  have hc_sup_pos : 0 < c_sup := by nlinarith
  have hu_mono : u θ.η (θ.q * K + F θ.A K L - K') L ≤
      θ.η * Real.log (c_sup - tv * ω) + (1 - θ.η) * Real.log ω := by
    unfold u
    have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
    have hlog := Real.log_le_log hc hc_le
    dsimp [ω]; nlinarith
  -- Linealidad en η ∈ [η₋, η₊] => el máximo se alcanza en un extremo {η₋, η₊}
  have hlin : θ.η * Real.log (c_sup - tv * ω) + (1 - θ.η) * Real.log ω ≤
      max (eta_min * Real.log (c_sup - tv * ω) + (1 - eta_min) * Real.log ω)
          (eta_max * Real.log (c_sup - tv * ω) + (1 - eta_max) * Real.log ω) := by
    rcases le_total (Real.log (c_sup - tv * ω)) (Real.log ω) with hle | hge
    · apply le_trans _ (le_max_left _ _)
      nlinarith [θ.hη.1]
    · apply le_trans _ (le_max_right _ _)
      nlinarith [θ.hη.2]
  have hmin := envelope_optimality (η := eta_min) (by unfold eta_min; norm_num)
    (by unfold eta_min; norm_num) hc_sup_pos htv_pos hω0 hω1 hc_ub_pos
  have hmax := envelope_optimality (η := eta_max) (by unfold eta_max; norm_num)
    (by unfold eta_max; norm_num) hc_sup_pos htv_pos hω0 hω1 hc_ub_pos
  unfold E_plus E_plus_branch
  exact le_trans hu_mono (le_trans hlin (max_le_max hmin hmax))

/-! ## 4. Derivadas exactas (F, t, S, c_X, E⁺, R_X y Wronskiano Q_X) -/

lemma hasDerivAt_g {l K : ℝ} (hKl : K + l ≠ 0) :
    HasDerivAt (g l) (2 * l ^ 2 / (K + l) ^ 2) K := by
  unfold g
  have h1 : HasDerivAt (fun x => 2 * x * l) (2 * l) K := by
    simpa using ((hasDerivAt_id K).const_mul 2).mul_const l
  have h2 : HasDerivAt (fun x => x + l) 1 K := (hasDerivAt_id K).add_const l
  convert h1.div h2 hKl using 1
  field_simp [hKl]; ring

lemma hasDerivAt_sqrt_g {l K : ℝ} (hl : 0 < l) (hK : 0 < K) :
    HasDerivAt (fun x => Real.sqrt (g l x))
      (l ^ 2 / (Real.sqrt (g l K) * (K + l) ^ 2)) K := by
  have hKl : K + l ≠ 0 := by linarith
  have hg_pos : 0 < g l K := by unfold g; positivity
  have hsq_ne : Real.sqrt (g l K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg_pos)
  convert (Real.hasDerivAt_sqrt (ne_of_gt hg_pos)).comp K (hasDerivAt_g hKl) using 1
  · rfl
  · field_simp [hKl, hsq_ne]

lemma hasDerivAt_F_K {A l K : ℝ} (hl : 0 < l) (hK : 0 < K) :
    HasDerivAt (fun x => F A x l) (FK A l K) K := by
  have hKl : K + l ≠ 0 := by linarith
  have hg_pos : 0 < g l K := by unfold g; positivity
  have hsq_ne : Real.sqrt (g l K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg_pos)
  have h1 : HasDerivAt (fun x => A * g l x) (A * (2 * l ^ 2 / (K + l) ^ 2)) K :=
    (hasDerivAt_g hKl).const_mul A
  have h2 := hasDerivAt_sqrt_g hl hK
  have hmul := h1.fun_mul h2
  have hFeq : (fun x => F A x l) = fun x => A * g l x * Real.sqrt (g l x) := by
    ext x; unfold F g; ring
  rw [hFeq]
  convert hmul using 1
  unfold FK
  have hsq : Real.sqrt (g l K) ^ 2 = g l K := Real.sq_sqrt (le_of_lt hg_pos)
  field_simp [hKl, hsq_ne]
  rw [hsq]; ring

lemma hasDerivAt_FK_K {A l K : ℝ} (hl : 0 < l) (hK : 0 < K) :
    HasDerivAt (FK A l) (FKK A l K) K := by
  unfold FK
  have hKl : K + l ≠ 0 := by linarith
  have hg_pos : 0 < g l K := by unfold g; positivity
  have hsq_ne : Real.sqrt (g l K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg_pos)
  have hnum := (hasDerivAt_sqrt_g hl hK).const_mul (3 * A * l ^ 2)
  have hden : HasDerivAt (fun x => (x + l) ^ 2) (2 * (K + l)) K := by
    simpa using ((hasDerivAt_id K).add_const l).fun_pow 2
  convert hnum.fun_div hden (pow_ne_zero 2 hKl) using 1
  unfold FKK
  have hsq : Real.sqrt (g l K) ^ 2 = 2 * K * l / (K + l) := Real.sq_sqrt (le_of_lt hg_pos)
  have hsq' : Real.sqrt (g l K) ^ 2 * (K + l) = 2 * K * l := by
    rw [hsq]; field_simp [hKl]
  field_simp [hKl, hsq_ne]
  have hA : A * (l ^ 2 - Real.sqrt (g l K) ^ 2 * (K + l) * 2) = A * (l ^ 2 - 4 * K * l) := by
    rw [hsq']; ring
  linarith

lemma hasDerivAt_t_val {l₀ K : ℝ} (hl₀ : 0 < l₀) (hK : 0 < K) :
    HasDerivAt (t_val l₀) (t_deriv l₀ K) K := by
  unfold t_val t_gen
  have hKl : K + l₀ ≠ 0 := by linarith
  have hKne : K ≠ 0 := ne_of_gt hK
  have hg_pos : 0 < g l₀ K := by unfold g; positivity
  have hsq_ne : Real.sqrt (g l₀ K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg_pos)
  have hK2 : HasDerivAt (fun x => 3 * A_max * x ^ 2) (6 * A_max * K) K := by
    have := (hasDerivAt_pow 2 K).const_mul (3 * A_max)
    convert this using 1; ring
  have hnum := hK2.fun_mul (hasDerivAt_sqrt_g hl₀ hK)
  have hden : HasDerivAt (fun x => (x + l₀) ^ 2) (2 * (K + l₀)) K := by
    simpa using ((hasDerivAt_id K).add_const l₀).fun_pow 2
  convert hnum.fun_div hden (pow_ne_zero 2 hKl) using 1
  unfold t_deriv t_val t_gen
  have hsq : Real.sqrt (g l₀ K) ^ 2 = 2 * K * l₀ / (K + l₀) := Real.sq_sqrt (le_of_lt hg_pos)
  field_simp [hKl, hKne, hsq_ne]
  rw [hsq]
  field_simp [hKl]; ring

lemma hasDerivAt_log_ratio_t {l₀ K : ℝ} (hl₀ : 0 < l₀) (hK : 0 < K) :
    HasDerivAt (fun x => 5 * l₀ / (2 * x * (x + l₀)))
      (-5 * l₀ * (2 * K + l₀) / (2 * K ^ 2 * (K + l₀) ^ 2)) K := by
  have hKl : K + l₀ ≠ 0 := by linarith
  have hKne : K ≠ 0 := ne_of_gt hK
  have hden : HasDerivAt (fun x => 2 * x * (x + l₀)) (2 * (2 * K + l₀)) K := by
    have h1 : HasDerivAt (fun x => 2 * x) 2 K := by simpa using (hasDerivAt_id K).const_mul 2
    have h2 : HasDerivAt (fun x => x + l₀) 1 K := (hasDerivAt_id K).add_const l₀
    convert h1.fun_mul h2 using 1; ring
  have hq := (hasDerivAt_const K (5 * l₀)).fun_div hden (by positivity)
  convert hq using 1
  field_simp [hKl, hKne]; ring

lemma hasDerivAt_t_deriv {l₀ K : ℝ} (hl₀ : 0 < l₀) (hK : 0 < K) :
    HasDerivAt (t_deriv l₀) (t_deriv2 l₀ K) K := by
  unfold t_deriv
  have hKl : K + l₀ ≠ 0 := by linarith
  have hKne : K ≠ 0 := ne_of_gt hK
  convert (hasDerivAt_t_val hl₀ hK).fun_mul (hasDerivAt_log_ratio_t hl₀ hK) using 1
  unfold t_deriv t_deriv2
  field_simp [hKl, hKne]; ring

lemma hasDerivAt_S {l₀ K : ℝ} (hl₀ : 0 < l₀) (hK : 0 < K) :
    HasDerivAt (S_val l₀) (S_deriv l₀ K) K := by
  unfold S_val S_deriv
  have h1 : HasDerivAt (fun x => q_max * x) q_max K := by
    simpa using (hasDerivAt_id K).const_mul q_max
  exact (h1.fun_add (hasDerivAt_F_K hl₀ hK)).fun_add ((hasDerivAt_t_val hl₀ hK).const_mul (1 - l₀))

lemma hasDerivAt_S' {l₀ K : ℝ} (hl₀ : 0 < l₀) (hK : 0 < K) :
    HasDerivAt (S_deriv l₀) (S_deriv2 l₀ K) K := by
  unfold S_deriv S_deriv2
  have h1 := (hasDerivAt_const K q_max).fun_add (hasDerivAt_FK_K (A := A_max) hl₀ hK)
  simpa using h1.fun_add ((hasDerivAt_t_deriv hl₀ hK).const_mul (1 - l₀))

lemma hasDerivAt_cX {lX sX K : ℝ} (hlX : 0 < lX) (hK : 0 < K) :
    HasDerivAt (cX lX sX) (cX_deriv lX K) K := by
  unfold cX cX_deriv
  have h1 : HasDerivAt (fun x => q_min * x) q_min K := by
    simpa using (hasDerivAt_id K).const_mul q_min
  simpa using (h1.fun_add (hasDerivAt_F_K (A := A_min) hlX hK)).fun_sub (hasDerivAt_const K sX)

lemma hasDerivAt_cX' {lX K : ℝ} (hlX : 0 < lX) (hK : 0 < K) :
    HasDerivAt (cX_deriv lX) (cX_deriv2 lX K) K := by
  unfold cX_deriv cX_deriv2
  simpa using (hasDerivAt_const K q_min).fun_add (hasDerivAt_FK_K (A := A_min) hlX hK)

/-- Identidad exacta de la envolvente interior (Proposición 2):
    cuando ω*(K, η) < 1,  dE⁺_η/dK = S'(K)/(S(K) - a) - (1 - η) * 5 l₀ / (2 K (K + l₀)). -/
theorem hasDerivAt_E_plus_interior {η a l₀ K : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hl₀ : 0 < l₀) (hK : 0 < K)
    (hcsup : 0 < S_val l₀ K - a)
    (hint : (1 - η) * (S_val l₀ K - a) / t_val l₀ K < 1) :
    HasDerivAt (E_plus_branch η a l₀)
      (S_deriv l₀ K / (S_val l₀ K - a) - (1 - η) * (5 * l₀ / (2 * K * (K + l₀)))) K := by
  have htv_pos : 0 < t_val l₀ K := by
    unfold t_val t_gen A_max g
    have hg : 0 < 2 * K * l₀ / (K + l₀) := by positivity
    have := Real.sqrt_pos.mpr hg; positivity
  -- En una vecindad de K se mantiene ω* < 1, por lo que E⁺_η coincide con la fórmula explícita
  have hcont_S : ContinuousAt (S_val l₀) K := (hasDerivAt_S hl₀ hK).continuousAt
  have hcont_t : ContinuousAt (t_val l₀) K := (hasDerivAt_t_val hl₀ hK).continuousAt
  have hcont_ω : ContinuousAt (fun x => (1 - η) * (S_val l₀ x - a) / t_val l₀ x) K :=
    ((continuousAt_const.mul (hcont_S.sub continuousAt_const)).div hcont_t (ne_of_gt htv_pos))
  have hnhds1 : ∀ᶠ x in nhds K, (1 - η) * (S_val l₀ x - a) / t_val l₀ x < 1 :=
    hcont_ω.eventually (gt_mem_nhds hint)
  have hnhds2 : ∀ᶠ x in nhds K, 0 < S_val l₀ x - a :=
    (hcont_S.sub continuousAt_const).eventually (lt_mem_nhds hcsup)
  have hnhds3 : ∀ᶠ x in nhds K, 0 < t_val l₀ x :=
    hcont_t.eventually (lt_mem_nhds htv_pos)
  let G : ℝ → ℝ := fun x =>
    Real.log (S_val l₀ x - a) - (1 - η) * Real.log (t_val l₀ x) +
      (η * Real.log η + (1 - η) * Real.log (1 - η))
  have heq : E_plus_branch η a l₀ =ᶠ[nhds K] G := by
    filter_upwards [hnhds1, hnhds2, hnhds3] with x hx1 hx2 hx3
    unfold E_plus_branch omega_star
    dsimp only
    rw [min_eq_right (le_of_lt hx1)]
    have hmul : t_val l₀ x * ((1 - η) * (S_val l₀ x - a) / t_val l₀ x) =
        (1 - η) * (S_val l₀ x - a) := by field_simp [ne_of_gt hx3]
    rw [hmul]
    have hsub : S_val l₀ x - a - (1 - η) * (S_val l₀ x - a) = η * (S_val l₀ x - a) := by ring
    rw [hsub, Real.log_mul (ne_of_gt hη0) (ne_of_gt hx2),
      Real.log_div (ne_of_gt (mul_pos (by linarith) hx2)) (ne_of_gt hx3),
      Real.log_mul (by linarith) (ne_of_gt hx2)]
    dsimp [G]; ring
  have hG : HasDerivAt G
      (S_deriv l₀ K / (S_val l₀ K - a) - (1 - η) * (5 * l₀ / (2 * K * (K + l₀)))) K := by
    have hlogS : HasDerivAt (fun x => Real.log (S_val l₀ x - a))
        (S_deriv l₀ K / (S_val l₀ K - a)) K := by
      simpa using ((hasDerivAt_S hl₀ hK).sub_const a).log (ne_of_gt hcsup)
    have hlogt : HasDerivAt (fun x => Real.log (t_val l₀ x))
        (5 * l₀ / (2 * K * (K + l₀))) K := by
      convert (hasDerivAt_t_val hl₀ hK).log (ne_of_gt htv_pos) using 1
      unfold t_deriv; field_simp [ne_of_gt htv_pos]
    have hconst : HasDerivAt (fun _ => η * Real.log η + (1 - η) * Real.log (1 - η)) 0 K :=
      hasDerivAt_const K _
    have hmul_t := (hasDerivAt_const K (1 - η)).fun_mul hlogt
    dsimp only [G]
    exact ((hlogS.fun_sub hmul_t).fun_add hconst).congr_deriv (by ring)
  exact hG.congr_of_eventuallyEq heq

/-- Derivada del cociente R_X'(K) = Q_X(K) / c_X(K)². -/
theorem hasDerivAt_RX {a l₀ lX sX K : ℝ}
    (hl₀ : 0 < l₀) (hlX : 0 < lX) (hK : 0 < K) (hcX : cX lX sX K ≠ 0) :
    HasDerivAt (RX a l₀ lX sX) (QX a l₀ lX sX K / (cX lX sX K) ^ 2) K := by
  have h1 := (hasDerivAt_S hl₀ hK).fun_sub (hasDerivAt_const K a)
  have h2 := hasDerivAt_cX hlX (sX := sX) hK
  exact (h1.fun_div h2 hcX).congr_deriv (by unfold QX; ring)

/-- Derivada del Wronskiano Q_X'(K) = S''(K) c_X(K) - c_X''(K) (S(K) - a)
    (cancelación exacta del término cruzado S' c_X'). -/
theorem hasDerivAt_QX {a l₀ lX sX K : ℝ}
    (hl₀ : 0 < l₀) (hlX : 0 < lX) (hK : 0 < K) :
    HasDerivAt (QX a l₀ lX sX) (QX_deriv a l₀ lX sX K) K := by
  unfold QX QX_deriv
  have h1 := (hasDerivAt_S' hl₀ hK).fun_mul (hasDerivAt_cX hlX (sX := sX) hK)
  have h2 := (hasDerivAt_cX' hlX hK).fun_mul ((hasDerivAt_S hl₀ hK).sub_const a)
  convert h1.fun_sub h2 using 1; ring

/-! ## 5. Cotas de Δ_X', Δ_X'', monotonicidad global y forma centrada 1D -/

/-- Derivada exacta de cada rama suave Δ_{X, η_W, η_E} y su cota inferior de la Proposición 2. -/
theorem delta_branch_deriv_lb {a l₀ lX sX TX Ψ_a ηW ηE K : ℝ}
    (hηW : eta_min ≤ ηW) (hηE0 : 0 < ηE) (hηE1 : ηE ≤ eta_max)
    (hl₀ : 0 < l₀) (hlX : 0 < lX) (hK : 0 < K)
    (hcX_pos : 0 < cX lX sX K) (hcsup : 0 < S_val l₀ K - a)
    (hint : (1 - ηE) * (S_val l₀ K - a) / t_val l₀ K < 1) :
    let d := ηW * (cX_deriv lX K / cX lX sX K) - S_deriv l₀ K / (S_val l₀ K - a) +
      (1 - ηE) * (5 * l₀ / (2 * K * (K + l₀)))
    HasDerivAt (delta_branch a l₀ lX sX TX Ψ_a ηW ηE) d K ∧
    (eta_min * cX_deriv lX K * RX a l₀ lX sX K - S_deriv l₀ K) / (S_val l₀ K - a) +
      (1 - eta_max) * (5 * l₀ / (2 * K * (K + l₀))) ≤ d := by
  have hηE_lt1 : ηE < 1 := lt_of_le_of_lt hηE1 (by unfold eta_max; norm_num)
  have hW : HasDerivAt (fun x => ηW * Real.log (cX lX sX x) +
      (1 - ηW) * Real.log (1 - lX) + beta_max * TX)
      (ηW * (cX_deriv lX K / cX lX sX K)) K := by
    have hlog := (hasDerivAt_cX hlX hK).log (ne_of_gt hcX_pos)
    simpa using ((hlog.const_mul ηW).add_const ((1 - ηW) * Real.log (1 - lX))).add_const
      (beta_max * TX)
  have hE := (hasDerivAt_E_plus_interior hηE0 hηE_lt1 hl₀ hK hcsup hint).add_const
    (beta_min * Ψ_a)
  refine ⟨?_, ?_⟩
  · unfold delta_branch
    convert hW.sub hE using 1; ring
  · have hcX'_nn : 0 ≤ cX_deriv lX K := by
      unfold cX_deriv q_min FK A_min g
      have := Real.sqrt_nonneg (2 * K * lX / (K + lX)); positivity
    have hfrac_nn : 0 ≤ cX_deriv lX K / cX lX sX K := div_nonneg hcX'_nn (le_of_lt hcX_pos)
    have hterm1 : eta_min * (cX_deriv lX K / cX lX sX K) ≤
        ηW * (cX_deriv lX K / cX lX sX K) := mul_le_mul_of_nonneg_right hηW hfrac_nn
    have hterm2 : (1 - eta_max) * (5 * l₀ / (2 * K * (K + l₀))) ≤
        (1 - ηE) * (5 * l₀ / (2 * K * (K + l₀))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hrew : (eta_min * cX_deriv lX K * RX a l₀ lX sX K - S_deriv l₀ K) / (S_val l₀ K - a) =
        eta_min * (cX_deriv lX K / cX lX sX K) - S_deriv l₀ K / (S_val l₀ K - a) := by
      unfold RX; field_simp [ne_of_gt hcX_pos, ne_of_gt hcsup]
    rw [hrew]; linarith

/-- Si Q_X ≤ 0 en [kL, kR], entonces R_X es decreciente en [kL, kR]. -/
theorem RX_antitone_of_QX_nonpos {a l₀ lX sX kL kR : ℝ}
    (hl₀ : 0 < l₀) (hlX : 0 < lX) (hkL : 0 < kL)
    (hcX : ∀ K ∈ Icc kL kR, 0 < cX lX sX K)
    (hQ : ∀ K ∈ Icc kL kR, QX a l₀ lX sX K ≤ 0) :
    AntitoneOn (RX a l₀ lX sX) (Icc kL kR) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc kL kR) ?_ ?_ ?_
  · exact DifferentiableOn.continuousOn (fun K hK => (hasDerivAt_RX hl₀ hlX
      (lt_of_lt_of_le hkL hK.1) (ne_of_gt (hcX K hK))).differentiableAt.differentiableWithinAt)
  · exact fun K hK => (hasDerivAt_RX hl₀ hlX (lt_of_lt_of_le hkL (interior_subset hK).1)
      (ne_of_gt (hcX K (interior_subset hK)))).differentiableAt.differentiableWithinAt
  · intro K hK
    have hK' := interior_subset hK
    rw [(hasDerivAt_RX hl₀ hlX (lt_of_lt_of_le hkL hK'.1) (ne_of_gt (hcX K hK'))).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (hQ K hK') (sq_nonneg _)

/-- Si la cota inferior de Δ' es ≥ 0 en todo [kL, kR], entonces Δ_X alcanza su mínimo
    exactamente en el borde izquierdo kL (sin necesidad de analizar los quiebres k_W, k_E). -/
theorem delta_X_min_at_left {a l₀ lX sX TX Ψ_a kL kR : ℝ}
    (hl₀ : 0 < l₀) (hlX : 0 < lX) (hkL : 0 < kL)
    (hcX : ∀ K ∈ Icc kL kR, 0 < cX lX sX K)
    (hcsup : ∀ K ∈ Icc kL kR, 0 < S_val l₀ K - a)
    (hint : ∀ η ∈ ({eta_min, eta_max} : Set ℝ), ∀ K ∈ Icc kL kR,
      (1 - η) * (S_val l₀ K - a) / t_val l₀ K < 1)
    (hlb : ∀ K ∈ Icc kL kR,
      0 ≤ (eta_min * cX_deriv lX K * RX a l₀ lX sX K - S_deriv l₀ K) / (S_val l₀ K - a) +
        (1 - eta_max) * (5 * l₀ / (2 * K * (K + l₀)))) :
    ∀ K ∈ Icc kL kR, delta_X a l₀ lX sX TX Ψ_a kL ≤ delta_X a l₀ lX sX TX Ψ_a K := by
  have hbranch : ∀ ηW ∈ ({eta_min, eta_max} : Set ℝ), ∀ ηE ∈ ({eta_min, eta_max} : Set ℝ),
      MonotoneOn (delta_branch a l₀ lX sX TX Ψ_a ηW ηE) (Icc kL kR) := by
    intro ηW hW ηE hE
    have hηW : eta_min ≤ ηW := by
      rcases hW with rfl | rfl
      · exact le_rfl
      · unfold eta_min eta_max; norm_num
    have hηE0 : 0 < ηE := by
      rcases hE with rfl | rfl <;> norm_num [eta_min, eta_max]
    have hηE1 : ηE ≤ eta_max := by
      rcases hE with rfl | rfl
      · unfold eta_min eta_max; norm_num
      · exact le_rfl
    refine monotoneOn_of_deriv_nonneg (convex_Icc kL kR) ?_ ?_ ?_
    · exact DifferentiableOn.continuousOn (fun K hK => (delta_branch_deriv_lb (TX := TX)
        (Ψ_a := Ψ_a) hηW hηE0 hηE1 hl₀ hlX (lt_of_lt_of_le hkL hK.1) (hcX K hK) (hcsup K hK)
        (hint ηE hE K hK)).1.differentiableAt.differentiableWithinAt)
    · exact fun K hK => (delta_branch_deriv_lb (TX := TX) (Ψ_a := Ψ_a) hηW hηE0 hηE1 hl₀ hlX
        (lt_of_lt_of_le hkL (interior_subset hK).1) (hcX K (interior_subset hK))
        (hcsup K (interior_subset hK))
        (hint ηE hE K (interior_subset hK))).1.differentiableAt.differentiableWithinAt
    · intro K hK
      have hK' := interior_subset hK
      have hdb := delta_branch_deriv_lb (TX := TX) (Ψ_a := Ψ_a) hηW hηE0 hηE1 hl₀ hlX
        (lt_of_lt_of_le hkL hK'.1) (hcX K hK') (hcsup K hK') (hint ηE hE K hK')
      rw [hdb.1.deriv]
      exact le_trans (hlb K hK') hdb.2
  intro K hK
  have hkL_mem : kL ∈ Icc kL kR := ⟨le_rfl, le_trans hK.1 hK.2⟩
  unfold delta_X
  exact min_le_min
    (min_le_min (hbranch eta_min (Or.inl rfl) eta_min (Or.inl rfl) hkL_mem hK hK.1)
                (hbranch eta_min (Or.inl rfl) eta_max (Or.inr rfl) hkL_mem hK hK.1))
    (min_le_min (hbranch eta_max (Or.inr rfl) eta_min (Or.inl rfl) hkL_mem hK hK.1)
                (hbranch eta_max (Or.inr rfl) eta_max (Or.inr rfl) hkL_mem hK hK.1))

/-- Lema de forma centrada 1D (puente directo para auditar los 4 + 6 subintervalos de Q_X):
    si |f'(x)| ≤ M en [kL, kR] y f((kL+kR)/2) + M*(kR-kL)/2 ≤ -ε, entonces f ≤ -ε en [kL, kR]. -/
theorem centered_form_neg {f f' : ℝ → ℝ} {kL kR M ε : ℝ} (hle : kL ≤ kR)
    (hderiv : ∀ x ∈ Icc kL kR, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc kL kR, |f' x| ≤ M)
    (hmid : f ((kL + kR) / 2) + M * ((kR - kL) / 2) ≤ -ε) :
    ∀ x ∈ Icc kL kR, f x ≤ -ε := by
  set m := (kL + kR) / 2
  have hm_mem : m ∈ Icc kL kR := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg (f' m)) (hbound m hm_mem)
  intro x hx
  rcases lt_trichotomy x m with hlt | rfl | hgt
  · have hcont : ContinuousOn f (Icc x m) := DifferentiableOn.continuousOn
      (fun z hz => (hderiv z ⟨le_trans hx.1 hz.1,
        le_trans hz.2 hm_mem.2⟩).differentiableAt.differentiableWithinAt)
    have hdiff : ∀ z ∈ Ioo x m, HasDerivAt f (f' z) z :=
      fun z hz => hderiv z ⟨le_trans hx.1 (le_of_lt hz.1), le_trans (le_of_lt hz.2) hm_mem.2⟩
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hdiff
    have hc_mem : c ∈ Icc kL kR :=
      ⟨le_trans hx.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hm_mem.2⟩
    have hsub : f x - f m = -f' c * (m - x) := by
      have hm_ne : m - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have := (eq_div_iff hm_ne).mp hslope
      linarith
    have h1 : -f' c ≤ M := le_trans (neg_le_abs (f' c)) (hbound c hc_mem)
    have h2 : m - x ≤ (kR - kL) / 2 := by dsimp [m]; linarith [hx.1]
    have h3 : f x - f m ≤ M * ((kR - kL) / 2) := by
      rw [hsub]
      calc -f' c * (m - x) ≤ M * (m - x) := mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ M * ((kR - kL) / 2) := mul_le_mul_of_nonneg_left h2 hM_nn
    linarith
  · have hrad : 0 ≤ (kR - kL) / 2 := by linarith
    nlinarith
  · have hcont : ContinuousOn f (Icc m x) := DifferentiableOn.continuousOn
      (fun z hz => (hderiv z ⟨le_trans hm_mem.1 hz.1,
        le_trans hz.2 hx.2⟩).differentiableAt.differentiableWithinAt)
    have hdiff : ∀ z ∈ Ioo m x, HasDerivAt f (f' z) z :=
      fun z hz => hderiv z ⟨le_trans hm_mem.1 (le_of_lt hz.1), le_trans (le_of_lt hz.2) hx.2⟩
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hgt hcont hdiff
    have hc_mem : c ∈ Icc kL kR :=
      ⟨le_trans hm_mem.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hx.2⟩
    have hsub : f x - f m = f' c * (x - m) := by
      have hx_ne : x - m ≠ 0 := sub_ne_zero.mpr (ne_of_gt hgt)
      have := (eq_div_iff hx_ne).mp hslope
      linarith
    have h1 : f' c ≤ M := le_trans (le_abs_self (f' c)) (hbound c hc_mem)
    have h2 : x - m ≤ (kR - kL) / 2 := by dsimp [m]; linarith [hx.2]
    have h3 : f x - f m ≤ M * ((kR - kL) / 2) := by
      rw [hsub]
      calc f' c * (x - m) ≤ M * (x - m) := mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ M * ((kR - kL) / 2) := mul_le_mul_of_nonneg_left h2 hM_nn
    linarith

end

end MVS.Proposition2
