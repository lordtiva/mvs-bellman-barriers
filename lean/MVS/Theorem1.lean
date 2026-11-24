import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import MVS.Lemma11

set_option linter.style.header false

/-!
# Lema 1 y Teorema 1 (MR): Reducción analítica a la mitad

Formalización de la cota inferior afín de un paso (Lema 1) y de la reducción
analítica $\tau_H \le 46 \to \tau_H \le 23$ (Teorema 1) sin derivadas ni `sorry`.
-/

open Finset Real

namespace MVS.Theorem1

noncomputable section

/-! ## 1. Calibración paramétrica de referencia (Sección 3.1) -/

/-- Extremos de la caja compacta de parámetros P de MR (2026). -/
def A_min : ℝ := 749 / 1000
def A_max : ℝ := 751 / 1000
def q_min : ℝ := 9199 / 10000
def q_max : ℝ := 9201 / 10000
def beta_min : ℝ := 9699 / 10000
def beta_max : ℝ := 9701 / 10000
def eta_min : ℝ := 6999 / 10000
def eta_max : ℝ := 7001 / 10000

/-- Región de tránsito M = [b, h) = [0.10, 0.28). -/
def b : ℝ := 1 / 10
def h : ℝ := 28 / 100

/-- Constantes analíticas exactas (racionales) del Lema 1 y Teorema 1. -/
def C_max_ub : ℝ := 37495167 / 100000000
def R_hat : ℝ := -996 / 1000
def Delta2 : ℝ := 2997 / 10000
def m_omega : ℝ := eta_min * q_min / C_max_ub

/-- Parámetros del modelo dentro de la caja compacta P. -/
structure Params where
  A : ℝ
  q : ℝ
  β : ℝ
  η : ℝ
  hA : A_min ≤ A ∧ A ≤ A_max
  hq : q_min ≤ q ∧ q ≤ q_max
  hβ : beta_min ≤ β ∧ β ≤ beta_max
  hη : eta_min ≤ η ∧ η ≤ eta_max

/-- Producción CES armónica (θ = 3/2, ρ = -1): F_A(K, L) = A * (2KL/(K+L))^(3/2).
    Se expresa como x * √x para x ≥ 0, evitando `rpow` innecesario. -/
def F (A K L : ℝ) : ℝ :=
  let x := 2 * K * L / (K + L)
  A * x * Real.sqrt x

/-- Utilidad de período u(c, L) = η log c + (1 - η) log (1 - L). -/
def u (η c L : ℝ) : ℝ :=
  η * Real.log c + (1 - η) * Real.log (1 - L)

/-- Barrera afín de un paso B₁(K) = B_*(β) - m_ω (h - K). -/
def B_star (β : ℝ) : ℝ := (R_hat - Delta2) / (1 - β)
def B_star_max : ℝ := B_star beta_min
def B1 (β K : ℝ) : ℝ := B_star β - m_omega * (h - K)
def B1_max (K : ℝ) : ℝ := B_star_max - m_omega * (h - K)

/-- Techo analítico Ψ♯(x) = 0.4 x - 5 x^(-1/2) - 18.5 - 10/301 de MR (Lema 12 / Ap. F.3). -/
def Psi_sharp (x : ℝ) : ℝ :=
  (4 / 10 : ℝ) * x - 5 / Real.sqrt x - (185 / 10 : ℝ) - (10 / 301 : ℝ)

/-! ## 2. Lemas auxiliares de monotonicidad y cotas racionales -/

lemma F_mono_K {A K₁ K₂ L : ℝ} (hA : 0 ≤ A) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) (hL : 0 ≤ L) :
    F A K₁ L ≤ F A K₂ L := by
  unfold F
  set x₁ := 2 * K₁ * L / (K₁ + L)
  set x₂ := 2 * K₂ * L / (K₂ + L)
  have hx₁ : 0 ≤ x₁ := div_nonneg (by positivity) (by linarith)
  have hle : x₁ ≤ x₂ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hdiff : 0 ≤ 2 * (K₂ - K₁) * L ^ 2 := mul_nonneg (by linarith) (sq_nonneg L)
    linarith
  have hsq : Real.sqrt x₁ ≤ Real.sqrt x₂ := Real.sqrt_le_sqrt hle
  have hmul : x₁ * Real.sqrt x₁ ≤ x₂ * Real.sqrt x₂ :=
    mul_le_mul hle hsq (Real.sqrt_nonneg x₁) (le_trans hx₁ hle)
  have hmulA := mul_le_mul_of_nonneg_left hmul hA
  linarith

lemma F_mono_L {A K L₁ L₂ : ℝ} (hA : 0 ≤ A) (hK : 0 < K) (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) :
    F A K L₁ ≤ F A K L₂ := by
  unfold F
  set x₁ := 2 * K * L₁ / (K + L₁)
  set x₂ := 2 * K * L₂ / (K + L₂)
  have hx₁ : 0 ≤ x₁ := div_nonneg (by positivity) (by linarith)
  have hle : x₁ ≤ x₂ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hdiff : 0 ≤ 2 * (L₂ - L₁) * K ^ 2 := mul_nonneg (by linarith) (sq_nonneg K)
    linarith
  have hsq : Real.sqrt x₁ ≤ Real.sqrt x₂ := Real.sqrt_le_sqrt hle
  have hmul : x₁ * Real.sqrt x₁ ≤ x₂ * Real.sqrt x₂ :=
    mul_le_mul hle hsq (Real.sqrt_nonneg x₁) (le_trans hx₁ hle)
  have hmulA := mul_le_mul_of_nonneg_left hmul hA
  linarith

lemma F_mono_A {A₁ A₂ K L : ℝ} (hA : A₁ ≤ A₂) (hK : 0 < K) (hL : 0 ≤ L) :
    F A₁ K L ≤ F A₂ K L := by
  unfold F
  have hx : 0 ≤ 2 * K * L / (K + L) := div_nonneg (by positivity) (by linarith)
  have hprod : 0 ≤ (2 * K * L / (K + L)) * Real.sqrt (2 * K * L / (K + L)) :=
    mul_nonneg hx (Real.sqrt_nonneg _)
  have := mul_le_mul_of_nonneg_right hA hprod
  linarith

/-- Certificación exacta por elevación al cuadrado: q₊ h + F_{A₊}(h, 1) - b ≤ 0.37495167. -/
lemma C_max_ub_valid : q_max * h + F A_max h 1 - b ≤ C_max_ub := by
  unfold F q_max A_max h b C_max_ub
  have hrat : (2 * (28 / 100 : ℝ) * 1 / (28 / 100 + 1)) = 7 / 16 := by norm_num
  rw [hrat]
  have hsq_le : ((751 / 1000 : ℝ) * (7 / 16) * Real.sqrt (7 / 16)) ^ 2 ≤
      (21732367 / 100000000 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hnn : 0 ≤ (751 / 1000 : ℝ) * (7 / 16) * Real.sqrt (7 / 16) := by positivity
  have hbound : (751 / 1000 : ℝ) * (7 / 16) * Real.sqrt (7 / 16) ≤ 21732367 / 100000000 := by
    nlinarith
  linarith

/-- Holgura exacta Δ₂^exact > Δ₂ = 0.2997. -/
lemma Delta2_le_exact : Delta2 ≤ eta_min * beta_min * q_min * (h - b) / C_max_ub := by
  unfold Delta2 eta_min beta_min q_min h b C_max_ub
  norm_num

/-- Certificación completa de R_hat = -0.996 para todo L ∈ [0, 1) usando `MVS.Lemma11`
    y una cota tangente polinomial exacta en L₀ = 28 * (769/1000)^2 / (1 - (769/1000)^2). -/
lemma R_hat_valid (θ : Params) {L : ℝ} (hL : 0 ≤ L ∧ L < 1) :
    u θ.η (q_max * h + F A_max h L - b) L ≤ R_hat := by
  set s : ℝ := 769 / 1000
  set L0 : ℝ := h * s ^ 2 / (1 - s ^ 2)
  set f0 : ℝ := s ^ 3
  set alpha : ℝ := (3 / 2 : ℝ) * s * (1 - s ^ 2) ^ 2 / h
  set rt2h_ub : ℝ := 748332 / 1000000
  set coef : ℝ := 2 * h * rt2h_ub
  set c0 : ℝ := q_max * h - b + A_max * coef * f0
  set m0 : ℝ := A_max * coef * alpha
  set c1 : ℝ := q_max * h + F A_max h L - b
  -- 1. Cota superior para √(2h)
  have hh_pos : 0 < h := by unfold h; norm_num
  have hrt2h : Real.sqrt (2 * h) ≤ rt2h_ub := by
    have hsq : (Real.sqrt (2 * h)) ^ 2 ≤ rt2h_ub ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      norm_num [h, rt2h_ub]
    have hnn : 0 ≤ Real.sqrt (2 * h) := Real.sqrt_nonneg _
    have hrt_nn : 0 ≤ rt2h_ub := by norm_num [rt2h_ub]
    nlinarith
  -- 2. Cota tangente algebraica para (L/(h+L))^(3/2) ≤ f0 + alpha * (L - L0) para todo L ≥ 0
  have hL_frac : L / (h + L) * Real.sqrt (L / (h + L)) ≤ f0 + alpha * (L - L0) := by
    set y : ℝ := L / (h + L)
    set rhs : ℝ := f0 + alpha * (L - L0)
    have hy_nn : 0 ≤ y := div_nonneg hL.1 (by linarith)
    have hrhs_pos : 0 < rhs := by
      have h0 : 0 < f0 - alpha * L0 := by norm_num [h, s, L0, f0, alpha]
      have ha : 0 < alpha := by norm_num [h, s, alpha]
      dsimp [rhs]; nlinarith [hL.1]
    have hpoly : (h + L) ^ 3 * rhs ^ 2 - L ^ 3 = (L - L0) ^ 2 * (
        (3028714663705269079095626841 / 6400000000000000000000000000 : ℝ) * L ^ 3 +
        (163710870993744748227364163661 / 160000000000000000000000000000 : ℝ) * L ^ 2 +
        (388796538766320872556041145627 / 4000000000000000000000000000000 : ℝ) * L +
        (414195527309660738881244006463 / 100000000000000000000000000000000 : ℝ)) := by
      dsimp [rhs, alpha, f0, L0, s]; unfold h; ring
    have hL0 : 0 ≤ L := hL.1
    have hpoly_nn : 0 ≤ (h + L) ^ 3 * rhs ^ 2 - L ^ 3 := by
      rw [hpoly]
      positivity
    have hdiv_le : y ^ 3 ≤ rhs ^ 2 := by
      dsimp [y]
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    have hsq_le : (y * Real.sqrt y) ^ 2 ≤ rhs ^ 2 := by
      calc (y * Real.sqrt y) ^ 2 = y ^ 2 * (Real.sqrt y) ^ 2 := by ring
        _ = y ^ 2 * y := by rw [Real.sq_sqrt hy_nn]
        _ = y ^ 3 := by ring
        _ ≤ rhs ^ 2 := hdiv_le
    have hmul_nn : 0 ≤ y * Real.sqrt y := mul_nonneg hy_nn (Real.sqrt_nonneg _)
    nlinarith
  -- 3. Cota lineal c1 ≤ c0 + m0 * (L - L0)
  have hc1_le : c1 ≤ c0 + m0 * (L - L0) := by
    have hF_eq : F A_max h L =
        A_max * ((2 * h * Real.sqrt (2 * h)) * (L / (h + L) * Real.sqrt (L / (h + L)))) := by
      unfold F
      dsimp only
      have hrew : 2 * h * L / (h + L) = (2 * h) * (L / (h + L)) := by ring
      rw [hrew, Real.sqrt_mul (by positivity : 0 ≤ 2 * h)]
      ring
    have hprod_le : (2 * h * Real.sqrt (2 * h)) * (L / (h + L) * Real.sqrt (L / (h + L))) ≤
        coef * (f0 + alpha * (L - L0)) := by
      have h1 : 2 * h * Real.sqrt (2 * h) ≤ coef := by
        dsimp [coef]; nlinarith
      have h2 : 0 ≤ L / (h + L) * Real.sqrt (L / (h + L)) :=
        mul_nonneg (div_nonneg hL.1 (by linarith)) (Real.sqrt_nonneg _)
      exact mul_le_mul h1 hL_frac h2 (by norm_num [h, coef, rt2h_ub])
    have hA_nn : 0 ≤ A_max := by unfold A_max; norm_num
    have hmulA := mul_le_mul_of_nonneg_left hprod_le hA_nn
    dsimp [c1, c0, m0]
    rw [hF_eq]
    linarith
  -- 4. Concavidad de log en c1 y en (1 - L)
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    have hF_nn : 0 ≤ F A_max h L := by
      unfold F A_max
      have hL0 : 0 ≤ L := hL.1
      have : 0 ≤ 2 * h * L / (h + L) := div_nonneg (by positivity) (by linarith)
      exact mul_nonneg (mul_nonneg (by norm_num) this) (Real.sqrt_nonneg _)
    have hqb : 0 < q_max * h - b := by unfold q_max h b; norm_num
    linarith
  have hc0_pos : 0 < c0 := by norm_num [q_max, h, b, A_max, s, f0, coef, rt2h_ub, c0]
  have hlog_c1 : Real.log c1 ≤ Real.log c0 + m0 * (L - L0) / c0 := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hc1_pos hc0_pos)
    rw [Real.log_div (ne_of_gt hc1_pos) (ne_of_gt hc0_pos)] at hconc
    have hle1 : c1 / c0 - 1 ≤ (c0 + m0 * (L - L0)) / c0 - 1 := by
      linarith [div_le_div_of_nonneg_right hc1_le (le_of_lt hc0_pos)]
    have hrew : (c0 + m0 * (L - L0)) / c0 - 1 = m0 * (L - L0) / c0 := by
      have hc0_ne : c0 ≠ 0 := ne_of_gt hc0_pos
      field_simp [hc0_ne]; ring
    linarith
  have h1mL_pos : 0 < 1 - L := by linarith [hL.2]
  have h1mL0_pos : 0 < 1 - L0 := by norm_num [h, s, L0]
  have hlog_1mL : Real.log (1 - L) ≤ Real.log (1 - L0) - (L - L0) / (1 - L0) := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos h1mL_pos h1mL0_pos)
    rw [Real.log_div (ne_of_gt h1mL_pos) (ne_of_gt h1mL0_pos)] at hconc
    have hrew : (1 - L) / (1 - L0) - 1 = -((L - L0) / (1 - L0)) := by
      have hne : 1 - L0 ≠ 0 := ne_of_gt h1mL0_pos
      field_simp [hne]; ring
    linarith
  -- 5. Evaluación certificada de log(c0) y log(1 - L0) vía MVS.Lemma11
  set rL_c0 : ℝ := 13503 / 10000
  set rL_1mL0 : ℝ := 6483 / 5000
  have hlog_c0_ub : Real.log c0 ≤
      -((2 ^ 2 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_c0 - 1) / (rL_c0 + 1))) := by
    have hinv_le : rL_c0 ^ (2 ^ 2) ≤ 1 / c0 := by
      norm_num [q_max, h, b, A_max, s, f0, coef, rt2h_ub, c0, rL_c0]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 2 (m := 1 / c0) (rL := rL_c0)
      (rU := (4 : ℝ)) (by norm_num [rL_c0]) (by norm_num)
      hinv_le (by norm_num [q_max, h, b, A_max, s, f0, coef, rt2h_ub, c0])).1
    rw [Real.log_div (by norm_num) (ne_of_gt hc0_pos), Real.log_one, zero_sub] at hb
    linarith
  have hlog_1mL0_ub : Real.log (1 - L0) ≤
      -((2 ^ 1 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_1mL0 - 1) / (rL_1mL0 + 1))) := by
    have hinv_le : rL_1mL0 ^ (2 ^ 1) ≤ 1 / (1 - L0) := by
      norm_num [h, s, L0, rL_1mL0]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 1 (m := 1 / (1 - L0)) (rL := rL_1mL0)
      (rU := (2 : ℝ)) (by norm_num [rL_1mL0]) (by norm_num)
      hinv_le (by norm_num [h, s, L0])).1
    rw [Real.log_div (by norm_num) (ne_of_gt h1mL0_pos), Real.log_one, zero_sub] at hb
    linarith
  -- 6. Signo de los logs y combinación lineal final
  set log_c0_ub : ℝ := -((2 ^ 2 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_c0 - 1) / (rL_c0 + 1)))
  set log_1mL0_ub : ℝ := -((2 ^ 1 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_1mL0 - 1) / (rL_1mL0 + 1)))
  have hc1_log_le : Real.log c1 ≤ log_c0_ub + m0 * (L - L0) / c0 := by linarith
  have hc1_rhs_nonpos : log_c0_ub + m0 * (L - L0) / c0 ≤ 0 := by
    dsimp [log_c0_ub]
    unfold MVS.Lemma11.atanhSeries
    have hm0_nn : 0 ≤ m0 := by norm_num [h, A_max, m0, coef, rt2h_ub, alpha, s]
    have hL_le : m0 * (L - L0) / c0 ≤ m0 * (1 - L0) / c0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hL.2]) hm0_nn)
        (le_of_lt hc0_pos)
    have hnum : -((2 ^ 2 : ℝ) * (2 * ∑ j ∈ range 3, ((rL_c0 - 1) / (rL_c0 + 1)) ^ (2 * j + 1) /
        (2 * j + 1 : ℝ))) + m0 * (1 - L0) / c0 ≤ 0 := by
      norm_num [Finset.sum_range_succ, q_max, h, b, A_max, rL_c0, m0, c0, coef, rt2h_ub, alpha,
        f0, L0, s]
    linarith
  have hterm1 : θ.η * Real.log c1 ≤ eta_min * (log_c0_ub + m0 * (L - L0) / c0) := by
    have hη_nn : 0 ≤ eta_min := by unfold eta_min; norm_num
    calc θ.η * Real.log c1
        ≤ θ.η * (log_c0_ub + m0 * (L - L0) / c0) :=
          mul_le_mul_of_nonneg_left hc1_log_le (le_trans hη_nn θ.hη.1)
      _ ≤ eta_min * (log_c0_ub + m0 * (L - L0) / c0) :=
          mul_le_mul_of_nonpos_right θ.hη.1 hc1_rhs_nonpos
  have h1mL_log_nonpos : Real.log (1 - L) ≤ 0 :=
    Real.log_nonpos (le_of_lt h1mL_pos) (by linarith [hL.1])
  have hterm2 : (1 - θ.η) * Real.log (1 - L) ≤
      (1 - eta_max) * (log_1mL0_ub - (L - L0) / (1 - L0)) := by
    have h1mη_nn : 0 ≤ 1 - eta_max := by unfold eta_max; norm_num
    calc (1 - θ.η) * Real.log (1 - L)
        ≤ (1 - eta_max) * Real.log (1 - L) :=
          mul_le_mul_of_nonpos_right (by linarith [θ.hη.2]) h1mL_log_nonpos
      _ ≤ (1 - eta_max) * (log_1mL0_ub - (L - L0) / (1 - L0)) :=
          mul_le_mul_of_nonneg_left (by linarith) h1mη_nn
  -- 7. Evaluación lineal en los extremos L = 0 y L = 1
  set val : ℝ → ℝ := fun x =>
    eta_min * (log_c0_ub + m0 * (x - L0) / c0) +
    (1 - eta_max) * (log_1mL0_ub - (x - L0) / (1 - L0))
  have hval_lin : val L = (1 - L) * val 0 + L * val 1 := by
    dsimp [val]; ring
  have hval0 : val 0 ≤ R_hat := by
    dsimp [val, log_c0_ub, log_1mL0_ub]
    unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_min, eta_max, q_max, h, b, A_max, R_hat,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h_ub, alpha, f0, L0, s]
  have hval1 : val 1 ≤ R_hat := by
    dsimp [val, log_c0_ub, log_1mL0_ub]
    unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_min, eta_max, q_max, h, b, A_max, R_hat,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h_ub, alpha, f0, L0, s]
  have hval_le : val L ≤ R_hat := by
    rw [hval_lin]
    nlinarith [hL.1, hL.2]
  unfold u
  dsimp [c1] at hterm1
  linarith

/-! ## 3. Lema 1: Cota inferior afín de un paso y margen del testigo -/

/-- Lema 1 (Parte 1): Desigualdad de Bellman de un paso para la barrera afín B₁(K) en M × M. -/
theorem lemma1_one_step_bellman (θ : Params) {K K' L : ℝ}
    (hK : b ≤ K ∧ K < h) (hK' : b ≤ K' ∧ K' < h) (hL : 0 ≤ L ∧ L < 1)
    (hc0 : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * B1 θ.β K' ≤ B1 θ.β K := by
  have hR_hat : u θ.η (q_max * h + F A_max h L - b) L ≤ R_hat := R_hat_valid θ hL
  set c₀ := θ.q * K + F θ.A K L - K'
  set c₁ := q_max * h + F A_max h L - b
  have hA_pos : 0 ≤ A_max := by unfold A_max; norm_num
  have hK_pos : 0 < K := by unfold b at hK; linarith
  have hh_pos : 0 < h := by unfold h; norm_num
  -- 1. c₁ ≤ C_max_ub
  have hc1_le : c₁ ≤ C_max_ub := by
    have hFL : F A_max h L ≤ F A_max h 1 := F_mono_L hA_pos hh_pos hL.1 (le_of_lt hL.2)
    linarith [C_max_ub_valid]
  -- 2. c₁ - c₀ ≥ q_min * (h - K) + (K' - b) ≥ 0
  have hF_le : F θ.A K L ≤ F A_max h L :=
    le_trans (F_mono_A θ.hA.2 hK_pos hL.1) (F_mono_K hA_pos hK_pos (le_of_lt hK.2) hL.1)
  have hdiff : q_min * (h - K) + (K' - b) ≤ c₁ - c₀ := by
    have hq_step : q_min * (h - K) ≤ q_max * h - θ.q * K := by
      have : θ.q * (h - K) ≤ q_max * h - θ.q * K := by nlinarith [θ.hq.2, hh_pos]
      have : q_min * (h - K) ≤ θ.q * (h - K) := by nlinarith [θ.hq.1, hK.2]
      linarith
    dsimp [c₁, c₀]
    linarith
  have hdiff_nn : 0 ≤ q_min * (h - K) + (K' - b) := by
    unfold q_min; nlinarith [hK.2, hK'.1]
  have hc1_pos : 0 < c₁ := by linarith
  -- 3. Concavidad de log: log(c₁) - log(c₀) ≥ (c₁ - c₀) / c₁
  have hlog : (c₁ - c₀) / c₁ ≤ Real.log c₁ - Real.log c₀ := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hc0 hc1_pos)
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt hc1_pos)] at hconc
    have hrew : 1 - c₀ / c₁ = (c₁ - c₀) / c₁ := by
      have hc1_ne : c₁ ≠ 0 := ne_of_gt hc1_pos
      field_simp [hc1_ne]
    linarith
  have hlog_lb : (q_min * (h - K) + (K' - b)) / C_max_ub ≤ Real.log c₁ - Real.log c₀ := by
    have h1 : (q_min * (h - K) + (K' - b)) / C_max_ub ≤ (q_min * (h - K) + (K' - b)) / c₁ :=
      div_le_div_of_nonneg_left hdiff_nn hc1_pos hc1_le
    have h2 : (q_min * (h - K) + (K' - b)) / c₁ ≤ (c₁ - c₀) / c₁ :=
      div_le_div_of_nonneg_right hdiff (le_of_lt hc1_pos)
    linarith
  -- 4. Cota de utilidad instantánea
  have hu_bound : u θ.η c₀ L ≤ R_hat - m_omega * (h - K) - (eta_min / C_max_ub) * (K' - b) := by
    have heta_nn : 0 ≤ eta_min := by unfold eta_min; norm_num
    have hC_pos : 0 < C_max_ub := by unfold C_max_ub; norm_num
    have hlog_nn : 0 ≤ (q_min * (h - K) + (K' - b)) / C_max_ub :=
      div_nonneg hdiff_nn (le_of_lt hC_pos)
    have hmul : eta_min * ((q_min * (h - K) + (K' - b)) / C_max_ub) ≤
        θ.η * (Real.log c₁ - Real.log c₀) :=
      mul_le_mul θ.hη.1 hlog_lb hlog_nn (le_trans heta_nn θ.hη.1)
    have hu_diff : u θ.η c₁ L - u θ.η c₀ L = θ.η * (Real.log c₁ - Real.log c₀) := by
      unfold u; ring
    unfold m_omega
    have : eta_min * ((q_min * (h - K) + (K' - b)) / C_max_ub) =
        eta_min * q_min / C_max_ub * (h - K) + eta_min / C_max_ub * (K' - b) := by ring
    linarith
  -- 5. Combinación lineal en K' y cierre de Bellman
  have hβ_ub : θ.β ≤ beta_max := θ.hβ.2
  have hβ_lb : beta_min ≤ θ.β := θ.hβ.1
  have hK'_comb : beta_min * q_min * (h - b) ≤ (K' - b) + θ.β * q_min * (h - K') := by
    have hβq_lt : θ.β * q_min ≤ 1 := by
      unfold beta_max q_min at *; nlinarith
    have h1 : (1 - θ.β * q_min) * (K' - b) ≥ 0 := mul_nonneg (by linarith) (by linarith [hK'.1])
    have h2 : beta_min * q_min * (h - b) ≤ θ.β * q_min * (h - b) := by
      unfold q_min h b at *; nlinarith
    nlinarith
  have hDelta : Delta2 ≤ (eta_min / C_max_ub) * ((K' - b) + θ.β * q_min * (h - K')) := by
    have hfac : 0 ≤ eta_min / C_max_ub := by unfold eta_min C_max_ub; positivity
    have hmul := mul_le_mul_of_nonneg_left hK'_comb hfac
    have hrew : eta_min / C_max_ub * (beta_min * q_min * (h - b)) =
        eta_min * beta_min * q_min * (h - b) / C_max_ub := by ring
    linarith [Delta2_le_exact]
  have hBstar_eq : R_hat - Delta2 + θ.β * B_star θ.β = B_star θ.β := by
    unfold B_star
    have h1β : 1 - θ.β ≠ 0 := by unfold beta_max at hβ_ub; linarith
    field_simp [h1β]
    ring
  have hrew_prod : θ.β * (eta_min * q_min / C_max_ub * (h - K')) =
      eta_min / C_max_ub * (θ.β * q_min * (h - K')) := by ring
  have hrew_add : eta_min / C_max_ub * (K' - b + θ.β * q_min * (h - K')) =
      eta_min / C_max_ub * (K' - b) + eta_min / C_max_ub * (θ.β * q_min * (h - K')) := by ring
  unfold B1 m_omega at *
  linarith

/-- Cota uniforme B_*(β) ≤ B_*^max en la caja P. -/
lemma B_star_le_max (θ : Params) : B_star θ.β ≤ B_star_max := by
  have hβ_ub : θ.β ≤ beta_max := θ.hβ.2
  have hβ_lb : beta_min ≤ θ.β := θ.hβ.1
  unfold B_star_max
  unfold B_star
  have hnum : R_hat - Delta2 ≤ 0 := by unfold R_hat Delta2; norm_num
  have hden_pos : 0 < 1 - θ.β := by unfold beta_max at hβ_ub; linarith
  have hden_le : 1 - θ.β ≤ 1 - beta_min := by linarith
  have hpos := div_le_div_of_nonneg_left (neg_nonneg.mpr hnum) hden_pos hden_le
  have h1 : -(R_hat - Delta2) / (1 - beta_min) = -((R_hat - Delta2) / (1 - beta_min)) := by ring
  have h2 : -(R_hat - Delta2) / (1 - θ.β) = -((R_hat - Delta2) / (1 - θ.β)) := by ring
  linarith

/-- Lema 1 (Parte 2): Monotonicidad estado a estado del margen W_M(K) - B₁^max(K) sin derivadas.
    Aquí W_M(K) = η_act * log(c_M(K)) + C_tail con c_M(K) = q_- K + F_{A_-}(K, 0.68) - 0.135. -/
theorem lemma1_witness_margin {K η_act C_tail : ℝ}
    (hK : b ≤ K ∧ K < h) (hη : eta_min ≤ η_act) :
    let cM := fun x => q_min * x + F A_min x (68 / 100) - (135 / 1000)
    let WM := fun x => η_act * Real.log (cM x) + C_tail
    WM b - B1_max b ≤ WM K - B1_max K := by
  intro cM WM
  -- Positividad estricta de cM(b) por elevación al cuadrado
  have hcMb_pos : 0 < cM b := by
    dsimp [cM]
    unfold F q_min A_min b
    have hrat : (2 * (1 / 10 : ℝ) * (68 / 100) / (1 / 10 + 68 / 100)) = 34 / 195 := by norm_num
    rw [hrat]
    have hsq : (4301 / 100000 : ℝ) ^ 2 <
        ((749 / 1000 : ℝ) * (34 / 195) * Real.sqrt (34 / 195)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hnn : 0 ≤ (749 / 1000 : ℝ) * (34 / 195) * Real.sqrt (34 / 195) := by positivity
    nlinarith
  -- cM(K) - cM(b) ≥ q_min * (K - b) ≥ 0
  have hF_mono : F A_min b (68 / 100) ≤ F A_min K (68 / 100) :=
    F_mono_K (by unfold A_min; norm_num) (by unfold b; norm_num) hK.1 (by norm_num)
  have hdiff : q_min * (K - b) ≤ cM K - cM b := by dsimp [cM]; linarith
  have hdiff_nn : 0 ≤ q_min * (K - b) := by unfold q_min; nlinarith [hK.1]
  have hcMK_pos : 0 < cM K := by linarith
  -- cM(K) ≤ C_max_ub (dominado término a término por q_+ h + F_{A_+}(h, 1) - b)
  have hcMK_le : cM K ≤ C_max_ub := by
    have hF1 : F A_min K (68 / 100) ≤ F A_max K (68 / 100) :=
      F_mono_A (by unfold A_min A_max; norm_num) (by unfold b at hK; linarith) (by norm_num)
    have hF2 : F A_max K (68 / 100) ≤ F A_max h (68 / 100) :=
      F_mono_K (by unfold A_max; norm_num) (by unfold b at hK; linarith)
        (le_of_lt hK.2) (by norm_num)
    have hF3 : F A_max h (68 / 100) ≤ F A_max h 1 :=
      F_mono_L (by unfold A_max; norm_num) (by unfold h; norm_num) (by norm_num) (by norm_num)
    have hqK : q_min * K ≤ q_max * h := by
      unfold q_min q_max h b at *; nlinarith [hK.1, hK.2]
    have hb_eq : b = 1 / 10 := rfl
    dsimp [cM]
    linarith [C_max_ub_valid]
  -- Concavidad de log
  have hlog : (cM K - cM b) / cM K ≤ Real.log (cM K) - Real.log (cM b) := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hcMb_pos hcMK_pos)
    rw [Real.log_div (ne_of_gt hcMb_pos) (ne_of_gt hcMK_pos)] at hconc
    have hrew : 1 - cM b / cM K = (cM K - cM b) / cM K := by
      have hne : cM K ≠ 0 := ne_of_gt hcMK_pos
      field_simp [hne]
    linarith
  have hlog_lb : q_min * (K - b) / C_max_ub ≤ Real.log (cM K) - Real.log (cM b) := by
    have h1 := div_le_div_of_nonneg_left hdiff_nn hcMK_pos hcMK_le
    have h2 := div_le_div_of_nonneg_right hdiff (le_of_lt hcMK_pos)
    linarith
  have hC_pos : 0 < C_max_ub := by unfold C_max_ub; norm_num
  have hη_pos : 0 ≤ η_act := le_trans (by unfold eta_min; norm_num) hη
  have hmul : eta_min * (q_min * (K - b) / C_max_ub) ≤
      η_act * (Real.log (cM K) - Real.log (cM b)) :=
    mul_le_mul hη hlog_lb (div_nonneg hdiff_nn (le_of_lt hC_pos)) hη_pos
  have hring : eta_min * (q_min * (K - b) / C_max_ub) =
      eta_min * q_min / C_max_ub * (h - b) - eta_min * q_min / C_max_ub * (h - K) := by ring
  dsimp [WM]
  unfold B1_max m_omega
  linarith

/-! ## 4. Teorema 1: Reducción analítica exacta a la mitad (τ_H ≤ 46 → τ_H ≤ 23) -/

/-- Inducción telescópica finita para cualquier sub-barrera de Bellman de un paso. -/
theorem telescoping_bellman {β : ℝ} (hβ : 0 ≤ β) (B : ℝ → ℝ) (u_seq x : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, u_seq t + β * B (x (t + 1)) ≤ B (x t)) :
    ∑ t ∈ range T, β ^ t * u_seq t ≤ B (x 0) - β ^ T * B (x T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have ihn := ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))
    have hlast := mul_le_mul_of_nonneg_left (hstep n (Nat.lt_succ_self n)) (pow_nonneg hβ n)
    have hpow : β ^ (n + 1) = β ^ n * β := pow_succ β n
    have hrew : β ^ n * (u_seq n + β * B (x (n + 1))) =
        β ^ n * u_seq n + β ^ (n + 1) * B (x (n + 1)) := by
      rw [hpow]; ring
    linarith

/-- Cota superior analítica en el borde derecho: Ψ♯(0.28) < -27.83. -/
lemma psi_sharp_h_lt : Psi_sharp h < -2783 / 100 := by
  unfold Psi_sharp h
  have hsq : Real.sqrt (28 / 100) < 53 / 100 := by
    have : (Real.sqrt (28 / 100)) ^ 2 = 28 / 100 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (28 / 100)]
  have hpos : 0 < Real.sqrt (28 / 100) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (500 / 53 : ℝ) < 5 / Real.sqrt (28 / 100) := by
    rw [div_lt_div_iff₀ (by norm_num) hpos]
    linarith
  linarith

/-- Monotonicidad de Ψ♯(x) - B₁(β, x) en [b, h] sin derivadas. -/
lemma psi_sharp_sub_B1_le_h (β : ℝ) {x : ℝ} (hx : b ≤ x ∧ x ≤ h) :
    Psi_sharp x - B1 β x ≤ Psi_sharp h - B1 β h := by
  have hx0 : 0 < x := by unfold b at hx; linarith
  have hh0 : 0 < h := by unfold h; norm_num
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hle_s : Real.sqrt x ≤ Real.sqrt h := Real.sqrt_le_sqrt hx.2
  have hsh_lt : Real.sqrt h < 53 / 100 := by
    have : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt (le_of_lt hh0)
    unfold h at *; nlinarith
  -- Racionalización: (1/√x - 1/√h) * (√x √h (√h + √x)) = h - x
  set D := Real.sqrt x * Real.sqrt h * (Real.sqrt h + Real.sqrt x)
  have hD_pos : 0 < D := by positivity
  have hrat : (1 / Real.sqrt x - 1 / Real.sqrt h) * D = h - x := by
    dsimp [D]
    have hsx_ne : Real.sqrt x ≠ 0 := ne_of_gt hsx
    have hsh_ne : Real.sqrt h ≠ 0 := ne_of_gt hsh
    field_simp [hsx_ne, hsh_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hx0), Real.sq_sqrt (le_of_lt hh0)]
  have hD_lt : D < 3 / 10 := by
    have h1 : Real.sqrt x * Real.sqrt h ≤ h := by
      have : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt (le_of_lt hh0)
      nlinarith
    have h2 : Real.sqrt h + Real.sqrt x ≤ 2 * Real.sqrt h := by linarith
    have h3 : D ≤ h * (2 * Real.sqrt h) := mul_le_mul h1 h2 (by linarith) (le_of_lt hh0)
    unfold h at *; nlinarith
  have hinv_lb : (50 / 3 : ℝ) * (h - x) ≤ 5 * (1 / Real.sqrt x - 1 / Real.sqrt h) := by
    have hhx : 0 ≤ h - x := by linarith [hx.2]
    have h1 : (h - x) / (3 / 10) ≤ (h - x) / D :=
      div_le_div_of_nonneg_left hhx hD_pos (le_of_lt hD_lt)
    have h2 : 1 / Real.sqrt x - 1 / Real.sqrt h = (h - x) / D :=
      eq_div_of_mul_eq (ne_of_gt hD_pos) hrat
    linarith
  have h5 : 5 / Real.sqrt x - 5 / Real.sqrt h = 5 * (1 / Real.sqrt x - 1 / Real.sqrt h) := by ring
  have hm_lt : m_omega ≤ 2 := by unfold m_omega eta_min q_min C_max_ub; norm_num
  unfold Psi_sharp B1
  nlinarith [hx.2]

/-- Cota maestra del Teorema 1 para cualquier trayectoria de T pasos en M = [0.10, 0.28). -/
theorem theorem1_master_bound (θ : Params) (T : ℕ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ T, b ≤ x t ∧ x t < h)
    (hL : ∀ t < T, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < T, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x T)) :
    (∑ t ∈ range T, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ T * V_cont ≤
    B1_max (x 0) + beta_max ^ T * (-2783 / 100 - B_star_max) := by
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have hβ1 : θ.β ≤ 1 := le_trans θ.hβ.2 (by unfold beta_max; norm_num)
  -- 1. Telescoping con Lema 1
  have htel := telescoping_bellman hβ0 (B1 θ.β)
    (fun t => u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) x T
    (fun t ht => lemma1_one_step_bellman θ
      (hx t (le_of_lt ht)) (hx (t + 1) ht) (hL t ht) (hc t ht))
  -- 2. Acotación de la continuación por Ψ♯(x_T) y monotonicidad hasta h
  have hcont : V_cont - B1 θ.β (x T) ≤ -2783 / 100 - B_star θ.β := by
    have hmono := psi_sharp_sub_B1_le_h θ.β ⟨(hx T le_rfl).1, le_of_lt (hx T le_rfl).2⟩
    have hB1h : B1 θ.β h = B_star θ.β := by unfold B1; ring
    linarith [psi_sharp_h_lt]
  have hβT_nn : 0 ≤ θ.β ^ T := pow_nonneg hβ0 T
  have hstep2 : (∑ t ∈ range T, θ.β ^ t *
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) + θ.β ^ T * V_cont ≤
      (1 - θ.β ^ T) * B_star θ.β - m_omega * (h - x 0) + θ.β ^ T * (-2783 / 100) := by
    have hmul := mul_le_mul_of_nonneg_left hcont hβT_nn
    have hdist1 : θ.β ^ T * (V_cont - B1 θ.β (x T)) =
        θ.β ^ T * V_cont - θ.β ^ T * B1 θ.β (x T) := by ring
    have hdist2 : (1 - θ.β ^ T) * B_star θ.β = B_star θ.β - θ.β ^ T * B_star θ.β := by ring
    have hdist3 : θ.β ^ T * (-2783 / 100 - B_star θ.β) =
        θ.β ^ T * (-2783 / 100) - θ.β ^ T * B_star θ.β := by ring
    unfold B1 at htel hmul hdist1
    linarith
  -- 3. Monotonicidad en β: B_*(β) ≤ B_*^max y θ.β^T ≤ beta_max^T
  have h1mβT : 0 ≤ 1 - θ.β ^ T := sub_nonneg.mpr (pow_le_one₀ hβ0 hβ1)
  have hB_le : (1 - θ.β ^ T) * B_star θ.β ≤ (1 - θ.β ^ T) * B_star_max :=
    mul_le_mul_of_nonneg_left (B_star_le_max θ) h1mβT
  have hgap_pos : 0 ≤ -2783 / 100 - B_star_max := by
    unfold B_star_max B_star R_hat Delta2 beta_min; norm_num
  have hpow_le : θ.β ^ T ≤ beta_max ^ T := pow_le_pow_left₀ hβ0 θ.hβ.2 T
  have hgap_mul : θ.β ^ T * (-2783 / 100 - B_star_max) ≤
      beta_max ^ T * (-2783 / 100 - B_star_max) :=
    mul_le_mul_of_nonneg_right hpow_le hgap_pos
  unfold B1_max
  linarith

/-- Teorema 1 (Cota uniforme independiente de K₀): ningún óptimo permanece 24 períodos en M. -/
theorem theorem1_uniform_24 (θ : Params) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 24, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 24, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 24, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x 24)) :
    (∑ t ∈ range 24, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 24 * V_cont < -3558 / 100 := by
  have hmaster := theorem1_master_bound θ 24 x L V_cont hx hL hc hV
  have hB1_le : B1_max (x 0) ≤ B_star_max := by
    unfold B1_max m_omega eta_min q_min C_max_ub
    have := (hx 0 (by norm_num)).2
    nlinarith
  have hnum : B_star_max + beta_max ^ 24 * (-2783 / 100 - B_star_max) < -3558 / 100 := by
    unfold B_star_max B_star R_hat Delta2 beta_min beta_max
    norm_num
  linarith

/-- Teorema 1 (Cota estado a estado: τ_H ≤ 23 con holgura > +0.205):
    para cualquier testigo W_M con W_M(0.10) ≥ -35.58 y margen creciente (Lema 1),
    toda trayectoria que permanezca 23 períodos en M es estrictamente subóptima. -/
theorem theorem1_state_by_state_23 (θ : Params) (x L : ℕ → ℝ) (V_cont : ℝ) (WM : ℝ → ℝ)
    (hx : ∀ t ≤ 23, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 23, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 23, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x 23))
    (hWM_b : -3558 / 100 ≤ WM b)
    (hWM_mono : WM b - B1_max b ≤ WM (x 0) - B1_max (x 0)) :
    (∑ t ∈ range 23, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 23 * V_cont + (205 / 1000 : ℝ) < WM (x 0) := by
  have hmaster := theorem1_master_bound θ 23 x L V_cont hx hL hc hV
  have hnum : beta_max ^ 23 * (-2783 / 100 - B_star_max) + (205 / 1000 : ℝ) <
      (-3558 / 100 : ℝ) - B1_max b := by
    unfold B1_max B_star_max B_star R_hat Delta2 m_omega eta_min q_min
      C_max_ub beta_min beta_max h b
    norm_num
  linarith

/-! ## 5. Certificación de W_M(0.10) ≥ -35.58 vía MVS.Lemma11 y cierre total del Teorema 1 -/

/-- Consumo del testigo en M: c_M(K) = q_- K + F_{A_-}(K, 0.68) - 0.135. -/
def c_M (K : ℝ) : ℝ :=
  q_min * K + F A_min K (68 / 100) - (135 / 1000)

/-- Testigo explícito en M: W_M(θ, K) = u(θ.η, c_M(K), 0.68) + θ.β * (-33.103). -/
def W_M (θ : Params) (K : ℝ) : ℝ :=
  u θ.η (c_M K) (68 / 100) + θ.β * (-33103 / 1000)

/-- Certificación completa en el kernel de Lean de W_M(0.10) ≥ -35.58 para todo θ ∈ P,
    usando exclusivamente `MVS.Lemma11` y aritmética racional exacta. -/
theorem W_M_b_ge (θ : Params) : (-3558 / 100 : ℝ) ≤ W_M θ b := by
  set sg_lo : ℝ := 417563 / 1000000
  set cM_lo : ℝ := q_min * b + A_min * (34 / 195) * sg_lo - (135 / 1000)
  set rU_cM : ℝ := 1321769 / 1000000
  set rU_32 : ℝ := 66479 / 50000
  set L1 : ℝ := -((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_cM - 1) / (rU_cM + 1)) +
    MVS.Lemma11.atanhRemUB 3 ((rU_cM - 1) / (rU_cM + 1))))
  set L2 : ℝ := -((2 ^ 2 : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_32 - 1) / (rU_32 + 1)) +
    MVS.Lemma11.atanhRemUB 3 ((rU_32 - 1) / (rU_32 + 1))))
  -- 1. Cota inferior racional de √(34/195) y c_M(0.10)
  have hsg_le : sg_lo ≤ Real.sqrt (34 / 195) := by
    have hsq : sg_lo ^ 2 ≤ (Real.sqrt (34 / 195)) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      norm_num [sg_lo]
    have hnn : 0 ≤ Real.sqrt (34 / 195) := Real.sqrt_nonneg _
    have hsg_nn : 0 ≤ sg_lo := by norm_num [sg_lo]
    nlinarith
  have hcM_ge : cM_lo ≤ c_M b := by
    dsimp [cM_lo]
    unfold c_M F
    have hrat : 2 * b * (68 / 100 : ℝ) / (b + 68 / 100) = 34 / 195 := by unfold b; norm_num
    rw [hrat]
    have hcoef_nn : 0 ≤ A_min * (34 / 195 : ℝ) := by unfold A_min; norm_num
    have hmul := mul_le_mul_of_nonneg_left hsg_le hcoef_nn
    linarith
  have hcM_lo_pos : 0 < cM_lo := by norm_num [cM_lo, q_min, b, A_min, sg_lo]
  have hcM_lo_le1 : cM_lo ≤ 1 := by norm_num [cM_lo, q_min, b, A_min, sg_lo]
  -- 2. Cota inferior certificada de log(c_M(0.10)) vía MVS.Lemma11 (s = 4, N = 3)
  have hlog_cM : L1 ≤ Real.log (c_M b) := by
    have hmL : (1 : ℝ) ^ (2 ^ 4) ≤ 1 / cM_lo := by
      rw [one_pow, one_le_div hcM_lo_pos]; exact hcM_lo_le1
    have hmU : 1 / cM_lo ≤ rU_cM ^ (2 ^ 4) := by
      norm_num [cM_lo, q_min, b, A_min, sg_lo, rU_cM]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 4 (m := 1 / cM_lo)
      (rL := 1) (rU := rU_cM) le_rfl (by norm_num [rU_cM]) hmL hmU).2
    rw [Real.log_div (by norm_num) (ne_of_gt hcM_lo_pos), Real.log_one, zero_sub] at hb
    have hmono := Real.log_le_log hcM_lo_pos hcM_ge
    dsimp [L1]
    linarith
  -- 3. Cota inferior certificada de log(1 - 0.68) = log(0.32) vía MVS.Lemma11 (s = 2, N = 3)
  have hlog_32 : L2 ≤ Real.log (1 - 68 / 100 : ℝ) := by
    have h32_pos : (0 : ℝ) < 1 - 68 / 100 := by norm_num
    have hmL : (1 : ℝ) ^ (2 ^ 2) ≤ 1 / (1 - 68 / 100 : ℝ) := by norm_num
    have hmU : 1 / (1 - 68 / 100 : ℝ) ≤ rU_32 ^ (2 ^ 2) := by norm_num [rU_32]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 2 (m := 1 / (1 - 68 / 100 : ℝ))
      (rL := 1) (rU := rU_32) le_rfl (by norm_num [rU_32]) hmL hmU).2
    rw [Real.log_div (by norm_num) (ne_of_gt h32_pos), Real.log_one, zero_sub] at hb
    dsimp [L2]
    linarith
  -- 4. Monotonicidad en η ∈ [η₋, η₊] y β ≤ β₊ + verificación numérica exacta
  have hL1_le_L2 : L1 ≤ L2 := by
    dsimp [L1, L2]
    unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
    norm_num [Finset.sum_range_succ, rU_cM, rU_32]
  have hnum : (-3558 / 100 : ℝ) ≤ eta_max * L1 + (1 - eta_max) * L2 + beta_max * (-33103 / 1000) := by
    dsimp [L1, L2]
    unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max beta_max
    norm_num [Finset.sum_range_succ, rU_cM, rU_32]
  have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by
    have := θ.hη.2; unfold eta_max at this; linarith
  have h1 := mul_le_mul_of_nonneg_left hlog_cM hη_nn
  have h2 := mul_le_mul_of_nonneg_left hlog_32 h1mη_nn
  have h3 : eta_max * (L1 - L2) ≤ θ.η * (L1 - L2) :=
    mul_le_mul_of_nonpos_right θ.hη.2 (by linarith [hL1_le_L2])
  have h4 : beta_max * (-33103 / 1000 : ℝ) ≤ θ.β * (-33103 / 1000 : ℝ) := by
    nlinarith [θ.hβ.2]
  unfold W_M u
  linarith

/-- Teorema 1 completamente autocontenido (cero hipótesis externas):
    para todo θ ∈ P, toda trayectoria que permanezca 23 períodos en M = [0.10, 0.28)
    es estrictamente subóptima respecto al testigo explícito W_M(θ, K₀) con holgura > +0.205. -/
theorem theorem1_state_by_state_23_closed (θ : Params) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 23, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 23, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 23, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x 23)) :
    (∑ t ∈ range 23, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 23 * V_cont + (205 / 1000 : ℝ) < W_M θ (x 0) := by
  have hWM_b : (-3558 / 100 : ℝ) ≤ W_M θ b := W_M_b_ge θ
  have hWM_mono : W_M θ b - B1_max b ≤ W_M θ (x 0) - B1_max (x 0) := by
    have h := lemma1_witness_margin (K := x 0) (η_act := θ.η)
      (C_tail := (1 - θ.η) * Real.log (1 - 68 / 100) + θ.β * (-33103 / 1000))
      (hx 0 (by norm_num)) θ.hη.1
    dsimp only at h
    have heq : ∀ y, W_M θ y = θ.η * Real.log (q_min * y + F A_min y (68 / 100) - 135 / 1000) +
        ((1 - θ.η) * Real.log (1 - 68 / 100) + θ.β * (-33103 / 1000)) := by
      intro y; unfold W_M c_M u; ring
    rw [heq b, heq (x 0)]
    exact h
  exact theorem1_state_by_state_23 θ x L V_cont (W_M θ) hx hL hc hV hWM_b hWM_mono

end

end MVS.Theorem1
