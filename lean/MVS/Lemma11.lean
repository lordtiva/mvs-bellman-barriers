import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# Lemma 11 (MR): Certified bounds for `Real.log`

Formalization of the truncated `2 * atanh(u)` series with explicit geometric remainder
and rational power-enclosure reduction `rL ^ (2 ^ s) ≤ m ≤ rU ^ (2 ^ s)`.
-/

open Finset Real

namespace MVS.Lemma11

/-- Suma parcial truncada de 2 * atanh(u) con N términos (j = 0, ..., N-1). -/
noncomputable def atanhSeries (N : ℕ) (u : ℝ) : ℝ :=
  2 * ∑ j ∈ range N, u ^ (2 * j + 1) / (2 * j + 1 : ℝ)

/-- Cota geométrica explícita superior del residuo para 0 ≤ u < 1. -/
noncomputable def atanhRemUB (N : ℕ) (u : ℝ) : ℝ :=
  2 * u ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - u ^ 2))

/-- Identidad finita geométrica: (1 - t^2) * ∑_{j<N} t^(2j) = 1 - t^(2N). -/
lemma geom_even_sum (N : ℕ) (t : ℝ) :
    (1 - t ^ 2) * ∑ j ∈ range N, t ^ (2 * j) = 1 - t ^ (2 * N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

/-- Derivada de la serie truncada de 2 * atanh(t). -/
lemma hasDerivAt_atanhSeries (N : ℕ) (t : ℝ) :
    HasDerivAt (atanhSeries N) (2 * ∑ j ∈ range N, t ^ (2 * j)) t := by
  unfold atanhSeries
  have hsum : HasDerivAt (fun x => ∑ j ∈ range N, x ^ (2 * j + 1) / (2 * j + 1 : ℝ))
      (∑ j ∈ range N, t ^ (2 * j)) t := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have hpow := (hasDerivAt_pow (2 * j + 1) t).div_const (2 * j + 1 : ℝ)
    convert hpow using 1
    have hne : (2 * j + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hne]
  simpa using hsum.const_mul 2

/-- Derivada de log(1+t) - log(1-t) en t ∈ (-1, 1). -/
lemma hasDerivAt_log_ratio {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt (fun x => Real.log (1 + x) - Real.log (1 - x)) (2 / (1 - t ^ 2)) t := by
  have h1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_id t).const_add (1 : ℝ)).log (by dsimp; linarith)
    simpa using this
  have h2 : HasDerivAt (fun x => Real.log (1 - x)) ((-1) / (1 - t)) t := by
    have := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log (by dsimp; linarith)
    simpa using this
  convert h1.sub h2 using 1
  have h1ne : 1 + t ≠ 0 := by linarith
  have h2ne : 1 - t ≠ 0 := by linarith
  have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith
  field_simp [h1ne, h2ne, hsq]
  ring

/-- Teorema central del Lema 11 (en variable u = (m-1)/(m+1) ∈ [0, 1)):
    atanhSeries N u ≤ log((1+u)/(1-u)) ≤ atanhSeries N u + atanhRemUB N u. -/
theorem atanh_log_bounds (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    atanhSeries N u ≤ Real.log ((1 + u) / (1 - u)) ∧
    Real.log ((1 + u) / (1 - u)) ≤ atanhSeries N u + atanhRemUB N u := by
  have hlog_eq : Real.log ((1 + u) / (1 - u)) = Real.log (1 + u) - Real.log (1 - u) :=
    Real.log_div (by linarith) (by linarith)
  rw [hlog_eq]
  -- Residuo f(t) = log(1+t) - log(1-t) - atanhSeries N t
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - atanhSeries N t
  have hf_deriv : ∀ t ∈ Set.Icc 0 u,
      HasDerivAt f (2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
    intro t ht
    have ht1 : -1 < t := by linarith [ht.1]
    have ht2 : t < 1 := by linarith [ht.2]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht2]
    convert (hasDerivAt_log_ratio ht1 ht2).sub (hasDerivAt_atanhSeries N t) using 1
    have hg := geom_even_sum N t
    field_simp [hsq]
    linarith [hg]
  have hf0 : f 0 = 0 := by
    simp [f, atanhSeries]
  -- 1. Cota inferior: f'(t) ≥ 0 en [0, u] => f(u) ≥ f(0) = 0
  have hlow : 0 ≤ f u := by
    have hmono : MonotoneOn f (Set.Icc 0 u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) ?_ ?_ ?_
      · exact DifferentiableOn.continuousOn
          (fun t ht => (hf_deriv t ht).differentiableAt.differentiableWithinAt)
      · exact fun t ht => (hf_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hf_deriv t ht').deriv]
        have ht0 : 0 ≤ t := ht'.1
        have hden : 0 < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2, hu1]
        positivity
    simpa [hf0] using hmono ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
  -- 2. Cota superior: g(t) = 2 t^(2N+1) / ((2N+1)(1-u^2)) - f(t) tiene g'(t) ≥ 0 en [0, u]
  let g : ℝ → ℝ := fun t =>
    2 * t ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - u ^ 2)) - f t
  have hden_u : 0 < 1 - u ^ 2 := by nlinarith
  have hg_deriv : ∀ t ∈ Set.Icc 0 u,
      HasDerivAt g (2 * t ^ (2 * N) / (1 - u ^ 2) - 2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
    intro t ht
    have hterm : HasDerivAt (fun x => 2 * x ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - u ^ 2)))
        (2 * t ^ (2 * N) / (1 - u ^ 2)) t := by
      have h1 := ((hasDerivAt_pow (2 * N + 1) t).const_mul 2).div_const
        ((2 * N + 1 : ℝ) * (1 - u ^ 2))
      convert h1 using 1
      have hNne : (2 * N + 1 : ℝ) ≠ 0 := by positivity
      have hune : 1 - u ^ 2 ≠ 0 := ne_of_gt hden_u
      push_cast
      field_simp [hNne, hune]
    exact hterm.sub (hf_deriv t ht)
  have hg0 : g 0 = 0 := by
    simp [g, hf0]
  have hup : f u ≤ atanhRemUB N u := by
    have hmono : MonotoneOn g (Set.Icc 0 u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) ?_ ?_ ?_
      · exact DifferentiableOn.continuousOn
          (fun t ht => (hg_deriv t ht).differentiableAt.differentiableWithinAt)
      · exact fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hg_deriv t ht').deriv]
        have ht0 : 0 ≤ t := ht'.1
        have hden_t : 0 < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2, hu1]
        have hle : 1 - u ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
        have hnum : 0 ≤ 2 * t ^ (2 * N) := by positivity
        have hdiv := div_le_div_of_nonneg_left hnum hden_u hle
        linarith
    have hgu : 0 ≤ g u := by simpa [hg0] using hmono ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
    dsimp [g] at hgu
    unfold atanhRemUB
    linarith
  dsimp [f] at hlow hup
  exact ⟨by linarith, by linarith⟩

/-- Envoltura rigurosa para cualquier m ≥ 1 usando u = (m - 1) / (m + 1). -/
theorem log_bounds_of_ge_one (N : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    atanhSeries N ((m - 1) / (m + 1)) ≤ Real.log m ∧
    Real.log m ≤ atanhSeries N ((m - 1) / (m + 1)) + atanhRemUB N ((m - 1) / (m + 1)) := by
  have hu0 : 0 ≤ (m - 1) / (m + 1) := div_nonneg (by linarith) (by linarith)
  have hu1 : (m - 1) / (m + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hratio : (1 + (m - 1) / (m + 1)) / (1 - (m - 1) / (m + 1)) = m := by
    have hm1 : m + 1 ≠ 0 := by linarith
    field_simp [hm1]
    ring
  simpa [hratio] using atanh_log_bounds N hu0 hu1

/-- Reducción por s raíces cuadradas acotadas racionalmente (rL^(2^s) ≤ m ≤ rU^(2^s)). -/
theorem log_bounds_of_pow_enclosure (N s : ℕ) {m rL rU : ℝ}
    (hrL : 1 ≤ rL) (hrU : 1 ≤ rU)
    (hmL : rL ^ (2 ^ s) ≤ m) (hmU : m ≤ rU ^ (2 ^ s)) :
    (2 ^ s : ℝ) * atanhSeries N ((rL - 1) / (rL + 1)) ≤ Real.log m ∧
    Real.log m ≤ (2 ^ s : ℝ) * (atanhSeries N ((rU - 1) / (rU + 1)) +
      atanhRemUB N ((rU - 1) / (rU + 1))) := by
  have hposL : 0 < rL ^ (2 ^ s) := by positivity
  have hposm : 0 < m := lt_of_lt_of_le hposL hmL
  have h1 : Real.log (rL ^ (2 ^ s)) ≤ Real.log m := Real.log_le_log hposL hmL
  have h2 : Real.log m ≤ Real.log (rU ^ (2 ^ s)) := Real.log_le_log hposm hmU
  rw [Real.log_pow] at h1 h2
  have hbL := (log_bounds_of_ge_one N hrL).1
  have hbU := (log_bounds_of_ge_one N hrU).2
  have h2s : (0 : ℝ) ≤ (2 ^ s : ℕ) := by positivity
  constructor
  · calc (2 ^ s : ℝ) * atanhSeries N ((rL - 1) / (rL + 1))
        = ((2 ^ s : ℕ) : ℝ) * atanhSeries N ((rL - 1) / (rL + 1)) := by norm_cast
      _ ≤ ((2 ^ s : ℕ) : ℝ) * Real.log rL := mul_le_mul_of_nonneg_left hbL h2s
      _ ≤ Real.log m := h1
  · calc Real.log m
        ≤ ((2 ^ s : ℕ) : ℝ) * Real.log rU := h2
      _ ≤ ((2 ^ s : ℕ) : ℝ) * (atanhSeries N ((rU - 1) / (rU + 1)) +
            atanhRemUB N ((rU - 1) / (rU + 1))) := mul_le_mul_of_nonneg_left hbU h2s
      _ = (2 ^ s : ℝ) * (atanhSeries N ((rU - 1) / (rU + 1)) +
            atanhRemUB N ((rU - 1) / (rU + 1))) := by norm_cast

/-- Reducción completa x = 2^k * m (k ∈ ℤ, m > 0) para todo x > 0. -/
theorem log_mul_zpow_two (k : ℤ) {m : ℝ} (hm : 0 < m) :
    Real.log ((2 : ℝ) ^ k * m) = (k : ℝ) * Real.log 2 + Real.log m := by
  rw [Real.log_mul (by positivity) (ne_of_gt hm), Real.log_zpow]

/-- Test inmediato sobre log 2: 0.6931 < log 2 < 0.6932 (s = 3, N = 4). -/
theorem log_two_bounds : (0.6931 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6932 := by
  have hb := log_bounds_of_pow_enclosure 4 3 (m := (2 : ℝ))
    (rL := (1090507 / 1000000 : ℝ)) (rU := (1090508 / 1000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold atanhSeries atanhRemUB at hb
  norm_num [Finset.sum_range_succ] at hb
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

end MVS.Lemma11
