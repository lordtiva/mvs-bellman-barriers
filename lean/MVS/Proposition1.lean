import MVS.Theorem1
import MVS.Lemma11
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Proposición 1 (MR): Banda de anclaje $M_0 = [0.05, 0.10)$ y cota $\tau_{0.1} \le 10$

Formalización completa y 100% autocontenida (cero `sorry`, cero hipótesis externas)
de la Proposición 1 sobre $M_0 = [0.05, 0.10)$:
1. Barrera afín de un paso $B_0(\beta, K)$ con $\hat{R}_0 = -1.827$ (certificado vía
   tangente polinomial exacta + `MVS.Lemma11`) y $\Delta_0 = 0.3115$.
2. Monotonicidad de $\Psi^\#(x) - B_0(\beta, x)$ en $[0.05, 0.10]$ sin derivadas.
3. Certificación vía `MVS.Lemma11` y `W_M_b_ge` de ambos testigos de 3 pasos:
   - Testigo original $W_{M_0}^{\text{orig}}(\theta, K_0) > -43.845$,
   - Testigo afinado $W_{M_0}^{\text{sharp}}(\theta, K_0) > -43.541$.
4. Cierre de $\tau_{0.1} \le 10$ (`prop1_uniform_10`) para todo $\theta \in \mathcal{P}$
   y todo $K_0 \in [0.05, 0.10)$.
-/

open Finset Real MVS.Theorem1

namespace MVS.Proposition1

noncomputable section

/-! ## 1. Constantes analíticas exactas de la banda $M_0 = [0.05, 0.10)$ -/

/-- Extremos de la banda de anclaje $M_0 = [b_0, h_0) = [0.05, 0.10)$. -/
def b0 : ℝ := 5 / 100
def h0 : ℝ := 10 / 100

/-- Constantes racionales exactas de la Proposición 1. -/
def C_max0_ub : ℝ := 5011659 / 50000000
def R_hat0 : ℝ := -1827 / 1000
def Delta0 : ℝ := 3115 / 10000
def m_omega0 : ℝ := eta_min * q_min / C_max0_ub

/-- Barrera afín de un paso en $M_0$: $B_0(\beta, K) = B_{0,*}(\beta) - m_{\omega,0}(h_0 - K)$. -/
def B0_star (β : ℝ) : ℝ := (R_hat0 - Delta0) / (1 - β)
def B0_star_max : ℝ := B0_star beta_min
def B0 (β K : ℝ) : ℝ := B0_star β - m_omega0 * (h0 - K)
def B0_max (K : ℝ) : ℝ := B0_star_max - m_omega0 * (h0 - K)

/-! ## 2. Certificación de $C_{\max,0}^{\text{ub}}$, $\Delta_0$ y $\hat{R}_0 = -1.827$ -/

/-- Certificación por elevación al cuadrado: $q_+ h_0 + F_{A_+}(h_0, 1) - b_0 \le C_{\max,0}^{\text{ub}}$. -/
lemma C_max0_ub_valid : q_max * h0 + F A_max h0 1 - b0 ≤ C_max0_ub := by
  unfold F q_max A_max h0 b0 C_max0_ub
  have hrat : (2 * (10 / 100 : ℝ) * 1 / (10 / 100 + 1)) = 2 / 11 := by norm_num
  rw [hrat]
  have hsq_le : ((751 / 1000 : ℝ) * (2 / 11) * Real.sqrt (2 / 11)) ^ 2 ≤
      (2911159 / 50000000 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hnn : 0 ≤ (751 / 1000 : ℝ) * (2 / 11) * Real.sqrt (2 / 11) := by positivity
  have hbound : (751 / 1000 : ℝ) * (2 / 11) * Real.sqrt (2 / 11) ≤ 2911159 / 50000000 := by
    nlinarith
  linarith

/-- Holgura exacta $\Delta_0^{\text{exact}} > \Delta_0 = 0.3115$. -/
lemma Delta0_le_exact : Delta0 ≤ eta_min * beta_min * q_min * (h0 - b0) / C_max0_ub := by
  unfold Delta0 eta_min beta_min q_min h0 b0 C_max0_ub
  norm_num

/-- Certificación completa de $\hat{R}_0 = -1.827$ para todo $\theta \in \mathcal{P}$ y $L \in [0, 1)$
    usando tangente polinomial exacta en $s = 21703 / 25000$ y `MVS.Lemma11`. -/
lemma R_hat0_valid (θ : Params) {L : ℝ} (hL : 0 ≤ L ∧ L < 1) :
    u θ.η (q_max * h0 + F A_max h0 L - b0) L ≤ R_hat0 := by
  set s : ℝ := 21703 / 25000
  set L0 : ℝ := h0 * s ^ 2 / (1 - s ^ 2)
  set f0 : ℝ := s ^ 3
  set alpha : ℝ := (3 / 2 : ℝ) * s * (1 - s ^ 2) ^ 2 / h0
  set rt2h0_ub : ℝ := 447214 / 1000000
  set coef : ℝ := 2 * h0 * rt2h0_ub
  set c0 : ℝ := q_max * h0 - b0 + A_max * coef * f0
  set m0 : ℝ := A_max * coef * alpha
  set c1 : ℝ := q_max * h0 + F A_max h0 L - b0
  -- 1. Cota superior para √(2 h0)
  have hh0_pos : 0 < h0 := by unfold h0; norm_num
  have hrt2h0 : Real.sqrt (2 * h0) ≤ rt2h0_ub := by
    have hsq : (Real.sqrt (2 * h0)) ^ 2 ≤ rt2h0_ub ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      norm_num [h0, rt2h0_ub]
    have hnn : 0 ≤ Real.sqrt (2 * h0) := Real.sqrt_nonneg _
    have hrt_nn : 0 ≤ rt2h0_ub := by norm_num [rt2h0_ub]
    nlinarith
  -- 2. Cota tangente algebraica para (L/(h0+L))^(3/2) ≤ f0 + alpha * (L - L0)
  have hL_frac : L / (h0 + L) * Real.sqrt (L / (h0 + L)) ≤ f0 + alpha * (L - L0) := by
    set y : ℝ := L / (h0 + L)
    set rhs : ℝ := f0 + alpha * (L - L0)
    have hy_nn : 0 ≤ y := div_nonneg hL.1 (by linarith)
    have hrhs_pos : 0 < rhs := by
      have h0p : 0 < f0 - alpha * L0 := by norm_num [h0, s, L0, f0, alpha]
      have ha : 0 < alpha := by norm_num [h0, s, alpha]
      dsimp [rhs]; nlinarith [hL.1]
    have hpoly : (h0 + L) ^ 3 * rhs ^ 2 - L ^ 3 = (L - L0) ^ 2 * (
        (2383070845470174563632570502530221683880441 /
          3814697265625000000000000000000000000000000 : ℝ) * L ^ 3 +
        (46601101002576532286706220810213872551641323 /
          38146972656250000000000000000000000000000000 : ℝ) * L ^ 2 +
        (27999587358160654177860576987837080051641323 /
          381469726562500000000000000000000000000000000 : ℝ) * L +
        (6935635361604766181349426680153429183880441 /
          3814697265625000000000000000000000000000000000 : ℝ)) := by
      dsimp [rhs, alpha, f0, L0, s]; unfold h0; ring
    have hL0 : 0 ≤ L := hL.1
    have hpoly_nn : 0 ≤ (h0 + L) ^ 3 * rhs ^ 2 - L ^ 3 := by
      rw [hpoly]; positivity
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
    have hF_eq : F A_max h0 L =
        A_max * ((2 * h0 * Real.sqrt (2 * h0)) * (L / (h0 + L) * Real.sqrt (L / (h0 + L)))) := by
      unfold F; dsimp only
      have hrew : 2 * h0 * L / (h0 + L) = (2 * h0) * (L / (h0 + L)) := by ring
      rw [hrew, Real.sqrt_mul (by positivity : 0 ≤ 2 * h0)]; ring
    have hprod_le : (2 * h0 * Real.sqrt (2 * h0)) * (L / (h0 + L) * Real.sqrt (L / (h0 + L))) ≤
        coef * (f0 + alpha * (L - L0)) := by
      have h1 : 2 * h0 * Real.sqrt (2 * h0) ≤ coef := by dsimp [coef]; nlinarith
      have h2 : 0 ≤ L / (h0 + L) * Real.sqrt (L / (h0 + L)) :=
        mul_nonneg (div_nonneg hL.1 (by linarith)) (Real.sqrt_nonneg _)
      exact mul_le_mul h1 hL_frac h2 (by norm_num [h0, coef, rt2h0_ub])
    have hA_nn : 0 ≤ A_max := by unfold A_max; norm_num
    have hmulA := mul_le_mul_of_nonneg_left hprod_le hA_nn
    dsimp [c1, c0, m0]; rw [hF_eq]; linarith
  -- 4. Concavidad de log en c1 y en (1 - L)
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    have hF_nn : 0 ≤ F A_max h0 L := by
      unfold F A_max
      have hL0 : 0 ≤ L := hL.1
      have : 0 ≤ 2 * h0 * L / (h0 + L) := div_nonneg (by positivity) (by linarith)
      exact mul_nonneg (mul_nonneg (by norm_num) this) (Real.sqrt_nonneg _)
    have hqb : 0 < q_max * h0 - b0 := by unfold q_max h0 b0; norm_num
    linarith
  have hc0_pos : 0 < c0 := by norm_num [q_max, h0, b0, A_max, s, f0, coef, rt2h0_ub, c0]
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
  have h1mL0_pos : 0 < 1 - L0 := by norm_num [h0, s, L0]
  have hlog_1mL : Real.log (1 - L) ≤ Real.log (1 - L0) - (L - L0) / (1 - L0) := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos h1mL_pos h1mL0_pos)
    rw [Real.log_div (ne_of_gt h1mL_pos) (ne_of_gt h1mL0_pos)] at hconc
    have hrew : (1 - L) / (1 - L0) - 1 = -((L - L0) / (1 - L0)) := by
      have hne : 1 - L0 ≠ 0 := ne_of_gt h1mL0_pos
      field_simp [hne]; ring
    linarith
  -- 5. Evaluación certificada de log(c0) y log(1 - L0) vía MVS.Lemma11
  set rL_c0 : ℝ := 233151 / 200000
  set rL_1mL0 : ℝ := 1095579 / 1000000
  set log_c0_ub : ℝ := -((2 ^ 4 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_c0 - 1) / (rL_c0 + 1)))
  set log_1mL0_ub : ℝ := -((2 ^ 2 : ℝ) * MVS.Lemma11.atanhSeries 3 ((rL_1mL0 - 1) / (rL_1mL0 + 1)))
  have hlog_c0_ub : Real.log c0 ≤ log_c0_ub := by
    have hinv_le : rL_c0 ^ (2 ^ 4) ≤ 1 / c0 := by
      norm_num [q_max, h0, b0, A_max, s, f0, coef, rt2h0_ub, c0, rL_c0]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 4 (m := 1 / c0) (rL := rL_c0)
      (rU := (2 : ℝ)) (by norm_num [rL_c0]) (by norm_num)
      hinv_le (by norm_num [q_max, h0, b0, A_max, s, f0, coef, rt2h0_ub, c0])).1
    rw [Real.log_div (by norm_num) (ne_of_gt hc0_pos), Real.log_one, zero_sub] at hb
    dsimp [log_c0_ub]; linarith
  have hlog_1mL0_ub : Real.log (1 - L0) ≤ log_1mL0_ub := by
    have hinv_le : rL_1mL0 ^ (2 ^ 2) ≤ 1 / (1 - L0) := by
      norm_num [h0, s, L0, rL_1mL0]
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 2 (m := 1 / (1 - L0)) (rL := rL_1mL0)
      (rU := (2 : ℝ)) (by norm_num [rL_1mL0]) (by norm_num)
      hinv_le (by norm_num [h0, s, L0])).1
    rw [Real.log_div (by norm_num) (ne_of_gt h1mL0_pos), Real.log_one, zero_sub] at hb
    dsimp [log_1mL0_ub]; linarith
  -- 6. Afinidad en (η, L) sobre el rectángulo [η₋, η₊] × [0, 1]
  set A_L : ℝ := log_c0_ub + m0 * (L - L0) / c0
  set B_L : ℝ := log_1mL0_ub - (L - L0) / (1 - L0)
  have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by
    have := θ.hη.2; unfold eta_max at this; linarith
  have hu_le : u θ.η c1 L ≤ θ.η * A_L + (1 - θ.η) * B_L := by
    unfold u
    have h1 := mul_le_mul_of_nonneg_left (show Real.log c1 ≤ A_L by dsimp [A_L]; linarith) hη_nn
    have h2 := mul_le_mul_of_nonneg_left (show Real.log (1 - L) ≤ B_L by dsimp [B_L]; linarith) h1mη_nn
    linarith
  set val : ℝ → ℝ → ℝ := fun η x =>
    η * (log_c0_ub + m0 * (x - L0) / c0) + (1 - η) * (log_1mL0_ub - (x - L0) / (1 - L0))
  have hval_eta : ∀ η, val η L = (1 - L) * val η 0 + L * val η 1 := by
    intro η; dsimp [val]; ring
  have hv_min_0 : val eta_min 0 ≤ R_hat0 := by
    dsimp [val, log_c0_ub, log_1mL0_ub]; unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_min, q_max, h0, b0, A_max, R_hat0,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h0_ub, alpha, f0, L0, s]
  have hv_min_1 : val eta_min 1 ≤ R_hat0 := by
    dsimp [val, log_c0_ub, log_1mL0_ub]; unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_min, q_max, h0, b0, A_max, R_hat0,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h0_ub, alpha, f0, L0, s]
  have hv_max_0 : val eta_max 0 ≤ R_hat0 := by
    dsimp [val, log_c0_ub, log_1mL0_ub]; unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_max, q_max, h0, b0, A_max, R_hat0,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h0_ub, alpha, f0, L0, s]
  have hv_max_1 : val eta_max 1 ≤ R_hat0 := by
    dsimp [val, log_c0_ub, log_1mL0_ub]; unfold MVS.Lemma11.atanhSeries
    norm_num [Finset.sum_range_succ, eta_max, q_max, h0, b0, A_max, R_hat0,
      rL_c0, rL_1mL0, m0, c0, coef, rt2h0_ub, alpha, f0, L0, s]
  have hval_min_L : val eta_min L ≤ R_hat0 := by rw [hval_eta]; nlinarith [hL.1, hL.2]
  have hval_max_L : val eta_max L ≤ R_hat0 := by rw [hval_eta]; nlinarith [hL.1, hL.2]
  have hlin_eta : θ.η * A_L + (1 - θ.η) * B_L =
      ((eta_max - θ.η) / (eta_max - eta_min)) * val eta_min L +
      ((θ.η - eta_min) / (eta_max - eta_min)) * val eta_max L := by
    have hne : eta_max - eta_min ≠ 0 := by unfold eta_max eta_min; norm_num
    dsimp [val, A_L, B_L]
    field_simp [hne]; ring
  have hw1 : 0 ≤ (eta_max - θ.η) / (eta_max - eta_min) :=
    div_nonneg (by linarith [θ.hη.2]) (by unfold eta_max eta_min; norm_num)
  have hw2 : 0 ≤ (θ.η - eta_min) / (eta_max - eta_min) :=
    div_nonneg (by linarith [θ.hη.1]) (by unfold eta_max eta_min; norm_num)
  have hw_sum : (eta_max - θ.η) / (eta_max - eta_min) +
      (θ.η - eta_min) / (eta_max - eta_min) = 1 := by
    have hne : eta_max - eta_min ≠ 0 := by unfold eta_max eta_min; norm_num
    field_simp [hne]; ring
  have hm1 := mul_le_mul_of_nonneg_left hval_min_L hw1
  have hm2 := mul_le_mul_of_nonneg_left hval_max_L hw2
  have hcomb : ((eta_max - θ.η) / (eta_max - eta_min)) * R_hat0 +
      ((θ.η - eta_min) / (eta_max - eta_min)) * R_hat0 = R_hat0 := by
    calc ((eta_max - θ.η) / (eta_max - eta_min)) * R_hat0 +
          ((θ.η - eta_min) / (eta_max - eta_min)) * R_hat0
        = (((eta_max - θ.η) / (eta_max - eta_min)) +
          ((θ.η - eta_min) / (eta_max - eta_min))) * R_hat0 := by ring
      _ = 1 * R_hat0 := by rw [hw_sum]
      _ = R_hat0 := one_mul R_hat0
  dsimp [c1] at hu_le
  linarith

/-! ## 3. Barrera afín de un paso y cota maestra en $M_0$ -/

/-- Desigualdad de Bellman de un paso para la barrera afín $B_0(\beta, K)$ en $M_0 \times M_0$. -/
theorem prop1_one_step_bellman (θ : Params) {K K' L : ℝ}
    (hK : b0 ≤ K ∧ K < h0) (hK' : b0 ≤ K' ∧ K' < h0) (hL : 0 ≤ L ∧ L < 1)
    (hc0 : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * B0 θ.β K' ≤ B0 θ.β K := by
  have hR_hat : u θ.η (q_max * h0 + F A_max h0 L - b0) L ≤ R_hat0 := R_hat0_valid θ hL
  set c₀ := θ.q * K + F θ.A K L - K'
  set c₁ := q_max * h0 + F A_max h0 L - b0
  have hA_pos : 0 ≤ A_max := by unfold A_max; norm_num
  have hK_pos : 0 < K := by unfold b0 at hK; linarith
  have hh0_pos : 0 < h0 := by unfold h0; norm_num
  have hc1_le : c₁ ≤ C_max0_ub := by
    have hFL : F A_max h0 L ≤ F A_max h0 1 := F_mono_L hA_pos hh0_pos hL.1 (le_of_lt hL.2)
    linarith [C_max0_ub_valid]
  have hF_le : F θ.A K L ≤ F A_max h0 L :=
    le_trans (F_mono_A θ.hA.2 hK_pos hL.1) (F_mono_K hA_pos hK_pos (le_of_lt hK.2) hL.1)
  have hdiff : q_min * (h0 - K) + (K' - b0) ≤ c₁ - c₀ := by
    have hq_step : q_min * (h0 - K) ≤ q_max * h0 - θ.q * K := by
      have : θ.q * (h0 - K) ≤ q_max * h0 - θ.q * K := by nlinarith [θ.hq.2, hh0_pos]
      have : q_min * (h0 - K) ≤ θ.q * (h0 - K) := by nlinarith [θ.hq.1, hK.2]
      linarith
    dsimp [c₁, c₀]; linarith
  have hdiff_nn : 0 ≤ q_min * (h0 - K) + (K' - b0) := by
    unfold q_min; nlinarith [hK.2, hK'.1]
  have hc1_pos : 0 < c₁ := by linarith
  have hlog : (c₁ - c₀) / c₁ ≤ Real.log c₁ - Real.log c₀ := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hc0 hc1_pos)
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt hc1_pos)] at hconc
    have hrew : 1 - c₀ / c₁ = (c₁ - c₀) / c₁ := by
      have hc1_ne : c₁ ≠ 0 := ne_of_gt hc1_pos
      field_simp [hc1_ne]
    linarith
  have hlog_lb : (q_min * (h0 - K) + (K' - b0)) / C_max0_ub ≤ Real.log c₁ - Real.log c₀ := by
    have h1 := div_le_div_of_nonneg_left hdiff_nn hc1_pos hc1_le
    have h2 := div_le_div_of_nonneg_right hdiff (le_of_lt hc1_pos)
    linarith
  have hu_bound : u θ.η c₀ L ≤ R_hat0 - m_omega0 * (h0 - K) - (eta_min / C_max0_ub) * (K' - b0) := by
    have heta_nn : 0 ≤ eta_min := by unfold eta_min; norm_num
    have hC_pos : 0 < C_max0_ub := by unfold C_max0_ub; norm_num
    have hlog_nn : 0 ≤ (q_min * (h0 - K) + (K' - b0)) / C_max0_ub :=
      div_nonneg hdiff_nn (le_of_lt hC_pos)
    have hmul : eta_min * ((q_min * (h0 - K) + (K' - b0)) / C_max0_ub) ≤
        θ.η * (Real.log c₁ - Real.log c₀) :=
      mul_le_mul θ.hη.1 hlog_lb hlog_nn (le_trans heta_nn θ.hη.1)
    have hu_diff : u θ.η c₁ L - u θ.η c₀ L = θ.η * (Real.log c₁ - Real.log c₀) := by
      unfold u; ring
    unfold m_omega0
    have : eta_min * ((q_min * (h0 - K) + (K' - b0)) / C_max0_ub) =
        eta_min * q_min / C_max0_ub * (h0 - K) + eta_min / C_max0_ub * (K' - b0) := by ring
    linarith
  have hβ_ub : θ.β ≤ beta_max := θ.hβ.2
  have hβ_lb : beta_min ≤ θ.β := θ.hβ.1
  have hK'_comb : beta_min * q_min * (h0 - b0) ≤ (K' - b0) + θ.β * q_min * (h0 - K') := by
    have hβq_lt : θ.β * q_min ≤ 1 := by unfold beta_max q_min at *; nlinarith
    have h1 : (1 - θ.β * q_min) * (K' - b0) ≥ 0 := mul_nonneg (by linarith) (by linarith [hK'.1])
    have h2 : beta_min * q_min * (h0 - b0) ≤ θ.β * q_min * (h0 - b0) := by
      unfold q_min h0 b0 at *; nlinarith
    nlinarith
  have hDelta : Delta0 ≤ (eta_min / C_max0_ub) * ((K' - b0) + θ.β * q_min * (h0 - K')) := by
    have hfac : 0 ≤ eta_min / C_max0_ub := by unfold eta_min C_max0_ub; positivity
    have hmul := mul_le_mul_of_nonneg_left hK'_comb hfac
    have hrew : eta_min / C_max0_ub * (beta_min * q_min * (h0 - b0)) =
        eta_min * beta_min * q_min * (h0 - b0) / C_max0_ub := by ring
    linarith [Delta0_le_exact]
  have hBstar_eq : R_hat0 - Delta0 + θ.β * B0_star θ.β = B0_star θ.β := by
    unfold B0_star
    have h1β : 1 - θ.β ≠ 0 := by unfold beta_max at hβ_ub; linarith
    field_simp [h1β]; ring
  have hrew_prod : θ.β * (eta_min * q_min / C_max0_ub * (h0 - K')) =
      eta_min / C_max0_ub * (θ.β * q_min * (h0 - K')) := by ring
  have hrew_add : eta_min / C_max0_ub * (K' - b0 + θ.β * q_min * (h0 - K')) =
      eta_min / C_max0_ub * (K' - b0) + eta_min / C_max0_ub * (θ.β * q_min * (h0 - K')) := by ring
  unfold B0 m_omega0 at *
  linarith

/-- Cota uniforme $B_{0,*}(\beta) \le B_{0,*}^{\max}$ en la caja $\mathcal{P}$. -/
lemma B0_star_le_max (θ : Params) : B0_star θ.β ≤ B0_star_max := by
  have hβ_ub : θ.β ≤ beta_max := θ.hβ.2
  have hβ_lb : beta_min ≤ θ.β := θ.hβ.1
  unfold B0_star_max B0_star
  have hnum : R_hat0 - Delta0 ≤ 0 := by unfold R_hat0 Delta0; norm_num
  have hden_pos : 0 < 1 - θ.β := by unfold beta_max at hβ_ub; linarith
  have hden_le : 1 - θ.β ≤ 1 - beta_min := by linarith
  have hpos := div_le_div_of_nonneg_left (neg_nonneg.mpr hnum) hden_pos hden_le
  have h1 : -(R_hat0 - Delta0) / (1 - beta_min) = -((R_hat0 - Delta0) / (1 - beta_min)) := by ring
  have h2 : -(R_hat0 - Delta0) / (1 - θ.β) = -((R_hat0 - Delta0) / (1 - θ.β)) := by ring
  linarith

/-- Cota superior analítica en el borde derecho de $M_0$: $\Psi^\#(0.10) < -34.30$. -/
lemma psi_sharp_h0_lt : Psi_sharp h0 < -343 / 10 := by
  unfold Psi_sharp h0
  have hsq : Real.sqrt (10 / 100) < 316228 / 1000000 := by
    have : (Real.sqrt (10 / 100)) ^ 2 = 10 / 100 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (10 / 100)]
  have hpos : 0 < Real.sqrt (10 / 100) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (5 / (316228 / 1000000) : ℝ) < 5 / Real.sqrt (10 / 100) := by
    rw [div_lt_div_iff₀ (by norm_num) hpos]
    linarith
  linarith

/-- Monotonicidad de $\Psi^\#(x) - B_0(\beta, x)$ en $[b_0, h_0]$ sin derivadas. -/
lemma psi_sharp_sub_B0_le_h0 (β : ℝ) {x : ℝ} (hx : b0 ≤ x ∧ x ≤ h0) :
    Psi_sharp x - B0 β x ≤ Psi_sharp h0 - B0 β h0 := by
  have hx0 : 0 < x := by unfold b0 at hx; linarith
  have hh0 : 0 < h0 := by unfold h0; norm_num
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsh : 0 < Real.sqrt h0 := Real.sqrt_pos.mpr hh0
  have hle_s : Real.sqrt x ≤ Real.sqrt h0 := Real.sqrt_le_sqrt hx.2
  have hsh_lt : Real.sqrt h0 < 32 / 100 := by
    have : (Real.sqrt h0) ^ 2 = h0 := Real.sq_sqrt (le_of_lt hh0)
    unfold h0 at *; nlinarith
  set D := Real.sqrt x * Real.sqrt h0 * (Real.sqrt h0 + Real.sqrt x)
  have hD_pos : 0 < D := by positivity
  have hrat : (1 / Real.sqrt x - 1 / Real.sqrt h0) * D = h0 - x := by
    dsimp [D]
    have hsx_ne : Real.sqrt x ≠ 0 := ne_of_gt hsx
    have hsh_ne : Real.sqrt h0 ≠ 0 := ne_of_gt hsh
    field_simp [hsx_ne, hsh_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hx0), Real.sq_sqrt (le_of_lt hh0)]
  have hD_lt : D < 1 / 10 := by
    have h1 : Real.sqrt x * Real.sqrt h0 ≤ h0 := by
      have : (Real.sqrt h0) ^ 2 = h0 := Real.sq_sqrt (le_of_lt hh0)
      nlinarith
    have h2 : Real.sqrt h0 + Real.sqrt x ≤ 2 * Real.sqrt h0 := by linarith
    have h3 : D ≤ h0 * (2 * Real.sqrt h0) := mul_le_mul h1 h2 (by linarith) (le_of_lt hh0)
    unfold h0 at *; nlinarith
  have hinv_lb : (50 : ℝ) * (h0 - x) ≤ 5 * (1 / Real.sqrt x - 1 / Real.sqrt h0) := by
    have hhx : 0 ≤ h0 - x := by linarith [hx.2]
    have h1 : (h0 - x) / (1 / 10) ≤ (h0 - x) / D :=
      div_le_div_of_nonneg_left hhx hD_pos (le_of_lt hD_lt)
    have h2 : 1 / Real.sqrt x - 1 / Real.sqrt h0 = (h0 - x) / D :=
      eq_div_of_mul_eq (ne_of_gt hD_pos) hrat
    linarith
  have h5 : 5 / Real.sqrt x - 5 / Real.sqrt h0 = 5 * (1 / Real.sqrt x - 1 / Real.sqrt h0) := by ring
  have hm_lt : m_omega0 ≤ 7 := by unfold m_omega0 eta_min q_min C_max0_ub; norm_num
  unfold Psi_sharp B0
  nlinarith [hx.2]

/-- Cota maestra en $M_0 = [0.05, 0.10)$ para cualquier trayectoria de $T$ pasos. -/
theorem prop1_master_bound (θ : Params) (T : ℕ) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ T, b0 ≤ x t ∧ x t < h0)
    (hL : ∀ t < T, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < T, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x T)) :
    (∑ t ∈ range T, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ T * V_cont ≤
    B0_max (x 0) + beta_max ^ T * (-343 / 10 - B0_star_max) := by
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have hβ1 : θ.β ≤ 1 := le_trans θ.hβ.2 (by unfold beta_max; norm_num)
  have htel := telescoping_bellman hβ0 (B0 θ.β)
    (fun t => u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) x T
    (fun t ht => prop1_one_step_bellman θ
      (hx t (le_of_lt ht)) (hx (t + 1) ht) (hL t ht) (hc t ht))
  have hcont : V_cont - B0 θ.β (x T) ≤ -343 / 10 - B0_star θ.β := by
    have hmono := psi_sharp_sub_B0_le_h0 θ.β ⟨(hx T le_rfl).1, le_of_lt (hx T le_rfl).2⟩
    have hB0h : B0 θ.β h0 = B0_star θ.β := by unfold B0; ring
    linarith [psi_sharp_h0_lt]
  have hβT_nn : 0 ≤ θ.β ^ T := pow_nonneg hβ0 T
  have hstep2 : (∑ t ∈ range T, θ.β ^ t *
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) + θ.β ^ T * V_cont ≤
      (1 - θ.β ^ T) * B0_star θ.β - m_omega0 * (h0 - x 0) + θ.β ^ T * (-343 / 10) := by
    have hmul := mul_le_mul_of_nonneg_left hcont hβT_nn
    have hdist1 : θ.β ^ T * (V_cont - B0 θ.β (x T)) =
        θ.β ^ T * V_cont - θ.β ^ T * B0 θ.β (x T) := by ring
    have hdist2 : (1 - θ.β ^ T) * B0_star θ.β = B0_star θ.β - θ.β ^ T * B0_star θ.β := by ring
    have hdist3 : θ.β ^ T * (-343 / 10 - B0_star θ.β) =
        θ.β ^ T * (-343 / 10) - θ.β ^ T * B0_star θ.β := by ring
    unfold B0 at htel hmul hdist1
    linarith
  have h1mβT : 0 ≤ 1 - θ.β ^ T := sub_nonneg.mpr (pow_le_one₀ hβ0 hβ1)
  have hB_le : (1 - θ.β ^ T) * B0_star θ.β ≤ (1 - θ.β ^ T) * B0_star_max :=
    mul_le_mul_of_nonneg_left (B0_star_le_max θ) h1mβT
  have hgap_pos : 0 ≤ -343 / 10 - B0_star_max := by
    unfold B0_star_max B0_star R_hat0 Delta0 beta_min; norm_num
  have hpow_le : θ.β ^ T ≤ beta_max ^ T := pow_le_pow_left₀ hβ0 θ.hβ.2 T
  have hgap_mul : θ.β ^ T * (-343 / 10 - B0_star_max) ≤
      beta_max ^ T * (-343 / 10 - B0_star_max) :=
    mul_le_mul_of_nonneg_right hpow_le hgap_pos
  unfold B0_max
  linarith

/-! ## 4. Testigos explícitos de 3 pasos en $M_0$ y certificación vía `MVS.Lemma11` -/

/-- Lema auxiliar: cota inferior certificada para un paso de utilidad $u(\theta.\eta, c, L)$
    cuando $0 < c_{\text{lo}} \le c$ y $c_{\text{lo}} \le 1 - L < 1$. -/
lemma step_u_lb (θ : Params) {k kp L sg_lo rU_c rU_L : ℝ} {sL : ℕ}
    (hk : 0 < k) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hsg_nn : 0 ≤ sg_lo) (hsg_sq : sg_lo ^ 2 ≤ 2 * k * L / (k + L))
    (hc_pos : 0 < q_min * k + A_min * (2 * k * L / (k + L)) * sg_lo - kp)
    (hc_le1 : q_min * k + A_min * (2 * k * L / (k + L)) * sg_lo - kp ≤ 1)
    (hrU_c : 1 ≤ rU_c)
    (hmU_c : 1 / (q_min * k + A_min * (2 * k * L / (k + L)) * sg_lo - kp) ≤ rU_c ^ (2 ^ 4))
    (hrU_L : 1 ≤ rU_L) (hmU_L : 1 / (1 - L) ≤ rU_L ^ (2 ^ sL))
    (hord : -((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_c - 1) / (rU_c + 1)) +
        MVS.Lemma11.atanhRemUB 3 ((rU_c - 1) / (rU_c + 1)))) ≤
      -((2 ^ sL : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_L - 1) / (rU_L + 1)) +
        MVS.Lemma11.atanhRemUB 3 ((rU_L - 1) / (rU_L + 1))))) :
    eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_c - 1) / (rU_c + 1)) +
        MVS.Lemma11.atanhRemUB 3 ((rU_c - 1) / (rU_c + 1))))) +
      (1 - eta_max) * (-((2 ^ sL : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_L - 1) / (rU_L + 1)) +
        MVS.Lemma11.atanhRemUB 3 ((rU_L - 1) / (rU_L + 1))))) ≤
    u θ.η (q_min * k + F A_min k L - kp) L := by
  set g := 2 * k * L / (k + L)
  set c_lo := q_min * k + A_min * g * sg_lo - kp
  set L1 := -((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_c - 1) / (rU_c + 1)) +
    MVS.Lemma11.atanhRemUB 3 ((rU_c - 1) / (rU_c + 1))))
  set L2 := -((2 ^ sL : ℝ) * (MVS.Lemma11.atanhSeries 3 ((rU_L - 1) / (rU_L + 1)) +
    MVS.Lemma11.atanhRemUB 3 ((rU_L - 1) / (rU_L + 1))))
  have hg_nn : 0 ≤ g := div_nonneg (by positivity) (by linarith)
  have hsg_le : sg_lo ≤ Real.sqrt g := by
    have hsq : sg_lo ^ 2 ≤ (Real.sqrt g) ^ 2 := by rw [Real.sq_sqrt hg_nn]; exact hsg_sq
    nlinarith [Real.sqrt_nonneg g]
  have hc_ge : c_lo ≤ q_min * k + F A_min k L - kp := by
    dsimp [c_lo]; unfold F; dsimp only
    have hA_nn : 0 ≤ A_min := by unfold A_min; norm_num
    have := mul_le_mul_of_nonneg_left hsg_le (mul_nonneg hA_nn hg_nn)
    linarith
  have hlog_c : L1 ≤ Real.log (q_min * k + F A_min k L - kp) := by
    have hmL : (1 : ℝ) ^ (2 ^ 4) ≤ 1 / c_lo := by rw [one_pow, one_le_div hc_pos]; exact hc_le1
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 4 (m := 1 / c_lo)
      (rL := 1) (rU := rU_c) le_rfl hrU_c hmL hmU_c).2
    rw [Real.log_div (by norm_num) (ne_of_gt hc_pos), Real.log_one, zero_sub] at hb
    have hmono := Real.log_le_log hc_pos hc_ge
    dsimp [L1]; linarith
  have hlog_L : L2 ≤ Real.log (1 - L) := by
    have h1mL : 0 < 1 - L := by linarith
    have hmL : (1 : ℝ) ^ (2 ^ sL) ≤ 1 / (1 - L) := by
      rw [one_pow, one_le_div h1mL]; linarith
    have hb := (MVS.Lemma11.log_bounds_of_pow_enclosure 3 sL (m := 1 / (1 - L))
      (rL := 1) (rU := rU_L) le_rfl hrU_L hmL hmU_L).2
    rw [Real.log_div (by norm_num) (ne_of_gt h1mL), Real.log_one, zero_sub] at hb
    dsimp [L2]; linarith
  have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
  have h1 := mul_le_mul_of_nonneg_left hlog_c hη_nn
  have h2 := mul_le_mul_of_nonneg_left hlog_L h1mη_nn
  have h3 : eta_max * (L1 - L2) ≤ θ.η * (L1 - L2) :=
    mul_le_mul_of_nonpos_right θ.hη.2 (by linarith [hord])
  unfold u; linarith

/-- Testigo original de 3 pasos en $M_0$: $(K_0 \to 0.065 \to 0.0845 \to 0.10)$ con $L = 0.75$. -/
def W_M0_orig (θ : Params) (K0 : ℝ) : ℝ :=
  u θ.η (q_min * K0 + F A_min K0 (75 / 100) - 65 / 1000) (75 / 100) +
  θ.β * u θ.η (q_min * (65 / 1000) + F A_min (65 / 1000) (75 / 100) - 845 / 10000) (75 / 100) +
  θ.β ^ 2 * u θ.η (q_min * (845 / 10000) + F A_min (845 / 10000) (75 / 100) - b) (75 / 100) +
  θ.β ^ 3 * W_M θ b

/-- Testigo afinado de 3 pasos en $M_0$: $(K_0 \to 0.0595 \to 0.0755 \to 0.10)$ con $L = (0.45, 0.50, 0.60)$. -/
def W_M0_sharp (θ : Params) (K0 : ℝ) : ℝ :=
  u θ.η (q_min * K0 + F A_min K0 (45 / 100) - 595 / 10000) (45 / 100) +
  θ.β * u θ.η (q_min * (595 / 10000) + F A_min (595 / 10000) (50 / 100) - 755 / 10000) (50 / 100) +
  θ.β ^ 2 * u θ.η (q_min * (755 / 10000) + F A_min (755 / 10000) (60 / 100) - b) (60 / 100) +
  θ.β ^ 3 * W_M θ b

/-- Certificación de $W_{M_0}^{\text{orig}}(\theta, K_0) > -43.845$ para todo $\theta \in \mathcal{P}$
    y todo $K_0 \ge 0.05$. -/
theorem W_M0_orig_ge (θ : Params) {K0 : ℝ} (hK0 : b0 ≤ K0) :
    (-43845 / 1000 : ℝ) < W_M0_orig θ K0 := by
  have hb0_pos : (0 : ℝ) < b0 := by unfold b0; norm_num
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  -- Monotonicidad en K0 del primer paso
  have hc0_mono : q_min * b0 + F A_min b0 (75 / 100) - 65 / 1000 ≤
      q_min * K0 + F A_min K0 (75 / 100) - 65 / 1000 := by
    have hF : F A_min b0 (75 / 100) ≤ F A_min K0 (75 / 100) :=
      F_mono_K (by unfold A_min; norm_num) hb0_pos hK0 (by norm_num)
    have hq : q_min * b0 ≤ q_min * K0 := mul_le_mul_of_nonneg_left hK0 (by unfold q_min; norm_num)
    linarith
  have hc0_pos : 0 < q_min * b0 + F A_min b0 (75 / 100) - 65 / 1000 := by
    unfold F q_min A_min b0
    have hrat : 2 * (5 / 100 : ℝ) * (75 / 100) / (5 / 100 + 75 / 100) = 3 / 32 := by norm_num
    rw [hrat]
    have hsq : (153093 / 500000 : ℝ) ^ 2 ≤ (Real.sqrt (3 / 32)) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    have hsg : (153093 / 500000 : ℝ) ≤ Real.sqrt (3 / 32) := by
      nlinarith [Real.sqrt_nonneg (3 / 32)]
    nlinarith
  have hu0_mono : u θ.η (q_min * b0 + F A_min b0 (75 / 100) - 65 / 1000) (75 / 100) ≤
      u θ.η (q_min * K0 + F A_min K0 (75 / 100) - 65 / 1000) (75 / 100) := by
    unfold u
    have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log hc0_pos hc0_mono) hη_nn]
  -- Cota inferior certificada para los 3 pasos
  have hu0 := step_u_lb θ (k := b0) (kp := 65 / 1000) (L := 75 / 100)
    (sg_lo := 153093 / 500000) (rU_c := 727199 / 500000) (rU_L := 148651 / 125000) (sL := 3)
    hb0_pos (by norm_num) (by norm_num) (by norm_num)
    (by unfold b0; norm_num) (by unfold q_min A_min b0; norm_num)
    (by unfold q_min A_min b0; norm_num) (by norm_num)
    (by unfold q_min A_min b0; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  have hu1 := step_u_lb θ (k := 65 / 1000) (kp := 845 / 10000) (L := 75 / 100)
    (sg_lo := 172939 / 500000) (rU_c := 1372787 / 1000000) (rU_L := 148651 / 125000) (sL := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by unfold q_min A_min; norm_num)
    (by unfold q_min A_min; norm_num) (by norm_num)
    (by unfold q_min A_min; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  have hu2 := step_u_lb θ (k := 845 / 10000) (kp := b) (L := 75 / 100)
    (sg_lo := 389727 / 1000000) (rU_c := 253831 / 200000) (rU_L := 148651 / 125000) (sL := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by unfold q_min A_min b; norm_num)
    (by unfold q_min A_min b; norm_num) (by norm_num)
    (by unfold q_min A_min b; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  -- Acotar factores β^t ≤ β_+^t para términos negativos
  set u0_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((727199 / 500000 : ℝ) - 1) / ((727199 / 500000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((727199 / 500000 : ℝ) - 1) / ((727199 / 500000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 3 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)))))
  set u1_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((1372787 / 1000000 : ℝ) - 1) / ((1372787 / 1000000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((1372787 / 1000000 : ℝ) - 1) / ((1372787 / 1000000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 3 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)))))
  set u2_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((253831 / 200000 : ℝ) - 1) / ((253831 / 200000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((253831 / 200000 : ℝ) - 1) / ((253831 / 200000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 3 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((148651 / 125000 : ℝ) - 1) / ((148651 / 125000 : ℝ) + 1)))))
  have hu1_np : u1_lb ≤ 0 := by
    dsimp [u1_lb]; unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max
    norm_num [Finset.sum_range_succ]
  have hu2_np : u2_lb ≤ 0 := by
    dsimp [u2_lb]; unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max
    norm_num [Finset.sum_range_succ]
  have hβ1_le : θ.β ≤ beta_max := θ.hβ.2
  have hβ2_le : θ.β ^ 2 ≤ beta_max ^ 2 := pow_le_pow_left₀ hβ0 hβ1_le 2
  have hβ3_le : θ.β ^ 3 ≤ beta_max ^ 3 := pow_le_pow_left₀ hβ0 hβ1_le 3
  have ht1 : beta_max * u1_lb ≤ θ.β * u θ.η (q_min * (65 / 1000) + F A_min (65 / 1000) (75 / 100) - 845 / 10000) (75 / 100) :=
    le_trans (mul_le_mul_of_nonpos_right hβ1_le hu1_np) (mul_le_mul_of_nonneg_left hu1 hβ0)
  have ht2 : beta_max ^ 2 * u2_lb ≤ θ.β ^ 2 * u θ.η (q_min * (845 / 10000) + F A_min (845 / 10000) (75 / 100) - b) (75 / 100) :=
    le_trans (mul_le_mul_of_nonpos_right hβ2_le hu2_np) (mul_le_mul_of_nonneg_left hu2 (pow_nonneg hβ0 2))
  have ht3 : beta_max ^ 3 * (-3558 / 100 : ℝ) ≤ θ.β ^ 3 * W_M θ b :=
    le_trans (mul_le_mul_of_nonpos_right hβ3_le (by norm_num))
      (mul_le_mul_of_nonneg_left (W_M_b_ge θ) (pow_nonneg hβ0 3))
  have hsum : (-43845 / 1000 : ℝ) <
      u0_lb + beta_max * u1_lb + beta_max ^ 2 * u2_lb + beta_max ^ 3 * (-3558 / 100) := by
    dsimp [u0_lb, u1_lb, u2_lb]
    unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max beta_max
    norm_num [Finset.sum_range_succ]
  unfold W_M0_orig
  linarith

/-- Certificación del testigo afinado $W_{M_0}^{\text{sharp}}(\theta, K_0) > -43.541$
    para todo $\theta \in \mathcal{P}$ y todo $K_0 \ge 0.05$. -/
theorem W_M0_sharp_ge (θ : Params) {K0 : ℝ} (hK0 : b0 ≤ K0) :
    (-43541 / 1000 : ℝ) < W_M0_sharp θ K0 := by
  have hb0_pos : (0 : ℝ) < b0 := by unfold b0; norm_num
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have hc0_mono : q_min * b0 + F A_min b0 (45 / 100) - 595 / 10000 ≤
      q_min * K0 + F A_min K0 (45 / 100) - 595 / 10000 := by
    have hF : F A_min b0 (45 / 100) ≤ F A_min K0 (45 / 100) :=
      F_mono_K (by unfold A_min; norm_num) hb0_pos hK0 (by norm_num)
    have hq : q_min * b0 ≤ q_min * K0 := mul_le_mul_of_nonneg_left hK0 (by unfold q_min; norm_num)
    linarith
  have hc0_pos : 0 < q_min * b0 + F A_min b0 (45 / 100) - 595 / 10000 := by
    unfold F q_min A_min b0
    have hrat : 2 * (5 / 100 : ℝ) * (45 / 100) / (5 / 100 + 45 / 100) = 9 / 100 := by norm_num
    rw [hrat]
    have hsq : (3 / 10 : ℝ) ^ 2 ≤ (Real.sqrt (9 / 100)) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    have hsg : (3 / 10 : ℝ) ≤ Real.sqrt (9 / 100) := by nlinarith [Real.sqrt_nonneg (9 / 100)]
    nlinarith
  have hu0_mono : u θ.η (q_min * b0 + F A_min b0 (45 / 100) - 595 / 10000) (45 / 100) ≤
      u θ.η (q_min * K0 + F A_min K0 (45 / 100) - 595 / 10000) (45 / 100) := by
    unfold u
    have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log hc0_pos hc0_mono) hη_nn]
  have hu0 := step_u_lb θ (k := b0) (kp := 595 / 10000) (L := 45 / 100)
    (sg_lo := 3 / 10) (rU_c := 13671 / 10000) (rU_L := 116121 / 100000) (sL := 2)
    hb0_pos (by norm_num) (by norm_num) (by norm_num)
    (by unfold b0; norm_num) (by unfold q_min A_min b0; norm_num)
    (by unfold q_min A_min b0; norm_num) (by norm_num)
    (by unfold q_min A_min b0; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  have hu1 := step_u_lb θ (k := 595 / 10000) (kp := 755 / 10000) (L := 50 / 100)
    (sg_lo := 65221 / 200000) (rU_c := 138901 / 100000) (rU_L := 118921 / 100000) (sL := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by unfold q_min A_min; norm_num)
    (by unfold q_min A_min; norm_num) (by norm_num)
    (by unfold q_min A_min; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  have hu2 := step_u_lb θ (k := 755 / 10000) (kp := b) (L := 60 / 100)
    (sg_lo := 366227 / 1000000) (rU_c := 68669 / 50000) (rU_L := 7859 / 6250) (sL := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by unfold q_min A_min b; norm_num)
    (by unfold q_min A_min b; norm_num) (by norm_num)
    (by unfold q_min A_min b; norm_num) (by norm_num) (by norm_num)
    (by unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB
        norm_num [Finset.sum_range_succ])
  set u0_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((13671 / 10000 : ℝ) - 1) / ((13671 / 10000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((13671 / 10000 : ℝ) - 1) / ((13671 / 10000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 2 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((116121 / 100000 : ℝ) - 1) / ((116121 / 100000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((116121 / 100000 : ℝ) - 1) / ((116121 / 100000 : ℝ) + 1)))))
  set u1_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((138901 / 100000 : ℝ) - 1) / ((138901 / 100000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((138901 / 100000 : ℝ) - 1) / ((138901 / 100000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 2 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((118921 / 100000 : ℝ) - 1) / ((118921 / 100000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((118921 / 100000 : ℝ) - 1) / ((118921 / 100000 : ℝ) + 1)))))
  set u2_lb := eta_max * (-((2 ^ 4 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((68669 / 50000 : ℝ) - 1) / ((68669 / 50000 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((68669 / 50000 : ℝ) - 1) / ((68669 / 50000 : ℝ) + 1))))) +
    (1 - eta_max) * (-((2 ^ 2 : ℝ) * (MVS.Lemma11.atanhSeries 3 (((7859 / 6250 : ℝ) - 1) / ((7859 / 6250 : ℝ) + 1)) +
      MVS.Lemma11.atanhRemUB 3 (((7859 / 6250 : ℝ) - 1) / ((7859 / 6250 : ℝ) + 1)))))
  have hu1_np : u1_lb ≤ 0 := by
    dsimp [u1_lb]; unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max
    norm_num [Finset.sum_range_succ]
  have hu2_np : u2_lb ≤ 0 := by
    dsimp [u2_lb]; unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max
    norm_num [Finset.sum_range_succ]
  have hβ1_le : θ.β ≤ beta_max := θ.hβ.2
  have hβ2_le : θ.β ^ 2 ≤ beta_max ^ 2 := pow_le_pow_left₀ hβ0 hβ1_le 2
  have hβ3_le : θ.β ^ 3 ≤ beta_max ^ 3 := pow_le_pow_left₀ hβ0 hβ1_le 3
  have ht1 : beta_max * u1_lb ≤ θ.β * u θ.η (q_min * (595 / 10000) + F A_min (595 / 10000) (50 / 100) - 755 / 10000) (50 / 100) :=
    le_trans (mul_le_mul_of_nonpos_right hβ1_le hu1_np) (mul_le_mul_of_nonneg_left hu1 hβ0)
  have ht2 : beta_max ^ 2 * u2_lb ≤ θ.β ^ 2 * u θ.η (q_min * (755 / 10000) + F A_min (755 / 10000) (60 / 100) - b) (60 / 100) :=
    le_trans (mul_le_mul_of_nonpos_right hβ2_le hu2_np) (mul_le_mul_of_nonneg_left hu2 (pow_nonneg hβ0 2))
  have ht3 : beta_max ^ 3 * (-3558 / 100 : ℝ) ≤ θ.β ^ 3 * W_M θ b :=
    le_trans (mul_le_mul_of_nonpos_right hβ3_le (by norm_num))
      (mul_le_mul_of_nonneg_left (W_M_b_ge θ) (pow_nonneg hβ0 3))
  have hsum : (-43541 / 1000 : ℝ) <
      u0_lb + beta_max * u1_lb + beta_max ^ 2 * u2_lb + beta_max ^ 3 * (-3558 / 100) := by
    dsimp [u0_lb, u1_lb, u2_lb]
    unfold MVS.Lemma11.atanhSeries MVS.Lemma11.atanhRemUB eta_max beta_max
    norm_num [Finset.sum_range_succ]
  unfold W_M0_sharp
  linarith

/-! ## 5. Proposición 1 cerrada ($\tau_{0.1} \le 10$ en todo $M_0 = [0.05, 0.10)$) -/

/-- Proposición 1 completamente autocontenida (cero hipótesis externas):
    para todo $\theta \in \mathcal{P}$, ninguna trayectoria óptima puede permanecer
    $10$ períodos en $M_0 = [0.05, 0.10)$, siendo estrictamente dominada por
    $W_{M_0}^{\text{orig}}(\theta, x_0)$ (y con mayor holgura por $W_{M_0}^{\text{sharp}}(\theta, x_0)$). -/
theorem prop1_uniform_10 (θ : Params) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 10, b0 ≤ x t ∧ x t < h0)
    (hL : ∀ t < 10, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 10, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x 10)) :
    (∑ t ∈ range 10, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 10 * V_cont < W_M0_orig θ (x 0) := by
  have hmaster := prop1_master_bound θ 10 x L V_cont hx hL hc hV
  have hB0_le : B0_max (x 0) ≤ B0_star_max := by
    unfold B0_max m_omega0 eta_min q_min C_max0_ub
    have := (hx 0 (by norm_num)).2
    nlinarith
  have hnum : B0_star_max + beta_max ^ 10 * (-343 / 10 - B0_star_max) < -43845 / 1000 := by
    unfold B0_star_max B0_star R_hat0 Delta0 beta_min beta_max
    norm_num
  have hW := W_M0_orig_ge θ (hx 0 (by norm_num)).1
  linarith

end

end MVS.Proposition1
