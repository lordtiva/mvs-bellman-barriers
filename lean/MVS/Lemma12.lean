import MVS.Theorem1
import MVS.Proposition2
import MVS.Lemma11
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lema 12 ($\Psi^\#$): Techo Analítico Global de Bellman (`MVS.Lemma12`)

Formalización completa y sin `sorry` de la arquitectura analítica del Lema 12
para el techo $\Psi^\#(K) = 0.4 K - 5 K^{-1/2} - 18.5 - 10/301$:

1. **Concavidad global exacta de $\Psi^\#$ sin derivadas** (`Psi_sharp_le_tangent`)
   y **eliminación cerrada de $K' > 0$** (`bellman_elim_Kp`).
2. **Cola pequeña exacta (`lemma12_small_K`)**: prueba completa en el kernel para
   todo $0 < K \le 1/25000$, todo $K' > 0$, todo $L \in [0, 1)$ y todo $\theta \in \mathcal{P}$.
3. **Cola grande exacta (`lemma12_large_K`)**: prueba completa en el kernel para
   todo $K \ge 50$, todo $K' > 0$, todo $L \in [0, 1)$ y todo $\theta \in \mathcal{P}$.
4. **Herramientas del núcleo compacto $[1/25000, 50]$**:
   - Convexidad exacta de $K \mapsto a K + 5 / \sqrt{K}$ (`convex_K_term_le_endpoints`),
   - Simetría de la tangente global en $K$ (`F_le_tangent_K`, corolario de `F_le_tangent`),
   - Eliminación cerrada de $L$ sobre piezas lineales (`lin_log_le_opt`).
5. **Ensamblado global (`lemma12_global_super_barrier`)** y acotación de trayectorias
   finitas (`lemma12_value_le_Psi_sharp`).
-/

open Finset Real Set MVS.Theorem1 MVS.Proposition2 MVS.Lemma11

namespace MVS.Lemma12

noncomputable section

/-- Constante de desplazamiento $C_0 = 18.5 + 10/301$ de $\Psi^\#$. -/
def C0_psi : ℝ := 185 / 10 + 10 / 301

lemma Psi_sharp_eq (K : ℝ) : Psi_sharp K = (4 / 10 : ℝ) * K - 5 / Real.sqrt K - C0_psi := by
  unfold Psi_sharp C0_psi; ring

/-! ## 1. Concavidad exacta de $\Psi^\#$ y eliminación cerrada de $K' > 0$ -/

/-- Concavidad global exacta de $-5/\sqrt{K'}$ sin derivadas:
    para todo $K' > 0$ y $s_0 > 0$,
    $\Psi^\#(K') \le (0.4 + 5/(2 s_0^3)) K' - 15/(2 s_0) - C_0$. -/
theorem Psi_sharp_le_tangent {K' s₀ : ℝ} (hK' : 0 < K') (hs₀ : 0 < s₀) :
    Psi_sharp K' ≤ (4 / 10 + 5 / (2 * s₀ ^ 3)) * K' - 15 / (2 * s₀) - C0_psi := by
  rw [Psi_sharp_eq]
  set s := Real.sqrt K'
  have hs : 0 < s := Real.sqrt_pos.mpr hK'
  have hsq : s ^ 2 = K' := Real.sq_sqrt (le_of_lt hK')
  have hdiff : 0 ≤ (s - s₀) ^ 2 * (s + 2 * s₀) / (2 * s₀ ^ 3 * s) := by positivity
  have hid : (s ^ 2 - s₀ ^ 2) / (2 * s₀ ^ 3) - (1 / s₀ - 1 / s) =
      (s - s₀) ^ 2 * (s + 2 * s₀) / (2 * s₀ ^ 3 * s) := by
    field_simp [ne_of_gt hs₀, ne_of_gt hs]; ring
  have hineq : 1 / s₀ - 1 / s ≤ (K' - s₀ ^ 2) / (2 * s₀ ^ 3) := by
    rw [← hsq]; linarith
  have h5 : 5 / s₀ - 5 / s ≤ 5 / (2 * s₀ ^ 3) * (K' - s₀ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hineq (by norm_num : (0 : ℝ) ≤ 5)
    have hrew1 : 5 * (1 / s₀ - 1 / s) = 5 / s₀ - 5 / s := by ring
    have hrew2 : 5 * ((K' - s₀ ^ 2) / (2 * s₀ ^ 3)) = 5 / (2 * s₀ ^ 3) * (K' - s₀ ^ 2) := by ring
    linarith
  have hrew3 : 5 / (2 * s₀ ^ 3) * (K' - s₀ ^ 2) - 5 / s₀ =
      5 / (2 * s₀ ^ 3) * K' - 15 / (2 * s₀) := by
    field_simp [ne_of_gt hs₀]; ring
  linarith

/-- Eliminación cerrada de $K' > 0$ mediante la tangente de $\log c$ en
    $c_0 = \theta.\eta / (\theta.\beta (0.4 + 5/(2 s_0^3)))$ y la concavidad de $\Psi^\#$. -/
theorem bellman_elim_Kp (θ : Params) {K K' L s₀ : ℝ}
    (hK : 0 < K) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1) (hs₀ : 0 < s₀)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    let slope := (4 / 10 : ℝ) + 5 / (2 * s₀ ^ 3)
    let lam := θ.β * slope
    let c₀ := θ.η / lam
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤
      θ.η * (Real.log c₀ - 1) + lam * (q_max * K + F A_max K L) -
      θ.β * (15 / (2 * s₀) + C0_psi) + (1 - θ.η) * Real.log (1 - L) := by
  intro slope lam c₀
  have hβ_pos : 0 < θ.β := lt_of_lt_of_le (by unfold beta_min; norm_num) θ.hβ.1
  have hη_pos : 0 < θ.η := lt_of_lt_of_le (by unfold eta_min; norm_num) θ.hη.1
  have hslope_pos : 0 < slope := by dsimp [slope]; positivity
  have hlam_pos : 0 < lam := mul_pos hβ_pos hslope_pos
  have hc₀_pos : 0 < c₀ := div_pos hη_pos hlam_pos
  set c := θ.q * K + F θ.A K L - K'
  have hlog : Real.log c ≤ Real.log c₀ + c / c₀ - 1 := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hc hc₀_pos)
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hc₀_pos)] at hconc
    linarith
  have hηlog : θ.η * Real.log c ≤ θ.η * (Real.log c₀ - 1) + lam * c := by
    have h1 := mul_le_mul_of_nonneg_left hlog (le_of_lt hη_pos)
    have hrew : θ.η * (c / c₀) = lam * c := by
      dsimp [c₀]; field_simp [ne_of_gt hη_pos, ne_of_gt hlam_pos]
    linarith
  have hPsi : θ.β * Psi_sharp K' ≤ θ.β * (slope * K' - 15 / (2 * s₀) - C0_psi) :=
    mul_le_mul_of_nonneg_left (Psi_sharp_le_tangent hK' hs₀) (le_of_lt hβ_pos)
  have hY : θ.q * K + F θ.A K L ≤ q_max * K + F A_max K L := by
    have hq := mul_le_mul_of_nonneg_right θ.hq.2 (le_of_lt hK)
    have hF := F_mono_A θ.hA.2 hK hL.1
    linarith
  have hlamY : lam * (θ.q * K + F θ.A K L) ≤ lam * (q_max * K + F A_max K L) :=
    mul_le_mul_of_nonneg_left hY (le_of_lt hlam_pos)
  unfold u
  have hcancel : lam * c + θ.β * (slope * K' - 15 / (2 * s₀) - C0_psi) =
      lam * (θ.q * K + F θ.A K L) - θ.β * (15 / (2 * s₀) + C0_psi) := by
    dsimp [c, lam]; ring
  linarith

/-! ## 2. Cotas globales elementales sobre $F_{A_+}(K, L)$ -/

/-- Para todo $K > 0$ y $L \ge 0$, $F_{A_+}(K, L) \le A_+ (2 K) \sqrt{2 K}$. -/
lemma F_le_two_K {K L : ℝ} (hK : 0 < K) (hL : 0 ≤ L) :
    F A_max K L ≤ A_max * (2 * K) * Real.sqrt (2 * K) := by
  unfold F; dsimp only
  have hrat : 2 * K * L / (K + L) ≤ 2 * K := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hg_nn : 0 ≤ 2 * K * L / (K + L) := div_nonneg (by positivity) (by linarith)
  have hsq : Real.sqrt (2 * K * L / (K + L)) ≤ Real.sqrt (2 * K) := Real.sqrt_le_sqrt hrat
  have hprod : (2 * K * L / (K + L)) * Real.sqrt (2 * K * L / (K + L)) ≤
      (2 * K) * Real.sqrt (2 * K) :=
    mul_le_mul hrat hsq (Real.sqrt_nonneg _) (by positivity)
  have hA_nn : 0 ≤ A_max := by unfold A_max; norm_num
  have := mul_le_mul_of_nonneg_left hprod hA_nn
  linarith

/-- Para todo $K > 0$ y $L \in [0, 1]$, $F_{A_+}(K, L) \le 21242 / 10000$. -/
lemma F_le_const_ub {K L : ℝ} (hK : 0 < K) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    F A_max K L ≤ 21242 / 10000 := by
  have hF1 : F A_max K L ≤ F A_max K 1 := F_mono_L (by unfold A_max; norm_num) hK hL0 hL1
  unfold F at hF1; dsimp only at hF1
  have hrat : 2 * K * 1 / (K + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hg_nn : 0 ≤ 2 * K * 1 / (K + 1) := div_nonneg (by positivity) (by linarith)
  have hsq : Real.sqrt (2 * K * 1 / (K + 1)) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hrat
  have hprod : (2 * K * 1 / (K + 1)) * Real.sqrt (2 * K * 1 / (K + 1)) ≤ 2 * Real.sqrt 2 :=
    mul_le_mul hrat hsq (Real.sqrt_nonneg _) (by norm_num)
  have hrt2 : Real.sqrt 2 ≤ 141422 / 100000 := by
    have hsq2 : (Real.sqrt 2) ^ 2 ≤ (141422 / 100000 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  unfold F; unfold A_max at hF1 ⊢; dsimp only at *
  nlinarith

/-! ## 3. Cola pequeña ($0 < K \le 1/25000$) y cola grande ($K \ge 50$) del Lema 12 -/

/-- Lema 12 (Cola pequeña exacta): para todo $\theta \in \mathcal{P}$, todo $0 < K \le 1/25000$,
    todo $K' > 0$ y $L \in [0, 1)$ con $c > 0$, se cumple $u(\theta.\eta, c, L) + \theta.\beta \Psi^\#(K') \le \Psi^\#(K)$. -/
theorem lemma12_small_K (θ : Params) {K K' L : ℝ}
    (hK0 : 0 < K) (hK_le : K ≤ 1 / 25000) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  -- 1. Y = q K + F_A(K, L) ≤ 934/1000 * K
  have hrt2K : Real.sqrt (2 * K) ≤ 9 / 1000 := by
    have hsq : (Real.sqrt (2 * K)) ^ 2 ≤ (9 / 1000 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]; linarith
    nlinarith [Real.sqrt_nonneg (2 * K)]
  have hF_le : F θ.A K L ≤ (136 / 10000 : ℝ) * K := by
    have h1 := le_trans (F_mono_A θ.hA.2 hK0 hL.1) (F_le_two_K hK0 hL.1)
    unfold A_max at h1
    nlinarith
  have hY_le : θ.q * K + F θ.A K L ≤ (934 / 1000 : ℝ) * K := by
    have hq : θ.q * K ≤ q_max * K := mul_le_mul_of_nonneg_right θ.hq.2 (le_of_lt hK0)
    unfold q_max at hq
    linarith
  have hK'_lt : K' < (934 / 1000 : ℝ) * K := by linarith
  have hc_lt : θ.q * K + F θ.A K L - K' < (1 / 25000 : ℝ) := by linarith
  -- 2. Dominancia estricta de -5 β / √K' ≤ -5 / √K (pues β₋ / √0.934 > 1)
  have hsqrt_K' : Real.sqrt K' ≤ (9665 / 10000 : ℝ) * Real.sqrt K := by
    have h1 : Real.sqrt K' ≤ Real.sqrt ((934 / 1000 : ℝ) * K) := Real.sqrt_le_sqrt (le_of_lt hK'_lt)
    rw [Real.sqrt_mul (by norm_num)] at h1
    have h2 : Real.sqrt (934 / 1000 : ℝ) ≤ 9665 / 10000 := by
      have hsq : (Real.sqrt (934 / 1000 : ℝ)) ^ 2 ≤ (9665 / 10000 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg (934 / 1000 : ℝ)]
    have := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg K)
    linarith
  have hinv_dom : 5 / Real.sqrt K ≤ θ.β * (5 / Real.sqrt K') := by
    have hsK' : 0 < Real.sqrt K' := Real.sqrt_pos.mpr hK'
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
    have hdiv : 5 / ((9665 / 10000 : ℝ) * Real.sqrt K) ≤ 5 / Real.sqrt K' :=
      div_le_div_of_nonneg_left (by norm_num) hsK' hsqrt_K'
    have hβ_ge : (9699 / 10000 : ℝ) ≤ θ.β := θ.hβ.1
    have hmul : (9699 / 10000 : ℝ) * (5 / ((9665 / 10000 : ℝ) * Real.sqrt K)) ≤
        θ.β * (5 / Real.sqrt K') :=
      mul_le_mul hβ_ge hdiv (by positivity) (by linarith)
    have hcoef : 5 / Real.sqrt K ≤ (9699 / 10000 : ℝ) * (5 / ((9665 / 10000 : ℝ) * Real.sqrt K)) := by
      have hrew : (9699 / 10000 : ℝ) * (5 / ((9665 / 10000 : ℝ) * Real.sqrt K)) =
          (9699 / 9665 : ℝ) * (5 / Real.sqrt K) := by field_simp [ne_of_gt hsK]
      rw [hrew]
      have hpos : 0 ≤ 5 / Real.sqrt K := by positivity
      nlinarith
    linarith
  -- 3. Cota logarítmica c < 1/25000 < 2^(-14) ⇒ log c ≤ -14 * 0.69 = -9.66
  have hlogc : Real.log (θ.q * K + F θ.A K L - K') ≤ -966 / 100 := by
    have hle : θ.q * K + F θ.A K L - K' ≤ ((2 : ℝ) ^ 14)⁻¹ := by
      have : (1 / 25000 : ℝ) ≤ ((2 : ℝ) ^ 14)⁻¹ := by norm_num
      linarith
    have hlog := Real.log_le_log hc hle
    rw [Real.log_inv, Real.log_pow] at hlog
    have hlog2 := log_two_bounds.1
    push_cast at hlog
    linarith
  have hlogL : Real.log (1 - L) ≤ 0 := Real.log_nonpos (by linarith [hL.2]) (by linarith [hL.1])
  have hη_ge : (6999 / 10000 : ℝ) ≤ θ.η := θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
  have hu_le : u θ.η (θ.q * K + F θ.A K L - K') L ≤ (6999 / 10000 : ℝ) * (-966 / 100) := by
    unfold u
    have h1 : θ.η * Real.log (θ.q * K + F θ.A K L - K') ≤ (6999 / 10000 : ℝ) * (-966 / 100) := by
      calc θ.η * Real.log (θ.q * K + F θ.A K L - K')
          ≤ θ.η * (-966 / 100) := mul_le_mul_of_nonneg_left hlogc (by linarith)
        _ ≤ (6999 / 10000 : ℝ) * (-966 / 100) := mul_le_mul_of_nonpos_right hη_ge (by norm_num)
    have h2 : (1 - θ.η) * Real.log (1 - L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1mη_nn hlogL
    linarith
  -- 4. Cierre algebraico final
  rw [Psi_sharp_eq K', Psi_sharp_eq K]
  have hβ_le : θ.β ≤ 9701 / 10000 := θ.hβ.2
  have hβ_ge : 9699 / 10000 ≤ θ.β := θ.hβ.1
  have hC0_pos : 0 < C0_psi := by unfold C0_psi; norm_num
  have hβC0 : (9699 / 10000 : ℝ) * C0_psi ≤ θ.β * C0_psi :=
    mul_le_mul_of_nonneg_right hβ_ge (le_of_lt hC0_pos)
  have h04 : θ.β * ((4 / 10 : ℝ) * K') ≤ (4 / 10 : ℝ) * K := by nlinarith
  have hnum : (6999 / 10000 : ℝ) * (-966 / 100) + (1 - 9699 / 10000 : ℝ) * C0_psi ≤ 0 := by
    unfold C0_psi; norm_num
  have hdist : θ.β * ((4 / 10 : ℝ) * K' - 5 / Real.sqrt K' - C0_psi) =
      θ.β * ((4 / 10 : ℝ) * K') - θ.β * (5 / Real.sqrt K') - θ.β * C0_psi := by ring
  linarith

/-- Lema 12 (Cola grande exacta): para todo $\theta \in \mathcal{P}$, todo $K \ge 50$,
    todo $K' > 0$ y $L \in [0, 1)$ con $c > 0$, se cumple $u(\theta.\eta, c, L) + \theta.\beta \Psi^\#(K') \le \Psi^\#(K)$. -/
theorem lemma12_large_K (θ : Params) {K K' L : ℝ}
    (hK_ge : 50 ≤ K) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  have hK0 : 0 < K := by linarith
  have hβ_pos : 0 < θ.β := lt_of_lt_of_le (by unfold beta_min; norm_num) θ.hβ.1
  have hη_pos : 0 < θ.η := lt_of_lt_of_le (by unfold eta_min; norm_num) θ.hη.1
  have h1mη_nn : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
  -- Elegimos c₀ = θ.η / (0.4 * θ.β) < 2, luego log c₀ ≤ log 2 ≤ 0.70
  set lam := (4 / 10 : ℝ) * θ.β
  set c₀ := θ.η / lam
  have hlam_pos : 0 < lam := by dsimp [lam]; positivity
  have hc₀_pos : 0 < c₀ := div_pos hη_pos hlam_pos
  have hc₀_le2 : c₀ ≤ 2 := by
    dsimp [c₀, lam]
    rw [div_le_iff₀ (by positivity)]
    have h1 := θ.hη.2; have h2 := θ.hβ.1
    unfold eta_max at h1; unfold beta_min at h2
    linarith
  have hlogc₀ : Real.log c₀ ≤ 70 / 100 := by
    linarith [Real.log_le_log hc₀_pos hc₀_le2, log_two_bounds.2]
  -- Tangente de log c en c₀ y descarte de -5/√K' ≤ 0 y (1 - η) log(1 - L) ≤ 0
  set c := θ.q * K + F θ.A K L - K'
  have hlogc : Real.log c ≤ Real.log c₀ + c / c₀ - 1 := by
    have hconc := Real.log_le_sub_one_of_pos (div_pos hc hc₀_pos)
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hc₀_pos)] at hconc
    linarith
  have hηlog : θ.η * Real.log c ≤ θ.η * (70 / 100 - 1) + lam * c := by
    have h1 := mul_le_mul_of_nonneg_left hlogc (le_of_lt hη_pos)
    have h2 := mul_le_mul_of_nonneg_left hlogc₀ (le_of_lt hη_pos)
    have hrew : θ.η * (c / c₀) = lam * c := by
      dsimp [c₀]; field_simp [ne_of_gt hη_pos, ne_of_gt hlam_pos]
    linarith
  have hlogL : Real.log (1 - L) ≤ 0 := Real.log_nonpos (by linarith [hL.2]) (by linarith [hL.1])
  have hL_term : (1 - θ.η) * Real.log (1 - L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1mη_nn hlogL
  have hPsiK' : Psi_sharp K' ≤ (4 / 10 : ℝ) * K' - C0_psi := by
    rw [Psi_sharp_eq]
    have : 0 ≤ 5 / Real.sqrt K' := by positivity
    linarith
  have hβPsi : θ.β * Psi_sharp K' ≤ lam * K' - θ.β * C0_psi := by
    have := mul_le_mul_of_nonneg_left hPsiK' (le_of_lt hβ_pos)
    dsimp [lam]; linarith
  have hF_ub : F θ.A K L ≤ 21242 / 10000 :=
    le_trans (F_mono_A θ.hA.2 hK0 hL.1) (F_le_const_ub hK0 hL.1 (le_of_lt hL.2))
  have hY_ub : θ.q * K + F θ.A K L ≤ (9201 / 10000 : ℝ) * K + 21242 / 10000 := by
    have hq : θ.q * K ≤ q_max * K := mul_le_mul_of_nonneg_right θ.hq.2 (le_of_lt hK0)
    unfold q_max at hq; linarith
  have hlamY : lam * (θ.q * K + F θ.A K L) ≤ lam * ((9201 / 10000 : ℝ) * K + 21242 / 10000) :=
    mul_le_mul_of_nonneg_left hY_ub (le_of_lt hlam_pos)
  -- Cota de 5/√K ≤ 5/√50 ≤ 71/100 para K ≥ 50
  have h5sK : 5 / Real.sqrt K ≤ 71 / 100 := by
    have hsq : (705 / 100 : ℝ) ≤ Real.sqrt K := by
      have : (705 / 100 : ℝ) ^ 2 ≤ (Real.sqrt K) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hK0)]; linarith
      nlinarith [Real.sqrt_nonneg K]
    have hdiv : 5 / Real.sqrt K ≤ 5 / (705 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
    linarith
  -- Combinar cotas paramétricas
  have hβ_le : θ.β ≤ 9701 / 10000 := θ.hβ.2
  have hβ_ge : 9699 / 10000 ≤ θ.β := θ.hβ.1
  have hη_ge : 6999 / 10000 ≤ θ.η := θ.hη.1
  have hη_term : θ.η * (70 / 100 - 1) ≤ (6999 / 10000 : ℝ) * (70 / 100 - 1) :=
    mul_le_mul_of_nonpos_right hη_ge (by norm_num)
  have hlam_le : lam ≤ (4 / 10 : ℝ) * (9701 / 10000) := by dsimp [lam]; linarith
  have hlamK : lam * ((9201 / 10000 : ℝ) * K + 21242 / 10000) ≤
      (4 / 10 : ℝ) * (9701 / 10000) * ((9201 / 10000 : ℝ) * K + 21242 / 10000) :=
    mul_le_mul_of_nonneg_right hlam_le (by positivity)
  have hC0_pos : 0 < C0_psi := by unfold C0_psi; norm_num
  have hβC0 : (9699 / 10000 : ℝ) * C0_psi ≤ θ.β * C0_psi :=
    mul_le_mul_of_nonneg_right hβ_ge (le_of_lt hC0_pos)
  have hlin : (6999 / 10000 : ℝ) * (70 / 100 - 1) +
      (4 / 10 : ℝ) * (9701 / 10000) * ((9201 / 10000 : ℝ) * K + 21242 / 10000) -
      (9699 / 10000 : ℝ) * C0_psi ≤ (4 / 10 : ℝ) * K - 71 / 100 - C0_psi := by
    unfold C0_psi; linarith
  rw [Psi_sharp_eq K]
  unfold u
  have hcancel : lam * c + lam * K' = lam * (θ.q * K + F θ.A K L) := by dsimp [c]; ring
  linarith

/-! ## 4. Herramientas analíticas exactas para el núcleo compacto $[1/25000, 50]$ -/

/-- Convexidad elemental de $K \mapsto a K + 5 / \sqrt{K}$ en $[k_L, k_R]$ sin derivadas:
    su máximo sobre $[k_L, k_R]$ se alcanza en uno de los dos extremos $\{k_L, k_R\}$. -/
theorem convex_K_term_le_endpoints {a kL kR K : ℝ}
    (hkL : 0 < kL) (hK : K ∈ Icc kL kR) :
    a * K + 5 / Real.sqrt K ≤ max (a * kL + 5 / Real.sqrt kL) (a * kR + 5 / Real.sqrt kR) := by
  by_cases heq : kL = kR
  · have hKe : K = kL := le_antisymm (heq ▸ hK.2) hK.1
    rw [hKe]; exact le_max_left _ _
  · have hlt : kL < kR := lt_of_le_of_ne (le_trans hK.1 hK.2) heq
    set t := (K - kL) / (kR - kL)
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hK.1]) (by linarith)
    have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; linarith [hK.2]
    have hK_eq : K = (1 - t) * kL + t * kR := by
      dsimp [t]; field_simp [ne_of_gt (sub_pos.mpr hlt)]; ring
    -- Probamos 1/√K ≤ (1 - t)/√kL + t/√kR por convexidad de s ↦ 1/s y concavidad de √
    have hK_pos : 0 < K := lt_of_lt_of_le hkL hK.1
    have hkR_pos : 0 < kR := lt_trans hkL hlt
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK_pos
    have hskL : 0 < Real.sqrt kL := Real.sqrt_pos.mpr hkL
    have hskR : 0 < Real.sqrt kR := Real.sqrt_pos.mpr hkR_pos
    -- Primero: (1 - t) √kL + t √kR ≤ √K (elevando al cuadrado)
    have hsqrt_conc : (1 - t) * Real.sqrt kL + t * Real.sqrt kR ≤ Real.sqrt K := by
      have hsq_le : ((1 - t) * Real.sqrt kL + t * Real.sqrt kR) ^ 2 ≤ (Real.sqrt K) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hK_pos), hK_eq]
        have hdiff : 0 ≤ t * (1 - t) * (Real.sqrt kL - Real.sqrt kR) ^ 2 := by
          exact mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
        have h1 : (Real.sqrt kL) ^ 2 = kL := Real.sq_sqrt (le_of_lt hkL)
        have h2 : (Real.sqrt kR) ^ 2 = kR := Real.sq_sqrt (le_of_lt hkR_pos)
        nlinarith
      nlinarith [Real.sqrt_nonneg K]
    -- Segundo: 1 / ((1 - t) u + t v) ≤ (1 - t) / u + t / v para u, v > 0
    have hden_pos : 0 < (1 - t) * Real.sqrt kL + t * Real.sqrt kR := by
      have hle_s : Real.sqrt kL ≤ Real.sqrt kR := Real.sqrt_le_sqrt (le_of_lt hlt)
      have := mul_le_mul_of_nonneg_left hle_s ht0
      linarith
    have hinv_conv : 1 / ((1 - t) * Real.sqrt kL + t * Real.sqrt kR) ≤
        (1 - t) / Real.sqrt kL + t / Real.sqrt kR := by
      rw [div_le_iff₀ hden_pos]
      have hdiff : 0 ≤ t * (1 - t) * (Real.sqrt kL - Real.sqrt kR) ^ 2 /
          (Real.sqrt kL * Real.sqrt kR) :=
        div_nonneg (mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)) (by positivity)
      have hid : ((1 - t) / Real.sqrt kL + t / Real.sqrt kR) *
          ((1 - t) * Real.sqrt kL + t * Real.sqrt kR) - 1 =
          t * (1 - t) * (Real.sqrt kL - Real.sqrt kR) ^ 2 / (Real.sqrt kL * Real.sqrt kR) := by
        field_simp [ne_of_gt hskL, ne_of_gt hskR]; ring
      linarith
    have hinv_le : 1 / Real.sqrt K ≤ (1 - t) / Real.sqrt kL + t / Real.sqrt kR :=
      le_trans (div_le_div_of_nonneg_left (by norm_num) hden_pos hsqrt_conc) hinv_conv
    have hconv : a * K + 5 / Real.sqrt K ≤
        (1 - t) * (a * kL + 5 / Real.sqrt kL) + t * (a * kR + 5 / Real.sqrt kR) := by
      have hlin_a : a * K = (1 - t) * (a * kL) + t * (a * kR) := by rw [hK_eq]; ring
      have h5 : 5 / Real.sqrt K ≤ (1 - t) * (5 / Real.sqrt kL) + t * (5 / Real.sqrt kR) := by
        have hmul := mul_le_mul_of_nonneg_left hinv_le (by norm_num : (0 : ℝ) ≤ 5)
        have hrew1 : 5 * (1 / Real.sqrt K) = 5 / Real.sqrt K := by ring
        have hrew2 : 5 * ((1 - t) / Real.sqrt kL + t / Real.sqrt kR) =
            (1 - t) * (5 / Real.sqrt kL) + t * (5 / Real.sqrt kR) := by ring
        linarith
      linarith
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (a * kL + 5 / Real.sqrt kL)
      (a * kR + 5 / Real.sqrt kR)) (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (a * kL + 5 / Real.sqrt kL)
      (a * kR + 5 / Real.sqrt kR)) ht0
    linarith

/-- Simetría de la tangente global en $K$ (corolario directo de `F_le_tangent` en 3 líneas):
    para todo $A \ge 0$, $L > 0$, $k_0 \ge L/2$ y $K \ge 0$,
    $F(A, K, L) \le F(A, k_0, L) + F_K(A, k_0, L) (K - k_0)$. -/
theorem F_le_tangent_K {A L k₀ K : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hk₀ : L / 2 ≤ k₀) (hK : 0 ≤ K) :
    F A K L ≤ F A k₀ L + FK A L k₀ * (K - k₀) := by
  have hsym : ∀ x y, F A x y = F A y x := by
    intro x y; unfold F; dsimp only
    have : 2 * x * y / (x + y) = 2 * y * x / (y + x) := by ring_nf
    rw [this]
  have hFK_eq : FK A L k₀ = t_gen A k₀ L := by
    unfold FK t_gen g
    have : 2 * k₀ * L / (k₀ + L) = 2 * L * k₀ / (L + k₀) := by ring_nf
    have hadd : (k₀ + L) ^ 2 = (L + k₀) ^ 2 := by ring
    rw [this, hadd]
  rw [hsym K L, hsym k₀ L, hFK_eq]
  exact tangent_dominance hA hL hk₀ hK

/-- Eliminación cerrada de $L \in [0, 1)$ para cualquier pieza lineal $\mu L + (1 - \eta)\log(1 - L)$:
    cuando $\mu > 0$ y $1 - \eta > 0$, para todo $L \in [0, 1)$:
    $\mu L + (1 - \eta)\log(1 - L) \le \mu - (1 - \eta) + (1 - \eta)\log((1 - \eta) / \mu)$. -/
theorem lin_log_le_opt {μ one_m_η L : ℝ} (hμ : 0 < μ) (hη : 0 < one_m_η) (hL1 : L < 1) :
    μ * L + one_m_η * Real.log (1 - L) ≤
      μ - one_m_η + one_m_η * Real.log (one_m_η / μ) := by
  have h1mL : 0 < 1 - L := by linarith
  have hratio : 0 < μ * (1 - L) / one_m_η := by positivity
  have hconc := Real.log_le_sub_one_of_pos hratio
  have hlog_eq : Real.log (μ * (1 - L) / one_m_η) =
      Real.log (1 - L) - Real.log (one_m_η / μ) := by
    rw [Real.log_div (ne_of_gt (mul_pos hμ h1mL)) (ne_of_gt hη),
        Real.log_mul (ne_of_gt hμ) (ne_of_gt h1mL),
        Real.log_div (ne_of_gt hη) (ne_of_gt hμ)]
    ring
  rw [hlog_eq] at hconc
  have hmul := mul_le_mul_of_nonneg_left hconc (le_of_lt hη)
  have hrew : one_m_η * (μ * (1 - L) / one_m_η - 1) = μ * (1 - L) - one_m_η := by
    field_simp [ne_of_gt hη]
  linarith

/-! ## 5. Ensamblado global del Lema 12 y cota de valor de continuación -/

/-- Ensamblado global del Lema 12:
    combinando `lemma12_small_K` ($K \le 1/25000$), `lemma12_large_K` ($K \ge 50$) y la
    verificación en el compacto intermedio $[1/25000, 50]$, $\Psi^\#$ es una super-barrera
    global de Bellman en todo $(0, \infty)$ para todo $\theta \in \mathcal{P}$. -/
theorem lemma12_global_super_barrier
    (hmid : ∀ (θ : Params) (K K' L : ℝ),
      1 / 25000 ≤ K ∧ K ≤ 50 → 0 < K' → 0 ≤ L ∧ L < 1 →
      0 < θ.q * K + F θ.A K L - K' →
      u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K) :
    ∀ (θ : Params) (K K' L : ℝ),
      0 < K → 0 < K' → 0 ≤ L ∧ L < 1 →
      0 < θ.q * K + F θ.A K L - K' →
      u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  intro θ K K' L hK hK' hL hc
  by_cases hsm : K ≤ 1 / 25000
  · exact lemma12_small_K θ hK hsm hK' hL hc
  · by_cases hlg : 50 ≤ K
    · exact lemma12_large_K θ hlg hK' hL hc
    · exact hmid θ K K' L ⟨by linarith, by linarith⟩ hK' hL hc

/-- Consecuencia telescópica del Lema 12: bajo la super-barrera global $\Psi^\#$, toda
    trayectoria factible de $T$ pasos satisface $\sum \beta^t u_t + \beta^T \Psi^\#(x_T) \le \Psi^\#(x_0)$. -/
theorem lemma12_value_le_Psi_sharp (θ : Params) (T : ℕ) (x L : ℕ → ℝ)
    (hglobal : ∀ (K K' Lv : ℝ), 0 < K → 0 < K' → 0 ≤ Lv ∧ Lv < 1 →
      0 < θ.q * K + F θ.A K Lv - K' →
      u θ.η (θ.q * K + F θ.A K Lv - K') Lv + θ.β * Psi_sharp K' ≤ Psi_sharp K)
    (hx : ∀ t ≤ T, 0 < x t)
    (hL : ∀ t < T, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < T, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) :
    (∑ t ∈ range T, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ T * Psi_sharp (x T) ≤ Psi_sharp (x 0) := by
  have hβ0 : 0 ≤ θ.β := le_trans (by unfold beta_min; norm_num) θ.hβ.1
  have htel := telescoping_bellman hβ0 Psi_sharp
    (fun t => u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) x T
    (fun t ht => hglobal (x t) (x (t + 1)) (L t) (hx t (le_of_lt ht)) (hx (t + 1) ht)
      (hL t ht) (hc t ht))
  linarith

end

end MVS.Lemma12
