import MVS.Theorem2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Teorema de Segundo Orden (`MVS.Theorem2SecondOrder`): Elevación de la Observación 1 (Parte 1) y Cota Superior de la Parte 2

Formalización completa y sin `sorry` de las **3 piezas** que elevan la Parte 1 de la
Observación 1 a Teorema riguroso para todo `p : CESParams` ($\beta \theta > 1$, sin
requerir $\beta \lambda_K \ge 1$), más la **cota superior completa de la Parte 2**
obtenida directamente del término $t = 0$ de la Pieza 3 y la envolvente de Milgrom--Segal:

1. **Pieza 1 (Exponente exacto $1 - \kappa$):**
   - Reescalado exacto $y_t = \alpha^{1/r} k_t \implies y_{t+1} = y_t^\theta$ (`piece1_exact_rescaling`),
   - Techo macroscópico CES $F_A(K, L) \le A \cdot c_K c_w^{-\theta/d}$ (`F_ces_le_macro_cap`),
   - Partición de la suma descontada en $t_0 = \lfloor \frac{\log\log A}{\log \theta} \rfloor$
     dando $O((\log A)^{1-\kappa})$ (`piece1_sum_split_upper`).
2. **Pieza 2 (Cota superior rigurosa de $\Delta_k(A)$ con $\lambda_K$ exacto):**
   - Convexidad cuadrática $g(k_* + x) \ge (\lambda_K - 1) x + m x^2$ (`g_net_convex_lower`),
   - Penalización CES $O(A^{-d/r})$ (`f_norm_ces_penalty`),
   - Política explícita $c_t^*$ válida incluso si $\beta \lambda_K < 1$ (`piece2_explicit_policy`),
   - Cota superior $\Delta_k(A) \le C_+ \left(\frac{\log\log A}{(\log A)^{1-\kappa}}\right)^{1/\mu_K}$ (`piece2_delta_k_upper`).
3. **Pieza 3 (Cota inferior rigurosa de $\Delta_k(A)$ vía $\phi(x) = x - C x^2$):**
   - Concavidad de $g''$ dando $g(k_* + x) \le (\lambda_K - 1) x + M x^2$ para todo $x \ge 0$ (`g_net_quadratic_upper`),
   - Cancelación algebraica exacta $\phi(\lambda_K x + M x^2) \le \lambda_K \phi(x)$ (`phi_sublinear_exact`),
   - Presupuesto telescópico $\frac{1}{2}\sum_{t=0}^{T-1} c_t / \lambda_K^{t+1} \le \Delta_k - \phi(\epsilon)/\lambda_K^T$ (`piece3_telescoping_budget`),
   - Cota del consumo inicial $c_0 \le 2 \lambda_K \Delta_k$ (`piece3_c0_bound`),
   - Cota de utilidad logarítmica vía `Real.log_le_sub_one_of_pos` (`piece3_log_sum_upper`),
   - Cota inferior $\Delta_k(A) \ge C_- \left(\frac{\log\log A}{(\log A)^{1-\kappa}}\right)^{1/\mu_K}$ (`piece3_delta_k_lower`).
4. **Parte 2 (Cota superior de la brecha relativa por Milgrom--Segal):**
   - $(k_A - k_A^{\text{fix}}) / k_A \le \frac{8}{\eta k_*} \Delta_k(A) \Delta W_A^+$ (`part2_free_relative_gap_bound`),
   - Tasa $\beta^{T + J} = O(\frac{\log\log A}{\log A})$ y brecha $O\!\left(\frac{(\log\log A)^{1+1/\mu_K}}{(\log A)^{1+(1-\kappa)/\mu_K}}\right)$ (`part2_delta_W_plus_rate`).
-/

open Finset Real Set MVS.Theorem2

namespace MVS.Theorem2.CESParams

variable (p : CESParams)

/-! ## 0. Constantes exactas de segundo orden -/

/-- Valor propio de expansión linealizada alrededor de $k_*$: $\lambda_K = q + \theta \delta = 1 + r \delta > 1$. -/
def lamK : ℝ := p.q + p.θ * p.δ

/-- Exponente exacto de la Fase II: $\kappa = |\log \beta| / \log \theta \in (0, 1)$. -/
noncomputable def κ : ℝ := (-Real.log p.β) / Real.log p.θ

/-- Exponente exacto de la Fase I linealizada: $\mu_K = |\log \beta| / \log \lambda_K > 0$. -/
noncomputable def μ_K : ℝ := (-Real.log p.β) / Real.log p.lamK

/-- Producto neto asintótico $g(k) = c_K k^\theta - \delta k$. -/
noncomputable def g_net (k : ℝ) : ℝ := p.cK * k ^ p.θ - p.δ * k

/-- Límite estacionario interior del trabajo $L_{\text{ss}} = \frac{\theta \eta}{\theta \eta + (1 - \eta)}$. -/
noncomputable def L_ss : ℝ := p.θ * p.η / (p.θ * p.η + (1 - p.η))

lemma lamK_eq : p.lamK = 1 + p.r * p.δ := by
  unfold lamK CESParams.q CESParams.θ; ring

lemma hlamK_gt1 : 1 < p.lamK := by
  rw [p.lamK_eq]; nlinarith [p.hr0, p.hδ0]

lemma hlamK_pos : 0 < p.lamK := by linarith [p.hlamK_gt1]

lemma hlog_β_neg : Real.log p.β < 0 := Real.log_neg p.hβ0 p.hβ1
lemma hlog_θ_pos : 0 < Real.log p.θ := Real.log_pos p.hθ_gt1
lemma hlog_lamK_pos : 0 < Real.log p.lamK := Real.log_pos p.hlamK_gt1

lemma hκ_pos : 0 < p.κ := div_pos (neg_pos.mpr p.hlog_β_neg) p.hlog_θ_pos

lemma hκ_lt1 : p.κ < 1 := by
  unfold κ
  rw [div_lt_one p.hlog_θ_pos]
  have hprod : 0 < Real.log (p.β * p.θ) := Real.log_pos (by unfold CESParams.θ; exact p.hβθ)
  rw [Real.log_mul (ne_of_gt p.hβ0) (ne_of_gt p.hθ_pos)] at hprod
  linarith

lemma hμ_K_pos : 0 < p.μ_K := div_pos (neg_pos.mpr p.hlog_β_neg) p.hlog_lamK_pos

lemma g_net_k_star : p.g_net p.k_star = 0 := by
  unfold g_net CESParams.k_star CESParams.θ
  have hpos : 0 < p.δ / p.cK := div_pos p.hδ0 p.hcK_pos
  have hr : ((p.δ / p.cK) ^ (1 / p.r)) ^ p.r = p.δ / p.cK := by
    rw [← Real.rpow_mul (le_of_lt hpos), one_div_mul_cancel (ne_of_gt p.hr0), Real.rpow_one]
  have hpow : ((p.δ / p.cK) ^ (1 / p.r)) ^ (1 + p.r) =
      ((p.δ / p.cK) ^ (1 / p.r)) * ((p.δ / p.cK) ^ (1 / p.r)) ^ p.r := by
    rw [Real.rpow_add (Real.rpow_pos_of_pos hpos _), Real.rpow_one]
  rw [hpow, hr]
  field_simp [ne_of_gt p.hcK_pos]
  ring

/-- Identidad de cambio de base: $\beta^T = (\lambda_K^T)^{-\mu_K}$ para todo $T \in \mathbb{N}$. -/
lemma beta_pow_eq_rpow_muK (T : ℕ) :
    p.β ^ T = (p.lamK ^ T) ^ (-p.μ_K) := by
  have hL : p.β ^ T = Real.exp ((T : ℝ) * Real.log p.β) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos p.hβ0]; ring_nf
  have hR : (p.lamK ^ T) ^ (-p.μ_K) = Real.exp ((T : ℝ) * Real.log p.lamK * (-p.μ_K)) := by
    rw [Real.rpow_def_of_pos (pow_pos p.hlamK_pos T), Real.log_pow]
  rw [hL, hR]; congr 1
  unfold μ_K
  field_simp [ne_of_gt p.hlog_lamK_pos]

/-- Identidad de cambio de base para cualquier real $u > 0$: $\beta^{\log u / \log \lambda_K} = u^{-\mu_K}$. -/
lemma rpow_muK_eq_exp {u : ℝ} (hu : 0 < u) :
    u ^ (-p.μ_K) = Real.exp ((Real.log u / Real.log p.lamK) * Real.log p.β) := by
  rw [Real.rpow_def_of_pos hu]
  congr 1; unfold μ_K; field_simp [ne_of_gt p.hlog_lamK_pos]

lemma geom_sum_eq (r : ℝ) (n : ℕ) :
    (∑ t ∈ range n, r ^ t) * (1 - r) = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

lemma telescope_sum (f : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ range n, (f t - f (t + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- Cota elemental de la serie aritmético-geométrica: $\sum_{t < T} t \beta^t \le \frac{\beta}{(1 - \beta)^2}$. -/
lemma sum_mul_beta_pow_le (T : ℕ) :
    ∑ t ∈ range T, (t : ℝ) * p.β ^ t ≤ p.β / (1 - p.β) ^ 2 := by
  have h1β : 0 < 1 - p.β := by linarith [p.hβ1]
  have hid : (1 - p.β) ^ 2 * (∑ t ∈ range T, (t : ℝ) * p.β ^ t) =
      p.β - (T : ℝ) * p.β ^ T + ((T : ℝ) - 1) * p.β ^ (T + 1) := by
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast; rw [pow_succ, pow_succ]; ring
  have hrem : 0 ≤ (T : ℝ) * p.β ^ T - ((T : ℝ) - 1) * p.β ^ (T + 1) := by
    have hrew : (T : ℝ) * p.β ^ T - ((T : ℝ) - 1) * p.β ^ (T + 1) =
        ((T : ℝ) * (1 - p.β) + p.β) * p.β ^ T := by rw [pow_succ]; ring
    rw [hrew]
    have hβ0 : 0 ≤ p.β := le_of_lt p.hβ0
    positivity
  rw [le_div_iff₀ (sq_pos_of_pos h1β)]
  linarith

/-! ## 1. Pieza 1: Exponente exacto $1 - \kappa$ en $v_A(k_* + \epsilon) = \Theta((\log A)^{1-\kappa})$ -/

/-- Reescalado exacto $y_t = \alpha^{1/r} k_t$: si $k_{t+1} \ge \alpha k_t^\theta$, entonces
    $y_j \ge y_0^{\theta^j}$ con el $\theta$ exacto (sin pérdida $\tilde{\theta} < \theta$). -/
theorem piece1_exact_rescaling {α : ℝ} (hα : 0 < α) (k : ℕ → ℝ)
    (hk0 : 0 < k 0) (hstep : ∀ j, α * (k j) ^ p.θ ≤ k (j + 1)) :
    ∀ j : ℕ, (α ^ (1 / p.r) * k 0) ^ (p.θ ^ j) ≤ α ^ (1 / p.r) * k j := by
  have hαr_pos : 0 < α ^ (1 / p.r) := Real.rpow_pos_of_pos hα _
  have hk_pos : ∀ j, 0 < k j := by
    intro j
    induction j with
    | zero => exact hk0
    | succ n ih =>
      exact lt_of_lt_of_le (mul_pos hα (Real.rpow_pos_of_pos ih _)) (hstep n)
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
    have hy0_pos : 0 < α ^ (1 / p.r) * k 0 := mul_pos hαr_pos hk0
    have hexp_eq : α ^ (1 / p.r) * α = (α ^ (1 / p.r)) ^ p.θ := by
      rw [← Real.rpow_mul (le_of_lt hα)]
      have h1 : α ^ (1 / p.r) * α = α ^ (1 / p.r + 1) := by
        rw [Real.rpow_add hα, Real.rpow_one]
      rw [h1]; congr 1
      unfold CESParams.θ; field_simp [ne_of_gt p.hr0]
    calc (α ^ (1 / p.r) * k 0) ^ (p.θ ^ (n + 1))
        = (α ^ (1 / p.r) * k 0) ^ (p.θ ^ n * p.θ) := by rw [pow_succ]
      _ = ((α ^ (1 / p.r) * k 0) ^ (p.θ ^ n)) ^ p.θ := Real.rpow_mul (le_of_lt hy0_pos) _ _
      _ ≤ (α ^ (1 / p.r) * k n) ^ p.θ :=
          Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hy0_pos _)) ih (le_of_lt p.hθ_pos)
      _ = (α ^ (1 / p.r)) ^ p.θ * (k n) ^ p.θ :=
          Real.mul_rpow (le_of_lt hαr_pos) (le_of_lt (hk_pos n))
      _ = α ^ (1 / p.r) * (α * (k n) ^ p.θ) := by rw [← hexp_eq]; ring
      _ ≤ α ^ (1 / p.r) * k (n + 1) := mul_le_mul_of_nonneg_left (hstep n) (le_of_lt hαr_pos)

/-- Cota inferior de la Fase II/III con el exponente **exacto** $1 - \kappa$:
    aplica `phase2_superexp` y `discount_times_logA_lower` con $\tilde{\theta} = \theta$. -/
theorem piece1_lower_exact {K_esc : ℝ} (hK : 0 < K_esc) :
    ∃ A₁ ≥ Real.exp 2, ∃ C_J : ℝ, ∀ A ≥ A₁,
      ∃ J : ℕ, A ^ (1 / p.r) * K_esc ≤ (2 : ℝ) ^ (p.θ ^ J) ∧
        (J : ℝ) ≤ Real.log (Real.log A) / Real.log p.θ + C_J ∧
        p.β ^ C_J * (Real.log A) ^ (1 - p.κ) ≤ p.β ^ J * Real.log A := by
  obtain ⟨C_J, A_min, _, hph2⟩ := p.phase2_step_bound p.hθ_gt1 hK
  refine ⟨max (Real.exp 2) A_min, le_max_left _ _, C_J, fun A hA => ?_⟩
  obtain ⟨J, hreach, hJ_le⟩ := hph2 A (le_trans (le_max_right _ _) hA)
  have hA_gt_e : Real.exp 1 < A := by
    have h1 : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    have h2 : Real.exp 2 ≤ A := le_trans (le_max_left _ _) hA
    linarith
  have hdisc := p.discount_times_logA_lower p.hθ_gt1 (by unfold CESParams.θ; exact p.hβθ) hA_gt_e hJ_le
  exact ⟨J, hreach, hJ_le, hdisc.2⟩

/-- Techo macroscópico uniforme de la producción CES:
    para todo $A > 0$, $K > 0$ y $L \in (0, 1]$, $F_A(K, L) \le A \cdot c_K c_w^{-\theta/d}$. -/
theorem F_ces_le_macro_cap {A K L : ℝ} (hA : 0 < A) (hK : 0 < K) (hL0 : 0 < L) (hL1 : L ≤ 1) :
    p.F_ces A K L ≤ A * (p.cK * p.cw ^ (-p.θ / p.d)) := by
  unfold CESParams.F_ces
  have hKL_pos : 0 < K / L := div_pos hK hL0
  have hterm_pos : 0 < p.cw * (K / L) ^ p.d := mul_pos p.hcw_pos (Real.rpow_pos_of_pos hKL_pos _)
  have hneg_exp : -p.θ / p.d ≤ 0 := le_of_lt (div_neg_of_neg_of_pos (neg_lt_zero.mpr p.hθ_pos) p.hd)
  have hpow_le : (1 + p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d) ≤
      (p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d) :=
    Real.rpow_le_rpow_of_nonpos hterm_pos (by linarith) hneg_exp
  have hsimp : K ^ p.θ * (p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d) = p.cw ^ (-p.θ / p.d) * L ^ p.θ := by
    rw [Real.mul_rpow (le_of_lt p.hcw_pos) (le_of_lt (Real.rpow_pos_of_pos hKL_pos _)),
        ← Real.rpow_mul (le_of_lt hKL_pos)]
    have hexp : p.d * (-p.θ / p.d) = -p.θ := by field_simp [ne_of_gt p.hd]
    rw [hexp, Real.div_rpow (le_of_lt hK) (le_of_lt hL0),
        Real.rpow_neg (le_of_lt hK), Real.rpow_neg (le_of_lt hL0)]
    have hKθ : K ^ p.θ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hK _)
    have hLθ : L ^ p.θ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL0 _)
    field_simp [hKθ, hLθ]
  have hLθ_le1 : L ^ p.θ ≤ 1 := Real.rpow_le_one (le_of_lt hL0) hL1 (le_of_lt p.hθ_pos)
  have h1 : A * p.cK * K ^ p.θ * (1 + p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d) ≤
      A * p.cK * (K ^ p.θ * (p.cw * (K / L) ^ p.d) ^ (-p.θ / p.d)) := by
    have hcoef : 0 ≤ A * p.cK * K ^ p.θ :=
      mul_nonneg (mul_nonneg (le_of_lt hA) (le_of_lt p.hcK_pos)) (le_of_lt (Real.rpow_pos_of_pos hK _))
    have hmul := mul_le_mul_of_nonneg_left hpow_le hcoef
    linarith
  rw [hsimp] at h1
  have h2 : A * p.cK * (p.cw ^ (-p.θ / p.d) * L ^ p.θ) ≤ A * (p.cK * p.cw ^ (-p.θ / p.d)) := by
    have hnn : 0 ≤ A * p.cK * p.cw ^ (-p.θ / p.d) :=
      mul_nonneg (mul_nonneg (le_of_lt hA) (le_of_lt p.hcK_pos))
        (le_of_lt (Real.rpow_pos_of_pos p.hcw_pos _))
    have := mul_le_mul_of_nonneg_left hLθ_le1 hnn
    linarith
  exact le_trans h1 h2

/-- Cota superior superexponencial de trayectorias factibles:
    si $k_{t+1} \le B \max(1, k_t)^\theta$ ($B \ge 1$), entonces
    $B^{1/r} \max(1, k_t) \le (B^{1/r} \max(1, k_0))^{\theta^t}$. -/
theorem piece1_traj_upper_exp {B : ℝ} (hB : 1 ≤ B) (k : ℕ → ℝ)
    (hstep : ∀ t, k (t + 1) ≤ B * (max 1 (k t)) ^ p.θ) :
    ∀ t : ℕ, B ^ (1 / p.r) * max 1 (k t) ≤ (B ^ (1 / p.r) * max 1 (k 0)) ^ (p.θ ^ t) := by
  have hB_pos : 0 < B := by linarith
  have hBr_pos : 0 < B ^ (1 / p.r) := Real.rpow_pos_of_pos hB_pos _
  have hBr_ge1 : 1 ≤ B ^ (1 / p.r) := Real.one_le_rpow hB (le_of_lt (div_pos one_pos p.hr0))
  have hz0_ge1 : 1 ≤ B ^ (1 / p.r) * max 1 (k 0) :=
    one_le_mul_of_one_le_of_one_le hBr_ge1 (le_max_left 1 (k 0))
  have hexp_eq : B ^ (1 / p.r) * B = (B ^ (1 / p.r)) ^ p.θ := by
    rw [← Real.rpow_mul (le_of_lt hB_pos)]
    have h1 : B ^ (1 / p.r) * B = B ^ (1 / p.r + 1) := by
      rw [Real.rpow_add hB_pos, Real.rpow_one]
    rw [h1]; congr 1
    unfold CESParams.θ; field_simp [ne_of_gt p.hr0]
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    have hm_ge1 : 1 ≤ max 1 (k n) := le_max_left 1 (k n)
    have hm_pos : 0 < max 1 (k n) := by linarith
    have hstep_max : max 1 (k (n + 1)) ≤ B * (max 1 (k n)) ^ p.θ := by
      apply max_le
      · have h1 : 1 ≤ (max 1 (k n)) ^ p.θ := Real.one_le_rpow hm_ge1 (le_of_lt p.hθ_pos)
        nlinarith
      · exact hstep n
    calc B ^ (1 / p.r) * max 1 (k (n + 1))
        ≤ B ^ (1 / p.r) * (B * (max 1 (k n)) ^ p.θ) :=
          mul_le_mul_of_nonneg_left hstep_max (le_of_lt hBr_pos)
      _ = (B ^ (1 / p.r)) ^ p.θ * (max 1 (k n)) ^ p.θ := by rw [← hexp_eq]; ring
      _ = (B ^ (1 / p.r) * max 1 (k n)) ^ p.θ :=
          (Real.mul_rpow (le_of_lt hBr_pos) (le_of_lt hm_pos)).symm
      _ ≤ ((B ^ (1 / p.r) * max 1 (k 0)) ^ (p.θ ^ n)) ^ p.θ :=
          Real.rpow_le_rpow (by positivity) ih (le_of_lt p.hθ_pos)
      _ = (B ^ (1 / p.r) * max 1 (k 0)) ^ (p.θ ^ (n + 1)) := by
          rw [← Real.rpow_mul (by linarith), pow_succ]

/-- Cota superior de la Pieza 1 con el exponente **exacto** $1 - \kappa$:
    partiendo la suma descontada en $t_0 = \lfloor \frac{\log\log A}{\log \theta} \rfloor$,
    toda sucesión con $u_t \le \min\{C_4 \theta^t, C_5 \log A\}$ satisface
    $\sum_{t < N} \beta^t u_t \le C_{\text{hi}} (\log A)^{1 - \kappa}$ uniformemente en $N$. -/
theorem piece1_sum_split_upper {C₄ C₅ A : ℝ} (hC₄ : 0 < C₄) (hC₅ : 0 < C₅)
    (hA : Real.exp p.θ ≤ A) (u : ℕ → ℝ)
    (hu1 : ∀ t, u t ≤ C₄ * p.θ ^ t) (hu2 : ∀ t, u t ≤ C₅ * Real.log A) (N : ℕ) :
    ∑ t ∈ range N, p.β ^ t * u t ≤
      (C₄ * (p.β * p.θ) / (p.β * p.θ - 1) + C₅ / (1 - p.β)) * (Real.log A) ^ (1 - p.κ) := by
  have hlogA_geθ : p.θ ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos p.θ) hA
    rwa [Real.log_exp] at this
  have hlogA_gt1 : 1 < Real.log A := lt_of_lt_of_le p.hθ_gt1 hlogA_geθ
  have hlogA_pos : 0 < Real.log A := by linarith
  have hloglog_nn : 0 ≤ Real.log (Real.log A) := Real.log_nonneg (le_of_lt hlogA_gt1)
  have hβθ_gt1 : 1 < p.β * p.θ := by unfold CESParams.θ; exact p.hβθ
  have h1β_pos : 0 < 1 - p.β := by linarith [p.hβ1]
  set t₀ : ℕ := Nat.floor (Real.log (Real.log A) / Real.log p.θ)
  have ht₀_le : (t₀ : ℝ) ≤ Real.log (Real.log A) / Real.log p.θ :=
    Nat.floor_le (div_nonneg hloglog_nn (le_of_lt p.hlog_θ_pos))
  have ht₀_gt : Real.log (Real.log A) / Real.log p.θ < (t₀ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  -- Propiedades exactas de θ^t₀ y β^(t₀+1) en términos de (log A)^(1 - κ)
  have hβθ_pow : (p.β * p.θ) ^ t₀ ≤ (Real.log A) ^ (1 - p.κ) := by
    have hL : (p.β * p.θ) ^ t₀ = Real.exp ((t₀ : ℝ) * Real.log (p.β * p.θ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]; ring_nf
    have hR : (Real.log A) ^ (1 - p.κ) = Real.exp ((1 - p.κ) * Real.log (Real.log A)) := by
      rw [Real.rpow_def_of_pos hlogA_pos]; ring_nf
    rw [hL, hR]; apply Real.exp_le_exp.mpr
    have hlog_prod : 0 < Real.log (p.β * p.θ) := Real.log_pos hβθ_gt1
    have hmul := mul_le_mul_of_nonneg_right ht₀_le (le_of_lt hlog_prod)
    have hrew : (Real.log (Real.log A) / Real.log p.θ) * Real.log (p.β * p.θ) =
        (1 - p.κ) * Real.log (Real.log A) := by
      rw [Real.log_mul (ne_of_gt p.hβ0) (ne_of_gt p.hθ_pos)]
      unfold κ; field_simp [ne_of_gt p.hlog_θ_pos]; ring
    linarith
  have hβ_pow : p.β ^ (t₀ + 1) * Real.log A ≤ (Real.log A) ^ (1 - p.κ) := by
    have hL : p.β ^ (t₀ + 1) * Real.log A =
        Real.exp (((t₀ : ℝ) + 1) * Real.log p.β + Real.log (Real.log A)) := by
      rw [Real.exp_add, Real.exp_log hlogA_pos, ← Real.rpow_natCast, Real.rpow_def_of_pos p.hβ0]
      push_cast; ring_nf
    have hR : (Real.log A) ^ (1 - p.κ) = Real.exp ((1 - p.κ) * Real.log (Real.log A)) := by
      rw [Real.rpow_def_of_pos hlogA_pos]; ring_nf
    rw [hL, hR]; apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_right (le_of_lt ht₀_gt) (le_of_lt p.hlog_β_neg)
    have hrew : (Real.log (Real.log A) / Real.log p.θ) * Real.log p.β + Real.log (Real.log A) =
        (1 - p.κ) * Real.log (Real.log A) := by
      unfold κ; field_simp [ne_of_gt p.hlog_θ_pos]; ring
    linarith
  -- Partimos range N en {t < N | t ≤ t₀} y {t < N | t₀ < t}
  have hsplit : ∑ t ∈ range N, p.β ^ t * u t ≤
      (∑ t ∈ range (t₀ + 1), C₄ * (p.β * p.θ) ^ t) +
      (∑ t ∈ range N, if t₀ + 1 ≤ t then C₅ * Real.log A * p.β ^ t else 0) := by
    have hpart : ∑ t ∈ range N, p.β ^ t * u t =
        (∑ t ∈ range N, if t < t₀ + 1 then p.β ^ t * u t else 0) +
        (∑ t ∈ range N, if t₀ + 1 ≤ t then p.β ^ t * u t else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : t < t₀ + 1
      · have hnot : ¬ t₀ + 1 ≤ t := by omega
        simp [h, hnot]
      · have hge : t₀ + 1 ≤ t := by omega
        simp [h, hge]
    rw [hpart]
    apply add_le_add
    · -- Primera parte: acotada por la suma sobre range (t₀ + 1)
      have h1 : ∑ t ∈ range N, (if t < t₀ + 1 then p.β ^ t * u t else 0) ≤
          ∑ t ∈ range N, (if t < t₀ + 1 then C₄ * (p.β * p.θ) ^ t else 0) := by
        refine Finset.sum_le_sum fun t _ => ?_
        split_ifs
        · have hmul := mul_le_mul_of_nonneg_left (hu1 t) (pow_nonneg (le_of_lt p.hβ0) t)
          rw [mul_pow]; linarith
        · exact le_rfl
      have h2 : ∑ t ∈ range N, (if t < t₀ + 1 then C₄ * (p.β * p.θ) ^ t else 0) ≤
          ∑ t ∈ range (t₀ + 1), C₄ * (p.β * p.θ) ^ t := by
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro t ht; simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢; exact ht.2
        · intro t _ _; positivity
      exact le_trans h1 h2
    · -- Segunda parte: u t ≤ C₅ * log A
      refine Finset.sum_le_sum fun t _ => ?_
      split_ifs
      · have hmul := mul_le_mul_of_nonneg_left (hu2 t) (pow_nonneg (le_of_lt p.hβ0) t)
        linarith
      · exact le_rfl
  -- Acotar ambas sumas geométricas
  have hgeom1 : ∑ t ∈ range (t₀ + 1), C₄ * (p.β * p.θ) ^ t ≤
      (C₄ * (p.β * p.θ) / (p.β * p.θ - 1)) * (Real.log A) ^ (1 - p.κ) := by
    rw [← Finset.mul_sum]
    have hsum : (∑ t ∈ range (t₀ + 1), (p.β * p.θ) ^ t) * (p.β * p.θ - 1) =
        (p.β * p.θ) ^ (t₀ + 1) - 1 := by
      induction (t₀ + 1) with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
    have hsum_le : ∑ t ∈ range (t₀ + 1), (p.β * p.θ) ^ t ≤ (p.β * p.θ) ^ (t₀ + 1) / (p.β * p.θ - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hpow_le : (p.β * p.θ) ^ (t₀ + 1) ≤ (p.β * p.θ) * (Real.log A) ^ (1 - p.κ) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left hβθ_pow (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hsum_le (le_of_lt hC₄)
    have h2 : C₄ * ((p.β * p.θ) ^ (t₀ + 1) / (p.β * p.θ - 1)) ≤
        C₄ * ((p.β * p.θ) * (Real.log A) ^ (1 - p.κ) / (p.β * p.θ - 1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow_le (by linarith)) (le_of_lt hC₄)
    have hrew : C₄ * ((p.β * p.θ) * (Real.log A) ^ (1 - p.κ) / (p.β * p.θ - 1)) =
        (C₄ * (p.β * p.θ) / (p.β * p.θ - 1)) * (Real.log A) ^ (1 - p.κ) := by ring
    linarith
  have hgeom2 : (∑ t ∈ range N, if t₀ + 1 ≤ t then C₅ * Real.log A * p.β ^ t else 0) ≤
      (C₅ / (1 - p.β)) * (Real.log A) ^ (1 - p.κ) := by
    have hshift : (∑ t ∈ range N, if t₀ + 1 ≤ t then C₅ * Real.log A * p.β ^ t else 0) ≤
        C₅ * Real.log A * p.β ^ (t₀ + 1) * (∑ j ∈ range N, p.β ^ j) := by
      have hrew : C₅ * Real.log A * p.β ^ (t₀ + 1) * (∑ j ∈ range N, p.β ^ j) =
          ∑ j ∈ range N, C₅ * Real.log A * p.β ^ (t₀ + 1 + j) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [pow_add]; ring
      rw [hrew]
      by_cases hN : N ≤ t₀ + 1
      · have hzero : (∑ t ∈ range N, if t₀ + 1 ≤ t then C₅ * Real.log A * p.β ^ t else 0) = 0 := by
          refine Finset.sum_eq_zero fun t ht => ?_
          simp only [Finset.mem_range] at ht
          have : ¬ t₀ + 1 ≤ t := by omega
          simp [this]
        rw [hzero]
        refine Finset.sum_nonneg fun j _ => ?_
        have hβ0 : 0 ≤ p.β := le_of_lt p.hβ0
        positivity
      · push Not at hN
        have h1 : (∑ t ∈ range N, if t₀ + 1 ≤ t then C₅ * Real.log A * p.β ^ t else 0) =
            ∑ j ∈ range (N - (t₀ + 1)), C₅ * Real.log A * p.β ^ (t₀ + 1 + j) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun t _ => t - (t₀ + 1)) ?_ ?_ ?_ ?_
          · intro t ht; simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢; omega
          · intro t₁ ht₁ t₂ ht₂ heq
            simp only [Finset.mem_filter, Finset.mem_range] at ht₁ ht₂; omega
          · intro j hj; simp only [Finset.mem_range] at hj
            refine ⟨t₀ + 1 + j, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]; omega
          · intro t ht; simp only [Finset.mem_filter, Finset.mem_range] at ht
            have : t₀ + 1 + (t - (t₀ + 1)) = t := by omega
            rw [this]
        rw [h1]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ _; have hβ0 : 0 ≤ p.β := le_of_lt p.hβ0; positivity
    have hsum_β : ∑ j ∈ range N, p.β ^ j ≤ 1 / (1 - p.β) := by
      have hid := geom_sum_eq p.β N
      rw [le_div_iff₀ h1β_pos]
      have : 0 ≤ p.β ^ N := pow_nonneg (le_of_lt p.hβ0) N
      linarith
    have h1 : C₅ * Real.log A * p.β ^ (t₀ + 1) * (∑ j ∈ range N, p.β ^ j) ≤
        C₅ * Real.log A * p.β ^ (t₀ + 1) * (1 / (1 - p.β)) :=
      mul_le_mul_of_nonneg_left hsum_β (by have hβ0 : 0 ≤ p.β := le_of_lt p.hβ0; positivity)
    have h2 : C₅ * (p.β ^ (t₀ + 1) * Real.log A) * (1 / (1 - p.β)) ≤
        C₅ * (Real.log A) ^ (1 - p.κ) * (1 / (1 - p.β)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ_pow (le_of_lt hC₅))
        (div_nonneg zero_le_one (le_of_lt h1β_pos))
    have hrew1 : C₅ * Real.log A * p.β ^ (t₀ + 1) * (1 / (1 - p.β)) =
        C₅ * (p.β ^ (t₀ + 1) * Real.log A) * (1 / (1 - p.β)) := by ring
    have hrew2 : C₅ * (Real.log A) ^ (1 - p.κ) * (1 / (1 - p.β)) =
        C₅ / (1 - p.β) * (Real.log A) ^ (1 - p.κ) := by ring
    linarith
  linarith

/-! ## 2. Derivadas de $g(k) = c_K k^\theta - \delta k$ y cotas cuadráticas (Piezas 2 y 3) -/

lemma hasDerivAt_g_net {k : ℝ} (hk : 0 < k) :
    HasDerivAt p.g_net (p.θ * p.cK * k ^ p.r - p.δ) k := by
  unfold g_net
  have h1 := (Real.hasDerivAt_rpow_const (p := p.θ) (Or.inl (ne_of_gt hk))).const_mul p.cK
  have h2 := (hasDerivAt_id k).const_mul p.δ
  convert h1.sub h2 using 1
  · ext x; simp
  · have : p.θ - 1 = p.r := by unfold CESParams.θ; ring
    rw [this]; ring

lemma hasDerivAt_g_net_deriv {k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x => p.θ * p.cK * x ^ p.r - p.δ)
      (p.θ * p.r * p.cK * k ^ (p.r - 1)) k := by
  have h1 := (Real.hasDerivAt_rpow_const (p := p.r) (Or.inl (ne_of_gt hk))).const_mul (p.θ * p.cK)
  have h2 := hasDerivAt_const k p.δ
  convert h1.sub h2 using 1
  ring

lemma g_net_deriv_k_star : p.θ * p.cK * p.k_star ^ p.r - p.δ = p.lamK - 1 := by
  unfold CESParams.k_star
  have hpos : 0 < p.δ / p.cK := div_pos p.hδ0 p.hcK_pos
  have hr : ((p.δ / p.cK) ^ (1 / p.r)) ^ p.r = p.δ / p.cK := by
    rw [← Real.rpow_mul (le_of_lt hpos), one_div_mul_cancel (ne_of_gt p.hr0), Real.rpow_one]
  rw [hr, p.lamK_eq]
  unfold CESParams.θ
  field_simp [ne_of_gt p.hcK_pos]; ring

/-- Cota inferior cuadrática de $g(k_* + x)$ en $[0, \epsilon]$ (para Pieza 2):
    $g(k_* + x) \ge (\lambda_K - 1) x + m x^2$ con $m = \frac{1}{2} g''(k_* + \epsilon) > 0$. -/
theorem g_net_convex_lower {ε : ℝ} (hε : 0 < ε) :
    let m := p.θ * p.r * p.cK * (p.k_star + ε) ^ (p.r - 1) / 2
    0 < m ∧ ∀ x ∈ Icc (0 : ℝ) ε, (p.lamK - 1) * x + m * x ^ 2 ≤ p.g_net (p.k_star + x) := by
  intro m
  have hm_pos : 0 < m := by
    dsimp [m]
    have h1 := p.hθ_pos; have h2 := p.hr0; have h3 := p.hcK_pos
    have h4 : 0 < (p.k_star + ε) ^ (p.r - 1) := Real.rpow_pos_of_pos (by linarith [p.hk_star_pos]) _
    positivity
  refine ⟨hm_pos, fun x hx => ?_⟩
  -- Definimos h(t) = g_net(k_* + t) - (lamK - 1) t - m t^2; probamos h'(t) ≥ 0 en [0, ε]
  let h : ℝ → ℝ := fun t => p.g_net (p.k_star + t) - (p.lamK - 1) * t - m * t ^ 2
  let h' : ℝ → ℝ := fun t => (p.θ * p.cK * (p.k_star + t) ^ p.r - p.δ) - (p.lamK - 1) - 2 * m * t
  have hh_deriv : ∀ t ∈ Icc (0 : ℝ) ε, HasDerivAt h (h' t) t := by
    intro t ht
    have hkt : 0 < p.k_star + t := by linarith [p.hk_star_pos, ht.1]
    have hcomp : HasDerivAt (fun s => p.g_net (p.k_star + s))
        (p.θ * p.cK * (p.k_star + t) ^ p.r - p.δ) t := by
      convert (p.hasDerivAt_g_net hkt).comp t ((hasDerivAt_id t).const_add p.k_star) using 1
      · ext s; simp
      · ring
    have hlin : HasDerivAt (fun s => (p.lamK - 1) * s) (p.lamK - 1) t := by
      simpa using (hasDerivAt_id t).const_mul (p.lamK - 1)
    have hsq : HasDerivAt (fun s => m * s ^ 2) (2 * m * t) t := by
      convert ((hasDerivAt_pow 2 t).const_mul m) using 1; ring
    exact (hcomp.sub hlin).sub hsq
  have hh'_nn : ∀ t ∈ Icc (0 : ℝ) ε, 0 ≤ h' t := by
    intro t ht
    have hh'0 : h' 0 = 0 := by dsimp [h']; rw [add_zero, p.g_net_deriv_k_star]; ring
    have hh'_mono : MonotoneOn h' (Icc 0 ε) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 ε) ?_ ?_ ?_
      · exact DifferentiableOn.continuousOn fun s hs => by
          have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs.1]
          have h1 := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have h2 := (hasDerivAt_id s).const_mul (2 * m)
          exact ((h1.sub (hasDerivAt_const s (p.lamK - 1))).sub h2).differentiableAt.differentiableWithinAt
      · exact fun s hs => by
          have hs' := interior_subset hs
          have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs'.1]
          have h1 := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have h2 := (hasDerivAt_id s).const_mul (2 * m)
          exact ((h1.sub (hasDerivAt_const s (p.lamK - 1))).sub h2).differentiableAt.differentiableWithinAt
      · intro s hs
        have hs' := interior_subset hs
        have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs'.1]
        have h1 : HasDerivAt h' (p.θ * p.r * p.cK * (p.k_star + s) ^ (p.r - 1) - 2 * m) s := by
          have ha := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have hb := (hasDerivAt_id s).const_mul (2 * m)
          convert (ha.sub (hasDerivAt_const s (p.lamK - 1))).sub hb using 1
          · ext u; simp [h']
          · ring
        rw [h1.deriv]
        -- Como r - 1 < 0 y k_* + s ≤ k_* + ε, (k_* + ε)^(r-1) ≤ (k_* + s)^(r-1)
        have hpow_le : (p.k_star + ε) ^ (p.r - 1) ≤ (p.k_star + s) ^ (p.r - 1) :=
          Real.rpow_le_rpow_of_nonpos hks (by linarith [hs'.2]) (by linarith [p.hr1])
        have hcoef_nn : 0 ≤ p.θ * p.r * p.cK := by
          have := p.hθ_pos; have := p.hr0; have := p.hcK_pos; positivity
        have hmul := mul_le_mul_of_nonneg_left hpow_le hcoef_nn
        dsimp [m]; linarith
    have := hh'_mono ⟨le_rfl, le_of_lt hε⟩ ht ht.1
    linarith
  have hh_mono : MonotoneOn h (Icc 0 ε) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 ε) ?_ ?_ ?_
    · exact DifferentiableOn.continuousOn fun s hs =>
        (hh_deriv s hs).differentiableAt.differentiableWithinAt
    · exact fun s hs => (hh_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hh_deriv s hs').deriv]
      exact hh'_nn s hs'
  have hh0 : h 0 = 0 := by dsimp [h]; rw [add_zero, p.g_net_k_star]; ring
  have hge := hh_mono ⟨le_rfl, le_of_lt hε⟩ hx hx.1
  dsimp [h] at hge; linarith

/-- Cota superior cuadrática global de $g(k_* + x)$ para **todo** $x \ge 0$ (para Pieza 3):
    $g(k_* + x) \le (\lambda_K - 1) x + M x^2$ con $M = \frac{\theta r \delta}{2 k_*} = \frac{1}{2} g''(k_*)$. -/
theorem g_net_quadratic_upper :
    let M := p.θ * p.r * p.δ / (2 * p.k_star)
    0 < M ∧ ∀ x ≥ 0, p.g_net (p.k_star + x) ≤ (p.lamK - 1) * x + M * x ^ 2 := by
  intro M
  have hM_pos : 0 < M := by
    dsimp [M]; have := p.hθ_pos; have := p.hr0; have := p.hδ0; have := p.hk_star_pos; positivity
  have hM_eq : 2 * M = p.θ * p.r * p.cK * p.k_star ^ (p.r - 1) := by
    dsimp [M]
    have hpos : 0 < p.δ / p.cK := div_pos p.hδ0 p.hcK_pos
    have hkr : p.k_star ^ p.r = p.δ / p.cK := by
      unfold CESParams.k_star
      rw [← Real.rpow_mul (le_of_lt hpos), one_div_mul_cancel (ne_of_gt p.hr0), Real.rpow_one]
    have hkm1 : p.k_star ^ (p.r - 1) = p.k_star ^ p.r / p.k_star := by
      rw [Real.rpow_sub p.hk_star_pos, Real.rpow_one]
    rw [hkm1, hkr]
    field_simp [ne_of_gt p.hk_star_pos, ne_of_gt p.hcK_pos]
  refine ⟨hM_pos, fun x hx => ?_⟩
  let h : ℝ → ℝ := fun t => (p.lamK - 1) * t + M * t ^ 2 - p.g_net (p.k_star + t)
  let h' : ℝ → ℝ := fun t => (p.lamK - 1) + 2 * M * t - (p.θ * p.cK * (p.k_star + t) ^ p.r - p.δ)
  have hh_deriv : ∀ t ∈ Icc (0 : ℝ) x, HasDerivAt h (h' t) t := by
    intro t ht
    have hkt : 0 < p.k_star + t := by linarith [p.hk_star_pos, ht.1]
    have hcomp : HasDerivAt (fun s => p.g_net (p.k_star + s))
        (p.θ * p.cK * (p.k_star + t) ^ p.r - p.δ) t := by
      convert (p.hasDerivAt_g_net hkt).comp t ((hasDerivAt_id t).const_add p.k_star) using 1
      · ext s; simp
      · ring
    have hlin : HasDerivAt (fun s => (p.lamK - 1) * s) (p.lamK - 1) t := by
      simpa using (hasDerivAt_id t).const_mul (p.lamK - 1)
    have hsq : HasDerivAt (fun s => M * s ^ 2) (2 * M * t) t := by
      convert ((hasDerivAt_pow 2 t).const_mul M) using 1; ring
    exact (hlin.add hsq).sub hcomp
  have hh'_nn : ∀ t ∈ Icc (0 : ℝ) x, 0 ≤ h' t := by
    intro t ht
    have hh'0 : h' 0 = 0 := by dsimp [h']; rw [add_zero, p.g_net_deriv_k_star]; ring
    have hh'_mono : MonotoneOn h' (Icc 0 x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) ?_ ?_ ?_
      · exact DifferentiableOn.continuousOn fun s hs => by
          have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs.1]
          have h1 := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have h2 := (hasDerivAt_id s).const_mul (2 * M)
          exact (((hasDerivAt_const s (p.lamK - 1)).add h2).sub h1).differentiableAt.differentiableWithinAt
      · exact fun s hs => by
          have hs' := interior_subset hs
          have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs'.1]
          have h1 := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have h2 := (hasDerivAt_id s).const_mul (2 * M)
          exact (((hasDerivAt_const s (p.lamK - 1)).add h2).sub h1).differentiableAt.differentiableWithinAt
      · intro s hs
        have hs' := interior_subset hs
        have hks : 0 < p.k_star + s := by linarith [p.hk_star_pos, hs'.1]
        have h1 : HasDerivAt h' (2 * M - p.θ * p.r * p.cK * (p.k_star + s) ^ (p.r - 1)) s := by
          have ha := (p.hasDerivAt_g_net_deriv hks).comp s ((hasDerivAt_id s).const_add p.k_star)
          have hb := (hasDerivAt_id s).const_mul (2 * M)
          convert ((hasDerivAt_const s (p.lamK - 1)).add hb).sub ha using 1
          · ext u; simp [h']
          · ring
        rw [h1.deriv, hM_eq]
        have hpow_le : (p.k_star + s) ^ (p.r - 1) ≤ p.k_star ^ (p.r - 1) :=
          Real.rpow_le_rpow_of_nonpos p.hk_star_pos (by linarith [hs'.1]) (by linarith [p.hr1])
        have hcoef_nn : 0 ≤ p.θ * p.r * p.cK := by
          have := p.hθ_pos; have := p.hr0; have := p.hcK_pos; positivity
        have hmul := mul_le_mul_of_nonneg_left hpow_le hcoef_nn
        linarith
    have := hh'_mono ⟨le_rfl, hx⟩ ht ht.1
    linarith
  have hh_mono : MonotoneOn h (Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) ?_ ?_ ?_
    · exact DifferentiableOn.continuousOn fun s hs =>
        (hh_deriv s hs).differentiableAt.differentiableWithinAt
    · exact fun s hs => (hh_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hh_deriv s hs').deriv]
      exact hh'_nn s hs'
  have hh0 : h 0 = 0 := by dsimp [h]; rw [add_zero, p.g_net_k_star]; ring
  have hge := hh_mono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  dsimp [h] at hge; linarith

/-- Penalización CES uniforme en $k \in (0, k_{\max}]$:
    $c_K k^\theta - f_A(k, 1) \le C_{\text{ces}} A^{-d/r}$. -/
theorem f_norm_ces_penalty {k_max : ℝ} (hkm : 0 < k_max) :
    let C_ces := (p.θ / p.d) * p.cK * p.cw * k_max ^ (p.θ + p.d)
    0 < C_ces ∧ ∀ {A k : ℝ}, 0 < A → 0 < k → k ≤ k_max →
      p.cK * k ^ p.θ - p.f_norm A k 1 ≤ C_ces * A ^ (-p.d / p.r) := by
  intro C_ces
  have hC_pos : 0 < C_ces := by
    dsimp [C_ces]
    have := p.hθ_pos; have := p.hd; have := p.hcK_pos; have := p.hcw_pos
    have := Real.rpow_pos_of_pos hkm (p.θ + p.d)
    positivity
  refine ⟨hC_pos, fun {A k} hA hk0 hkm_le => ?_⟩
  rw [p.f_norm_eq hA hk0 one_pos, mul_one]
  set u : ℝ := p.cw * (k / A ^ (1 / p.r)) ^ p.d
  have hu_nn : 0 ≤ u := by
    dsimp [u]
    have := p.hcw_pos
    have : 0 ≤ (k / A ^ (1 / p.r)) ^ p.d :=
      le_of_lt (Real.rpow_pos_of_pos (div_pos hk0 (Real.rpow_pos_of_pos hA _)) _)
    positivity
  -- 1 - (1 + u)^(-θ/d) ≤ (θ/d) * u vía exp(-α u) ≥ 1 - α u y log(1 + u) ≤ u
  have hpow_ge : 1 - (p.θ / p.d) * u ≤ (1 + u) ^ (-p.θ / p.d) := by
    have hlog_le : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
      linarith
    have hexp_ge : Real.exp (-(p.θ / p.d) * u) ≤ (1 + u) ^ (-p.θ / p.d) := by
      rw [Real.rpow_def_of_pos (show 0 < 1 + u by linarith)]
      apply Real.exp_le_exp.mpr
      have hα : 0 ≤ p.θ / p.d := div_nonneg (le_of_lt p.hθ_pos) (le_of_lt p.hd)
      have hmul := mul_le_mul_of_nonneg_left hlog_le hα
      have : -p.θ / p.d = -(p.θ / p.d) := by ring
      rw [this]; linarith
    have hlin := Real.add_one_le_exp (-(p.θ / p.d) * u)
    linarith
  have hdiff : p.cK * k ^ p.θ - p.cK * k ^ p.θ * (1 + u) ^ (-p.θ / p.d) ≤
      (p.θ / p.d) * p.cK * k ^ p.θ * u := by
    have hnn : 0 ≤ p.cK * k ^ p.θ := mul_nonneg (le_of_lt p.hcK_pos) (le_of_lt (Real.rpow_pos_of_pos hk0 _))
    have hmul := mul_le_mul_of_nonneg_left hpow_ge hnn
    linarith
  have hu_eq : k ^ p.θ * u = p.cw * k ^ (p.θ + p.d) * A ^ (-p.d / p.r) := by
    dsimp [u]
    rw [Real.div_rpow (le_of_lt hk0) (le_of_lt (Real.rpow_pos_of_pos hA _)),
        ← Real.rpow_mul (le_of_lt hA), Real.rpow_add hk0]
    have hinv : (A ^ (1 / p.r * p.d))⁻¹ = A ^ (-p.d / p.r) := by
      rw [← Real.rpow_neg (le_of_lt hA)]; congr 1; ring
    rw [div_eq_mul_inv, hinv]; ring
  have hk_le : k ^ (p.θ + p.d) ≤ k_max ^ (p.θ + p.d) :=
    Real.rpow_le_rpow (le_of_lt hk0) hkm_le (by linarith [p.hθ_pos, p.hd])
  have hfinal : (p.θ / p.d) * p.cK * (p.cw * k ^ (p.θ + p.d) * A ^ (-p.d / p.r)) ≤
      C_ces * A ^ (-p.d / p.r) := by
    dsimp [C_ces]
    have hnn : 0 ≤ (p.θ / p.d) * p.cK * p.cw * A ^ (-p.d / p.r) := by
      have := p.hθ_pos; have := p.hd; have := p.hcK_pos; have := p.hcw_pos
      have := Real.rpow_pos_of_pos hA (-p.d / p.r)
      positivity
    have := mul_le_mul_of_nonneg_left hk_le hnn
    linarith
  have hrew : (p.θ / p.d) * p.cK * k ^ p.θ * u =
      (p.θ / p.d) * p.cK * (p.cw * k ^ (p.θ + p.d) * A ^ (-p.d / p.r)) := by
    rw [← hu_eq]; ring
  linarith

/-! ## 3. Pieza 2: Política explícita y cota superior rigurosa de $\Delta_k(A)$ -/

/-- Política explícita de escape linealizado (válida para todo $\beta \theta > 1$, incluso si
    $\beta \lambda_K < 1$): alcanza $x_T = \epsilon$ desde $x_0 = \Delta_k$ en
    $T = \lceil \frac{\log(2\epsilon/\Delta_k)}{\log \lambda_K} \rceil$ pasos, manteniendo
    $x_t \ge \frac{1 - \beta}{2} \Delta_k$ en todos los pasos, con $\beta^T \ge (\frac{\Delta_k}{2\lambda_K\epsilon})^{\mu_K}$
    y utilidad acumulada $\ge \frac{\eta}{1-\beta} \log \Delta_k - C_{\text{pol}}$. -/
theorem piece2_explicit_policy {ε Δk : ℝ} (hε : 0 < ε) (hΔ0 : 0 < Δk) (hΔε : Δk < ε)
    (hΔ1 : Δk ≤ 1) :
    let T : ℕ := Nat.ceil (Real.log (2 * ε / Δk) / Real.log p.lamK)
    let c : ℕ → ℝ := fun t =>
      ((1 - p.β) / (1 - p.β ^ T)) * p.lamK * (p.β * p.lamK) ^ t * (Δk - ε / p.lamK ^ T)
    let x : ℕ → ℝ := fun t =>
      p.lamK ^ t * (Δk - ∑ j ∈ range t, c j / p.lamK ^ (j + 1))
    0 < T ∧
    (∀ t, 0 < c t) ∧
    x 0 = Δk ∧
    x T = ε ∧
    (∀ t, x (t + 1) = p.lamK * x t - c t) ∧
    (∀ t ≤ T, ((1 - p.β) / 2) * Δk ≤ x t) ∧
    (Δk / (2 * p.lamK * ε)) ^ p.μ_K ≤ p.β ^ T ∧
    (p.η / (1 - p.β)) * Real.log Δk -
      (p.η / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)| +
       p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)|) ≤
      ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (c t)) := by
  intro T c x
  have hratio_gt2 : 2 < 2 * ε / Δk := by rw [lt_div_iff₀ hΔ0]; linarith
  have hlog_pos : 0 < Real.log (2 * ε / Δk) / Real.log p.lamK :=
    div_pos (Real.log_pos (by linarith)) p.hlog_lamK_pos
  have hT_pos : 0 < T := Nat.ceil_pos.mpr hlog_pos
  have h1β_pos : 0 < 1 - p.β := by linarith [p.hβ1]
  have hβT_lt1 : p.β ^ T < 1 := pow_lt_one₀ (le_of_lt p.hβ0) p.hβ1 (ne_of_gt hT_pos)
  have h1βT_pos : 0 < 1 - p.β ^ T := by linarith
  -- Cotas exactas sobre lamK^T
  have hlamT_ge : 2 * ε / Δk ≤ p.lamK ^ T := by
    have hceil : Real.log (2 * ε / Δk) / Real.log p.lamK ≤ (T : ℝ) := Nat.le_ceil _
    have hmul := mul_le_mul_of_nonneg_right hceil (le_of_lt p.hlog_lamK_pos)
    have hrew : Real.log (2 * ε / Δk) / Real.log p.lamK * Real.log p.lamK = Real.log (2 * ε / Δk) := by
      field_simp [ne_of_gt p.hlog_lamK_pos]
    rw [← Real.exp_log (show 0 < 2 * ε / Δk by positivity),
        show p.lamK ^ T = Real.exp ((T : ℝ) * Real.log p.lamK) by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos p.hlamK_pos]; ring_nf]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlamT_le : p.lamK ^ T ≤ 2 * p.lamK * ε / Δk := by
    have hceil : (T : ℝ) < Real.log (2 * ε / Δk) / Real.log p.lamK + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hlog_pos)
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hceil) (le_of_lt p.hlog_lamK_pos)
    have hrew : (Real.log (2 * ε / Δk) / Real.log p.lamK + 1) * Real.log p.lamK =
        Real.log (2 * ε / Δk) + Real.log p.lamK := by
      field_simp [ne_of_gt p.hlog_lamK_pos]
    rw [show p.lamK ^ T = Real.exp ((T : ℝ) * Real.log p.lamK) by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos p.hlamK_pos]; ring_nf,
        show 2 * p.lamK * ε / Δk = (2 * ε / Δk) * p.lamK by ring,
        ← Real.exp_log (mul_pos (div_pos (by linarith) hΔ0) p.hlamK_pos),
        Real.log_mul (ne_of_gt (div_pos (by linarith) hΔ0)) (ne_of_gt p.hlamK_pos)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hrem_ge : Δk / 2 ≤ Δk - ε / p.lamK ^ T := by
    have h1 : ε / p.lamK ^ T ≤ Δk / 2 := by
      rw [div_le_iff₀ (pow_pos p.hlamK_pos T)]
      have := (div_le_iff₀ hΔ0).mp hlamT_ge
      linarith
    linarith
  have hc_pos : ∀ t, 0 < c t := by
    intro t; dsimp [c]
    have h1 : 0 < Δk - ε / p.lamK ^ T := by linarith
    have h2 : 0 < (p.β * p.lamK) ^ t := pow_pos (mul_pos p.hβ0 p.hlamK_pos) t
    have h3 := p.hlamK_pos
    positivity
  have hx0 : x 0 = Δk := by dsimp [x]; simp
  have hsum_c : ∀ t, ∑ j ∈ range t, c j / p.lamK ^ (j + 1) =
      ((1 - p.β ^ t) / (1 - p.β ^ T)) * (Δk - ε / p.lamK ^ T) := by
    intro t
    have hterm : ∀ j, c j / p.lamK ^ (j + 1) =
        ((1 - p.β) / (1 - p.β ^ T)) * (Δk - ε / p.lamK ^ T) * p.β ^ j := by
      intro j; dsimp [c]
      rw [pow_succ, mul_pow]
      have hne : p.lamK ^ j ≠ 0 := ne_of_gt (pow_pos p.hlamK_pos j)
      have hne1 : p.lamK ≠ 0 := ne_of_gt p.hlamK_pos
      field_simp [hne, hne1]
    simp_rw [hterm, ← Finset.mul_sum]
    have hgeom := geom_sum_eq p.β t
    have hsum : ∑ j ∈ range t, p.β ^ j = (1 - p.β ^ t) / (1 - p.β) :=
      eq_div_of_mul_eq (ne_of_gt h1β_pos) hgeom
    rw [hsum]; field_simp [ne_of_gt h1β_pos, ne_of_gt h1βT_pos]
  have hxT : x T = ε := by
    dsimp [x]; rw [hsum_c T, div_self (ne_of_gt h1βT_pos), one_mul]
    field_simp [ne_of_gt (pow_pos p.hlamK_pos T)]; ring
  have hx_step : ∀ t, x (t + 1) = p.lamK * x t - c t := by
    intro t; dsimp [x]
    rw [Finset.sum_range_succ, pow_succ]
    have hne : p.lamK ^ t * p.lamK ≠ 0 := ne_of_gt (mul_pos (pow_pos p.hlamK_pos t) p.hlamK_pos)
    have hmul : (p.lamK ^ t * p.lamK) * (c t / (p.lamK ^ t * p.lamK)) = c t := mul_div_cancel₀ _ hne
    have hdist : p.lamK ^ t * p.lamK * (Δk - (∑ j ∈ range t, c j / p.lamK ^ (j + 1) + c t / (p.lamK ^ t * p.lamK))) =
        p.lamK * (p.lamK ^ t * (Δk - ∑ j ∈ range t, c j / p.lamK ^ (j + 1))) -
        (p.lamK ^ t * p.lamK) * (c t / (p.lamK ^ t * p.lamK)) := by ring
    rw [hdist, hmul]
  have hx_ge : ∀ t ≤ T, ((1 - p.β) / 2) * Δk ≤ x t := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0; rw [hx0]
      have : (1 - p.β) / 2 ≤ 1 := by linarith [p.hβ0]
      nlinarith
    · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
      dsimp [x]; rw [hsum_c t]
      have hβt_ge : p.β ^ T ≤ p.β ^ t := pow_le_pow_of_le_one (le_of_lt p.hβ0) (le_of_lt p.hβ1) ht
      have h1βt_ge : 1 - p.β ≤ 1 - p.β ^ t := by
        have : p.β ^ t ≤ p.β ^ 1 := pow_le_pow_of_le_one (le_of_lt p.hβ0) (le_of_lt p.hβ1) ht_pos
        rw [pow_one] at this; linarith
      have hrew : Δk - (1 - p.β ^ t) / (1 - p.β ^ T) * (Δk - ε / p.lamK ^ T) =
          ((p.β ^ t - p.β ^ T) / (1 - p.β ^ T)) * Δk +
          ((1 - p.β ^ t) / (1 - p.β ^ T)) * (ε / p.lamK ^ T) := by
        field_simp [ne_of_gt h1βT_pos]; ring
      rw [hrew]
      have hterm1 : 0 ≤ ((p.β ^ t - p.β ^ T) / (1 - p.β ^ T)) * Δk :=
        mul_nonneg (div_nonneg (by linarith) (le_of_lt h1βT_pos)) (le_of_lt hΔ0)
      have hlamt_ge : p.lamK ≤ p.lamK ^ t := by
        calc p.lamK = p.lamK ^ 1 := (pow_one _).symm
          _ ≤ p.lamK ^ t := pow_le_pow_right₀ (le_of_lt p.hlamK_gt1) ht_pos
      have hε_div : Δk / (2 * p.lamK) ≤ ε / p.lamK ^ T := by
        rw [div_le_div_iff₀ (by linarith [p.hlamK_pos]) (pow_pos p.hlamK_pos T)]
        have := (le_div_iff₀ hΔ0).mp hlamT_le
        linarith
      have hfrac : 1 - p.β ≤ (1 - p.β ^ t) / (1 - p.β ^ T) := by
        rw [le_div_iff₀ h1βT_pos]
        have : (1 - p.β) * (1 - p.β ^ T) ≤ 1 - p.β := by
          have : 0 ≤ p.β ^ T := pow_nonneg (le_of_lt p.hβ0) T
          nlinarith
        linarith
      have hprod : p.lamK ^ t * (((1 - p.β ^ t) / (1 - p.β ^ T)) * (ε / p.lamK ^ T)) ≥
          p.lamK * ((1 - p.β) * (Δk / (2 * p.lamK))) := by
        have h1 : (1 - p.β) * (Δk / (2 * p.lamK)) ≤
            ((1 - p.β ^ t) / (1 - p.β ^ T)) * (ε / p.lamK ^ T) :=
          mul_le_mul hfrac hε_div (div_nonneg (le_of_lt hΔ0) (by linarith [p.hlamK_pos]))
            (div_nonneg (by linarith [pow_le_one₀ (le_of_lt p.hβ0) (le_of_lt p.hβ1) (n := t)]) (le_of_lt h1βT_pos))
        have hnn1 : 0 ≤ (1 - p.β) * (Δk / (2 * p.lamK)) :=
          mul_nonneg (le_of_lt h1β_pos) (div_nonneg (le_of_lt hΔ0) (by linarith [p.hlamK_pos]))
        exact mul_le_mul hlamt_ge h1 hnn1 (pow_nonneg (le_of_lt p.hlamK_pos) t)
      have hsimp : p.lamK * ((1 - p.β) * (Δk / (2 * p.lamK))) = ((1 - p.β) / 2) * Δk := by
        field_simp [ne_of_gt p.hlamK_pos]
      have hlamt_nn : 0 ≤ p.lamK ^ t := pow_nonneg (le_of_lt p.hlamK_pos) t
      nlinarith
  have hβT_ge : (Δk / (2 * p.lamK * ε)) ^ p.μ_K ≤ p.β ^ T := by
    rw [p.beta_pow_eq_rpow_muK T]
    have hinv : (p.lamK ^ T) ^ (-p.μ_K) = ((p.lamK ^ T)⁻¹) ^ p.μ_K := by
      rw [Real.rpow_neg (le_of_lt (pow_pos p.hlamK_pos T)), Real.inv_rpow (le_of_lt (pow_pos p.hlamK_pos T))]
    rw [hinv]
    apply Real.rpow_le_rpow (by have := p.hlamK_pos; positivity) _ (le_of_lt p.hμ_K_pos)
    rw [div_le_iff₀ (by have := p.hlamK_pos; positivity)]
    have h1 := (le_div_iff₀ hΔ0).mp hlamT_le
    have h2 : Δk ≤ (p.lamK ^ T)⁻¹ * (2 * p.lamK * ε) := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos p.hlamK_pos T)]
      linarith
    linarith
  -- Cota inferior de la utilidad acumulada
  have hutil : (p.η / (1 - p.β)) * Real.log Δk -
      (p.η / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)| +
       p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)|) ≤
      ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (c t)) := by
    have hc_lb : ∀ t, ((1 - p.β) * p.lamK / 2) * (p.β * p.lamK) ^ t * Δk ≤ c t := by
      intro t; dsimp [c]
      have h1 : 1 - p.β ≤ (1 - p.β) / (1 - p.β ^ T) := by
        rw [le_div_iff₀ h1βT_pos]
        have : 0 ≤ p.β ^ T := pow_nonneg (le_of_lt p.hβ0) T
        nlinarith
      have h2 : ((1 - p.β) * p.lamK) * (p.β * p.lamK) ^ t * (Δk / 2) ≤
          ((1 - p.β) / (1 - p.β ^ T)) * p.lamK * (p.β * p.lamK) ^ t * (Δk - ε / p.lamK ^ T) := by
        have ha : (1 - p.β) * p.lamK * (p.β * p.lamK) ^ t ≤
            (1 - p.β) / (1 - p.β ^ T) * p.lamK * (p.β * p.lamK) ^ t := by
          have hnn : 0 ≤ p.lamK * (p.β * p.lamK) ^ t := by
            have := p.hlamK_pos; have := p.hβ0; positivity
          have := mul_le_mul_of_nonneg_right h1 hnn
          linarith
        exact mul_le_mul ha hrem_ge (by positivity) (by have := p.hlamK_pos; have := p.hβ0; positivity)
      linarith
    have hlog_lb : ∀ t : ℕ, Real.log ((1 - p.β) * p.lamK / 2) + (t : ℝ) * Real.log (p.β * p.lamK) +
        Real.log Δk ≤ Real.log (c t) := by
      intro t
      have hpos1 : 0 < (1 - p.β) * p.lamK / 2 := by have := p.hlamK_pos; positivity
      have hpos2 : 0 < (p.β * p.lamK) ^ t := pow_pos (mul_pos p.hβ0 p.hlamK_pos) t
      have hle := Real.log_le_log (mul_pos (mul_pos hpos1 hpos2) hΔ0) (hc_lb t)
      rw [Real.log_mul (ne_of_gt (mul_pos hpos1 hpos2)) (ne_of_gt hΔ0),
          Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2), Real.log_pow] at hle
      exact hle
    have hsum_le : ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log ((1 - p.β) * p.lamK / 2) +
        (t : ℝ) * Real.log (p.β * p.lamK) + Real.log Δk)) ≤
        ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (c t)) :=
      Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog_lb t) (le_of_lt p.hη0))
          (pow_nonneg (le_of_lt p.hβ0) t)
    have hgeom : ∑ t ∈ range T, p.β ^ t = (1 - p.β ^ T) / (1 - p.β) := by
      have hid := geom_sum_eq p.β T
      exact eq_div_of_mul_eq (ne_of_gt h1β_pos) hid
    have hexp : ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log ((1 - p.β) * p.lamK / 2) +
        (t : ℝ) * Real.log (p.β * p.lamK) + Real.log Δk)) =
        p.η * ((1 - p.β ^ T) / (1 - p.β)) * Real.log Δk +
        p.η * ((1 - p.β ^ T) / (1 - p.β)) * Real.log ((1 - p.β) * p.lamK / 2) +
        p.η * (∑ t ∈ range T, (t : ℝ) * p.β ^ t) * Real.log (p.β * p.lamK) := by
      have hrew : ∀ t : ℕ, p.β ^ t * (p.η * (Real.log ((1 - p.β) * p.lamK / 2) +
          (t : ℝ) * Real.log (p.β * p.lamK) + Real.log Δk)) =
          p.β ^ t * (p.η * Real.log Δk) + p.β ^ t * (p.η * Real.log ((1 - p.β) * p.lamK / 2)) +
          ((t : ℝ) * p.β ^ t) * (p.η * Real.log (p.β * p.lamK)) := fun t => by ring
      simp_rw [hrew]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hgeom]
      ring
    have hlogΔ_np : Real.log Δk ≤ 0 := Real.log_nonpos (le_of_lt hΔ0) hΔ1
    have hfrac_le : (1 - p.β ^ T) / (1 - p.β) ≤ 1 / (1 - p.β) :=
      div_le_div_of_nonneg_right (by linarith [pow_nonneg (le_of_lt p.hβ0) T]) (le_of_lt h1β_pos)
    have hterm1 : (p.η / (1 - p.β)) * Real.log Δk ≤
        p.η * ((1 - p.β ^ T) / (1 - p.β)) * Real.log Δk := by
      have h1 := mul_le_mul_of_nonpos_right hfrac_le hlogΔ_np
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt p.hη0)
      have ha : p.η * (1 / (1 - p.β) * Real.log Δk) = (p.η / (1 - p.β)) * Real.log Δk := by ring
      have hb : p.η * ((1 - p.β ^ T) / (1 - p.β) * Real.log Δk) = p.η * ((1 - p.β ^ T) / (1 - p.β)) * Real.log Δk := by ring
      linarith
    have hterm2 : -(p.η / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)|) ≤
        p.η * ((1 - p.β ^ T) / (1 - p.β)) * Real.log ((1 - p.β) * p.lamK / 2) := by
      have h1 : -|Real.log ((1 - p.β) * p.lamK / 2)| ≤ Real.log ((1 - p.β) * p.lamK / 2) :=
        neg_abs_le _
      have h2 := mul_le_mul_of_nonneg_left h1
        (mul_nonneg (le_of_lt p.hη0) (div_nonneg (le_of_lt h1βT_pos) (le_of_lt h1β_pos)))
      have h3 := mul_le_mul_of_nonneg_right hfrac_le (abs_nonneg (Real.log ((1 - p.β) * p.lamK / 2)))
      have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt p.hη0)
      have ha : p.η * (1 / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)|) =
          p.η / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)| := by ring
      have hb : p.η * ((1 - p.β ^ T) / (1 - p.β)) * -|Real.log ((1 - p.β) * p.lamK / 2)| =
          -(p.η * ((1 - p.β ^ T) / (1 - p.β) * |Real.log ((1 - p.β) * p.lamK / 2)|)) := by ring
      linarith
    have hterm3 : -(p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)|) ≤
        p.η * (∑ t ∈ range T, (t : ℝ) * p.β ^ t) * Real.log (p.β * p.lamK) := by
      have hs_nn : 0 ≤ ∑ t ∈ range T, (t : ℝ) * p.β ^ t :=
        Finset.sum_nonneg fun t _ => mul_nonneg (Nat.cast_nonneg t) (pow_nonneg (le_of_lt p.hβ0) t)
      have hs_le := p.sum_mul_beta_pow_le T
      have h1 : -|Real.log (p.β * p.lamK)| ≤ Real.log (p.β * p.lamK) := neg_abs_le _
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt p.hη0) hs_nn)
      have h3 := mul_le_mul_of_nonneg_right hs_le (abs_nonneg (Real.log (p.β * p.lamK)))
      have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt p.hη0)
      linarith
    linarith
  exact ⟨hT_pos, hc_pos, hx0, hxT, hx_step, hx_ge, hβT_ge, hutil⟩

/-- Inversión algebraica de la Pieza 2:
    si en todo $\Delta_k$ donde la supervivencia vence estrictamente a la extinción se tiene
    $\Delta_k(A) \le \Delta_k$, y la supervivencia satisface la desigualdad de balance
    $(\eta/(1-\beta)) \log \Delta_k - C_{\text{pol}} + (\Delta_k / D)^{\mu_K} (c_{\text{lo}} (\log A)^{1-\kappa} - C_{\text{lo}}) > C_{\text{ext}}$,
    entonces para todo $A$ suficientemente grande:
    $\Delta_k(A) \le C_+ \left(\frac{\log\log A}{(\log A)^{1 - \kappa}}\right)^{1 / \mu_K}$. -/
theorem piece2_delta_k_upper {D c_lo C_lo C_pol C_ext : ℝ}
    (hD : 0 < D) (hclo : 0 < c_lo) :
    ∃ A₂ ≥ Real.exp (Real.exp 2), ∃ C_plus > 0, ∀ A ≥ A₂,
      let Δ_cand := C_plus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K)
      0 < Δ_cand ∧ Δ_cand ≤ 1 ∧
      C_ext < (p.η / (1 - p.β)) * Real.log Δ_cand - C_pol +
        (Δ_cand / D) ^ p.μ_K * (c_lo * (Real.log A) ^ (1 - p.κ) - C_lo) := by
  have h1β : 0 < 1 - p.β := by linarith [p.hβ1]
  have h1κ : 0 < 1 - p.κ := by linarith [p.hκ_lt1]
  -- Elegimos C_plus tal que (C_plus / D)^μ_K * (c_lo / 2) = 2 * (η / ((1 - β) * μ_K)) + 1
  set K_coef : ℝ := 2 * (p.η / ((1 - p.β) * p.μ_K)) + 1
  have hK_pos : 0 < K_coef := by
    dsimp [K_coef]; have := p.hη0; have := p.hμ_K_pos; positivity
  set C_plus : ℝ := D * (2 * K_coef / c_lo) ^ (1 / p.μ_K)
  have hCp_pos : 0 < C_plus := mul_pos hD (Real.rpow_pos_of_pos (by positivity) _)
  -- Necesitamos A suficientemente grande para que:
  -- (1) c_lo * (log A)^(1 - κ) - C_lo ≥ (c_lo / 2) * (log A)^(1 - κ)
  -- (2) Δ_cand ≤ 1
  -- (3) K_coef * log(log A) + (η / (1 - β)) * log Δ_cand - C_pol > C_ext
  --     donde log Δ_cand = log C_plus + (1/μ_K) * log(log log A) - ((1 - κ)/μ_K) * log(log A)
  --     Nota: K_coef - (η / ((1 - β) * μ_K)) * (1 - κ) ≥ 1 + (η / ((1 - β) * μ_K)) > 1!
  set M_const : ℝ := |C_ext| + |C_pol| + (p.η / (1 - p.β)) * |Real.log C_plus| + 1
  have hM_pos : 0 < M_const := by dsimp [M_const]; have := p.hη0; positivity
  -- Para log(log A) ≥ max(2, M_const) y (log A)^(1-κ) ≥ max(2 * |C_lo| / c_lo + 1, ...):
  -- Notar que log(log A) ≤ (2 / (1 - κ)) * (log A)^((1 - κ)/2) por log y ≤ y - 1
  set B_logA : ℝ := max (Real.exp (max 2 M_const))
    (max ((2 * (|C_lo| + 1) / c_lo) ^ (1 / (1 - p.κ)))
         (((2 * C_plus ^ p.μ_K + 1) * (2 / (1 - p.κ))) ^ (2 / (1 - p.κ))))
  refine ⟨Real.exp (max (Real.exp 2) B_logA),
    Real.exp_le_exp.mpr (le_max_left _ _), C_plus, hCp_pos, fun A hA => ?_⟩
  have hlogA_ge : max (Real.exp 2) B_logA ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos _) hA; rwa [Real.log_exp] at this
  have hlogA_ge_e2 : Real.exp 2 ≤ Real.log A := le_trans (le_max_left _ _) hlogA_ge
  have hlogA_ge_B : B_logA ≤ Real.log A := le_trans (le_max_right _ _) hlogA_ge
  have hlogA_pos : 0 < Real.log A := lt_of_lt_of_le (Real.exp_pos 2) hlogA_ge_e2
  have hloglogA_ge : max 2 M_const ≤ Real.log (Real.log A) := by
    have h1 : Real.exp (max 2 M_const) ≤ Real.log A := le_trans (le_max_left _ _) hlogA_ge_B
    have := Real.log_le_log (Real.exp_pos _) h1; rwa [Real.log_exp] at this
  have hloglogA_ge2 : 2 ≤ Real.log (Real.log A) := le_trans (le_max_left _ _) hloglogA_ge
  have hloglogA_geM : M_const ≤ Real.log (Real.log A) := le_trans (le_max_right _ _) hloglogA_ge
  have hloglogA_pos : 0 < Real.log (Real.log A) := by linarith
  have hlogA_pow_pos : 0 < (Real.log A) ^ (1 - p.κ) := Real.rpow_pos_of_pos hlogA_pos _
  set Δ_cand : ℝ := C_plus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K)
  have hΔ_pos : 0 < Δ_cand := mul_pos hCp_pos (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)
  -- (1) c_lo * (log A)^(1 - κ) - C_lo ≥ (c_lo / 2) * (log A)^(1 - κ)
  have hclo_half : (c_lo / 2) * (Real.log A) ^ (1 - p.κ) ≤ c_lo * (Real.log A) ^ (1 - p.κ) - C_lo := by
    have h1 : (2 * (|C_lo| + 1) / c_lo) ^ (1 / (1 - p.κ)) ≤ Real.log A :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hlogA_ge_B)
    have h2 : 2 * (|C_lo| + 1) / c_lo ≤ (Real.log A) ^ (1 - p.κ) := by
      have hpos : 0 < 2 * (|C_lo| + 1) / c_lo := by positivity
      have := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hpos _)) h1 (le_of_lt h1κ)
      rwa [← Real.rpow_mul (le_of_lt hpos), one_div_mul_cancel (ne_of_gt h1κ), Real.rpow_one] at this
    have h3 : 2 * (|C_lo| + 1) ≤ c_lo * (Real.log A) ^ (1 - p.κ) := by
      have := (div_le_iff₀ hclo).mp h2; linarith
    have h4 : C_lo ≤ |C_lo| := le_abs_self C_lo
    linarith
  -- (2) Δ_cand ≤ 1 usando log(log A) ≤ (2/(1-κ)) * (log A)^((1-κ)/2)
  have hΔ_le1 : Δ_cand ≤ 1 := by
    have hlog_sub : Real.log (Real.log A) ≤ (2 / (1 - p.κ)) * (Real.log A) ^ ((1 - p.κ) / 2) := by
      have hconc := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hlogA_pos ((1 - p.κ) / 2))
      rw [Real.log_rpow hlogA_pos] at hconc
      have hmul := mul_le_mul_of_nonneg_left hconc (show 0 ≤ 2 / (1 - p.κ) by positivity)
      have hrew : (2 / (1 - p.κ)) * (((1 - p.κ) / 2) * Real.log (Real.log A)) = Real.log (Real.log A) := by
        field_simp [ne_of_gt h1κ]
      have hdist : (2 / (1 - p.κ)) * ((Real.log A) ^ ((1 - p.κ) / 2) - 1) =
          (2 / (1 - p.κ)) * (Real.log A) ^ ((1 - p.κ) / 2) - 2 / (1 - p.κ) := by ring
      have hpos2 : 0 < 2 / (1 - p.κ) := by positivity
      linarith
    have hhalf_ge : (2 * C_plus ^ p.μ_K + 1) * (2 / (1 - p.κ)) ≤ (Real.log A) ^ ((1 - p.κ) / 2) := by
      have h1 : ((2 * C_plus ^ p.μ_K + 1) * (2 / (1 - p.κ))) ^ (2 / (1 - p.κ)) ≤ Real.log A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hlogA_ge_B)
      have hpos : 0 < (2 * C_plus ^ p.μ_K + 1) * (2 / (1 - p.κ)) := by
        have := Real.rpow_pos_of_pos hCp_pos p.μ_K; positivity
      have := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hpos _)) h1 (show 0 ≤ (1 - p.κ) / 2 by linarith)
      rw [← Real.rpow_mul (le_of_lt hpos)] at this
      have hexp : (2 / (1 - p.κ)) * ((1 - p.κ) / 2) = 1 := by field_simp [ne_of_gt h1κ]
      rwa [hexp, Real.rpow_one] at this
    have hsq_eq : (Real.log A) ^ ((1 - p.κ) / 2) * (Real.log A) ^ ((1 - p.κ) / 2) =
        (Real.log A) ^ (1 - p.κ) := by
      rw [← Real.rpow_add hlogA_pos]; congr 1; ring
    have hratio_le : C_plus ^ p.μ_K * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hlogA_pow_pos]
      have h1 : C_plus ^ p.μ_K * Real.log (Real.log A) ≤
          C_plus ^ p.μ_K * ((2 / (1 - p.κ)) * (Real.log A) ^ ((1 - p.κ) / 2)) :=
        mul_le_mul_of_nonneg_left hlog_sub (le_of_lt (Real.rpow_pos_of_pos hCp_pos _))
      have h2 : C_plus ^ p.μ_K * (2 / (1 - p.κ)) ≤ (Real.log A) ^ ((1 - p.κ) / 2) := by
        have hpos_c : 0 < 2 / (1 - p.κ) := by positivity
        have hpos_p : 0 < C_plus ^ p.μ_K := Real.rpow_pos_of_pos hCp_pos _
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.rpow_pos_of_pos hlogA_pos ((1 - p.κ) / 2)))
      linarith
    have hpow_le : Δ_cand ^ p.μ_K ≤ 1 := by
      dsimp [Δ_cand]
      rw [Real.mul_rpow (le_of_lt hCp_pos) (le_of_lt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
          ← Real.rpow_mul (le_of_lt (div_pos hloglogA_pos hlogA_pow_pos)),
          one_div_mul_cancel (ne_of_gt p.hμ_K_pos), Real.rpow_one]
      exact hratio_le
    by_contra hgt
    push Not at hgt
    have : 1 < Δ_cand ^ p.μ_K := Real.one_lt_rpow hgt p.hμ_K_pos
    linarith
  -- (3) Evaluar el balance en Δ_cand
  have hgain : K_coef * Real.log (Real.log A) ≤
      (Δ_cand / D) ^ p.μ_K * (c_lo * (Real.log A) ^ (1 - p.κ) - C_lo) := by
    have hΔD : (Δ_cand / D) ^ p.μ_K = (2 * K_coef / c_lo) * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) := by
      have hdiv : Δ_cand / D = (2 * K_coef / c_lo) ^ (1 / p.μ_K) *
          (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K) := by
        dsimp [Δ_cand, C_plus]; field_simp [ne_of_gt hD]
      rw [hdiv,
          Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
            (le_of_lt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (le_of_lt (div_pos hloglogA_pos hlogA_pow_pos)),
          one_div_mul_cancel (ne_of_gt p.hμ_K_pos), Real.rpow_one, Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_left hclo_half (le_of_lt (Real.rpow_pos_of_pos (div_pos hΔ_pos hD) p.μ_K))
    rw [hΔD] at hmul ⊢
    have hsimp : (2 * K_coef / c_lo) * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) *
        ((c_lo / 2) * (Real.log A) ^ (1 - p.κ)) = K_coef * Real.log (Real.log A) := by
      field_simp [ne_of_gt hclo, ne_of_gt hlogA_pow_pos]
    linarith
  have hlogΔ : Real.log Δ_cand = Real.log C_plus +
      (1 / p.μ_K) * (Real.log (Real.log (Real.log A)) - (1 - p.κ) * Real.log (Real.log A)) := by
    dsimp [Δ_cand]
    rw [Real.log_mul (ne_of_gt hCp_pos) (ne_of_gt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
        Real.log_rpow (div_pos hloglogA_pos hlogA_pow_pos),
        Real.log_div (ne_of_gt hloglogA_pos) (ne_of_gt hlogA_pow_pos),
        Real.log_rpow hlogA_pos]
  have hlog3_nn : 0 ≤ Real.log (Real.log (Real.log A)) := Real.log_nonneg (by linarith)
  have hcost_ge : (p.η / (1 - p.β)) * Real.log Δ_cand ≥
      -(p.η / (1 - p.β)) * |Real.log C_plus| - (p.η / ((1 - p.β) * p.μ_K)) * Real.log (Real.log A) := by
    rw [hlogΔ]
    have h1 : -|Real.log C_plus| ≤ Real.log C_plus := neg_abs_le _
    have h2 : (1 - p.κ) * Real.log (Real.log A) ≤ Real.log (Real.log A) := by
      have := p.hκ_pos; nlinarith
    have h3 : -(1 / p.μ_K) * Real.log (Real.log A) ≤
        (1 / p.μ_K) * (Real.log (Real.log (Real.log A)) - (1 - p.κ) * Real.log (Real.log A)) := by
      have : -Real.log (Real.log A) ≤ Real.log (Real.log (Real.log A)) - (1 - p.κ) * Real.log (Real.log A) := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left this (le_of_lt (div_pos one_pos p.hμ_K_pos))
      linarith
    have hηβ : 0 ≤ p.η / (1 - p.β) := div_nonneg (le_of_lt p.hη0) (le_of_lt h1β)
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h1 h3) hηβ
    have hrew : (p.η / (1 - p.β)) * (-|Real.log C_plus| + -(1 / p.μ_K) * Real.log (Real.log A)) =
        -(p.η / (1 - p.β)) * |Real.log C_plus| - (p.η / ((1 - p.β) * p.μ_K)) * Real.log (Real.log A) := by
      field_simp [ne_of_gt h1β, ne_of_gt p.hμ_K_pos]; ring
    linarith
  refine ⟨hΔ_pos, hΔ_le1, ?_⟩
  have hCext : C_ext ≤ |C_ext| := le_abs_self C_ext
  have hCpol : C_pol ≤ |C_pol| := le_abs_self C_pol
  have hnet_coef : 1 ≤ K_coef - p.η / ((1 - p.β) * p.μ_K) := by
    dsimp [K_coef]; have := p.hη0; have := p.hμ_K_pos; linarith [div_pos p.hη0 (mul_pos h1β p.hμ_K_pos)]
  have hnet_gain : M_const ≤ (K_coef - p.η / ((1 - p.β) * p.μ_K)) * Real.log (Real.log A) := by
    nlinarith
  dsimp [M_const] at hnet_gain
  linarith

/-! ## 4. Pieza 3: Coordenada cuadrática $\phi(x) = x - C x^2$ y cota inferior rigurosa de $\Delta_k(A)$ -/

/-- Constante cuadrática exacta $C_{\text{sub}} = \frac{M}{\lambda_K (\lambda_K - 1)}$ para $\phi(x) = x - C x^2$. -/
noncomputable def C_sub (M : ℝ) : ℝ := M / (p.lamK * (p.lamK - 1))

/-- Coordenada sub-linealizada $\phi(x) = x - C x^2$. -/
def phi_coord (C x : ℝ) : ℝ := x - C * x ^ 2

/-- Cancelación algebraica exacta del término $x^2$ (Pieza 3):
    $\phi(\lambda_K x + M x^2) - \lambda_K \phi(x) = -2 C \lambda_K M x^3 - C M^2 x^4 \le 0$ para todo $x \ge 0$. -/
theorem phi_sublinear_exact {M x : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) :
    let C := p.C_sub M
    phi_coord C (p.lamK * x + M * x ^ 2) ≤ p.lamK * phi_coord C x := by
  intro C
  have hden : p.lamK * (p.lamK - 1) ≠ 0 :=
    ne_of_gt (mul_pos p.hlamK_pos (by linarith [p.hlamK_gt1]))
  have hCM : C * (p.lamK * (p.lamK - 1)) = M := by
    dsimp [C, C_sub]; exact div_mul_cancel₀ M hden
  have hid : phi_coord C (p.lamK * x + M * x ^ 2) - p.lamK * phi_coord C x =
      (M - C * (p.lamK * (p.lamK - 1))) * x ^ 2 - 2 * C * p.lamK * M * x ^ 3 - C * M ^ 2 * x ^ 4 := by
    unfold phi_coord; ring
  rw [hCM, sub_self, zero_mul, zero_sub] at hid
  have hC_nn : 0 ≤ C := div_nonneg hM (le_of_lt (mul_pos p.hlamK_pos (by linarith [p.hlamK_gt1])))
  have hlam_nn : 0 ≤ p.lamK := le_of_lt p.hlamK_pos
  have hrem : 0 ≤ 2 * C * p.lamK * M * x ^ 3 + C * M ^ 2 * x ^ 4 := by positivity
  linarith

/-- Paso de contracción en la coordenada $\phi$ (sin derivadas):
    si $0 \le x_{t+1} \le u_1 - c_t$ con $u_1 = \lambda_K x_t + M x_t^2 \le \frac{1}{4 C}$, entonces
    $\phi(x_{t+1}) \le \lambda_K \phi(x_t) - \frac{1}{2} c_t$. -/
theorem phi_step_budget {M x_t x_next c_t : ℝ} (hM : 0 < M)
    (hxt : 0 ≤ x_t) (hxn : 0 ≤ x_next) (hc : 0 ≤ c_t)
    (hdyn : x_next ≤ p.lamK * x_t + M * x_t ^ 2 - c_t)
    (hcap : p.lamK * x_t + M * x_t ^ 2 ≤ 1 / (4 * p.C_sub M)) :
    phi_coord (p.C_sub M) x_next ≤ p.lamK * phi_coord (p.C_sub M) x_t - (1 / 2) * c_t := by
  set C := p.C_sub M
  have hC_pos : 0 < C := div_pos hM (mul_pos p.hlamK_pos (by linarith [p.hlamK_gt1]))
  set u₁ := p.lamK * x_t + M * x_t ^ 2
  have hu₁_ge : x_next + c_t ≤ u₁ := by linarith
  have hu₁_ge_xn : x_next ≤ u₁ := by linarith
  -- Identidad sin derivadas: φ(u₁) - φ(x_next) = (u₁ - x_next) * (1 - C * (u₁ + x_next)) ≥ (1/2) * c_t
  have hdiff_id : phi_coord C u₁ - phi_coord C x_next =
      (u₁ - x_next) * (1 - C * (u₁ + x_next)) := by unfold phi_coord; ring
  have hsum_le : C * (u₁ + x_next) ≤ 1 / 2 := by
    have h1 : u₁ + x_next ≤ 2 / (4 * C) := by
      have : 1 / (4 * C) + 1 / (4 * C) = 2 / (4 * C) := by ring
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hC_pos)
    have hrew : C * (2 / (4 * C)) = 1 / 2 := by field_simp [ne_of_gt hC_pos]; ring
    linarith
  have hphi_drop : (1 / 2) * c_t ≤ phi_coord C u₁ - phi_coord C x_next := by
    rw [hdiff_id]
    have h1 : c_t ≤ u₁ - x_next := by linarith
    have h2 : 1 / 2 ≤ 1 - C * (u₁ + x_next) := by linarith
    have hmul := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  have hsub := p.phi_sublinear_exact (le_of_lt hM) hxt
  linarith

/-- Presupuesto telescópico de la Pieza 3:
    toda trayectoria factible con $x_0 = \Delta_k$, $0 \le x_t \le \epsilon$ para $t < T$, $x_T \ge \epsilon$
    y $\lambda_K \epsilon + M \epsilon^2 \le \frac{1}{4 C}$ satisface
    $\frac{1}{2} \sum_{t < T} c_t / \lambda_K^{t+1} \le \phi(\Delta_k) - \phi(\epsilon) / \lambda_K^T \le \Delta_k - \phi(\epsilon) / \lambda_K^T$. -/
theorem piece3_telescoping_budget {M ε Δk : ℝ} (hM : 0 < M) (hε : 0 < ε) (hΔ : 0 < Δk)
    (hcap : p.lamK * ε + M * ε ^ 2 ≤ 1 / (4 * p.C_sub M))
    (T : ℕ) (hT : 0 < T) (x c : ℕ → ℝ)
    (hx0 : x 0 = Δk) (hxT : ε ≤ x T)
    (hx_nn : ∀ t ≤ T, 0 ≤ x t)
    (hx_stay : ∀ t < T, x t ≤ ε)
    (hc_pos : ∀ t < T, 0 < c t)
    (hdyn : ∀ t < T, x (t + 1) ≤ p.lamK * x t + M * (x t) ^ 2 - c t) :
    let C := p.C_sub M
    (1 / 2) * (∑ t ∈ range T, c t / p.lamK ^ (t + 1)) ≤
      Δk - phi_coord C ε / p.lamK ^ T ∧
    0 < phi_coord C ε ∧
    phi_coord C ε / Δk < p.lamK ^ T ∧
    p.β ^ T ≤ (Δk / phi_coord C ε) ^ p.μ_K := by
  intro C
  have hC_pos : 0 < C := div_pos hM (mul_pos p.hlamK_pos (by linarith [p.hlamK_gt1]))
  -- Telescoping en φ(x_t) / lamK^t
  have hstep_div : ∀ t < T,
      (1 / 2) * (c t / p.lamK ^ (t + 1)) ≤
        phi_coord C (x t) / p.lamK ^ t - phi_coord C (x (t + 1)) / p.lamK ^ (t + 1) := by
    intro t ht
    have hxt_cap : p.lamK * x t + M * (x t) ^ 2 ≤ 1 / (4 * C) := by
      have hle := hx_stay t ht
      have hnn := hx_nn t (le_of_lt ht)
      have h1 : p.lamK * x t ≤ p.lamK * ε := mul_le_mul_of_nonneg_left hle (le_of_lt p.hlamK_pos)
      have h2 : M * (x t) ^ 2 ≤ M * ε ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hle 2) (le_of_lt hM)
      linarith
    have hbud := p.phi_step_budget hM (hx_nn t (le_of_lt ht)) (hx_nn (t + 1) ht)
      (le_of_lt (hc_pos t ht)) (hdyn t ht) hxt_cap
    have hdiv := div_le_div_of_nonneg_right hbud (le_of_lt (pow_pos p.hlamK_pos (t + 1)))
    have hrew1 : (p.lamK * phi_coord C (x t) - 1 / 2 * c t) / p.lamK ^ (t + 1) =
        phi_coord C (x t) / p.lamK ^ t - (1 / 2) * (c t / p.lamK ^ (t + 1)) := by
      rw [pow_succ]; field_simp [ne_of_gt (pow_pos p.hlamK_pos t), ne_of_gt p.hlamK_pos]
    linarith
  have htel : (1 / 2) * (∑ t ∈ range T, c t / p.lamK ^ (t + 1)) ≤
      phi_coord C (x 0) - phi_coord C (x T) / p.lamK ^ T := by
    have hsum := Finset.sum_le_sum fun t ht => hstep_div t (Finset.mem_range.mp ht)
    rw [← Finset.mul_sum] at hsum
    have hcol : ∑ t ∈ range T,
        (phi_coord C (x t) / p.lamK ^ t - phi_coord C (x (t + 1)) / p.lamK ^ (t + 1)) =
        phi_coord C (x 0) / p.lamK ^ 0 - phi_coord C (x T) / p.lamK ^ T :=
      telescope_sum (fun t => phi_coord C (x t) / p.lamK ^ t) T
    rw [hcol, pow_zero, div_one] at hsum
    exact hsum
  -- Mostrar φ(ε) ≤ φ(x T) usando que x T ≤ lamK ε + M ε^2 ≤ 1 / (4 C) y φ es creciente en [0, 1/(2C)]
  have hxT_le : x T ≤ 1 / (4 * C) := by
    have hTm1 : T - 1 < T := Nat.sub_lt hT one_pos
    have hdyn_last := hdyn (T - 1) hTm1
    have hrew : T - 1 + 1 = T := Nat.sub_add_cancel hT
    rw [hrew] at hdyn_last
    have hle := hx_stay (T - 1) hTm1
    have hnn := hx_nn (T - 1) (le_of_lt hTm1)
    have h1 : p.lamK * x (T - 1) ≤ p.lamK * ε := mul_le_mul_of_nonneg_left hle (le_of_lt p.hlamK_pos)
    have h2 : M * (x (T - 1)) ^ 2 ≤ M * ε ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hle 2) (le_of_lt hM)
    have hc_last := hc_pos (T - 1) hTm1
    linarith
  have hphi_xT_ge : phi_coord C ε ≤ phi_coord C (x T) := by
    have hid : phi_coord C (x T) - phi_coord C ε = (x T - ε) * (1 - C * (x T + ε)) := by
      unfold phi_coord; ring
    have hε_le : ε ≤ 1 / (4 * C) := by
      have : ε ≤ p.lamK * ε + M * ε ^ 2 := by nlinarith [p.hlamK_gt1, mul_nonneg (le_of_lt hM) (sq_nonneg ε)]
      linarith
    have hsum_le : C * (x T + ε) ≤ 1 / 2 := by
      have h1 : x T + ε ≤ 2 / (4 * C) := by
        have : 1 / (4 * C) + 1 / (4 * C) = 2 / (4 * C) := by ring
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hC_pos)
      have hrew : C * (2 / (4 * C)) = 1 / 2 := by field_simp [ne_of_gt hC_pos]; ring
      linarith
    have hnn : 0 ≤ (x T - ε) * (1 - C * (x T + ε)) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hphi_Δ_le : phi_coord C Δk ≤ Δk := by
    unfold phi_coord; have : 0 ≤ C * Δk ^ 2 := by positivity
    linarith
  have hbud_main : (1 / 2) * (∑ t ∈ range T, c t / p.lamK ^ (t + 1)) ≤
      Δk - phi_coord C ε / p.lamK ^ T := by
    rw [hx0] at htel
    have hdiv := div_le_div_of_nonneg_right hphi_xT_ge (le_of_lt (pow_pos p.hlamK_pos T))
    linarith
  have hphi_ε_pos : 0 < phi_coord C ε := by
    unfold phi_coord
    have hε_le : ε ≤ 1 / (4 * C) := by
      have : ε ≤ p.lamK * ε + M * ε ^ 2 := by nlinarith [p.hlamK_gt1, mul_nonneg (le_of_lt hM) (sq_nonneg ε)]
      linarith [p.hlamK_gt1, mul_nonneg (le_of_lt hM) (sq_nonneg ε)]
    have hCε : C * ε ≤ 1 / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hε_le (le_of_lt hC_pos)
      have hrew : C * (1 / (4 * C)) = 1 / 4 := by field_simp [ne_of_gt hC_pos]
      linarith
    have hrew : ε - C * ε ^ 2 = ε * (1 - C * ε) := by ring
    rw [hrew]; exact mul_pos hε (by linarith)
  have hsum_pos : 0 < ∑ t ∈ range T, c t / p.lamK ^ (t + 1) := by
    have h0 : 0 ∈ range T := Finset.mem_range.mpr hT
    have hterm_nn : ∀ t ∈ range T, 0 ≤ c t / p.lamK ^ (t + 1) := fun t ht =>
      div_nonneg (le_of_lt (hc_pos t (Finset.mem_range.mp ht))) (le_of_lt (pow_pos p.hlamK_pos _))
    have h0_pos : 0 < c 0 / p.lamK ^ (0 + 1) := div_pos (hc_pos 0 hT) (pow_pos p.hlamK_pos 1)
    exact lt_of_lt_of_le h0_pos (Finset.single_le_sum hterm_nn h0)
  have hlamT_gt : phi_coord C ε / Δk < p.lamK ^ T := by
    rw [div_lt_iff₀ hΔ]
    have h1 : phi_coord C ε / p.lamK ^ T < Δk := by linarith
    have := (div_lt_iff₀ (pow_pos p.hlamK_pos T)).mp h1
    linarith
  have hβT_le : p.β ^ T ≤ (Δk / phi_coord C ε) ^ p.μ_K := by
    rw [p.beta_pow_eq_rpow_muK T]
    have hinv : (p.lamK ^ T) ^ (-p.μ_K) = ((p.lamK ^ T)⁻¹) ^ p.μ_K := by
      rw [Real.rpow_neg (le_of_lt (pow_pos p.hlamK_pos T)), Real.inv_rpow (le_of_lt (pow_pos p.hlamK_pos T))]
    rw [hinv]
    apply Real.rpow_le_rpow (inv_nonneg.mpr (le_of_lt (pow_pos p.hlamK_pos T))) _ (le_of_lt p.hμ_K_pos)
    rw [← one_div, div_le_div_iff₀ (pow_pos p.hlamK_pos T) hphi_ε_pos]
    have := (div_lt_iff₀ hΔ).mp hlamT_gt
    linarith
  exact ⟨hbud_main, hphi_ε_pos, hlamT_gt, hβT_le⟩

/-- **Corolario gratis del término $t = 0$ de la Pieza 3**:
    $c_0 \le 2 \lambda_K \Delta_k$ sin usar ecuaciones de Euler. -/
theorem piece3_c0_bound {Δk : ℝ} {T : ℕ} (hT : 0 < T) (c : ℕ → ℝ)
    (hc_nn : ∀ t < T, 0 ≤ c t)
    (hbud : (1 / 2) * (∑ t ∈ range T, c t / p.lamK ^ (t + 1)) ≤ Δk) :
    c 0 ≤ 2 * p.lamK * Δk := by
  have h0 : 0 ∈ range T := Finset.mem_range.mpr hT
  have hle := Finset.single_le_sum (f := fun t => c t / p.lamK ^ (t + 1))
    (fun t ht => div_nonneg (hc_nn t (Finset.mem_range.mp ht)) (le_of_lt (pow_pos p.hlamK_pos _))) h0
  rw [zero_add, pow_one] at hle
  have h1 : c 0 / p.lamK ≤ 2 * Δk := by linarith
  have := (div_le_iff₀ p.hlamK_pos).mp h1
  linarith

/-- Cota superior de la suma logarítmica en la Pieza 3 vía `Real.log_le_sub_one_of_pos` (sin Jensen):
    si $\frac{1}{2} \sum_{t < T} c_t / \lambda_K^{t+1} \le \Delta_k$, entonces
    $\sum_{t < T} \beta^t \eta \log c_t \le \frac{\eta (1 - \beta^T)}{1 - \beta} \log \Delta_k + C_2$. -/
theorem piece3_log_sum_upper {Δk : ℝ} (hΔ : 0 < Δk) {T : ℕ} (hT : 0 < T) (c : ℕ → ℝ)
    (hc_pos : ∀ t < T, 0 < c t)
    (hbud : (1 / 2) * (∑ t ∈ range T, c t / p.lamK ^ (t + 1)) ≤ Δk) :
    ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (c t)) ≤
      (p.η * (1 - p.β ^ T) / (1 - p.β)) * Real.log Δk +
      (p.η / (1 - p.β) * |Real.log (2 * p.lamK)| +
       p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)|) := by
  have h1β : 0 < 1 - p.β := by linarith [p.hβ1]
  have hβT_lt1 : p.β ^ T < 1 := pow_lt_one₀ (le_of_lt p.hβ0) p.hβ1 (ne_of_gt hT)
  have h1βT : 0 < 1 - p.β ^ T := by linarith
  -- Punto de tangencia óptimo w_t = 2 Δk * ((1 - β) / (1 - β^T)) * lamK * (β lamK)^t
  let w : ℕ → ℝ := fun t =>
    2 * Δk * ((1 - p.β) / (1 - p.β ^ T)) * p.lamK * (p.β * p.lamK) ^ t
  have hw_pos : ∀ t, 0 < w t := by
    intro t; dsimp [w]; have := p.hlamK_pos; have := p.hβ0; positivity
  have hlog_le : ∀ t < T,
      Real.log (c t) ≤ Real.log (w t) + c t / w t - 1 := by
    intro t ht
    have hconc := Real.log_le_sub_one_of_pos (div_pos (hc_pos t ht) (hw_pos t))
    rw [Real.log_div (ne_of_gt (hc_pos t ht)) (ne_of_gt (hw_pos t))] at hconc
    linarith
  have hsum_le : ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (c t)) ≤
      ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log (w t) + c t / w t - 1)) :=
    Finset.sum_le_sum fun t ht =>
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hlog_le t (Finset.mem_range.mp ht)) (le_of_lt p.hη0))
        (pow_nonneg (le_of_lt p.hβ0) t)
  have hgeom : ∑ t ∈ range T, p.β ^ t = (1 - p.β ^ T) / (1 - p.β) := by
    have hid := geom_sum_eq p.β T
    exact eq_div_of_mul_eq (ne_of_gt h1β) hid
  -- El residuo ∑ β^t (c_t / w_t - 1) ≤ 0 exactamente por la restricción presupuestaria
  have hrem_np : ∑ t ∈ range T, p.β ^ t * (c t / w t - 1) ≤ 0 := by
    have hterm : ∀ t, p.β ^ t * (c t / w t) =
        ((1 - p.β ^ T) / (2 * Δk * (1 - p.β))) * (c t / p.lamK ^ (t + 1)) := by
      intro t; dsimp [w]; rw [pow_succ, mul_pow]
      have hβt : p.β ^ t ≠ 0 := ne_of_gt (pow_pos p.hβ0 t)
      have hlamt : p.lamK ^ t ≠ 0 := ne_of_gt (pow_pos p.hlamK_pos t)
      have hlam1 : p.lamK ≠ 0 := ne_of_gt p.hlamK_pos
      field_simp [hβt, hlamt, hlam1, ne_of_gt hΔ, ne_of_gt h1β, ne_of_gt h1βT]
    have hsplit : ∑ t ∈ range T, p.β ^ t * (c t / w t - 1) =
        (∑ t ∈ range T, p.β ^ t * (c t / w t)) - ∑ t ∈ range T, p.β ^ t := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => by ring
    rw [hsplit]
    simp_rw [hterm, ← Finset.mul_sum, hgeom]
    have hsum_c : ∑ t ∈ range T, c t / p.lamK ^ (t + 1) ≤ 2 * Δk := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsum_c
      (div_nonneg (le_of_lt h1βT) (by positivity : 0 ≤ 2 * Δk * (1 - p.β)))
    have hrew : (1 - p.β ^ T) / (2 * Δk * (1 - p.β)) * (2 * Δk) = (1 - p.β ^ T) / (1 - p.β) := by
      field_simp [ne_of_gt hΔ, ne_of_gt h1β]
    linarith
  -- Evaluar ∑ β^t log(w_t): notar que (1 - β) / (1 - β^T) ≤ 1 ⇒ log((1-β)/(1-β^T)) ≤ 0
  have hlogw : ∀ t, Real.log (w t) ≤
      Real.log Δk + Real.log (2 * p.lamK) + (t : ℝ) * Real.log (p.β * p.lamK) := by
    intro t; dsimp [w]
    have hfrac_le1 : (1 - p.β) / (1 - p.β ^ T) ≤ 1 := by
      rw [div_le_one h1βT]
      have : p.β ^ T ≤ p.β := by
        calc p.β ^ T ≤ p.β ^ 1 := pow_le_pow_of_le_one (le_of_lt p.hβ0) (le_of_lt p.hβ1) hT
          _ = p.β := pow_one _
      linarith
    have hle : 2 * Δk * ((1 - p.β) / (1 - p.β ^ T)) * p.lamK * (p.β * p.lamK) ^ t ≤
        Δk * (2 * p.lamK) * (p.β * p.lamK) ^ t := by
      have hnn : 0 ≤ 2 * Δk * p.lamK * (p.β * p.lamK) ^ t := by
        have := p.hlamK_pos; have := p.hβ0; positivity
      have := mul_le_mul_of_nonneg_right hfrac_le1 hnn
      linarith
    have h1 := Real.log_le_log (hw_pos t) hle
    have hpos1 : 0 < 2 * p.lamK := by linarith [p.hlamK_pos]
    have hpos2 : 0 < (p.β * p.lamK) ^ t := pow_pos (mul_pos p.hβ0 p.hlamK_pos) t
    rw [Real.log_mul (ne_of_gt (mul_pos hΔ hpos1)) (ne_of_gt hpos2),
        Real.log_mul (ne_of_gt hΔ) (ne_of_gt hpos1), Real.log_pow] at h1
    exact h1
  have hsum_w : ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (w t)) ≤
      (p.η * (1 - p.β ^ T) / (1 - p.β)) * Real.log Δk +
      (p.η / (1 - p.β) * |Real.log (2 * p.lamK)| +
       p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)|) := by
    have h1 : ∑ t ∈ range T, p.β ^ t * (p.η * Real.log (w t)) ≤
        ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log Δk + Real.log (2 * p.lamK) +
          (t : ℝ) * Real.log (p.β * p.lamK))) :=
      Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlogw t) (le_of_lt p.hη0))
          (pow_nonneg (le_of_lt p.hβ0) t)
    have hexp : ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log Δk + Real.log (2 * p.lamK) +
          (t : ℝ) * Real.log (p.β * p.lamK))) =
        (p.η * (1 - p.β ^ T) / (1 - p.β)) * Real.log Δk +
        (p.η * (1 - p.β ^ T) / (1 - p.β)) * Real.log (2 * p.lamK) +
        p.η * (∑ t ∈ range T, (t : ℝ) * p.β ^ t) * Real.log (p.β * p.lamK) := by
      have hrew : ∀ t : ℕ, p.β ^ t * (p.η * (Real.log Δk + Real.log (2 * p.lamK) +
            (t : ℝ) * Real.log (p.β * p.lamK))) =
          p.β ^ t * (p.η * Real.log Δk) + p.β ^ t * (p.η * Real.log (2 * p.lamK)) +
          ((t : ℝ) * p.β ^ t) * (p.η * Real.log (p.β * p.lamK)) := fun t => by ring
      simp_rw [hrew]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hgeom]
      ring
    have hfrac_le : (1 - p.β ^ T) / (1 - p.β) ≤ 1 / (1 - p.β) :=
      div_le_div_of_nonneg_right (by linarith [pow_nonneg (le_of_lt p.hβ0) T]) (le_of_lt h1β)
    have ht2 : (p.η * (1 - p.β ^ T) / (1 - p.β)) * Real.log (2 * p.lamK) ≤
        p.η / (1 - p.β) * |Real.log (2 * p.lamK)| := by
      have ha : Real.log (2 * p.lamK) ≤ |Real.log (2 * p.lamK)| := le_abs_self _
      have hnn : 0 ≤ p.η * (1 - p.β ^ T) / (1 - p.β) := by have := p.hη0; positivity
      have hb := mul_le_mul_of_nonneg_left ha hnn
      have hc := mul_le_mul_of_nonneg_right hfrac_le (abs_nonneg (Real.log (2 * p.lamK)))
      have hd := mul_le_mul_of_nonneg_left hc (le_of_lt p.hη0)
      have hrew1 : p.η * (1 - p.β ^ T) / (1 - p.β) * |Real.log (2 * p.lamK)| =
          p.η * ((1 - p.β ^ T) / (1 - p.β) * |Real.log (2 * p.lamK)|) := by ring
      have hrew2 : p.η * (1 / (1 - p.β) * |Real.log (2 * p.lamK)|) =
          p.η / (1 - p.β) * |Real.log (2 * p.lamK)| := by ring
      linarith
    have ht3 : p.η * (∑ t ∈ range T, (t : ℝ) * p.β ^ t) * Real.log (p.β * p.lamK) ≤
        p.η * (p.β / (1 - p.β) ^ 2) * |Real.log (p.β * p.lamK)| := by
      have hs_nn : 0 ≤ ∑ t ∈ range T, (t : ℝ) * p.β ^ t :=
        Finset.sum_nonneg fun t _ => mul_nonneg (Nat.cast_nonneg t) (pow_nonneg (le_of_lt p.hβ0) t)
      have ha : Real.log (p.β * p.lamK) ≤ |Real.log (p.β * p.lamK)| := le_abs_self _
      have hb := mul_le_mul_of_nonneg_left ha (mul_nonneg (le_of_lt p.hη0) hs_nn)
      have hc := mul_le_mul_of_nonneg_right (p.sum_mul_beta_pow_le T) (abs_nonneg (Real.log (p.β * p.lamK)))
      have hd := mul_le_mul_of_nonneg_left hc (le_of_lt p.hη0)
      have hrew1 : p.η * (1 - p.β ^ T) / (1 - p.β) * |Real.log (2 * p.lamK)| =
          p.η * ((1 - p.β ^ T) / (1 - p.β) * |Real.log (2 * p.lamK)|) := by ring
      have hrew2 : p.η * (1 / (1 - p.β) * |Real.log (2 * p.lamK)|) =
          p.η / (1 - p.β) * |Real.log (2 * p.lamK)| := by ring
      linarith
    linarith
  have hsplit2 : ∑ t ∈ range T, p.β ^ t * (p.η * (Real.log (w t) + c t / w t - 1)) =
      (∑ t ∈ range T, p.β ^ t * (p.η * Real.log (w t))) +
      p.η * (∑ t ∈ range T, p.β ^ t * (c t / w t - 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => by ring
  have hηrem : p.η * (∑ t ∈ range T, p.β ^ t * (c t / w t - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt p.hη0) hrem_np
  linarith

/-- Inversión algebraica de la Pieza 3 (cota inferior rigurosa de $\Delta_k(A)$):
    de la desigualdad de indiferencia
    $\frac{\eta}{1-\beta} \log(1/\Delta_k) - C_3 \le (\Delta_k / \phi_\epsilon)^{\mu_K} (c_{\text{hi}} (\log A)^{1-\kappa} + C_{\text{hi}})$
    se deduce para todo $A$ suficientemente grande:
    $C_- \left(\frac{\log\log A}{(\log A)^{1-\kappa}}\right)^{1/\mu_K} \le \Delta_k$. -/
theorem piece3_delta_k_lower {φ_ε c_hi C_hi C₃ : ℝ}
    (hφε : 0 < φ_ε) (hchi : 0 < c_hi) :
    ∃ A₃ ≥ Real.exp (Real.exp 2), ∃ C_minus > 0, ∀ A ≥ A₃, ∀ Δk > 0,
      (p.η / (1 - p.β)) * Real.log (1 / Δk) - C₃ ≤
        (Δk / φ_ε) ^ p.μ_K * (c_hi * (Real.log A) ^ (1 - p.κ) + C_hi) →
      C_minus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K) ≤ Δk := by
  have h1β : 0 < 1 - p.β := by linarith [p.hβ1]
  have h1κ : 0 < 1 - p.κ := by linarith [p.hκ_lt1]
  -- Elegimos C_minus tal que (C_minus / φ_ε)^μ_K * (2 * c_hi) = (η * (1 - κ)) / (4 * (1 - β) * μ_K)
  set L_coef : ℝ := p.η * (1 - p.κ) / (4 * (1 - p.β) * p.μ_K)
  have hL_pos : 0 < L_coef := by
    dsimp [L_coef]; have := p.hη0; have := p.hμ_K_pos; positivity
  set C_minus : ℝ := φ_ε * (L_coef / (2 * c_hi)) ^ (1 / p.μ_K)
  have hCm_pos : 0 < C_minus := mul_pos hφε (Real.rpow_pos_of_pos (by positivity) _)
  -- Tomamos A₃ tal que:
  -- (1) c_hi * (log A)^(1 - κ) + C_hi ≤ 2 * c_hi * (log A)^(1 - κ)
  -- (2) (η / ((1 - β) * μ_K)) * log(log(log A)) ≤ L_coef * log(log A)
  -- (3) |C₃| + (η / (1 - β)) * |log C_minus| + 1 ≤ L_coef * log(log A)
  -- (porque L_coef = (1/4) * (η (1-κ) / ((1-β) μ_K)), luego 4 * L_coef - L_coef - L_coef - L_coef = L_coef > 0!)
  set M_lo : ℝ := (|C₃| + (p.η / (1 - p.β)) * |Real.log C_minus| + 1) / L_coef
  set M_log3 : ℝ := (p.η / ((1 - p.β) * p.μ_K)) / L_coef
  set B_logA : ℝ := max (Real.exp (max 2 (max M_lo (4 * M_log3 ^ 2 + 1))))
    (((|C_hi| + 1) / c_hi) ^ (1 / (1 - p.κ)))
  refine ⟨Real.exp (max (Real.exp 2) B_logA),
    Real.exp_le_exp.mpr (le_max_left _ _), C_minus, hCm_pos, fun A hA Δk hΔ0 hind => ?_⟩
  have hlogA_ge : max (Real.exp 2) B_logA ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos _) hA; rwa [Real.log_exp] at this
  have hlogA_ge_e2 : Real.exp 2 ≤ Real.log A := le_trans (le_max_left _ _) hlogA_ge
  have hlogA_ge_B : B_logA ≤ Real.log A := le_trans (le_max_right _ _) hlogA_ge
  have hlogA_pos : 0 < Real.log A := lt_of_lt_of_le (Real.exp_pos 2) hlogA_ge_e2
  have hloglogA_ge : max 2 (max M_lo (4 * M_log3 ^ 2 + 1)) ≤ Real.log (Real.log A) := by
    have h1 : Real.exp (max 2 (max M_lo (4 * M_log3 ^ 2 + 1))) ≤ Real.log A :=
      le_trans (le_max_left _ _) hlogA_ge_B
    have := Real.log_le_log (Real.exp_pos _) h1; rwa [Real.log_exp] at this
  have hloglogA_ge2 : 2 ≤ Real.log (Real.log A) := le_trans (le_max_left _ _) hloglogA_ge
  have hloglogA_pos : 0 < Real.log (Real.log A) := by linarith
  have hlogA_pow_pos : 0 < (Real.log A) ^ (1 - p.κ) := Real.rpow_pos_of_pos hlogA_pos _
  -- Por contradicción: si Δk < Δ_lo := C_minus * (...)^(1/μ_K)
  set Δ_lo : ℝ := C_minus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K)
  have hΔlo_pos : 0 < Δ_lo := mul_pos hCm_pos (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)
  by_contra hlt
  push Not at hlt
  -- (1) RHS ≤ (Δ_lo / φ_ε)^μ_K * (2 * c_hi * (log A)^(1 - κ)) = L_coef * log(log A)
  have hchi_2 : c_hi * (Real.log A) ^ (1 - p.κ) + C_hi ≤ 2 * c_hi * (Real.log A) ^ (1 - p.κ) := by
    have h1 : ((|C_hi| + 1) / c_hi) ^ (1 / (1 - p.κ)) ≤ Real.log A := le_trans (le_max_right _ _) hlogA_ge_B
    have hpos : 0 < (|C_hi| + 1) / c_hi := by positivity
    have h2 : (|C_hi| + 1) / c_hi ≤ (Real.log A) ^ (1 - p.κ) := by
      have := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hpos _)) h1 (le_of_lt h1κ)
      rwa [← Real.rpow_mul (le_of_lt hpos), one_div_mul_cancel (ne_of_gt h1κ), Real.rpow_one] at this
    have h3 : |C_hi| + 1 ≤ c_hi * (Real.log A) ^ (1 - p.κ) := by linarith [(div_le_iff₀ hchi).mp h2]
    have h4 : C_hi ≤ |C_hi| := le_abs_self C_hi
    linarith
  have hRHS_le : (Δk / φ_ε) ^ p.μ_K * (c_hi * (Real.log A) ^ (1 - p.κ) + C_hi) ≤
      L_coef * Real.log (Real.log A) := by
    have hpow_le : (Δk / φ_ε) ^ p.μ_K ≤ (Δ_lo / φ_ε) ^ p.μ_K :=
      Real.rpow_le_rpow (div_nonneg (le_of_lt hΔ0) (le_of_lt hφε))
        (div_le_div_of_nonneg_right (le_of_lt hlt) (le_of_lt hφε)) (le_of_lt p.hμ_K_pos)
    have hΔlo_pow : (Δ_lo / φ_ε) ^ p.μ_K = (L_coef / (2 * c_hi)) * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) := by
      have hdiv : Δ_lo / φ_ε = (L_coef / (2 * c_hi)) ^ (1 / p.μ_K) *
          (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K) := by
        dsimp [Δ_lo, C_minus]; field_simp [ne_of_gt hφε]
      rw [hdiv,
          Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
            (le_of_lt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (le_of_lt (div_pos hloglogA_pos hlogA_pow_pos)),
          one_div_mul_cancel (ne_of_gt p.hμ_K_pos), Real.rpow_one, Real.rpow_one]
    have h1 : (Δk / φ_ε) ^ p.μ_K * (c_hi * (Real.log A) ^ (1 - p.κ) + C_hi) ≤
        (Δ_lo / φ_ε) ^ p.μ_K * (2 * c_hi * (Real.log A) ^ (1 - p.κ)) := by
      by_cases hsign : 0 ≤ c_hi * (Real.log A) ^ (1 - p.κ) + C_hi
      · exact mul_le_mul hpow_le hchi_2 hsign (le_of_lt (Real.rpow_pos_of_pos (div_pos hΔlo_pos hφε) _))
      · have hneg : (Δk / φ_ε) ^ p.μ_K * (c_hi * (Real.log A) ^ (1 - p.κ) + C_hi) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.rpow_pos_of_pos (div_pos hΔ0 hφε) _)) (by linarith)
        have hpos_r : 0 ≤ (Δ_lo / φ_ε) ^ p.μ_K * (2 * c_hi * (Real.log A) ^ (1 - p.κ)) := by
          have := Real.rpow_pos_of_pos (div_pos hΔlo_pos hφε) p.μ_K; positivity
        linarith
    rw [hΔlo_pow] at h1
    have hsimp : (L_coef / (2 * c_hi)) * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) *
        (2 * c_hi * (Real.log A) ^ (1 - p.κ)) = L_coef * Real.log (Real.log A) := by
      field_simp [ne_of_gt hchi, ne_of_gt hlogA_pow_pos]
    linarith
  -- (2) LHS > L_coef * log(log A): como Δk < Δ_lo, log(1/Δk) > -log Δ_lo
  have hlog_inv : -Real.log Δ_lo < Real.log (1 / Δk) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_lt_log hΔ0 hlt]
  have hlogΔlo : Real.log Δ_lo = Real.log C_minus +
      (1 / p.μ_K) * (Real.log (Real.log (Real.log A)) - (1 - p.κ) * Real.log (Real.log A)) := by
    dsimp [Δ_lo]
    rw [Real.log_mul (ne_of_gt hCm_pos) (ne_of_gt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
        Real.log_rpow (div_pos hloglogA_pos hlogA_pow_pos),
        Real.log_div (ne_of_gt hloglogA_pos) (ne_of_gt hlogA_pow_pos),
        Real.log_rpow hlogA_pos]
  -- log(log(log A)) ≤ 2 * √(log(log A)) ≤ (L_coef / (η / ((1-β) μ_K))) * log(log A)
  have hlog3_le : (p.η / ((1 - p.β) * p.μ_K)) * Real.log (Real.log (Real.log A)) ≤
      L_coef * Real.log (Real.log A) := by
    have hsqrt : Real.log (Real.log (Real.log A)) ≤ 2 * Real.sqrt (Real.log (Real.log A)) := by
      have hs_pos : 0 < Real.sqrt (Real.log (Real.log A)) := Real.sqrt_pos.mpr hloglogA_pos
      have hconc := Real.log_le_sub_one_of_pos hs_pos
      rw [Real.log_sqrt (le_of_lt hloglogA_pos)] at hconc
      linarith
    have hM2 : 4 * M_log3 ^ 2 ≤ Real.log (Real.log A) := by
      have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hloglogA_ge)
      linarith
    have h2M : 2 * M_log3 ≤ Real.sqrt (Real.log (Real.log A)) := by
      have hM_nn : 0 ≤ M_log3 := by dsimp [M_log3]; have := p.hη0; have := p.hμ_K_pos; positivity
      have hsq : (2 * M_log3) ^ 2 ≤ (Real.sqrt (Real.log (Real.log A))) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hloglogA_pos)]; linarith
      nlinarith [Real.sqrt_nonneg (Real.log (Real.log A))]
    have hprod : 2 * M_log3 * Real.sqrt (Real.log (Real.log A)) ≤ Real.log (Real.log A) := by
      have h1 := mul_le_mul_of_nonneg_right h2M (Real.sqrt_nonneg (Real.log (Real.log A)))
      rwa [Real.mul_self_sqrt (le_of_lt hloglogA_pos)] at h1
    have h1 := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ p.η / ((1 - p.β) * p.μ_K) by
      have := p.hη0; have := p.hμ_K_pos; positivity)
    have hrew : (p.η / ((1 - p.β) * p.μ_K)) * (2 * Real.sqrt (Real.log (Real.log A))) =
        L_coef * (2 * M_log3 * Real.sqrt (Real.log (Real.log A))) := by
      dsimp [M_log3]; field_simp [ne_of_gt hL_pos]
    have h2 := mul_le_mul_of_nonneg_left hprod (le_of_lt hL_pos)
    linarith
  have hconst_le : |C₃| + (p.η / (1 - p.β)) * |Real.log C_minus| + 1 ≤ L_coef * Real.log (Real.log A) := by
    have h1 : M_lo ≤ Real.log (Real.log A) := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hloglogA_ge)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
    have hrew : L_coef * M_lo = |C₃| + (p.η / (1 - p.β)) * |Real.log C_minus| + 1 := by
      dsimp [M_lo]; field_simp [ne_of_gt hL_pos]
    linarith
  have h4L : 4 * L_coef = p.η * (1 - p.κ) / ((1 - p.β) * p.μ_K) := by
    dsimp [L_coef]; field_simp [ne_of_gt h1β, ne_of_gt p.hμ_K_pos]
  have hLHS_gt : L_coef * Real.log (Real.log A) < (p.η / (1 - p.β)) * Real.log (1 / Δk) - C₃ := by
    have h1 := mul_lt_mul_of_pos_left hlog_inv (div_pos p.hη0 h1β)
    rw [hlogΔlo] at h1
    have hC3 : C₃ ≤ |C₃| := le_abs_self C₃
    have hCm : Real.log C_minus ≤ |Real.log C_minus| := le_abs_self _
    have hηβ : 0 ≤ p.η / (1 - p.β) := div_nonneg (le_of_lt p.hη0) (le_of_lt h1β)
    have hCm_mul := mul_le_mul_of_nonneg_left hCm hηβ
    have hrew : (p.η / (1 - p.β)) * -(Real.log C_minus +
          1 / p.μ_K * (Real.log (Real.log (Real.log A)) - (1 - p.κ) * Real.log (Real.log A))) =
        (4 * L_coef) * Real.log (Real.log A) -
        (p.η / ((1 - p.β) * p.μ_K)) * Real.log (Real.log (Real.log A)) -
        (p.η / (1 - p.β)) * Real.log C_minus := by
      rw [h4L]; field_simp [ne_of_gt h1β, ne_of_gt p.hμ_K_pos]; ring
    have h4mul : (4 * L_coef) * Real.log (Real.log A) = 4 * (L_coef * Real.log (Real.log A)) := by ring
    have hL_nn : 0 ≤ L_coef * Real.log (Real.log A) := mul_nonneg (le_of_lt hL_pos) (le_of_lt hloglogA_pos)
    linarith
  linarith

/-! ## 5. Parte 2 (mitad "gratis"): Envolvente de Milgrom--Segal y cota superior de la brecha relativa -/

/-- **Parte 2 (cota superior de la brecha relativa vía Milgrom--Segal + $c_0 \le 2 \lambda_K \Delta_k$):**
    si $k_* < k_A^{\text{fix}} \le k_A = k_* + \Delta_k$ y sobre $[k_A^{\text{fix}}, k_A]$ se tiene
    $(v_{\text{surv}}^{\text{fix}})'(k) \ge \frac{\eta}{4 \Delta_k}$ (del término $t = 0$ de la Pieza 3)
    y $(v_{\text{ext}}^{\text{fix}})'(k) \le \frac{\eta}{8 \Delta_k}$, con $v_{\text{surv}}^{\text{fix}}(k_A^{\text{fix}}) = v_{\text{ext}}^{\text{fix}}(k_A^{\text{fix}})$
    y $v_{\text{surv}}^{\text{fix}}(k_A) - v_{\text{ext}}^{\text{fix}}(k_A) \le \Delta W_A^+$, entonces:
    $$\frac{k_A - k_A^{\text{fix}}}{k_A} \le \frac{8}{\eta k_*} \Delta_k \Delta W_A^+.$$ -/
theorem part2_free_relative_gap_bound {k_fix k_A Δk ΔW_plus : ℝ}
    (hk_fix_gt : p.k_star < k_fix) (hle : k_fix ≤ k_A) (hΔ : 0 < Δk)
    (v_surv v_ext v_surv' v_ext' : ℝ → ℝ)
    (hdiff_s : ∀ k ∈ Icc k_fix k_A, HasDerivAt v_surv (v_surv' k) k)
    (hdiff_e : ∀ k ∈ Icc k_fix k_A, HasDerivAt v_ext (v_ext' k) k)
    (hind_fix : v_surv k_fix = v_ext k_fix)
    (hgap_A : v_surv k_A - v_ext k_A ≤ ΔW_plus)
    (hslope_s : ∀ k ∈ Icc k_fix k_A, p.η / (4 * Δk) ≤ v_surv' k)
    (hslope_e : ∀ k ∈ Icc k_fix k_A, v_ext' k ≤ p.η / (8 * Δk)) :
    (k_A - k_fix) / k_A ≤ (8 / (p.η * p.k_star)) * Δk * ΔW_plus := by
  have hkA_gt : p.k_star < k_A := lt_of_lt_of_le hk_fix_gt hle
  have hkA_pos : 0 < k_A := lt_trans p.hk_star_pos hkA_gt
  by_cases heq : k_fix = k_A
  · subst heq
    have h0 : 0 ≤ ΔW_plus := by linarith
    rw [sub_self, zero_div]
    have := p.hη0; have := p.hk_star_pos; positivity
  · have hlt : k_fix < k_A := lt_of_le_of_ne hle heq
    let g : ℝ → ℝ := fun k => v_surv k - v_ext k
    have hg_cont : ContinuousOn g (Icc k_fix k_A) :=
      DifferentiableOn.continuousOn fun k hk =>
        ((hdiff_s k hk).sub (hdiff_e k hk)).differentiableAt.differentiableWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g (fun k => v_surv' k - v_ext' k) hlt
      hg_cont (fun k hk => (hdiff_s k (Ioo_subset_Icc_self hk)).sub (hdiff_e k (Ioo_subset_Icc_self hk)))
    have hξ_mem : ξ ∈ Icc k_fix k_A := Ioo_subset_Icc_self hξ
    have hgp_ge : p.η / (8 * Δk) ≤ v_surv' ξ - v_ext' ξ := by
      have hs := hslope_s ξ hξ_mem
      have he := hslope_e ξ hξ_mem
      have hdiff : p.η / (4 * Δk) - p.η / (8 * Δk) = p.η / (8 * Δk) := by
        field_simp [ne_of_gt hΔ]; ring
      linarith
    have hg_diff : g k_A - g k_fix = (v_surv' ξ - v_ext' ξ) * (k_A - k_fix) := by
      have := (eq_div_iff (ne_of_gt (sub_pos.mpr hlt))).mp hslope
      linarith
    have hg_fix : g k_fix = 0 := by dsimp [g]; linarith
    have hΔW_ge : (p.η / (8 * Δk)) * (k_A - k_fix) ≤ ΔW_plus := by
      have hmul := mul_le_mul_of_nonneg_right hgp_ge (le_of_lt (sub_pos.mpr hlt))
      dsimp [g] at hg_diff hg_fix hgap_A ⊢
      linarith
    have hnum : k_A - k_fix ≤ (8 / p.η) * Δk * ΔW_plus := by
      have h1 := mul_le_mul_of_nonneg_left hΔW_ge (show 0 ≤ 8 * Δk / p.η by have := p.hη0; positivity)
      have hrew : (8 * Δk / p.η) * ((p.η / (8 * Δk)) * (k_A - k_fix)) = k_A - k_fix := by
        field_simp [ne_of_gt p.hη0, ne_of_gt hΔ]
      have hrew2 : (8 * Δk / p.η) * ΔW_plus = (8 / p.η) * Δk * ΔW_plus := by ring
      linarith
    have hdiv1 : (k_A - k_fix) / k_A ≤ ((8 / p.η) * Δk * ΔW_plus) / k_A :=
      div_le_div_of_nonneg_right hnum (le_of_lt hkA_pos)
    have hΔW_nn : 0 ≤ ΔW_plus := le_trans (by have := p.hη0; positivity) hΔW_ge
    have hdiv2 : ((8 / p.η) * Δk * ΔW_plus) / k_A ≤ ((8 / p.η) * Δk * ΔW_plus) / p.k_star :=
      div_le_div_of_nonneg_left (by have := p.hη0; positivity) p.hk_star_pos (le_of_lt hkA_gt)
    have hrew3 : ((8 / p.η) * Δk * ΔW_plus) / p.k_star = (8 / (p.η * p.k_star)) * Δk * ΔW_plus := by
      field_simp [ne_of_gt p.hη0, ne_of_gt p.hk_star_pos]
    linarith

/-- Tasa exacta $\beta^{T + J} = O(\frac{\log\log A}{\log A})$ y producto $\Delta_k \cdot \beta^{T + J} =
    O\!\left(\frac{(\log\log A)^{1 + 1/\mu_K}}{(\log A)^{1 + (1-\kappa)/\mu_K}}\right)$ (Parte 2):
    combinación directa de las cotas de la Pieza 1, Pieza 2 y Pieza 3. -/
theorem part2_delta_W_plus_rate {A Δk φ_ε C_plus C_J : ℝ} {T J : ℕ}
    (hA : Real.exp (Real.exp 1) ≤ A) (hΔ0 : 0 < Δk) (hφε : 0 < φ_ε) (hCp : 0 < C_plus)
    (hΔ_ub : Δk ≤ C_plus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K))
    (hβT : p.β ^ T ≤ (Δk / φ_ε) ^ p.μ_K)
    (hJ_ge : Real.log (Real.log A) / Real.log p.θ - C_J ≤ (J : ℝ)) :
    p.β ^ (T + J) ≤ (C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J) * (Real.log (Real.log A) / Real.log A) ∧
    Δk * p.β ^ (T + J) ≤
      (C_plus * (C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J)) *
        ((Real.log (Real.log A)) ^ (1 + 1 / p.μ_K) /
         (Real.log A) ^ (1 + (1 - p.κ) / p.μ_K)) := by
  have hlogA_ge : Real.exp 1 ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos _) hA; rwa [Real.log_exp] at this
  have hlogA_pos : 0 < Real.log A := lt_of_lt_of_le (Real.exp_pos 1) hlogA_ge
  have hloglogA_ge1 : 1 ≤ Real.log (Real.log A) := by
    have := Real.log_le_log (Real.exp_pos 1) hlogA_ge; rwa [Real.log_exp] at this
  have hloglogA_pos : 0 < Real.log (Real.log A) := by linarith
  have hlogA_pow_pos : 0 < (Real.log A) ^ (1 - p.κ) := Real.rpow_pos_of_pos hlogA_pos _
  -- 1. Cota de β^T ≤ (C_plus / φ_ε)^μ_K * (log log A / (log A)^(1 - κ))
  have hβT_rate : p.β ^ T ≤
      (C_plus / φ_ε) ^ p.μ_K * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) := by
    have h1 : (Δk / φ_ε) ^ p.μ_K ≤
        ((C_plus / φ_ε) * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K)) ^ p.μ_K := by
      apply Real.rpow_le_rpow (div_nonneg (le_of_lt hΔ0) (le_of_lt hφε)) _ (le_of_lt p.hμ_K_pos)
      rw [← mul_div_right_comm]
      exact div_le_div_of_nonneg_right hΔ_ub (le_of_lt hφε)
    rw [Real.mul_rpow (le_of_lt (div_pos hCp hφε))
          (le_of_lt (Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) _)),
        ← Real.rpow_mul (le_of_lt (div_pos hloglogA_pos hlogA_pow_pos)),
        one_div_mul_cancel (ne_of_gt p.hμ_K_pos), Real.rpow_one] at h1
    exact le_trans hβT h1
  -- 2. Cota de β^J ≤ β^(-C_J) * (log A)^(-κ)
  have hβJ_rate : p.β ^ J ≤ p.β ^ (-C_J) * (Real.log A) ^ (-p.κ) := by
    have hL : p.β ^ J = Real.exp ((J : ℝ) * Real.log p.β) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos p.hβ0]; ring_nf
    have hR : p.β ^ (-C_J) * (Real.log A) ^ (-p.κ) =
        Real.exp ((-C_J) * Real.log p.β + (-p.κ) * Real.log (Real.log A)) := by
      rw [Real.exp_add, Real.rpow_def_of_pos p.hβ0, Real.rpow_def_of_pos hlogA_pos]; ring_nf
    rw [hL, hR]; apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_right hJ_ge (le_of_lt p.hlog_β_neg)
    have hrew : (Real.log (Real.log A) / Real.log p.θ - C_J) * Real.log p.β =
        (-C_J) * Real.log p.β + (-p.κ) * Real.log (Real.log A) := by
      unfold κ; field_simp [ne_of_gt p.hlog_θ_pos]; ring
    linarith
  -- 3. Producto β^(T + J) = β^T * β^J
  have hβTJ : p.β ^ (T + J) ≤
      (C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J) * (Real.log (Real.log A) / Real.log A) := by
    rw [pow_add]
    have hmul := mul_le_mul hβT_rate hβJ_rate (pow_nonneg (le_of_lt p.hβ0) J)
      (by have := Real.rpow_pos_of_pos (div_pos hCp hφε) p.μ_K; positivity)
    have hcomb : (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) * (Real.log A) ^ (-p.κ) =
        Real.log (Real.log A) / Real.log A := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (ne_of_gt hlogA_pow_pos) (ne_of_gt hlogA_pos)]
      have hexp : (Real.log A) ^ (-p.κ) * Real.log A = (Real.log A) ^ (1 - p.κ) := by
        nth_rw 2 [← Real.rpow_one (Real.log A)]
        rw [← Real.rpow_add hlogA_pos]; congr 1; ring
      have : Real.log (Real.log A) * (Real.log A) ^ (-p.κ) * Real.log A =
          Real.log (Real.log A) * ((Real.log A) ^ (-p.κ) * Real.log A) := by ring
      rw [this, hexp]
    have hrew : (C_plus / φ_ε) ^ p.μ_K * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) *
        (p.β ^ (-C_J) * (Real.log A) ^ (-p.κ)) =
        (C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J) * (Real.log (Real.log A) / Real.log A) := by
      rw [← hcomb]; ring
    linarith
  refine ⟨hβTJ, ?_⟩
  -- 4. Producto Δk * β^(T + J)
  have hprod := mul_le_mul hΔ_ub hβTJ (pow_nonneg (le_of_lt p.hβ0) (T + J))
    (by have := Real.rpow_pos_of_pos (div_pos hloglogA_pos hlogA_pow_pos) (1 / p.μ_K); positivity)
  have hpow_merge : (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K) *
      (Real.log (Real.log A) / Real.log A) =
      (Real.log (Real.log A)) ^ (1 + 1 / p.μ_K) / (Real.log A) ^ (1 + (1 - p.κ) / p.μ_K) := by
    rw [Real.div_rpow (le_of_lt hloglogA_pos) (le_of_lt hlogA_pow_pos),
        ← Real.rpow_mul (le_of_lt hlogA_pos), div_mul_div_comm]
    congr 1
    · rw [Real.rpow_add hloglogA_pos, Real.rpow_one]; ring
    · rw [Real.rpow_add hlogA_pos, Real.rpow_one, mul_one_div]; ring
  have hrew2 : C_plus * (Real.log (Real.log A) / (Real.log A) ^ (1 - p.κ)) ^ (1 / p.μ_K) *
      ((C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J) * (Real.log (Real.log A) / Real.log A)) =
      (C_plus * (C_plus / φ_ε) ^ p.μ_K * p.β ^ (-C_J)) *
        ((Real.log (Real.log A)) ^ (1 + 1 / p.μ_K) /
         (Real.log A) ^ (1 + (1 - p.κ) / p.μ_K)) := by
    rw [← hpow_merge]; ring
  linarith

end MVS.Theorem2.CESParams

namespace MVS.Theorem2SecondOrder

/-! ## 6. Constantes exactas de la calibración armónica (Tabla 3 y Observación 1) -/

theorem harmonic_second_order_exact_constants :
    MVS.Theorem2.CESParams.lamK harmonicBenchmark = 104 / 100 ∧
    MVS.Theorem2.CESParams.L_ss harmonicBenchmark = 7 / 9 := by
  unfold MVS.Theorem2.CESParams.lamK MVS.Theorem2.CESParams.L_ss CESParams.q CESParams.θ harmonicBenchmark
  norm_num

end MVS.Theorem2SecondOrder

