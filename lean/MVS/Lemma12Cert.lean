import MVS.Lemma12
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Lema 12 Certificado (`MVS.Lemma12Cert`): Cierre Completo de $[1/25000, 50]$ y Global $(0, \infty)$

Cierra el núcleo compacto $K \in [1/25000, 50]$ del Lema 12 mediante una partición
certificada de 131 segmentos racionales en 5 bandas:
- **Banda A** $[1/25000, 11/200]$ (17 segs): convexidad de $K \mapsto F(A_+, K, 1)$ (secante).
- **Banda B1** $[11/200, 1/4]$ (27 segs): monotonía en $K$ + `tangent_dominance` en $L$.
- **Banda B2** $[1/4, 31/20]$ (36 segs): concavidad en $K$ + `tangent_dominance` en $L$.
- **Banda C** $[31/20, 25]$ (49 segs): concavidad en $K$ + envolvente lineal a trozos en $L$.
- **Banda D** $[25, 50]$ (2 segs): concavidad de $K \mapsto F(A_+, K, 1)$ (tangente).

Combinado con `lemma12_global_super_barrier`, produce **`lemma12_global_certified`**:
$\Psi^\#$ es una super-barrera global de Bellman en todo $(0, \infty)$ para todo
$\theta \in \mathcal{P}$, sin `sorry` ni axiomas adicionales.
-/

open Real Set MVS.Theorem1 MVS.Proposition2 MVS.Lemma11 MVS.Lemma12

namespace MVS.Lemma12Cert

/-! ## 1. Lemas analíticos de convexidad, concavidad y secantes de $F_A(K, L)$ -/

lemma F_symm (A K L : ℝ) : F A K L = F A L K := by
  unfold F; dsimp only
  have : 2 * K * L / (K + L) = 2 * L * K / (L + K) := by ring_nf
  rw [this]

lemma FK_mono_l {A K l₁ l₂ : ℝ} (hA : 0 ≤ A) (hK : 0 < K) (hl₁ : 0 < l₁) (hle : l₁ ≤ l₂) :
    FK A l₁ K ≤ FK A l₂ K := by
  have hl₂ : 0 < l₂ := lt_of_lt_of_le hl₁ hle
  have hd₁ : 0 < K + l₁ := by linarith
  have hd₂ : 0 < K + l₂ := by linarith
  have hrat : l₁ / (K + l₁) ≤ l₂ / (K + l₂) := by
    rw [div_le_div_iff₀ hd₁ hd₂]; nlinarith
  have hr₁_nn : 0 ≤ l₁ / (K + l₁) := div_nonneg (le_of_lt hl₁) (le_of_lt hd₁)
  have hr₂_nn : 0 ≤ l₂ / (K + l₂) := div_nonneg (le_of_lt hl₂) (le_of_lt hd₂)
  have hsq : (l₁ / (K + l₁)) ^ 2 ≤ (l₂ / (K + l₂)) ^ 2 :=
    pow_le_pow_left₀ hr₁_nn hrat 2
  have hg_le : g l₁ K ≤ g l₂ K := by
    unfold g
    have : 2 * K * l₁ / (K + l₁) = 2 * K * (l₁ / (K + l₁)) := by ring
    have : 2 * K * l₂ / (K + l₂) = 2 * K * (l₂ / (K + l₂)) := by ring
    nlinarith
  have hsqrt : Real.sqrt (g l₁ K) ≤ Real.sqrt (g l₂ K) := Real.sqrt_le_sqrt hg_le
  have hprod : (l₁ / (K + l₁)) ^ 2 * Real.sqrt (g l₁ K) ≤
      (l₂ / (K + l₂)) ^ 2 * Real.sqrt (g l₂ K) :=
    mul_le_mul hsq hsqrt (Real.sqrt_nonneg _) (sq_nonneg _)
  unfold FK
  have hrew₁ : 3 * A * l₁ ^ 2 * Real.sqrt (g l₁ K) / (K + l₁) ^ 2 =
      (3 * A) * ((l₁ / (K + l₁)) ^ 2 * Real.sqrt (g l₁ K)) := by
    field_simp [ne_of_gt hd₁]
  have hrew₂ : 3 * A * l₂ ^ 2 * Real.sqrt (g l₂ K) / (K + l₂) ^ 2 =
      (3 * A) * ((l₂ / (K + l₂)) ^ 2 * Real.sqrt (g l₂ K)) := by
    field_simp [ne_of_gt hd₂]
  rw [hrew₁, hrew₂]
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- Cota secante desde el origen sin cálculo: para $0 \le x \le b \le l/2$ ($b > 0$),
    $F_A(x, l) \le (x / b) F_A(b, l)$. -/
theorem F_sec0_le {A l b x : ℝ} (hA : 0 ≤ A) (hl : 0 < l)
    (hb0 : 0 < b) (hbl : b ≤ l / 2) (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    F A x l ≤ (x / b) * F A b l := by
  by_cases hx : x = 0
  · subst hx; unfold F; simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hxl : 0 < x + l := by linarith
    have hblp : 0 < b + l := by linarith
    -- Basta probar x / (x + l)^3 ≤ b / (b + l)^3
    have hcube : x / (x + l) ^ 3 ≤ b / (b + l) ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hxl 3) (pow_pos hblp 3)]
      have hfac : b * (x + l) ^ 3 - x * (b + l) ^ 3 =
          (b - x) * (l ^ 3 - 3 * l * x * b - x * b * (x + b)) := by ring
      have hxb_le : x * b ≤ l ^ 2 / 4 := by nlinarith
      have hxb_sum : x + b ≤ l := by linarith
      have hterm1 : 3 * l * (x * b) ≤ 3 * l ^ 3 / 4 := by nlinarith
      have hterm2 : x * b * (x + b) ≤ l ^ 3 / 4 := by nlinarith
      have hbr : 0 ≤ l ^ 3 - 3 * l * x * b - x * b * (x + b) := by linarith
      have hdiff : 0 ≤ (b - x) * (l ^ 3 - 3 * l * x * b - x * b * (x + b)) :=
        mul_nonneg (by linarith) hbr
      linarith
    have hsq_le : (x * Real.sqrt (x / (x + l)) / (x + l)) ^ 2 ≤
        (x / b * (b * Real.sqrt (b / (b + l)) / (b + l))) ^ 2 := by
      have h1 : (x * Real.sqrt (x / (x + l)) / (x + l)) ^ 2 =
          x ^ 2 * (x / (x + l) ^ 3) := by
        rw [div_pow, mul_pow, Real.sq_sqrt (div_nonneg hx0 (le_of_lt hxl))]
        field_simp [ne_of_gt hxl]
      have h2 : (x / b * (b * Real.sqrt (b / (b + l)) / (b + l))) ^ 2 =
          x ^ 2 * (b / (b + l) ^ 3) := by
        rw [mul_pow, div_pow, div_pow, mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hb0) (le_of_lt hblp))]
        field_simp [ne_of_gt hb0, ne_of_gt hblp]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hcube (sq_nonneg x)
    have hnn_r : 0 ≤ x / b * (b * Real.sqrt (b / (b + l)) / (b + l)) := by positivity
    have hlin : x * Real.sqrt (x / (x + l)) / (x + l) ≤
        x / b * (b * Real.sqrt (b / (b + l)) / (b + l)) := by
      nlinarith [sq_nonneg (x * Real.sqrt (x / (x + l)) / (x + l) -
        x / b * (b * Real.sqrt (b / (b + l)) / (b + l)))]
    have hF_rew : ∀ y, 0 ≤ y → 0 < y + l →
        F A y l = (A * (2 * l) * Real.sqrt (2 * l)) * (y * Real.sqrt (y / (y + l)) / (y + l)) := by
      intro y hy hyl
      unfold F; dsimp only
      have hsplit : 2 * y * l / (y + l) = (2 * l) * (y / (y + l)) := by ring
      rw [hsplit, Real.sqrt_mul (by linarith)]
      ring
    rw [hF_rew x hx0 hxl, hF_rew b (le_of_lt hb0) hblp]
    have hC_nn : 0 ≤ A * (2 * l) * Real.sqrt (2 * l) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlin hC_nn
    linarith

/-- Convexidad de $K \mapsto F_A(K, l)$ en $(0, l/4]$: la secante domina en $[a, b]$. -/
theorem F_convex_secant_K {A l a b x : ℝ} (hA : 0 ≤ A) (hl : 0 < l)
    (ha : 0 < a) (hab : a < b) (hbl : b ≤ l / 4) (hx : x ∈ Icc a b) :
    F A x l ≤ ((b - x) * F A a l + (x - a) * F A b l) / (b - a) := by
  by_cases hxa : x = a
  · subst hxa; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring_nf; exact le_rfl
  by_cases hxb : x = b
  · subst hxb; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring_nf; exact le_rfl
  have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
  have hxb' : x < b := lt_of_le_of_ne hx.2 hxb
  -- FK es creciente en [a, b] pues FKK ≥ 0 en (0, l/4]
  have hFK_mono : MonotoneOn (FK A l) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact DifferentiableOn.continuousOn
        (fun t ht => (hasDerivAt_FK_K hl (lt_of_lt_of_le ha ht.1)).differentiableAt.differentiableWithinAt)
    · exact fun t ht =>
        (hasDerivAt_FK_K hl (lt_of_lt_of_le ha (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht'.1
      rw [(hasDerivAt_FK_K hl ht_pos).deriv]
      unfold FKK
      have hnum : 0 ≤ l - 4 * t := by linarith [ht'.2]
      have hg_pos : 0 < g l t := by unfold g; positivity
      have hsq_pos : 0 < Real.sqrt (g l t) := Real.sqrt_pos.mpr hg_pos
      have htl_pos : 0 < t + l := by linarith
      positivity
  -- TVM en [a, x] y [x, b]
  have hcont : ContinuousOn (fun t => F A t l) (Icc a b) :=
    DifferentiableOn.continuousOn
      (fun t ht => (hasDerivAt_F_K hl (lt_of_lt_of_le ha ht.1)).differentiableAt.differentiableWithinAt)
  obtain ⟨c₁, hc₁, hslope₁⟩ := exists_hasDerivAt_eq_slope (fun t => F A t l) (FK A l) hax
    (hcont.mono (Icc_subset_Icc_right (le_of_lt hxb')))
    (fun t ht => hasDerivAt_F_K hl (lt_trans ha ht.1))
  obtain ⟨c₂, hc₂, hslope₂⟩ := exists_hasDerivAt_eq_slope (fun t => F A t l) (FK A l) hxb'
    (hcont.mono (Icc_subset_Icc_left (le_of_lt hax)))
    (fun t ht => hasDerivAt_F_K hl (lt_trans (lt_trans ha hax) ht.1))
  have hc₁_mem : c₁ ∈ Icc a b := ⟨le_of_lt hc₁.1, le_of_lt (lt_trans hc₁.2 hxb')⟩
  have hc₂_mem : c₂ ∈ Icc a b := ⟨le_of_lt (lt_trans hax hc₂.1), le_of_lt hc₂.2⟩
  have hle_slope : (F A x l - F A a l) / (x - a) ≤ (F A b l - F A x l) / (b - x) := by
    rw [← hslope₁, ← hslope₂]
    exact hFK_mono hc₁_mem hc₂_mem (le_of_lt (lt_trans hc₁.2 hc₂.1))
  rw [div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hxb')] at hle_slope
  rw [le_div_iff₀ (sub_pos.mpr hab)]
  nlinarith

/-- Concavidad de $K \mapsto F_A(K, l)$ en $[l/4, \infty)$: la tangente en $k_0 \ge l/4$ domina. -/
theorem F_concave_tangent_K {A l k₀ K : ℝ} (hA : 0 ≤ A) (hl : 0 < l)
    (hk₀ : l / 4 ≤ k₀) (hK : k₀ ≤ K) :
    F A K l ≤ F A k₀ l + FK A l k₀ * (K - k₀) := by
  by_cases heq : k₀ = K
  · subst heq; simp
  have hlt : k₀ < K := lt_of_le_of_ne hK heq
  have hk₀_pos : 0 < k₀ := by linarith
  have hFK_anti : AntitoneOn (FK A l) (Icc k₀ K) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc k₀ K) ?_ ?_ ?_
    · exact DifferentiableOn.continuousOn
        (fun t ht => (hasDerivAt_FK_K hl (lt_of_lt_of_le hk₀_pos ht.1)).differentiableAt.differentiableWithinAt)
    · exact fun t ht =>
        (hasDerivAt_FK_K hl (lt_of_lt_of_le hk₀_pos (interior_subset ht).1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have ht_pos : 0 < t := lt_of_lt_of_le hk₀_pos ht'.1
      rw [(hasDerivAt_FK_K hl ht_pos).deriv]
      unfold FKK
      have hnum : l - 4 * t ≤ 0 := by linarith [ht'.1]
      have htop : 3 * A * l ^ 3 * (l - 4 * t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hnum
      have hg_pos : 0 < g l t := by unfold g; positivity
      have hden : 0 < Real.sqrt (g l t) * (t + l) ^ 4 :=
        mul_pos (Real.sqrt_pos.mpr hg_pos) (pow_pos (by linarith) 4)
      exact div_nonpos_of_nonpos_of_nonneg htop (le_of_lt hden)
  have hcont : ContinuousOn (fun t => F A t l) (Icc k₀ K) :=
    DifferentiableOn.continuousOn
      (fun t ht => (hasDerivAt_F_K hl (lt_of_lt_of_le hk₀_pos ht.1)).differentiableAt.differentiableWithinAt)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => F A t l) (FK A l) hlt hcont
    (fun t ht => hasDerivAt_F_K hl (lt_trans hk₀_pos ht.1))
  have hle : (F A K l - F A k₀ l) / (K - k₀) ≤ FK A l k₀ := by
    rw [← hslope]
    exact hFK_anti ⟨le_rfl, le_of_lt hlt⟩ ⟨le_of_lt hc.1, le_of_lt hc.2⟩ (le_of_lt hc.1)
  rw [div_le_iff₀ (sub_pos.mpr hlt)] at hle
  linarith

/-- Cota tangente uniforme en $K \ge k_L \ge 1/4$ para todo $L \in [0, 1]$. -/
theorem F_concave_tangent_K_all_L {kL K L : ℝ}
    (hkL : (1 / 4 : ℝ) ≤ kL) (hK : kL ≤ K) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    F A_max K L ≤ F A_max kL L + FK A_max 1 kL * (K - kL) := by
  have hA : 0 ≤ A_max := by unfold A_max; norm_num
  have hkL_pos : 0 < kL := by linarith
  by_cases hL : L = 0
  · subst hL
    have hF0 : ∀ x, F A_max x 0 = 0 := by intro x; unfold F; simp
    rw [hF0 K, hF0 kL]
    have hFK_nn : 0 ≤ FK A_max 1 kL := by
      unfold FK; positivity
    nlinarith
  · have hL_pos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    have htan := F_concave_tangent_K hA hL_pos (by linarith : L / 4 ≤ kL) hK
    have hmono := FK_mono_l hA hkL_pos hL_pos hL1
    have hmul := mul_le_mul_of_nonneg_right hmono (show 0 ≤ K - kL by linarith)
    linarith

/-- Versiones simétricas en $L$ (por `F_symm`). -/
theorem F_sec0_le_L {K Lb L : ℝ} (hK : 0 < K) (hLb0 : 0 < Lb) (hLb : Lb ≤ K / 2)
    (hL0 : 0 ≤ L) (hL : L ≤ Lb) :
    F A_max K L ≤ (L / Lb) * F A_max K Lb := by
  rw [F_symm A_max K L, F_symm A_max K Lb]
  exact F_sec0_le (by unfold A_max; norm_num) hK hLb0 hLb hL0 hL

theorem F_convex_secant_L {K La Lb L : ℝ} (hK : 0 < K) (hLa : 0 < La) (hLab : La < Lb)
    (hLb : Lb ≤ K / 4) (hL : L ∈ Icc La Lb) :
    F A_max K L ≤ ((Lb - L) * F A_max K La + (L - La) * F A_max K Lb) / (Lb - La) := by
  rw [F_symm A_max K L, F_symm A_max K La, F_symm A_max K Lb]
  exact F_convex_secant_K (by unfold A_max; norm_num) hK hLa hLab hLb hL

theorem F_concave_tangent_L {K La L : ℝ} (hK : 0 < K) (hLa : K / 4 ≤ La) (hL : La ≤ L) :
    F A_max K L ≤ F A_max K La + t_gen A_max La K * (L - La) := by
  have ht_eq : t_gen A_max La K = FK A_max K La := by
    unfold t_gen FK g
    have : 2 * K * La / (K + La) = 2 * La * K / (La + K) := by ring_nf
    have hadd : (K + La) ^ 2 = (La + K) ^ 2 := by ring
    rw [this, hadd]
  rw [F_symm A_max K L, F_symm A_max K La, ht_eq]
  exact F_concave_tangent_K (by unfold A_max; norm_num) hK hLa hL

/-! ## 2. Certificador racional de $\log$ ($s = 4, N = 2$) y cota afín de $\log(1 - L)$ -/

def pow16 (r : ℚ) : ℚ :=
  let r2 := r * r
  let r4 := r2 * r2
  let r8 := r4 * r4
  r8 * r8

lemma pow16_cast (r : ℚ) : ((pow16 r : ℚ) : ℝ) = ((r : ℝ)) ^ 16 := by
  unfold pow16; dsimp only; push_cast; ring

def atanh2_ub (z : ℚ) : ℚ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / (5 * (1 - z ^ 2)))

def atanh2_lb (z : ℚ) : ℚ :=
  2 * (z + z ^ 3 / 3)

lemma atanh2_lb_cast (z : ℚ) : ((atanh2_lb z : ℚ) : ℝ) = atanhSeries 2 (z : ℝ) := by
  unfold atanh2_lb atanhSeries
  simp [Finset.sum_range_succ]
  ring

lemma atanh2_ub_cast (z : ℚ) :
    ((atanh2_ub z : ℚ) : ℝ) = atanhSeries 2 (z : ℝ) + atanhRemUB 2 (z : ℝ) := by
  unfold atanh2_ub atanhSeries atanhRemUB
  simp [Finset.sum_range_succ]
  ring

def log_ub_val (r : ℚ) (ge1 : Bool) : ℚ :=
  let z := (r - 1) / (r + 1)
  if ge1 then 16 * atanh2_ub z else -16 * atanh2_lb z

def log_ub_ok (x r : ℚ) (ge1 : Bool) : Prop :=
  1 ≤ r ∧ 0 < x ∧ (if ge1 then x ≤ pow16 r else x * pow16 r ≤ 1)

def log_ub_le1_val (r : ℚ) : ℚ :=
  let z := (r - 1) / (r + 1);
  -16 * atanh2_lb z

def log_ub_le1_ok (x r : ℚ) : Prop :=
  1 ≤ r ∧ 0 < x ∧ x * pow16 r ≤ 1

theorem log_ub_sound {x r : ℚ} {ge1 : Bool} (hok : log_ub_ok x r ge1) :
    Real.log (x : ℝ) ≤ (log_ub_val r ge1 : ℝ) := by
  rcases hok with ⟨hr, hx, hpow⟩
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hrb := log_bounds_of_ge_one 2 hrR
  have hz : (((r - 1) / (r + 1) : ℚ) : ℝ) = ((r : ℝ) - 1) / ((r : ℝ) + 1) := by push_cast; ring
  cases ge1 with
  | true =>
    simp only [ite_true] at hpow
    have hpowR : (x : ℝ) ≤ (r : ℝ) ^ 16 := by
      have : (x : ℝ) ≤ ((pow16 r : ℚ) : ℝ) := by exact_mod_cast hpow
      rwa [pow16_cast] at this
    have hlog := Real.log_le_log hxR hpowR
    rw [Real.log_pow] at hlog
    push_cast at hlog
    unfold log_ub_val; simp only [ite_true]; push_cast
    rw [atanh2_ub_cast, hz]
    linarith [hrb.2]
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hpow
    have hpowR : (x : ℝ) * (r : ℝ) ^ 16 ≤ 1 := by
      have : ((x * pow16 r : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hpow
      push_cast at this; rwa [pow16_cast] at this
    have hinv : (r : ℝ) ^ 16 ≤ (x : ℝ)⁻¹ := by
      rw [← one_div, le_div_iff₀ hxR]
      linarith
    have hlog := Real.log_le_log (pow_pos (by linarith) 16) hinv
    rw [Real.log_pow, Real.log_inv] at hlog
    push_cast at hlog
    unfold log_ub_val; simp only [Bool.false_eq_true, ite_false]; push_cast
    rw [atanh2_lb_cast, hz]
    linarith [hrb.1]

theorem log_ub_le1_sound {x r : ℚ} (hok : log_ub_le1_ok x r) :
    Real.log (x : ℝ) ≤ (log_ub_le1_val r : ℝ) := by
  have h := log_ub_sound (x := x) (r := r) (ge1 := false) hok
  simpa [log_ub_val, log_ub_le1_val] using h

/-- Cota afín global de $\log(1 - L)$ en cualquier ancla $L_* \in [0, 1)$. -/
lemma log_one_sub_le_tangent {L Lstar : ℝ} (hL1 : L < 1) (hLs1 : Lstar < 1) :
    Real.log (1 - L) ≤ Real.log (1 - Lstar) - (L - Lstar) / (1 - Lstar) := by
  have h1 : 0 < 1 - L := by linarith
  have h2 : 0 < 1 - Lstar := by linarith
  have hconc := Real.log_le_sub_one_of_pos (div_pos h1 h2)
  rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2)] at hconc
  have hrew : (1 - L) / (1 - Lstar) - 1 = -((L - Lstar) / (1 - Lstar)) := by
    field_simp [ne_of_gt h2]; ring
  linarith

/-- Máximo de una función bilineal en $(L, \eta) \in [L_L, L_R] \times [\eta_-, \eta_+]$
    alcanzado en las 4 esquinas. -/
lemma bilinear_le_four_corners {A B C D LL LR L ηMin ηMax η M : ℝ}
    (hL : L ∈ Icc LL LR) (hη : η ∈ Icc ηMin ηMax)
    (h1 : A + B * LL + (1 - ηMin) * (C + D * LL) ≤ M)
    (h2 : A + B * LR + (1 - ηMin) * (C + D * LR) ≤ M)
    (h3 : A + B * LL + (1 - ηMax) * (C + D * LL) ≤ M)
    (h4 : A + B * LR + (1 - ηMax) * (C + D * LR) ≤ M) :
    A + B * L + (1 - η) * (C + D * L) ≤ M := by
  -- Primero acotamos en L ∈ [LL, LR] para η fijo (es afín en L)
  have h_at_LL : A + B * LL + (1 - η) * (C + D * LL) ≤ M := by
    rcases le_total (C + D * LL) 0 with hle | hge
    · have := mul_le_mul_of_nonpos_right (show 1 - ηMax ≤ 1 - η by linarith [hη.2]) hle
      linarith
    · have := mul_le_mul_of_nonneg_right (show 1 - η ≤ 1 - ηMin by linarith [hη.1]) hge
      linarith
  have h_at_LR : A + B * LR + (1 - η) * (C + D * LR) ≤ M := by
    rcases le_total (C + D * LR) 0 with hle | hge
    · have := mul_le_mul_of_nonpos_right (show 1 - ηMax ≤ 1 - η by linarith [hη.2]) hle
      linarith
    · have := mul_le_mul_of_nonneg_right (show 1 - η ≤ 1 - ηMin by linarith [hη.1]) hge
      linarith
  -- Ahora acotamos en L ∈ [LL, LR] por afinidad en L
  have hrew : ∀ x, A + B * x + (1 - η) * (C + D * x) =
      (A + (1 - η) * C) + (B + (1 - η) * D) * x := fun x => by ring
  rw [hrew L]
  rw [hrew LL] at h_at_LL
  rw [hrew LR] at h_at_LR
  rcases le_total (B + (1 - η) * D) 0 with hle | hge
  · have := mul_le_mul_of_nonpos_left hL.1 hle; linarith
  · have := mul_le_mul_of_nonneg_left hL.2 hge; linarith

/-! ## 3. Constantes racionales y núcleo común de eliminación de $K'$ -/

def q_Amax : ℚ := 751 / 1000
def q_qmax : ℚ := 9201 / 10000
def q_bmin : ℚ := 9699 / 10000
def q_bmax : ℚ := 9701 / 10000
def q_emin : ℚ := 6999 / 10000
def q_emax : ℚ := 7001 / 10000
def q_C0 : ℚ := 185 / 10 + 10 / 301

lemma q_consts_cast :
    (q_Amax : ℝ) = A_max ∧ (q_qmax : ℝ) = q_max ∧ (q_bmin : ℝ) = beta_min ∧
    (q_bmax : ℝ) = beta_max ∧ (q_emin : ℝ) = eta_min ∧ (q_emax : ℝ) = eta_max ∧
    (q_C0 : ℝ) = C0_psi := by
  unfold q_Amax q_qmax q_bmin q_bmax q_emin q_emax q_C0
    A_max q_max beta_min beta_max eta_min eta_max C0_psi
  push_cast; refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def g_q (l k : ℚ) : ℚ := 2 * k * l / (k + l)

def slope_q (s0 : ℚ) : ℚ := 4 / 10 + 5 / (2 * s0 ^ 3)
def lam_max_q (s0 : ℚ) : ℚ := q_bmax * slope_q s0
def c0_ub_q (s0 : ℚ) : ℚ := q_emax / (q_bmin * slope_q s0)

def const_base_q (s0 r_c0 : ℚ) (ge1 : Bool) : ℚ :=
  let Lc := log_ub_val r_c0 ge1
  (if Lc - 1 ≤ 0 then q_emin else q_emax) * (Lc - 1) -
    q_bmin * (15 / (2 * s0) + q_C0) + q_C0

lemma bellman_base_step (θ : Params) {K K' L : ℝ} {s0 r_c0 : ℚ} {ge1 : Bool}
    (hK : 0 < K) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K')
    (hs0 : 0 < s0) (hlog : log_ub_ok (c0_ub_q s0) r_c0 ge1) :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' - Psi_sharp K ≤
      (const_base_q s0 r_c0 ge1 : ℝ) +
      ((lam_max_q s0 : ℝ) * q_max - 4 / 10) * K + 5 / Real.sqrt K +
      (lam_max_q s0 : ℝ) * F A_max K L + (1 - θ.η) * Real.log (1 - L) := by
  have hs0R : (0 : ℝ) < (s0 : ℝ) := by exact_mod_cast hs0
  have hbel := bellman_elim_Kp θ hK hK' hL hs0R hc
  set sl : ℝ := (4 / 10 : ℝ) + 5 / (2 * (s0 : ℝ) ^ 3)
  have hsl_eq : (slope_q s0 : ℝ) = sl := by unfold slope_q; dsimp [sl]; push_cast; ring
  have hsl_pos : 0 < sl := by dsimp [sl]; positivity
  have hβ_pos : 0 < θ.β := lt_of_lt_of_le (by unfold beta_min; norm_num) θ.hβ.1
  have hη_pos : 0 < θ.η := lt_of_lt_of_le (by unfold eta_min; norm_num) θ.hη.1
  have hlam_le : θ.β * sl ≤ (lam_max_q s0 : ℝ) := by
    unfold lam_max_q; push_cast; rw [q_consts_cast.2.2.2.1, hsl_eq]
    exact mul_le_mul_of_nonneg_right θ.hβ.2 (le_of_lt hsl_pos)
  have hc0_le : θ.η / (θ.β * sl) ≤ (c0_ub_q s0 : ℝ) := by
    unfold c0_ub_q; push_cast
    rw [q_consts_cast.2.2.2.2.2.1, q_consts_cast.2.2.1, hsl_eq]
    have hden_le : beta_min * sl ≤ θ.β * sl :=
      mul_le_mul_of_nonneg_right θ.hβ.1 (le_of_lt hsl_pos)
    exact div_le_div₀ (by unfold eta_max; norm_num) θ.hη.2
      (mul_pos (by unfold beta_min; norm_num) hsl_pos) hden_le
  have hlogc0 : Real.log (θ.η / (θ.β * sl)) ≤ (log_ub_val r_c0 ge1 : ℝ) :=
    le_trans (Real.log_le_log (div_pos hη_pos (mul_pos hβ_pos hsl_pos)) hc0_le)
      (log_ub_sound hlog)
  have hη_term : θ.η * (Real.log (θ.η / (θ.β * sl)) - 1) ≤
      ((if log_ub_val r_c0 ge1 - 1 ≤ 0 then q_emin else q_emax : ℚ) : ℝ) *
        ((log_ub_val r_c0 ge1 : ℝ) - 1) := by
    have h1 : θ.η * (Real.log (θ.η / (θ.β * sl)) - 1) ≤
        θ.η * ((log_ub_val r_c0 ge1 : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hη_pos)
    by_cases hsign : log_ub_val r_c0 ge1 - 1 ≤ 0
    · simp only [hsign, ite_true]
      rw [q_consts_cast.2.2.2.2.1]
      have hsignR : (log_ub_val r_c0 ge1 : ℝ) - 1 ≤ 0 := by exact_mod_cast hsign
      have h2 := mul_le_mul_of_nonpos_right θ.hη.1 hsignR
      linarith
    · simp only [hsign, ite_false]
      rw [q_consts_cast.2.2.2.2.2.1]
      have hsignR : 0 ≤ (log_ub_val r_c0 ge1 : ℝ) - 1 := by
        have : ¬ ((log_ub_val r_c0 ge1 : ℝ) - 1 ≤ 0) := by exact_mod_cast hsign
        linarith
      have h2 := mul_le_mul_of_nonneg_right θ.hη.2 hsignR
      linarith
  have hβ_term : (q_bmin : ℝ) * (15 / (2 * (s0 : ℝ)) + C0_psi) ≤
      θ.β * (15 / (2 * (s0 : ℝ)) + C0_psi) := by
    rw [q_consts_cast.2.2.1]
    have hpos : 0 ≤ 15 / (2 * (s0 : ℝ)) + C0_psi := by unfold C0_psi; positivity
    exact mul_le_mul_of_nonneg_right θ.hβ.1 hpos
  have hF_nn : 0 ≤ F A_max K L := by
    unfold F A_max; dsimp only
    have hL0 : 0 ≤ L := hL.1
    have hg : 0 ≤ 2 * K * L / (K + L) := div_nonneg (by positivity) (by linarith)
    positivity
  have hqK_nn : 0 ≤ q_max * K + F A_max K L := by
    have hq_nn : 0 ≤ q_max := by unfold q_max; norm_num
    exact add_nonneg (mul_nonneg hq_nn (le_of_lt hK)) hF_nn
  have hlam_term : θ.β * sl * (q_max * K + F A_max K L) ≤
      (lam_max_q s0 : ℝ) * (q_max * K + F A_max K L) :=
    mul_le_mul_of_nonneg_right hlam_le hqK_nn
  have hcb : (const_base_q s0 r_c0 ge1 : ℝ) =
      ((if log_ub_val r_c0 ge1 - 1 ≤ 0 then q_emin else q_emax : ℚ) : ℝ) *
        ((log_ub_val r_c0 ge1 : ℝ) - 1) -
      (q_bmin : ℝ) * (15 / (2 * (s0 : ℝ)) + C0_psi) + C0_psi := by
    unfold const_base_q; dsimp only; push_cast; rw [q_consts_cast.2.2.2.2.2.2]
  rw [Psi_sharp_eq K, hcb]
  dsimp only at hbel
  linarith

lemma sqrt_lb_sound {k sk : ℚ} (hsk : 0 < sk) (hsq : sk ^ 2 ≤ k) :
    5 / Real.sqrt (k : ℝ) ≤ 5 / (sk : ℝ) := by
  have hskR : (0 : ℝ) < (sk : ℝ) := by exact_mod_cast hsk
  have hsqR : (sk : ℝ) ^ 2 ≤ (k : ℝ) := by exact_mod_cast hsq
  have hk_nn : 0 ≤ (k : ℝ) := le_trans (sq_nonneg _) hsqR
  have hle : (sk : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have h2 : (sk : ℝ) ^ 2 ≤ (Real.sqrt (k : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hk_nn]; exact hsqR
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  exact div_le_div_of_nonneg_left (by norm_num) hskR hle

lemma sqrt_ub_sound {x sg : ℚ} (hsg : 0 ≤ sg) (hsq : x ≤ sg ^ 2) :
    Real.sqrt (x : ℝ) ≤ (sg : ℝ) := by
  have hsgR : (0 : ℝ) ≤ (sg : ℝ) := by exact_mod_cast hsg
  have hsqR : (x : ℝ) ≤ (sg : ℝ) ^ 2 := by exact_mod_cast hsq
  by_cases hx : 0 ≤ (x : ℝ)
  · have h2 : (Real.sqrt (x : ℝ)) ^ 2 ≤ (sg : ℝ) ^ 2 := by rw [Real.sq_sqrt hx]; exact hsqR
    nlinarith [Real.sqrt_nonneg (x : ℝ)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]; exact hsgR

def L_corner (lam_max a0 a1 log1mL Lstar eta L : ℚ) : ℚ :=
  lam_max * (a0 + a1 * L) + (1 - eta) * (log1mL - (L - Lstar) / (1 - Lstar))

def L_affine_ok (lam_max a0 a1 LL LR Lstar rL bound : ℚ) : Prop :=
  0 ≤ Lstar ∧ Lstar < 1 ∧ log_ub_le1_ok (1 - Lstar) rL ∧
  let log1mL := log_ub_le1_val rL
  L_corner lam_max a0 a1 log1mL Lstar q_emin LL ≤ bound ∧
  L_corner lam_max a0 a1 log1mL Lstar q_emin LR ≤ bound ∧
  L_corner lam_max a0 a1 log1mL Lstar q_emax LL ≤ bound ∧
  L_corner lam_max a0 a1 log1mL Lstar q_emax LR ≤ bound

lemma L_affine_sound (θ : Params) {lam_max a0 a1 LL LR Lstar rL bound : ℚ} {L : ℝ}
    (hL : L ∈ Icc (LL : ℝ) (LR : ℝ)) (hL1 : L < 1)
    (hok : L_affine_ok lam_max a0 a1 LL LR Lstar rL bound) :
    (lam_max : ℝ) * ((a0 : ℝ) + (a1 : ℝ) * L) + (1 - θ.η) * Real.log (1 - L) ≤ (bound : ℝ) := by
  rcases hok with ⟨_, hLs1, hlogok, h1, h2, h3, h4⟩
  have hLs1R : (Lstar : ℝ) < 1 := by exact_mod_cast hLs1
  have h1mη : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
  have htan := log_one_sub_le_tangent hL1 hLs1R
  have hlog := log_ub_le1_sound hlogok
  have hlogR : Real.log (1 - (Lstar : ℝ)) ≤ (log_ub_le1_val rL : ℝ) := by
    have : ((1 - Lstar : ℚ) : ℝ) = 1 - (Lstar : ℝ) := by push_cast; ring
    rwa [← this]
  have hstep : (1 - θ.η) * Real.log (1 - L) ≤
      (1 - θ.η) * ((log_ub_le1_val rL : ℝ) - (L - (Lstar : ℝ)) / (1 - (Lstar : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) h1mη
  -- Reescribir en la forma A + B * L + (1 - η) * (C + D * L)
  set C : ℝ := (log_ub_le1_val rL : ℝ) + (Lstar : ℝ) / (1 - (Lstar : ℝ))
  set D : ℝ := -(1 / (1 - (Lstar : ℝ)))
  have hCD : ∀ x : ℝ, (log_ub_le1_val rL : ℝ) - (x - (Lstar : ℝ)) / (1 - (Lstar : ℝ)) =
      C + D * x := by
    intro x; dsimp [C, D]; ring
  have hcorner : ∀ (e x : ℚ),
      L_corner lam_max a0 a1 (log_ub_le1_val rL) Lstar e x ≤ bound →
      (lam_max : ℝ) * (a0 : ℝ) + ((lam_max : ℝ) * (a1 : ℝ)) * (x : ℝ) +
        (1 - (e : ℝ)) * (C + D * (x : ℝ)) ≤ (bound : ℝ) := by
    intro e x hle
    have hR : (L_corner lam_max a0 a1 (log_ub_le1_val rL) Lstar e x : ℝ) ≤ (bound : ℝ) := by
      exact_mod_cast hle
    unfold L_corner at hR; push_cast at hR
    rw [← hCD (x : ℝ)]; linarith
  have hbil := bilinear_le_four_corners (A := (lam_max : ℝ) * (a0 : ℝ))
    (B := (lam_max : ℝ) * (a1 : ℝ)) (C := C) (D := D)
    (LL := (LL : ℝ)) (LR := (LR : ℝ)) (L := L)
    (ηMin := eta_min) (ηMax := eta_max) (η := θ.η) (M := (bound : ℝ))
    hL θ.hη
    (by rw [← q_consts_cast.2.2.2.2.1]; exact hcorner q_emin LL h1)
    (by rw [← q_consts_cast.2.2.2.2.1]; exact hcorner q_emin LR h2)
    (by rw [← q_consts_cast.2.2.2.2.2.1]; exact hcorner q_emax LL h3)
    (by rw [← q_consts_cast.2.2.2.2.2.1]; exact hcorner q_emax LR h4)
  rw [← hCD L] at hbil
  linarith

/-! ## 4. Los 4 validadores de segmentos y sus teoremas de solidez -/

/-- Tipo 1 (Banda A): secante de $K \mapsto F(A_+, K, 1)$ en $[k_L, k_R] \subseteq (0, 1/4]$. -/
structure NoLeisureSecSeg where
  kL : ℚ
  kR : ℚ
  s0 : ℚ
  r_c0 : ℚ
  c0_ge1 : Bool
  skL : ℚ
  skR : ℚ
  sgL : ℚ
  sgR : ℚ

def NoLeisureSecSeg.valid (s : NoLeisureSecSeg) : Prop :=
  0 < s.kL ∧ s.kL < s.kR ∧ s.kR ≤ 1 / 4 ∧ 0 < s.s0 ∧
  log_ub_ok (c0_ub_q s.s0) s.r_c0 s.c0_ge1 ∧
  0 < s.skL ∧ s.skL ^ 2 ≤ s.kL ∧
  0 < s.skR ∧ s.skR ^ 2 ≤ s.kR ∧
  0 ≤ s.sgL ∧ g_q 1 s.kL ≤ s.sgL ^ 2 ∧
  0 ≤ s.sgR ∧ g_q 1 s.kR ≤ s.sgR ^ 2 ∧
  let lm := lam_max_q s.s0
  let cb := const_base_q s.s0 s.r_c0 s.c0_ge1
  let aK := lm * q_qmax - 4 / 10
  let FL := q_Amax * g_q 1 s.kL * s.sgL
  let FR := q_Amax * g_q 1 s.kR * s.sgR
  cb + aK * s.kL + 5 / s.skL + lm * FL ≤ 0 ∧
  cb + aK * s.kR + 5 / s.skR + lm * FR ≤ 0

theorem NoLeisureSecSeg.sound (s : NoLeisureSecSeg) (hv : s.valid) (θ : Params)
    {K K' L : ℝ} (hK : K ∈ Icc (s.kL : ℝ) (s.kR : ℝ)) (hK' : 0 < K')
    (hL : 0 ≤ L ∧ L < 1) (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  rcases hv with ⟨hkL0, hkLR, hkR4, hs0, hlog, hskL0, hskL2, hskR0, hskR2,
    hsgL0, hsgL2, hsgR0, hsgR2, hvL, hvR⟩
  have hkL_pos : (0 : ℝ) < (s.kL : ℝ) := by exact_mod_cast hkL0
  have hkLR_R : (s.kL : ℝ) < (s.kR : ℝ) := by exact_mod_cast hkLR
  have hkR4_R : (s.kR : ℝ) ≤ (1 : ℝ) / 4 := by
    have : (s.kR : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by exact_mod_cast hkR4
    norm_num at this; exact this
  have hK_pos : 0 < K := lt_of_lt_of_le hkL_pos hK.1
  have hbase := bellman_base_step θ hK_pos hK' hL hc hs0 hlog
  -- Descartar (1 - η) log(1 - L) ≤ 0
  have hL_np : (1 - θ.η) * Real.log (1 - L) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by have := θ.hη.2; unfold eta_max at this; linarith)
      (Real.log_nonpos (by linarith [hL.2]) (by linarith [hL.1]))
  -- F(A_max, K, L) ≤ F(A_max, K, 1) ≤ secante en [kL, kR]
  have hF1 : F A_max K L ≤ F A_max K 1 :=
    F_mono_L (by unfold A_max; norm_num) hK_pos hL.1 (le_of_lt hL.2)
  have hFsec := F_convex_secant_K (A := A_max) (l := 1) (by unfold A_max; norm_num)
    (by norm_num) hkL_pos hkLR_R hkR4_R hK
  set FLq : ℚ := q_Amax * g_q 1 s.kL * s.sgL
  set FRq : ℚ := q_Amax * g_q 1 s.kR * s.sgR
  have hFL_ub : F A_max (s.kL : ℝ) 1 ≤ (FLq : ℝ) := by
    unfold F; dsimp only
    have hg_eq : 2 * (s.kL : ℝ) * 1 / ((s.kL : ℝ) + 1) = ((g_q 1 s.kL : ℚ) : ℝ) := by
      unfold g_q; push_cast; ring
    rw [hg_eq]
    have hsg := sqrt_ub_sound hsgL0 hsgL2
    have hnn : 0 ≤ A_max * ((g_q 1 s.kL : ℚ) : ℝ) := by
      unfold A_max g_q; push_cast; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg hnn
    dsimp [FLq]; push_cast; rw [q_consts_cast.1]; linarith
  have hFR_ub : F A_max (s.kR : ℝ) 1 ≤ (FRq : ℝ) := by
    unfold F; dsimp only
    have hg_eq : 2 * (s.kR : ℝ) * 1 / ((s.kR : ℝ) + 1) = ((g_q 1 s.kR : ℚ) : ℝ) := by
      unfold g_q; push_cast; ring
    rw [hg_eq]
    have hsg := sqrt_ub_sound hsgR0 hsgR2
    have hkR_pos : (0 : ℝ) < (s.kR : ℝ) := lt_trans hkL_pos hkLR_R
    have hnn : 0 ≤ A_max * ((g_q 1 s.kR : ℚ) : ℝ) := by
      unfold A_max g_q; push_cast; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg hnn
    dsimp [FRq]; push_cast; rw [q_consts_cast.1]; linarith
  have hden_pos : 0 < (s.kR : ℝ) - (s.kL : ℝ) := sub_pos.mpr hkLR_R
  have hF_lin : F A_max K L ≤
      (((s.kR : ℝ) - K) * (FLq : ℝ) + (K - (s.kL : ℝ)) * (FRq : ℝ)) / ((s.kR : ℝ) - (s.kL : ℝ)) := by
    refine le_trans hF1 (le_trans hFsec ?_)
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hden_pos)
    have h1 := mul_le_mul_of_nonneg_left hFL_ub (show 0 ≤ (s.kR : ℝ) - K by linarith [hK.2])
    have h2 := mul_le_mul_of_nonneg_left hFR_ub (show 0 ≤ K - (s.kL : ℝ) by linarith [hK.1])
    linarith
  have hlm_nn : 0 ≤ (lam_max_q s.s0 : ℝ) := by
    unfold lam_max_q slope_q q_bmax; push_cast
    have : (0 : ℝ) < (s.s0 : ℝ) := by exact_mod_cast hs0
    positivity
  have hlmF := mul_le_mul_of_nonneg_left hF_lin hlm_nn
  -- Combinar parte lineal en K + 5/√K por convex_K_term_le_endpoints
  set slF : ℝ := ((FRq : ℝ) - (FLq : ℝ)) / ((s.kR : ℝ) - (s.kL : ℝ))
  set offF : ℝ := (FLq : ℝ) - slF * (s.kL : ℝ)
  have hsec_eq : ∀ x : ℝ,
      (((s.kR : ℝ) - x) * (FLq : ℝ) + (x - (s.kL : ℝ)) * (FRq : ℝ)) / ((s.kR : ℝ) - (s.kL : ℝ)) =
      offF + slF * x := by
    intro x; dsimp [offF, slF]; field_simp [ne_of_gt hden_pos]; ring
  set a_eff : ℝ := ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) + (lam_max_q s.s0 : ℝ) * slF
  have hconv := convex_K_term_le_endpoints (a := a_eff) hkL_pos hK
  have hL_end : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + (lam_max_q s.s0 : ℝ) * offF +
      (a_eff * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ)) ≤ 0 := by
    have hsk := sqrt_lb_sound hskL0 hskL2
    have hR : ((const_base_q s.s0 s.r_c0 s.c0_ge1 + (lam_max_q s.s0 * q_qmax - 4 / 10) * s.kL +
        5 / s.skL + lam_max_q s.s0 * FLq : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hvL
    push_cast at hR; rw [q_consts_cast.2.1] at hR
    have heqL : offF + slF * (s.kL : ℝ) = (FLq : ℝ) := by
      rw [← hsec_eq]; field_simp [ne_of_gt hden_pos]; ring
    dsimp [a_eff]
    have hdist : (lam_max_q s.s0 : ℝ) * offF +
        (((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) + (lam_max_q s.s0 : ℝ) * slF) * (s.kL : ℝ) =
        ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * (s.kL : ℝ) + (lam_max_q s.s0 : ℝ) * (FLq : ℝ) := by
      have : (lam_max_q s.s0 : ℝ) * (offF + slF * (s.kL : ℝ)) = (lam_max_q s.s0 : ℝ) * (FLq : ℝ) := by
        rw [heqL]
      linarith
    linarith
  have hR_end : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + (lam_max_q s.s0 : ℝ) * offF +
      (a_eff * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤ 0 := by
    have hsk := sqrt_lb_sound hskR0 hskR2
    have hR : ((const_base_q s.s0 s.r_c0 s.c0_ge1 + (lam_max_q s.s0 * q_qmax - 4 / 10) * s.kR +
        5 / s.skR + lam_max_q s.s0 * FRq : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hvR
    push_cast at hR; rw [q_consts_cast.2.1] at hR
    have heqR : offF + slF * (s.kR : ℝ) = (FRq : ℝ) := by
      rw [← hsec_eq]; field_simp [ne_of_gt hden_pos]; ring
    dsimp [a_eff]
    have hdist : (lam_max_q s.s0 : ℝ) * offF +
        (((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) + (lam_max_q s.s0 : ℝ) * slF) * (s.kR : ℝ) =
        ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * (s.kR : ℝ) + (lam_max_q s.s0 : ℝ) * (FRq : ℝ) := by
      have : (lam_max_q s.s0 : ℝ) * (offF + slF * (s.kR : ℝ)) = (lam_max_q s.s0 : ℝ) * (FRq : ℝ) := by
        rw [heqR]
      linarith
    linarith
  rw [hsec_eq K] at hlmF
  have hmax : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + (lam_max_q s.s0 : ℝ) * offF +
      max (a_eff * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
          (a_eff * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤ 0 := by
    rcases max_cases (a_eff * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
        (a_eff * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hrew : ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * K +
      (lam_max_q s.s0 : ℝ) * (offF + slF * K) =
      (lam_max_q s.s0 : ℝ) * offF + a_eff * K := by dsimp [a_eff]; ring
  linarith

/-- Tipo 2 (Banda D): tangente de $K \mapsto F(A_+, K, 1)$ en $k_L \ge 1/4$. -/
structure NoLeisureTanSeg where
  kL : ℚ
  kR : ℚ
  s0 : ℚ
  r_c0 : ℚ
  c0_ge1 : Bool
  skL : ℚ
  skR : ℚ
  sg : ℚ

def NoLeisureTanSeg.valid (s : NoLeisureTanSeg) : Prop :=
  1 / 4 ≤ s.kL ∧ s.kL < s.kR ∧ 0 < s.s0 ∧
  log_ub_ok (c0_ub_q s.s0) s.r_c0 s.c0_ge1 ∧
  0 < s.skL ∧ s.skL ^ 2 ≤ s.kL ∧
  0 < s.skR ∧ s.skR ^ 2 ≤ s.kR ∧
  0 ≤ s.sg ∧ g_q 1 s.kL ≤ s.sg ^ 2 ∧
  let lm := lam_max_q s.s0
  let cb := const_base_q s.s0 s.r_c0 s.c0_ge1
  let F_ub := q_Amax * g_q 1 s.kL * s.sg
  let FK_ub := 3 * q_Amax * s.sg / (s.kL + 1) ^ 2
  let aK := lm * (q_qmax + FK_ub) - 4 / 10
  let off := lm * (F_ub - FK_ub * s.kL)
  cb + off + aK * s.kL + 5 / s.skL ≤ 0 ∧
  cb + off + aK * s.kR + 5 / s.skR ≤ 0

theorem NoLeisureTanSeg.sound (s : NoLeisureTanSeg) (hv : s.valid) (θ : Params)
    {K K' L : ℝ} (hK : K ∈ Icc (s.kL : ℝ) (s.kR : ℝ)) (hK' : 0 < K')
    (hL : 0 ≤ L ∧ L < 1) (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  rcases hv with ⟨hkL4, hkLR, hs0, hlog, hskL0, hskL2, hskR0, hskR2, hsg0, hsg2, hvL, hvR⟩
  have hkL4_R : (1 / 4 : ℝ) ≤ (s.kL : ℝ) := by
    have : ((1 / 4 : ℚ) : ℝ) ≤ (s.kL : ℝ) := by exact_mod_cast hkL4
    norm_num at this; exact this
  have hkL_pos : (0 : ℝ) < (s.kL : ℝ) := by linarith
  have hK_pos : 0 < K := lt_of_lt_of_le hkL_pos hK.1
  have hbase := bellman_base_step θ hK_pos hK' hL hc hs0 hlog
  have hL_np : (1 - θ.η) * Real.log (1 - L) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by have := θ.hη.2; unfold eta_max at this; linarith)
      (Real.log_nonpos (by linarith [hL.2]) (by linarith [hL.1]))
  have hF1 : F A_max K L ≤ F A_max K 1 :=
    F_mono_L (by unfold A_max; norm_num) hK_pos hL.1 (le_of_lt hL.2)
  have htan := F_concave_tangent_K (A := A_max) (l := 1) (by unfold A_max; norm_num)
    (by norm_num) (by linarith) hK.1
  set F_ub : ℚ := q_Amax * g_q 1 s.kL * s.sg
  set FK_ub : ℚ := 3 * q_Amax * s.sg / (s.kL + 1) ^ 2
  have hsg_R := sqrt_ub_sound hsg0 hsg2
  have hg_eq : g 1 (s.kL : ℝ) = ((g_q 1 s.kL : ℚ) : ℝ) := by unfold g g_q; push_cast; ring
  have hF_le : F A_max (s.kL : ℝ) 1 ≤ (F_ub : ℝ) := by
    unfold F; dsimp only
    have : 2 * (s.kL : ℝ) * 1 / ((s.kL : ℝ) + 1) = ((g_q 1 s.kL : ℚ) : ℝ) := by
      unfold g_q; push_cast; ring
    rw [this]
    have hnn : 0 ≤ A_max * ((g_q 1 s.kL : ℚ) : ℝ) := by unfold A_max g_q; push_cast; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg_R hnn
    dsimp [F_ub]; push_cast; rw [q_consts_cast.1]; linarith
  have hFK_le : FK A_max 1 (s.kL : ℝ) ≤ (FK_ub : ℝ) := by
    unfold FK; rw [hg_eq]
    have hnn : 0 ≤ 3 * A_max * (1 : ℝ) ^ 2 / ((s.kL : ℝ) + 1) ^ 2 := by
      unfold A_max; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg_R hnn
    have hrew1 : 3 * A_max * 1 ^ 2 * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) / ((s.kL : ℝ) + 1) ^ 2 =
        (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) := by ring
    have hrew2 : (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * (s.sg : ℝ) = (FK_ub : ℝ) := by
      dsimp [FK_ub]; push_cast; rw [q_consts_cast.1]; ring
    linarith
  have hF_lin : F A_max K L ≤ (F_ub : ℝ) + (FK_ub : ℝ) * (K - (s.kL : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hFK_le (show 0 ≤ K - (s.kL : ℝ) by linarith [hK.1])
    linarith
  have hlm_nn : 0 ≤ (lam_max_q s.s0 : ℝ) := by
    unfold lam_max_q slope_q q_bmax; push_cast
    have : (0 : ℝ) < (s.s0 : ℝ) := by exact_mod_cast hs0
    positivity
  have hlmF := mul_le_mul_of_nonneg_left hF_lin hlm_nn
  set aK : ℝ := (lam_max_q s.s0 : ℝ) * (q_max + (FK_ub : ℝ)) - 4 / 10
  set off : ℝ := (lam_max_q s.s0 : ℝ) * ((F_ub : ℝ) - (FK_ub : ℝ) * (s.kL : ℝ))
  have hconv := convex_K_term_le_endpoints (a := aK) hkL_pos hK
  have hL_end : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + off +
      (aK * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ)) ≤ 0 := by
    have hsk := sqrt_lb_sound hskL0 hskL2
    have hR : ((const_base_q s.s0 s.r_c0 s.c0_ge1 +
        lam_max_q s.s0 * (F_ub - FK_ub * s.kL) +
        (lam_max_q s.s0 * (q_qmax + FK_ub) - 4 / 10) * s.kL + 5 / s.skL : ℚ) : ℝ) ≤ 0 := by
      exact_mod_cast hvL
    push_cast at hR; rw [q_consts_cast.2.1] at hR; dsimp [aK, off]; linarith
  have hR_end : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + off +
      (aK * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤ 0 := by
    have hsk := sqrt_lb_sound hskR0 hskR2
    have hR : ((const_base_q s.s0 s.r_c0 s.c0_ge1 +
        lam_max_q s.s0 * (F_ub - FK_ub * s.kL) +
        (lam_max_q s.s0 * (q_qmax + FK_ub) - 4 / 10) * s.kR + 5 / s.skR : ℚ) : ℝ) ≤ 0 := by
      exact_mod_cast hvR
    push_cast at hR; rw [q_consts_cast.2.1] at hR; dsimp [aK, off]; linarith
  have hmax : (const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + off +
      max (aK * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
          (aK * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤ 0 := by
    rcases max_cases (aK * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
        (aK * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hrew : ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * K +
      (lam_max_q s.s0 : ℝ) * ((F_ub : ℝ) + (FK_ub : ℝ) * (K - (s.kL : ℝ))) =
      off + aK * K := by dsimp [off, aK]; ring
  linarith

/-- Tipo 3 (Bandas B1 y B2): 1 tangente global en $L$ (`tangent_dominance`, $l_0 \ge k_{\text{eval}}/2$). -/
structure TanLSeg where
  kL : ℚ
  kR : ℚ
  use_FK : Bool
  s0 : ℚ
  r_c0 : ℚ
  c0_ge1 : Bool
  skL : ℚ
  skR : ℚ
  sg1 : ℚ
  l0 : ℚ
  sg0 : ℚ
  Lstar : ℚ
  rL : ℚ

def TanLSeg.valid (s : TanLSeg) : Prop :=
  0 < s.kL ∧ s.kL < s.kR ∧ 0 < s.s0 ∧
  log_ub_ok (c0_ub_q s.s0) s.r_c0 s.c0_ge1 ∧
  0 < s.skL ∧ s.skL ^ 2 ≤ s.kL ∧
  0 < s.skR ∧ s.skR ^ 2 ≤ s.kR ∧
  (if s.use_FK then 1 / 4 ≤ s.kL ∧ 0 ≤ s.sg1 ∧ g_q 1 s.kL ≤ s.sg1 ^ 2 else True) ∧
  let k_eval := if s.use_FK then s.kL else s.kR
  k_eval / 2 ≤ s.l0 ∧ 0 ≤ s.sg0 ∧ g_q s.l0 k_eval ≤ s.sg0 ^ 2 ∧
  let lm := lam_max_q s.s0
  let cb := const_base_q s.s0 s.r_c0 s.c0_ge1
  let FK_ub := if s.use_FK then 3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2 else 0
  let aK := lm * (q_qmax + FK_ub) - 4 / 10
  let K_part := max (aK * s.kL + 5 / s.skL) (aK * s.kR + 5 / s.skR) - lm * FK_ub * s.kL
  let a0 := q_Amax * s.sg0 * k_eval * s.l0 * (2 * s.l0 - k_eval) / (k_eval + s.l0) ^ 2
  let a1 := 3 * q_Amax * k_eval ^ 2 * s.sg0 / (k_eval + s.l0) ^ 2
  L_affine_ok lm a0 a1 0 1 s.Lstar s.rL (-(cb + K_part))

lemma tangent_dominance_rat_ub {ke l0 sg0 : ℚ} {L : ℝ}
    (hke : 0 < ke) (hl0 : ke / 2 ≤ l0) (hsg0 : 0 ≤ sg0) (hsg2 : g_q l0 ke ≤ sg0 ^ 2)
    (hL0 : 0 ≤ L) :
    F A_max (ke : ℝ) L ≤
      ((q_Amax * sg0 * ke * l0 * (2 * l0 - ke) / (ke + l0) ^ 2 : ℚ) : ℝ) +
      ((3 * q_Amax * ke ^ 2 * sg0 / (ke + l0) ^ 2 : ℚ) : ℝ) * L := by
  have hkeR : (0 : ℝ) < (ke : ℝ) := by exact_mod_cast hke
  have hl0R : (ke : ℝ) / 2 ≤ (l0 : ℝ) := by exact_mod_cast hl0
  have htan := tangent_dominance (A := A_max) (by unfold A_max; norm_num) hkeR hl0R hL0
  have hg_eq : g (l0 : ℝ) (ke : ℝ) = ((g_q l0 ke : ℚ) : ℝ) := by unfold g g_q; push_cast; ring
  have hsg := sqrt_ub_sound hsg0 hsg2
  have hl0_pos : (0 : ℝ) < (l0 : ℝ) := by linarith
  have hden_ne : (ke : ℝ) + (l0 : ℝ) ≠ 0 := by linarith
  have ha0_exact : F A_max (ke : ℝ) (l0 : ℝ) - t_gen A_max (l0 : ℝ) (ke : ℝ) * (l0 : ℝ) =
      A_max * Real.sqrt (g (l0 : ℝ) (ke : ℝ)) * (ke : ℝ) * (l0 : ℝ) *
        (2 * (l0 : ℝ) - (ke : ℝ)) / ((ke : ℝ) + (l0 : ℝ)) ^ 2 := by
    unfold F t_gen g; dsimp only
    field_simp [hden_ne]; ring
  have ha0_le : A_max * Real.sqrt (g (l0 : ℝ) (ke : ℝ)) * (ke : ℝ) * (l0 : ℝ) *
        (2 * (l0 : ℝ) - (ke : ℝ)) / ((ke : ℝ) + (l0 : ℝ)) ^ 2 ≤
      ((q_Amax * sg0 * ke * l0 * (2 * l0 - ke) / (ke + l0) ^ 2 : ℚ) : ℝ) := by
    rw [hg_eq]
    have hcoef_nn : 0 ≤ A_max * (ke : ℝ) * (l0 : ℝ) * (2 * (l0 : ℝ) - (ke : ℝ)) /
        ((ke : ℝ) + (l0 : ℝ)) ^ 2 := by
      have : 0 ≤ 2 * (l0 : ℝ) - (ke : ℝ) := by linarith
      unfold A_max; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg hcoef_nn
    have hrew1 : A_max * Real.sqrt ((g_q l0 ke : ℚ) : ℝ) * (ke : ℝ) * (l0 : ℝ) *
        (2 * (l0 : ℝ) - (ke : ℝ)) / ((ke : ℝ) + (l0 : ℝ)) ^ 2 =
        (A_max * (ke : ℝ) * (l0 : ℝ) * (2 * (l0 : ℝ) - (ke : ℝ)) / ((ke : ℝ) + (l0 : ℝ)) ^ 2) *
          Real.sqrt ((g_q l0 ke : ℚ) : ℝ) := by ring
    have hrew2 : (A_max * (ke : ℝ) * (l0 : ℝ) * (2 * (l0 : ℝ) - (ke : ℝ)) / ((ke : ℝ) + (l0 : ℝ)) ^ 2) *
        (sg0 : ℝ) = ((q_Amax * sg0 * ke * l0 * (2 * l0 - ke) / (ke + l0) ^ 2 : ℚ) : ℝ) := by
      push_cast; rw [q_consts_cast.1]; ring
    linarith
  have ha1_le : t_gen A_max (l0 : ℝ) (ke : ℝ) ≤
      ((3 * q_Amax * ke ^ 2 * sg0 / (ke + l0) ^ 2 : ℚ) : ℝ) := by
    unfold t_gen; rw [hg_eq]
    have hcoef_nn : 0 ≤ 3 * A_max * (ke : ℝ) ^ 2 / ((ke : ℝ) + (l0 : ℝ)) ^ 2 := by
      unfold A_max; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg hcoef_nn
    have hrew1 : 3 * A_max * (ke : ℝ) ^ 2 * Real.sqrt ((g_q l0 ke : ℚ) : ℝ) / ((ke : ℝ) + (l0 : ℝ)) ^ 2 =
        (3 * A_max * (ke : ℝ) ^ 2 / ((ke : ℝ) + (l0 : ℝ)) ^ 2) * Real.sqrt ((g_q l0 ke : ℚ) : ℝ) := by ring
    have hrew2 : (3 * A_max * (ke : ℝ) ^ 2 / ((ke : ℝ) + (l0 : ℝ)) ^ 2) * (sg0 : ℝ) =
        ((3 * q_Amax * ke ^ 2 * sg0 / (ke + l0) ^ 2 : ℚ) : ℝ) := by
      push_cast; rw [q_consts_cast.1]; ring
    linarith
  have hmulL := mul_le_mul_of_nonneg_right ha1_le hL0
  linarith

theorem TanLSeg.sound (s : TanLSeg) (hv : s.valid) (θ : Params)
    {K K' L : ℝ} (hK : K ∈ Icc (s.kL : ℝ) (s.kR : ℝ)) (hK' : 0 < K')
    (hL : 0 ≤ L ∧ L < 1) (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  rcases hv with ⟨hkL0, hkLR, hs0, hlog, hskL0, hskL2, hskR0, hskR2, hFKcond,
    hl0, hsg0, hsg2, hLaff⟩
  have hkL_pos : (0 : ℝ) < (s.kL : ℝ) := by exact_mod_cast hkL0
  have hK_pos : 0 < K := lt_of_lt_of_le hkL_pos hK.1
  have hbase := bellman_base_step θ hK_pos hK' hL hc hs0 hlog
  set k_eval : ℚ := if s.use_FK then s.kL else s.kR
  set FK_ub : ℚ := if s.use_FK then 3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2 else 0
  have hke_pos : 0 < k_eval := by
    dsimp [k_eval]; cases s.use_FK <;> [exact lt_trans hkL0 hkLR; exact hkL0]
  have hF_split : F A_max K L ≤ F A_max (k_eval : ℝ) L + (FK_ub : ℝ) * (K - (s.kL : ℝ)) := by
    cases huf : s.use_FK with
    | false =>
      have hk_eq : k_eval = s.kR := by dsimp [k_eval]; simp [huf]
      have hFK_eq : FK_ub = 0 := by dsimp [FK_ub]; simp [huf]
      rw [hk_eq, hFK_eq]; push_cast; rw [zero_mul, add_zero]
      exact F_mono_K (by unfold A_max; norm_num) hK_pos hK.2 hL.1
    | true =>
      simp only [huf, ite_true] at hFKcond
      have hk_eq : k_eval = s.kL := by dsimp [k_eval]; simp [huf]
      have hFK_eq : FK_ub = 3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2 := by dsimp [FK_ub]; simp [huf]
      rw [hk_eq, hFK_eq]
      rcases hFKcond with ⟨hkL4, hsg10, hsg12⟩
      have hkL4_R : (1 / 4 : ℝ) ≤ (s.kL : ℝ) := by
        have : ((1 / 4 : ℚ) : ℝ) ≤ (s.kL : ℝ) := by exact_mod_cast hkL4
        norm_num at this; exact this
      have htan := F_concave_tangent_K_all_L hkL4_R hK.1 hL.1 (le_of_lt hL.2)
      have hsg1 := sqrt_ub_sound hsg10 hsg12
      have hg_eq : g 1 (s.kL : ℝ) = ((g_q 1 s.kL : ℚ) : ℝ) := by unfold g g_q; push_cast; ring
      have hFK_le : FK A_max 1 (s.kL : ℝ) ≤ ((3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2 : ℚ) : ℝ) := by
        unfold FK; rw [hg_eq]
        have hnn : 0 ≤ 3 * A_max * (1 : ℝ) ^ 2 / ((s.kL : ℝ) + 1) ^ 2 := by
          unfold A_max; positivity
        have hmul := mul_le_mul_of_nonneg_left hsg1 hnn
        have hrew1 : 3 * A_max * 1 ^ 2 * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) / ((s.kL : ℝ) + 1) ^ 2 =
            (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) := by ring
        have hrew2 : (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * (s.sg1 : ℝ) =
            ((3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2 : ℚ) : ℝ) := by
          push_cast; rw [q_consts_cast.1]; ring
        linarith
      have hmul := mul_le_mul_of_nonneg_right hFK_le (show 0 ≤ K - (s.kL : ℝ) by linarith [hK.1])
      linarith
  have hF_L := tangent_dominance_rat_ub hke_pos hl0 hsg0 hsg2 hL.1
  have hlm_nn : 0 ≤ (lam_max_q s.s0 : ℝ) := by
    unfold lam_max_q slope_q q_bmax; push_cast
    have : (0 : ℝ) < (s.s0 : ℝ) := by exact_mod_cast hs0
    positivity
  have hF_comb : F A_max K L ≤
      ((q_Amax * s.sg0 * k_eval * s.l0 * (2 * s.l0 - k_eval) / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) +
      ((3 * q_Amax * k_eval ^ 2 * s.sg0 / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) * L +
      (FK_ub : ℝ) * (K - (s.kL : ℝ)) := by linarith
  have hlmF := mul_le_mul_of_nonneg_left hF_comb hlm_nn
  -- Parte K por convex_K_term_le_endpoints
  set aKq : ℚ := lam_max_q s.s0 * (q_qmax + FK_ub) - 4 / 10
  set K_part_q : ℚ := max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) -
    lam_max_q s.s0 * FK_ub * s.kL
  have hK_bound : (aKq : ℝ) * K + 5 / Real.sqrt K - (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ) ≤
      (K_part_q : ℝ) := by
    have hconv := convex_K_term_le_endpoints (a := (aKq : ℝ)) hkL_pos hK
    have h1 := sqrt_lb_sound hskL0 hskL2
    have h2 := sqrt_lb_sound hskR0 hskR2
    have hmax : max ((aKq : ℝ) * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
        ((aKq : ℝ) * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤
        ((max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) : ℚ) : ℝ) := by
      push_cast
      exact max_le_max (by linarith) (by linarith)
    have hKp_eq : (K_part_q : ℝ) = ((max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) : ℚ) : ℝ) -
        (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ) := by
      dsimp [K_part_q]; push_cast; ring
    linarith
  have hL_bound := L_affine_sound θ (L := L) ⟨by simpa using hL.1, by simpa using le_of_lt hL.2⟩ hL.2 hLaff
  have haK_rew : (aKq : ℝ) = (lam_max_q s.s0 : ℝ) * (q_max + (FK_ub : ℝ)) - 4 / 10 := by
    dsimp [aKq]; push_cast; rw [q_consts_cast.2.1]
  have hcb_neg : ((-(const_base_q s.s0 s.r_c0 s.c0_ge1 + K_part_q) : ℚ) : ℝ) =
      -((const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + (K_part_q : ℝ)) := by push_cast; ring
  rw [hcb_neg] at hL_bound
  have hdist : ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * K +
      (lam_max_q s.s0 : ℝ) *
        (((q_Amax * s.sg0 * k_eval * s.l0 * (2 * s.l0 - k_eval) / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) +
         ((3 * q_Amax * k_eval ^ 2 * s.sg0 / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) * L +
         (FK_ub : ℝ) * (K - (s.kL : ℝ))) =
      ((aKq : ℝ) * K - (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ)) +
      (lam_max_q s.s0 : ℝ) *
        (((q_Amax * s.sg0 * k_eval * s.l0 * (2 * s.l0 - k_eval) / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) +
         ((3 * q_Amax * k_eval ^ 2 * s.sg0 / (k_eval + s.l0) ^ 2 : ℚ) : ℝ) * L) := by
    rw [haK_rew]; ring
  linarith

/-- Piezas de envolvente lineal en $L \in [0, 1]$ para la Banda C. -/
inductive LPiece where
  | sec0 (Lb sgb Lstar rL : ℚ)
  | sec (La Lb sga sgb Lstar rL : ℚ)
  | tan (La Lb sga Lstar rL : ℚ)

def LPiece.ok (kL lm bound : ℚ) (cur : ℚ) : LPiece → Prop
  | .sec0 Lb sgb Lstar rL =>
      cur = 0 ∧ 0 < Lb ∧ Lb ≤ kL / 2 ∧ Lb ≤ 1 ∧
      0 ≤ sgb ∧ g_q Lb kL ≤ sgb ^ 2 ∧
      let Fb := q_Amax * g_q Lb kL * sgb
      L_affine_ok lm 0 (Fb / Lb) 0 Lb Lstar rL bound
  | .sec La Lb sga sgb Lstar rL =>
      cur = La ∧ 0 < La ∧ La < Lb ∧ Lb ≤ kL / 4 ∧ Lb ≤ 1 ∧
      0 ≤ sga ∧ g_q La kL ≤ sga ^ 2 ∧
      0 ≤ sgb ∧ g_q Lb kL ≤ sgb ^ 2 ∧
      let Fa := q_Amax * g_q La kL * sga
      let Fb := q_Amax * g_q Lb kL * sgb
      let sl := (Fb - Fa) / (Lb - La)
      L_affine_ok lm (Fa - sl * La) sl La Lb Lstar rL bound
  | .tan La Lb sga Lstar rL =>
      cur = La ∧ kL / 4 ≤ La ∧ La < Lb ∧ Lb ≤ 1 ∧
      0 ≤ sga ∧ g_q La kL ≤ sga ^ 2 ∧
      let Fa := q_Amax * g_q La kL * sga
      let ta := 3 * q_Amax * kL ^ 2 * sga / (kL + La) ^ 2
      L_affine_ok lm (Fa - ta * La) ta La Lb Lstar rL bound

def LPiece.right : LPiece → ℚ
  | .sec0 Lb _ _ _ => Lb
  | .sec _ Lb _ _ _ _ => Lb
  | .tan _ Lb _ _ _ => Lb

def LPiecesOk (kL lm bound : ℚ) : ℚ → List LPiece → Prop
  | cur, [] => cur = 1
  | cur, p :: ps => p.ok kL lm bound cur ∧ LPiecesOk kL lm bound p.right ps

lemma LPiece.sound (θ : Params) {kL lm bound cur : ℚ} {p : LPiece} {L : ℝ}
    (hkL : 0 < kL) (hlm : 0 ≤ lm)
    (hok : p.ok kL lm bound cur) (hL_lo : (cur : ℝ) ≤ L) (hL_hi : L ≤ (p.right : ℝ)) (hL1 : L < 1) :
    (lm : ℝ) * F A_max (kL : ℝ) L + (1 - θ.η) * Real.log (1 - L) ≤ (bound : ℝ) := by
  have hkLR : (0 : ℝ) < (kL : ℝ) := by exact_mod_cast hkL
  have hlmR : (0 : ℝ) ≤ (lm : ℝ) := by exact_mod_cast hlm
  cases p with
  | sec0 Lb sgb Lstar rL =>
    rcases hok with ⟨hcur, hLb0, hLb2, _, hsgb0, hsgb2, haff⟩
    subst hcur
    have hL0 : 0 ≤ L := by simpa using hL_lo
    have hLb0R : (0 : ℝ) < (Lb : ℝ) := by exact_mod_cast hLb0
    have hLb2R : (Lb : ℝ) ≤ (kL : ℝ) / 2 := by exact_mod_cast hLb2
    have hFsec := F_sec0_le_L hkLR hLb0R hLb2R hL0 hL_hi
    set Fbq : ℚ := q_Amax * g_q Lb kL * sgb
    have hFb_le : F A_max (kL : ℝ) (Lb : ℝ) ≤ (Fbq : ℝ) := by
      unfold F; dsimp only
      have hg_eq : 2 * (kL : ℝ) * (Lb : ℝ) / ((kL : ℝ) + (Lb : ℝ)) = ((g_q Lb kL : ℚ) : ℝ) := by
        unfold g_q; push_cast; ring
      rw [hg_eq]
      have hsg := sqrt_ub_sound hsgb0 hsgb2
      have hnn : 0 ≤ A_max * ((g_q Lb kL : ℚ) : ℝ) := by unfold A_max g_q; push_cast; positivity
      have hmul := mul_le_mul_of_nonneg_left hsg hnn
      dsimp [Fbq]; push_cast; rw [q_consts_cast.1]; linarith
    have hF_lin : F A_max (kL : ℝ) L ≤ ((0 : ℚ) : ℝ) + ((Fbq / Lb : ℚ) : ℝ) * L := by
      have hmul := mul_le_mul_of_nonneg_left hFb_le (div_nonneg hL0 (le_of_lt hLb0R))
      have hrew : L / (Lb : ℝ) * (Fbq : ℝ) = ((0 : ℚ) : ℝ) + ((Fbq / Lb : ℚ) : ℝ) * L := by
        push_cast; ring
      linarith
    have haff_s := L_affine_sound θ (L := L) ⟨hL_lo, hL_hi⟩ hL1 haff
    have hmul := mul_le_mul_of_nonneg_left hF_lin hlmR
    linarith
  | sec La Lb sga sgb Lstar rL =>
    rcases hok with ⟨hcur, hLa0, hLab, hLb4, _, hsga0, hsga2, hsgb0, hsgb2, haff⟩
    rw [hcur] at hL_lo
    dsimp [LPiece.right] at hL_hi
    have hLa0R : (0 : ℝ) < (La : ℝ) := by exact_mod_cast hLa0
    have hLabR : (La : ℝ) < (Lb : ℝ) := by exact_mod_cast hLab
    have hLb4R : (Lb : ℝ) ≤ (kL : ℝ) / 4 := by exact_mod_cast hLb4
    have hFsec := F_convex_secant_L hkLR hLa0R hLabR hLb4R ⟨hL_lo, hL_hi⟩
    set Faq : ℚ := q_Amax * g_q La kL * sga
    set Fbq : ℚ := q_Amax * g_q Lb kL * sgb
    have hFa_le : F A_max (kL : ℝ) (La : ℝ) ≤ (Faq : ℝ) := by
      unfold F; dsimp only
      have hg_eq : 2 * (kL : ℝ) * (La : ℝ) / ((kL : ℝ) + (La : ℝ)) = ((g_q La kL : ℚ) : ℝ) := by
        unfold g_q; push_cast; ring
      rw [hg_eq]
      have hsg := sqrt_ub_sound hsga0 hsga2
      have hnn : 0 ≤ A_max * ((g_q La kL : ℚ) : ℝ) := by unfold A_max g_q; push_cast; positivity
      have hmul := mul_le_mul_of_nonneg_left hsg hnn
      dsimp [Faq]; push_cast; rw [q_consts_cast.1]; linarith
    have hFb_le : F A_max (kL : ℝ) (Lb : ℝ) ≤ (Fbq : ℝ) := by
      unfold F; dsimp only
      have hg_eq : 2 * (kL : ℝ) * (Lb : ℝ) / ((kL : ℝ) + (Lb : ℝ)) = ((g_q Lb kL : ℚ) : ℝ) := by
        unfold g_q; push_cast; ring
      rw [hg_eq]
      have hsg := sqrt_ub_sound hsgb0 hsgb2
      have hLb_pos : (0 : ℝ) < (Lb : ℝ) := lt_trans hLa0R hLabR
      have hnn : 0 ≤ A_max * ((g_q Lb kL : ℚ) : ℝ) := by unfold A_max g_q; push_cast; positivity
      have hmul := mul_le_mul_of_nonneg_left hsg hnn
      dsimp [Fbq]; push_cast; rw [q_consts_cast.1]; linarith
    have hden_pos : 0 < (Lb : ℝ) - (La : ℝ) := sub_pos.mpr hLabR
    set sl : ℚ := (Fbq - Faq) / (Lb - La)
    have hF_lin : F A_max (kL : ℝ) L ≤ ((Faq - sl * La : ℚ) : ℝ) + (sl : ℝ) * L := by
      have h1 := mul_le_mul_of_nonneg_left hFa_le (show 0 ≤ (Lb : ℝ) - L by linarith)
      have h2 := mul_le_mul_of_nonneg_left hFb_le (show 0 ≤ L - (La : ℝ) by linarith)
      have hdiv : (((Lb : ℝ) - L) * F A_max (kL : ℝ) (La : ℝ) +
          (L - (La : ℝ)) * F A_max (kL : ℝ) (Lb : ℝ)) / ((Lb : ℝ) - (La : ℝ)) ≤
          (((Lb : ℝ) - L) * (Faq : ℝ) + (L - (La : ℝ)) * (Fbq : ℝ)) / ((Lb : ℝ) - (La : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hden_pos)
      have heq : (((Lb : ℝ) - L) * (Faq : ℝ) + (L - (La : ℝ)) * (Fbq : ℝ)) / ((Lb : ℝ) - (La : ℝ)) =
          ((Faq - sl * La : ℚ) : ℝ) + (sl : ℝ) * L := by
        dsimp [sl]; push_cast; field_simp [ne_of_gt hden_pos]; ring
      linarith
    have haff_s := L_affine_sound θ (L := L) ⟨hL_lo, hL_hi⟩ hL1 haff
    have hmul := mul_le_mul_of_nonneg_left hF_lin hlmR
    linarith
  | tan La Lb sga Lstar rL =>
    rcases hok with ⟨hcur, hLa4, _, _, hsga0, hsga2, haff⟩
    rw [hcur] at hL_lo
    have hLa4R : (kL : ℝ) / 4 ≤ (La : ℝ) := by exact_mod_cast hLa4
    have hFtan := F_concave_tangent_L hkLR hLa4R hL_lo
    set Faq : ℚ := q_Amax * g_q La kL * sga
    set taq : ℚ := 3 * q_Amax * kL ^ 2 * sga / (kL + La) ^ 2
    have hsg := sqrt_ub_sound hsga0 hsga2
    have hFa_le : F A_max (kL : ℝ) (La : ℝ) ≤ (Faq : ℝ) := by
      unfold F; dsimp only
      have hg_eq : 2 * (kL : ℝ) * (La : ℝ) / ((kL : ℝ) + (La : ℝ)) = ((g_q La kL : ℚ) : ℝ) := by
        unfold g_q; push_cast; ring
      rw [hg_eq]
      have hnn : 0 ≤ A_max * ((g_q La kL : ℚ) : ℝ) := by
        have hLa0 : (0 : ℝ) < (La : ℝ) := by linarith
        unfold A_max g_q; push_cast; positivity
      have hmul := mul_le_mul_of_nonneg_left hsg hnn
      dsimp [Faq]; push_cast; rw [q_consts_cast.1]; linarith
    have hta_le : t_gen A_max (La : ℝ) (kL : ℝ) ≤ (taq : ℝ) := by
      unfold t_gen
      have hg_eq : g (La : ℝ) (kL : ℝ) = ((g_q La kL : ℚ) : ℝ) := by unfold g g_q; push_cast; ring
      rw [hg_eq]
      have hnn : 0 ≤ 3 * A_max * (kL : ℝ) ^ 2 / ((kL : ℝ) + (La : ℝ)) ^ 2 := by
        unfold A_max; positivity
      have hmul := mul_le_mul_of_nonneg_left hsg hnn
      have hrew1 : 3 * A_max * (kL : ℝ) ^ 2 * Real.sqrt ((g_q La kL : ℚ) : ℝ) / ((kL : ℝ) + (La : ℝ)) ^ 2 =
          (3 * A_max * (kL : ℝ) ^ 2 / ((kL : ℝ) + (La : ℝ)) ^ 2) * Real.sqrt ((g_q La kL : ℚ) : ℝ) := by ring
      have hrew2 : (3 * A_max * (kL : ℝ) ^ 2 / ((kL : ℝ) + (La : ℝ)) ^ 2) * (sga : ℝ) = (taq : ℝ) := by
        dsimp [taq]; push_cast; rw [q_consts_cast.1]; ring
      linarith
    have hF_lin : F A_max (kL : ℝ) L ≤ ((Faq - taq * La : ℚ) : ℝ) + (taq : ℝ) * L := by
      have hmul := mul_le_mul_of_nonneg_right hta_le (show 0 ≤ L - (La : ℝ) by linarith)
      push_cast; linarith
    have haff_s := L_affine_sound θ (L := L) ⟨hL_lo, hL_hi⟩ hL1 haff
    have hmul := mul_le_mul_of_nonneg_left hF_lin hlmR
    linarith

lemma LPiecesOk.sound (θ : Params) {kL lm bound : ℚ} (hkL : 0 < kL) (hlm : 0 ≤ lm) :
    ∀ (cur : ℚ) (ps : List LPiece), LPiecesOk kL lm bound cur ps →
      ∀ {L : ℝ}, (cur : ℝ) ≤ L → L < 1 →
        (lm : ℝ) * F A_max (kL : ℝ) L + (1 - θ.η) * Real.log (1 - L) ≤ (bound : ℝ)
  | cur, [], hok, L, hlo, h1 => by
    simp only [LPiecesOk] at hok; subst hok; push_cast at hlo; linarith
  | cur, p :: ps, hok, L, hlo, h1 => by
    rcases hok with ⟨hp, hrest⟩
    by_cases hle : L ≤ (p.right : ℝ)
    · exact p.sound θ hkL hlm hp hlo hle h1
    · exact LPiecesOk.sound θ hkL hlm p.right ps hrest (le_of_not_ge hle) h1

/-- Tipo 4 (Banda C): concavidad en $K \ge 1/4$ + envolvente lineal a trozos en $L$. -/
structure PieceLSeg where
  kL : ℚ
  kR : ℚ
  s0 : ℚ
  r_c0 : ℚ
  c0_ge1 : Bool
  skL : ℚ
  skR : ℚ
  sg1 : ℚ
  pieces : List LPiece

def PieceLSeg.valid (s : PieceLSeg) : Prop :=
  1 / 4 ≤ s.kL ∧ s.kL < s.kR ∧ 0 < s.s0 ∧
  log_ub_ok (c0_ub_q s.s0) s.r_c0 s.c0_ge1 ∧
  0 < s.skL ∧ s.skL ^ 2 ≤ s.kL ∧
  0 < s.skR ∧ s.skR ^ 2 ≤ s.kR ∧
  0 ≤ s.sg1 ∧ g_q 1 s.kL ≤ s.sg1 ^ 2 ∧
  let lm := lam_max_q s.s0
  let cb := const_base_q s.s0 s.r_c0 s.c0_ge1
  let FK_ub := 3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2
  let aK := lm * (q_qmax + FK_ub) - 4 / 10
  let K_part := max (aK * s.kL + 5 / s.skL) (aK * s.kR + 5 / s.skR) - lm * FK_ub * s.kL
  LPiecesOk s.kL lm (-(cb + K_part)) 0 s.pieces

theorem PieceLSeg.sound (s : PieceLSeg) (hv : s.valid) (θ : Params)
    {K K' L : ℝ} (hK : K ∈ Icc (s.kL : ℝ) (s.kR : ℝ)) (hK' : 0 < K')
    (hL : 0 ≤ L ∧ L < 1) (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  rcases hv with ⟨hkL4, hkLR, hs0, hlog, hskL0, hskL2, hskR0, hskR2, hsg10, hsg12, hps⟩
  have hkL4_R : (1 / 4 : ℝ) ≤ (s.kL : ℝ) := by
    have : ((1 / 4 : ℚ) : ℝ) ≤ (s.kL : ℝ) := by exact_mod_cast hkL4
    norm_num at this; exact this
  have hkL_pos : (0 : ℝ) < (s.kL : ℝ) := by linarith
  have hkL_qpos : 0 < s.kL := by linarith
  have hK_pos : 0 < K := lt_of_lt_of_le hkL_pos hK.1
  have hbase := bellman_base_step θ hK_pos hK' hL hc hs0 hlog
  set FK_ub : ℚ := 3 * q_Amax * s.sg1 / (s.kL + 1) ^ 2
  have htan := F_concave_tangent_K_all_L hkL4_R hK.1 hL.1 (le_of_lt hL.2)
  have hsg1 := sqrt_ub_sound hsg10 hsg12
  have hg_eq : g 1 (s.kL : ℝ) = ((g_q 1 s.kL : ℚ) : ℝ) := by unfold g g_q; push_cast; ring
  have hFK_le : FK A_max 1 (s.kL : ℝ) ≤ (FK_ub : ℝ) := by
    unfold FK; rw [hg_eq]
    have hnn : 0 ≤ 3 * A_max * (1 : ℝ) ^ 2 / ((s.kL : ℝ) + 1) ^ 2 := by unfold A_max; positivity
    have hmul := mul_le_mul_of_nonneg_left hsg1 hnn
    have hrew1 : 3 * A_max * 1 ^ 2 * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) / ((s.kL : ℝ) + 1) ^ 2 =
        (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * Real.sqrt ((g_q 1 s.kL : ℚ) : ℝ) := by ring
    have hrew2 : (3 * A_max * 1 ^ 2 / ((s.kL : ℝ) + 1) ^ 2) * (s.sg1 : ℝ) = (FK_ub : ℝ) := by
      dsimp [FK_ub]; push_cast; rw [q_consts_cast.1]; ring
    linarith
  have hF_split : F A_max K L ≤ F A_max (s.kL : ℝ) L + (FK_ub : ℝ) * (K - (s.kL : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hFK_le (show 0 ≤ K - (s.kL : ℝ) by linarith [hK.1])
    linarith
  have hlm_qnn : 0 ≤ lam_max_q s.s0 := by
    unfold lam_max_q slope_q q_bmax; positivity
  have hlm_nn : 0 ≤ (lam_max_q s.s0 : ℝ) := by exact_mod_cast hlm_qnn
  have hlmF := mul_le_mul_of_nonneg_left hF_split hlm_nn
  set aKq : ℚ := lam_max_q s.s0 * (q_qmax + FK_ub) - 4 / 10
  set K_part_q : ℚ := max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) -
    lam_max_q s.s0 * FK_ub * s.kL
  have hK_bound : (aKq : ℝ) * K + 5 / Real.sqrt K - (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ) ≤
      (K_part_q : ℝ) := by
    have hconv := convex_K_term_le_endpoints (a := (aKq : ℝ)) hkL_pos hK
    have h1 := sqrt_lb_sound hskL0 hskL2
    have h2 := sqrt_lb_sound hskR0 hskR2
    have hmax : max ((aKq : ℝ) * (s.kL : ℝ) + 5 / Real.sqrt (s.kL : ℝ))
        ((aKq : ℝ) * (s.kR : ℝ) + 5 / Real.sqrt (s.kR : ℝ)) ≤
        ((max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) : ℚ) : ℝ) := by
      push_cast; exact max_le_max (by linarith) (by linarith)
    have hKp_eq : (K_part_q : ℝ) = ((max (aKq * s.kL + 5 / s.skL) (aKq * s.kR + 5 / s.skR) : ℚ) : ℝ) -
        (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ) := by
      dsimp [K_part_q]; push_cast; ring
    linarith
  have hL_bound := LPiecesOk.sound θ hkL_qpos hlm_qnn 0 s.pieces hps
    (by simpa using hL.1) hL.2
  have haK_rew : (aKq : ℝ) = (lam_max_q s.s0 : ℝ) * (q_max + (FK_ub : ℝ)) - 4 / 10 := by
    dsimp [aKq]; push_cast; rw [q_consts_cast.2.1]
  have hcb_neg : ((-(const_base_q s.s0 s.r_c0 s.c0_ge1 + K_part_q) : ℚ) : ℝ) =
      -((const_base_q s.s0 s.r_c0 s.c0_ge1 : ℝ) + (K_part_q : ℝ)) := by push_cast; ring
  rw [hcb_neg] at hL_bound
  have hdist : ((lam_max_q s.s0 : ℝ) * q_max - 4 / 10) * K +
      (lam_max_q s.s0 : ℝ) * (F A_max (s.kL : ℝ) L + (FK_ub : ℝ) * (K - (s.kL : ℝ))) =
      ((aKq : ℝ) * K - (lam_max_q s.s0 : ℝ) * (FK_ub : ℝ) * (s.kL : ℝ)) +
      (lam_max_q s.s0 : ℝ) * F A_max (s.kL : ℝ) L := by
    rw [haK_rew]; ring
  linarith

/-! ## 5. Encadenamiento genérico de segmentos sobre $[a, b]$ -/

def ChainOk {α : Type} (getL getR : α → ℚ) (val : α → Prop) : ℚ → ℚ → List α → Prop
  | _, _, [] => False
  | a, b, [s] => getL s = a ∧ getR s = b ∧ val s
  | a, b, s :: t :: ss => getL s = a ∧ val s ∧ ChainOk getL getR val (getR s) b (t :: ss)

theorem ChainOk.sound {α : Type} {getL getR : α → ℚ} {val : α → Prop}
    (hsound : ∀ s, val s → ∀ (θ : Params) {K K' L : ℝ},
      K ∈ Icc (getL s : ℝ) (getR s : ℝ) → 0 < K' → 0 ≤ L ∧ L < 1 →
      0 < θ.q * K + F θ.A K L - K' →
      u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K) :
    ∀ (a b : ℚ) (ss : List α), ChainOk getL getR val a b ss →
      ∀ (θ : Params) {K K' L : ℝ},
        (a : ℝ) ≤ K → K ≤ (b : ℝ) → 0 < K' → 0 ≤ L ∧ L < 1 →
        0 < θ.q * K + F θ.A K L - K' →
        u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K
  | _, _, [], hok, _, _, _, _, _, _, _, _, _ => False.elim hok
  | a, b, [s], hok, θ, K, K', L, hKa, hKb, hK', hL, hc => by
    rcases hok with ⟨hL_eq, hR_eq, hval⟩
    subst hL_eq; subst hR_eq
    exact hsound s hval θ ⟨hKa, hKb⟩ hK' hL hc
  | a, b, s :: t :: ss, hok, θ, K, K', L, hKa, hKb, hK', hL, hc => by
    rcases hok with ⟨hL_eq, hval, hrest⟩
    subst hL_eq
    by_cases hle : K ≤ (getR s : ℝ)
    · exact hsound s hval θ ⟨hKa, hle⟩ hK' hL hc
    · exact ChainOk.sound hsound (getR s) b (t :: ss) hrest θ (le_of_not_ge hle) hKb hK' hL hc


/-! ## 6. Tablas racionales certificadas (131 segmentos en 5 bandas) -/

def bandA : List NoLeisureSecSeg := [
  ⟨(1/25000), (3/50000), (683/100000), (137637/50000), false, (79/12500), (387/50000), (179/20000), (137/12500)⟩,
  ⟨(3/50000), (9/100000), (419/50000), (264917/100000), false, (387/50000), (237/25000), (137/12500), (671/50000)⟩,
  ⟨(9/100000), (7/50000), (13/1250), (63601/25000), false, (237/25000), (1183/100000), (671/50000), (837/50000)⟩,
  ⟨(7/50000), (11/50000), (163/12500), (243839/100000), false, (1183/100000), (1483/100000), (837/50000), (1049/50000)⟩,
  ⟨(11/50000), (7/20000), (1647/100000), (233393/100000), false, (1483/100000), (187/10000), (1049/50000), (1323/50000)⟩,
  ⟨(7/20000), (57/100000), (2101/100000), (222979/100000), false, (187/10000), (2387/100000), (1323/50000), (211/6250)⟩,
  ⟨(57/100000), (47/50000), (677/25000), (26577/12500), false, (2387/100000), (613/20000), (211/6250), (2167/50000)⟩,
  ⟨(47/50000), (157/100000), (3517/100000), (202447/100000), false, (613/20000), (1981/50000), (2167/50000), (7/125)⟩,
  ⟨(157/100000), (133/50000), (4609/100000), (192439/100000), false, (1981/50000), (5157/100000), (7/125), (1457/20000)⟩,
  ⟨(133/50000), (453/100000), (38/625), (182699/100000), false, (5157/100000), (673/10000), (1457/20000), (9497/100000)⟩,
  ⟨(453/100000), (767/100000), (201/2500), (86687/50000), false, (673/10000), (8757/100000), (9497/100000), (12339/100000)⟩,
  ⟨(767/100000), (8/625), (53/500), (82309/50000), false, (8757/100000), (11313/100000), (12339/100000), (15899/100000)⟩,
  ⟨(8/625), (2023/100000), (1373/10000), (6273/4000), false, (11313/100000), (14223/100000), (15899/100000), (3983/20000)⟩,
  ⟨(2023/100000), (371/12500), (43/250), (150341/100000), false, (14223/100000), (17227/100000), (3983/20000), (24011/100000)⟩,
  ⟨(371/12500), (3991/100000), (129/625), (72647/50000), false, (17227/100000), (19977/100000), (24011/100000), (5541/20000)⟩,
  ⟨(3991/100000), (4897/100000), (2361/10000), (141683/100000), false, (19977/100000), (22129/100000), (5541/20000), (30557/100000)⟩,
  ⟨(4897/100000), (11/200), (1287/5000), (139413/100000), false, (22129/100000), (5863/25000), (30557/100000), (32291/100000)⟩,
]

def bandB1 : List TanLSeg := [
  ⟨(11/200), (609/10000), false, (271/1000), (138077/100000), false, (5863/25000), (24677/100000), 1, (11/20), (6623/20000), (669/1000), (53577/50000)⟩,
  ⟨(609/10000), (669/10000), false, (357/1250), (13673/10000), false, (24677/100000), (5173/20000), 1, (11/20), (34539/100000), (6863/10000), (53757/50000)⟩,
  ⟨(669/10000), (731/10000), false, (3/10), (3387/2500), false, (5173/20000), (27037/100000), 1, (18/25), (2277/6250), (5231/10000), (3273/3125)⟩,
  ⟨(731/10000), (159/2000), false, (3147/10000), (33569/25000), false, (27037/100000), (5639/20000), 1, (18/25), (37841/100000), (5449/10000), (105043/100000)⟩,
  ⟨(159/2000), (861/10000), false, (411/1250), (66591/50000), false, (5639/20000), (14671/50000), 1, (18/25), (39219/100000), (5663/10000), (105359/100000)⟩,
  ⟨(861/10000), (929/10000), false, (3427/10000), (132159/100000), false, (14671/50000), (30479/100000), 1, (18/25), (40567/100000), (366/625), (5283/5000)⟩,
  ⟨(929/10000), (499/5000), false, (713/2000), (131191/100000), false, (30479/100000), (31591/100000), 1, (18/25), (41869/100000), (301/500), (105927/100000)⟩,
  ⟨(499/5000), (1069/10000), false, (3707/10000), (130241/100000), false, (31591/100000), (6539/20000), 1, (18/25), (43147/100000), (6153/10000), (13269/12500)⟩,
  ⟨(1069/10000), (1141/10000), false, (48/125), (12939/10000), false, (6539/20000), (16889/50000), 1, (18/25), (44383/100000), (629/1000), (106393/100000)⟩,
  ⟨(1141/10000), (243/2000), false, (993/2500), (6429/5000), false, (16889/50000), (4357/12500), 1, (18/25), (22799/50000), (401/625), (106623/100000)⟩,
  ⟨(243/2000), (129/1000), false, (2051/5000), (63907/50000), false, (4357/12500), (8979/25000), 1, (18/25), (5847/12500), (6529/10000), (26709/25000)⟩,
  ⟨(129/1000), (683/5000), false, (423/1000), (7943/6250), false, (8979/25000), (36959/100000), 1, (18/25), (47921/100000), (6631/10000), (26759/25000)⟩,
  ⟨(683/5000), (1443/10000), false, (871/2000), (25281/20000), false, (36959/100000), (18993/50000), 1, (18/25), (49033/100000), (269/400), (4289/4000)⟩,
  ⟨(1443/10000), (19/125), false, (561/1250), (125703/100000), false, (18993/50000), (38987/100000), 1, (18/25), (50101/100000), (3393/5000), (107351/100000)⟩,
  ⟨(19/125), (799/5000), false, (288/625), (31273/25000), false, (38987/100000), (19987/50000), 1, (18/25), (25571/50000), (1373/2000), (53759/50000)⟩,
  ⟨(799/5000), (419/2500), false, (2363/5000), (12451/10000), false, (19987/50000), (20469/50000), 1, (18/25), (10429/20000), (1387/2000), (10767/10000)⟩,
  ⟨(419/2500), (351/2000), false, (4841/10000), (3099/2500), false, (20469/50000), (10473/25000), 1, (18/25), (13281/25000), (3501/5000), (107819/100000)⟩,
  ⟨(351/2000), (917/5000), false, (2477/5000), (61717/50000), false, (10473/25000), (1713/4000), 1, (18/25), (54069/100000), (3531/5000), (21591/20000)⟩,
  ⟨(917/5000), (957/5000), false, (633/1250), (122937/100000), false, (1713/4000), (43749/100000), 1, (18/25), (3437/6250), (89/125), (10809/10000)⟩,
  ⟨(957/5000), (997/5000), false, (5173/10000), (122457/100000), false, (43749/100000), (22327/50000), 1, (18/25), (11177/20000), (7171/10000), (108211/100000)⟩,
  ⟨(997/5000), (1037/5000), false, (5279/10000), (122003/100000), false, (22327/50000), (45541/100000), 1, (18/25), (56749/100000), (361/500), (108329/100000)⟩,
  ⟨(1037/5000), (431/2000), false, (337/625), (121531/100000), false, (45541/100000), (46421/100000), 1, (18/25), (11519/20000), (7253/10000), (10841/10000)⟩,
  ⟨(431/2000), (447/2000), false, (2751/5000), (121083/100000), false, (46421/100000), (1891/4000), 1, (18/25), (11681/20000), (3641/5000), (54241/50000)⟩,
  ⟨(447/2000), (579/2500), false, (2801/5000), (60343/50000), false, (1891/4000), (12031/25000), 1, (18/25), (59201/100000), (7323/10000), (21717/20000)⟩,
  ⟨(579/2500), (2397/10000), false, (57/100), (24061/20000), false, (12031/25000), (48959/100000), 1, (18/25), (14993/25000), (92/125), (2717/2500)⟩,
  ⟨(2397/10000), (1239/5000), false, (5797/10000), (3748/3125), false, (48959/100000), (49779/100000), 1, (18/25), (30361/50000), (3697/5000), (3399/3125)⟩,
  ⟨(1239/5000), (1/4), false, (5857/10000), (3741/3125), false, (49779/100000), (1/2), 1, (18/25), (60921/100000), (7359/10000), (108677/100000)⟩,
]

def bandB2a : List TanLSeg := [
  ⟨(1/4), (7/25), true, (6041/10000), (59521/50000), false, (1/2), (10583/20000), (31623/50000), (18/25), (60921/100000), (7111/10000), (108069/100000)⟩,
  ⟨(7/25), (773/2500), true, (159/250), (117941/100000), false, (10583/20000), (11121/20000), (2067/3125), (18/25), (63499/100000), (291/400), (6779/6250)⟩,
  ⟨(773/2500), (211/625), true, (6651/10000), (116997/100000), false, (11121/20000), (58103/100000), (8591/12500), (18/25), (32887/50000), (7401/10000), (54393/50000)⟩,
  ⟨(211/625), (917/2500), true, (1739/2500), (3627/3125), false, (58103/100000), (15141/25000), (71049/100000), (18/25), (67799/100000), (3731/5000), (27237/25000)⟩,
  ⟨(917/2500), (1977/5000), true, (7219/10000), (115303/100000), false, (15141/25000), (393/625), (36631/50000), (18/25), (13943/20000), (7547/10000), (5459/5000)⟩,
  ⟨(1977/5000), (847/2000), true, (1493/2000), (114623/100000), false, (393/625), (16269/25000), (75281/100000), (18/25), (8931/12500), (1523/2000), (27343/25000)⟩,
  ⟨(847/2000), (4511/10000), true, (1539/2000), (22803/20000), false, (16269/25000), (67163/100000), (38569/50000), (18/25), (73029/100000), (959/1250), (109537/100000)⟩,
  ⟨(4511/10000), (299/625), true, (989/1250), (14183/12500), false, (67163/100000), (34583/50000), (78851/100000), (18/25), (74477/100000), (193/250), (1371/1250)⟩,
  ⟨(299/625), (5053/10000), true, (8117/10000), (56481/50000), false, (34583/50000), (17771/25000), (2514/3125), (18/25), (75819/100000), (7761/10000), (27451/25000)⟩,
  ⟨(5053/10000), (2661/5000), true, (8313/10000), (112499/100000), false, (17771/25000), (9119/12500), (81937/100000), (18/25), (38531/50000), (1949/2500), (109913/100000)⟩,
  ⟨(2661/5000), (559/1000), true, (4251/5000), (112067/100000), false, (9119/12500), (37383/50000), (20837/25000), (18/25), (9779/12500), (3913/5000), (110007/100000)⟩,
  ⟨(559/1000), (5857/10000), true, (2171/2500), (6979/6250), false, (37383/50000), (76531/100000), (21171/25000), (18/25), (79333/100000), (1963/2500), (110089/100000)⟩,
  ⟨(5857/10000), (49/80), true, (443/500), (22257/20000), false, (76531/100000), (39131/50000), (1719/2000), (18/25), (80371/100000), (63/80), (27541/25000)⟩,
  ⟨(49/80), (6393/10000), true, (9031/10000), (6933/6250), false, (39131/50000), (19989/25000), (87161/100000), (18/25), (81359/100000), (987/1250), (13779/12500)⟩,
  ⟨(6393/10000), (833/1250), true, (9197/10000), (11059/10000), false, (19989/25000), (81633/100000), (22079/25000), (18/25), (10287/12500), (7913/10000), (6893/6250)⟩,
  ⟨(833/1250), (6941/10000), true, (4683/5000), (6891/6250), false, (81633/100000), (5207/6250), (11179/12500), (18/25), (83197/100000), (3963/5000), (110331/100000)⟩,
  ⟨(6941/10000), (3617/5000), true, (239/250), (27471/25000), false, (5207/6250), (21263/25000), (90523/100000), (18/25), (84073/100000), (3961/5000), (55159/50000)⟩,
  ⟨(3617/5000), (1509/2000), true, (9759/10000), (109513/100000), false, (21263/25000), (86861/100000), (733/800), (18/25), (84953/100000), (3959/5000), (3447/3125)⟩,
]

def bandB2b : List TanLSeg := [
  ⟨(1509/2000), (1573/2000), true, (4967/5000), (109197/100000), false, (86861/100000), (22171/25000), (92741/100000), (18/25), (1073/1250), (793/1000), (13793/12500)⟩,
  ⟨(1573/2000), (1639/2000), true, (1011/1000), (13611/12500), false, (22171/25000), (45263/50000), (18767/20000), (18/25), (43353/50000), (397/500), (55189/50000)⟩,
  ⟨(1639/2000), (1707/2000), true, (2057/2000), (108589/100000), false, (45263/50000), (18477/20000), (94911/100000), (18/25), (2736/3125), (7949/10000), (13801/12500)⟩,
  ⟨(1707/2000), (4443/5000), true, (10461/10000), (13537/12500), false, (18477/20000), (18853/20000), (95967/100000), (17/20), (92291/100000), (7707/10000), (109641/100000)⟩,
  ⟨(4443/5000), (9253/10000), true, (10639/10000), (13501/12500), false, (18853/20000), (3006/3125), (48503/50000), (17/20), (46607/50000), (7723/10000), (109689/100000)⟩,
  ⟨(9253/10000), (1927/2000), true, (541/500), (107723/100000), false, (3006/3125), (49079/50000), (98041/100000), (17/20), (94131/100000), (7739/10000), (109737/100000)⟩,
  ⟨(1927/2000), (2007/2000), true, (11003/10000), (107443/100000), false, (49079/50000), (50087/50000), (99067/100000), (17/20), (95037/100000), (7753/10000), (5489/5000)⟩,
  ⟨(2007/2000), (1307/1250), true, (1119/1000), (21433/20000), false, (50087/50000), (51127/50000), (12511/12500), (17/20), (47969/50000), (1553/2000), (109817/100000)⟩,
  ⟨(1307/1250), (10897/10000), true, (11381/10000), (106889/100000), false, (51127/50000), (26097/25000), (101109/100000), (17/20), (24209/25000), (7777/10000), (54927/50000)⟩,
  ⟨(10897/10000), (11357/10000), true, (463/400), (13327/12500), false, (26097/25000), (106569/100000), (25531/25000), (17/20), (97727/100000), (1947/2500), (3434/3125)⟩,
  ⟨(11357/10000), (5919/5000), true, (2943/2500), (26587/25000), false, (106569/100000), (54401/50000), (103129/100000), (17/20), (49303/50000), (3899/5000), (109919/100000)⟩,
  ⟨(5919/5000), (12337/10000), true, (2993/2500), (106083/100000), false, (54401/50000), (3471/3125), (26031/25000), (17/20), (49737/50000), (7807/10000), (109947/100000)⟩,
  ⟨(12337/10000), (6429/5000), true, (487/400), (52911/50000), false, (3471/3125), (113393/100000), (52551/50000), (17/20), (50163/50000), (3907/5000), (109969/100000)⟩,
  ⟨(6429/5000), (13399/10000), true, (619/500), (105567/100000), false, (113393/100000), (57877/50000), (26517/25000), (17/20), (50583/50000), (391/500), (27497/25000)⟩,
  ⟨(13399/10000), (349/250), true, (12587/10000), (105317/100000), false, (57877/50000), (14769/12500), (107017/100000), (17/20), (25497/25000), (3913/5000), (110007/100000)⟩,
  ⟨(349/250), (7267/5000), true, (3199/2500), (6567/6250), false, (14769/12500), (120557/100000), (26987/25000), (17/20), (102793/100000), (7831/10000), (110023/100000)⟩,
  ⟨(7267/5000), (15131/10000), true, (2601/2000), (20967/20000), false, (120557/100000), (3844/3125), (108849/100000), (17/20), (10357/10000), (3917/5000), (6877/6250)⟩,
  ⟨(15131/10000), (31/20), true, (6587/5000), (13081/12500), false, (3844/3125), (62249/50000), (21947/20000), (3783/5000), (50219/50000), (7941/10000), (110381/100000)⟩,
]

def bandC1 : List PieceLSeg := [
  ⟨(31/20), (779/500), (13251/10000), (20913/20000), false, (62249/50000), (124819/100000), (110259/100000), [.sec0 (31/320) (42703/100000) (969/10000) (100639/100000), .sec (31/320) (31/160) (42703/100000) (5869/10000) (969/5000) (20271/20000), .sec (31/160) (93/320) (5869/10000) (69963/100000) (1453/5000) (102169/100000), .sec (93/320) (31/80) (69963/100000) (78741/100000) (31/80) (103111/100000), .tan (31/80) (71/120) (78741/100000) (5917/10000) (52879/50000), .tan (71/120) (191/240) (92543/100000) (3979/5000) (55219/50000), .tan (191/240) 1 (12819/12500) (3979/5000) (55219/50000)]⟩,
  ⟨(779/500), (1567/1000), (13281/10000), (104533/100000), false, (124819/100000), (125179/100000), (11037/10000), [.sec0 (779/8000) (42813/100000) (487/5000) (50321/50000), .sec (779/8000) (779/4000) (42813/100000) (58841/100000) (487/2500) (101363/100000), .sec (779/4000) (2337/8000) (58841/100000) (70143/100000) (2921/10000) (51091/50000), .sec (2337/8000) (779/2000) (70143/100000) (2467/3125) (779/2000) (25783/25000), .tan (779/2000) (593/1000) (2467/3125) (593/1000) (105779/100000), .tan (593/1000) (1593/2000) (18537/20000) (1593/2000) (55231/50000), .tan (1593/2000) 1 (10267/10000) (1593/2000) (55231/50000)]⟩,
  ⟨(1567/1000), (197/125), (13311/10000), (209/200), false, (125179/100000), (62769/50000), (55247/50000), [.sec0 (1567/16000) (42937/100000) (979/10000) (50323/50000), .sec (1567/16000) (1567/8000) (42937/100000) (59011/100000) (1959/10000) (25343/25000), .sec (1567/8000) (4701/16000) (59011/100000) (35173/50000) (1469/5000) (102197/100000), .sec (4701/16000) (1567/4000) (35173/50000) (79171/100000) (1959/5000) (25789/25000), .tan (1567/4000) (1189/2000) (79171/100000) (1189/2000) (105803/100000), .tan (1189/2000) (3189/4000) (92843/100000) (1993/2500) (55243/50000), .tan (3189/4000) 1 (51401/50000) (1993/2500) (55243/50000)]⟩,
  ⟨(197/125), (1587/1000), (2669/2000), (6529/6250), false, (62769/50000), (15747/12500), (110617/100000), [.sec0 (197/2000) (2153/5000) (197/2000) (2013/2000), .sec (197/2000) (197/1000) (2153/5000) (2959/5000) (197/1000) (5069/5000), .sec (197/1000) (591/2000) (2959/5000) (70547/100000) (591/2000) (102213/100000), .sec (591/2000) (197/500) (70547/100000) (39699/50000) (197/500) (103179/100000), .tan (197/500) (149/250) (39699/50000) (149/250) (26457/25000), .tan (149/250) (399/500) (93001/100000) (399/500) (110513/100000), .tan (399/500) 1 (102933/100000) (399/500) (110513/100000)]⟩,
  ⟨(1587/1000), (1599/1000), (1673/1250), (104423/100000), false, (15747/12500), (126451/100000), (55383/50000), [.sec0 (1587/16000) (4321/10000) (62/625) (20131/20000), .sec (1587/16000) (1587/8000) (4321/10000) (29693/50000) (124/625) (101391/100000), .sec (1587/8000) (4761/16000) (29693/50000) (70793/100000) (186/625) (12779/12500), .sec (4761/16000) (1587/4000) (70793/100000) (3187/4000) (248/625) (103209/100000), .tan (1587/4000) (3587/6000) (3187/4000) (2989/5000) (105857/100000), .tan (3587/6000) (9587/12000) (46597/50000) (7989/10000) (6909/6250), .tan (9587/12000) 1 (103093/100000) (7989/10000) (6909/6250)]⟩,
  ⟨(1599/1000), (403/250), (13427/10000), (104377/100000), false, (126451/100000), (31741/25000), (110927/100000), [.sec0 (1599/16000) (43373/100000) (999/10000) (100659/100000), .sec (1599/16000) (1599/8000) (43373/100000) (5961/10000) (1999/10000) (101403/100000), .sec (1599/8000) (4797/16000) (5961/10000) (3553/5000) (1499/5000) (25563/25000), .sec (4797/16000) (1599/4000) (3553/5000) (3199/4000) (1999/5000) (51621/50000), .tan (1599/4000) (3599/6000) (3199/4000) (2999/5000) (10589/10000), .tan (3599/6000) (9599/12000) (93403/100000) (7999/10000) (55289/50000), .tan (9599/12000) 1 (51633/50000) (7999/10000) (55289/50000)]⟩,
  ⟨(403/250), (1627/1000), (6737/5000), (13041/12500), false, (31741/25000), (127553/100000), (1111/1000), [.sec0 (403/4000) (43549/100000) (63/625) (50333/50000), .sec (403/4000) (403/2000) (43549/100000) (14963/25000) (403/2000) (12677/12500), .sec (403/2000) (1209/4000) (14963/25000) (17837/25000) (1511/5000) (51137/50000), .sec (1209/4000) (403/1000) (17837/25000) (803/1000) (403/1000) (25819/25000), .tan (403/1000) (301/500) (803/1000) (301/500) (105927/100000), .tan (301/500) (801/1000) (93629/100000) (801/1000) (13827/12500), .tan (801/1000) 1 (25863/25000) (801/1000) (13827/12500)]⟩,
  ⟨(1627/1000), (411/250), (13527/10000), (104273/100000), false, (127553/100000), (64109/50000), (3478/3125), [.sec0 (1627/16000) (43751/100000) (1017/10000) (3146/3125), .sec (1627/16000) (1627/8000) (43751/100000) (6013/10000) (1017/5000) (101431/100000), .sec (1627/8000) (4881/16000) (6013/10000) (448/625) (3051/10000) (1023/1000), .sec (4881/16000) (1627/4000) (448/625) (80673/100000) (1017/2500) (103317/100000), .tan (1627/4000) (1209/2000) (80673/100000) (1209/2000) (6623/6250), .tan (1209/2000) (3209/4000) (2934/3125) (4011/5000) (55329/50000), .tan (3209/4000) 1 (6479/6250) (4011/5000) (55329/50000)]⟩,
  ⟨(411/250), (208/125), (13589/10000), (104209/100000), false, (64109/50000), (32249/25000), (27879/25000), [.sec0 (411/4000) (43979/100000) (257/2500) (2517/2500), .sec (411/4000) (411/2000) (43979/100000) (60443/100000) (411/2000) (12681/12500), .sec (411/2000) (1233/4000) (60443/100000) (72053/100000) (3083/10000) (10233/10000), .sec (1233/4000) (411/1000) (72053/100000) (81093/100000) (411/1000) (103363/100000), .tan (411/1000) (911/1500) (81093/100000) (6073/10000) (21203/20000), .tan (911/1500) (2411/3000) (94181/100000) (8037/10000) (110711/100000), .tan (2411/3000) 1 (103903/100000) (8037/10000) (110711/100000)]⟩,
  ⟨(208/125), (1687/1000), (13659/10000), (52069/50000), false, (32249/25000), (32471/25000), (11177/10000), [.sec0 (13/125) (22123/50000) (13/125) (6293/6250), .sec (13/125) (26/125) (22123/50000) (6081/10000) (26/125) (25367/25000), .sec (26/125) (39/125) (6081/10000) (7249/10000) (39/125) (25591/25000), .sec (39/125) (52/125) (7249/10000) (16317/20000) (52/125) (51709/50000), .tan (52/125) (229/375) (16317/20000) (6107/10000) (106073/100000), .tan (229/375) (302/375) (94523/100000) (1607/2000) (6919/6250), .tan (302/375) 1 (52091/50000) (8053/10000) (6923/6250)]⟩,
  ⟨(1687/1000), (1713/1000), (687/500), (13007/12500), false, (32471/25000), (130881/100000), (112057/100000), [.sec0 (1687/16000) (44551/100000) (527/5000) (50349/50000), .sec (1687/16000) (1687/8000) (44551/100000) (61229/100000) (2109/10000) (101491/100000), .sec (1687/8000) (5061/16000) (61229/100000) (72989/100000) (3163/10000) (25601/25000), .sec (5061/16000) (1687/4000) (72989/100000) (82147/100000) (2109/5000) (103483/100000), .tan (1687/4000) (1229/2000) (82147/100000) (1229/2000) (53069/50000), .tan (1229/2000) (3229/4000) (47457/50000) (4013/5000) (6917/6250), .tan (3229/4000) 1 (52249/50000) (1009/1250) (22167/20000)]⟩,
  ⟨(1713/1000), (871/500), (13829/10000), (103967/100000), false, (130881/100000), (8249/6250), (899/800), [.sec0 (1713/16000) (44893/100000) (1071/10000) (10071/10000), .sec (1713/16000) (1713/8000) (44893/100000) (61699/100000) (2141/10000) (101517/100000), .sec (1713/8000) (5139/16000) (61699/100000) (1471/2000) (803/2500) (2049/2000), .sec (5139/16000) (1713/4000) (1471/2000) (82777/100000) (2141/5000) (20711/20000), .tan (1713/4000) (3713/6000) (82777/100000) (1547/2500) (106213/100000), .tan (3713/6000) (9713/12000) (95353/100000) (8017/10000) (110641/100000), .tan (9713/12000) 1 (104851/100000) (4047/5000) (22183/20000)]⟩,
  ⟨(871/500), (71/40), (1741/1250), (10387/10000), false, (8249/6250), (133229/100000), (56361/50000), [.sec0 (871/8000) (45271/100000) (1089/10000) (100723/100000), .sec (871/8000) (871/4000) (45271/100000) (62219/100000) (1089/5000) (101547/100000), .sec (871/4000) (2613/8000) (62219/100000) (7417/10000) (1633/5000) (51251/50000), .sec (2613/8000) (871/2000) (7417/10000) (3339/4000) (871/2000) (51819/50000), .tan (871/2000) (1871/3000) (3339/4000) (6237/10000) (53149/50000), .tan (1871/3000) (4871/6000) (95839/100000) (8007/10000) (55303/50000), .tan (4871/6000) 1 (105239/100000) (4059/5000) (111003/100000)]⟩,
]

def bandC2 : List PieceLSeg := [
  ⟨(71/40), (453/250), (14039/10000), (51881/50000), false, (133229/100000), (13461/10000), (56553/50000), [.sec0 (71/640) (22849/50000) (1109/10000) (100737/100000), .sec (71/640) (71/320) (22849/50000) (12561/20000) (2219/10000) (5079/5000), .sec (71/320) (213/640) (12561/20000) (74869/100000) (208/625) (102561/100000), .sec (213/640) (71/160) (74869/100000) (42131/50000) (2219/5000) (51867/50000), .tan (71/160) (151/240) (42131/50000) (1573/2500) (26599/25000), .tan (151/240) (391/480) (96387/100000) (1999/2500) (13821/12500), .tan (391/480) 1 (52837/50000) (4073/5000) (111107/100000)]⟩,
  ⟨(453/250), (1853/1000), (7081/5000), (20729/20000), false, (13461/10000), (34031/25000), (28381/25000), [.sec0 (453/4000) (11543/25000) (283/2500) (100753/100000), .sec (453/4000) (453/2000) (11543/25000) (63457/100000) (453/2000) (50809/50000), .sec (453/2000) (1359/4000) (63457/100000) (15129/20000) (1699/5000) (102629/100000), .sec (1359/4000) (453/1000) (15129/20000) (5321/6250) (453/1000) (51921/50000), .tan (453/1000) (953/1500) (5321/6250) (6353/10000) (106507/100000), .tan (953/1500) (2453/3000) (19399/20000) (499/625) (110527/100000), .tan (2453/3000) 1 (106153/100000) (8177/10000) (13903/12500)]⟩,
  ⟨(1853/1000), (949/500), (2859/2000), (103521/100000), false, (34031/25000), (137767/100000), (113973/100000), [.sec0 (1853/16000) (46691/100000) (579/5000) (25193/25000), .sec (1853/16000) (1853/8000) (46691/100000) (6417/10000) (579/2500) (5083/5000), .sec (1853/8000) (5559/16000) (6417/10000) (4781/6250) (1737/5000) (102703/100000), .sec (5559/16000) (1853/4000) (4781/6250) (86093/100000) (579/1250) (25991/25000), .tan (1853/4000) (3853/6000) (86093/100000) (3211/5000) (53317/50000), .tan (3853/6000) (9853/12000) (97663/100000) (7971/10000) (55241/50000), .tan (9853/12000) 1 (4267/4000) (8211/10000) (22271/20000)]⟩,
  ⟨(949/500), (1947/1000), (14439/10000), (103389/100000), false, (137767/100000), (69767/50000), (2289/2000), [.sec0 (949/8000) (9451/20000) (593/5000) (12599/12500), .sec (949/8000) (949/4000) (9451/20000) (12989/20000) (593/2500) (50853/50000), .sec (949/4000) (2847/8000) (12989/20000) (77419/100000) (3559/10000) (102787/100000), .sec (2847/8000) (949/2000) (77419/100000) (87133/100000) (949/2000) (104103/100000), .tan (949/2000) (1949/3000) (87133/100000) (6497/10000) (4271/4000), .tan (1949/3000) (4949/6000) (98387/100000) (7957/10000) (22087/20000), .tan (4949/6000) 1 (21447/20000) (1031/1250) (111501/100000)]⟩,
  ⟨(1947/1000), 2, (14593/10000), (103251/100000), false, (69767/50000), (141421/100000), (2299/2000), [.sec0 (1947/16000) (47861/100000) (1217/10000) (50407/50000), .sec (1947/16000) (1947/8000) (47861/100000) (32889/50000) (1217/5000) (50879/50000), .sec (1947/8000) (5841/16000) (32889/50000) (19603/25000) (3651/10000) (102879/100000), .sec (5841/16000) (1947/4000) (19603/25000) (353/400) (1217/2500) (104257/100000), .tan (1947/4000) (3947/6000) (353/400) (3289/5000) (106931/100000), .tan (3947/6000) (9947/12000) (99167/100000) (7943/10000) (27597/25000), .tan (9947/12000) 1 (107833/100000) (8289/10000) (55833/50000)]⟩,
  ⟨2, (2057/1000), (3689/2500), (103109/100000), false, (141421/100000), (71711/50000), (115471/100000), [.sec0 (1/8) (12127/25000) (1/8) (50419/50000), .sec (1/8) (1/4) (12127/25000) (66667/100000) (1/4) (50907/50000), .sec (1/4) (3/8) (66667/100000) (4967/6250) (3/8) (102981/100000), .sec (3/8) (1/2) (4967/6250) (89443/100000) (1/2) (104427/100000), .tan (1/2) (2/3) (89443/100000) (6667/10000) (26777/25000), .tan (2/3) (5/6) 1 (7929/10000) (110341/100000), .tan (5/6) 1 (54233/50000) (8333/10000) (13981/12500)]⟩,
  ⟨(2057/1000), (1059/500), (14929/10000), (102961/100000), false, (71711/50000), (145533/100000), (14501/12500), [.sec0 (2057/16000) (24597/50000) (643/5000) (3152/3125), .sec (2057/16000) (2057/8000) (24597/50000) (6761/10000) (2571/10000) (50937/50000), .sec (2057/8000) (6171/16000) (6761/10000) (80597/100000) (3857/10000) (25773/25000), .sec (6171/16000) (2057/4000) (80597/100000) (90709/100000) (2571/5000) (20923/20000), .tan (2057/4000) (4057/6000) (90709/100000) (3381/5000) (107301/100000), .tan (4057/6000) (10057/12000) (20177/20000) (3957/5000) (110291/100000), .tan (10057/12000) 1 (109131/100000) (8381/10000) (28013/25000)]⟩,
  ⟨(1059/500), (1091/500), (15109/10000), (102811/100000), false, (145533/100000), (29543/20000), (58279/50000), [.sec0 (1059/8000) (24959/50000) (331/2500) (100891/100000), .sec (1059/8000) (1059/4000) (24959/50000) (34303/50000) (331/1250) (101941/100000), .sec (1059/4000) (3177/8000) (34303/50000) (81783/100000) (3971/10000) (103213/100000), .sec (3177/8000) (1059/2000) (81783/100000) (23011/25000) (1059/2000) (4193/4000), .tan (1059/2000) (2059/3000) (23011/25000) (6863/10000) (53757/50000), .tan (2059/3000) (5059/6000) (5091/5000) (7899/10000) (55121/50000), .tan (5059/6000) 1 (54913/50000) (527/625) (112277/100000)]⟩,
  ⟨(1091/500), (281/125), (7647/5000), (102661/100000), false, (29543/20000), (149933/100000), (11711/10000), [.sec0 (1091/8000) (50667/100000) (341/2500) (2523/2500), .sec (1091/8000) (1091/4000) (50667/100000) (34817/50000) (341/1250) (10201/10000), .sec (1091/4000) (3273/8000) (34817/50000) (8301/10000) (4091/10000) (51671/50000), .sec (3273/8000) (1091/2000) (8301/10000) (5839/6250) (1091/2000) (105051/100000), .tan (1091/2000) (697/1000) (5839/6250) (697/1000) (26937/25000), .tan (697/1000) (1697/2000) (102787/100000) (1971/2500) (110193/100000), .tan (1697/2000) 1 (55269/50000) (1697/2000) (56259/50000)]⟩,
  ⟨(281/125), (579/250), (15481/10000), (102513/100000), false, (149933/100000), (19023/12500), (58827/50000), [.sec0 (281/2000) (51427/100000) (281/2000) (2019/2000), .sec (281/2000) (281/1000) (51427/100000) (1767/2500) (281/1000) (102083/100000), .sec (281/1000) (843/2000) (1767/2500) (2633/3125) (843/2000) (103479/100000), .sec (843/2000) (281/500) (2633/3125) (94827/100000) (281/500) (21059/20000), .tan (281/500) (177/250) (94827/100000) (177/250) (107997/100000), .tan (177/250) (427/500) (25943/25000) (787/1000) (110147/100000), .tan (427/500) 1 (13907/12500) (427/500) (56389/50000)]⟩,
  ⟨(579/250), (1193/500), (15671/10000), (102367/100000), false, (19023/12500), (77233/50000), (118189/100000), [.sec0 (579/4000) (52199/100000) (181/1250) (50491/50000), .sec (579/4000) (579/2000) (52199/100000) (71741/100000) (579/2000) (102159/100000), .sec (579/2000) (1737/4000) (71741/100000) (85521/100000) (2171/5000) (103623/100000), .sec (1737/4000) (579/1000) (85521/100000) (77/80) (579/1000) (21111/20000), .tan (579/1000) (1079/1500) (77/80) (7193/10000) (13533/12500), .tan (1079/1500) (2579/3000) (104773/100000) (491/625) (55051/50000), .tan (2579/3000) 1 (55989/50000) (8597/10000) (113059/100000)]⟩,
  ⟨(1193/500), (2457/1000), (7931/5000), (6389/6250), false, (77233/50000), (39187/25000), (29679/25000), [.sec0 (1193/8000) (26491/50000) (1491/10000) (50507/50000), .sec (1193/8000) (1193/4000) (26491/50000) (72817/100000) (1491/5000) (102237/100000), .sec (1193/4000) (3579/8000) (72817/100000) (86803/100000) (2237/5000) (3243/3125), .sec (3579/8000) (1193/2000) (86803/100000) (48847/50000) (1193/2000) (26459/25000), .tan (1193/2000) (731/1000) (48847/50000) (731/1000) (13569/12500), .tan (731/1000) (1731/2000) (105789/100000) (7843/10000) (110061/100000), .tan (1731/2000) 1 (22541/20000) (1731/2000) (56679/50000)]⟩,
  ⟨(2457/1000), (2529/1000), (16053/10000), (20417/20000), false, (39187/25000), (39757/25000), (59613/50000), [.sec0 (2457/16000) (10753/20000) (96/625) (101047/100000), .sec (2457/16000) (2457/8000) (10753/20000) (18473/25000) (3071/10000) (102319/100000), .sec (2457/8000) (7371/16000) (18473/25000) (17617/20000) (4607/10000) (51967/50000), .sec (7371/16000) (2457/4000) (17617/20000) (99137/100000) (3071/5000) (106133/100000), .tan (2457/4000) (4457/6000) (99137/100000) (1857/2500) (108857/100000), .tan (4457/6000) (10457/12000) (106807/100000) (783/1000) (110019/100000), .tan (10457/12000) 1 (56713/50000) (4357/5000) (28419/25000)]⟩,
]

def bandC3 : List PieceLSeg := [
  ⟨(2529/1000), (2601/1000), (8103/5000), (101977/100000), false, (39757/25000), (40319/25000), (2993/2500), [.sec0 (2529/16000) (54547/100000) (1581/10000) (101081/100000), .sec (2529/16000) (2529/8000) (54547/100000) (74967/100000) (3161/10000) (102403/100000), .sec (2529/8000) (7587/16000) (74967/100000) (89367/100000) (2371/5000) (104099/100000), .sec (7587/16000) (2529/4000) (89367/100000) (100579/100000) (3161/5000) (2129/2000), .tan (2529/4000) (4529/6000) (100579/100000) (1887/2500) (54591/50000), .tan (4529/6000) (10529/12000) (107827/100000) (3913/5000) (110007/100000), .tan (10529/12000) 1 (57071/50000) (4387/5000) (3563/3125)]⟩,
  ⟨(2601/1000), (2671/1000), (16351/10000), (25469/25000), false, (40319/25000), (163431/100000), (3756/3125), [.sec0 (2601/16000) (27659/50000) (813/5000) (20223/20000), .sec (2601/16000) (2601/8000) (27659/50000) (76027/100000) (3251/10000) (102487/100000), .sec (2601/8000) (7803/16000) (76027/100000) (9063/10000) (4877/10000) (26067/25000), .sec (7803/16000) (2601/4000) (9063/10000) (51/50) (3251/5000) (21357/20000), .tan (2601/4000) (4601/6000) (51/50) (1917/2500) (4381/4000), .tan (4601/6000) (10601/12000) (108833/100000) (489/625) (11/10), .tan (10601/12000) 1 (114843/100000) (4417/5000) (183/160)]⟩,
  ⟨(2671/1000), (2737/1000), (8243/5000), (12723/12500), false, (163431/100000), (82719/50000), (15079/12500), [.sec0 (2671/16000) (56057/100000) (1669/10000) (101147/100000), .sec (2671/16000) (2671/8000) (56057/100000) (77043/100000) (3339/10000) (102571/100000), .sec (2671/8000) (8013/16000) (77043/100000) (91841/100000) (313/625) (104437/100000), .sec (8013/16000) (2671/4000) (91841/100000) (25841/25000) (3339/5000) (10713/10000), .tan (2671/4000) (1557/2000) (25841/25000) (1557/2000) (54939/50000), .tan (1557/2000) (3557/4000) (109801/100000) (7823/10000) (109997/100000), .tan (3557/4000) 1 (14439/12500) (2223/2500) (5737/5000)]⟩,
  ⟨(2737/1000), (2803/1000), (2081/1250), (25419/25000), false, (82719/50000), (167421/100000), (12103/10000), [.sec0 (2737/16000) (28373/50000) (1711/10000) (101179/100000), .sec (2737/16000) (2737/8000) (28373/50000) (77989/100000) (3421/10000) (102651/100000), .sec (2737/8000) (8211/16000) (77989/100000) (92969/100000) (1283/2500) (52301/50000), .sec (8211/16000) (2737/4000) (92969/100000) (104633/100000) (3421/5000) (107469/100000), .tan (2737/4000) (1579/2000) (104633/100000) (489/625) (11/10), .tan (1579/2000) (3579/4000) (110703/100000) (1579/2000) (110229/100000), .tan (3579/4000) 1 (116131/100000) (2237/2500) (14389/12500)]⟩,
  ⟨(2803/1000), (2871/1000), (3363/2000), (101567/100000), false, (167421/100000), (1059/625), (121413/100000), [.sec0 (2803/16000) (28713/50000) (219/1250) (101211/100000), .sec (2803/16000) (2803/8000) (28713/50000) (19731/25000) (219/625) (25683/25000), .sec (2803/8000) (8409/16000) (19731/25000) (94083/100000) (657/1250) (10477/10000), .sec (8409/16000) (2803/4000) (94083/100000) (105887/100000) (438/625) (107833/100000), .tan (2803/4000) (1601/2000) (105887/100000) (1953/2500) (109963/100000), .tan (1601/2000) (3601/4000) (27899/25000) (1601/2000) (110599/100000), .tan (3601/4000) 1 (5837/5000) (4501/5000) (28873/25000)]⟩,
  ⟨(2871/1000), (2941/1000), (8493/5000), (101459/100000), false, (1059/625), (171493/100000), (121793/100000), [.sec0 (2871/16000) (29059/50000) (897/5000) (101243/100000), .sec (2871/16000) (2871/8000) (29059/50000) (639/800) (3589/10000) (102817/100000), .sec (2871/8000) (8613/16000) (639/800) (47609/50000) (5383/10000) (26237/25000), .sec (8613/16000) (2871/4000) (47609/50000) (26791/25000) (3589/5000) (27057/25000), .tan (2871/4000) (4871/6000) (26791/25000) (7801/10000) (13741/12500), .tan (4871/6000) (10871/12000) (56253/50000) (4059/5000) (111003/100000), .tan (10871/12000) 1 (117357/100000) (9059/10000) (115917/100000)]⟩,
  ⟨(2941/1000), (3013/1000), (429/250), (101351/100000), false, (171493/100000), (173579/100000), (122169/100000), [.sec0 (2941/16000) (29411/50000) (919/5000) (101277/100000), .sec (2941/16000) (2941/8000) (29411/50000) (80843/100000) (919/2500) (20581/20000), .sec (2941/8000) (8823/16000) (80843/100000) (96371/100000) (2757/5000) (105137/100000), .sec (8823/16000) (2941/4000) (96371/100000) (54231/50000) (919/1250) (108659/100000), .tan (2941/4000) (1647/2000) (54231/50000) (779/1000) (54947/50000), .tan (1647/2000) (3647/4000) (56717/50000) (1647/2000) (111449/100000), .tan (3647/4000) 1 (58991/50000) (4559/5000) (29097/25000)]⟩,
  ⟨(3013/1000), (1543/500), (3467/2000), (20249/20000), false, (173579/100000), (17567/10000), (122541/100000), [.sec0 (3013/16000) (29769/50000) (1883/10000) (3166/3125), .sec (3013/16000) (3013/8000) (29769/50000) (81827/100000) (1883/5000) (102997/100000), .sec (3013/8000) (9039/16000) (81827/100000) (12193/12500) (5649/10000) (52669/50000), .sec (9039/16000) (3013/4000) (12193/12500) (54891/50000) (1883/2500) (54569/50000), .tan (3013/4000) (1671/2000) (54891/50000) (389/500) (109863/100000), .tan (1671/2000) (3671/4000) (57189/50000) (1671/2000) (111941/100000), .tan (3671/4000) 1 (23723/20000) (4589/5000) (116901/100000)]⟩,
  ⟨(1543/500), (3163/1000), (3503/2000), (101139/100000), false, (17567/10000), (22231/12500), (15363/12500), [.sec0 (1543/8000) (12051/20000) (1929/10000) (25337/25000), .sec (1543/8000) (1543/4000) (12051/20000) (20703/25000) (1929/5000) (103093/100000), .sec (1543/4000) (4629/8000) (20703/25000) (98719/100000) (2893/5000) (105549/100000), .sec (4629/8000) (1543/2000) (98719/100000) (3472/3125) (1543/2000) (21933/20000), .tan (1543/2000) (2543/3000) (3472/3125) (7769/10000) (109829/100000), .tan (2543/3000) (5543/6000) (57663/50000) (8477/10000) (112481/100000), .tan (5543/6000) 1 (119247/100000) (4619/5000) (7341/6250)]⟩,
  ⟨(3163/1000), (3243/1000), (17701/10000), (12629/12500), false, (22231/12500), (180083/100000), (15409/12500), [.sec0 (3163/16000) (30501/50000) (1977/10000) (50693/50000), .sec (3163/16000) (3163/8000) (30501/50000) (83839/100000) (1977/5000) (51597/50000), .sec (3163/8000) (9489/16000) (83839/100000) (99943/100000) (5931/10000) (5289/5000), .sec (9489/16000) (3163/4000) (99943/100000) (56241/50000) (1937/2500) (21953/20000), .tan (3163/4000) (1721/2000) (56241/50000) (7907/10000) (27567/25000), .tan (1721/2000) (3721/4000) (29079/25000) (1721/2000) (1131/1000), .tan (3721/4000) 1 (3747/3125) (4651/5000) (59051/50000)]⟩,
  ⟨(3243/1000), (133/40), (1789/1000), (50463/50000), false, (180083/100000), (36469/20000), (61819/50000), [.sec0 (3243/16000) (61769/100000) (2027/10000) (4057/4000), .sec (3243/16000) (3243/8000) (61769/100000) (84893/100000) (2027/5000) (51651/50000), .sec (3243/8000) (9729/16000) (84893/100000) (101199/100000) (6081/10000) (106029/100000), .sec (9729/16000) (3243/4000) (101199/100000) (22779/20000) (3869/5000) (54867/50000), .tan (3243/4000) (5243/6000) (22779/20000) (2027/2500) (55483/50000), .tan (5243/6000) (11243/12000) (58667/50000) (4369/5000) (11381/10000), .tan (11243/12000) 1 (4823/4000) (9369/10000) (118849/100000)]⟩,
  ⟨(133/40), (3411/1000), (3617/2000), (5041/5000), false, (36469/20000), (11543/6250), (123999/100000), [.sec0 (133/640) (12509/20000) (1039/5000) (50733/50000), .sec (133/640) (133/320) (12509/20000) (85959/100000) (1039/2500) (51707/50000), .sec (133/320) (399/640) (85959/100000) (10247/10000) (3117/5000) (106293/100000), .sec (399/640) (133/160) (10247/10000) (57663/50000) (483/625) (13713/12500), .tan (133/160) (71/80) (57663/50000) (1039/1250) (1397/1250), .tan (71/80) (151/160) (59183/50000) (71/80) (114631/100000), .tan (151/160) 1 (121253/100000) (4719/5000) (119713/100000)]⟩,
  ⟨(3411/1000), (438/125), (18291/10000), (100711/100000), false, (11543/6250), (187189/100000), (62181/50000), [.sec0 (3411/16000) (15837/25000) (533/2500) (101509/100000), .sec (3411/16000) (3411/8000) (15837/25000) (10883/12500) (533/1250) (51767/50000), .sec (3411/8000) (10233/16000) (10883/12500) (103787/100000) (1599/2500) (53293/50000), .sec (10233/16000) (3411/4000) (103787/100000) (14601/12500) (3859/5000) (54837/50000), .tan (3411/4000) (5411/6000) (14601/12500) (533/625) (112721/100000), .tan (5411/6000) (11411/12000) (119437/100000) (4509/5000) (115609/100000), .tan (11411/12000) 1 (3811/3125) (9509/10000) (120727/100000)]⟩,
]

def bandC4 : List PieceLSeg := [
  ⟨(438/125), (721/200), (18511/10000), (50299/50000), false, (187189/100000), (47467/25000), (62369/50000), [.sec0 (219/1000) (32103/50000) (219/1000) (25389/25000), .sec (219/1000) (219/500) (32103/50000) (88243/100000) (219/500) (103667/100000), .sec (219/500) (657/1000) (88243/100000) (13149/12500) (657/1000) (26729/25000), .sec (657/1000) (219/250) (13149/12500) (11839/10000) (1927/2500) (27411/25000), .tan (219/250) (344/375) (11839/10000) (219/250) (7121/6250), .tan (344/375) (719/750) (120583/100000) (9173/10000) (116857/100000), .tan (719/750) 1 (122697/100000) (9587/10000) (3051/2500)]⟩,
  ⟨(721/200), (1861/500), (3751/2000), (100477/100000), false, (47467/25000), (48231/25000), (15641/12500), [.sec0 (721/3200) (521/800) (2253/10000) (12701/12500), .sec (721/3200) (721/1600) (521/800) (17901/20000) (2253/5000) (51907/50000), .sec (721/1600) (2163/3200) (17901/20000) (106697/100000) (6759/10000) (21459/20000), .sec (2163/3200) (721/800) (106697/100000) (30021/25000) (481/625) (13701/12500), .tan (721/800) (1121/1200) (30021/25000) (2253/2500) (23113/20000), .tan (1121/1200) (2321/2400) (121813/100000) (4671/5000) (59269/50000), .tan (2321/2400) 1 (61747/50000) (9671/10000) (123787/100000)]⟩,
  ⟨(1861/500), (3863/1000), (238/125), (5017/5000), false, (48231/25000), (39309/20000), (125557/100000), [.sec0 (1861/8000) (66173/100000) (1163/5000) (25417/25000), .sec (1861/8000) (1861/4000) (66173/100000) (45473/50000) (1163/2500) (103989/100000), .sec (1861/4000) (5583/8000) (45473/50000) (21683/20000) (6979/10000) (13471/12500), .sec (5583/8000) (1861/2000) (21683/20000) (122017/100000) (7683/10000) (10957/10000), .tan (1861/2000) (2861/3000) (122017/100000) (1861/2000) (59067/50000), .tan (2861/3000) (5861/6000) (6161/5000) (9537/10000) (121171/100000), .tan (5861/6000) 1 (311/250) (1221/1250) (126519/100000)]⟩,
  ⟨(3863/1000), (4043/1000), (1939/1000), (5009/5000), false, (39309/20000), (12567/6250), (25209/20000), [.sec0 (3863/16000) (13483/20000) (1207/5000) (101741/100000), .sec (3863/16000) (3863/8000) (13483/20000) (92653/100000) (4829/10000) (6513/6250), .sec (3863/8000) (11589/16000) (92653/100000) (110449/100000) (7243/10000) (21677/20000), .sec (11589/16000) (3863/4000) (110449/100000) (124307/100000) (3833/5000) (1369/1250), .tan (3863/4000) (5863/6000) (124307/100000) (4829/5000) (123487/100000), .tan (5863/6000) (11863/12000) (31223/25000) (2443/2500) (3958/3125), .tan (11863/12000) 1 (125471/100000) (4943/5000) (16533/12500)]⟩,
  ⟨(4043/1000), (4293/1000), (19849/10000), (100019/100000), true, (12567/6250), (41439/20000), (63313/50000), [.sec0 (1/4) (68621/100000) (1/4) (50907/50000), .sec (1/4) (1/2) (68621/100000) (94337/100000) (1/2) (104427/100000), .sec (1/2) (3/4) (94337/100000) (22497/20000) (3/4) (2181/2000), .sec (3/4) 1 (22497/20000) (63313/50000) (1911/2500) (21891/20000)]⟩,
  ⟨(4293/1000), (4671/1000), (2563/1250), (100283/100000), true, (41439/20000), (54031/25000), (31841/25000), [.sec0 (1/4) (34369/50000) (1/4) (50907/50000), .sec (1/4) (1/2) (34369/50000) (94641/100000) (1/2) (104427/100000), .sec (1/2) (3/4) (94641/100000) (113001/100000) (3747/5000) (54517/50000), .sec (3/4) 1 (113001/100000) (31841/25000) (3803/5000) (54673/50000)]⟩,
  ⟨(4671/1000), (2687/500), (21591/10000), (100673/100000), true, (54031/25000), (115909/50000), (128349/100000), [.sec0 (1/4) (17223/25000) (1/4) (50907/50000), .sec (1/4) (1/2) (17223/25000) (95043/100000) (1/2) (104427/100000), .sec (1/2) (3/4) (95043/100000) (14211/12500) (7401/10000) (54393/50000), .sec (3/4) 1 (14211/12500) (128349/100000) (3769/5000) (21831/20000)]⟩,
  ⟨(2687/500), (3669/500), (23961/10000), (50679/50000), true, (115909/50000), (270887/100000), (25971/20000), [.sec0 (1/4) (34561/50000) (1/4) (50907/50000), .sec (1/4) (1/2) (34561/50000) (1913/2000) (1/2) (104427/100000), .sec (1/2) (3/4) (1913/2000) (11473/10000) (3607/5000) (21663/20000), .sec (3/4) 1 (11473/10000) (25971/20000) (3/4) (2181/2000)]⟩,
  ⟨(3669/500), (323/25), (7523/2500), (25607/25000), true, (270887/100000), (89861/25000), (132671/100000), [.sec0 (1/4) (69537/100000) (1/4) (50907/50000), .sec (1/4) (1/2) (69537/100000) (48379/50000) (1/2) (104427/100000), .sec (1/2) (3/4) (48379/50000) (58329/50000) (6929/10000) (107657/100000), .sec (3/4) 1 (58329/50000) (132671/100000) (3/4) (2181/2000)]⟩,
  ⟨(323/25), 25, (10299/2500), (20641/20000), true, (89861/25000), 5, (136247/100000), [.sec0 (1/4) (70037/100000) (1/4) (50907/50000), .sec (1/4) (1/2) (70037/100000) (2453/2500) (1/2) (104427/100000), .sec (1/2) (3/4) (2453/2500) (29767/25000) (3411/5000) (107427/100000), .sec (3/4) 1 (29767/25000) (136247/100000) (3/4) (2181/2000)]⟩,
]

def bandD : List NoLeisureTanSeg := [
  ⟨25, (4401/100), (56609/10000), (103539/100000), true, 5, (3317/500), (34669/25000)⟩,
  ⟨(4401/100), 50, (65993/10000), (103619/100000), true, (3317/500), (353553/50000), (69921/50000)⟩,
]

/-! ## 7. Certificación en el kernel de las 5 bandas y ensamblado global -/

set_option maxHeartbeats 1600000 in
theorem bandA_ok :
    ChainOk NoLeisureSecSeg.kL NoLeisureSecSeg.kR NoLeisureSecSeg.valid (1/25000) (11/200) bandA := by
  simp only [bandA, ChainOk]
  repeat' constructor
  all_goals norm_num [NoLeisureSecSeg.valid, log_ub_ok, c0_ub_q, slope_q,
    lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandB1_ok :
    ChainOk TanLSeg.kL TanLSeg.kR TanLSeg.valid (11/200) (1/4) bandB1 := by
  simp only [bandB1, ChainOk]
  repeat' constructor
  all_goals norm_num [TanLSeg.valid, L_affine_ok, L_corner, log_ub_ok,
    log_ub_le1_ok, log_ub_le1_val, c0_ub_q, slope_q, lam_max_q, const_base_q,
    log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandB2a_ok :
    ChainOk TanLSeg.kL TanLSeg.kR TanLSeg.valid (1/4) (1509/2000) bandB2a := by
  simp only [bandB2a, ChainOk]
  repeat' constructor
  all_goals norm_num [TanLSeg.valid, L_affine_ok, L_corner, log_ub_ok,
    log_ub_le1_ok, log_ub_le1_val, c0_ub_q, slope_q, lam_max_q, const_base_q,
    log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandB2b_ok :
    ChainOk TanLSeg.kL TanLSeg.kR TanLSeg.valid (1509/2000) (31/20) bandB2b := by
  simp only [bandB2b, ChainOk]
  repeat' constructor
  all_goals norm_num [TanLSeg.valid, L_affine_ok, L_corner, log_ub_ok,
    log_ub_le1_ok, log_ub_le1_val, c0_ub_q, slope_q, lam_max_q, const_base_q,
    log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandC1_ok :
    ChainOk PieceLSeg.kL PieceLSeg.kR PieceLSeg.valid (31/20) (71/40) bandC1 := by
  simp only [bandC1, ChainOk]
  repeat' constructor
  all_goals norm_num [PieceLSeg.valid, LPiecesOk, LPiece.ok, LPiece.right,
    L_affine_ok, L_corner, log_ub_ok, log_ub_le1_ok, log_ub_le1_val, c0_ub_q,
    slope_q, lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandC2_ok :
    ChainOk PieceLSeg.kL PieceLSeg.kR PieceLSeg.valid (71/40) (2529/1000) bandC2 := by
  simp only [bandC2, ChainOk]
  repeat' constructor
  all_goals norm_num [PieceLSeg.valid, LPiecesOk, LPiece.ok, LPiece.right,
    L_affine_ok, L_corner, log_ub_ok, log_ub_le1_ok, log_ub_le1_val, c0_ub_q,
    slope_q, lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandC3_ok :
    ChainOk PieceLSeg.kL PieceLSeg.kR PieceLSeg.valid (2529/1000) (438/125) bandC3 := by
  simp only [bandC3, ChainOk]
  repeat' constructor
  all_goals norm_num [PieceLSeg.valid, LPiecesOk, LPiece.ok, LPiece.right,
    L_affine_ok, L_corner, log_ub_ok, log_ub_le1_ok, log_ub_le1_val, c0_ub_q,
    slope_q, lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 3200000 in
theorem bandC4_ok :
    ChainOk PieceLSeg.kL PieceLSeg.kR PieceLSeg.valid (438/125) 25 bandC4 := by
  simp only [bandC4, ChainOk]
  repeat' constructor
  all_goals norm_num [PieceLSeg.valid, LPiecesOk, LPiece.ok, LPiece.right,
    L_affine_ok, L_corner, log_ub_ok, log_ub_le1_ok, log_ub_le1_val, c0_ub_q,
    slope_q, lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

set_option maxHeartbeats 800000 in
theorem bandD_ok :
    ChainOk NoLeisureTanSeg.kL NoLeisureTanSeg.kR NoLeisureTanSeg.valid 25 50 bandD := by
  simp only [bandD, ChainOk]
  repeat' constructor
  all_goals norm_num [NoLeisureTanSeg.valid, log_ub_ok, c0_ub_q, slope_q,
    lam_max_q, const_base_q, log_ub_val, atanh2_ub, atanh2_lb, pow16, g_q,
    q_Amax, q_qmax, q_bmin, q_bmax, q_emin, q_emax, q_C0]

/-- Lema 12 certificado en el núcleo compacto $[1/25000, 50]$. -/
theorem lemma12_mid_certified (θ : Params) (K K' L : ℝ)
    (hK : 1 / 25000 ≤ K ∧ K ≤ 50) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K := by
  by_cases hA : K ≤ ((11 / 200 : ℚ) : ℝ)
  · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (1/25000) (11/200) bandA bandA_ok θ
      (by push_cast; exact hK.1) hA hK' hL hc
  · by_cases hB1 : K ≤ ((1 / 4 : ℚ) : ℝ)
    · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (11/200) (1/4) bandB1 bandB1_ok θ
        (le_of_not_ge hA) hB1 hK' hL hc
    · by_cases hB2a : K ≤ ((1509 / 2000 : ℚ) : ℝ)
      · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (1/4) (1509/2000) bandB2a bandB2a_ok θ
          (le_of_not_ge hB1) hB2a hK' hL hc
      · by_cases hB2b : K ≤ ((31 / 20 : ℚ) : ℝ)
        · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (1509/2000) (31/20) bandB2b bandB2b_ok θ
            (le_of_not_ge hB2a) hB2b hK' hL hc
        · by_cases hC1 : K ≤ ((71 / 40 : ℚ) : ℝ)
          · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (31/20) (71/40) bandC1 bandC1_ok θ
              (le_of_not_ge hB2b) hC1 hK' hL hc
          · by_cases hC2 : K ≤ ((2529 / 1000 : ℚ) : ℝ)
            · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (71/40) (2529/1000) bandC2 bandC2_ok θ
                (le_of_not_ge hC1) hC2 hK' hL hc
            · by_cases hC3 : K ≤ ((438 / 125 : ℚ) : ℝ)
              · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (2529/1000) (438/125) bandC3 bandC3_ok θ
                  (le_of_not_ge hC2) hC3 hK' hL hc
              · by_cases hC4 : K ≤ ((25 : ℚ) : ℝ)
                · exact ChainOk.sound (fun s hv θ => s.sound hv θ) (438/125) 25 bandC4 bandC4_ok θ
                    (le_of_not_ge hC3) hC4 hK' hL hc
                · exact ChainOk.sound (fun s hv θ => s.sound hv θ) 25 50 bandD bandD_ok θ
                    (le_of_not_ge hC4) (by push_cast; exact hK.2) hK' hL hc

/-- **Lema 12 global incondicional (`lemma12_global_certified`)**:
    $\Psi^\#(K) = 0.4 K - 5/\sqrt{K} - 18.5 - 10/301$ es una super-barrera global de Bellman
    en TODO $K \in (0, \infty)$ para TODO $	heta \in \mathcal{P}$, certificado 100% en el kernel. -/
theorem lemma12_global_certified (θ : Params) (K K' L : ℝ)
    (hK : 0 < K) (hK' : 0 < K') (hL : 0 ≤ L ∧ L < 1)
    (hc : 0 < θ.q * K + F θ.A K L - K') :
    u θ.η (θ.q * K + F θ.A K L - K') L + θ.β * Psi_sharp K' ≤ Psi_sharp K :=
  lemma12_global_super_barrier lemma12_mid_certified θ K K' L hK hK' hL hc

end MVS.Lemma12Cert
