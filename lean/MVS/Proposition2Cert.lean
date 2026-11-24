import MVS.Proposition2
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Certificación Numérica de la Proposición 2 (Tabla 2: Regiones M y H₁)

Certificación completamente libre de `sorry` de la positividad puntual
`0 < Δ_X(K)` sobre `M = [0.10, 0.28]` (12 subintervalos) y `H₁ = [0.28, 0.80]`
(13 subintervalos), usando `decide` sobre `ℚ` para los subintervalos y
`MVS.Lemma11` para la evaluación logarítmica en los bordes izquierdos.
-/

open Real Set MVS.Theorem1 MVS.Proposition2 MVS.Lemma11

namespace MVS.Proposition2Cert

/-! ## 1. Versiones racionales decidibles de constantes y funciones -/

def A_min_q : ℚ := 749 / 1000
def A_max_q : ℚ := 751 / 1000
def q_min_q : ℚ := 9199 / 10000
def q_max_q : ℚ := 9201 / 10000
def beta_min_q : ℚ := 9699 / 10000
def beta_max_q : ℚ := 9701 / 10000
def eta_min_q : ℚ := 6999 / 10000
def eta_max_q : ℚ := 7001 / 10000

def g_q (l K : ℚ) : ℚ := 2 * K * l / (K + l)

def atanhSeriesQ (N : ℕ) (u : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range N, u ^ (2 * j + 1) / (2 * j + 1 : ℚ)

def atanhRemUBQ (N : ℕ) (u : ℚ) : ℚ :=
  2 * u ^ (2 * N + 1) / ((2 * N + 1 : ℚ) * (1 - u ^ 2))

lemma atanhSeriesQ_cast (N : ℕ) (u : ℚ) :
    (atanhSeriesQ N u : ℝ) = atanhSeries N (u : ℝ) := by
  unfold atanhSeriesQ atanhSeries
  push_cast
  rfl

lemma atanhRemUBQ_cast (N : ℕ) (u : ℚ) :
    (atanhRemUBQ N u : ℝ) = atanhRemUB N (u : ℝ) := by
  unfold atanhRemUBQ atanhRemUB
  push_cast
  rfl

/-! ## 2. Monotonicidad básica en K sobre intervalos positivos -/

section RealHelpers
noncomputable section

lemma g_mono_K {l K₁ K₂ : ℝ} (hl : 0 ≤ l) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    g l K₁ ≤ g l K₂ := by
  unfold g
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hdiff : 0 ≤ 2 * l ^ 2 * (K₂ - K₁) := mul_nonneg (by positivity) (by linarith)
  linarith

lemma sq_g_mono_K {l K₁ K₂ : ℝ} (hl : 0 ≤ l) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    Real.sqrt (g l K₁) ≤ Real.sqrt (g l K₂) :=
  Real.sqrt_le_sqrt (g_mono_K hl hK₁ hK)

lemma ratio_sq_mono_K {l K₁ K₂ : ℝ} (hl : 0 ≤ l) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    K₁ ^ 2 / (K₁ + l) ^ 2 ≤ K₂ ^ 2 / (K₂ + l) ^ 2 := by
  have hK₂ : 0 < K₂ := by linarith
  have h1 : 0 < K₁ + l := by linarith
  have h2 : 0 < K₂ + l := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul : K₁ * (K₂ + l) ≤ K₂ * (K₁ + l) := by nlinarith
  have hnn1 : 0 ≤ K₁ * (K₂ + l) := by positivity
  have hnn2 : 0 ≤ K₂ * (K₁ + l) := by positivity
  nlinarith

lemma t_val_mono_K {l₀ K₁ K₂ : ℝ} (hl₀ : 0 ≤ l₀) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    t_val l₀ K₁ ≤ t_val l₀ K₂ := by
  unfold t_val t_gen
  have hA : 0 ≤ 3 * A_max := by unfold A_max; norm_num
  have h1 : K₁ ^ 2 / (K₁ + l₀) ^ 2 ≤ K₂ ^ 2 / (K₂ + l₀) ^ 2 := ratio_sq_mono_K hl₀ hK₁ hK
  have h2 : Real.sqrt (g l₀ K₁) ≤ Real.sqrt (g l₀ K₂) := sq_g_mono_K hl₀ hK₁ hK
  have hmul : (K₁ ^ 2 / (K₁ + l₀) ^ 2) * Real.sqrt (g l₀ K₁) ≤
      (K₂ ^ 2 / (K₂ + l₀) ^ 2) * Real.sqrt (g l₀ K₂) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  have hmulA := mul_le_mul_of_nonneg_left hmul hA
  have hr1 : 3 * A_max * (K₁ ^ 2 / (K₁ + l₀) ^ 2 * Real.sqrt (g l₀ K₁)) =
      3 * A_max * K₁ ^ 2 * Real.sqrt (g l₀ K₁) / (K₁ + l₀) ^ 2 := by ring
  have hr2 : 3 * A_max * (K₂ ^ 2 / (K₂ + l₀) ^ 2 * Real.sqrt (g l₀ K₂)) =
      3 * A_max * K₂ ^ 2 * Real.sqrt (g l₀ K₂) / (K₂ + l₀) ^ 2 := by ring
  linarith

lemma S_val_mono_K {l₀ K₁ K₂ : ℝ} (hl₀ : 0 ≤ l₀) (hl₀1 : l₀ ≤ 1)
    (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    S_val l₀ K₁ ≤ S_val l₀ K₂ := by
  unfold S_val
  have hq : q_max * K₁ ≤ q_max * K₂ := by unfold q_max; nlinarith
  have hF : F A_max K₁ l₀ ≤ F A_max K₂ l₀ :=
    F_mono_K (by unfold A_max; norm_num) hK₁ hK hl₀
  have ht : (1 - l₀) * t_val l₀ K₁ ≤ (1 - l₀) * t_val l₀ K₂ :=
    mul_le_mul_of_nonneg_left (t_val_mono_K hl₀ hK₁ hK) (by linarith)
  linarith

lemma cX_mono_K {lX sX K₁ K₂ : ℝ} (hlX : 0 ≤ lX) (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    cX lX sX K₁ ≤ cX lX sX K₂ := by
  unfold cX
  have hq : q_min * K₁ ≤ q_min * K₂ := by unfold q_min; nlinarith
  have hF : F A_min K₁ lX ≤ F A_min K₂ lX :=
    F_mono_K (by unfold A_min; norm_num) hK₁ hK hlX
  linarith

lemma sqrt_bounds_of_sq {q rL rU : ℝ} (hrL : 0 ≤ rL) (hrU : 0 ≤ rU)
    (hL : rL ^ 2 ≤ q) (hU : q ≤ rU ^ 2) :
    rL ≤ Real.sqrt q ∧ Real.sqrt q ≤ rU := by
  constructor
  · rw [← Real.sqrt_sq hrL]; exact Real.sqrt_le_sqrt hL
  · rw [← Real.sqrt_sq hrU]; exact Real.sqrt_le_sqrt hU

end
end RealHelpers

/-! ## 3. Certificado racional por subintervalo (`CertSeg`) -/

structure CertSeg where
  kL : ℚ
  kR : ℚ
  sg0_L : ℚ
  sg0_U : ℚ
  sgX_L : ℚ
  sgX_U : ℚ
  sg0_mL : ℚ
  sg0_mU : ℚ
  sgX_mL : ℚ
  sgX_mU : ℚ
  deriving DecidableEq

def CertSeg.valid (seg : CertSeg) (a l₀ lX sX : ℚ) : Bool :=
  let kL := seg.kL
  let kR := seg.kR
  let mid := (kL + kR) / 2
  (0 < kL) && (kL < kR) &&
  (0 ≤ seg.sg0_L) && (seg.sg0_L ^ 2 ≤ g_q l₀ kL) && (g_q l₀ kR ≤ seg.sg0_U ^ 2) &&
  (0 ≤ seg.sgX_L) && (seg.sgX_L ^ 2 ≤ g_q lX kL) && (g_q lX kR ≤ seg.sgX_U ^ 2) &&
  (0 ≤ seg.sg0_mL) && (seg.sg0_mL ^ 2 ≤ g_q l₀ mid) && (g_q l₀ mid ≤ seg.sg0_mU ^ 2) &&
  (0 ≤ seg.sgX_mL) && (seg.sgX_mL ^ 2 ≤ g_q lX mid) && (g_q lX mid ≤ seg.sgX_mU ^ 2) &&
  let cX_L := q_min_q * kL + A_min_q * g_q lX kL * seg.sgX_L - sX
  let cX_R_hi := q_min_q * kR + A_min_q * g_q lX kR * seg.sgX_U - sX
  let t_L := 3 * A_max_q * kL ^ 2 * seg.sg0_L / (kL + l₀) ^ 2
  let t_U := 3 * A_max_q * kR ^ 2 * seg.sg0_U / (kR + l₀) ^ 2
  let S_L := q_max_q * kL + A_max_q * g_q l₀ kL * seg.sg0_L + (1 - l₀) * t_L
  let S_U := q_max_q * kR + A_max_q * g_q l₀ kR * seg.sg0_U + (1 - l₀) * t_U
  let S_R_lo := q_max_q * kR + A_max_q * g_q l₀ kR * seg.sg0_L +
    (1 - l₀) * (3 * A_max_q * kR ^ 2 * seg.sg0_L / (kR + l₀) ^ 2)
  let t_m_hi := 3 * A_max_q * mid ^ 2 * seg.sg0_mU / (mid + l₀) ^ 2
  let t_m_lo := 3 * A_max_q * mid ^ 2 * seg.sg0_mL / (mid + l₀) ^ 2
  let S_m_lo := q_max_q * mid + A_max_q * g_q l₀ mid * seg.sg0_mL + (1 - l₀) * t_m_lo
  let Sd_m_hi := q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_mU / (mid + l₀) ^ 2 +
    (1 - l₀) * t_m_hi * (5 * l₀ / (2 * mid * (mid + l₀)))
  let cX_m_hi := q_min_q * mid + A_min_q * g_q lX mid * seg.sgX_mU - sX
  let cXd_m_lo := q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_mL / (mid + lX) ^ 2
  let Q_mid_ub := Sd_m_hi * cX_m_hi - cXd_m_lo * (S_m_lo - a)
  let fkk0_ub := 3 * A_max_q * l₀ ^ 3 * max |l₀ - 4 * kL| |l₀ - 4 * kR| /
    (seg.sg0_L * (kL + l₀) ^ 4)
  let fkkX_ub := 3 * A_min_q * lX ^ 3 * max |lX - 4 * kL| |lX - 4 * kR| /
    (seg.sgX_L * (kL + lX) ^ 4)
  let td2_ub := t_U * (5 * l₀ * max |3 * l₀ - 4 * kL| |3 * l₀ - 4 * kR| /
    (4 * kL ^ 2 * (kL + l₀) ^ 2))
  let M_Q := (fkk0_ub + (1 - l₀) * td2_ub) * cX_R_hi + fkkX_ub * (S_U - a)
  let cXd_lb := q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_L / (kR + lX) ^ 2
  let RX_lb := (S_R_lo - a) / cX_R_hi
  let Sd_ub := q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_U / (kL + l₀) ^ 2 +
    (1 - l₀) * t_U * (5 * l₀ / (2 * kL * (kL + l₀)))
  let num_lb := eta_min_q * cXd_lb * RX_lb - Sd_ub
  let den := if num_lb < 0 then S_L - a else S_U - a
  let d_lb := num_lb / den + (1 - eta_max_q) * (5 * l₀ / (2 * kR * (kR + l₀)))
  let om_ub := (1 - eta_min_q) * (S_U - a) / t_L
  (0 < seg.sg0_L) && (0 < seg.sgX_L) &&
  (0 ≤ seg.sg0_U) && (0 ≤ seg.sgX_U) && (0 ≤ seg.sg0_mU) && (0 ≤ seg.sgX_mU) &&
  (0 < cX_L) && (0 < S_L - a) && (om_ub < 1) &&
  (Q_mid_ub + M_Q * ((kR - kL) / 2) ≤ 0) && (0 ≤ d_lb)

set_option maxHeartbeats 800000 in
theorem CertSeg.valid_sound (seg : CertSeg) {a l₀ lX sX : ℚ}
    (hl₀ : 0 < l₀) (hl₀1 : l₀ ≤ 1) (hlX : 0 < lX) (TX Ψ_a : ℝ)
    (hv : seg.valid a l₀ lX sX = true) :
    ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ),
      delta_X (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) TX Ψ_a (seg.kL : ℝ) ≤
      delta_X (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) TX Ψ_a K := by
  -- Desempaquetar todas las condiciones booleanas de `seg.valid`
  unfold CertSeg.valid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  have hkL_pos : 0 < seg.kL := hv.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hkLR : seg.kL < seg.kR := hv.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hsg0L_nn : 0 ≤ seg.sg0_L := hv.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hsg0L_sq : seg.sg0_L ^ 2 ≤ g_q l₀ seg.kL := hv.1.1.1.1.1.1.1.1.1.1.1.2
  have hsg0U_sq : g_q l₀ seg.kR ≤ seg.sg0_U ^ 2 := hv.1.1.1.1.1.1.1.1.1.1.2
  have hsgXL_nn : 0 ≤ seg.sgX_L := hv.1.1.1.1.1.1.1.1.1.2
  have hsgXL_sq : seg.sgX_L ^ 2 ≤ g_q lX seg.kL := hv.1.1.1.1.1.1.1.1.2
  have hsgXU_sq : g_q lX seg.kR ≤ seg.sgX_U ^ 2 := hv.1.1.1.1.1.1.1.2
  have hsg0mL_nn : 0 ≤ seg.sg0_mL := hv.1.1.1.1.1.1.2
  have hsg0mL_sq : seg.sg0_mL ^ 2 ≤ g_q l₀ ((seg.kL + seg.kR) / 2) := hv.1.1.1.1.1.2
  have hsg0mU_sq : g_q l₀ ((seg.kL + seg.kR) / 2) ≤ seg.sg0_mU ^ 2 := hv.1.1.1.1.2
  have hsgXmL_nn : 0 ≤ seg.sgX_mL := hv.1.1.1.2
  have hsgXmL_sq : seg.sgX_mL ^ 2 ≤ g_q lX ((seg.kL + seg.kR) / 2) := hv.1.1.2
  have hsgXmU_sq : g_q lX ((seg.kL + seg.kR) / 2) ≤ seg.sgX_mU ^ 2 := hv.1.2
  have hsg0L_pos : 0 < seg.sg0_L := hv.2.1.1.1.1.1.1.1.1.1.1
  have hsgXL_pos : 0 < seg.sgX_L := hv.2.1.1.1.1.1.1.1.1.1.2
  have hsg0U_nn_q : 0 ≤ seg.sg0_U := hv.2.1.1.1.1.1.1.1.1.2
  have hsgXU_nn_q : 0 ≤ seg.sgX_U := hv.2.1.1.1.1.1.1.1.2
  have hsg0mU_nn_q : 0 ≤ seg.sg0_mU := hv.2.1.1.1.1.1.1.2
  have hsgXmU_nn_q : 0 ≤ seg.sgX_mU := hv.2.1.1.1.1.1.2
  have hcXL_pos := hv.2.1.1.1.1.2
  have hSLa_pos := hv.2.1.1.1.2
  have hom_lt := hv.2.1.1.2
  have hQ_neg := hv.2.1.2
  have hd_nn := hv.2.2
  have hl₀R : (0 : ℝ) < (l₀ : ℝ) := by exact_mod_cast hl₀
  have hl₀1R : (l₀ : ℝ) ≤ 1 := by exact_mod_cast hl₀1
  have hlXR : (0 : ℝ) < (lX : ℝ) := by exact_mod_cast hlX
  have hkL_R : (0 : ℝ) < (seg.kL : ℝ) := by exact_mod_cast hkL_pos
  have hkLR_R : (seg.kL : ℝ) < (seg.kR : ℝ) := by exact_mod_cast hkLR
  have hkR_R_pos : (0 : ℝ) < (seg.kR : ℝ) := lt_trans hkL_R hkLR_R
  have hsg0U_nn : (0 : ℝ) ≤ (seg.sg0_U : ℝ) := by exact_mod_cast hsg0U_nn_q
  have hsgXU_nn : (0 : ℝ) ≤ (seg.sgX_U : ℝ) := by exact_mod_cast hsgXU_nn_q
  have hsg0mU_nn : (0 : ℝ) ≤ (seg.sg0_mU : ℝ) := by exact_mod_cast hsg0mU_nn_q
  have hsgXmU_nn : (0 : ℝ) ≤ (seg.sgX_mU : ℝ) := by exact_mod_cast hsgXmU_nn_q
  -- Cotas de √(g l₀ K) y √(g lX K) en todo el subintervalo [kL, kR]
  have hg0_L_lb : (seg.sg0_L : ℝ) ≤ Real.sqrt (g (l₀ : ℝ) (seg.kL : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (seg.sg0_L : ℝ) := by exact_mod_cast hsg0L_nn
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    have : (seg.sg0_L ^ 2 : ℝ) ≤ (g_q l₀ seg.kL : ℝ) := by exact_mod_cast hsg0L_sq
    simpa [g_q, g] using this
  have hg0_R_ub : Real.sqrt (g (l₀ : ℝ) (seg.kR : ℝ)) ≤ (seg.sg0_U : ℝ) := by
    rw [← Real.sqrt_sq hsg0U_nn]
    apply Real.sqrt_le_sqrt
    have : (g_q l₀ seg.kR : ℝ) ≤ (seg.sg0_U ^ 2 : ℝ) := by exact_mod_cast hsg0U_sq
    simpa [g_q, g] using this
  have hgX_L_lb : (seg.sgX_L : ℝ) ≤ Real.sqrt (g (lX : ℝ) (seg.kL : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (seg.sgX_L : ℝ) := by exact_mod_cast hsgXL_nn
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    have : (seg.sgX_L ^ 2 : ℝ) ≤ (g_q lX seg.kL : ℝ) := by exact_mod_cast hsgXL_sq
    simpa [g_q, g] using this
  have hgX_R_ub : Real.sqrt (g (lX : ℝ) (seg.kR : ℝ)) ≤ (seg.sgX_U : ℝ) := by
    rw [← Real.sqrt_sq hsgXU_nn]
    apply Real.sqrt_le_sqrt
    have : (g_q lX seg.kR : ℝ) ≤ (seg.sgX_U ^ 2 : ℝ) := by exact_mod_cast hsgXU_sq
    simpa [g_q, g] using this
  -- Cotas en el punto medio mid = (kL + kR) / 2
  set mid_q : ℚ := (seg.kL + seg.kR) / 2
  have hmid_eq : (mid_q : ℝ) = ((seg.kL : ℝ) + (seg.kR : ℝ)) / 2 := by
    dsimp [mid_q]; push_cast; ring
  have hg0_m : (seg.sg0_mL : ℝ) ≤ Real.sqrt (g (l₀ : ℝ) (mid_q : ℝ)) ∧
      Real.sqrt (g (l₀ : ℝ) (mid_q : ℝ)) ≤ (seg.sg0_mU : ℝ) := by
    apply sqrt_bounds_of_sq (by exact_mod_cast hsg0mL_nn) hsg0mU_nn
    · have : (seg.sg0_mL ^ 2 : ℝ) ≤ (g_q l₀ mid_q : ℝ) := by exact_mod_cast hsg0mL_sq
      simpa [g_q, g] using this
    · have : (g_q l₀ mid_q : ℝ) ≤ (seg.sg0_mU ^ 2 : ℝ) := by exact_mod_cast hsg0mU_sq
      simpa [g_q, g] using this
  have hgX_m : (seg.sgX_mL : ℝ) ≤ Real.sqrt (g (lX : ℝ) (mid_q : ℝ)) ∧
      Real.sqrt (g (lX : ℝ) (mid_q : ℝ)) ≤ (seg.sgX_mU : ℝ) := by
    apply sqrt_bounds_of_sq (by exact_mod_cast hsgXmL_nn) hsgXmU_nn
    · have : (seg.sgX_mL ^ 2 : ℝ) ≤ (g_q lX mid_q : ℝ) := by exact_mod_cast hsgXmL_sq
      simpa [g_q, g] using this
    · have : (g_q lX mid_q : ℝ) ≤ (seg.sgX_mU ^ 2 : ℝ) := by exact_mod_cast hsgXmU_sq
      simpa [g_q, g] using this
  -- Cotas puntuales de cX, S_val, t_val en los extremos kL, kR
  have hcX_L_lb : ((q_min_q * seg.kL + A_min_q * g_q lX seg.kL * seg.sgX_L - sX : ℚ) : ℝ) ≤
      cX (lX : ℝ) (sX : ℝ) (seg.kL : ℝ) := by
    unfold cX F q_min A_min q_min_q A_min_q g_q
    push_cast
    have hgX_nn : 0 ≤ 2 * (seg.kL : ℝ) * (lX : ℝ) / ((seg.kL : ℝ) + (lX : ℝ)) := by positivity
    have hA_nn : (0 : ℝ) ≤ 749 / 1000 := by norm_num
    have hmul : (749 / 1000 : ℝ) * (2 * (seg.kL : ℝ) * (lX : ℝ) / ((seg.kL : ℝ) + (lX : ℝ))) *
        (seg.sgX_L : ℝ) ≤
        (749 / 1000 : ℝ) * (2 * (seg.kL : ℝ) * (lX : ℝ) / ((seg.kL : ℝ) + (lX : ℝ))) *
        Real.sqrt (2 * (seg.kL : ℝ) * (lX : ℝ) / ((seg.kL : ℝ) + (lX : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA_nn hgX_nn)
      simpa [g] using hgX_L_lb
    linarith
  have hcX_R_ub : cX (lX : ℝ) (sX : ℝ) (seg.kR : ℝ) ≤
      ((q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX : ℚ) : ℝ) := by
    unfold cX F q_min A_min q_min_q A_min_q g_q
    push_cast
    have hgX_nn : 0 ≤ 2 * (seg.kR : ℝ) * (lX : ℝ) / ((seg.kR : ℝ) + (lX : ℝ)) := by positivity
    have hA_nn : (0 : ℝ) ≤ 749 / 1000 := by norm_num
    have hmul : (749 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (lX : ℝ) / ((seg.kR : ℝ) + (lX : ℝ))) *
        Real.sqrt (2 * (seg.kR : ℝ) * (lX : ℝ) / ((seg.kR : ℝ) + (lX : ℝ))) ≤
        (749 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (lX : ℝ) / ((seg.kR : ℝ) + (lX : ℝ))) *
        (seg.sgX_U : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA_nn hgX_nn)
      simpa [g] using hgX_R_ub
    linarith
  have ht_L_lb : ((3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2 : ℚ) : ℝ) ≤
      t_val (l₀ : ℝ) (seg.kL : ℝ) := by
    unfold t_val t_gen A_max A_max_q
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hg0_L_lb (by positivity)
  have ht_R_ub : t_val (l₀ : ℝ) (seg.kR : ℝ) ≤
      ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2 : ℚ) : ℝ) := by
    unfold t_val t_gen A_max A_max_q
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hg0_R_ub (by positivity)
  have ht_R_lb : ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2 : ℚ) : ℝ) ≤
      t_val (l₀ : ℝ) (seg.kR : ℝ) := by
    unfold t_val t_gen A_max A_max_q
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsg : (seg.sg0_L : ℝ) ≤ Real.sqrt (g (l₀ : ℝ) (seg.kR : ℝ)) :=
      le_trans hg0_L_lb (sq_g_mono_K (le_of_lt hl₀R) hkL_R (le_of_lt hkLR_R))
    exact mul_le_mul_of_nonneg_left hsg (by positivity)
  have hS_L_lb : ((q_max_q * seg.kL + A_max_q * g_q l₀ seg.kL * seg.sg0_L +
      (1 - l₀) * (3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2) : ℚ) : ℝ) ≤
      S_val (l₀ : ℝ) (seg.kL : ℝ) := by
    unfold S_val F q_max A_max q_max_q A_max_q g_q
    push_cast
    have hg0_nn : 0 ≤ 2 * (seg.kL : ℝ) * (l₀ : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ)) := by positivity
    have hF : (751 / 1000 : ℝ) * (2 * (seg.kL : ℝ) * (l₀ : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ))) *
        (seg.sg0_L : ℝ) ≤
        (751 / 1000 : ℝ) * (2 * (seg.kL : ℝ) * (l₀ : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ))) *
        Real.sqrt (2 * (seg.kL : ℝ) * (l₀ : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hg0_nn)
      simpa [g] using hg0_L_lb
    have ht := mul_le_mul_of_nonneg_left ht_L_lb (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
    unfold A_max A_max_q at ht
    push_cast at ht
    linarith
  have hS_R_ub : S_val (l₀ : ℝ) (seg.kR : ℝ) ≤
      ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
      (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) : ℚ) : ℝ) := by
    unfold S_val F q_max A_max q_max_q A_max_q g_q
    push_cast
    have hg0_nn : 0 ≤ 2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ)) := by positivity
    have hF : (751 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) *
        Real.sqrt (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) ≤
        (751 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) *
        (seg.sg0_U : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hg0_nn)
      simpa [g] using hg0_R_ub
    have ht := mul_le_mul_of_nonneg_left ht_R_ub (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
    unfold A_max A_max_q at ht
    push_cast at ht
    linarith
  have hS_R_lb : ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
      (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) : ℚ) : ℝ) ≤
      S_val (l₀ : ℝ) (seg.kR : ℝ) := by
    unfold S_val F q_max A_max q_max_q A_max_q g_q
    push_cast
    have hg0_nn : 0 ≤ 2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ)) := by positivity
    have hsg : (seg.sg0_L : ℝ) ≤
        Real.sqrt (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) := by
      simpa [g] using le_trans hg0_L_lb (sq_g_mono_K (le_of_lt hl₀R) hkL_R (le_of_lt hkLR_R))
    have hF : (751 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) *
        (seg.sg0_L : ℝ) ≤
        (751 / 1000 : ℝ) * (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) *
        Real.sqrt (2 * (seg.kR : ℝ) * (l₀ : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ))) :=
      mul_le_mul_of_nonneg_left hsg (mul_nonneg (by norm_num) hg0_nn)
    have ht := mul_le_mul_of_nonneg_left ht_R_lb (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
    unfold A_max A_max_q at ht
    push_cast at ht
    linarith
  -- 1. Positividad de cX y (S_val - a) en todo [kL, kR]
  have hcX_pos : ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ), 0 < cX (lX : ℝ) (sX : ℝ) K := by
    intro K hK
    have h1 : (0 : ℝ) < ((q_min_q * seg.kL + A_min_q * g_q lX seg.kL * seg.sgX_L - sX : ℚ) : ℝ) := by
      exact_mod_cast hcXL_pos
    have h2 := cX_mono_K (sX := (sX : ℝ)) (le_of_lt hlXR) hkL_R hK.1
    linarith
  have hcsup_pos : ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ), 0 < S_val (l₀ : ℝ) K - (a : ℝ) := by
    intro K hK
    have h1 : (0 : ℝ) < ((q_max_q * seg.kL + A_max_q * g_q l₀ seg.kL * seg.sg0_L +
        (1 - l₀) * (3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2) - a : ℚ) : ℝ) := by
      exact_mod_cast hSLa_pos
    rw [Rat.cast_sub] at h1
    have h2 := S_val_mono_K (le_of_lt hl₀R) hl₀1R hkL_R hK.1
    linarith
  -- 2. Condición interior ω* < 1 en todo [kL, kR]
  have hint : ∀ η ∈ ({eta_min, eta_max} : Set ℝ), ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ),
      (1 - η) * (S_val (l₀ : ℝ) K - (a : ℝ)) / t_val (l₀ : ℝ) K < 1 := by
    intro η hη K hK
    have h1mη_le : 1 - η ≤ 1 - eta_min := by
      rcases hη with rfl | rfl
      · exact le_rfl
      · unfold eta_min eta_max; norm_num
    have h1mη_nn : 0 ≤ 1 - η := by
      rcases hη with rfl | rfl <;> norm_num [eta_min, eta_max]
    have hS_le : S_val (l₀ : ℝ) K - (a : ℝ) ≤ S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ) := by
      linarith [S_val_mono_K (le_of_lt hl₀R) hl₀1R (lt_of_lt_of_le hkL_R hK.1) hK.2]
    have ht_ge : t_val (l₀ : ℝ) (seg.kL : ℝ) ≤ t_val (l₀ : ℝ) K :=
      t_val_mono_K (le_of_lt hl₀R) hkL_R hK.1
    have ht_L_pos : (0 : ℝ) < ((3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2 : ℚ) : ℝ) := by
      have hsg : (0 : ℝ) < (seg.sg0_L : ℝ) := by exact_mod_cast hsg0L_pos
      unfold A_max_q; push_cast; positivity
    have ht_pos : 0 < t_val (l₀ : ℝ) K := lt_of_lt_of_le (lt_of_lt_of_le ht_L_pos ht_L_lb) ht_ge
    have hnum_le : (1 - η) * (S_val (l₀ : ℝ) K - (a : ℝ)) ≤
        ((1 - eta_min_q) * (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) := by
      have hS_nn : 0 ≤ S_val (l₀ : ℝ) K - (a : ℝ) := le_of_lt (hcsup_pos K hK)
      have h1 : (1 - η) * (S_val (l₀ : ℝ) K - (a : ℝ)) ≤ (1 - eta_min) * (S_val (l₀ : ℝ) K - (a : ℝ)) :=
        mul_le_mul_of_nonneg_right h1mη_le hS_nn
      have h2 : (1 - eta_min) * (S_val (l₀ : ℝ) K - (a : ℝ)) ≤
          (1 - eta_min) * (S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hS_le (by unfold eta_min; norm_num)
      have h3 : S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ) ≤
          ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
          (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) := by
        push_cast at hS_R_ub ⊢; linarith
      have h4 : (1 - eta_min) * (S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ)) ≤
          ((1 - eta_min_q) * (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
          (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) := by
        unfold eta_min eta_min_q; push_cast at h3 ⊢
        exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    have hdiv_le : (1 - η) * (S_val (l₀ : ℝ) K - (a : ℝ)) / t_val (l₀ : ℝ) K ≤
        (((1 - eta_min_q) * (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a) /
        (3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2) : ℚ) : ℝ) := by
      push_cast at hnum_le ht_L_pos ht_L_lb ⊢
      exact div_le_div₀
        (le_trans (mul_nonneg h1mη_nn (le_of_lt (hcsup_pos K hK))) hnum_le)
        hnum_le ht_L_pos (le_trans ht_L_lb ht_ge)
    have hom_R : (((1 - eta_min_q) * (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a) /
        (3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2) : ℚ) : ℝ) < 1 := by
      exact_mod_cast hom_lt
    linarith
  -- 3. Forma centrada 1D para QX ≤ 0 en [kL, kR]
  have hQ_nonpos : ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ),
      QX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K ≤ 0 := by
    let M_Q_q : ℚ :=
      (3 * A_max_q * l₀ ^ 3 * max |l₀ - 4 * seg.kL| |l₀ - 4 * seg.kR| /
        (seg.sg0_L * (seg.kL + l₀) ^ 4) +
      (1 - l₀) * ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) *
        (5 * l₀ * max |3 * l₀ - 4 * seg.kL| |3 * l₀ - 4 * seg.kR| /
        (4 * seg.kL ^ 2 * (seg.kL + l₀) ^ 2)))) *
      (q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX) +
      (3 * A_min_q * lX ^ 3 * max |lX - 4 * seg.kL| |lX - 4 * seg.kR| /
        (seg.sgX_L * (seg.kL + lX) ^ 4)) *
      (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a)
    refine centered_form_neg (f' := QX_deriv (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ))
      (M := (M_Q_q : ℝ)) (ε := 0) (le_of_lt hkLR_R) ?_ ?_ ?_
    · intro K hK
      exact hasDerivAt_QX hl₀R hlXR (lt_of_lt_of_le hkL_R hK.1)
    · intro K hK
      have hK_pos : 0 < K := lt_of_lt_of_le hkL_R hK.1
      have hsg0_K : (seg.sg0_L : ℝ) ≤ Real.sqrt (g (l₀ : ℝ) K) :=
        le_trans hg0_L_lb (sq_g_mono_K (le_of_lt hl₀R) hkL_R hK.1)
      have hsgX_K : (seg.sgX_L : ℝ) ≤ Real.sqrt (g (lX : ℝ) K) :=
        le_trans hgX_L_lb (sq_g_mono_K (le_of_lt hlXR) hkL_R hK.1)
      have hsg0L_R : (0 : ℝ) < (seg.sg0_L : ℝ) := by exact_mod_cast hsg0L_pos
      have hsgXL_R : (0 : ℝ) < (seg.sgX_L : ℝ) := by exact_mod_cast hsgXL_pos
      -- |FKK A_max l₀ K| ≤ fkk0_ub
      have hfkk0 : |FKK A_max (l₀ : ℝ) K| ≤
          ((3 * A_max_q * l₀ ^ 3 * max |l₀ - 4 * seg.kL| |l₀ - 4 * seg.kR| /
            (seg.sg0_L * (seg.kL + l₀) ^ 4) : ℚ) : ℝ) := by
        unfold FKK A_max A_max_q
        rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by unfold g; positivity)) (by positivity))]
        have hnum_le : |3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 3 * ((l₀ : ℝ) - 4 * K)| ≤
            3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 3 *
              max |(l₀ : ℝ) - 4 * (seg.kL : ℝ)| |(l₀ : ℝ) - 4 * (seg.kR : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_le]; constructor
          · have : -(max |(l₀ : ℝ) - 4 * (seg.kL : ℝ)| |(l₀ : ℝ) - 4 * (seg.kR : ℝ)|) ≤
                -|((l₀ : ℝ) - 4 * (seg.kR : ℝ))| := neg_le_neg (le_max_right _ _)
            linarith [neg_abs_le ((l₀ : ℝ) - 4 * (seg.kR : ℝ)), hK.2]
          · have : |((l₀ : ℝ) - 4 * (seg.kL : ℝ))| ≤
                max |(l₀ : ℝ) - 4 * (seg.kL : ℝ)| |(l₀ : ℝ) - 4 * (seg.kR : ℝ)| := le_max_left _ _
            linarith [le_abs_self ((l₀ : ℝ) - 4 * (seg.kL : ℝ)), hK.1]
        have hden_ge : (seg.sg0_L : ℝ) * ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 4 ≤
            Real.sqrt (g (l₀ : ℝ) K) * (K + (l₀ : ℝ)) ^ 4 := by
          apply mul_le_mul hsg0_K (pow_le_pow_left₀ (by positivity) (by linarith [hK.1]) 4)
            (by positivity) (Real.sqrt_nonneg _)
        push_cast
        exact div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
      -- |FKK A_min lX K| ≤ fkkX_ub
      have hfkkX : |FKK A_min (lX : ℝ) K| ≤
          ((3 * A_min_q * lX ^ 3 * max |lX - 4 * seg.kL| |lX - 4 * seg.kR| /
            (seg.sgX_L * (seg.kL + lX) ^ 4) : ℚ) : ℝ) := by
        unfold FKK A_min A_min_q
        rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by unfold g; positivity)) (by positivity))]
        have hnum_le : |3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 3 * ((lX : ℝ) - 4 * K)| ≤
            3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 3 *
              max |(lX : ℝ) - 4 * (seg.kL : ℝ)| |(lX : ℝ) - 4 * (seg.kR : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_le]; constructor
          · have : -(max |(lX : ℝ) - 4 * (seg.kL : ℝ)| |(lX : ℝ) - 4 * (seg.kR : ℝ)|) ≤
                -|((lX : ℝ) - 4 * (seg.kR : ℝ))| := neg_le_neg (le_max_right _ _)
            linarith [neg_abs_le ((lX : ℝ) - 4 * (seg.kR : ℝ)), hK.2]
          · have : |((lX : ℝ) - 4 * (seg.kL : ℝ))| ≤
                max |(lX : ℝ) - 4 * (seg.kL : ℝ)| |(lX : ℝ) - 4 * (seg.kR : ℝ)| := le_max_left _ _
            linarith [le_abs_self ((lX : ℝ) - 4 * (seg.kL : ℝ)), hK.1]
        have hden_ge : (seg.sgX_L : ℝ) * ((seg.kL : ℝ) + (lX : ℝ)) ^ 4 ≤
            Real.sqrt (g (lX : ℝ) K) * (K + (lX : ℝ)) ^ 4 := by
          apply mul_le_mul hsgX_K (pow_le_pow_left₀ (by positivity) (by linarith [hK.1]) 4)
            (by positivity) (Real.sqrt_nonneg _)
        push_cast
        exact div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
      -- |t_deriv2 l₀ K| ≤ td2_ub
      have htd2 : |t_deriv2 (l₀ : ℝ) K| ≤
          (((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) *
            (5 * l₀ * max |3 * l₀ - 4 * seg.kL| |3 * l₀ - 4 * seg.kR| /
            (4 * seg.kL ^ 2 * (seg.kL + l₀) ^ 2)) : ℚ) : ℝ) := by
        unfold t_deriv2
        have ht_nn : 0 ≤ t_val (l₀ : ℝ) K := by
          unfold t_val t_gen A_max; positivity
        have ht_ub : t_val (l₀ : ℝ) K ≤
            ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2 : ℚ) : ℝ) :=
          le_trans (t_val_mono_K (le_of_lt hl₀R) hK_pos hK.2) ht_R_ub
        have hfac_ub : |5 * (l₀ : ℝ) * (3 * (l₀ : ℝ) - 4 * K) / (4 * K ^ 2 * (K + (l₀ : ℝ)) ^ 2)| ≤
            ((5 * l₀ * max |3 * l₀ - 4 * seg.kL| |3 * l₀ - 4 * seg.kR| /
              (4 * seg.kL ^ 2 * (seg.kL + l₀) ^ 2) : ℚ) : ℝ) := by
          have hden_pos : 0 < 4 * K ^ 2 * (K + (l₀ : ℝ)) ^ 2 := by positivity
          rw [abs_div, abs_of_pos hden_pos]
          have hnum_le : |5 * (l₀ : ℝ) * (3 * (l₀ : ℝ) - 4 * K)| ≤
              5 * (l₀ : ℝ) * max |3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)| |3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [abs_le]; constructor
            · have : -(max |3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)| |3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)|) ≤
                  -|3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)| := neg_le_neg (le_max_right _ _)
              linarith [neg_abs_le (3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)), hK.2]
            · have : |3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)| ≤
                  max |3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)| |3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)| := le_max_left _ _
              linarith [le_abs_self (3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)), hK.1]
          have hden_ge : 4 * (seg.kL : ℝ) ^ 2 * ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2 ≤
              4 * K ^ 2 * (K + (l₀ : ℝ)) ^ 2 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hkL_R) hK.1 2) (by norm_num))
              (pow_le_pow_left₀ (by positivity) (by linarith [hK.1]) 2) (by positivity) (by positivity)
          push_cast
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
        rw [abs_mul, abs_of_nonneg ht_nn]
        push_cast at ht_ub hfac_ub ⊢
        exact mul_le_mul ht_ub hfac_ub (abs_nonneg _) (by unfold A_max_q; push_cast; positivity)
      have hSd2_ub : |S_deriv2 (l₀ : ℝ) K| ≤
          ((3 * A_max_q * l₀ ^ 3 * max |l₀ - 4 * seg.kL| |l₀ - 4 * seg.kR| /
            (seg.sg0_L * (seg.kL + l₀) ^ 4) +
          (1 - l₀) * ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) *
            (5 * l₀ * max |3 * l₀ - 4 * seg.kL| |3 * l₀ - 4 * seg.kR| /
            (4 * seg.kL ^ 2 * (seg.kL + l₀) ^ 2))) : ℚ) : ℝ) := by
        unfold S_deriv2
        have h1 := abs_add_le (FKK A_max (l₀ : ℝ) K) ((1 - (l₀ : ℝ)) * t_deriv2 (l₀ : ℝ) K)
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 - (l₀ : ℝ) by linarith)] at h1
        have h2 := mul_le_mul_of_nonneg_left htd2 (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
        push_cast at hfkk0 h2 ⊢; linarith
      have hcX_K_ub : |cX (lX : ℝ) (sX : ℝ) K| ≤
          ((q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX : ℚ) : ℝ) := by
        rw [abs_of_pos (hcX_pos K hK)]
        exact le_trans (cX_mono_K (le_of_lt hlXR) hK_pos hK.2) hcX_R_ub
      have hS_K_ub : |S_val (l₀ : ℝ) K - (a : ℝ)| ≤
          ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
            (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) := by
        rw [abs_of_pos (hcsup_pos K hK)]
        have := le_trans (S_val_mono_K (le_of_lt hl₀R) hl₀1R hK_pos hK.2) hS_R_ub
        push_cast at this ⊢; linarith
      unfold QX_deriv cX_deriv2
      have htri := abs_sub (S_deriv2 (l₀ : ℝ) K * cX (lX : ℝ) (sX : ℝ) K)
        (FKK A_min (lX : ℝ) K * (S_val (l₀ : ℝ) K - (a : ℝ)))
      rw [abs_mul, abs_mul] at htri
      have hm1 := mul_le_mul hSd2_ub hcX_K_ub (abs_nonneg _) (by
        unfold A_max_q; push_cast
        have : 0 ≤ 3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 3 *
            max |(l₀ : ℝ) - 4 * (seg.kL : ℝ)| |(l₀ : ℝ) - 4 * (seg.kR : ℝ)| /
            ((seg.sg0_L : ℝ) * ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 4) := by positivity
        have : 0 ≤ (1 - (l₀ : ℝ)) * ((3 * (751 / 1000 : ℝ) * (seg.kR : ℝ) ^ 2 * (seg.sg0_U : ℝ) /
            ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2) *
            (5 * (l₀ : ℝ) * max |3 * (l₀ : ℝ) - 4 * (seg.kL : ℝ)| |3 * (l₀ : ℝ) - 4 * (seg.kR : ℝ)| /
            (4 * (seg.kL : ℝ) ^ 2 * ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2))) := by positivity
        linarith)
      have hm2 := mul_le_mul hfkkX hS_K_ub (abs_nonneg _) (by unfold A_min_q; push_cast; positivity)
      dsimp [M_Q_q]
      push_cast at hm1 hm2 ⊢
      linarith
    · -- Cota en el punto medio mid
      rw [← hmid_eq]
      have hmid_pos : (0 : ℝ) < (mid_q : ℝ) := by dsimp [mid_q]; push_cast; linarith
      have ht_m_ub : t_val (l₀ : ℝ) (mid_q : ℝ) ≤
          ((3 * A_max_q * mid_q ^ 2 * seg.sg0_mU / (mid_q + l₀) ^ 2 : ℚ) : ℝ) := by
        unfold t_val t_gen A_max A_max_q; push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hg0_m.2 (by positivity)
      have ht_m_lb : ((3 * A_max_q * mid_q ^ 2 * seg.sg0_mL / (mid_q + l₀) ^ 2 : ℚ) : ℝ) ≤
          t_val (l₀ : ℝ) (mid_q : ℝ) := by
        unfold t_val t_gen A_max A_max_q; push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hg0_m.1 (by positivity)
      have hS_m_lb : ((q_max_q * mid_q + A_max_q * g_q l₀ mid_q * seg.sg0_mL +
          (1 - l₀) * (3 * A_max_q * mid_q ^ 2 * seg.sg0_mL / (mid_q + l₀) ^ 2) : ℚ) : ℝ) ≤
          S_val (l₀ : ℝ) (mid_q : ℝ) := by
        unfold S_val F q_max A_max q_max_q A_max_q g_q; push_cast
        have hg0_nn : 0 ≤ 2 * (mid_q : ℝ) * (l₀ : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ)) := by positivity
        have hF : (751 / 1000 : ℝ) * (2 * (mid_q : ℝ) * (l₀ : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ))) *
            (seg.sg0_mL : ℝ) ≤
            (751 / 1000 : ℝ) * (2 * (mid_q : ℝ) * (l₀ : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ))) *
            Real.sqrt (2 * (mid_q : ℝ) * (l₀ : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ))) :=
          mul_le_mul_of_nonneg_left (by simpa [g] using hg0_m.1) (mul_nonneg (by norm_num) hg0_nn)
        have ht := mul_le_mul_of_nonneg_left ht_m_lb (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
        unfold A_max_q at ht; push_cast at ht
        linarith
      have hSd_m_ub : S_deriv (l₀ : ℝ) (mid_q : ℝ) ≤
          ((q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_mU / (mid_q + l₀) ^ 2 +
          (1 - l₀) * (3 * A_max_q * mid_q ^ 2 * seg.sg0_mU / (mid_q + l₀) ^ 2) *
          (5 * l₀ / (2 * mid_q * (mid_q + l₀))) : ℚ) : ℝ) := by
        unfold S_deriv FK t_deriv q_max A_max q_max_q A_max_q; push_cast
        have h1 : 3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 2 * Real.sqrt (g (l₀ : ℝ) (mid_q : ℝ)) /
            ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2 ≤
            3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 2 * (seg.sg0_mU : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hg0_m.2 (by positivity)
        have h2 : (1 - (l₀ : ℝ)) * (t_val (l₀ : ℝ) (mid_q : ℝ) *
            (5 * (l₀ : ℝ) / (2 * (mid_q : ℝ) * ((mid_q : ℝ) + (l₀ : ℝ))))) ≤
            (1 - (l₀ : ℝ)) * (((3 * (751 / 1000 : ℝ) * (mid_q : ℝ) ^ 2 * (seg.sg0_mU : ℝ) /
            ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2)) *
            (5 * (l₀ : ℝ) / (2 * (mid_q : ℝ) * ((mid_q : ℝ) + (l₀ : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          unfold A_max_q at ht_m_ub; push_cast at ht_m_ub
          apply mul_le_mul_of_nonneg_right ht_m_ub (by positivity)
        unfold A_max at h2; push_cast at h2
        linarith
      have hcX_m_ub : cX (lX : ℝ) (sX : ℝ) (mid_q : ℝ) ≤
          ((q_min_q * mid_q + A_min_q * g_q lX mid_q * seg.sgX_mU - sX : ℚ) : ℝ) := by
        unfold cX F q_min A_min q_min_q A_min_q g_q; push_cast
        have hgX_nn : 0 ≤ 2 * (mid_q : ℝ) * (lX : ℝ) / ((mid_q : ℝ) + (lX : ℝ)) := by positivity
        have hF : (749 / 1000 : ℝ) * (2 * (mid_q : ℝ) * (lX : ℝ) / ((mid_q : ℝ) + (lX : ℝ))) *
            Real.sqrt (2 * (mid_q : ℝ) * (lX : ℝ) / ((mid_q : ℝ) + (lX : ℝ))) ≤
            (749 / 1000 : ℝ) * (2 * (mid_q : ℝ) * (lX : ℝ) / ((mid_q : ℝ) + (lX : ℝ))) *
            (seg.sgX_mU : ℝ) :=
          mul_le_mul_of_nonneg_left (by simpa [g] using hgX_m.2) (mul_nonneg (by norm_num) hgX_nn)
        linarith
      have hcXd_m_lb : ((q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_mL / (mid_q + lX) ^ 2 : ℚ) : ℝ) ≤
          cX_deriv (lX : ℝ) (mid_q : ℝ) := by
        unfold cX_deriv FK q_min A_min q_min_q A_min_q; push_cast
        have h1 : 3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 2 * (seg.sgX_mL : ℝ) / ((mid_q : ℝ) + (lX : ℝ)) ^ 2 ≤
            3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 2 * Real.sqrt (g (lX : ℝ) (mid_q : ℝ)) /
            ((mid_q : ℝ) + (lX : ℝ)) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hgX_m.1 (by positivity)
        linarith
      have hmid_mem : (mid_q : ℝ) ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ) := by
        rw [hmid_eq]; exact ⟨by linarith, by linarith⟩
      have hcX_m_pos : 0 < cX (lX : ℝ) (sX : ℝ) (mid_q : ℝ) := hcX_pos (mid_q : ℝ) hmid_mem
      have hS_m_pos : 0 < S_val (l₀ : ℝ) (mid_q : ℝ) - (a : ℝ) := hcsup_pos (mid_q : ℝ) hmid_mem
      have hSd_m_nn : 0 ≤ S_deriv (l₀ : ℝ) (mid_q : ℝ) := by
        unfold S_deriv FK t_deriv q_max A_max t_val t_gen
        have h1m : (0 : ℝ) ≤ 1 - (l₀ : ℝ) := by linarith
        have hfk : (0 : ℝ) ≤ 3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 2 * Real.sqrt (g (l₀ : ℝ) (mid_q : ℝ)) /
            ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _)) (sq_nonneg _)
        have ht : (0 : ℝ) ≤ 3 * (751 / 1000 : ℝ) * (mid_q : ℝ) ^ 2 * Real.sqrt (g (l₀ : ℝ) (mid_q : ℝ)) /
            ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _)) (sq_nonneg _)
        have hfac : (0 : ℝ) ≤ 5 * (l₀ : ℝ) / (2 * (mid_q : ℝ) * ((mid_q : ℝ) + (l₀ : ℝ))) :=
          div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
        exact add_nonneg (add_nonneg (by norm_num) hfk) (mul_nonneg h1m (mul_nonneg ht hfac))
      have hcXd_m_lb_nn : (0 : ℝ) ≤
          ((q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_mL / (mid_q + lX) ^ 2 : ℚ) : ℝ) := by
        unfold q_min_q A_min_q; push_cast; positivity
      have hterm1 : S_deriv (l₀ : ℝ) (mid_q : ℝ) * cX (lX : ℝ) (sX : ℝ) (mid_q : ℝ) ≤
          ((q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_mU / (mid_q + l₀) ^ 2 +
          (1 - l₀) * (3 * A_max_q * mid_q ^ 2 * seg.sg0_mU / (mid_q + l₀) ^ 2) *
          (5 * l₀ / (2 * mid_q * (mid_q + l₀)))) *
          (q_min_q * mid_q + A_min_q * g_q lX mid_q * seg.sgX_mU - sX) : ℚ) := by
        push_cast at hSd_m_ub hcX_m_ub ⊢
        exact mul_le_mul hSd_m_ub hcX_m_ub (le_of_lt hcX_m_pos) (le_trans hSd_m_nn hSd_m_ub)
      have hterm2 : ((q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_mL / (mid_q + lX) ^ 2) *
          (q_max_q * mid_q + A_max_q * g_q l₀ mid_q * seg.sg0_mL +
          (1 - l₀) * (3 * A_max_q * mid_q ^ 2 * seg.sg0_mL / (mid_q + l₀) ^ 2) - a) : ℚ) ≤
          cX_deriv (lX : ℝ) (mid_q : ℝ) * (S_val (l₀ : ℝ) (mid_q : ℝ) - (a : ℝ)) := by
        push_cast
        have hb : (q_max_q : ℝ) * (mid_q : ℝ) + (A_max_q : ℝ) * (g_q l₀ mid_q : ℝ) * (seg.sg0_mL : ℝ) +
            (1 - (l₀ : ℝ)) * (3 * (A_max_q : ℝ) * (mid_q : ℝ) ^ 2 * (seg.sg0_mL : ℝ) / ((mid_q : ℝ) + (l₀ : ℝ)) ^ 2) -
            (a : ℝ) ≤ S_val (l₀ : ℝ) (mid_q : ℝ) - (a : ℝ) := by
          push_cast at hS_m_lb; linarith
        push_cast at hcXd_m_lb_nn
        have h1 := mul_le_mul_of_nonneg_left hb hcXd_m_lb_nn
        have h2 := mul_le_mul_of_nonneg_right hcXd_m_lb (le_of_lt hS_m_pos)
        push_cast at h2
        linarith
      have hQ_R := (Rat.cast_nonpos (K := ℝ)).mpr hQ_neg
      unfold QX
      dsimp [M_Q_q] at hQ_R ⊢
      push_cast at hterm1 hterm2 hQ_R ⊢
      linarith
  -- 4. Monotonicidad de RX y cota inferior de Δ' en todo [kL, kR]
  have hRX_anti : AntitoneOn (RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ))
      (Icc (seg.kL : ℝ) (seg.kR : ℝ)) :=
    RX_antitone_of_QX_nonpos hl₀R hlXR hkL_R hcX_pos hQ_nonpos
  have hlb : ∀ K ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ),
      0 ≤ (eta_min * cX_deriv (lX : ℝ) K * RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K -
        S_deriv (l₀ : ℝ) K) / (S_val (l₀ : ℝ) K - (a : ℝ)) +
        (1 - eta_max) * (5 * (l₀ : ℝ) / (2 * K * (K + (l₀ : ℝ)))) := by
    intro K hK
    have hK_pos : 0 < K := lt_of_lt_of_le hkL_R hK.1
    have hcX_R_pos : 0 < cX (lX : ℝ) (sX : ℝ) (seg.kR : ℝ) :=
      hcX_pos (seg.kR : ℝ) ⟨le_of_lt hkLR_R, le_rfl⟩
    have hS_R_pos : 0 < S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ) :=
      hcsup_pos (seg.kR : ℝ) ⟨le_of_lt hkLR_R, le_rfl⟩
    have hcX_R_ub_pos : (0 : ℝ) <
        ((q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX : ℚ) : ℝ) :=
      lt_of_lt_of_le hcX_R_pos hcX_R_ub
    -- RX K ≥ RX kR ≥ RX_lb
    have hRX_ge : ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) - a) /
        (q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX) : ℚ) ≤
        RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K := by
      have hanti := hRX_anti hK ⟨le_of_lt hkLR_R, le_rfl⟩ hK.2
      unfold RX at hanti ⊢
      have h1 : ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
          (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) /
          ((q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX : ℚ) : ℝ) ≤
          (S_val (l₀ : ℝ) (seg.kR : ℝ) - (a : ℝ)) / cX (lX : ℝ) (sX : ℝ) (seg.kR : ℝ) :=
        div_le_div₀ (le_of_lt hS_R_pos) (by push_cast at hS_R_lb ⊢; linarith) hcX_R_pos hcX_R_ub
      push_cast at h1 ⊢
      linarith
    -- cX_deriv K ≥ cXd_lb
    have hcXd_ge : ((q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_L / (seg.kR + lX) ^ 2 : ℚ) : ℝ) ≤
        cX_deriv (lX : ℝ) K := by
      unfold cX_deriv FK q_min A_min q_min_q A_min_q; push_cast
      have hsg : (seg.sgX_L : ℝ) ≤ Real.sqrt (g (lX : ℝ) K) :=
        le_trans hgX_L_lb (sq_g_mono_K (le_of_lt hlXR) hkL_R hK.1)
      have hdiv : 3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 2 * (seg.sgX_L : ℝ) / ((seg.kR : ℝ) + (lX : ℝ)) ^ 2 ≤
          3 * (749 / 1000 : ℝ) * (lX : ℝ) ^ 2 * Real.sqrt (g (lX : ℝ) K) / (K + (lX : ℝ)) ^ 2 := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hsg (by positivity)) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith [hK.2]) 2)
      linarith
    -- S_deriv K ≤ Sd_ub
    have hSd_le : S_deriv (l₀ : ℝ) K ≤
        ((q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_U / (seg.kL + l₀) ^ 2 +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) *
        (5 * l₀ / (2 * seg.kL * (seg.kL + l₀))) : ℚ) : ℝ) := by
      unfold S_deriv FK t_deriv q_max A_max q_max_q A_max_q; push_cast
      have hsg : Real.sqrt (g (l₀ : ℝ) K) ≤ (seg.sg0_U : ℝ) :=
        le_trans (sq_g_mono_K (le_of_lt hl₀R) hK_pos hK.2) hg0_R_ub
      have h1 : 3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 2 * Real.sqrt (g (l₀ : ℝ) K) / (K + (l₀ : ℝ)) ^ 2 ≤
          3 * (751 / 1000 : ℝ) * (l₀ : ℝ) ^ 2 * (seg.sg0_U : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2 := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hsg (by positivity)) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith [hK.1]) 2)
      have ht_le : t_val (l₀ : ℝ) K ≤
          ((3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2 : ℚ) : ℝ) :=
        le_trans (t_val_mono_K (le_of_lt hl₀R) hK_pos hK.2) ht_R_ub
      have hrat_le : 5 * (l₀ : ℝ) / (2 * K * (K + (l₀ : ℝ))) ≤
          5 * (l₀ : ℝ) / (2 * (seg.kL : ℝ) * ((seg.kL : ℝ) + (l₀ : ℝ))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hK.1]
      have h2 : (1 - (l₀ : ℝ)) * (t_val (l₀ : ℝ) K * (5 * (l₀ : ℝ) / (2 * K * (K + (l₀ : ℝ))))) ≤
          (1 - (l₀ : ℝ)) * (((3 * (751 / 1000 : ℝ) * (seg.kR : ℝ) ^ 2 * (seg.sg0_U : ℝ) /
          ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2)) *
          (5 * (l₀ : ℝ) / (2 * (seg.kL : ℝ) * ((seg.kL : ℝ) + (l₀ : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        unfold A_max_q at ht_le; push_cast at ht_le
        exact mul_le_mul ht_le hrat_le (by positivity) (by positivity)
      unfold A_max at h2; push_cast at h2
      linarith
    -- Combinar numerador y denominador
    set cXd_lb_q : ℚ := q_min_q + 3 * A_min_q * lX ^ 2 * seg.sgX_L / (seg.kR + lX) ^ 2
    set RX_lb_q : ℚ := (q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) - a) /
        (q_min_q * seg.kR + A_min_q * g_q lX seg.kR * seg.sgX_U - sX)
    set Sd_ub_q : ℚ := q_max_q + 3 * A_max_q * l₀ ^ 2 * seg.sg0_U / (seg.kL + l₀) ^ 2 +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2) *
        (5 * l₀ / (2 * seg.kL * (seg.kL + l₀)))
    set num_lb_q : ℚ := eta_min_q * cXd_lb_q * RX_lb_q - Sd_ub_q
    set S_L_q : ℚ := q_max_q * seg.kL + A_max_q * g_q l₀ seg.kL * seg.sg0_L +
        (1 - l₀) * (3 * A_max_q * seg.kL ^ 2 * seg.sg0_L / (seg.kL + l₀) ^ 2)
    set S_U_q : ℚ := q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_U +
        (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_U / (seg.kR + l₀) ^ 2)
    have hcXd_nn : (0 : ℝ) ≤ (cXd_lb_q : ℝ) := by
      dsimp [cXd_lb_q]; unfold q_min_q A_min_q; push_cast; positivity
    have hRX_nn : (0 : ℝ) ≤ (RX_lb_q : ℝ) := by
      have hnum : (0 : ℝ) ≤ ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
          (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) - a : ℚ) : ℝ) := by
        have hS_L_pos_R : (0 : ℝ) < (S_L_q : ℝ) - (a : ℝ) := by
          have : (0 : ℝ) < ((S_L_q - a : ℚ) : ℝ) := by exact_mod_cast hSLa_pos
          rwa [Rat.cast_sub] at this
        have h1 : (S_L_q : ℝ) ≤ ((q_max_q * seg.kR + A_max_q * g_q l₀ seg.kR * seg.sg0_L +
            (1 - l₀) * (3 * A_max_q * seg.kR ^ 2 * seg.sg0_L / (seg.kR + l₀) ^ 2) : ℚ) : ℝ) := by
          dsimp [S_L_q]; unfold q_max_q A_max_q; push_cast
          have hg_le : (g_q l₀ seg.kL : ℝ) ≤ (g_q l₀ seg.kR : ℝ) := by
            simpa [g_q, g] using g_mono_K (le_of_lt hl₀R) hkL_R (le_of_lt hkLR_R)
          have hr_le : ((seg.kL : ℝ) ^ 2 / ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2) ≤
              ((seg.kR : ℝ) ^ 2 / ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2) :=
            ratio_sq_mono_K (le_of_lt hl₀R) hkL_R (le_of_lt hkLR_R)
          have hsg0_nn : (0 : ℝ) ≤ (seg.sg0_L : ℝ) := by positivity
          have ht1 : (9201 / 10000 : ℝ) * (seg.kL : ℝ) ≤ (9201 / 10000 : ℝ) * (seg.kR : ℝ) := by
            linarith [hkLR_R]
          have ht2 : (751 / 1000 : ℝ) * (g_q l₀ seg.kL : ℝ) * (seg.sg0_L : ℝ) ≤
              (751 / 1000 : ℝ) * (g_q l₀ seg.kR : ℝ) * (seg.sg0_L : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg_le (by norm_num)) hsg0_nn
          have ht3 : (1 - (l₀ : ℝ)) * (3 * (751 / 1000 : ℝ) * (seg.kL : ℝ) ^ 2 * (seg.sg0_L : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2) ≤
              (1 - (l₀ : ℝ)) * (3 * (751 / 1000 : ℝ) * (seg.kR : ℝ) ^ 2 * (seg.sg0_L : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            have hr' := mul_le_mul_of_nonneg_left hr_le
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 * (751 / 1000)) hsg0_nn)
            linarith [show 3 * (751 / 1000 : ℝ) * (seg.kL : ℝ) ^ 2 * (seg.sg0_L : ℝ) / ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2 =
                3 * (751 / 1000 : ℝ) * (seg.sg0_L : ℝ) * ((seg.kL : ℝ) ^ 2 / ((seg.kL : ℝ) + (l₀ : ℝ)) ^ 2) by ring,
              show 3 * (751 / 1000 : ℝ) * (seg.kR : ℝ) ^ 2 * (seg.sg0_L : ℝ) / ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2 =
                3 * (751 / 1000 : ℝ) * (seg.sg0_L : ℝ) * ((seg.kR : ℝ) ^ 2 / ((seg.kR : ℝ) + (l₀ : ℝ)) ^ 2) by ring]
          linarith
        push_cast at h1 ⊢; linarith
      dsimp [RX_lb_q]; push_cast at hnum hcX_R_ub_pos ⊢
      exact div_nonneg hnum (le_of_lt hcX_R_ub_pos)
    have hnum_ge : (num_lb_q : ℝ) ≤ eta_min * cX_deriv (lX : ℝ) K *
        RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K - S_deriv (l₀ : ℝ) K := by
      have hmul1 : eta_min * (cXd_lb_q : ℝ) * (RX_lb_q : ℝ) ≤
          eta_min * cX_deriv (lX : ℝ) K * RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K := by
        have heta_nn : 0 ≤ eta_min := by unfold eta_min; norm_num
        have hm1 : eta_min * (cXd_lb_q : ℝ) ≤ eta_min * cX_deriv (lX : ℝ) K :=
          mul_le_mul_of_nonneg_left hcXd_ge heta_nn
        exact mul_le_mul hm1 hRX_ge hRX_nn (mul_nonneg heta_nn (le_trans hcXd_nn hcXd_ge))
      dsimp [num_lb_q]; unfold eta_min eta_min_q at *; push_cast at hmul1 ⊢; linarith
    have hS_K_pos : 0 < S_val (l₀ : ℝ) K - (a : ℝ) := hcsup_pos K hK
    have hS_K_ge : (S_L_q - a : ℚ) ≤ S_val (l₀ : ℝ) K - (a : ℝ) := by
      have := S_val_mono_K (le_of_lt hl₀R) hl₀1R hkL_R hK.1
      rw [Rat.cast_sub]; linarith
    have hS_K_le : S_val (l₀ : ℝ) K - (a : ℝ) ≤ (S_U_q - a : ℚ) := by
      have := S_val_mono_K (le_of_lt hl₀R) hl₀1R hK_pos hK.2
      rw [Rat.cast_sub]; linarith
    have hS_L_pos_R : (0 : ℝ) < (S_L_q - a : ℚ) := by exact_mod_cast hSLa_pos
    have hfrac_ge : ((num_lb_q / (if num_lb_q < 0 then S_L_q - a else S_U_q - a) : ℚ) : ℝ) ≤
        (eta_min * cX_deriv (lX : ℝ) K * RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K -
          S_deriv (l₀ : ℝ) K) / (S_val (l₀ : ℝ) K - (a : ℝ)) := by
      have h1 : (num_lb_q : ℝ) / (S_val (l₀ : ℝ) K - (a : ℝ)) ≤
          (eta_min * cX_deriv (lX : ℝ) K * RX (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) K -
            S_deriv (l₀ : ℝ) K) / (S_val (l₀ : ℝ) K - (a : ℝ)) :=
        div_le_div_of_nonneg_right hnum_ge (le_of_lt hS_K_pos)
      by_cases hneg : num_lb_q < 0
      · simp only [hneg, ↓reduceIte]; push_cast
        have hnum_neg : (num_lb_q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hneg)
        have h2 : (num_lb_q : ℝ) / ((S_L_q : ℝ) - (a : ℝ)) ≤
            (num_lb_q : ℝ) / (S_val (l₀ : ℝ) K - (a : ℝ)) := by
          rw [← neg_le_neg_iff, ← neg_div, ← neg_div]
          exact div_le_div_of_nonneg_left (neg_nonneg.mpr hnum_neg)
            (by push_cast at hS_L_pos_R; exact hS_L_pos_R)
            (by push_cast at hS_K_ge; exact hS_K_ge)
        linarith
      · simp only [hneg, ↓reduceIte]; push_cast
        have hnum_nn : 0 ≤ (num_lb_q : ℝ) := by exact_mod_cast (not_lt.mp hneg)
        have h2 : (num_lb_q : ℝ) / ((S_U_q : ℝ) - (a : ℝ)) ≤
            (num_lb_q : ℝ) / (S_val (l₀ : ℝ) K - (a : ℝ)) :=
          div_le_div_of_nonneg_left hnum_nn hS_K_pos (by push_cast at hS_K_le; exact hS_K_le)
        linarith
    have htail_ge : (((1 - eta_max_q) * (5 * l₀ / (2 * seg.kR * (seg.kR + l₀))) : ℚ) : ℝ) ≤
        (1 - eta_max) * (5 * (l₀ : ℝ) / (2 * K * (K + (l₀ : ℝ)))) := by
      unfold eta_max eta_max_q; push_cast
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul (by linarith [hK.2]) (by linarith [hK.2]) (by positivity) (by positivity)
    have hd_nn_R : (0 : ℝ) ≤
        ((num_lb_q / (if num_lb_q < 0 then S_L_q - a else S_U_q - a) +
          (1 - eta_max_q) * (5 * l₀ / (2 * seg.kR * (seg.kR + l₀))) : ℚ) : ℝ) := by
      exact_mod_cast hd_nn
    rw [Rat.cast_add] at hd_nn_R
    linarith
  exact delta_X_min_at_left hl₀R hlXR hkL_R hcX_pos hcsup_pos hint hlb

/-! ## 4. Cadena de segmentos certificables (`chain_ok`) -/

def chain_ok (segs : List CertSeg) (a l₀ lX sX kmin kmax : ℚ) : Bool :=
  match segs with
  | [] => kmin == kmax
  | seg :: rest =>
    (seg.kL == kmin) && seg.valid a l₀ lX sX && chain_ok rest a l₀ lX sX seg.kR kmax

theorem chain_sound (segs : List CertSeg) {a l₀ lX sX kmin kmax : ℚ}
    (hl₀ : 0 < l₀) (hl₀1 : l₀ ≤ 1) (hlX : 0 < lX) (TX Ψ_a : ℝ)
    (hchain : chain_ok segs a l₀ lX sX kmin kmax = true) :
    ∀ K ∈ Icc (kmin : ℝ) (kmax : ℝ),
      delta_X (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) TX Ψ_a (kmin : ℝ) ≤
      delta_X (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) TX Ψ_a K := by
  induction segs generalizing kmin with
  | nil =>
    unfold chain_ok at hchain
    simp only [beq_iff_eq] at hchain
    subst hchain
    intro K hK
    have : K = (kmin : ℝ) := le_antisymm hK.2 hK.1
    subst this; exact le_rfl
  | cons seg rest ih =>
    unfold chain_ok at hchain
    simp only [Bool.and_eq_true, beq_iff_eq] at hchain
    rcases hchain with ⟨⟨hk_eq, hseg⟩, hrest⟩
    subst hk_eq
    have hseg_sound := seg.valid_sound hl₀ hl₀1 hlX TX Ψ_a hseg
    have hrest_sound := ih hrest
    intro K hK
    rcases le_total K (seg.kR : ℝ) with hle | hge
    · exact hseg_sound K ⟨hK.1, hle⟩
    · have hkR_mem : (seg.kR : ℝ) ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ) := by
        unfold CertSeg.valid at hseg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hseg
        exact ⟨by exact_mod_cast le_of_lt hseg.1.1.1.1.1.1.1.1.1.1.1.1.1.2, le_rfl⟩
      exact le_trans (hseg_sound (seg.kR : ℝ) hkR_mem) (hrest_sound K ⟨hge, hK.2⟩)

/-! ## 5. Listas certificadas para M (12 segmentos) y H₁ (13 segmentos) -/

def M_segs : List CertSeg := [
  ⟨1/10, 23/200, 1009/2500, 4271/10000, 167/400, 1109/2500, 1039/2500, 4157/10000, 1077/2500, 4309/10000⟩,
  ⟨23/200, 13/100, 427/1000, 56/125, 887/2000, 292/625, 4377/10000, 2189/5000, 1139/2500, 4557/10000⟩,
  ⟨13/100, 29/200, 4479/10000, 4671/10000, 4671/10000, 489/1000, 4577/10000, 2289/5000, 2391/5000, 4783/10000⟩,
  ⟨29/200, 4/25, 467/1000, 969/2000, 4889/10000, 509/1000, 4759/10000, 119/250, 4991/10000, 312/625⟩,
  ⟨4/25, 7/40, 1211/2500, 1001/2000, 5089/10000, 5277/10000, 197/400, 2463/5000, 324/625, 1037/2000⟩,
  ⟨7/40, 19/100, 1251/2500, 322/625, 1319/2500, 109/200, 5079/10000, 127/250, 1341/2500, 1073/2000⟩,
  ⟨19/100, 41/200, 5151/10000, 5289/10000, 5449/10000, 5613/10000, 5221/10000, 2611/5000, 1383/2500, 5533/10000⟩,
  ⟨41/200, 11/50, 661/1250, 5417/10000, 1403/2500, 2883/5000, 5353/10000, 2677/5000, 569/1000, 5691/10000⟩,
  ⟨11/50, 47/200, 677/1250, 346/625, 1153/2000, 5911/10000, 1369/2500, 5477/10000, 2919/5000, 5839/10000⟩,
  ⟨47/200, 1/4, 1107/2000, 5647/10000, 591/1000, 6047/10000, 5591/10000, 699/1250, 5979/10000, 299/500⟩,
  ⟨1/4, 53/200, 2823/5000, 719/1250, 3023/5000, 386/625, 5699/10000, 57/100, 6111/10000, 382/625⟩,
  ⟨53/200, 7/25, 5751/10000, 117/200, 247/400, 6299/10000, 5801/10000, 2901/5000, 6237/10000, 3119/5000⟩
]

def H1_segs : List CertSeg := [
  ⟨7/25, 8/25, 383/625, 6403/10000, 6349/10000, 6657/10000, 6269/10000, 627/1000, 6507/10000, 1627/2500⟩,
  ⟨8/25, 9/25, 3201/5000, 6643/10000, 416/625, 6929/10000, 3263/5000, 6527/10000, 1699/2500, 6797/10000⟩,
  ⟨9/25, 2/5, 3321/5000, 6857/10000, 433/625, 1793/2500, 422/625, 6753/10000, 7053/10000, 3527/5000⟩,
  ⟨2/5, 11/25, 857/1250, 881/1250, 7171/10000, 7391/10000, 3477/5000, 1391/2000, 7283/10000, 1821/2500⟩,
  ⟨11/25, 12/25, 7047/10000, 361/500, 739/1000, 759/1000, 1427/2000, 446/625, 1873/2500, 7493/10000⟩,
  ⟨12/25, 13/25, 7219/10000, 59/80, 7589/10000, 7771/10000, 3649/5000, 7299/10000, 3841/5000, 7683/10000⟩,
  ⟨13/25, 14/25, 3687/5000, 7517/10000, 777/1000, 3969/5000, 7447/10000, 931/1250, 1571/2000, 491/625⟩,
  ⟨14/25, 3/5, 1879/2500, 7647/10000, 7937/10000, 8091/10000, 3791/5000, 7583/10000, 1603/2000, 501/625⟩,
  ⟨3/5, 16/25, 3823/5000, 3883/5000, 809/1000, 1029/1250, 3853/5000, 7707/10000, 4081/5000, 8163/10000⟩,
  ⟨16/25, 17/25, 1553/2000, 1969/2500, 8231/10000, 2091/2500, 7821/10000, 3911/5000, 4149/5000, 8299/10000⟩,
  ⟨17/25, 18/25, 63/80, 7977/10000, 8363/10000, 4243/5000, 3963/5000, 7927/10000, 337/400, 4213/5000⟩,
  ⟨18/25, 19/25, 997/1250, 1009/1250, 1697/2000, 43/50, 1003/1250, 321/400, 8543/10000, 534/625⟩,
  ⟨19/25, 4/5, 8071/10000, 102/125, 8599/10000, 4353/5000, 1623/2000, 2029/2500, 8653/10000, 4327/5000⟩
]

theorem M_chain_ok :
    chain_ok M_segs (1/10) (44/100) (68/100) (135/1000) (1/10) (28/100) = true := by
  norm_num [chain_ok, M_segs, CertSeg.valid, g_q, A_min_q, A_max_q, q_min_q, q_max_q,
    eta_min_q, eta_max_q]

theorem H1_chain_ok :
    chain_ok H1_segs (28/100) (57/100) (72/100) (375/1000) (28/100) (80/100) = true := by
  norm_num [chain_ok, H1_segs, CertSeg.valid, g_q, A_min_q, A_max_q, q_min_q, q_max_q,
    eta_min_q, eta_max_q]

/-! ## 6. Certificación en los bordes izquierdos usando MVS.Lemma11 -/

section LeftEndpoint
noncomputable section

/-- Cota certificada inferior de log x para 0 < x < 1 usando rU^(2^s) ≥ 1/x. -/
lemma log_lb_of_inv_pow {x rU : ℝ} {s N : ℕ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hrU : 1 ≤ rU) (hmU : 1 / x ≤ rU ^ (2 ^ s)) :
    -((2 ^ s : ℝ) * (atanhSeries N ((rU - 1) / (rU + 1)) +
      atanhRemUB N ((rU - 1) / (rU + 1)))) ≤ Real.log x := by
  have hmL : (1 : ℝ) ^ (2 ^ s) ≤ 1 / x := by
    rw [one_pow, one_le_div hx0]; exact hx1
  have hb := (log_bounds_of_pow_enclosure N s (m := 1 / x) (rL := 1) (rU := rU)
    le_rfl hrU hmL hmU).2
  rw [Real.log_div one_ne_zero (ne_of_gt hx0), Real.log_one, zero_sub] at hb
  linarith

/-- Cota certificada superior de log x para 0 < x < 1 usando rL^(2^s) ≤ 1/x. -/
lemma log_ub_of_inv_pow {x rL : ℝ} {s N : ℕ}
    (hx0 : 0 < x) (hrL : 1 ≤ rL) (hmL : rL ^ (2 ^ s) ≤ 1 / x) :
    Real.log x ≤ -((2 ^ s : ℝ) * atanhSeries N ((rL - 1) / (rL + 1))) := by
  have hb := (log_bounds_of_pow_enclosure N s (m := 1 / x) (rL := rL) (rU := 1 / x)
    hrL (by have : (1 : ℝ) ≤ rL ^ (2 ^ s) := one_le_pow₀ hrL; linarith)
    hmL (by
      have h1 : (1 : ℝ) ≤ 1 / x := le_trans (one_le_pow₀ hrL) hmL
      exact le_self_pow₀ h1 (by positivity))).1
  rw [Real.log_div one_ne_zero (ne_of_gt hx0), Real.log_one, zero_sub] at hb
  linarith

def left_cert_ok (a l₀ lX sX TX sg0_lo sg0_hi sgX_lo sa_hi : ℚ)
    (rU_cX rU_1mlX rL_S rU_t : ℚ) (s_cX : ℕ) : Bool :=
  let cX_lo := q_min_q * a + A_min_q * g_q lX a * sgX_lo - sX
  let t_lo := 3 * A_max_q * a ^ 2 * sg0_lo / (a + l₀) ^ 2
  let t_hi := 3 * A_max_q * a ^ 2 * sg0_hi / (a + l₀) ^ 2
  let S_lo := q_max_q * a + A_max_q * g_q l₀ a * sg0_lo + (1 - l₀) * t_lo - a
  let S_hi := q_max_q * a + A_max_q * g_q l₀ a * sg0_hi + (1 - l₀) * t_hi - a
  let Psi_ub := (4 / 10 : ℚ) * a - 5 / sa_hi - (185 / 10 : ℚ) - (10 / 301 : ℚ)
  let log_inv_ub := fun (rU : ℚ) (s : ℕ) =>
    (2 ^ s : ℚ) * (atanhSeriesQ 3 ((rU - 1) / (rU + 1)) + atanhRemUBQ 3 ((rU - 1) / (rU + 1)))
  let log_inv_lb := fun (rL : ℚ) (s : ℕ) =>
    (2 ^ s : ℚ) * atanhSeriesQ 3 ((rL - 1) / (rL + 1))
  (0 < l₀) && (0 < lX) && (0 < sg0_lo) && (0 < sg0_hi) && (0 < sgX_lo) && (0 < sa_hi) &&
  (sg0_lo ^ 2 ≤ g_q l₀ a) && (g_q l₀ a ≤ sg0_hi ^ 2) &&
  (sgX_lo ^ 2 ≤ g_q lX a) && (a ≤ sa_hi ^ 2) &&
  (0 < cX_lo) && (cX_lo ≤ 1) && (0 < S_lo) && (0 < S_hi) && (S_hi ≤ 1) && (0 < t_lo) && (t_lo ≤ 1) &&
  ((1 - eta_min_q) * S_hi / t_lo < 1) &&
  (1 ≤ rU_cX) && (1 / cX_lo ≤ rU_cX ^ (2 ^ s_cX)) &&
  (1 ≤ rU_1mlX) && (1 / (1 - lX) ≤ rU_1mlX ^ (2 ^ 2)) &&
  (1 ≤ rL_S) && (rL_S ^ (2 ^ 3) ≤ 1 / S_hi) &&
  (1 ≤ rU_t) && (1 / t_lo ≤ rU_t ^ (2 ^ 3)) &&
  (let lcX_lb := -log_inv_ub rU_cX s_cX
   let l1mlX_lb := -log_inv_ub rU_1mlX 2
   let lS_ub := -log_inv_lb rL_S 3
   let lt_lb := -log_inv_ub rU_t 3
   let check_branch := fun (ηW ηE rL_E rL_1mE : ℚ) =>
     (1 ≤ rL_E) && (rL_E ^ (2 ^ 1) ≤ 1 / ηE) &&
     (1 ≤ rL_1mE) && (rL_1mE ^ (2 ^ 2) ≤ 1 / (1 - ηE)) &&
     let W_lb := ηW * lcX_lb + (1 - ηW) * l1mlX_lb + beta_max_q * TX
     let E_ub := lS_ub - (1 - ηE) * lt_lb +
       ηE * (-log_inv_lb rL_E 1) + (1 - ηE) * (-log_inv_lb rL_1mE 2)
     0 < W_lb - (E_ub + beta_min_q * Psi_ub)
   check_branch eta_min_q eta_min_q (1195/1000) (1351/1000) &&
   check_branch eta_min_q eta_max_q (1195/1000) (1351/1000) &&
   check_branch eta_max_q eta_min_q (1195/1000) (1351/1000) &&
   check_branch eta_max_q eta_max_q (1195/1000) (1351/1000))

theorem left_pos_of_cert {a l₀ lX sX TX sg0_lo sg0_hi sgX_lo sa_hi : ℚ}
    {rU_cX rU_1mlX rL_S rU_t : ℚ} {s_cX : ℕ}
    (ha : 0 < a) (hl₀1 : l₀ ≤ 1) (hlX1 : lX < 1)
    (hok : left_cert_ok a l₀ lX sX TX sg0_lo sg0_hi sgX_lo sa_hi rU_cX rU_1mlX rL_S rU_t s_cX = true) :
    0 < delta_X (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) (TX : ℝ) (Psi_sharp (a : ℝ)) (a : ℝ) := by
  unfold left_cert_ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl₀_pos, hlX_pos⟩, hsg0L_pos⟩, hsg0U_pos⟩, hsgXL_pos⟩,
    hsa_pos⟩, hsg0L_sq⟩, hsg0U_sq⟩, hsgXL_sq⟩, hsa_sq⟩, hcX_pos⟩, hcX_le1⟩, hS_lo_pos⟩, hS_pos⟩,
    hS_le1⟩, ht_pos⟩, ht_le1⟩, hom_lt⟩, hrU_cX_ge1⟩, hrU_cX_pow⟩, hrU_1mlX_ge1⟩, hrU_1mlX_pow⟩,
    hrL_S_ge1⟩, hrL_S_pow⟩, hrU_t_ge1⟩, hrU_t_pow⟩, hbranches⟩
  rcases hbranches with ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hl₀R : (0 : ℝ) < (l₀ : ℝ) := by exact_mod_cast hl₀_pos
  have hl₀1R : (l₀ : ℝ) ≤ 1 := by exact_mod_cast hl₀1
  have hlXR : (0 : ℝ) < (lX : ℝ) := by exact_mod_cast hlX_pos
  have hlX1R : (lX : ℝ) < 1 := by exact_mod_cast hlX1
  have hsg0_bounds : (sg0_lo : ℝ) ≤ Real.sqrt (g (l₀ : ℝ) (a : ℝ)) ∧
      Real.sqrt (g (l₀ : ℝ) (a : ℝ)) ≤ (sg0_hi : ℝ) := by
    apply sqrt_bounds_of_sq (by exact_mod_cast le_of_lt hsg0L_pos)
      (by exact_mod_cast le_of_lt hsg0U_pos)
    · have : (sg0_lo ^ 2 : ℝ) ≤ (g_q l₀ a : ℝ) := by exact_mod_cast hsg0L_sq
      simpa [g_q, g] using this
    · have : (g_q l₀ a : ℝ) ≤ (sg0_hi ^ 2 : ℝ) := by exact_mod_cast hsg0U_sq
      simpa [g_q, g] using this
  have hsgX_lb : (sgX_lo : ℝ) ≤ Real.sqrt (g (lX : ℝ) (a : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (sgX_lo : ℝ) := by exact_mod_cast le_of_lt hsgXL_pos
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    have : (sgX_lo ^ 2 : ℝ) ≤ (g_q lX a : ℝ) := by exact_mod_cast hsgXL_sq
    simpa [g_q, g] using this
  have hsa_ub : Real.sqrt (a : ℝ) ≤ (sa_hi : ℝ) := by
    have hnn : (0 : ℝ) ≤ (sa_hi : ℝ) := by exact_mod_cast le_of_lt hsa_pos
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hsa_sq
  -- Cotas de cX, t_val, S_val - a, Psi_sharp
  set cX_lo_q : ℚ := q_min_q * a + A_min_q * g_q lX a * sgX_lo - sX
  set t_lo_q : ℚ := 3 * A_max_q * a ^ 2 * sg0_lo / (a + l₀) ^ 2
  set t_hi_q : ℚ := 3 * A_max_q * a ^ 2 * sg0_hi / (a + l₀) ^ 2
  set S_hi_q : ℚ := q_max_q * a + A_max_q * g_q l₀ a * sg0_hi + (1 - l₀) * t_hi_q - a
  set Psi_ub_q : ℚ := (4 / 10 : ℚ) * a - 5 / sa_hi - (185 / 10 : ℚ) - (10 / 301 : ℚ)
  have hcX_ge : (cX_lo_q : ℝ) ≤ cX (lX : ℝ) (sX : ℝ) (a : ℝ) := by
    dsimp [cX_lo_q]; unfold cX F q_min A_min q_min_q A_min_q g_q; push_cast
    have hgX_nn : 0 ≤ 2 * (a : ℝ) * (lX : ℝ) / ((a : ℝ) + (lX : ℝ)) := by positivity
    have hF := mul_le_mul_of_nonneg_left (by simpa [g] using hsgX_lb)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 749 / 1000) hgX_nn)
    linarith
  have ht_ge : (t_lo_q : ℝ) ≤ t_val (l₀ : ℝ) (a : ℝ) := by
    dsimp [t_lo_q]; unfold t_val t_gen A_max A_max_q; push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsg0_bounds.1 (by positivity)
  have ht_le : t_val (l₀ : ℝ) (a : ℝ) ≤ (t_hi_q : ℝ) := by
    dsimp [t_hi_q]; unfold t_val t_gen A_max A_max_q; push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsg0_bounds.2 (by positivity)
  have hS_le : S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ) ≤ (S_hi_q : ℝ) := by
    dsimp [S_hi_q]; unfold S_val F q_max A_max q_max_q A_max_q g_q; push_cast
    have hg0_nn : 0 ≤ 2 * (a : ℝ) * (l₀ : ℝ) / ((a : ℝ) + (l₀ : ℝ)) := by positivity
    have hF := mul_le_mul_of_nonneg_left (by simpa [g] using hsg0_bounds.2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 751 / 1000) hg0_nn)
    have ht := mul_le_mul_of_nonneg_left ht_le (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
    unfold A_max at ht; push_cast at ht
    linarith
  have hPsi_le : Psi_sharp (a : ℝ) ≤ (Psi_ub_q : ℝ) := by
    dsimp [Psi_ub_q]; unfold Psi_sharp; push_cast
    have hsa_posR : (0 : ℝ) < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr haR
    have hdiv : 5 / (sa_hi : ℝ) ≤ 5 / Real.sqrt (a : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hsa_posR hsa_ub
    linarith
  have hcX_lo_posR : (0 : ℝ) < (cX_lo_q : ℝ) := by exact_mod_cast hcX_pos
  have hcX_lo_le1R : (cX_lo_q : ℝ) ≤ 1 := by exact_mod_cast hcX_le1
  have ht_lo_posR : (0 : ℝ) < (t_lo_q : ℝ) := by exact_mod_cast ht_pos
  have ht_lo_le1R : (t_lo_q : ℝ) ≤ 1 := by exact_mod_cast ht_le1
  have hS_hi_posR : (0 : ℝ) < (S_hi_q : ℝ) := by exact_mod_cast hS_pos
  have hS_hi_le1R : (S_hi_q : ℝ) ≤ 1 := by exact_mod_cast hS_le1
  have hS_a_pos : 0 < S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ) := by
    have hS_lo_R : (0 : ℝ) <
        ((q_max_q * a + A_max_q * g_q l₀ a * sg0_lo + (1 - l₀) * t_lo_q - a : ℚ) : ℝ) := by
      exact_mod_cast hS_lo_pos
    have hS_ge : ((q_max_q * a + A_max_q * g_q l₀ a * sg0_lo + (1 - l₀) * t_lo_q - a : ℚ) : ℝ) ≤
        S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ) := by
      unfold S_val F q_max A_max q_max_q A_max_q g_q; push_cast
      have hg0_nn : 0 ≤ 2 * (a : ℝ) * (l₀ : ℝ) / ((a : ℝ) + (l₀ : ℝ)) := by positivity
      have hF := mul_le_mul_of_nonneg_left (by simpa [g] using hsg0_bounds.1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 751 / 1000) hg0_nn)
      have ht := mul_le_mul_of_nonneg_left ht_ge (show 0 ≤ 1 - (l₀ : ℝ) by linarith)
      unfold A_max at ht; push_cast at ht
      linarith
    linarith
  -- Cotas de log vía Lemma11
  have hlog_cX : -((2 ^ s_cX : ℝ) * (atanhSeries 3 (((rU_cX : ℝ) - 1) / ((rU_cX : ℝ) + 1)) +
      atanhRemUB 3 (((rU_cX : ℝ) - 1) / ((rU_cX : ℝ) + 1)))) ≤
      Real.log (cX (lX : ℝ) (sX : ℝ) (a : ℝ)) := by
    have h1 := log_lb_of_inv_pow (rU := (rU_cX : ℝ)) (s := s_cX) (N := 3) hcX_lo_posR hcX_lo_le1R
      (by exact_mod_cast hrU_cX_ge1) (by exact_mod_cast hrU_cX_pow)
    have h2 := Real.log_le_log hcX_lo_posR hcX_ge
    linarith
  have hlog_1mlX : -((2 ^ 2 : ℝ) * (atanhSeries 3 (((rU_1mlX : ℝ) - 1) / ((rU_1mlX : ℝ) + 1)) +
      atanhRemUB 3 (((rU_1mlX : ℝ) - 1) / ((rU_1mlX : ℝ) + 1)))) ≤
      Real.log (1 - (lX : ℝ)) := by
    have h1mlX_pos : (0 : ℝ) < 1 - (lX : ℝ) := by linarith
    have h1mlX_le1 : 1 - (lX : ℝ) ≤ 1 := by linarith
    exact log_lb_of_inv_pow (rU := (rU_1mlX : ℝ)) (s := 2) (N := 3) h1mlX_pos h1mlX_le1
      (by exact_mod_cast hrU_1mlX_ge1) (by exact_mod_cast hrU_1mlX_pow)
  have hlog_S : Real.log (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) ≤
      -((2 ^ 3 : ℝ) * atanhSeries 3 (((rL_S : ℝ) - 1) / ((rL_S : ℝ) + 1))) := by
    have h1 := log_ub_of_inv_pow (rL := (rL_S : ℝ)) (s := 3) (N := 3) hS_hi_posR
      (by exact_mod_cast hrL_S_ge1) (by exact_mod_cast hrL_S_pow)
    have h2 := Real.log_le_log hS_a_pos hS_le
    linarith
  have hlog_t : -((2 ^ 3 : ℝ) * (atanhSeries 3 (((rU_t : ℝ) - 1) / ((rU_t : ℝ) + 1)) +
      atanhRemUB 3 (((rU_t : ℝ) - 1) / ((rU_t : ℝ) + 1)))) ≤
      Real.log (t_val (l₀ : ℝ) (a : ℝ)) := by
    have h1 := log_lb_of_inv_pow (rU := (rU_t : ℝ)) (s := 3) (N := 3) ht_lo_posR ht_lo_le1R
      (by exact_mod_cast hrU_t_ge1) (by exact_mod_cast hrU_t_pow)
    have h2 := Real.log_le_log ht_lo_posR ht_ge
    linarith
  -- Lema auxiliar para cada una de las 4 ramas
  have hbranch_pos : ∀ {ηW ηE rL_E rL_1mE : ℚ},
      (ηW = eta_min_q ∨ ηW = eta_max_q) → (ηE = eta_min_q ∨ ηE = eta_max_q) →
      (1 ≤ rL_E ∧ rL_E ^ (2 ^ 1) ≤ 1 / ηE ∧
       1 ≤ rL_1mE ∧ rL_1mE ^ (2 ^ 2) ≤ 1 / (1 - ηE) ∧
       0 < (ηW * (-((2 ^ s_cX : ℚ) * (atanhSeriesQ 3 ((rU_cX - 1) / (rU_cX + 1)) +
              atanhRemUBQ 3 ((rU_cX - 1) / (rU_cX + 1))))) +
            (1 - ηW) * (-((2 ^ 2 : ℚ) * (atanhSeriesQ 3 ((rU_1mlX - 1) / (rU_1mlX + 1)) +
              atanhRemUBQ 3 ((rU_1mlX - 1) / (rU_1mlX + 1))))) +
            beta_max_q * TX) -
           (((-((2 ^ 3 : ℚ) * atanhSeriesQ 3 ((rL_S - 1) / (rL_S + 1)))) -
            (1 - ηE) * (-((2 ^ 3 : ℚ) * (atanhSeriesQ 3 ((rU_t - 1) / (rU_t + 1)) +
              atanhRemUBQ 3 ((rU_t - 1) / (rU_t + 1))))) +
            ηE * (-((2 ^ 1 : ℚ) * atanhSeriesQ 3 ((rL_E - 1) / (rL_E + 1)))) +
            (1 - ηE) * (-((2 ^ 2 : ℚ) * atanhSeriesQ 3 ((rL_1mE - 1) / (rL_1mE + 1))))) +
            beta_min_q * Psi_ub_q)) →
      0 < delta_branch (a : ℝ) (l₀ : ℝ) (lX : ℝ) (sX : ℝ) (TX : ℝ) (Psi_sharp (a : ℝ))
        (ηW : ℝ) (ηE : ℝ) (a : ℝ) := by
    intro ηW ηE rL_E rL_1mE hηW_eq hηE_eq ⟨hrE1, hrE_pow, hr1mE1, hr1mE_pow, hpos_q⟩
    have hηW_pos : (0 : ℝ) < (ηW : ℝ) := by
      rcases hηW_eq with rfl | rfl <;> norm_num [eta_min_q, eta_max_q]
    have h1mηW_nn : (0 : ℝ) ≤ 1 - (ηW : ℝ) := by
      rcases hηW_eq with rfl | rfl <;> norm_num [eta_min_q, eta_max_q]
    have hηE_pos : (0 : ℝ) < (ηE : ℝ) := by
      rcases hηE_eq with rfl | rfl <;> norm_num [eta_min_q, eta_max_q]
    have hηE_lt1 : (ηE : ℝ) < 1 := by
      rcases hηE_eq with rfl | rfl <;> norm_num [eta_min_q, eta_max_q]
    have h1mηE_pos : (0 : ℝ) < 1 - (ηE : ℝ) := by linarith
    -- Simplificar E_plus_branch usando ω* < 1
    have hint_E : (1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) /
        t_val (l₀ : ℝ) (a : ℝ) < 1 := by
      have h1mη_le : 1 - (ηE : ℝ) ≤ 1 - (eta_min_q : ℝ) := by
        rcases hηE_eq with rfl | rfl
        · exact le_rfl
        · norm_num [eta_min_q, eta_max_q]
      have hnum : (1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) ≤
          ((1 - eta_min_q) * S_hi_q : ℚ) := by
        have hS_nn : 0 ≤ S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ) := le_of_lt hS_a_pos
        have := mul_le_mul h1mη_le hS_le hS_nn (by norm_num [eta_min_q])
        push_cast; linarith
      have hdiv : (1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) /
          t_val (l₀ : ℝ) (a : ℝ) ≤ (((1 - eta_min_q) * S_hi_q / t_lo_q : ℚ) : ℝ) := by
        push_cast at hnum ⊢
        exact div_le_div₀ (by unfold eta_min_q; push_cast; positivity)
          hnum ht_lo_posR ht_ge
      have homR : (((1 - eta_min_q) * S_hi_q / t_lo_q : ℚ) : ℝ) < 1 := by
        exact_mod_cast hom_lt
      linarith
    have hE_eq : E_plus_branch (ηE : ℝ) (a : ℝ) (l₀ : ℝ) (a : ℝ) =
        Real.log (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) -
          (1 - (ηE : ℝ)) * Real.log (t_val (l₀ : ℝ) (a : ℝ)) +
          ((ηE : ℝ) * Real.log (ηE : ℝ) + (1 - (ηE : ℝ)) * Real.log (1 - (ηE : ℝ))) := by
      unfold E_plus_branch omega_star; dsimp only
      rw [min_eq_right (le_of_lt hint_E)]
      have ht_posR : 0 < t_val (l₀ : ℝ) (a : ℝ) := lt_of_lt_of_le ht_lo_posR ht_ge
      have hmul : t_val (l₀ : ℝ) (a : ℝ) *
          ((1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) / t_val (l₀ : ℝ) (a : ℝ)) =
          (1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) := by
        field_simp [ne_of_gt ht_posR]
      rw [hmul]
      have hsub : S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ) -
          (1 - (ηE : ℝ)) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) =
          (ηE : ℝ) * (S_val (l₀ : ℝ) (a : ℝ) - (a : ℝ)) := by ring
      rw [hsub, Real.log_mul (ne_of_gt hηE_pos) (ne_of_gt hS_a_pos),
        Real.log_div (ne_of_gt (mul_pos h1mηE_pos hS_a_pos)) (ne_of_gt ht_posR),
        Real.log_mul (ne_of_gt h1mηE_pos) (ne_of_gt hS_a_pos)]
      ring
    have hlog_E := log_ub_of_inv_pow (rL := (rL_E : ℝ)) (s := 1) (N := 3) hηE_pos
      (by exact_mod_cast hrE1) (by exact_mod_cast hrE_pow)
    have hlog_1mE := log_ub_of_inv_pow (rL := (rL_1mE : ℝ)) (s := 2) (N := 3) h1mηE_pos
      (by exact_mod_cast hr1mE1) (by exact_mod_cast hr1mE_pow)
    unfold delta_branch
    rw [hE_eq]
    have hW1 := mul_le_mul_of_nonneg_left hlog_cX (le_of_lt hηW_pos)
    have hW2 := mul_le_mul_of_nonneg_left hlog_1mlX h1mηW_nn
    have hE1 := mul_le_mul_of_nonneg_left hlog_t (le_of_lt h1mηE_pos)
    have hE2 := mul_le_mul_of_nonneg_left hlog_E (le_of_lt hηE_pos)
    have hE3 := mul_le_mul_of_nonneg_left hlog_1mE (le_of_lt h1mηE_pos)
    have hPsi := mul_le_mul_of_nonneg_left hPsi_le (by unfold beta_min; norm_num : (0 : ℝ) ≤ beta_min)
    have hposR : (0 : ℝ) <
        (ηW : ℝ) * -(2 ^ s_cX * (atanhSeries 3 (((rU_cX : ℝ) - 1) / ((rU_cX : ℝ) + 1)) +
          atanhRemUB 3 (((rU_cX : ℝ) - 1) / ((rU_cX : ℝ) + 1)))) +
        (1 - (ηW : ℝ)) * -(2 ^ 2 * (atanhSeries 3 (((rU_1mlX : ℝ) - 1) / ((rU_1mlX : ℝ) + 1)) +
          atanhRemUB 3 (((rU_1mlX : ℝ) - 1) / ((rU_1mlX : ℝ) + 1)))) +
        beta_max * (TX : ℝ) -
        (-(2 ^ 3 * atanhSeries 3 (((rL_S : ℝ) - 1) / ((rL_S : ℝ) + 1))) -
          (1 - (ηE : ℝ)) * -(2 ^ 3 * (atanhSeries 3 (((rU_t : ℝ) - 1) / ((rU_t : ℝ) + 1)) +
            atanhRemUB 3 (((rU_t : ℝ) - 1) / ((rU_t : ℝ) + 1)))) +
          (ηE : ℝ) * -(2 ^ 1 * atanhSeries 3 (((rL_E : ℝ) - 1) / ((rL_E : ℝ) + 1))) +
          (1 - (ηE : ℝ)) * -(2 ^ 2 * atanhSeries 3 (((rL_1mE : ℝ) - 1) / ((rL_1mE : ℝ) + 1))) +
          beta_min * (Psi_ub_q : ℝ)) := by
      have hr : ∀ q : ℚ, (((q - 1) / (q + 1) : ℚ) : ℝ) = ((q : ℝ) - 1) / ((q : ℝ) + 1) := by
        intro q; push_cast; ring
      simp only [← hr, ← atanhSeriesQ_cast, ← atanhRemUBQ_cast]
      unfold beta_max beta_min
      have hbm1 : (9701 / 10000 : ℝ) = (beta_max_q : ℝ) := by unfold beta_max_q; norm_num
      have hbm2 : (9699 / 10000 : ℝ) = (beta_min_q : ℝ) := by unfold beta_min_q; norm_num
      rw [hbm1, hbm2]
      exact_mod_cast hpos_q
    linarith
  -- Cerrar las 4 ramas de delta_X
  unfold delta_X eta_min eta_max
  have heta_min_eq : (eta_min_q : ℝ) = 6999 / 10000 := by unfold eta_min_q; norm_num
  have heta_max_eq : (eta_max_q : ℝ) = 7001 / 10000 := by unfold eta_max_q; norm_num
  rw [← heta_min_eq, ← heta_max_eq]
  simp only [lt_min_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact hbranch_pos (ηW := eta_min_q) (ηE := eta_min_q) (rL_E := 1195/1000)
      (rL_1mE := 1351/1000) (Or.inl rfl) (Or.inl rfl)
      ⟨hb1.1.1.1.1, hb1.1.1.1.2, hb1.1.1.2, hb1.1.2, hb1.2⟩
  · exact hbranch_pos (ηW := eta_min_q) (ηE := eta_max_q) (rL_E := 1195/1000)
      (rL_1mE := 1351/1000) (Or.inl rfl) (Or.inr rfl)
      ⟨hb2.1.1.1.1, hb2.1.1.1.2, hb2.1.1.2, hb2.1.2, hb2.2⟩
  · exact hbranch_pos (ηW := eta_max_q) (ηE := eta_min_q) (rL_E := 1195/1000)
      (rL_1mE := 1351/1000) (Or.inr rfl) (Or.inl rfl)
      ⟨hb3.1.1.1.1, hb3.1.1.1.2, hb3.1.1.2, hb3.1.2, hb3.2⟩
  · exact hbranch_pos (ηW := eta_max_q) (ηE := eta_max_q) (rL_E := 1195/1000)
      (rL_1mE := 1351/1000) (Or.inr rfl) (Or.inr rfl)
      ⟨hb4.1.1.1.1, hb4.1.1.1.2, hb4.1.1.2, hb4.1.2, hb4.2⟩

theorem M_left_ok :
    left_cert_ok (1/10) (44/100) (68/100) (135/1000) (-33103/1000)
      (2523/6250) (40369/100000) (10439/25000) (31623/100000)
      (6609/5000) (831/625) (14247/10000) (7713/5000) 4 = true := by
  norm_num [left_cert_ok, atanhSeriesQ, atanhRemUBQ, Finset.sum_range_succ, g_q,
    A_min_q, A_max_q, q_min_q, q_max_q, beta_min_q, beta_max_q, eta_min_q, eta_max_q]

theorem H1_left_ok :
    left_cert_ok (28/100) (57/100) (72/100) (375/1000) (-27164/1000)
      (383/625) (61281/100000) (31749/50000) (13229/25000)
      (2941/2500) (3437/2500) (12119/10000) (12679/10000) 4 = true := by
  norm_num [left_cert_ok, atanhSeriesQ, atanhRemUBQ, Finset.sum_range_succ, g_q,
    A_min_q, A_max_q, q_min_q, q_max_q, beta_min_q, beta_max_q, eta_min_q, eta_max_q]

/-- Proposición 2 (Región M = [0.10, 0.28]): positividad estricta Δ_M(K) > 0 en todo [0.10, 0.28]. -/
theorem prop2_M_positive :
    ∀ K ∈ Icc (1 / 10 : ℝ) (28 / 100 : ℝ),
      0 < delta_X (1 / 10) (44 / 100) (68 / 100) (135 / 1000) (-33103 / 1000)
        (Psi_sharp (1 / 10)) K := by
  have hleft : 0 < delta_X (1 / 10) (44 / 100) (68 / 100) (135 / 1000) (-33103 / 1000)
      (Psi_sharp (1 / 10)) (1 / 10) := by
    simpa using left_pos_of_cert (a := 1/10) (l₀ := 44/100) (lX := 68/100)
      (sX := 135/1000) (TX := -33103/1000) (by norm_num) (by norm_num) (by norm_num) M_left_ok
  have hmono := chain_sound M_segs (a := 1/10) (l₀ := 44/100) (lX := 68/100)
    (sX := 135/1000) (kmin := 1/10) (kmax := 28/100) (by norm_num) (by norm_num) (by norm_num)
    (-33103 / 1000) (Psi_sharp (1 / 10)) M_chain_ok
  push_cast at hmono
  intro K hK
  exact lt_of_lt_of_le hleft (hmono K hK)

/-- Proposición 2 (Región H₁ = [0.28, 0.80]): positividad estricta Δ_{H₁}(K) > 0 en todo [0.28, 0.80]. -/
theorem prop2_H1_positive :
    ∀ K ∈ Icc (28 / 100 : ℝ) (80 / 100 : ℝ),
      0 < delta_X (28 / 100) (57 / 100) (72 / 100) (375 / 1000) (-27164 / 1000)
        (Psi_sharp (28 / 100)) K := by
  have hleft : 0 < delta_X (28 / 100) (57 / 100) (72 / 100) (375 / 1000) (-27164 / 1000)
      (Psi_sharp (28 / 100)) (28 / 100) := by
    simpa using left_pos_of_cert (a := 28/100) (l₀ := 57/100) (lX := 72/100)
      (sX := 375/1000) (TX := -27164/1000) (by norm_num) (by norm_num) (by norm_num) H1_left_ok
  have hmono := chain_sound H1_segs (a := 28/100) (l₀ := 57/100) (lX := 72/100)
    (sX := 375/1000) (kmin := 28/100) (kmax := 80/100) (by norm_num) (by norm_num) (by norm_num)
    (-27164 / 1000) (Psi_sharp (28 / 100)) H1_chain_ok
  push_cast at hmono
  intro K hK
  exact lt_of_lt_of_le hleft (hmono K hK)

end
end LeftEndpoint

end MVS.Proposition2Cert
