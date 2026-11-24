import MVS.CEGIS
import MVS.Lemma11
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Certificación en el Kernel de la Barrera `B_net` de 22 Nodos (Caso 1, $\tau_H \le 9$)

Conecta directamente los 22 nodos exportados de `case1_affine_gap.B_net` en
`cegis_certificates.json` con `MVS.CEGIS.cegis_staying_deadline_sound` y `MVS.Lemma11`,
certificando en el kernel de Lean 4 (sin `sorry` ni axiomas extra):
1. $\forall \theta \in \mathcal{P},\ \forall y \in [0.10, 0.28],\ 19 \le W_M(\theta, y) - B_{\text{case1}}(y)$.
2. $\forall y \in [0.10, 0.28],\ \Psi^\#(y) - B_{\text{case1}}(y) \le 24.7$.
3. `case1_deadline_9_certified`: toda trayectoria de 9 pasos que permanezca en $M = [0.10, 0.28)$
   bajo la barrera `B_case1` es estrictamente dominada por $W_M(\theta, x_0)$.
-/

open Finset Real Set MVS.Theorem1 MVS.Lemma11 MVS.CEGIS

namespace MVS.CEGISCert

/-! ## 1. Segmentos racionales y evaluador exacto `LogPWL` -/

/-- Un segmento `[kL, kR]` de la tabla `LogPWL` de `B_net` con testigos racionales
    para `W_M(kL)` (`sg_lo`, `rU_c`) y `Psi_sharp(kR)` (`sk_ub`). -/
structure BSeg where
  kL : ℚ
  vL : ℚ
  kR : ℚ
  vR : ℚ
  sg_lo : ℚ
  rU_c : ℚ
  sk_ub : ℚ

/-- Evaluación exacta `LogPWL` de la cadena de segmentos `BSeg`. -/
noncomputable def evalBSegs : List BSeg → ℝ → ℝ
  | [], _ => 0
  | [seg], x => segEval (seg.kL : ℝ) (seg.vL : ℝ) (seg.kR : ℝ) (seg.vR : ℝ) x
  | seg :: rest, x =>
    if x ≤ (seg.kR : ℝ) then segEval (seg.kL : ℝ) (seg.vL : ℝ) (seg.kR : ℝ) (seg.vR : ℝ) x
    else evalBSegs rest x

/-- Constantes racionales exactas para la verificación booleana. -/
def q_min_q : ℚ := 9199 / 10000
def A_min_q : ℚ := 749 / 1000
def eta_max_q : ℚ := 7001 / 10000
def beta_max_q : ℚ := 9701 / 10000
def lM_q : ℚ := 68 / 100
def sM_q : ℚ := 135 / 1000
def TM_q : ℚ := -33103 / 1000
def rU_32_q : ℚ := 66479 / 50000

/-- Serie truncada racional `atanhSeries` de orden `N = 2` y residuo `atanhRemUB`. -/
def atanh2Q (u : ℚ) : ℚ :=
  2 * (u + u ^ 3 / 3) + 2 * u ^ 5 / (5 * (1 - u ^ 2))

lemma atanh2Q_cast (u : ℚ) :
    (atanh2Q u : ℝ) = atanhSeries 2 (u : ℝ) + atanhRemUB 2 (u : ℝ) := by
  unfold atanh2Q atanhSeries atanhRemUB
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast; ring

/-- Cota inferior racional fija para `log(0.32)` con `s = 2`, `N = 2`. -/
def L32_q : ℚ := -(4 * atanh2Q ((rU_32_q - 1) / (rU_32_q + 1)))

lemma L32_le_log : (L32_q : ℝ) ≤ Real.log (1 - 68 / 100 : ℝ) := by
  have h32_pos : (0 : ℝ) < 1 - 68 / 100 := by norm_num
  have hmL : (1 : ℝ) ^ (2 ^ 2) ≤ 1 / (1 - 68 / 100 : ℝ) := by norm_num
  have hmU : 1 / (1 - 68 / 100 : ℝ) ≤ (rU_32_q : ℝ) ^ (2 ^ 2) := by
    unfold rU_32_q; push_cast; norm_num
  have hb := (log_bounds_of_pow_enclosure 2 2 (m := 1 / (1 - 68 / 100 : ℝ))
    (rL := 1) (rU := (rU_32_q : ℝ)) le_rfl (by unfold rU_32_q; push_cast; norm_num) hmL hmU).2
  rw [Real.log_div (by norm_num) (ne_of_gt h32_pos), Real.log_one, zero_sub] at hb
  have hcast : (L32_q : ℝ) = -((2 ^ 2 : ℝ) *
      (atanhSeries 2 (((rU_32_q : ℝ) - 1) / ((rU_32_q : ℝ) + 1)) +
       atanhRemUB 2 (((rU_32_q : ℝ) - 1) / ((rU_32_q : ℝ) + 1)))) := by
    unfold L32_q
    have hu : (((rU_32_q - 1) / (rU_32_q + 1) : ℚ) : ℝ) =
        ((rU_32_q : ℝ) - 1) / ((rU_32_q : ℝ) + 1) := by push_cast; ring
    push_cast
    rw [← hu, atanh2Q_cast]
    ring
  linarith

/-- Verificador booleano racional de un segmento `BSeg`. -/
def BSeg.valid (seg : BSeg) : Bool :=
  let g := 2 * seg.kL * lM_q / (seg.kL + lM_q)
  let c_lo := q_min_q * seg.kL + A_min_q * g * seg.sg_lo - sM_q
  let L_c := -(16 * atanh2Q ((seg.rU_c - 1) / (seg.rU_c + 1)))
  let W_lb := eta_max_q * L_c + (1 - eta_max_q) * L32_q + beta_max_q * TM_q
  let Psi_ub := (4 / 10 : ℚ) * seg.kR - 5 / seg.sk_ub - (185 / 10 : ℚ) - (10 / 301 : ℚ)
  decide (
    (0 < seg.kL) ∧ (seg.kL < seg.kR) ∧ (seg.vL ≤ seg.vR) ∧
    (0 ≤ seg.sg_lo) ∧ (seg.sg_lo ^ 2 ≤ g) ∧
    (0 < c_lo) ∧ (c_lo ≤ 1) ∧
    (1 ≤ seg.rU_c) ∧ (1 / c_lo ≤ seg.rU_c ^ 16) ∧
    (L_c ≤ L32_q) ∧
    (19 ≤ W_lb - seg.vR) ∧
    (0 < seg.sk_ub) ∧ (seg.kR ≤ seg.sk_ub ^ 2) ∧
    (Psi_ub - seg.vL ≤ 247 / 10)
  )

/-! ## 2. Corrección de `BSeg.valid` y composición de cadena -/

/-- Monotonicidad de `Psi_sharp` en `(0, ∞)`. -/
lemma Psi_sharp_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Psi_sharp x ≤ Psi_sharp y := by
  unfold Psi_sharp
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hdiv : 5 / Real.sqrt y ≤ 5 / Real.sqrt x :=
    div_le_div_of_nonneg_left (by norm_num) hsx hsq
  linarith

/-- Corrección de un segmento `BSeg` certificado:
    en todo `y ∈ [kL, kR]` y para todo `θ ∈ P`,
    `19 ≤ W_M θ y - segEval ... y` y `Psi_sharp y - segEval ... y ≤ 24.7`. -/
theorem BSeg.valid_sound (seg : BSeg) (hv : seg.valid = true) (θ : Params) {y : ℝ}
    (hy : y ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ)) :
    (19 : ℝ) ≤ W_M θ y - segEval (seg.kL : ℝ) (seg.vL : ℝ) (seg.kR : ℝ) (seg.vR : ℝ) y ∧
    Psi_sharp y - segEval (seg.kL : ℝ) (seg.vL : ℝ) (seg.kR : ℝ) (seg.vR : ℝ) y ≤ 247 / 10 := by
  unfold BSeg.valid at hv
  rw [decide_eq_true_iff] at hv
  rcases hv with ⟨hkL0, hkLR, hvLR, hsg_nn, hsg_sq, hc_pos, hc_le1, hrU1, hmU, hL_ord,
    hW_gap, hsk_pos, hsk_sq, hPsi_gap⟩
  have hkL_R : (0 : ℝ) < (seg.kL : ℝ) := by exact_mod_cast hkL0
  have hkLR_R : (seg.kL : ℝ) < (seg.kR : ℝ) := by exact_mod_cast hkLR
  have hvLR_R : (seg.vL : ℝ) ≤ (seg.vR : ℝ) := by exact_mod_cast hvLR
  -- Encierro del segmento LogPWL: vL ≤ segEval y ≤ vR
  have hseg_bounds := segEval_mem_Icc (vL := (seg.vL : ℝ)) (vR := (seg.vR : ℝ)) hkL_R hkLR_R hy
  rw [min_eq_left hvLR_R, max_eq_right hvLR_R] at hseg_bounds
  constructor
  · -- 1. Cota inferior 19 ≤ W_M θ y - B(y)
    set g_q : ℚ := 2 * seg.kL * lM_q / (seg.kL + lM_q)
    set c_lo_q : ℚ := q_min_q * seg.kL + A_min_q * g_q * seg.sg_lo - sM_q
    set L_c_q : ℚ := -(16 * atanh2Q ((seg.rU_c - 1) / (seg.rU_c + 1)))
    have hg_nn : (0 : ℝ) ≤ (g_q : ℝ) := by
      dsimp [g_q]; unfold lM_q; push_cast; positivity
    have hsg_le : (seg.sg_lo : ℝ) ≤ Real.sqrt (g_q : ℝ) := by
      have hsq : (seg.sg_lo : ℝ) ^ 2 ≤ (Real.sqrt (g_q : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt hg_nn]; exact_mod_cast hsg_sq
      have hsg_nnR : (0 : ℝ) ≤ (seg.sg_lo : ℝ) := by exact_mod_cast hsg_nn
      nlinarith [Real.sqrt_nonneg (g_q : ℝ)]
    have hcM_kL_ge : (c_lo_q : ℝ) ≤ c_M (seg.kL : ℝ) := by
      dsimp [c_lo_q, g_q]; unfold c_M F q_min A_min q_min_q A_min_q lM_q sM_q; push_cast
      have hA_nn : (0 : ℝ) ≤ 749 / 1000 := by norm_num
      have hg_eq : (2 * (seg.kL : ℝ) * (68 / 100) / ((seg.kL : ℝ) + 68 / 100)) = (g_q : ℝ) := by
        dsimp [g_q]; unfold lM_q; push_cast; ring
      have h1 := mul_le_mul_of_nonneg_left hsg_le (mul_nonneg hA_nn hg_nn)
      rw [← hg_eq] at h1
      linarith
    have hcM_mono : c_M (seg.kL : ℝ) ≤ c_M y := by
      unfold c_M
      have hF : F A_min (seg.kL : ℝ) (68 / 100) ≤ F A_min y (68 / 100) :=
        F_mono_K (by unfold A_min; norm_num) hkL_R hy.1 (by norm_num)
      have hq : q_min * (seg.kL : ℝ) ≤ q_min * y :=
        mul_le_mul_of_nonneg_left hy.1 (by unfold q_min; norm_num)
      linarith
    have hc_posR : (0 : ℝ) < (c_lo_q : ℝ) := by exact_mod_cast hc_pos
    have hc_le1R : (c_lo_q : ℝ) ≤ 1 := by exact_mod_cast hc_le1
    have hlog_cM : (L_c_q : ℝ) ≤ Real.log (c_M y) := by
      have hmL : (1 : ℝ) ^ (2 ^ 4) ≤ 1 / (c_lo_q : ℝ) := by
        rw [one_pow, one_le_div hc_posR]; exact hc_le1R
      have hmU_R : 1 / (c_lo_q : ℝ) ≤ (seg.rU_c : ℝ) ^ (2 ^ 4) := by
        have : 1 / (c_lo_q : ℝ) ≤ (seg.rU_c : ℝ) ^ 16 := by exact_mod_cast hmU
        simpa using this
      have hb := (log_bounds_of_pow_enclosure 2 4 (m := 1 / (c_lo_q : ℝ))
        (rL := 1) (rU := (seg.rU_c : ℝ)) le_rfl (by exact_mod_cast hrU1) hmL hmU_R).2
      rw [Real.log_div (by norm_num) (ne_of_gt hc_posR), Real.log_one, zero_sub] at hb
      have hcast : (L_c_q : ℝ) = -((2 ^ 4 : ℝ) *
          (atanhSeries 2 (((seg.rU_c : ℝ) - 1) / ((seg.rU_c : ℝ) + 1)) +
           atanhRemUB 2 (((seg.rU_c : ℝ) - 1) / ((seg.rU_c : ℝ) + 1)))) := by
        dsimp [L_c_q]
        have hu : (((seg.rU_c - 1) / (seg.rU_c + 1) : ℚ) : ℝ) =
            ((seg.rU_c : ℝ) - 1) / ((seg.rU_c : ℝ) + 1) := by push_cast; ring
        push_cast; rw [← hu, atanh2Q_cast]; ring
      have hmono := Real.log_le_log hc_posR (le_trans hcM_kL_ge hcM_mono)
      linarith
    have hL_ordR : (L_c_q : ℝ) ≤ (L32_q : ℝ) := by exact_mod_cast hL_ord
    have hW_gapR : (19 : ℝ) ≤ eta_max * (L_c_q : ℝ) + (1 - eta_max) * (L32_q : ℝ) +
        beta_max * (-33103 / 1000 : ℝ) - (seg.vR : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hW_gap
      unfold eta_max beta_max
      unfold eta_max_q beta_max_q TM_q at h
      push_cast at h
      exact h
    have hη_nn : 0 ≤ θ.η := le_trans (by unfold eta_min; norm_num) θ.hη.1
    have h1mη_nn : 0 ≤ 1 - θ.η := by have := θ.hη.2; unfold eta_max at this; linarith
    have h1 := mul_le_mul_of_nonneg_left hlog_cM hη_nn
    have h2 := mul_le_mul_of_nonneg_left L32_le_log h1mη_nn
    have h3 : eta_max * ((L_c_q : ℝ) - (L32_q : ℝ)) ≤ θ.η * ((L_c_q : ℝ) - (L32_q : ℝ)) :=
      mul_le_mul_of_nonpos_right θ.hη.2 (by linarith)
    have h4 : beta_max * (-33103 / 1000 : ℝ) ≤ θ.β * (-33103 / 1000 : ℝ) := by
      nlinarith [θ.hβ.2]
    unfold W_M u
    linarith [hseg_bounds.2]
  · -- 2. Cota superior Psi_sharp y - B(y) ≤ 24.7
    have hy_pos : 0 < y := lt_of_lt_of_le hkL_R hy.1
    have hPsi_mono : Psi_sharp y ≤ Psi_sharp (seg.kR : ℝ) := Psi_sharp_mono hy_pos hy.2
    have hsk_posR : (0 : ℝ) < (seg.sk_ub : ℝ) := by exact_mod_cast hsk_pos
    have hkR_posR : (0 : ℝ) < (seg.kR : ℝ) := lt_trans hkL_R hkLR_R
    have hsq_le : Real.sqrt (seg.kR : ℝ) ≤ (seg.sk_ub : ℝ) := by
      have hsq : (Real.sqrt (seg.kR : ℝ)) ^ 2 ≤ (seg.sk_ub : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hkR_posR)]; exact_mod_cast hsk_sq
      nlinarith [Real.sqrt_nonneg (seg.kR : ℝ)]
    have hPsi_ub : Psi_sharp (seg.kR : ℝ) ≤
        (4 / 10 : ℝ) * (seg.kR : ℝ) - 5 / (seg.sk_ub : ℝ) - (185 / 10 : ℝ) - (10 / 301 : ℝ) := by
      unfold Psi_sharp
      have hdiv : 5 / (seg.sk_ub : ℝ) ≤ 5 / Real.sqrt (seg.kR : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hkR_posR) hsq_le
      linarith
    have hPsi_gapR : (4 / 10 : ℝ) * (seg.kR : ℝ) - 5 / (seg.sk_ub : ℝ) -
        (185 / 10 : ℝ) - (10 / 301 : ℝ) - (seg.vL : ℝ) ≤ 247 / 10 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hPsi_gap
      push_cast at h
      exact h
    linarith [hseg_bounds.1]

/-- Verificador de cadena contigua de segmentos `BSeg` sobre `[kmin, kmax]`. -/
def bsegs_chain_ok (segs : List BSeg) (kmin kmax : ℚ) : Bool :=
  match segs with
  | [] => false
  | [seg] => (seg.kL == kmin) && (seg.kR == kmax) && seg.valid
  | seg :: rest =>
    (seg.kL == kmin) && seg.valid && bsegs_chain_ok rest seg.kR kmax

/-- Corrección de `bsegs_chain_ok`: certifica ambos márgenes uniformes sobre todo `[kmin, kmax]`. -/
theorem bsegs_chain_sound : ∀ (segs : List BSeg) (kmin kmax : ℚ),
    bsegs_chain_ok segs kmin kmax = true →
    ∀ (θ : Params) {y : ℝ}, y ∈ Icc (kmin : ℝ) (kmax : ℝ) →
      (19 : ℝ) ≤ W_M θ y - evalBSegs segs y ∧
      Psi_sharp y - evalBSegs segs y ≤ 247 / 10
  | [], _, _, h => by simp [bsegs_chain_ok] at h
  | [seg], kmin, kmax, h => by
    simp only [bsegs_chain_ok, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, hv⟩
    intro θ y hy
    simpa [evalBSegs] using seg.valid_sound hv θ hy
  | seg :: seg2 :: rest, kmin, kmax, h => by
    simp only [bsegs_chain_ok, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, hv⟩, hrest⟩
    intro θ y hy
    by_cases hle : y ≤ (seg.kR : ℝ)
    · have hy1 : y ∈ Icc (seg.kL : ℝ) (seg.kR : ℝ) := ⟨hy.1, hle⟩
      simpa [evalBSegs, hle] using seg.valid_sound hv θ hy1
    · push_neg at hle
      have hy2 : y ∈ Icc (seg.kR : ℝ) (kmax : ℝ) := ⟨le_of_lt hle, hy.2⟩
      have ih := bsegs_chain_sound (seg2 :: rest) seg.kR kmax hrest θ hy2
      have hnot : ¬ y ≤ (seg.kR : ℝ) := not_le.mpr hle
      simpa [evalBSegs, hnot] using ih

/-! ## 3. Los 22 nodos exportados de `case1_affine_gap.B_net` y certificación de $\tau_H \le 9$ -/

/-- Tabla exacta de los 21 segmentos (22 nodos) de `case1_affine_gap.B_net`
    de `cegis_certificates.json` junto con sus testigos racionales. -/
def case1_B_segs : List BSeg := [
  ⟨1/10, -28236859/500000, 29231/250000, -55565291/1000000, 167/400, 13219/10000, 171/500⟩,
  ⟨29231/250000, -55565291/1000000, 30811/250000, -1382177/25000, 2233/5000, 6121/5000, 3511/10000⟩,
  ⟨30811/250000, -1382177/25000, 137307/1000000, -27387181/500000, 571/1250, 12063/10000, 1853/5000⟩,
  ⟨137307/1000000, -27387181/500000, 41091/250000, -54007679/1000000, 4779/10000, 11777/10000, 811/2000⟩,
  ⟨41091/250000, -54007679/1000000, 176739/1000000, -2148953/40000, 1029/2000, 2857/2500, 841/2000⟩,
  ⟨176739/1000000, -2148953/40000, 193863/1000000, -53398379/1000000, 331/625, 5657/5000, 4403/10000⟩,
  ⟨193863/1000000, -53398379/1000000, 205947/1000000, -10640183/200000, 1373/2500, 5591/5000, 4539/10000⟩,
  ⟨205947/1000000, -10640183/200000, 103833/500000, -1329347/25000, 2811/5000, 11103/10000, 2279/5000⟩,
  ⟨103833/500000, -1329347/25000, 213273/1000000, -53091041/1000000, 141/250, 11093/10000, 4619/10000⟩,
  ⟨213273/1000000, -53091041/1000000, 54887/250000, -1656303/31250, 2849/5000, 553/500, 2343/5000⟩,
  ⟨54887/250000, -1656303/31250, 111553/500000, -52956517/1000000, 5761/10000, 689/625, 1181/2500⟩,
  ⟨111553/500000, -52956517/1000000, 933/4000, -2641913/50000, 1449/2500, 2201/2000, 483/1000⟩,
  ⟨933/4000, -2641913/50000, 234617/1000000, -3301439/62500, 5893/10000, 5477/5000, 1211/2500⟩,
  ⟨234617/1000000, -3301439/62500, 9427/40000, -6601403/125000, 2953/5000, 10947/10000, 971/2000⟩,
  ⟨9427/40000, -6601403/125000, 47149/200000, -52810461/1000000, 1479/2500, 5471/5000, 607/1250⟩,
  ⟨47149/200000, -52810461/1000000, 247017/1000000, -10538571/200000, 5917/10000, 5471/5000, 4971/10000⟩,
  ⟨247017/1000000, -10538571/200000, 127681/500000, -52615659/1000000, 6019/10000, 1089/1000, 2527/5000⟩,
  ⟨127681/500000, -52615659/1000000, 25931/100000, -52582147/1000000, 6093/10000, 2171/2000, 5093/10000⟩,
  ⟨25931/100000, -52582147/1000000, 13033/50000, -3285681/62500, 6127/10000, 10839/10000, 2553/5000⟩,
  ⟨13033/50000, -3285681/62500, 65697/250000, -3284683/62500, 3069/5000, 10833/10000, 5127/10000⟩,
  ⟨65697/250000, -3284683/62500, 7/25, -262179/5000, 1539/2500, 433/400, 1323/2500⟩
]

/-- Barrera `LogPWL` exacta de 22 nodos del Caso 1. -/
noncomputable def B_case1 (x : ℝ) : ℝ := evalBSegs case1_B_segs x

/-- Verificación racional completa por `norm_num` de los 21 segmentos de `B_case1`. -/
theorem case1_B_chain_ok :
    bsegs_chain_ok case1_B_segs (1 / 10) (28 / 100) = true := by
  norm_num [bsegs_chain_ok, case1_B_segs, BSeg.valid, atanh2Q, L32_q,
    q_min_q, A_min_q, eta_max_q, beta_max_q, lM_q, sM_q, TM_q, rU_32_q]

/-- Márgenes certificados en todo `M = [0.10, 0.28]` para `B_case1`, `W_M` y `Psi_sharp`. -/
theorem case1_B_margins (θ : Params) {y : ℝ} (hy : b ≤ y ∧ y ≤ h) :
    (19 : ℝ) ≤ W_M θ y - B_case1 y ∧ Psi_sharp y - B_case1 y ≤ 247 / 10 := by
  have hy' : y ∈ Icc ((1 / 10 : ℚ) : ℝ) ((28 / 100 : ℚ) : ℝ) := by
    unfold b h at hy; push_cast; exact hy
  exact bsegs_chain_sound case1_B_segs (1 / 10) (28 / 100) case1_B_chain_ok θ hy'

/-- Cierre certificado en el kernel del Caso 1 ($\tau_H \le 9$) sobre la barrera
    real de 22 nodos `B_case1`: elimina por completo las hipótesis `hm_inf` y `hM_sup`. -/
theorem case1_deadline_9_certified (θ : Params) (x L : ℕ → ℝ) (V_cont : ℝ)
    (hx : ∀ t ≤ 9, b ≤ x t ∧ x t < h)
    (hL : ∀ t < 9, 0 ≤ L t ∧ L t < 1)
    (hc : ∀ t < 9, 0 < θ.q * x t + F θ.A (x t) (L t) - x (t + 1))
    (hV : V_cont ≤ Psi_sharp (x 9))
    (hB_stay : ∀ t < 9,
      u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t) +
        θ.β * B_case1 (x (t + 1)) ≤ B_case1 (x t)) :
    (∑ t ∈ range 9, θ.β ^ t * u θ.η (θ.q * x t + F θ.A (x t) (L t) - x (t + 1)) (L t)) +
      θ.β ^ 9 * V_cont < W_M θ (x 0) :=
  cegis_staying_deadline_sound θ 9 b h 19 (247 / 10) B_case1 (W_M θ) Psi_sharp x L V_cont
    hx hL hc hV hB_stay
    (fun y hy => (case1_B_margins θ ⟨hy.1, le_of_lt hy.2⟩).1)
    (fun y hy => (case1_B_margins θ ⟨hy.1, le_of_lt hy.2⟩).2)
    (by norm_num) (by unfold beta_max; norm_num)

end MVS.CEGISCert
