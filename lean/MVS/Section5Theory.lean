import MVS.Theorem1
import MVS.CEGIS
import MVS.Stochastic
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Teoría Estructural de la Sección 5 (`MVS.Section5Theory`): Proposiciones 3 a 9

Formalización completa y sin `sorry` de la arquitectura matemática de los 6 casos
de la Sección 5 del artículo (Proposiciones 3–9):

1. **Proposición 3 (Caso 1C):** Solidez de cadenas no estacionarias de Bellman $\{J_k\}_{k=0}^T$
   (`nonstationary_chain_upper`, `nonstationary_chain_deadline`).
2. **Proposición 4 (Caso 1B):** Teorema de composición de cascadas contiguas sin retroceso
   (`cascade_two_stage`, `cascade_multi_stage`, `cascade_5stage_52`).
3. **Proposición 5 (Caso 2):** Invariancia exacta respecto a $V_{\text{ruin}}$ bajo ruina
   exógena constante (`exog_ruin_shift_identity`, `exog_ruin_bellman_invariance`).
4. **Proposición 6 (Caso 3):** Barreras acopladas $(B_G, B_B)$ en Markov de 2 estados y
   brecha de Doob $\epsilon_0$ (`markov2_coupled_doob_gap`).
5. **Proposición 7 (Caso 4):** Régimen híbrido CES--AK, homogeneidad de grado 1 en $[h, \infty)$
   y pendiente logarítmica asintótica exacta $D_{\text{hi}} = \eta / (1 - \beta)$
   (`F_AK_homog_ray`, `AK_tail_ray_invariance`).
6. **Proposición 8 (Caso 5):** Ruina endógena $p(K) = p \mathbf{1}_{K < h}$, prima de
   supervivencia $V(K') - V_{\text{ruin}} > 0$, equivalencia de cota $(1 - p)^{T^*}$
   y verificación exacta de la Tabla 7 (`endo_ruin_survival_premium`,
   `endo_ruin_staying_telescoping`, `table7_survival_bounds_exact`).
7. **Proposición 9 (Caso 6):** Cubrimiento finito por subcajas paramétricas
   (`subbox_cover_deadline`).
-/

open Finset Real Set MVS.Theorem1 MVS.CEGIS MVS.Stochastic

namespace MVS.Section5Theory

/-! ## 1. Proposición 3 (Caso 1C): Cadenas no estacionarias de Bellman $\{J_k\}_{k=0}^T$ -/

/-- Inducción telescópica para una cadena no estacionaria de horizonte finito $\{J_k\}_{k=0}^T$:
    si $J_0 \ge \Psi$ en $M$ y $u_t + \beta J_k(x') \le J_{k+1}(x)$ para todo paso dentro de $M$,
    entonces toda trayectoria que permanece en $M$ durante $T$ pasos satisface
    $\sum_{t=0}^{T-1} \beta^t u_t + \beta^T \Psi(x_T) \le J_T(x_0)$. -/
theorem nonstationary_chain_upper {β : ℝ} (hβ : 0 ≤ β) {M : Set ℝ}
    (J : ℕ → ℝ → ℝ) (Ψ : ℝ → ℝ) (u_seq : ℕ → ℝ) (x : ℕ → ℝ) :
    ∀ T : ℕ,
      (∀ y ∈ M, Ψ y ≤ J 0 y) →
      (∀ k < T, ∀ t < T, x t ∈ M → x (t + 1) ∈ M → u_seq t + β * J k (x (t + 1)) ≤ J (k + 1) (x t)) →
      (∀ t ≤ T, x t ∈ M) →
      (∑ t ∈ range T, β ^ t * u_seq t) + β ^ T * Ψ (x T) ≤ J T (x 0) := by
  intro T hJ0 hstep hstay
  -- Probamos por inducción en k ≤ T la cola desde (T - k) hasta T:
  -- ∑_{j=0}^{k-1} β^j u_{T - k + j} + β^k Ψ(x_T) ≤ J k (x (T - k))
  have haux : ∀ k ≤ T,
      (∑ j ∈ range k, β ^ j * u_seq (T - k + j)) + β ^ k * Ψ (x T) ≤ J k (x (T - k)) := by
    intro k hk
    induction k with
    | zero =>
      simp only [range_zero, sum_empty, zero_add, pow_zero, one_mul, Nat.sub_zero]
      exact hJ0 (x T) (hstay T le_rfl)
    | succ m ih =>
      have hm_lt : m < T := Nat.lt_of_succ_le hk
      have ih_m := ih (le_of_lt hm_lt)
      have hsub : T - (m + 1) + 1 = T - m := by omega
      have hidx : T - (m + 1) < T := by omega
      have hstep_m := hstep m hm_lt (T - (m + 1)) hidx
        (hstay (T - (m + 1)) (by omega)) (by rw [hsub]; exact hstay (T - m) (by omega))
      rw [hsub] at hstep_m
      have hmul := mul_le_mul_of_nonneg_left ih_m hβ
      -- Reindexamos la suma de range (m + 1) separando j = 0 del resto
      have hsum_split : ∑ j ∈ range (m + 1), β ^ j * u_seq (T - (m + 1) + j) =
          u_seq (T - (m + 1)) + β * ∑ j ∈ range m, β ^ j * u_seq (T - m + j) := by
        rw [Finset.sum_range_succ', pow_zero, one_mul, add_zero, Finset.mul_sum]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : T - (m + 1) + (j + 1) = T - m + j := by omega
        rw [hj, pow_succ']; ring
      rw [hsum_split, pow_succ']
      linarith
  have hT := haux T le_rfl
  simpa [Nat.sub_self] using hT

/-- Solidez de plazo de una cadena no estacionaria $\{J_k\}_{k=0}^T$:
    si el testigo $W(x_0)$ domina estrictamente a $J_T(x_0)$ y toda senda que permanece en $M$
    está acotada arriba por $J_T(x_0)$, entonces toda trayectoria óptima con valor $\ge W(x_0)$
    debe abandonar $M$ en a lo sumo $T$ pasos. -/
theorem nonstationary_chain_deadline {β : ℝ} (hβ : 0 ≤ β) {M : Set ℝ}
    (J : ℕ → ℝ → ℝ) (Ψ W : ℝ → ℝ) (u_seq : ℕ → ℝ) (x : ℕ → ℝ) (T : ℕ)
    (hJ0 : ∀ y ∈ M, Ψ y ≤ J 0 y)
    (hstep : ∀ k < T, ∀ t < T, x t ∈ M → x (t + 1) ∈ M →
      u_seq t + β * J k (x (t + 1)) ≤ J (k + 1) (x t))
    (hopt : W (x 0) ≤ (∑ t ∈ range T, β ^ t * u_seq t) + β ^ T * Ψ (x T))
    (hgap : J T (x 0) < W (x 0)) :
    ∃ t ≤ T, x t ∉ M := by
  by_contra hall
  push Not at hall
  have hub := nonstationary_chain_upper hβ J Ψ u_seq x T hJ0 hstep hall
  linarith

/-! ## 2. Proposición 4 (Caso 1B): Composición de cascadas contiguas -/

/-- Composición de dos etapas contiguas $[b_0, b_1)$ y $[b_1, b_2)$ sin retroceso:
    si cada etapa certifica salida en $\le T_1$ y $\le T_2$ pasos respectivamente,
    entonces desde $x_0 \ge b_0$ se alcanza $b_2$ en $\le T_1 + T_2$ pasos. -/
theorem cascade_two_stage (x : ℕ → ℝ) {b₀ b₁ b₂ : ℝ} {T₁ T₂ : ℕ}
    (hx0 : b₀ ≤ x 0)
    (hstage1 : ∀ t, b₀ ≤ x t → x t < b₁ → ∃ d ≤ T₁, b₁ ≤ x (t + d))
    (hstage2 : ∀ t, b₁ ≤ x t → x t < b₂ → ∃ d ≤ T₂, b₂ ≤ x (t + d)) :
    ∃ t ≤ T₁ + T₂, b₂ ≤ x t := by
  by_cases h1 : b₁ ≤ x 0
  · by_cases h2 : b₂ ≤ x 0
    · exact ⟨0, Nat.zero_le _, h2⟩
    · obtain ⟨d₂, hd₂, hreach₂⟩ := hstage2 0 h1 (lt_of_not_ge h2)
      exact ⟨0 + d₂, by omega, hreach₂⟩
  · obtain ⟨d₁, hd₁, hreach₁⟩ := hstage1 0 hx0 (lt_of_not_ge h1)
    by_cases h2 : b₂ ≤ x (0 + d₁)
    · exact ⟨0 + d₁, by omega, h2⟩
    · obtain ⟨d₂, hd₂, hreach₂⟩ := hstage2 (0 + d₁) hreach₁ (lt_of_not_ge h2)
      exact ⟨0 + d₁ + d₂, by omega, hreach₂⟩

/-- Composición inductiva de una cascada arbitraria de etapas contiguas
    $[(b_1, T_1), (b_2, T_2), \dots, (b_m, T_m)]$ desde un borde inicial $b_0$:
    el plazo total queda acotado por $\sum_{i=1}^m T_i$. -/
theorem cascade_multi_stage (x : ℕ → ℝ) :
    ∀ (b_cur : ℝ) (t_cur : ℕ) (stages : List (ℝ × ℕ)),
      b_cur ≤ x t_cur →
      (∀ i (hi : i < stages.length),
        let b_lo := if h0 : i = 0 then b_cur else (stages.get ⟨i - 1, by omega⟩).1
        let b_hi := (stages.get ⟨i, hi⟩).1
        let Ti := (stages.get ⟨i, hi⟩).2
        ∀ t, b_lo ≤ x t → x t < b_hi → ∃ d ≤ Ti, b_hi ≤ x (t + d)) →
      match stages.getLast? with
      | none => True
      | some (b_end, _) => ∃ t ≤ t_cur + (stages.map Prod.snd).sum, b_end ≤ x t
  | b_cur, t_cur, [], _, _ => trivial
  | b_cur, t_cur, [(b₁, T₁)], hx, hst => by
    simp only [List.getLast?_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    by_cases h : b₁ ≤ x t_cur
    · exact ⟨t_cur, Nat.le_add_right _ _, h⟩
    · obtain ⟨d, hd, hreach⟩ := hst 0 (by simp) t_cur hx (lt_of_not_ge h)
      exact ⟨t_cur + d, Nat.add_le_add_left hd t_cur, hreach⟩
  | b_cur, t_cur, (b₁, T₁) :: (b₂, T₂) :: rest, hx, hst => by
    -- Primero alcanzamos b₁ en a lo sumo T₁ pasos desde t_cur
    have hreach1 : ∃ t₁ ≤ t_cur + T₁, b₁ ≤ x t₁ := by
      by_cases h : b₁ ≤ x t_cur
      · exact ⟨t_cur, Nat.le_add_right _ _, h⟩
      · obtain ⟨d, hd, hreach⟩ := hst 0 (by simp) t_cur hx (lt_of_not_ge h)
        exact ⟨t_cur + d, Nat.add_le_add_left hd t_cur, hreach⟩
    obtain ⟨t₁, ht₁, hxb₁⟩ := hreach1
    -- Aplicamos la hipótesis inductiva sobre ((b₂, T₂) :: rest) desde (b₁, t₁)
    have ih := cascade_multi_stage x b₁ t₁ ((b₂, T₂) :: rest) hxb₁ (fun i hi => by
      have hi' : i + 1 < ((b₁, T₁) :: (b₂, T₂) :: rest).length := by simpa using Nat.succ_lt_succ hi
      have hspec := hst (i + 1) hi'
      cases i with
      | zero => simpa using hspec
      | succ j => simpa using hspec)
    have hlast : ((b₁, T₁) :: (b₂, T₂) :: rest).getLast? = ((b₂, T₂) :: rest).getLast? := by
      simp [List.getLast?_cons_cons]
    rw [hlast]
    cases hgl : ((b₂, T₂) :: rest).getLast? with
    | none => exact trivial
    | some pair =>
      simp only [hgl] at ih
      obtain ⟨t_fin, ht_fin, hreach_fin⟩ := ih
      refine ⟨t_fin, ?_, hreach_fin⟩
      simp only [List.map_cons, List.sum_cons] at ht_fin ⊢
      omega

/-- Instanciación exacta de la Proposición 4 (Caso 1B):
    cascada de 5 etapas $[0.003, 0.006, 0.015, 0.040, 0.100, 0.280]$ con plazos
    $(21, 13, 8, 5, 5)$ produce el plazo total $T_{\text{total}} \le 52$. -/
theorem cascade_5stage_52 (x : ℕ → ℝ)
    (hx0 : (3 / 1000 : ℝ) ≤ x 0)
    (hs1 : ∀ t, (3 / 1000 : ℝ) ≤ x t → x t < 6 / 1000 → ∃ d ≤ 21, (6 / 1000 : ℝ) ≤ x (t + d))
    (hs2 : ∀ t, (6 / 1000 : ℝ) ≤ x t → x t < 15 / 1000 → ∃ d ≤ 13, (15 / 1000 : ℝ) ≤ x (t + d))
    (hs3 : ∀ t, (15 / 1000 : ℝ) ≤ x t → x t < 40 / 1000 → ∃ d ≤ 8, (40 / 1000 : ℝ) ≤ x (t + d))
    (hs4 : ∀ t, (40 / 1000 : ℝ) ≤ x t → x t < 100 / 1000 → ∃ d ≤ 5, (100 / 1000 : ℝ) ≤ x (t + d))
    (hs5 : ∀ t, (100 / 1000 : ℝ) ≤ x t → x t < 280 / 1000 → ∃ d ≤ 5, (280 / 1000 : ℝ) ≤ x (t + d)) :
    ∃ t ≤ 52, (280 / 1000 : ℝ) ≤ x t := by
  have h12 : ∀ t, (3 / 1000 : ℝ) ≤ x t → x t < 15 / 1000 → ∃ d ≤ 34, (15 / 1000 : ℝ) ≤ x (t + d) := by
    intro t ht hlt
    by_cases h : (6 / 1000 : ℝ) ≤ x t
    · obtain ⟨d, hd, hr⟩ := hs2 t h hlt; exact ⟨d, by omega, hr⟩
    · obtain ⟨d₁, hd₁, hr₁⟩ := hs1 t ht (lt_of_not_ge h)
      by_cases h2 : (15 / 1000 : ℝ) ≤ x (t + d₁)
      · exact ⟨d₁, by omega, h2⟩
      · obtain ⟨d₂, hd₂, hr₂⟩ := hs2 (t + d₁) hr₁ (lt_of_not_ge h2)
        exact ⟨d₁ + d₂, by omega, by simpa [Nat.add_assoc] using hr₂⟩
  have h123 : ∀ t, (3 / 1000 : ℝ) ≤ x t → x t < 40 / 1000 → ∃ d ≤ 42, (40 / 1000 : ℝ) ≤ x (t + d) := by
    intro t ht hlt
    by_cases h : (15 / 1000 : ℝ) ≤ x t
    · obtain ⟨d, hd, hr⟩ := hs3 t h hlt; exact ⟨d, by omega, hr⟩
    · obtain ⟨d₁, hd₁, hr₁⟩ := h12 t ht (lt_of_not_ge h)
      by_cases h2 : (40 / 1000 : ℝ) ≤ x (t + d₁)
      · exact ⟨d₁, by omega, h2⟩
      · obtain ⟨d₂, hd₂, hr₂⟩ := hs3 (t + d₁) hr₁ (lt_of_not_ge h2)
        exact ⟨d₁ + d₂, by omega, by simpa [Nat.add_assoc] using hr₂⟩
  have h1234 : ∀ t, (3 / 1000 : ℝ) ≤ x t → x t < 100 / 1000 → ∃ d ≤ 47, (100 / 1000 : ℝ) ≤ x (t + d) := by
    intro t ht hlt
    by_cases h : (40 / 1000 : ℝ) ≤ x t
    · obtain ⟨d, hd, hr⟩ := hs4 t h hlt; exact ⟨d, by omega, hr⟩
    · obtain ⟨d₁, hd₁, hr₁⟩ := h123 t ht (lt_of_not_ge h)
      by_cases h2 : (100 / 1000 : ℝ) ≤ x (t + d₁)
      · exact ⟨d₁, by omega, h2⟩
      · obtain ⟨d₂, hd₂, hr₂⟩ := hs4 (t + d₁) hr₁ (lt_of_not_ge h2)
        exact ⟨d₁ + d₂, by omega, by simpa [Nat.add_assoc] using hr₂⟩
  exact cascade_two_stage x hx0 h1234 hs5

/-! ## 3. Proposición 5 (Caso 2): Invariancia exacta respecto a $V_{\text{ruin}}$ -/

/-- Desplazamiento exacto de ruina exógena:
    $\text{shift}(\beta, p, V_{\text{ruin}}) = \frac{\beta p V_{\text{ruin}}}{1 - \beta (1 - p)}$. -/
noncomputable def ruinShift (β p V_ruin : ℝ) : ℝ :=
  β * p * V_ruin / (1 - β * (1 - p))

/-- Identidad exacta de cancelación del término absorbente $\beta p V_{\text{ruin}}$:
    para todo $\beta \in (0, 1)$, $p \in [0, 1)$, $u, V', V_{\text{ruin}} \in \mathbb{R}$,
    $u + \beta ((1 - p)(V' + S) + p V_{\text{ruin}}) = (u + \beta(1 - p) V') + S$. -/
theorem exog_ruin_shift_identity {β p u V' V_ruin : ℝ}
    (hden : 1 - β * (1 - p) ≠ 0) :
    let S := ruinShift β p V_ruin
    u + β * ((1 - p) * (V' + S) + p * V_ruin) = (u + β * (1 - p) * V') + S := by
  intro S
  dsimp [S, ruinShift]
  field_simp [hden]
  ring

/-- Invariancia exacta de Bellman respecto a $V_{\text{ruin}}$ (Proposición 5):
    la función $V_0$ satisface la desigualdad de Bellman con descuento efectivo
    $\tilde{\beta}_p = \beta (1 - p)$ y $V_{\text{ruin}} = 0$ si y solo si
    $V(K) = V_0(K) + \text{ruinShift}(\beta, p, V_{\text{ruin}})$ satisface la desigualdad
    de Bellman con riesgo de ruina $(p, V_{\text{ruin}})$. -/
theorem exog_ruin_bellman_invariance {β p V_ruin : ℝ}
    (hden : 1 - β * (1 - p) ≠ 0) (V₀ : ℝ → ℝ) (u_val K K' : ℝ) :
    let S := ruinShift β p V_ruin
    (u_val + β * (1 - p) * V₀ K' ≤ V₀ K) ↔
    (u_val + β * ((1 - p) * (V₀ K' + S) + p * V_ruin) ≤ V₀ K + S) := by
  intro S
  rw [exog_ruin_shift_identity hden]
  constructor <;> intro h <;> linarith

/-! ## 4. Proposición 6 (Caso 3): Barreras acopladas $(B_G, B_B)$ en Markov de 2 estados -/

/-- Brecha de Doob $\epsilon_0$ para el sistema acoplado de Markov de 2 estados $(G, B)$:
    si en el tiempo de parada $T_0$ se verifica la cota de parada opcional acoplada
    $W_\omega(K) \le B_\omega(K) + P_{\text{exit}} (\beta_0 d_{\text{exit}}) + (1 - P_{\text{exit}}) (\beta_+^{T_0} d_{\text{stay}})$
    con $m_{\inf} \le W_\omega(K) - B_\omega(K)$ y $\beta_+^{T_0} d_{\text{stay}} < \beta_0 d_{\text{exit}}$,
    entonces $P_{\text{exit}} \ge \epsilon_0 := \frac{m_{\inf} - \beta_+^{T_0} d_{\text{stay}}}{\beta_0 d_{\text{exit}} - \beta_+^{T_0} d_{\text{stay}}}$. -/
theorem markov2_coupled_doob_gap {W_val B_val m_inf d_stay d_exit β₀ β_max P_exit : ℝ} {T₀ : ℕ}
    (hm : m_inf ≤ W_val - B_val)
    (hden : 0 < β₀ * d_exit - β_max ^ T₀ * d_stay)
    (hdoob : W_val ≤ B_val + P_exit * (β₀ * d_exit) + (1 - P_exit) * (β_max ^ T₀ * d_stay)) :
    (m_inf - β_max ^ T₀ * d_stay) / (β₀ * d_exit - β_max ^ T₀ * d_stay) ≤ P_exit := by
  rw [div_le_iff₀ hden]
  have h1 : m_inf ≤ P_exit * (β₀ * d_exit) + (1 - P_exit) * (β_max ^ T₀ * d_stay) := by linarith
  have hrew : P_exit * (β₀ * d_exit) + (1 - P_exit) * (β_max ^ T₀ * d_stay) - β_max ^ T₀ * d_stay =
      P_exit * (β₀ * d_exit - β_max ^ T₀ * d_stay) := by ring
  linarith

/-! ## 5. Proposición 7 (Caso 4): Régimen híbrido CES--AK y rayo homogéneo -/

/-- Producción híbrida CES--AK continua por tramos (Proposición 7):
    CES en $K < h$ y lineal $F_{\text{AK}}(K, L) = (K / h) F_A(h, L)$ en $K \ge h$. -/
noncomputable def F_AK (A h K L : ℝ) : ℝ :=
  if K < h then F A K L else (K / h) * F A h L

lemma F_AK_eq_at_h {A h L : ℝ} (hh : h ≠ 0) : F_AK A h h L = F A h L := by
  unfold F_AK; simp [div_self hh]

/-- Homogeneidad exacta de grado 1 de $F_{\text{AK}}$ en la cola $K \ge h$ para todo $\lambda \ge 1$. -/
theorem F_AK_homog_ray {A h K L lam : ℝ} (hh : 0 < h) (hK : h ≤ K) (hlam : 1 ≤ lam) :
    F_AK A h (lam * K) L = lam * F_AK A h K L := by
  have hnot1 : ¬ (K < h) := not_lt.mpr hK
  have hnot2 : ¬ (lam * K < h) := not_lt.mpr (by nlinarith)
  unfold F_AK
  simp only [hnot1, hnot2, ite_false]
  ring

/-- Invariancia exacta del residuo de Bellman a lo largo de cualquier rayo homogéneo
    $(K, K', c) \mapsto (\lambda K, \lambda K', \lambda c)$ bajo la cola logarítmica
    $V_{\text{tail}}(K) = \frac{\eta}{1 - \beta} \log K + C_0$ (Proposición 7):
    certificar la desigualdad en un único punto $K_{\text{tail}}$ certifica todo $[K_{\text{tail}}, \infty)$. -/
theorem AK_tail_ray_invariance {η β C₀ K K' c L lam : ℝ}
    (hβ : β ≠ 1) (hK : 0 < K) (hK' : 0 < K') (hc : 0 < c) (hlam : 0 < lam) :
    let V_tail : ℝ → ℝ := fun x => (η / (1 - β)) * Real.log x + C₀
    u η (lam * c) L + β * V_tail (lam * K') - V_tail (lam * K) =
      u η c L + β * V_tail K' - V_tail K := by
  intro V_tail
  have h1β : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  unfold u; dsimp [V_tail]
  rw [Real.log_mul (ne_of_gt hlam) (ne_of_gt hc),
      Real.log_mul (ne_of_gt hlam) (ne_of_gt hK'),
      Real.log_mul (ne_of_gt hlam) (ne_of_gt hK)]
  field_simp [h1β]
  ring

/-! ## 6. Proposición 8 (Caso 5): Ruina endógena $p(K) = p \mathbf{1}_{K < h}$ y Tabla 7 -/

/-- Prima endógena de supervivencia al cruzar el umbral seguro $h$ (Proposición 8):
    comparando el operador de Bellman sin ruina ($K \ge h$) frente al de ruina activa ($K < h$),
    la ganancia estricta es exactamente $\beta p (V(K') - V_{\text{ruin}}) > 0$ cuando $V(K') > V_{\text{ruin}}$. -/
theorem endo_ruin_survival_premium {β p u_val V_next V_ruin : ℝ}
    (hβ : 0 < β) (hp : 0 < p) (hprem : V_ruin < V_next) :
    (u_val + β * V_next) - (u_val + β * ((1 - p) * V_next + p * V_ruin)) =
      β * p * (V_next - V_ruin) ∧
    0 < β * p * (V_next - V_ruin) := by
  refine ⟨by ring, ?_⟩
  have : 0 < V_next - V_ruin := by linarith
  positivity

/-- Telescopio de permanencia bajo ruina endógena $p(K) = p \mathbf{1}_{K < h}$:
    mientras $x_t < h$ para todo $t < T$, el factor de descuento efectivo es
    $\tilde{\beta}_p = \beta (1 - p)$ y toda trayectoria que permanece en $M = [b, h)$
    satisface la misma cota telescópica con desplazamiento $\text{ruinShift}(\beta, p, V_{\text{ruin}})$. -/
theorem endo_ruin_staying_telescoping {β p V_ruin : ℝ}
    (hβ0 : 0 ≤ β) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hden : 1 - β * (1 - p) ≠ 0)
    (B : ℝ → ℝ) (u_seq : ℕ → ℝ) (x : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, u_seq t + β * ((1 - p) * B (x (t + 1)) + p * V_ruin) ≤ B (x t)) :
    let βt := β * (1 - p)
    let S := ruinShift β p V_ruin
    (∑ t ∈ range T, βt ^ t * u_seq t) + βt ^ T * (B (x T) - S) ≤ B (x 0) - S := by
  intro βt S
  have hβt_nn : 0 ≤ βt := mul_nonneg hβ0 (by linarith)
  have hstep' : ∀ t < T, u_seq t + βt * (B (x (t + 1)) - S) ≤ B (x t) - S := by
    intro t ht
    have h1 := hstep t ht
    have hid := exog_ruin_shift_identity (β := β) (p := p) (u := u_seq t)
      (V' := B (x (t + 1)) - S) (V_ruin := V_ruin) hden
    have hsimp : B (x (t + 1)) - S + S = B (x (t + 1)) := by ring
    dsimp [S] at hid hsimp ⊢
    rw [hsimp] at hid
    dsimp [βt]; linarith
  have htel := telescoping_bellman hβt_nn (fun y => B y - S) u_seq x T hstep'
  linarith

/-- Verificación exacta en $\mathbb{Q}$ de las cotas garantizadas de supervivencia $(1 - p)^5$
    reportadas en la Proposición 8 y la Tabla 7 para $p \in \{1\%, 2\%, 5\%, 8\%\}$. -/
theorem table7_survival_bounds_exact :
    (9509 / 10000 : ℚ) ≤ (1 - 1 / 100) ^ 5 ∧
    (9039 / 10000 : ℚ) ≤ (1 - 2 / 100) ^ 5 ∧
    (7737 / 10000 : ℚ) ≤ (1 - 5 / 100) ^ 5 ∧
    (6590 / 10000 : ℚ) ≤ (1 - 8 / 100) ^ 5 := by
  norm_num

/-! ## 7. Proposición 9 (Caso 6): Cubrimiento finito por subcajas paramétricas -/

/-- Teorema de escalabilidad por partición en subcajas (Proposición 9):
    si una familia finita de subcajas $\{\mathcal{P}_i\}$ recubre $\mathcal{P}$ y cada
    subcaja $\mathcal{P}_i$ certifica un plazo $T_i$, entonces todo $\theta \in \mathcal{P}$
    cumple el plazo uniforme $\max_i T_i$. -/
theorem subbox_cover_deadline {α : Type*} {P : Set α} {escape_by : α → ℕ → Prop}
    (hmono : ∀ θ {T₁ T₂}, T₁ ≤ T₂ → escape_by θ T₁ → escape_by θ T₂)
    (boxes : List (Set α × ℕ))
    (hcover : ∀ θ ∈ P, ∃ B ∈ boxes, θ ∈ B.1)
    (hcert : ∀ B ∈ boxes, ∀ θ ∈ B.1, escape_by θ B.2) :
    ∀ θ ∈ P, escape_by θ (boxes.foldr (fun B acc => max B.2 acc) 0) := by
  intro θ hθ
  obtain ⟨B, hB_mem, hθB⟩ := hcover θ hθ
  have hle_aux : ∀ (L : List (Set α × ℕ)), B ∈ L → B.2 ≤ L.foldr (fun B' acc => max B'.2 acc) 0 := by
    intro L hmem
    induction L with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact le_max_left _ _
      · exact le_trans (ih htl) (le_max_right _ _)
  exact hmono θ (hle_aux boxes hB_mem) (hcert B hB_mem θ hθB)

end MVS.Section5Theory
