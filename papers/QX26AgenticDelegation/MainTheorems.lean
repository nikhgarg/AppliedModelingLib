/-
Copyright (c) 2026 Alexander Quispe and Kevin Xu. All rights reserved.
Released under Apache 2.0 license.
Authors: Alexander Quispe, Kevin Xu
-/
import QX26AgenticDelegation.Model

/-!
# Quispe–Xu 2026: threshold algebra and Propositions 1–2

Proved results: Eqs. 4–8, 14–15 (closed form), 20–21, Prop. 1, Prop. 2
(activation band), and algebraic cores of Eqs. 9–10, 26 and Props. 3–5.
No `sorry`. CDF identification of Eq. 9 with \(\mathbb{E}[N^2-N^1]\) is
left to `PaperInterface` Specs (needs a probability space).
-/

open scoped BigOperators
open Finset

namespace QX26AgenticDelegation

noncomputable section

/-! ## Helper algebra -/

/-- \(\min\{a,a-x\}=a-\max\{0,x\}\). -/
lemma min_self_sub_eq_sub_max (a x : ℝ) :
    min a (a - x) = a - max 0 x := by
  rcases le_total 0 x with hx | hx
  · rw [min_eq_right (sub_le_self a hx), max_eq_right hx]
  · have hle : a ≤ a - x := by linarith
    rw [min_eq_left hle, max_eq_left hx, sub_zero]

/-- \(\max\{a-b,a-c\}=a-\min\{b,c\}\). -/
lemma max_sub_eq_sub_min (a b c : ℝ) :
    max (a - b) (a - c) = a - min b c := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, max_eq_left (sub_le_sub_left h a)]
  · rw [min_eq_right h, max_eq_right (sub_le_sub_left h a)]

/-- Variance-reduction identity used in Eq. (20):
\(1-(1-\lambda)^2=2\lambda-\lambda^2\). -/
lemma one_sub_one_sub_sq (lam : ℝ) :
    (1 : ℝ) - (1 - lam) ^ 2 = 2 * lam - lam ^ 2 := by
  ring

theorem wellFormed_iff (p : TaskParams) :
    p.WellFormed ↔
      0 ≤ p.s ∧ p.s ≤ 1 ∧ 0 < p.pi ∧ 0 < p.rho ∧ 0 < p.lambda ∧
        p.lambda ≤ 1 ∧ 0 ≤ p.a ∧ 0 ≤ p.sigmaD2 := by
  constructor
  · intro hp
    exact ⟨hp.s_nonneg, hp.s_le_one, hp.pi_pos, hp.rho_pos, hp.lambda_pos,
      hp.lambda_le_one, hp.a_nonneg, hp.sigmaD2_nonneg⟩
  · rintro ⟨hs0, hs1, hπ, hρ, hlam0, hlam1, ha, hσ⟩
    exact ⟨hs0, hs1, hπ, hρ, hlam0, hlam1, ha, hσ⟩

/-! ## Eqs. (14)–(15): CARA–Normal CE identity -/

/-- \(u(\mathrm{CE})=\mathbb{E}[u]\) as closed forms (Eqs. 14–15). -/
theorem caraExpectedUtility_eq_utility_of_CE (m sigma2 rho : ℝ) :
    caraExpectedUtility m sigma2 rho =
      caraUtility rho (certaintyEquivalent m sigma2 rho) := by
  unfold caraExpectedUtility caraUtility certaintyEquivalent
  congr 2
  ring

/-- Uniqueness of the CE as the number \(c\) with \(u(c)=\mathbb{E}[u]\),
given \(\rho\neq 0\). -/
theorem certaintyEquivalent_unique (m sigma2 rho c : ℝ) (hρ : rho ≠ 0)
    (h : caraUtility rho c = caraExpectedUtility m sigma2 rho) :
    c = certaintyEquivalent m sigma2 rho := by
  unfold caraUtility caraExpectedUtility at h
  unfold certaintyEquivalent
  have hexp :
      Real.exp (-(rho * c)) =
        Real.exp (-(rho * m) + rho ^ 2 * sigma2 / 2) :=
    neg_inj.mp h
  have hlin : -(rho * c) = -(rho * m) + rho ^ 2 * sigma2 / 2 :=
    Real.exp_injective hexp
  apply mul_left_cancel₀ hρ
  have hrhs :
      rho * (m - rho * sigma2 / 2) = rho * m - rho ^ 2 * sigma2 / 2 := by
    ring
  linarith

/-- Eq. (1) is the solo CE. -/
theorem VS_eq_certaintyEquivalent (p : TaskParams) :
    V_S p =
      certaintyEquivalent (p.omega + p.s * p.mu - p.b) (p.s ^ 2 / p.pi) p.rho := by
  unfold V_S certaintyEquivalent
  ring

/-- Eq. (2) is the copilot CE (same variance, mean shifted by \(\gamma s-r_C\)). -/
theorem VC_eq_certaintyEquivalent (p : TaskParams) :
    V_C p =
      certaintyEquivalent
        (p.omega + p.s * p.mu - p.b + p.gamma * p.s - p.rC)
        (p.s ^ 2 / p.pi) p.rho := by
  unfold V_C V_S certaintyEquivalent
  ring

/-- Eq. (3) is the delegation CE. -/
theorem VD_eq_certaintyEquivalent (p : TaskParams) :
    V_D p =
      certaintyEquivalent
        (p.omega + (1 - p.lambda) * p.s * p.mu + p.lambda * p.a * p.zA
          - p.kappa - p.rD - p.b)
        (((1 - p.lambda) ^ 2 * p.s ^ 2) / p.pi + p.sigmaD2) p.rho := by
  unfold V_D certaintyEquivalent
  ring

/-! ## Threshold characterizations (Eqs. 4–7, 20) -/

/-- Affine identity \(V^S=\omega-T^S\). -/
theorem VS_eq_omega_sub_TS (p : TaskParams) :
    V_S p = p.omega - T_S p := by
  unfold V_S T_S
  ring

/-- Eq. (4): \(V^S\ge 0\Leftrightarrow\omega\ge T^S\). -/
theorem VS_nonneg_iff_omega_ge_TS (p : TaskParams) (_hp : p.WellFormed) :
    0 ≤ V_S p ↔ T_S p ≤ p.omega := by
  rw [VS_eq_omega_sub_TS, sub_nonneg]

/-- Eq. (2) as a theorem (definitional). -/
theorem VC_eq_VS_add_augmentation (p : TaskParams) :
    V_C p = V_S p + p.gamma * p.s - p.rC :=
  rfl

/-- Affine identity \(V^C=\omega-T^C\). -/
theorem VC_eq_omega_sub_TC (p : TaskParams) :
    V_C p = p.omega - T_C p := by
  unfold V_C T_C
  rw [VS_eq_omega_sub_TS]
  ring

/-- Copilot threshold characterization: \(V^C\ge 0\Leftrightarrow\omega\ge T^C\). -/
theorem VC_nonneg_iff_omega_ge_TC (p : TaskParams) (_hp : p.WellFormed) :
    0 ≤ V_C p ↔ T_C p ≤ p.omega := by
  rw [VC_eq_omega_sub_TC, sub_nonneg]

/-- Appendix Eq. (17) expanded form of \(T^C\). -/
theorem TC_eq_expanded (p : TaskParams) :
    T_C p =
      p.b - p.s * p.mu - p.gamma * p.s + p.rC
        + (p.rho * p.s ^ 2) / (2 * p.pi) := by
  unfold T_C T_S
  ring

/-- Eq. (5), first display: \(T^1=\min\{T^S,T^C\}\). -/
theorem T1_eq_min_TS_TC (p : TaskParams) :
    T_1 p = min (T_S p) (T_C p) :=
  rfl

/-- Eq. (5), second display: \(T^1=T^S-\max\{0,\gamma s-r_C\}\). -/
theorem T1_eq_TS_sub_max_augmentation (p : TaskParams) :
    T_1 p = T_S p - max 0 (p.gamma * p.s - p.rC) := by
  unfold T_1 T_C
  exact min_self_sub_eq_sub_max _ _

/-- Affine identity \(V^D=\omega-T^D\). -/
theorem VD_eq_omega_sub_TD (p : TaskParams) :
    V_D p = p.omega - T_D p := by
  unfold V_D T_D
  ring

/-- Eq. (6): \(V^D\ge 0\Leftrightarrow\omega\ge T^D\). -/
theorem VD_nonneg_iff_omega_ge_TD (p : TaskParams) (_hp : p.WellFormed) :
    0 ≤ V_D p ↔ T_D p ≤ p.omega := by
  rw [VD_eq_omega_sub_TD, sub_nonneg]

/-- Eq. (20) / Eq. (7): \(B=T^S-T^D\). -/
theorem B_eq_TS_sub_TD (p : TaskParams) :
    B p = T_S p - T_D p := by
  unfold B T_S T_D
  rw [← one_sub_one_sub_sq p.lambda]
  ring

/-- Affine identity \(V^1=\omega-T^1\). -/
theorem V1_eq_omega_sub_T1 (p : TaskParams) :
    V1 p = p.omega - T_1 p := by
  unfold V1 T_1
  rw [VS_eq_omega_sub_TS, VC_eq_omega_sub_TC]
  exact max_sub_eq_sub_min _ _ _

/-- Affine identity \(V^2=\omega-T^2\). -/
theorem V2_eq_omega_sub_T2 (p : TaskParams) :
    V2 p = p.omega - T_2 p := by
  unfold V2 T_2
  rw [V1_eq_omega_sub_T1, VD_eq_omega_sub_TD]
  exact max_sub_eq_sub_min _ _ _

/-- \(V^1\ge 0\Leftrightarrow\omega\ge T^1\). -/
theorem V1_nonneg_iff_omega_ge_T1 (p : TaskParams) :
    0 ≤ V1 p ↔ T_1 p ≤ p.omega := by
  rw [V1_eq_omega_sub_T1, sub_nonneg]

/-- \(V^1<0\Leftrightarrow\omega<T^1\). -/
theorem V1_neg_iff_omega_lt_T1 (p : TaskParams) :
    V1 p < 0 ↔ p.omega < T_1 p := by
  rw [V1_eq_omega_sub_T1, sub_lt_zero]

/-- \(V^2\ge 0\Leftrightarrow\omega\ge T^2\). -/
theorem V2_nonneg_iff_omega_ge_T2 (p : TaskParams) :
    0 ≤ V2 p ↔ T_2 p ≤ p.omega := by
  rw [V2_eq_omega_sub_T2, sub_nonneg]

/-- Post-agent threshold never exceeds the pre-agent threshold. -/
theorem T2_le_T1 (p : TaskParams) : T_2 p ≤ T_1 p :=
  min_le_left _ _

/-! ## Eq. (21) and menus -/

theorem menu1_subset_menu2 : Menu1 ⊆ Menu2 := by
  intro m hm
  simp [Menu1, Menu2] at hm ⊢
  tauto

/-- Eq. (21): \(V^2=\max\{V^1,V^D\}\). -/
theorem V2_eq_max_V1_VD (p : TaskParams) :
    V2 p = max (V1 p) (V_D p) :=
  rfl

/-- Eq. (21): \(V^2\ge V^1\). -/
theorem V1_le_V2 (p : TaskParams) : V1 p ≤ V2 p :=
  le_max_left _ _

theorem V2_eq_max_three (p : TaskParams) :
    V2 p = max (max (V_S p) (V_C p)) (V_D p) :=
  rfl

/-! ## Activity indicators -/

lemma Z_zero_or_one (v : ℝ) : Z v = 0 ∨ Z v = 1 := by
  unfold Z
  split_ifs <;> simp

lemma Z_eq_one_iff (v : ℝ) : Z v = 1 ↔ 0 ≤ v := by
  unfold Z
  split_ifs with h
  · simp [h]
  · constructor
    · intro h01
      have : (0 : ℝ) = 1 := h01
      exact absurd this (by norm_num)
    · intro hv
      exact (h hv).elim

lemma Z_eq_zero_iff (v : ℝ) : Z v = 0 ↔ v < 0 := by
  unfold Z
  split_ifs with h
  · constructor
    · intro h10
      have : (1 : ℝ) = 0 := h10
      exact absurd this (by norm_num)
    · intro hvlt
      exact absurd h (not_le.mpr hvlt)
  · constructor
    · intro; exact lt_of_not_ge h
    · intro; rfl

lemma Z_mono {v w : ℝ} (h : v ≤ w) : Z v ≤ Z w := by
  unfold Z
  split_ifs with hv hw
  · exact le_rfl
  · exact (hw (le_trans hv h)).elim
  · exact zero_le_one
  · exact le_rfl

/-- \(Z(v)-Z(w)=1\) iff \(v\ge 0\) and \(w<0\). -/
lemma Z_sub_eq_one_iff (v w : ℝ) :
    Z v - Z w = 1 ↔ 0 ≤ v ∧ w < 0 := by
  unfold Z
  split_ifs with hv hw
  · constructor
    · intro h; linarith
    · rintro ⟨_, hlt⟩; linarith
  · constructor
    · intro; exact ⟨hv, lt_of_not_ge hw⟩
    · intro; simp
  · constructor
    · intro h; linarith
    · rintro ⟨h0, _⟩; exact (hv h0).elim
  · constructor
    · intro h; linarith
    · rintro ⟨h0, _⟩; exact (hv h0).elim

/-! ## Proposition 1 (frontier expansion) -/

/-- Proposition 1, one language: \(V^1\ge 0\Rightarrow V^2\ge 0\), hence
`LanguageActive` is monotone in the menu and \(Z^2\ge Z^1\). -/
theorem proposition1_frontierExpansion_ofTaskParams (p : TaskParams) :
    (LanguageActive (V1 p) → LanguageActive (V2 p)) ∧
      Z (V1 p) ≤ Z (V2 p) := by
  constructor
  · intro h
    exact le_trans h (V1_le_V2 p)
  · exact Z_mono (V1_le_V2 p)

/-- Proposition 1, finite language set: \(N^2\ge N^1\) as a sum of
indicators. -/
theorem Proposition1_frontierExpansion_sum {n : ℕ}
    (params : Fin n → TaskParams) :
    (∑ k : Fin n, Z (V1 (params k))) ≤ ∑ k : Fin n, Z (V2 (params k)) :=
  sum_le_sum fun k _ => (proposition1_frontierExpansion_ofTaskParams (params k)).2

/-- Proposition 1, finite language set: \(N^2\ge N^1\) as `Finset.card`. -/
theorem Proposition1_frontierExpansion_card {n : ℕ}
    (params : Fin n → TaskParams) :
    (activeSet (fun k => V1 (params k))).card ≤
      (activeSet (fun k => V2 (params k))).card := by
  classical
  refine card_le_card ?_
  intro k hk
  simp only [activeSet, mem_filter, mem_univ, true_and] at hk ⊢
  exact (proposition1_frontierExpansion_ofTaskParams (params k)).1 hk

/-! ## Proposition 2 (activation band) -/

/-- Ass. 1 ⇒ \(T^1=T^S\) on unfamiliar languages. -/
theorem T1_eq_TS_of_foothold (p : TaskParams) (h : Assumption1_foothold p) :
    T_1 p = T_S p := by
  unfold T_1 Assumption1_foothold at *
  have : T_S p ≤ T_C p := by
    unfold T_C
    linarith
  exact min_eq_left this

/-- Under Ass. 1 and \(B>0\): \(T^D<T^S\). -/
theorem TD_lt_TS_of_band (p : TaskParams) (hB : 0 < B p) :
    T_D p < T_S p := by
  have hBeq : B p = T_S p - T_D p := B_eq_TS_sub_TD p
  linarith

/-- Under Ass. 1 and \(B>0\): \(T^2=T^D\). -/
theorem T2_eq_TD_of_band (p : TaskParams)
    (hAss1 : Assumption1_foothold p) (hB : 0 < B p) :
    T_2 p = T_D p := by
  have hT1 : T_1 p = T_S p := T1_eq_TS_of_foothold p hAss1
  have hlt : T_D p < T_S p := TD_lt_TS_of_band p hB
  unfold T_2
  rw [hT1]
  exact min_eq_right (le_of_lt hlt)

/-- Proposition 2 (activation band for unfamiliar languages).

Assume Ass. 1 and \(B>0\). Then \(T^1=T^S\), \(T^2=T^D<T^S\), and the
activity increment is the half-open band (Eq. 8):
\(Z^2-Z^1=1\) iff \(T^D\le\omega<T^S\). -/
theorem proposition2_activationBand_ofTaskParams (p : TaskParams) (_hp : p.WellFormed)
    (hAss1 : Assumption1_foothold p) (hB : 0 < B p) :
    T_1 p = T_S p ∧
      T_2 p = T_D p ∧
        T_D p < T_S p ∧
          (Z (V2 p) - Z (V1 p) = 1 ↔ T_D p ≤ p.omega ∧ p.omega < T_S p) := by
  have hT1 : T_1 p = T_S p := T1_eq_TS_of_foothold p hAss1
  have hlt : T_D p < T_S p := TD_lt_TS_of_band p hB
  have hT2 : T_2 p = T_D p := T2_eq_TD_of_band p hAss1 hB
  refine ⟨hT1, hT2, hlt, ?_⟩
  rw [Z_sub_eq_one_iff, V2_nonneg_iff_omega_ge_T2, V1_neg_iff_omega_lt_T1, hT1,
    hT2]

/-- Eq. (9) inequality: for a monotone abstract CDF \(F\), the threshold-gap
mass is nonnegative. Identification with \(\mathbb{E}[N^2-N^1]\) is Spec-only. -/
theorem expected_count_expansion_nonneg {n : ℕ}
    (F : Fin n → ℝ → ℝ) (params : Fin n → TaskParams)
    (hF : ∀ k, Monotone (F k)) :
    0 ≤ ∑ k : Fin n, (F k (T_1 (params k)) - F k (T_2 (params k))) := by
  apply sum_nonneg
  intro k _
  have hle : T_2 (params k) ≤ T_1 (params k) := T2_le_T1 (params k)
  have hF' : F k (T_2 (params k)) ≤ F k (T_1 (params k)) := hF k hle
  linarith

/-! ## Algebraic cores of Propositions 3–5 (not the MVP stop) -/

/-- One-language first difference of the survival gap (Eq. 26). -/
theorem eq26_first_difference (p1 p2 : ℝ) (s : ℕ) :
    ((1 - p1) ^ (s + 2) - (1 - p2) ^ (s + 2))
        - ((1 - p1) ^ (s + 1) - (1 - p2) ^ (s + 1)) =
      p2 * (1 - p2) ^ (s + 1) - p1 * (1 - p1) ^ (s + 1) := by
  have h (p : ℝ) :
      (1 - p) ^ (s + 2) - (1 - p) ^ (s + 1) = -p * (1 - p) ^ (s + 1) := by
    have hs : s + 2 = (s + 1) + 1 := rfl
    rw [hs, pow_succ]
    ring
  calc
    ((1 - p1) ^ (s + 2) - (1 - p2) ^ (s + 2))
        - ((1 - p1) ^ (s + 1) - (1 - p2) ^ (s + 1)) =
        ((1 - p1) ^ (s + 2) - (1 - p1) ^ (s + 1))
          - ((1 - p2) ^ (s + 2) - (1 - p2) ^ (s + 1)) := by ring
    _ = (-p1 * (1 - p1) ^ (s + 1)) - (-p2 * (1 - p2) ^ (s + 1)) := by
        rw [h p1, h p2]
    _ = p2 * (1 - p2) ^ (s + 1) - p1 * (1 - p1) ^ (s + 1) := by ring

/-- If \(0\le a\le b\le 1\), then \(a^n\le b^n\) is not what we need;
we need \((1-p_2)^n\le(1-p_1)^n\). -/
lemma pow_le_pow_of_survival {p1 p2 : ℝ} {n : ℕ}
    (_h0 : 0 ≤ p1) (hle : p1 ≤ p2) (h1 : p2 ≤ 1) :
    (1 - p2) ^ n ≤ (1 - p1) ^ n := by
  have hnonneg : 0 ≤ 1 - p2 := by linarith
  have hcmp : 1 - p2 ≤ 1 - p1 := by linarith
  exact pow_le_pow_left₀ hnonneg hcmp n

/-- Eq. (10) inequality on a finite unfamiliar set, given
\(0\le p^1_k\le p^2_k\le 1\). -/
theorem cumulativeGap_nonneg {K : Type*} (U : Finset K) (p1 p2 : K → ℝ)
    (hp : ∀ k ∈ U, 0 ≤ p1 k ∧ p1 k ≤ p2 k ∧ p2 k ≤ 1) (s : ℕ) :
    0 ≤ cumulativeGap U p1 p2 s := by
  unfold cumulativeGap
  apply sum_nonneg
  intro k hk
  have hk' := hp k hk
  have hpow := pow_le_pow_of_survival hk'.1 hk'.2.1 hk'.2.2 (n := s + 1)
  linarith

/-- Closed-frontier first difference is \(p_2(1-p_2)^{s+1}\) (Eq. 26 with \(p_1=0\)). -/
theorem closed_frontier_first_difference (p2 : ℝ) (s : ℕ) :
    ((1 : ℝ) ^ (s + 2) - (1 - p2) ^ (s + 2))
        - ((1 : ℝ) ^ (s + 1) - (1 - p2) ^ (s + 1)) =
      p2 * (1 - p2) ^ (s + 1) := by
  simpa using eq26_first_difference 0 p2 s

/-- Closed-frontier second difference is \(-(p_2)^2(1-p_2)^{s+1}\). -/
theorem closed_frontier_second_difference (p2 : ℝ) (s : ℕ) :
    p2 * (1 - p2) ^ (s + 2) - p2 * (1 - p2) ^ (s + 1) =
      -(p2 ^ 2) * (1 - p2) ^ (s + 1) := by
  have hs : s + 2 = (s + 1) + 1 := rfl
  rw [hs, pow_succ]
  ring

/-- Closed-frontier concavity: second difference \(\le 0\) if \(0\le p_2\le 1\). -/
theorem closed_frontier_second_difference_nonpos {p2 : ℝ}
    (_h0 : 0 ≤ p2) (h1 : p2 ≤ 1) (s : ℕ) :
    p2 * (1 - p2) ^ (s + 2) - p2 * (1 - p2) ^ (s + 1) ≤ 0 := by
  rw [closed_frontier_second_difference]
  have hpow : 0 ≤ (1 - p2) ^ (s + 1) :=
    pow_nonneg (by linarith : 0 ≤ 1 - p2) _
  nlinarith [sq_nonneg p2, hpow]

/-- Prop. 4 counting identity: if every unfamiliar language has the same
increment \(p\), then \(\sum\delta=|U|\,p\). -/
theorem specialist_expansion_of_constant_increment {K : Type*}
    (U : Finset K) (delta : K → ℝ) (p : ℝ)
    (hp : ∀ k ∈ U, delta k = p) :
    ∑ k ∈ U, delta k = (U.card : ℝ) * p := by
  rw [sum_congr rfl fun k hk => hp k hk, sum_const, nsmul_eq_mul]

/-- Prop. 5 core: if activity expands and repository entry costs weakly
fall, every repository that was feasible remains feasible. -/
theorem proposition5_repositoryExpansion_ofMenus {Repo Lang : Type*}
    (ell : Repo → Lang) (c : Repo → Generation → ℝ)
    (hc : ∀ r, c r Generation.gen2 ≤ c r Generation.gen1)
    (Omega : Repo → ℝ) (Zact : Generation → Lang → Prop)
    (hZ : ∀ k, Zact Generation.gen1 k → Zact Generation.gen2 k) :
    ∀ r, c r Generation.gen1 ≤ Omega r ∧ Zact Generation.gen1 (ell r) →
      c r Generation.gen2 ≤ Omega r ∧ Zact Generation.gen2 (ell r) := by
  intro r ⟨hcost, hlang⟩
  exact ⟨le_trans (hc r) hcost, hZ _ hlang⟩

/-- Assumption 2 as a conjunction of the five stored inequalities. -/
theorem Assumption2_verification_ofHypotheses (H : Assumption2Hypotheses) :
    Assumption2_verification H :=
  ⟨H.h_kappa_a, H.h_kappa_s, H.h_sigma_a, H.h_sigma_s, H.h_sigma_A⟩

end

end QX26AgenticDelegation
