import SeshadriUgander2020IIATesting.ChoiceSystem

/-!
# Balanced perturbations of the uniform IIA null

Source: Seshadri--Ugander (2020), Section 4.  The source associates a sign
vector to an Eulerian orientation of the comparison-incidence graph.  The
`BalancedSign` interface below records exactly the two consequences used in
the statistical proof: its signs sum to zero at every choice-set vertex and
at every item vertex.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- A `{-1,1}` perturbation that is balanced at both sides of the comparison
incidence graph.  Source equation (4). -/
structure BalancedSign (F : ChoiceFrame) where
  sign : F.Observation → ℝ
  sign_eq_one_or_neg_one : ∀ o, sign o = 1 ∨ sign o = -1
  set_balance : ∀ C, ∑ x : {x : F.Item // x ∈ F.members C}, sign ⟨C, x⟩ = 0
  item_balance : ∀ x, ∑ C : {C : F.SetId // x ∈ F.members C},
    sign ⟨C, ⟨x, C.2⟩⟩ = 0

namespace BalancedSign

variable (b : BalancedSign F)

theorem abs_sign (o : F.Observation) : |b.sign o| = 1 := by
  rcases b.sign_eq_one_or_neg_one o with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

/-- Summing the set balances gives zero total perturbation mass. -/
theorem sum_sign_eq_zero : ∑ o : F.Observation, b.sign o = 0 := by
  change (∑ o : Σ C : F.SetId, {x : F.Item // x ∈ F.members C}, b.sign o) = 0
  rw [Fintype.sum_sigma]
  exact Finset.sum_eq_zero fun C _ => b.set_balance C

end BalancedSign

/-- Source Section 4's perturbed alternative
`q_{b,ε}(x,C) = (1 + ε b_(x,C)) / d`. -/
noncomputable def perturb (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) : ChoiceSystem F where
  mass o := (1 + ε * b.sign o) / (F.incidenceCount : ℝ)
  nonneg o := by
    have hdenom : 0 < (F.incidenceCount : ℝ) := by
      exact_mod_cast ChoiceFrame.incidenceCount_pos F
    have hnumerator : 0 ≤ 1 + ε * b.sign o := by
      rcases b.sign_eq_one_or_neg_one o with h | h
      · rw [h]
        linarith
      · rw [h]
        linarith
    exact div_nonneg hnumerator hdenom.le
  sum_one := by
    have hsum : ∑ o : F.Observation, (1 + ε * b.sign o) = F.incidenceCount := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ChoiceFrame.observation_card, ← Finset.mul_sum,
        b.sum_sign_eq_zero]
      ring
    rw [← Finset.sum_div, hsum]
    exact div_self (by
      exact_mod_cast Nat.ne_of_gt (ChoiceFrame.incidenceCount_pos F))

theorem perturb_mass (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (o : F.Observation) :
    (perturb b ε hε_nonneg hε_le_one).mass o =
      (1 + ε * b.sign o) / (F.incidenceCount : ℝ) := rfl

/-- The set sufficient statistics of `q_{b,ε}` agree exactly with the
uniform null (source Section 4). -/
theorem perturb_setMass (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (C : F.SetId) :
    (perturb b ε hε_nonneg hε_le_one).setMass C =
      (uniform F).setMass C := by
  rw [setMass, uniform_setMass]
  change (∑ x : {x : F.Item // x ∈ F.members C},
    (1 + ε * b.sign ⟨C, x⟩) / (F.incidenceCount : ℝ)) =
      (F.members C).card / (F.incidenceCount : ℝ)
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, b.set_balance]
  rw [Fintype.card_coe]
  ring

/-- The item sufficient statistics of `q_{b,ε}` agree exactly with the
uniform null (source Section 4). -/
theorem perturb_itemMass (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (x : F.Item) :
    (perturb b ε hε_nonneg hε_le_one).itemMass x =
      (uniform F).itemMass x := by
  unfold itemMass
  change (∑ C : {C : F.SetId // x ∈ F.members C},
    (1 + ε * b.sign ⟨C, ⟨x, C.2⟩⟩) / (F.incidenceCount : ℝ)) =
      ∑ C : {C : F.SetId // x ∈ F.members C}, 1 / (F.incidenceCount : ℝ)
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, b.item_balance]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Pointwise difference from the uniform null. -/
theorem perturb_sub_uniform (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (o : F.Observation) :
    (perturb b ε hε_nonneg hε_le_one).mass o - (uniform F).mass o =
      ε * b.sign o / (F.incidenceCount : ℝ) := by
  rw [perturb_mass, uniform_mass]
  ring

/-- Each coordinate difference has the same absolute value. -/
theorem abs_perturb_sub_uniform (b : BalancedSign F) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_le_one : ε ≤ 1) (o : F.Observation) :
    |(perturb b ε hε_nonneg hε_le_one).mass o - (uniform F).mass o| =
      ε / (F.incidenceCount : ℝ) := by
  rw [perturb_sub_uniform, abs_div, abs_mul, b.abs_sign]
  rw [abs_of_nonneg hε_nonneg]
  have hdenom : 0 < (F.incidenceCount : ℝ) := by
    exact_mod_cast ChoiceFrame.incidenceCount_pos F
  rw [abs_of_pos hdenom]
  ring

/-- Source Section 4's exact observation that every balanced perturbation is
at total-variation distance `ε / 2` from the uniform point it leaves. -/
theorem perturb_totalVariation_uniform (b : BalancedSign F) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    totalVariation (perturb b ε hε_nonneg hε_le_one) (uniform F) = ε / 2 := by
  unfold totalVariation
  rw [Finset.sum_congr rfl (fun o _ => abs_perturb_sub_uniform b ε hε_nonneg hε_le_one o),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ChoiceFrame.observation_card]
  have hincidence : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ChoiceFrame.incidenceCount_pos F)
  field_simp

end ChoiceSystem

end SeshadriUgander2020IIATesting
