import HT26EFXChores.BiValuedReduction
import HT26EFXChores.ConstantBiValued
import HT26EFXChores.BinaryChores

/-!
# Complete value-level dispatch for bi-valued chores

This module separates equal values, the binary `{0,q}` degeneracy, and
distinct positive values, whose normalized ratio uses either the low- or
high-ratio dispatcher.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Every four-agent nonnegative bi-valued additive chore profile admits an
EFX allocation. -/
theorem existsEfxOfBiValuedChoreCost
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hbi : IsBiValuedChoreCost cost) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  rcases hbi with ⟨p, q, hp, hq, hvalues⟩
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · by_cases hpzero : p = 0
    · subst p
      have hqpos : 0 < q := by linarith
      exact existsEfxOfZeroOrQChoreCost Item q cost chores hqpos hvalues
    have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    by_cases hratio : q / p ≤ 2
    · exact existsEfxOfPositiveBiValued_lowRatio Item p q cost chores hppos hpq hratio hvalues
    · exact existsEfxOfPositiveBiValued_highRatio Item p q cost chores hppos hpq
        (lt_of_not_ge hratio) hvalues
  · exact existsEfxOfEqualBiValuedChoreCost Item p q cost chores hpq hp hvalues
  · have hvaluesSwap : ∀ agent item, cost agent item = q ∨ cost agent item = p := by
      intro agent item
      rcases hvalues agent item with hpvalue | hqvalue
      · exact Or.inr hpvalue
      · exact Or.inl hqvalue
    by_cases hqzero : q = 0
    · subst q
      have hppos : 0 < p := by linarith
      exact existsEfxOfZeroOrQChoreCost Item p cost chores hppos hvaluesSwap
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
    by_cases hratio : p / q ≤ 2
    · exact existsEfxOfPositiveBiValued_lowRatio Item q p cost chores hqpos hqp hratio
        hvaluesSwap
    · exact existsEfxOfPositiveBiValued_highRatio Item q p cost chores hqpos hqp
        (lt_of_not_ge hratio) hvaluesSwap

end HT26EFXChores
