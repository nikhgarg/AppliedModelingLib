import AppliedModelingLib.SocialChoice.FairDivision.Chores
import HT26EFXChores.M01M2Combination
import HT26EFXChores.M01Only
import HT26EFXChores.LowRatioRoundRobin
import HT26EFXChores.HighRatioDispatch

/-!
# Positive bi-valued normalization

The paper normalizes strictly positive ordered values `{p,q}` to `{1,q/p}`.
This module records both the normalized value fact and the exact transport of
an EFX allocation back through positive rescaling.  Degenerate constant and
binary cases are deliberately not hidden here; they require their own source
branches before the public theorem can close.

Source: `EFXadditivechores.tex`, lines 294--296.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- An EFX allocation for the positive normalization is EFX for the original
cost profile.  Feasibility is unchanged because rescaling changes only costs. -/
theorem efx_of_positive_normalization
    (Item : Type) [DecidableEq Item] (p : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hp : 0 < p)
    (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation chores)
    (hefx : EFXForChores (additiveChoreCost (rescaleChoreCost p⁻¹ cost)) allocation) :
    ∃ restored : Allocation (Fin 4) Item,
      IsAllocationOf restored chores ∧ EFXForChores (additiveChoreCost cost) restored := by
  have hrescale : rescaleChoreCost p (rescaleChoreCost p⁻¹ cost) = cost := by
    funext agent item
    simp [rescaleChoreCost, hp.ne']
  have hscaled := hefx.rescale_of_pos p (rescaleChoreCost p⁻¹ cost) allocation hp
  rw [hrescale] at hscaled
  exact ⟨allocation, halloc, hscaled⟩

/-- The source normalization data for an ordered strictly positive bi-valued
cost profile. -/
theorem positive_biValued_normalization
    (Item : Type) (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (hp : 0 < p) (hpq : p < q)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q) :
    IsOneOrRChoreCost (rescaleChoreCost p⁻¹ cost) (q / p) ∧ 1 < q / p :=
  normalize_positive_biValuedChoreCost cost p q hp hpq hvalues

/-- The fully proved normalized `b = 0` branch transports to strictly positive
ordered bi-valued costs. -/
theorem existsEfxOfPositiveBiValued_b0
    (Item : Type) [DecidableEq Item] (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hp : 0 < p) (hpq : p < q) (hratio : 2 < q / p)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q)
    (hcard : (m01ChorePool (rescaleChoreCost p⁻¹ cost) chores).card = 4 * a) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  have hnormalized := positive_biValued_normalization Item p q cost hp hpq hvalues
  obtain ⟨allocation, halloc, hefx⟩ :=
    existsEfxOfOneOrR_b0 Item (q / p) (rescaleChoreCost p⁻¹ cost) chores a hratio
      hnormalized.1 hcard
  exact efx_of_positive_normalization Item p cost chores hp allocation halloc hefx

/-- The fully proved normalized M₀₁/M₃₄-only branch transports to strictly
positive ordered bi-valued costs. -/
theorem existsEfxOfPositiveBiValued_of_m2Empty
    (Item : Type) [DecidableEq Item] (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a b : ℕ)
    (hp : 0 < p) (hpq : p < q) (hratio : 2 < q / p) (hb : b ≤ 4)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q)
    (hprefixCard : (m01ChorePool (rescaleChoreCost p⁻¹ cost) chores).card = 4 * a + b)
    (hm2Empty : m2ChorePool (rescaleChoreCost p⁻¹ cost) chores = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  have hnormalized := positive_biValued_normalization Item p q cost hp hpq hvalues
  obtain ⟨allocation, halloc, hefx⟩ :=
    existsEfxOfOneOrR_of_m2Empty Item (q / p) (rescaleChoreCost p⁻¹ cost) chores a b
      hratio hnormalized.1 hb hprefixCard hm2Empty
  exact efx_of_positive_normalization Item p cost chores hp allocation halloc hefx

/-- The positive normalization route when the normalized ratio is at most
two.  Unlike the high-ratio branch, this uses the paper's round-robin proof
directly and is independent of the M₀₁/M₂/M₃₄ decomposition. -/
theorem existsEfxOfPositiveBiValued_lowRatio
    (Item : Type) [DecidableEq Item] (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hp : 0 < p) (hpq : p < q) (hratio : q / p ≤ 2)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨hnormalized, hratioOne⟩ :=
    positive_biValued_normalization Item p q cost hp hpq hvalues
  obtain ⟨allocation, halloc, hefx⟩ := existsEfxOfOneOrR_lowRatio Item (q / p)
    (rescaleChoreCost p⁻¹ cost) chores hratioOne.le hratio hnormalized
  exact efx_of_positive_normalization Item p cost chores hp allocation halloc hefx

/-- The positive normalization route when the normalized ratio exceeds two.
The complete high-ratio modulo dispatcher supplies the normalized EFX
allocation, which is then transported back by positive rescaling. -/
theorem existsEfxOfPositiveBiValued_highRatio
    (Item : Type) [DecidableEq Item] (p q : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hp : 0 < p) (hpq : p < q) (hratio : 2 < q / p)
    (hvalues : ∀ agent item, cost agent item = p ∨ cost agent item = q) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨hnormalized, _⟩ := positive_biValued_normalization Item p q cost hp hpq hvalues
  obtain ⟨allocation, halloc, hefx⟩ := existsEfxOfOneOrR_highRatio Item (q / p)
    (rescaleChoreCost p⁻¹ cost) chores hratio hnormalized
  exact efx_of_positive_normalization Item p cost chores hp allocation halloc hefx

end HT26EFXChores
