import HT26EFXChores.PoolPartition
import HT26EFXChores.Canonical
import HT26EFXChores.M34Extension

/-!
# The M₀₁-only branch

When the M₂ pool is empty, the paper's canonical M₀₁ allocation is already
EFX for every remainder size.  The M₃₄ chores can then be restored by the
iterated insertion theorem.  This isolates a complete family of the final
Theorem 3 instances before the source's M₂ gap-filling case analysis.

Source: `EFXadditivechores.tex`, lines 681--700 and 732--759.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A canonical M₀₁ allocation, with any prescribed set of long agents, can
be extended across an M₃₄ pool. -/
theorem existsEfxOfM01M34
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m34Chores : Finset Item) (longAgents : Finset (Fin 4)) (a b : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdisjoint : Disjoint prefixChores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + b)
    (hlongCard : longAgents.card = b)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let quota : Fin 4 → ℕ := canonicalQuota a longAgents
  have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
    rw [show quota = canonicalQuota a longAgents by rfl, canonicalQuota_sum,
      hlongCard, hprefixCard]
  obtain ⟨prefixAllocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
  have hquotaBalanced : ∀ first second, quota first ≤ quota second + 1 := by
    intro first second
    dsimp [quota, canonicalQuota]
    by_cases hfirst : first ∈ longAgents
    · by_cases hsecond : second ∈ longAgents
      · simp [hfirst, hsecond]
      · simp [hfirst, hsecond]
    · by_cases hsecond : second ∈ longAgents
      · simp [hfirst, hsecond]
        omega
      · simp [hfirst, hsecond]
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  exact extendEfxByM34 Item r cost prefixChores m34Chores hr hcost hdisjoint hm34Small
    prefixAllocation hcanonical.isAllocationOf hprefixEFX

/-- Every normalized instance whose M₂ pool is empty admits EFX, for every
M₀₁ remainder size. -/
theorem existsEfxOfOneOrR_of_m2Empty
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a b : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r) (hb : b ≤ 4)
    (hprefixCard : (m01ChorePool cost chores).card = 4 * a + b)
    (hm2Empty : m2ChorePool cost chores = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have hbCard : b ≤ (Finset.univ : Finset (Fin 4)).card := by
    simpa using hb
  obtain ⟨longAgents, _, hlongCard⟩ :=
    (Finset.univ : Finset (Fin 4)).exists_subset_card_eq hbCard
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M34 Item r cost (m01ChorePool cost chores) (m34ChorePool cost chores)
      longAgents a b hr hcost
      (m01ChorePool_disjoint_m34ChorePool cost chores) hprefixCard hlongCard
      (m01ChorePool_small cost chores) (m34ChorePool_small cost chores)
  have hcover : m01ChorePool cost chores ∪ m34ChorePool cost chores = chores := by
    have hpartition := m01_m2_m34_union_eq cost chores
    simpa [hm2Empty] using hpartition
  refine ⟨allocation, ?_, hefx⟩
  simpa [hcover] using hallocation

end HT26EFXChores
