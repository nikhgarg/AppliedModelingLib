import HT26EFXChores.M2Orientation

/-!
# Nonexceptional M₂ residue concatenation

After M₂ gap filling makes the M₀₁-side allocation envy-free, every
nonexceptional M₂ residue combines by the unit-slack part of the source's
`M2properties` lemma and the composition lemma.  This is the standard branch
shared by the `b=1,2,3` source case analysis.

Source: `EFXadditivechores.tex`, lines 1692--1700.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- An envy-free allocation of a pool disjoint from a nonexceptional M₂ pool
extends to an EFX allocation of their union. -/
theorem existsEfxUnionOfEnvyFreeAndNonexceptionalM2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (leftChores residueChores : Finset Item) (left : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdisjoint : Disjoint leftChores residueChores)
    (hleftAlloc : IsAllocationOf left leftChores)
    (hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost) left)
    (hresidueSmall : ∀ item ∈ residueChores, IsSmallForExactlyTwo cost item)
    (hnotExceptional : ¬ IsM2Exceptional cost residueChores) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (leftChores ∪ residueChores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨right, hrightAlloc, _hrightEFX, hcertificates⟩ :=
    existsEfxOfM2_with_conditionalCertificates Item r cost residueChores hr hcost hresidueSmall
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleft hright
    exact (Finset.disjoint_left.mp hdisjoint
      (hleftAlloc.1 agent item hleft) (hrightAlloc.1 agent item hright)).elim
  have hcertificate := hcertificates hnotExceptional
  have hunit : ∀ agent other,
      additiveChoreCost cost agent (right agent) - 1 ≤
        additiveChoreCost cost agent (right other) := by
    intro agent other
    by_cases hsmall : ∃ item ∈ right agent, IsSmallChore cost agent item
    · exact hcertificate.1 agent hsmall other
    · have hlarge : ∀ item ∈ right agent, IsLargeChore cost r agent item := by
        intro item hitem
        rcases hcost agent item with hsmallItem | hlargeItem
        · exact (hsmall ⟨item, hitem, by simpa [IsSmallChore] using hsmallItem⟩).elim
        · simpa [IsLargeChore] using hlargeItem
      linarith [hcertificate.2 agent hlarge other]
  refine ⟨fun agent => left agent ∪ right agent,
    isAllocationOf_union left right leftChores residueChores hdisjoint hleftAlloc hrightAlloc, ?_⟩
  exact efxForChores_union_of_envyFree_of_unit_slack cost left right hbundlesDisjoint
    hcostLower hleftEnvyFree hunit

/-- The standard post-gap-filling branch of the source.  Once a canonical
M₀₁ prefix together with its explicitly allocated M₂ gap chores is envy-free,
any nonexceptional M₂ residue combines by the unit-slack certificate. -/
theorem existsEfxOfPrefixGapAndNonexceptionalM2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores gapChores residueChores : Finset Item)
    (prefixAllocation gap : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hgapResidue : Disjoint gapChores residueChores)
    (hgapResidueUnion : gapChores ∪ residueChores = m2Chores)
    (hprefixAllocation : IsAllocationOf prefixAllocation prefixChores)
    (hgapAllocation : IsAllocationOf gap gapChores)
    (hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent))
    (hresidueSmall : ∀ item ∈ residueChores, IsSmallForExactlyTwo cost item)
    (hnotExceptional : ¬ IsM2Exceptional cost residueChores) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro item hitem
    rw [← hgapResidueUnion]
    exact Finset.mem_union_left _ hitem
  have hresidueSubset : residueChores ⊆ m2Chores := by
    intro item hitem
    rw [← hgapResidueUnion]
    exact Finset.mem_union_right _ hitem
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hprefixAllocation hgapAllocation
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right hresidueSubset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro item hleft hresidue
    rcases Finset.mem_union.mp hleft with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue hprefix hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgap hresidue).elim
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxUnionOfEnvyFreeAndNonexceptionalM2 Item r cost
      (prefixChores ∪ gapChores) residueChores left hr hcost hleftResidue
      hleftAllocation (by simpa [left] using hleftEnvyFree)
      hresidueSmall hnotExceptional
  refine ⟨allocation, ?_, hefx⟩
  have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
    rw [← hgapResidueUnion]
    ac_rfl
  simpa [hgoods] using hallocation

end HT26EFXChores
