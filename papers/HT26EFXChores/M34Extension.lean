import HT26EFXChores.MainTheorems

/-!
# Iterated M₃₄ insertion

The paper first finds EFX allocations for the M₀₁--M₂ reduction and then
inserts every chore that is small for at least three agents.  This module
packages that finite induction around the already formalized single-item
insertion lemma.

Source: `EFXadditivechores.tex`, lines 672--676.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Repeatedly insert a finite, disjoint pool of chores each of which is small
for at least three of the four agents. -/
theorem extendEfxByM34
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (baseChores m34Chores : Finset Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdisjoint : Disjoint baseChores m34Chores)
    (hsmall : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation baseChores)
    (hefx : EFXForChores (additiveChoreCost cost) allocation) :
    ∃ extended : Allocation (Fin 4) Item,
      IsAllocationOf extended (baseChores ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) extended := by
  classical
  revert hdisjoint hsmall allocation halloc hefx
  induction m34Chores using Finset.induction_on with
  | empty =>
      intro _ _ allocation halloc hefx
      simpa using ⟨allocation, halloc, hefx⟩
  | @insert item rest hitem ih =>
      intro hdisjoint hsmall allocation halloc hefx
      have hdisjointRest : Disjoint baseChores rest :=
        hdisjoint.mono_right (Finset.subset_insert item rest)
      have hsmallRest : ∀ other ∈ rest, IsSmallForAtLeastThree cost other := by
        intro other hother
        exact hsmall other (Finset.mem_insert_of_mem hother)
      obtain ⟨partialAllocation, hpartialAlloc, hpartialEFX⟩ :=
        ih hdisjointRest hsmallRest allocation halloc hefx
      have hitemNotBaseUnionRest : item ∉ baseChores ∪ rest := by
        intro hmember
        rcases Finset.mem_union.mp hmember with hbase | hrest
        · exact (Finset.disjoint_left.mp hdisjoint hbase (Finset.mem_insert_self item rest)).elim
        · exact hitem hrest
      obtain ⟨extended, hextendedAlloc, hextendedEFX⟩ :=
        m34InsertionProof Item r cost (baseChores ∪ rest) item hr hcost hitemNotBaseUnionRest
          (hsmall item (Finset.mem_insert_self item rest)) partialAllocation hpartialAlloc hpartialEFX
      refine ⟨extended, ?_, hextendedEFX⟩
      simpa [Finset.insert_union, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using hextendedAlloc

end HT26EFXChores
