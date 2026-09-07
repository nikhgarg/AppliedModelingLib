import HT26EFXChores.B2TightExceptionalAllocation

/-!
# The zero-prefix corner of source Case B.3.1

The final `a = 0` branch of the tight exceptional configuration is a finite
direct allocation.  This module first records its reusable EFX verification
kernel: every owned chore is small, and the cardinality left after removing
one chore is bounded by every comparison bundle.

Source: `EFXadditivechores.tex`, lines 2665--2676.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- An allocation whose own bundles consist entirely of unit-cost chores is
EFX once every comparison bundle meets the corresponding post-removal
cardinality lower bound.  This is the finite numerical verification used in
the `a=0` tight corner. -/
theorem efxForChores_of_unit_own_bundles_and_card_lower_bounds
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (allocation : Allocation (Fin 4) Item)
    (halloc : IsAllocationOf allocation chores)
    (hownSmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item)
    (hbound : ∀ own comparison,
      ((allocation own).card - 1 : ℕ) ≤ additiveChoreCost cost own (allocation comparison)) :
    EFXForChores (additiveChoreCost cost) allocation := by
  intro own comparison
  by_cases hempty : allocation own = ∅
  · exact Or.inl hempty
  · right
    intro item hitem
    have herase : additiveChoreCost cost own (allocation own \ {item}) =
        ((allocation own).card - 1 : ℕ) := by
      rw [additiveChoreCost_erase_eq_card_sub_one_nsmul_of_constant cost own
        (allocation own) item 1 hitem]
      · simp [nsmul_eq_mul]
      · intro chore hchore
        simpa [IsSmallChore] using hownSmall own chore hchore
    rw [herase]
    exact hbound own comparison

/-- The `2:1` allocation of each three-chore complementary type in the
source's zero-prefix corner.  The two selected heads receive the one-chore
bundles, while the remaining two chores of each type form the paired bundles.
-/
theorem existsB2ZeroCornerSuffixAllocation
    (Item : Type) [DecidableEq Item]
    (m2Chores firstType secondType : Finset Item)
    (hcover : m2Chores = firstType ∪ secondType)
    (htypesDisjoint : Disjoint firstType secondType)
    (hfirstCard : firstType.card = 3) (hsecondCard : secondType.card = 3) :
    ∃ firstHead ∈ firstType, ∃ secondHead ∈ secondType,
      ∃ suffix : Allocation (Fin 4) Item,
        IsAllocationOf suffix m2Chores ∧
        suffix 0 = firstType.erase firstHead ∧ suffix 1 = {firstHead} ∧
        suffix 2 = secondType.erase secondHead ∧ suffix 3 = {secondHead} ∧
        (suffix 0).card = 2 ∧ (suffix 1).card = 1 ∧
        (suffix 2).card = 2 ∧ (suffix 3).card = 1 := by
  have hfirstNonempty : firstType.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨firstHead, hfirstHead⟩ := hfirstNonempty
  have hsecondNonempty : secondType.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨secondHead, hsecondHead⟩ := hsecondNonempty
  let firstRest : Finset Item := firstType.erase firstHead
  let secondRest : Finset Item := secondType.erase secondHead
  let firstRestAllocation : Allocation (Fin 4) Item :=
    allocateAllTo (Fin 4) Item 0 firstRest
  let firstHeadAllocation : Allocation (Fin 4) Item :=
    allocateAllTo (Fin 4) Item 1 {firstHead}
  let secondRestAllocation : Allocation (Fin 4) Item :=
    allocateAllTo (Fin 4) Item 2 secondRest
  let secondHeadAllocation : Allocation (Fin 4) Item :=
    allocateAllTo (Fin 4) Item 3 {secondHead}
  let firstAllocation : Allocation (Fin 4) Item := fun agent =>
    firstRestAllocation agent ∪ firstHeadAllocation agent
  let secondAllocation : Allocation (Fin 4) Item := fun agent =>
    secondRestAllocation agent ∪ secondHeadAllocation agent
  let suffix : Allocation (Fin 4) Item := fun agent =>
    firstAllocation agent ∪ secondAllocation agent
  have hfirstPartsDisjoint : Disjoint firstRest ({firstHead} : Finset Item) := by
    rw [Finset.disjoint_singleton_right]
    simpa [firstRest] using Finset.not_mem_erase firstHead firstType
  have hsecondPartsDisjoint : Disjoint secondRest ({secondHead} : Finset Item) := by
    rw [Finset.disjoint_singleton_right]
    simpa [secondRest] using Finset.not_mem_erase secondHead secondType
  have hfirstRestAllocation : IsAllocationOf firstRestAllocation firstRest :=
    isAllocationOf_allocateAllTo 0 firstRest
  have hfirstHeadAllocation : IsAllocationOf firstHeadAllocation {firstHead} :=
    isAllocationOf_allocateAllTo 1 {firstHead}
  have hsecondRestAllocation : IsAllocationOf secondRestAllocation secondRest :=
    isAllocationOf_allocateAllTo 2 secondRest
  have hsecondHeadAllocation : IsAllocationOf secondHeadAllocation {secondHead} :=
    isAllocationOf_allocateAllTo 3 {secondHead}
  have hfirstAllocation : IsAllocationOf firstAllocation (firstRest ∪ {firstHead}) := by
    simpa [firstAllocation] using isAllocationOf_union firstRestAllocation firstHeadAllocation
      firstRest {firstHead} hfirstPartsDisjoint hfirstRestAllocation hfirstHeadAllocation
  have hsecondAllocation : IsAllocationOf secondAllocation (secondRest ∪ {secondHead}) := by
    simpa [secondAllocation] using isAllocationOf_union secondRestAllocation secondHeadAllocation
      secondRest {secondHead} hsecondPartsDisjoint hsecondRestAllocation hsecondHeadAllocation
  have hfirstSecondDisjoint : Disjoint (firstRest ∪ {firstHead})
      (secondRest ∪ {secondHead}) := by
    rw [Finset.disjoint_left]
    intro item hfirstItem hsecondItem
    rcases Finset.mem_union.mp hfirstItem with hfirstRestItem | hfirstHeadItem
    · have hfirstTypeItem : item ∈ firstType :=
        Finset.erase_subset firstHead firstType (by simpa [firstRest] using hfirstRestItem)
      rcases Finset.mem_union.mp hsecondItem with hsecondRestItem | hsecondHeadItem
      · have hsecondTypeItem : item ∈ secondType :=
          Finset.erase_subset secondHead secondType (by simpa [secondRest] using hsecondRestItem)
        exact (Finset.disjoint_left.mp htypesDisjoint hfirstTypeItem hsecondTypeItem).elim
      · have hEq : item = secondHead := Finset.mem_singleton.mp hsecondHeadItem
        subst item
        exact (Finset.disjoint_left.mp htypesDisjoint hfirstTypeItem hsecondHead).elim
    · have hEq : item = firstHead := Finset.mem_singleton.mp hfirstHeadItem
      subst item
      rcases Finset.mem_union.mp hsecondItem with hsecondRestItem | hsecondHeadItem
      · have hsecondTypeItem : firstHead ∈ secondType :=
          Finset.erase_subset secondHead secondType (by simpa [secondRest] using hsecondRestItem)
        exact (Finset.disjoint_left.mp htypesDisjoint hfirstHead hsecondTypeItem).elim
      · have hheadsEq : firstHead = secondHead := Finset.mem_singleton.mp hsecondHeadItem
        subst secondHead
        exact (Finset.disjoint_left.mp htypesDisjoint hfirstHead hsecondHead).elim
  have hsuffixAllocation : IsAllocationOf suffix
      ((firstRest ∪ {firstHead}) ∪ (secondRest ∪ {secondHead})) := by
    simpa [suffix] using isAllocationOf_union firstAllocation secondAllocation
      (firstRest ∪ {firstHead}) (secondRest ∪ {secondHead}) hfirstSecondDisjoint
      hfirstAllocation hsecondAllocation
  have hfirstDecomposition : firstRest ∪ ({firstHead} : Finset Item) = firstType := by
    simpa [firstRest, Finset.union_comm] using Finset.insert_erase hfirstHead
  have hsecondDecomposition : secondRest ∪ ({secondHead} : Finset Item) = secondType := by
    simpa [secondRest, Finset.union_comm] using Finset.insert_erase hsecondHead
  have hsuffixAllocation' : IsAllocationOf suffix m2Chores := by
    have hgoods : (firstRest ∪ {firstHead}) ∪ (secondRest ∪ {secondHead}) = m2Chores := by
      rw [hfirstDecomposition, hsecondDecomposition, hcover]
    rw [← hgoods]
    exact hsuffixAllocation
  have hsuffixZero : suffix 0 = firstRest := by
    simp [suffix, firstAllocation, secondAllocation, firstRestAllocation,
      firstHeadAllocation, secondRestAllocation, secondHeadAllocation, allocateAllTo]
  have hsuffixOne : suffix 1 = {firstHead} := by
    simp [suffix, firstAllocation, secondAllocation, firstRestAllocation,
      firstHeadAllocation, secondRestAllocation, secondHeadAllocation, allocateAllTo]
  have hsuffixTwo : suffix 2 = secondRest := by
    simp [suffix, firstAllocation, secondAllocation, firstRestAllocation,
      firstHeadAllocation, secondRestAllocation, secondHeadAllocation, allocateAllTo]
  have hsuffixThree : suffix 3 = {secondHead} := by
    simp [suffix, firstAllocation, secondAllocation, firstRestAllocation,
      firstHeadAllocation, secondRestAllocation, secondHeadAllocation, allocateAllTo]
  refine ⟨firstHead, hfirstHead, secondHead, hsecondHead, suffix, hsuffixAllocation',
    ?_, hsuffixOne, ?_, hsuffixThree, ?_, ?_, ?_, ?_⟩
  · simpa [firstRest] using hsuffixZero
  · simpa [secondRest] using hsuffixTwo
  · rw [hsuffixZero]
    change (firstType.erase firstHead).card = 2
    rw [Finset.card_erase_of_mem hfirstHead, hfirstCard]
  · simp [hsuffixOne]
  · rw [hsuffixTwo]
    change (secondType.erase secondHead).card = 2
    rw [Finset.card_erase_of_mem hsecondHead, hsecondCard]
  · simp [hsuffixThree]

/-- The hard `a=0` allocation of source Case B.3.1.  The two prefix chores
are respectively small only for the two long agents, while the two
three-chore M₂ types are split `2:1` between their small endpoint pairs. -/
theorem existsEfxOfB2ZeroCornerDirect
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores firstType secondType : Finset Item) (prefixZero prefixOne : Item)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixAllocation : IsAllocationOf prefixAllocation prefixChores)
    (hprefixZero : prefixAllocation 0 = {prefixZero})
    (hprefixOne : prefixAllocation 1 = {prefixOne})
    (hprefixTwo : prefixAllocation 2 = ∅) (hprefixThree : prefixAllocation 3 = ∅)
    (hprefixZeroCosts : cost 0 prefixZero = 1 ∧ cost 1 prefixZero = r ∧
      cost 2 prefixZero = r ∧ cost 3 prefixZero = r)
    (hprefixOneCosts : cost 0 prefixOne = r ∧ cost 1 prefixOne = 1 ∧
      cost 2 prefixOne = r ∧ cost 3 prefixOne = r)
    (hcover : m2Chores = firstType ∪ secondType)
    (htypesDisjoint : Disjoint firstType secondType)
    (hfirstCard : firstType.card = 3) (hsecondCard : secondType.card = 3)
    (hfirstType : ∀ item ∈ firstType,
      cost 0 item = 1 ∧ cost 1 item = 1 ∧ cost 2 item = r ∧ cost 3 item = r)
    (hsecondType : ∀ item ∈ secondType,
      cost 0 item = r ∧ cost 1 item = r ∧ cost 2 item = 1 ∧ cost 3 item = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨firstHead, hfirstHead, secondHead, hsecondHead, suffix, hsuffixAllocation,
    hsuffixZero, hsuffixOne, hsuffixTwo, hsuffixThree, hsuffixZeroCard, hsuffixOneCard,
    hsuffixTwoCard, hsuffixThreeCard⟩ :=
    existsB2ZeroCornerSuffixAllocation Item m2Chores firstType secondType hcover
      htypesDisjoint hfirstCard hsecondCard
  let allocation : Allocation (Fin 4) Item := fun agent =>
    prefixAllocation agent ∪ suffix agent
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hprefixAllocation.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hfinalAllocation : IsAllocationOf allocation (prefixChores ∪ m2Chores) := by
    simpa [allocation] using isAllocationOf_union prefixAllocation suffix prefixChores m2Chores
      hprefixM2 hprefixAllocation hsuffixAllocation
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (allocation owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) := by
    exact additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hpfxZeroCostZero : additiveChoreCost cost 0 (prefixAllocation 0) = 1 := by
    rw [hprefixZero]
    simp [additiveChoreCost, hprefixZeroCosts.1]
  have hpfxOneCostZero : additiveChoreCost cost 0 (prefixAllocation 1) = r := by
    rw [hprefixOne]
    simp [additiveChoreCost, hprefixOneCosts.1]
  have hpfxZeroCostOne : additiveChoreCost cost 1 (prefixAllocation 0) = r := by
    rw [hprefixZero]
    simp [additiveChoreCost, hprefixZeroCosts.2.1]
  have hpfxOneCostOne : additiveChoreCost cost 1 (prefixAllocation 1) = 1 := by
    rw [hprefixOne]
    simp [additiveChoreCost, hprefixOneCosts.2.1]
  have hpfxZeroCostTwo : additiveChoreCost cost 2 (prefixAllocation 0) = r := by
    rw [hprefixZero]
    simp [additiveChoreCost, hprefixZeroCosts.2.2.1]
  have hpfxOneCostTwo : additiveChoreCost cost 2 (prefixAllocation 1) = r := by
    rw [hprefixOne]
    simp [additiveChoreCost, hprefixOneCosts.2.2.1]
  have hfirstRestCard : (firstType.erase firstHead).card = 2 := by
    simpa [hsuffixZero] using hsuffixZeroCard
  have hsecondRestCard : (secondType.erase secondHead).card = 2 := by
    simpa [hsuffixTwo] using hsuffixTwoCard
  have hsuffixZeroCostZero : additiveChoreCost cost 0 (suffix 0) = 2 := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 0
      (firstType.erase firstHead) 1]
    · simp [hfirstRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hfirstType item (Finset.erase_subset firstHead firstType hitem)).1
  have hsuffixOneCostZero : additiveChoreCost cost 0 (suffix 1) = 1 := by
    rw [hsuffixOne]
    simp [additiveChoreCost, (hfirstType firstHead hfirstHead).1]
  have hsuffixTwoCostZero : additiveChoreCost cost 0 (suffix 2) = 2 * r := by
    rw [hsuffixTwo, additiveChoreCost_eq_card_nsmul_of_constant cost 0
      (secondType.erase secondHead) r]
    · simp [hsecondRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hsecondType item (Finset.erase_subset secondHead secondType hitem)).1
  have hsuffixThreeCostZero : additiveChoreCost cost 0 (suffix 3) = r := by
    rw [hsuffixThree]
    simp [additiveChoreCost, (hsecondType secondHead hsecondHead).1]
  have hsuffixZeroCostOne : additiveChoreCost cost 1 (suffix 0) = 2 := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 1
      (firstType.erase firstHead) 1]
    · simp [hfirstRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hfirstType item (Finset.erase_subset firstHead firstType hitem)).2.1
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = 1 := by
    rw [hsuffixOne]
    simp [additiveChoreCost, (hfirstType firstHead hfirstHead).2.1]
  have hsuffixTwoCostOne : additiveChoreCost cost 1 (suffix 2) = 2 * r := by
    rw [hsuffixTwo, additiveChoreCost_eq_card_nsmul_of_constant cost 1
      (secondType.erase secondHead) r]
    · simp [hsecondRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hsecondType item (Finset.erase_subset secondHead secondType hitem)).2.1
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = r := by
    rw [hsuffixThree]
    simp [additiveChoreCost, (hsecondType secondHead hsecondHead).2.1]
  have hsuffixZeroCostTwo : additiveChoreCost cost 2 (suffix 0) = 2 * r := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 2
      (firstType.erase firstHead) r]
    · simp [hfirstRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hfirstType item (Finset.erase_subset firstHead firstType hitem)).2.2.1
  have hsuffixOneCostTwo : additiveChoreCost cost 2 (suffix 1) = r := by
    rw [hsuffixOne]
    simp [additiveChoreCost, (hfirstType firstHead hfirstHead).2.2.1]
  have hsuffixTwoCostTwo : additiveChoreCost cost 2 (suffix 2) = 2 := by
    rw [hsuffixTwo, additiveChoreCost_eq_card_nsmul_of_constant cost 2
      (secondType.erase secondHead) 1]
    · simp [hsecondRestCard, nsmul_eq_mul]
    · intro item hitem
      exact (hsecondType item (Finset.erase_subset secondHead secondType hitem)).2.2.1
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = 1 := by
    rw [hsuffixThree]
    simp [additiveChoreCost, (hsecondType secondHead hsecondHead).2.2.1]
  have hfinalZeroCard : (allocation 0).card = 3 := by
    change (prefixAllocation 0 ∪ suffix 0).card = 3
    rw [Finset.card_union_of_disjoint (hbundlesDisjoint 0), hprefixZero, hsuffixZeroCard]
    simp
  have hfinalOneCard : (allocation 1).card = 2 := by
    change (prefixAllocation 1 ∪ suffix 1).card = 2
    rw [Finset.card_union_of_disjoint (hbundlesDisjoint 1), hprefixOne, hsuffixOneCard]
    simp
  have hfinalTwoCard : (allocation 2).card = 2 := by
    change (prefixAllocation 2 ∪ suffix 2).card = 2
    rw [hprefixTwo, Finset.empty_union, hsuffixTwoCard]
  have hfinalThreeCard : (allocation 3).card = 1 := by
    change (prefixAllocation 3 ∪ suffix 3).card = 1
    rw [hprefixThree, Finset.empty_union, hsuffixThreeCard]
  have hownSmall : ∀ agent item, item ∈ allocation agent → IsSmallChore cost agent item := by
    intro agent item hitem
    fin_cases agent
    · rcases Finset.mem_union.mp hitem with hprefixItem | hsuffixItem
      · have hEq : item = prefixZero := by simpa [allocation, hprefixZero] using hprefixItem
        simpa [hEq, IsSmallChore] using hprefixZeroCosts.1
      · have hfirstItem : item ∈ firstType := by
          change item ∈ suffix 0 at hsuffixItem
          rw [hsuffixZero] at hsuffixItem
          exact Finset.erase_subset firstHead firstType hsuffixItem
        simpa [IsSmallChore] using (hfirstType item hfirstItem).1
    · rcases Finset.mem_union.mp hitem with hprefixItem | hsuffixItem
      · have hEq : item = prefixOne := by simpa [allocation, hprefixOne] using hprefixItem
        simpa [hEq, IsSmallChore] using hprefixOneCosts.2.1
      · have hEq : item = firstHead := by simpa [hsuffixOne] using hsuffixItem
        simpa [hEq, IsSmallChore] using (hfirstType firstHead hfirstHead).2.1
    · have hsuffixItem : item ∈ suffix 2 := by simpa [allocation, hprefixTwo] using hitem
      have hsecondItem : item ∈ secondType := by
        rw [hsuffixTwo] at hsuffixItem
        exact Finset.erase_subset secondHead secondType hsuffixItem
      simpa [IsSmallChore] using (hsecondType item hsecondItem).2.2.1
    · have hsuffixItem : item ∈ suffix 3 := by simpa [allocation, hprefixThree] using hitem
      have hEq : item = secondHead := by simpa [hsuffixThree] using hsuffixItem
      simpa [hEq, IsSmallChore] using (hsecondType secondHead hsecondHead).2.2.2
  have hcostNonneg : ∀ agent item, 0 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) agent item
  have hfinalNonneg : ∀ observer owner : Fin 4,
      0 ≤ additiveChoreCost cost observer (allocation owner) :=
    fun observer owner => additiveChoreCost_nonneg cost hcostNonneg observer (allocation owner)
  have hbound : ∀ own comparison,
      ((allocation own).card - 1 : ℕ) ≤ additiveChoreCost cost own (allocation comparison) := by
    intro own comparison
    fin_cases own <;> fin_cases comparison
    · change ((allocation 0).card - 1 : ℕ) ≤ additiveChoreCost cost 0 (allocation 0)
      rw [hfinalZeroCard, hfinalCost 0 0, hpfxZeroCostZero, hsuffixZeroCostZero]
      norm_num
    · change ((allocation 0).card - 1 : ℕ) ≤ additiveChoreCost cost 0 (allocation 1)
      rw [hfinalZeroCard, hfinalCost 0 1, hpfxOneCostZero, hsuffixOneCostZero]
      norm_num at ⊢
      linarith
    · change ((allocation 0).card - 1 : ℕ) ≤ additiveChoreCost cost 0 (allocation 2)
      rw [hfinalZeroCard, hfinalCost 0 2, hprefixTwo, hsuffixTwoCostZero]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num at ⊢
      linarith
    · change ((allocation 0).card - 1 : ℕ) ≤ additiveChoreCost cost 0 (allocation 3)
      rw [hfinalZeroCard, hfinalCost 0 3, hprefixThree, hsuffixThreeCostZero]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num at ⊢
      linarith
    · change ((allocation 1).card - 1 : ℕ) ≤ additiveChoreCost cost 1 (allocation 0)
      rw [hfinalOneCard, hfinalCost 1 0, hpfxZeroCostOne, hsuffixZeroCostOne]
      norm_num at ⊢
      linarith
    · change ((allocation 1).card - 1 : ℕ) ≤ additiveChoreCost cost 1 (allocation 1)
      rw [hfinalOneCard, hfinalCost 1 1, hpfxOneCostOne, hsuffixOneCostOne]
      norm_num
    · change ((allocation 1).card - 1 : ℕ) ≤ additiveChoreCost cost 1 (allocation 2)
      rw [hfinalOneCard, hfinalCost 1 2, hprefixTwo, hsuffixTwoCostOne]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num at ⊢
      linarith
    · change ((allocation 1).card - 1 : ℕ) ≤ additiveChoreCost cost 1 (allocation 3)
      rw [hfinalOneCard, hfinalCost 1 3, hprefixThree, hsuffixThreeCostOne]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num at ⊢
      linarith
    · change ((allocation 2).card - 1 : ℕ) ≤ additiveChoreCost cost 2 (allocation 0)
      rw [hfinalTwoCard, hfinalCost 2 0, hpfxZeroCostTwo, hsuffixZeroCostTwo]
      norm_num at ⊢
      linarith
    · change ((allocation 2).card - 1 : ℕ) ≤ additiveChoreCost cost 2 (allocation 1)
      rw [hfinalTwoCard, hfinalCost 2 1, hpfxOneCostTwo, hsuffixOneCostTwo]
      norm_num at ⊢
      linarith
    · change ((allocation 2).card - 1 : ℕ) ≤ additiveChoreCost cost 2 (allocation 2)
      rw [hfinalTwoCard, hfinalCost 2 2, hprefixTwo, hsuffixTwoCostTwo]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num
    · change ((allocation 2).card - 1 : ℕ) ≤ additiveChoreCost cost 2 (allocation 3)
      rw [hfinalTwoCard, hfinalCost 2 3, hprefixThree, hsuffixThreeCostTwo]
      simp only [additiveChoreCost_empty, zero_add]
      norm_num
    · change ((allocation 3).card - 1 : ℕ) ≤ additiveChoreCost cost 3 (allocation 0)
      rw [hfinalThreeCard]
      norm_num at ⊢
      exact hfinalNonneg 3 0
    · change ((allocation 3).card - 1 : ℕ) ≤ additiveChoreCost cost 3 (allocation 1)
      rw [hfinalThreeCard]
      norm_num at ⊢
      exact hfinalNonneg 3 1
    · change ((allocation 3).card - 1 : ℕ) ≤ additiveChoreCost cost 3 (allocation 2)
      rw [hfinalThreeCard]
      norm_num at ⊢
      exact hfinalNonneg 3 2
    · change ((allocation 3).card - 1 : ℕ) ≤ additiveChoreCost cost 3 (allocation 3)
      rw [hfinalThreeCard]
      norm_num at ⊢
      exact hfinalNonneg 3 3
  exact ⟨allocation, hfinalAllocation,
    efxForChores_of_unit_own_bundles_and_card_lower_bounds Item cost
      (prefixChores ∪ m2Chores) allocation hfinalAllocation hownSmall hbound⟩

end HT26EFXChores
