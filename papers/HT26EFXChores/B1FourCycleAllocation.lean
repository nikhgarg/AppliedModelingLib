import HT26EFXChores.B1DirectAllocation

/-!
# The four-cycle direct allocation in Case B.2.2(b)

This module formalizes the second explicit four-chore schedule in the source's
low-multiplicity `b = 1` case.  Its hypotheses use the M₂ type fibres rather
than an abstract graph certificate.

Source: `EFXadditivechores.tex`, Case B.2.2(b), lines 2525--2542.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Source Case B.2.2(b)'s four-cycle schedule with agent `0` long.  The
four chores have types `(0,1)`, `(1,2)`, `(2,3)`, and `(0,3)` respectively.
The first two go to agent `1`, and the others go to agents `2` and `3`.

The explicit cover hypothesis says that these are all of M₂; fibre membership
both identifies the source graph configuration and supplies the `{1,r}` cost
table used in the finite EFX calculation. -/
theorem existsEfxOfB1LowMultiplicity_fourCycle_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (item01 item12 item23 item03 : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (h01 : item01 ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (h12 : item12 ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (h23 : item23 ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (h03 : item03 ∈ m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)))
    (hcover : m2Chores = ({item01, item12} ∪ {item23}) ∪ {item03}) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  have htypeDisjoint (firstType secondType : Finset (Fin 4))
      (hfirst : firstType ≠ secondType) :
      Disjoint (m2TypeChorePool cost m2Chores firstType)
        (m2TypeChorePool cost m2Chores secondType) :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores firstType secondType hfirst
  have h01ne12 : item01 ≠ item12 := by
    intro hEq
    subst item12
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) (by decide)) h01 h12).elim
  have h01ne23 : item01 ≠ item23 := by
    intro hEq
    subst item23
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)) h01 h23).elim
  have h12ne23 : item12 ≠ item23 := by
    intro hEq
    subst item23
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({1, 2} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)) h12 h23).elim
  have h01ne03 : item01 ≠ item03 := by
    intro hEq
    subst item03
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({0, 1} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) (by decide)) h01 h03).elim
  have h12ne03 : item12 ≠ item03 := by
    intro hEq
    subst item03
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({1, 2} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) (by decide)) h12 h03).elim
  have h23ne03 : item23 ≠ item03 := by
    intro hEq
    subst item03
    exact (Finset.disjoint_left.mp
      (htypeDisjoint ({2, 3} : Finset (Fin 4)) ({0, 3} : Finset (Fin 4)) (by decide)) h23 h03).elim
  have h01_12_23 : Disjoint ({item01, item12} : Finset Item) {item23} := by
    rw [Finset.disjoint_singleton_right]
    intro hitem
    rcases (by simpa using hitem : item23 = item01 ∨ item23 = item12) with h23eq01 | h23eq12
    · exact (h01ne23 h23eq01.symm).elim
    · exact (h12ne23 h23eq12.symm).elim
  have h01_12_23_03 : Disjoint (({item01, item12} : Finset Item) ∪ {item23}) {item03} := by
    rw [Finset.disjoint_singleton_right]
    intro hitem
    rcases Finset.mem_union.mp hitem with hitem01_12 | hitem23
    · rcases (by simpa using hitem01_12 : item03 = item01 ∨ item03 = item12) with h03eq01 | h03eq12
      · exact (h01ne03 h03eq01.symm).elim
      · exact (h12ne03 h03eq12.symm).elim
    · have h03eq23 : item03 = item23 := by simpa using hitem23
      exact (h23ne03 h03eq23.symm).elim
  let suffixOne : Allocation (Fin 4) Item :=
    allocateAllTo (Fin 4) Item 1 ({item01, item12} : Finset Item)
  let suffixTwo : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 {item23}
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 {item03}
  let suffixTwelve : Allocation (Fin 4) Item := fun agent => suffixOne agent ∪ suffixTwo agent
  let suffix : Allocation (Fin 4) Item := fun agent => suffixTwelve agent ∪ suffixThree agent
  have hsuffixOne : IsAllocationOf suffixOne ({item01, item12} : Finset Item) :=
    isAllocationOf_allocateAllTo 1 {item01, item12}
  have hsuffixTwo : IsAllocationOf suffixTwo {item23} := isAllocationOf_allocateAllTo 2 {item23}
  have hsuffixThree : IsAllocationOf suffixThree {item03} := isAllocationOf_allocateAllTo 3 {item03}
  have hsuffixTwelve : IsAllocationOf suffixTwelve (({item01, item12} : Finset Item) ∪ {item23}) := by
    simpa [suffixTwelve] using isAllocationOf_union suffixOne suffixTwo {item01, item12} {item23}
      h01_12_23 hsuffixOne hsuffixTwo
  have hsuffixAllocation : IsAllocationOf suffix
      ((({item01, item12} : Finset Item) ∪ {item23}) ∪ {item03}) := by
    simpa [suffix] using isAllocationOf_union suffixTwelve suffixThree
      (({item01, item12} : Finset Item) ∪ {item23}) {item03}
      h01_12_23_03 hsuffixTwelve hsuffixThree
  have hsuffixZero : suffix 0 = ∅ := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixOneEq : suffix 1 = {item01, item12} := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixTwoEq : suffix 2 = {item23} := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixThreeEq : suffix 3 = {item03} := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have h01CostOne : cost 1 item01 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({0, 1} : Finset (Fin 4)) item01 1 h01 (by simp)
  have h12CostOne : cost 1 item12 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({1, 2} : Finset (Fin 4)) item12 1 h12 (by simp)
  have h01CostTwo : cost 2 item01 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 1} : Finset (Fin 4)) item01 2 hcost h01 (by simp)
  have h12CostTwo : cost 2 item12 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({1, 2} : Finset (Fin 4)) item12 2 h12 (by simp)
  have h01CostThree : cost 3 item01 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 1} : Finset (Fin 4)) item01 3 hcost h01 (by simp)
  have h12CostThree : cost 3 item12 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({1, 2} : Finset (Fin 4)) item12 3 hcost h12 (by simp)
  have h23CostOne : cost 1 item23 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({2, 3} : Finset (Fin 4)) item23 1 hcost h23 (by simp)
  have h23CostTwo : cost 2 item23 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({2, 3} : Finset (Fin 4)) item23 2 h23 (by simp)
  have h23CostThree : cost 3 item23 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({2, 3} : Finset (Fin 4)) item23 3 h23 (by simp)
  have h03CostOne : cost 1 item03 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 3} : Finset (Fin 4)) item03 1 hcost h03 (by simp)
  have h03CostTwo : cost 2 item03 = r := by
    simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 3} : Finset (Fin 4)) item03 2 hcost h03 (by simp)
  have h03CostThree : cost 3 item03 = 1 := by
    simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
      ({0, 3} : Finset (Fin 4)) item03 3 h03 (by simp)
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = 2 := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 {item01, item12} 1]
    · norm_num [Finset.card_pair h01ne12, nsmul_eq_mul]
    · intro item hitem
      rcases (by simpa using hitem : item = item01 ∨ item = item12) with hEq | hEq
      · simpa [hEq] using h01CostOne
      · simpa [hEq] using h12CostOne
  have hsuffixOneCostTwo : additiveChoreCost cost 2 (suffix 1) = r + 1 := by
    rw [hsuffixOneEq]
    simp [additiveChoreCost, h01CostTwo, h12CostTwo, h01ne12]
  have hsuffixOneCostThree : additiveChoreCost cost 3 (suffix 1) = 2 * r := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 {item01, item12} r]
    · norm_num [Finset.card_pair h01ne12, nsmul_eq_mul]
    · intro item hitem
      rcases (by simpa using hitem : item = item01 ∨ item = item12) with hEq | hEq
      · simpa [hEq] using h01CostThree
      · simpa [hEq] using h12CostThree
  have hsuffixTwoCostOne : additiveChoreCost cost 1 (suffix 2) = r := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, h23CostOne]
  have hsuffixTwoCostTwo : additiveChoreCost cost 2 (suffix 2) = 1 := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, h23CostTwo]
  have hsuffixTwoCostThree : additiveChoreCost cost 3 (suffix 2) = 1 := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, h23CostThree]
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = r := by
    rw [hsuffixThreeEq]
    simp [additiveChoreCost, h03CostOne]
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = r := by
    rw [hsuffixThreeEq]
    simp [additiveChoreCost, h03CostTwo]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 1 := by
    rw [hsuffixThreeEq]
    simp [additiveChoreCost, h03CostThree]
  have hshortLong : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤ r + 1 := by
    intro short hshort
    fin_cases short
    · exact (hshort rfl).elim
    · simpa using (by rw [hsuffixOneCostOne]; linarith :
        additiveChoreCost cost 1 (suffix 1) ≤ r + 1)
    · simpa using (by rw [hsuffixTwoCostTwo]; linarith :
        additiveChoreCost cost 2 (suffix 2) ≤ r + 1)
    · simpa using (by rw [hsuffixThreeCostThree]; linarith :
        additiveChoreCost cost 3 (suffix 3) ≤ r + 1)
  have hshortUnit : ∀ short other : Fin 4, short ≠ 0 → other ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤
        additiveChoreCost cost short (suffix other) + 1 := by
    intro short other hshort hother
    fin_cases short <;> fin_cases other
    · exact (hshort rfl).elim
    · exact (hshort rfl).elim
    · exact (hshort rfl).elim
    · exact (hshort rfl).elim
    · exact (hother rfl).elim
    · simpa using (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
        additiveChoreCost cost 1 (suffix 1) ≤ additiveChoreCost cost 1 (suffix 1) + 1)
    · simpa using (by rw [hsuffixOneCostOne, hsuffixTwoCostOne]; linarith :
        additiveChoreCost cost 1 (suffix 1) ≤ additiveChoreCost cost 1 (suffix 2) + 1)
    · simpa using (by rw [hsuffixOneCostOne, hsuffixThreeCostOne]; linarith :
        additiveChoreCost cost 1 (suffix 1) ≤ additiveChoreCost cost 1 (suffix 3) + 1)
    · exact (hother rfl).elim
    · simpa using (by rw [hsuffixTwoCostTwo, hsuffixOneCostTwo]; linarith :
        additiveChoreCost cost 2 (suffix 2) ≤ additiveChoreCost cost 2 (suffix 1) + 1)
    · simpa using (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
        additiveChoreCost cost 2 (suffix 2) ≤ additiveChoreCost cost 2 (suffix 2) + 1)
    · simpa using (by rw [hsuffixTwoCostTwo, hsuffixThreeCostTwo]; linarith :
        additiveChoreCost cost 2 (suffix 2) ≤ additiveChoreCost cost 2 (suffix 3) + 1)
    · exact (hother rfl).elim
    · simpa using (by rw [hsuffixThreeCostThree, hsuffixOneCostThree]; linarith :
        additiveChoreCost cost 3 (suffix 3) ≤ additiveChoreCost cost 3 (suffix 1) + 1)
    · simpa using (by rw [hsuffixThreeCostThree, hsuffixTwoCostThree]; linarith :
        additiveChoreCost cost 3 (suffix 3) ≤ additiveChoreCost cost 3 (suffix 2) + 1)
    · simpa using (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
        additiveChoreCost cost 3 (suffix 3) ≤ additiveChoreCost cost 3 (suffix 3) + 1)
  have hfinal := efxForChores_union_of_supercanonicalLongZeroAndControlledSuffix Item r cost
    prefixChores ((({item01, item12} : Finset Item) ∪ {item23}) ∪ {item03})
    a quota prefixAllocation suffix hr hcost
    (by simpa [hcover] using hprefixM2) hcanonical hquota0 hquota1 hquota2 hquota3 hsuper
    hsuffixAllocation hsuffixZero hshortLong hshortUnit
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent,
    (by simpa [hcover] using hfinal.1), (by simpa [hcover] using hfinal.2)⟩

/-- The four-cycle schedule is label-invariant.  It covers the paper's
``up to relabeling'' reduction and every choice of the long agent. -/
theorem existsEfxOfB1LowMultiplicity_fourCycle_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (item01 item12 item23 item03 : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (h01 : item01 ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (h12 : item12 ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 2} : Finset (Fin 4)))
    (h23 : item23 ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)))
    (h03 : item03 ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 3} : Finset (Fin 4)))
    (hcover : m2Chores = ({item01, item12} ∪ {item23}) ∪ {item03}) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_fourCycle_longZero Item r (relabelChoreCost labels cost)
    prefixChores m2Chores item01 item12 item23 item03 a
    (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota] using hquota0
  · simpa [relabelQuota] using hquota1
  · simpa [relabelQuota] using hquota2
  · simpa [relabelQuota] using hquota3
  · intro short hshort
    have hshortOriginal : labels short ≠ labels 0 := by
      intro hEq
      apply hshort
      exact labels.injective hEq
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) hshortOriginal
  · exact h01
  · exact h12
  · exact h23
  · exact h03
  · exact hcover

end HT26EFXChores
