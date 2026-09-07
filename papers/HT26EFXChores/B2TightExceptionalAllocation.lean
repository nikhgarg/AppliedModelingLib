import HT26EFXChores.B2MaxMultiplicityAllocation

/-!
# The tight exceptional direct allocation in source Case B.3.1

When the parallel-edge gap fill would leave the exceptional type itself as the
exceptional pair, the source proves that the only tight configuration consists
of three chores of each of two disjoint types.  This module records the direct
allocation used there after the source's within-pair relabelling: the short
agents are `1` and `3`, and receive the three chores small for them.

Source: `EFXadditivechores.tex`, lines 2612--2676.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The direct part of the tight exceptional configuration in source Case
B.3.1.  The two type pools are disjoint, have cardinality three, and are
assigned wholesale to their respectively short endpoints. -/
theorem existsEfxOfB2TightExceptionalDirect
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores firstType secondType : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
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
  classical
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 firstType
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 secondType
  let suffix : Allocation (Fin 4) Item := fun agent => suffixOne agent ∪ suffixThree agent
  have hsuffixOneAllocation : IsAllocationOf suffixOne firstType :=
    isAllocationOf_allocateAllTo 1 firstType
  have hsuffixThreeAllocation : IsAllocationOf suffixThree secondType :=
    isAllocationOf_allocateAllTo 3 secondType
  have hsuffixAllocation : IsAllocationOf suffix (firstType ∪ secondType) := by
    simpa [suffix] using isAllocationOf_union suffixOne suffixThree firstType secondType
      htypesDisjoint hsuffixOneAllocation hsuffixThreeAllocation
  have hsuffixZero : suffix 0 = ∅ := by
    simp [suffix, suffixOne, suffixThree, allocateAllTo]
  have hsuffixOne : suffix 1 = firstType := by
    simp [suffix, suffixOne, suffixThree, allocateAllTo]
  have hsuffixTwo : suffix 2 = ∅ := by
    simp [suffix, suffixOne, suffixThree, allocateAllTo]
  have hsuffixThree : suffix 3 = secondType := by
    simp [suffix, suffixOne, suffixThree, allocateAllTo]
  have hprefixSuffix : Disjoint prefixChores (firstType ∪ secondType) := by
    rw [← hcover]
    exact hprefixM2
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixSuffix
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hsuffixOneCostZero : additiveChoreCost cost 0 (suffix 1) = 3 := by
    rw [hsuffixOne,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 firstType 1
        (fun item hitem => (hfirstType item hitem).1), hfirstCard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = 3 := by
    rw [hsuffixOne,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 firstType 1
        (fun item hitem => (hfirstType item hitem).2.1), hfirstCard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostTwo : additiveChoreCost cost 2 (suffix 1) = 3 * r := by
    rw [hsuffixOne,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 firstType r
        (fun item hitem => (hfirstType item hitem).2.2.1), hfirstCard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostThree : additiveChoreCost cost 3 (suffix 1) = 3 * r := by
    rw [hsuffixOne,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 firstType r
        (fun item hitem => (hfirstType item hitem).2.2.2), hfirstCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostZero : additiveChoreCost cost 0 (suffix 3) = 3 * r := by
    rw [hsuffixThree,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 secondType r
        (fun item hitem => (hsecondType item hitem).1), hsecondCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = 3 * r := by
    rw [hsuffixThree,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 secondType r
        (fun item hitem => (hsecondType item hitem).2.1), hsecondCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = 3 := by
    rw [hsuffixThree,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 secondType 1
        (fun item hitem => (hsecondType item hitem).2.2.1), hsecondCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 3 := by
    rw [hsuffixThree,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 secondType 1
        (fun item hitem => (hsecondType item hitem).2.2.2), hsecondCard]
    norm_num [nsmul_eq_mul]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hprefixEqual : ∀ first second : Fin 4, quota first = quota second →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hquota
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second hquota
  have hshortUnit : ∀ short : Fin 4, short = 1 ∨ short = 3 → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    rcases hshort with rfl | rfl
    · fin_cases other
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 1 1, hfinalCost 1 0, hsuffixOneCostOne, hsuffixZero]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 1 0 (by rw [hquota1]) (by rw [hquota0])]
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) + 1
        linarith
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 1 1, hfinalCost 1 2, hsuffixOneCostOne, hsuffixTwo]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 1 2 (by rw [hquota1]) (by rw [hquota2])]
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 3 ∪ suffix 3) + 1
        rw [hfinalCost 1 1, hfinalCost 1 3, hsuffixOneCostOne, hsuffixThreeCostOne]
        linarith [hprefixEqual 1 3 (by rw [hquota1, hquota3])]
    · fin_cases other
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 3 3, hfinalCost 3 0, hsuffixThreeCostThree, hsuffixZero]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 3 0 (by rw [hquota3]) (by rw [hquota0])]
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 1 ∪ suffix 1) + 1
        rw [hfinalCost 3 3, hfinalCost 3 1, hsuffixThreeCostThree, hsuffixOneCostThree]
        linarith [hprefixEqual 3 1 (by rw [hquota3, hquota1])]
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 3 3, hfinalCost 3 2, hsuffixThreeCostThree, hsuffixTwo]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 3 2 (by rw [hquota3]) (by rw [hquota2])]
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) + 1
        linarith
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf
      (fun agent => prefixAllocation agent ∪ suffix agent) (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union prefixAllocation suffix prefixChores
      (firstType ∪ secondType) hprefixSuffix hcanonical.1 hsuffixAllocation
    simpa [hcover] using hcombined
  refine ⟨fun agent => prefixAllocation agent ∪ suffix agent, hfinalAllocation, ?_⟩
  intro agent other
  fin_cases agent
  · by_cases hempty : prefixAllocation 0 = ∅
    · left
      simpa [hsuffixZero] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 0 := by simpa [hsuffixZero] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX 0 other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost 0 ((prefixAllocation 0 ∪ suffix 0).erase item) ≤
          additiveChoreCost cost 0 (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost 0 (prefixAllocation 0) item hprefixItem
        rw [hsuffixZero, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' : additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
            additiveChoreCost cost 0 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 0 (prefixAllocation 0) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
              additiveChoreCost cost 0 (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost 0 (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost 0 other]
            have hnonneg : 0 ≤ additiveChoreCost cost 0 (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 0 (suffix other)
            linarith
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 1 ((prefixAllocation 1 ∪ suffix 1).erase item) ≤
      additiveChoreCost cost 1 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 1 ∪ suffix 1 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 1 (prefixAllocation 1 ∪ suffix 1) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 1 (Or.inl rfl) other, hcostLower 1 item]
  · by_cases hempty : prefixAllocation 2 = ∅
    · left
      simpa [hsuffixTwo] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 2 := by simpa [hsuffixTwo] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX 2 other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2).erase item) ≤
          additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost 2 (prefixAllocation 2) item hprefixItem
        rw [hsuffixTwo, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' : additiveChoreCost cost 2 (prefixAllocation 2) - cost 2 item ≤
            additiveChoreCost cost 2 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 2 (prefixAllocation 2) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 2 (prefixAllocation 2) - cost 2 item ≤
              additiveChoreCost cost 2 (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost 2 other]
            have hnonneg : 0 ≤ additiveChoreCost cost 2 (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (suffix other)
            linarith
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
      additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 3 ∪ suffix 3 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3 ∪ suffix 3) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 3 (Or.inr rfl) other, hcostLower 3 item]

/-- The source's tight-residual counting deduction in Case B.3.1.  Removing
two chores from a maximum type and leaving one surviving chore of that type
together with an exceptional complementary residue forces both types to have
cardinality three. -/
theorem b2_parallel_exceptional_forces_33
    (Item : Type) [DecidableEq Item]
    (m2Chores firstType secondType : Finset Item) (first second surviving : Item) (q : ℕ)
    (hfirstSubset : firstType ⊆ m2Chores) (hsecondSubset : secondType ⊆ m2Chores)
    (htypesDisjoint : Disjoint firstType secondType)
    (hfirst : first ∈ firstType) (hsecond : second ∈ firstType)
    (hsurviving : surviving ∈ firstType) (hfirstNeSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second} = {surviving} ∪ secondType)
    (hsecondCardFormula : secondType.card = 4 * q + 3)
    (hmaximum : secondType.card ≤ firstType.card) :
    m2Chores = firstType ∪ secondType ∧ firstType.card = 3 ∧ secondType.card = 3 := by
  have hsurvivingResidue : surviving ∈ m2Chores \ {first, second} := by
    rw [hresidue]
    simp
  have hsurvivingNotGap : surviving ∉ ({first, second} : Finset Item) :=
    (Finset.mem_sdiff.mp hsurvivingResidue).2
  have hsurvivingNeFirst : surviving ≠ first := by
    intro hEq
    subst surviving
    exact hsurvivingNotGap (by simp)
  have hsurvivingNeSecond : surviving ≠ second := by
    intro hEq
    subst surviving
    exact hsurvivingNotGap (by simp)
  have hfirstTypeEq : firstType = {first, second, surviving} := by
    apply Finset.Subset.antisymm
    · intro item hitem
      by_cases hgap : item ∈ ({first, second} : Finset Item)
      · rcases Finset.mem_insert.mp hgap with rfl | hsecondItem
        · simp
        · have hEq : item = second := Finset.mem_singleton.mp hsecondItem
          subst item
          simp
      · have hresidueItem : item ∈ m2Chores \ {first, second} :=
          Finset.mem_sdiff.mpr ⟨hfirstSubset hitem, hgap⟩
        rw [hresidue] at hresidueItem
        rcases Finset.mem_union.mp hresidueItem with hsurvivingItem | hsecondItem
        · have hEq : item = surviving := by simpa using hsurvivingItem
          simpa [hEq]
        · exact (Finset.disjoint_left.mp htypesDisjoint hitem hsecondItem).elim
    · intro item hitem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hitem
      rcases hitem with rfl | rfl | rfl
      · exact hfirst
      · exact hsecond
      · exact hsurviving
  have hfirstCard : firstType.card = 3 := by
    rw [hfirstTypeEq]
    simp [hfirstNeSecond, Ne.symm hsurvivingNeFirst, Ne.symm hsurvivingNeSecond]
  have hqZero : q = 0 := by
    rw [hsecondCardFormula, hfirstCard] at hmaximum
    omega
  have hsecondCard : secondType.card = 3 := by
    rw [hsecondCardFormula, hqZero]
  refine ⟨?_, hfirstCard, hsecondCard⟩
  apply Finset.Subset.antisymm
  · intro item hitem
    by_cases hgap : item ∈ ({first, second} : Finset Item)
    · rcases (by simpa using hgap : item = first ∨ item = second) with rfl | rfl
      · exact Finset.mem_union_left _ hfirst
      · exact Finset.mem_union_left _ hsecond
    · have hresidueItem : item ∈ m2Chores \ {first, second} :=
        Finset.mem_sdiff.mpr ⟨hitem, hgap⟩
      rw [hresidue] at hresidueItem
      rcases Finset.mem_union.mp hresidueItem with hsurvivingItem | hsecondItem
      · have hEq : item = surviving := by simpa using hsurvivingItem
        rw [hEq]
        exact Finset.mem_union_left _ hsurviving
      · exact Finset.mem_union_right _ hsecondItem
  · intro item hitem
    rcases Finset.mem_union.mp hitem with hfirstItem | hsecondItem
    · exact hfirstSubset hfirstItem
    · exact hsecondSubset hsecondItem

/-- With a `4a+2` canonical prefix, fixing one short agent in each of two
disjoint pairs forces the two remaining agents to be long.  This is the quota
bookkeeping used after the source's within-pair relabelling. -/
theorem b2_remaining_quotas_are_long
    (a : ℕ) (quota : Fin 4 → ℕ)
    (hquota : ∀ agent, quota agent = a ∨ quota agent = a + 1)
    (hsum : Finset.univ.sum quota = 4 * a + 2)
    (hzero : quota 0 = a) (htwo : quota 2 = a) :
    quota 1 = a + 1 ∧ quota 3 = a + 1 := by
  have hsum' : quota 0 + quota 1 + quota 2 + quota 3 = 4 * a + 2 := by
    simpa [Fin.sum_univ_four] using hsum
  rcases hquota 1 with hzeroOrOne | hzeroOrOne
  · rcases hquota 3 with hthreeOrOne | hthreeOrOne
    · omega
    · omega
  · rcases hquota 3 with hthreeOrOne | hthreeOrOne
    · omega
    · exact ⟨hzeroOrOne, hthreeOrOne⟩

/-- The source-to-model bridge for the tight exceptional branch of Case
B.3.1.  Once the residual exceptional pair is the type used for the original
two-chore gap fill, its literal residual shape and maximum-multiplicity bound
invoke `b2_parallel_exceptional_forces_33`, then the direct `3+3` schedule. -/
theorem existsEfxOfB2TightExceptionalDirect_of_exceptionalResidue
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (first second surviving : Item) (q : ℕ)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsurviving : surviving ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second} = {surviving} ∪
      m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hresidueCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card =
      4 * q + 3)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let firstType := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let secondType := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have hfirstSubset : firstType ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
      (by simpa [firstType] using hitem) |>.1
  have hsecondSubset : secondType ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
      (by simpa [secondType] using hitem) |>.1
  have htypesDisjoint : Disjoint firstType secondType := by
    simpa [firstType, secondType] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  obtain ⟨hcover, hfirstCard, hsecondCard⟩ :=
    b2_parallel_exceptional_forces_33 Item m2Chores firstType secondType first second surviving q
      hfirstSubset hsecondSubset htypesDisjoint (by simpa [firstType] using hfirst)
      (by simpa [firstType] using hsecond) (by simpa [firstType] using hsurviving)
      hfirstNeSecond (by simpa [firstType, secondType] using hresidue)
      (by simpa [secondType] using hresidueCard)
      (by simpa [firstType, secondType] using hmaximum ({2, 3} : Finset (Fin 4)))
  apply existsEfxOfB2TightExceptionalDirect Item r cost prefixChores m2Chores firstType
    secondType a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
    hquota3 hsuper hcover htypesDisjoint hfirstCard hsecondCard
  · intro item hitem
    have hitem' : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
      simpa [firstType] using hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 0 hitem' (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 1 hitem' (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 2 hcost hitem' (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 3 hcost hitem' (by decide)
  · intro item hitem
    have hitem' : item ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) := by
      simpa [secondType] using hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 0 hcost hitem' (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 1 hcost hitem' (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 2 hitem' (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 3 hitem' (by decide)

/-- The same tight direct allocation stated with the library's M₂ type-pool
definitions.  This is the bridge from the source's two labelled edge types to
the explicit `{1,r}` table used by the direct schedule. -/
theorem existsEfxOfB2TightExceptionalDirect_of_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 3)
    (hsecondCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  refine existsEfxOfB2TightExceptionalDirect Item r cost prefixChores m2Chores
    (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
    hsuper hcover
    (m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
    hfirstCard hsecondCard ?_ ?_
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 0 hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 1 hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) item 3 hcost hitem (by decide)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 0 hcost hitem (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 2 hitem (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 3 hitem (by decide)

/-- The tight direct schedule transported across a relabelling.  The labels
map the displayed source agents `0,1,2,3` to the agents in the input
instance, so this is the formal `without loss of generality` bridge for the
two endpoint pairs. -/
theorem existsEfxOfB2TightExceptionalDirect_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a + 1) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores =
      m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card = 3)
    (hsecondCard : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2TightExceptionalDirect_of_typePools Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a
    (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota] using hquota0
  · simpa [relabelQuota] using hquota1
  · simpa [relabelQuota] using hquota2
  · simpa [relabelQuota] using hquota3
  · intro short long hshort hlong
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) (labels long) (by simpa [relabelQuota] using hshort)
        (by simpa [relabelQuota] using hlong)
  · exact hcover
  · exact hfirstCard
  · exact hsecondCard

end HT26EFXChores
