import HT26EFXChores.B2TightExceptionalAllocation

/-!
# A controlled-suffix EFX kernel for source Case B.3.2

The simple-graph branches of the `b = 2` case all use a super-canonical
prefix with two short and two long agents.  This module factors out their
common EFX argument: once the direct suffix has empty long bundles and each
short bundle has the displayed one-unit comparison certificate, every
remaining EFX comparison is automatic.

Source: `EFXadditivechores.tex`, lines 2684--2967.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A direct suffix combines with a two-short/two-long super-canonical prefix
when the long suffixes are empty and each short final bundle is within one
unit of every comparison bundle. -/
theorem efxForChores_union_of_supercanonicalShort01AndControlledSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores suffixChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixSuffix : Disjoint prefixChores suffixChores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (_hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsuffixAllocation : IsAllocationOf suffix suffixChores)
    (hsuffixTwo : suffix 2 = ∅) (hsuffixThree : suffix 3 = ∅)
    (hshortUnit : ∀ short : Fin 4, short = 0 ∨ short = 1 → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ suffixChores) ∧
      EFXForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ suffix agent) := by
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixSuffix
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores suffixChores hprefixSuffix
    hcanonical.1 hsuffixAllocation, ?_⟩
  intro agent other
  fin_cases agent
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 0 ((prefixAllocation 0 ∪ suffix 0).erase item) ≤
      additiveChoreCost cost 0 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 0 ∪ suffix 0 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 0 (prefixAllocation 0 ∪ suffix 0) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 0 (Or.inl rfl) other, hcostLower 0 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 1 ((prefixAllocation 1 ∪ suffix 1).erase item) ≤
      additiveChoreCost cost 1 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 1 ∪ suffix 1 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 1 (prefixAllocation 1 ∪ suffix 1) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 1 (Or.inr rfl) other, hcostLower 1 item]
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
  · by_cases hempty : prefixAllocation 3 = ∅
    · left
      simpa [hsuffixThree] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 3 := by simpa [hsuffixThree] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX 3 other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
          additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem
        rw [hsuffixThree, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' : additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
            additiveChoreCost cost 3 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
              additiveChoreCost cost 3 (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost 3 other]
            have hnonneg : 0 ≤ additiveChoreCost cost 3 (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (suffix other)
            linarith

/-- A two-pool direct schedule for the simple-graph branch.  It is the common
numerical core of source Case B.3.2(a) when no M₂ chore is given to a long
agent: the first short agent has at most three own-small chores, the second
at most two, and each sees a large chore in the other's suffix. -/
theorem existsEfxOfB2SimpleGraphControlledShortPools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores leftPool rightPool : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores = leftPool ∪ rightPool)
    (hdisjoint : Disjoint leftPool rightPool)
    (hleftCard : leftPool.card ≤ 3) (hrightCard : rightPool.card ≤ 2)
    (hleftSmall : ∀ item ∈ leftPool, IsSmallChore cost 0 item)
    (hrightSmall : ∀ item ∈ rightPool, IsSmallChore cost 1 item)
    (hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool)
    (hrightLargeForZero : r ≤ additiveChoreCost cost 0 rightPool) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 leftPool
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 rightPool
  let suffix : Allocation (Fin 4) Item := fun agent => suffixZero agent ∪ suffixOne agent
  have hsuffixZeroAllocation : IsAllocationOf suffixZero leftPool :=
    isAllocationOf_allocateAllTo 0 leftPool
  have hsuffixOneAllocation : IsAllocationOf suffixOne rightPool :=
    isAllocationOf_allocateAllTo 1 rightPool
  have hsuffixAllocation : IsAllocationOf suffix m2Chores := by
    rw [hcover]
    simpa [suffix] using isAllocationOf_union suffixZero suffixOne leftPool rightPool hdisjoint
      hsuffixZeroAllocation hsuffixOneAllocation
  have hsuffixZero : suffix 0 = leftPool := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixOne : suffix 1 = rightPool := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixTwo : suffix 2 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixThree : suffix 3 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hprefixEqual : ∀ first second : Fin 4, quota first = quota second →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hquota
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second hquota
  have hleftOwn : additiveChoreCost cost 0 (suffix 0) = leftPool.card := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 0 leftPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simpa [IsSmallChore] using hleftSmall item hitem
  have hrightOwn : additiveChoreCost cost 1 (suffix 1) = rightPool.card := by
    rw [hsuffixOne, additiveChoreCost_eq_card_nsmul_of_constant cost 1 rightPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simpa [IsSmallChore] using hrightSmall item hitem
  have hleftOwnUpper : additiveChoreCost cost 0 (suffix 0) ≤ 3 := by
    rw [hleftOwn]
    exact_mod_cast hleftCard
  have hrightOwnUpper : additiveChoreCost cost 1 (suffix 1) ≤ 2 := by
    rw [hrightOwn]
    exact_mod_cast hrightCard
  have hrightLargeForZero' : r ≤ additiveChoreCost cost 0 (suffix 1) := by
    simpa [hsuffixOne] using hrightLargeForZero
  have hleftLargeForOne' : r ≤ additiveChoreCost cost 1 (suffix 0) := by
    simpa [hsuffixZero] using hleftLargeForOne
  have hshortUnit : ∀ short : Fin 4, short = 0 ∨ short = 1 → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    rcases hshort with rfl | rfl
    · fin_cases other
      · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) ≤
          additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) + 1
        linarith
      · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) ≤
          additiveChoreCost cost 0 (prefixAllocation 1 ∪ suffix 1) + 1
        rw [hfinalCost 0 0, hfinalCost 0 1]
        linarith [hprefixEqual 0 1 (by rw [hquota0, hquota1])]
      · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) ≤
          additiveChoreCost cost 0 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 0 0, hfinalCost 0 2, hsuffixTwo]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 0 2 (by rw [hquota0]) (by rw [hquota2])]
      · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) ≤
          additiveChoreCost cost 0 (prefixAllocation 3 ∪ suffix 3) + 1
        rw [hfinalCost 0 0, hfinalCost 0 3, hsuffixThree]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 0 3 (by rw [hquota0]) (by rw [hquota3])]
    · fin_cases other
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 1 1, hfinalCost 1 0]
        linarith [hprefixEqual 1 0 (by rw [hquota1, hquota0])]
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) + 1
        linarith
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 1 1, hfinalCost 1 2, hsuffixTwo]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 1 2 (by rw [hquota1]) (by rw [hquota2])]
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 3 ∪ suffix 3) + 1
        rw [hfinalCost 1 1, hfinalCost 1 3, hsuffixThree]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 1 3 (by rw [hquota1]) (by rw [hquota3])]
  refine ⟨fun agent => prefixAllocation agent ∪ suffix agent, ?_, ?_⟩
  · exact efxForChores_union_of_supercanonicalShort01AndControlledSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixTwo hsuffixThree
      hshortUnit |>.1
  · exact efxForChores_union_of_supercanonicalShort01AndControlledSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixTwo hsuffixThree
      hshortUnit |>.2

/-- A direct simple-graph suffix may contain a large chore on a short bundle.
The source calculations only need two numerical facts: every short suffix has
cost at most `r + 1` to its owner, and removing one unit of cost from it is
covered by the other short suffix.  With no suffix chore on a long bundle,
these facts combine with super-canonicity to prove EFX. -/
theorem efxForChores_union_of_supercanonicalShort01AndBoundedSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores suffixChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixSuffix : Disjoint prefixChores suffixChores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsuffixAllocation : IsAllocationOf suffix suffixChores)
    (hsuffixTwo : suffix 2 = ∅) (hsuffixThree : suffix 3 = ∅)
    (hshortBound : ∀ short : Fin 4, short = 0 ∨ short = 1 →
      additiveChoreCost cost short (suffix short) ≤ r + 1)
    (hshortComparison : ∀ short other : Fin 4, short = 0 ∨ short = 1 →
      other = 0 ∨ other = 1 → short ≠ other →
      additiveChoreCost cost short (suffix short) - 1 ≤
        additiveChoreCost cost short (suffix other)) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ suffixChores) ∧
      EFXForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ suffix agent) := by
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixSuffix
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
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
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores suffixChores hprefixSuffix
    hcanonical.1 hsuffixAllocation, ?_⟩
  intro agent other
  fin_cases agent
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 0 ((prefixAllocation 0 ∪ suffix 0).erase item) ≤
      additiveChoreCost cost 0 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 0 ∪ suffix 0 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 0 (prefixAllocation 0 ∪ suffix 0) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    fin_cases other
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0)
      rw [hfinalCost 0 0]
      have hnonneg : 0 ≤ cost 0 item := by linarith [hcostLower 0 item]
      linarith
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 1 ∪ suffix 1)
      rw [hfinalCost 0 0, hfinalCost 0 1]
      linarith [hprefixEqual 0 1 (by rw [hquota0, hquota1]),
        hshortComparison 0 1 (Or.inl rfl) (Or.inr rfl) (by decide), hcostLower 0 item]
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 2 ∪ suffix 2)
      rw [hfinalCost 0 0, hfinalCost 0 2, hsuffixTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 2 (by rw [hquota0]) (by rw [hquota2]),
        hshortBound 0 (Or.inl rfl), hcostLower 0 item]
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 3 ∪ suffix 3)
      rw [hfinalCost 0 0, hfinalCost 0 3, hsuffixThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 3 (by rw [hquota0]) (by rw [hquota3]),
        hshortBound 0 (Or.inl rfl), hcostLower 0 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 1 ((prefixAllocation 1 ∪ suffix 1).erase item) ≤
      additiveChoreCost cost 1 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 1 ∪ suffix 1 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 1 (prefixAllocation 1 ∪ suffix 1) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    fin_cases other
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 0 ∪ suffix 0)
      rw [hfinalCost 1 1, hfinalCost 1 0]
      linarith [hprefixEqual 1 0 (by rw [hquota1, hquota0]),
        hshortComparison 1 0 (Or.inr rfl) (Or.inl rfl) (by decide), hcostLower 1 item]
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1)
      rw [hfinalCost 1 1]
      have hnonneg : 0 ≤ cost 1 item := by linarith [hcostLower 1 item]
      linarith
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 2 ∪ suffix 2)
      rw [hfinalCost 1 1, hfinalCost 1 2, hsuffixTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 1 2 (by rw [hquota1]) (by rw [hquota2]),
        hshortBound 1 (Or.inr rfl), hcostLower 1 item]
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 3 ∪ suffix 3)
      rw [hfinalCost 1 1, hfinalCost 1 3, hsuffixThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 1 3 (by rw [hquota1]) (by rw [hquota3]),
        hshortBound 1 (Or.inr rfl), hcostLower 1 item]
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
  · by_cases hempty : prefixAllocation 3 = ∅
    · left
      simpa [hsuffixThree] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 3 := by simpa [hsuffixThree] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX 3 other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
          additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem
        rw [hsuffixThree, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' : additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
            additiveChoreCost cost 3 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
              additiveChoreCost cost 3 (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost 3 other]
            have hnonneg : 0 ≤ additiveChoreCost cost 3 (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 3 (suffix other)
            linarith

/-- The B.3.2 schedules that give one small M₂ chore to long agent `2` use the
same short-side bounds.  The long agent's suffix has cost one; every short
comparison is made at least `r` more costly for her, and the other long agent
has an empty suffix. -/
theorem efxForChores_union_of_supercanonicalShort01AndBoundedSuffixWithSmallLong2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores suffixChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixSuffix : Disjoint prefixChores suffixChores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsuffixAllocation : IsAllocationOf suffix suffixChores)
    (hsuffixThree : suffix 3 = ∅)
    (hlongTwoCost : additiveChoreCost cost 2 (suffix 2) = 1)
    (hlongTwoShortLarge : ∀ short : Fin 4, short = 0 ∨ short = 1 →
      r ≤ additiveChoreCost cost 2 (suffix short))
    (hshortBound : ∀ short : Fin 4, short = 0 ∨ short = 1 →
      additiveChoreCost cost short (suffix short) ≤ r + 1)
    (hshortComparison : ∀ short other : Fin 4, short = 0 ∨ short = 1 →
      other = 0 ∨ other = 1 → short ≠ other →
      additiveChoreCost cost short (suffix short) - 1 ≤
        additiveChoreCost cost short (suffix other)) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ suffixChores) ∧
      EFXForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ suffix agent) := by
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixSuffix
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
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
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hcostNonneg : ∀ agent item, 0 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores suffixChores hprefixSuffix
    hcanonical.1 hsuffixAllocation, ?_⟩
  intro agent other
  fin_cases agent
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 0 ((prefixAllocation 0 ∪ suffix 0).erase item) ≤
      additiveChoreCost cost 0 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 0 ∪ suffix 0 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 0 (prefixAllocation 0 ∪ suffix 0) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    fin_cases other
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0)
      rw [hfinalCost 0 0]
      linarith [hcostLower 0 item]
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 1 ∪ suffix 1)
      rw [hfinalCost 0 0, hfinalCost 0 1]
      linarith [hprefixEqual 0 1 (by rw [hquota0, hquota1]),
        hshortComparison 0 1 (Or.inl rfl) (Or.inr rfl) (by decide), hcostLower 0 item]
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 2 ∪ suffix 2)
      rw [hfinalCost 0 0, hfinalCost 0 2]
      have hnonneg : 0 ≤ additiveChoreCost cost 0 (suffix 2) :=
        additiveChoreCost_nonneg cost hcostNonneg 0 (suffix 2)
      linarith [hsuper 0 2 (by rw [hquota0]) (by rw [hquota2]),
        hshortBound 0 (Or.inl rfl), hcostLower 0 item]
    · change additiveChoreCost cost 0 (prefixAllocation 0 ∪ suffix 0) - cost 0 item ≤
          additiveChoreCost cost 0 (prefixAllocation 3 ∪ suffix 3)
      rw [hfinalCost 0 0, hfinalCost 0 3, hsuffixThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 3 (by rw [hquota0]) (by rw [hquota3]),
        hshortBound 0 (Or.inl rfl), hcostLower 0 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 1 ((prefixAllocation 1 ∪ suffix 1).erase item) ≤
      additiveChoreCost cost 1 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 1 ∪ suffix 1 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 1 (prefixAllocation 1 ∪ suffix 1) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    fin_cases other
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 0 ∪ suffix 0)
      rw [hfinalCost 1 1, hfinalCost 1 0]
      linarith [hprefixEqual 1 0 (by rw [hquota1, hquota0]),
        hshortComparison 1 0 (Or.inr rfl) (Or.inl rfl) (by decide), hcostLower 1 item]
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1)
      rw [hfinalCost 1 1]
      linarith [hcostLower 1 item]
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 2 ∪ suffix 2)
      rw [hfinalCost 1 1, hfinalCost 1 2]
      have hnonneg : 0 ≤ additiveChoreCost cost 1 (suffix 2) :=
        additiveChoreCost_nonneg cost hcostNonneg 1 (suffix 2)
      linarith [hsuper 1 2 (by rw [hquota1]) (by rw [hquota2]),
        hshortBound 1 (Or.inr rfl), hcostLower 1 item]
    · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) - cost 1 item ≤
          additiveChoreCost cost 1 (prefixAllocation 3 ∪ suffix 3)
      rw [hfinalCost 1 1, hfinalCost 1 3, hsuffixThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 1 3 (by rw [hquota1]) (by rw [hquota3]),
        hshortBound 1 (Or.inr rfl), hcostLower 1 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2).erase item) ≤
      additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 2 ∪ suffix 2 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 2 (prefixAllocation 2 ∪ suffix 2) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    fin_cases other
    · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) - cost 2 item ≤
          additiveChoreCost cost 2 (prefixAllocation 0 ∪ suffix 0)
      rw [hfinalCost 2 2, hfinalCost 2 0]
      linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith)
        2 0, hlongTwoCost, hlongTwoShortLarge 0 (Or.inl rfl), hcostLower 2 item]
    · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) - cost 2 item ≤
          additiveChoreCost cost 2 (prefixAllocation 1 ∪ suffix 1)
      rw [hfinalCost 2 2, hfinalCost 2 1]
      linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith)
        2 1, hlongTwoCost, hlongTwoShortLarge 1 (Or.inr rfl), hcostLower 2 item]
    · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) - cost 2 item ≤
          additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2)
      rw [hfinalCost 2 2]
      linarith [hcostLower 2 item]
    · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) - cost 2 item ≤
          additiveChoreCost cost 2 (prefixAllocation 3 ∪ suffix 3)
      rw [hfinalCost 2 2, hfinalCost 2 3, hsuffixThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hprefixEqual 2 3 (by rw [hquota2, hquota3]), hlongTwoCost,
        hcostLower 2 item]
  · by_cases hempty : prefixAllocation 3 = ∅
    · left
      simpa [hsuffixThree] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 3 := by simpa [hsuffixThree] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX 3 other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
          additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem
        rw [hsuffixThree, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' : additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
            additiveChoreCost cost 3 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 3 (prefixAllocation 3) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 3 (prefixAllocation 3) - cost 3 item ≤
              additiveChoreCost cost 3 (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost 3 other]
            have hnonneg : 0 ≤ additiveChoreCost cost 3 (suffix other) :=
              additiveChoreCost_nonneg cost hcostNonneg 3 (suffix other)
            linarith

/-- A direct suffix constructor for the B.3.2 schedules that give a single
small suffix bundle to long agent `2`. -/
theorem existsEfxOfB2SimpleGraphBoundedShortPoolsWithSmallLong2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores leftPool rightPool longPool : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores = (leftPool ∪ rightPool) ∪ longPool)
    (hshortDisjoint : Disjoint leftPool rightPool)
    (hlongDisjoint : Disjoint (leftPool ∪ rightPool) longPool)
    (hlongTwoCost : additiveChoreCost cost 2 longPool = 1)
    (hlongTwoLeftLarge : r ≤ additiveChoreCost cost 2 leftPool)
    (hlongTwoRightLarge : r ≤ additiveChoreCost cost 2 rightPool)
    (hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1)
    (hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1)
    (hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 rightPool)
    (hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 leftPool) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 leftPool
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 rightPool
  let suffixTwo : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 longPool
  let shortSuffix : Allocation (Fin 4) Item := fun agent => suffixZero agent ∪ suffixOne agent
  let suffix : Allocation (Fin 4) Item := fun agent => shortSuffix agent ∪ suffixTwo agent
  have hzeroAllocation : IsAllocationOf suffixZero leftPool :=
    isAllocationOf_allocateAllTo 0 leftPool
  have honeAllocation : IsAllocationOf suffixOne rightPool :=
    isAllocationOf_allocateAllTo 1 rightPool
  have htwoAllocation : IsAllocationOf suffixTwo longPool :=
    isAllocationOf_allocateAllTo 2 longPool
  have hshortAllocation : IsAllocationOf shortSuffix (leftPool ∪ rightPool) := by
    simpa [shortSuffix] using isAllocationOf_union suffixZero suffixOne leftPool rightPool
      hshortDisjoint hzeroAllocation honeAllocation
  have hsuffixAllocation : IsAllocationOf suffix m2Chores := by
    rw [hcover]
    simpa [suffix] using isAllocationOf_union shortSuffix suffixTwo (leftPool ∪ rightPool)
      longPool hlongDisjoint hshortAllocation htwoAllocation
  have hsuffixZero : suffix 0 = leftPool := by
    simp [suffix, shortSuffix, suffixZero, suffixOne, suffixTwo, allocateAllTo]
  have hsuffixOne : suffix 1 = rightPool := by
    simp [suffix, shortSuffix, suffixZero, suffixOne, suffixTwo, allocateAllTo]
  have hsuffixTwo : suffix 2 = longPool := by
    simp [suffix, shortSuffix, suffixZero, suffixOne, suffixTwo, allocateAllTo]
  have hsuffixThree : suffix 3 = ∅ := by
    simp [suffix, shortSuffix, suffixZero, suffixOne, suffixTwo, allocateAllTo]
  have hshortBound : ∀ short : Fin 4, short = 0 ∨ short = 1 →
      additiveChoreCost cost short (suffix short) ≤ r + 1 := by
    intro short hshort
    rcases hshort with rfl | rfl
    · simpa [hsuffixZero] using hleftBound
    · simpa [hsuffixOne] using hrightBound
  have hshortComparison : ∀ short other : Fin 4, short = 0 ∨ short = 1 →
      other = 0 ∨ other = 1 → short ≠ other →
      additiveChoreCost cost short (suffix short) - 1 ≤
        additiveChoreCost cost short (suffix other) := by
    intro short other hshort hother hne
    rcases hshort with rfl | rfl <;> rcases hother with rfl | rfl
    · exact (hne rfl).elim
    · simpa [hsuffixZero, hsuffixOne] using hleftComparison
    · simpa [hsuffixZero, hsuffixOne] using hrightComparison
    · exact (hne rfl).elim
  obtain ⟨hfinalAllocation, hfinalEFX⟩ :=
    efxForChores_union_of_supercanonicalShort01AndBoundedSuffixWithSmallLong2
      Item r cost prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixThree
      (by simpa [hsuffixTwo] using hlongTwoCost)
      (by intro short hshort; rcases hshort with rfl | rfl
          · simpa [hsuffixZero] using hlongTwoLeftLarge
          · simpa [hsuffixOne] using hlongTwoRightLarge)
      hshortBound hshortComparison
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent, hfinalAllocation, hfinalEFX⟩

/-- A two-pool suffix constructor for the direct simple-graph schedules that
place every M₂ chore on a short agent.  The four displayed bounds are exactly
the numerical source checks after a suffix chore is removed. -/
theorem existsEfxOfB2SimpleGraphBoundedShortPools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores leftPool rightPool : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hcover : m2Chores = leftPool ∪ rightPool)
    (hdisjoint : Disjoint leftPool rightPool)
    (hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1)
    (hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1)
    (hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 rightPool)
    (hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 leftPool) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 leftPool
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 rightPool
  let suffix : Allocation (Fin 4) Item := fun agent => suffixZero agent ∪ suffixOne agent
  have hsuffixZeroAllocation : IsAllocationOf suffixZero leftPool :=
    isAllocationOf_allocateAllTo 0 leftPool
  have hsuffixOneAllocation : IsAllocationOf suffixOne rightPool :=
    isAllocationOf_allocateAllTo 1 rightPool
  have hsuffixAllocation : IsAllocationOf suffix m2Chores := by
    rw [hcover]
    simpa [suffix] using isAllocationOf_union suffixZero suffixOne leftPool rightPool hdisjoint
      hsuffixZeroAllocation hsuffixOneAllocation
  have hsuffixZero : suffix 0 = leftPool := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixOne : suffix 1 = rightPool := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixTwo : suffix 2 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixThree : suffix 3 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hshortBound : ∀ short : Fin 4, short = 0 ∨ short = 1 →
      additiveChoreCost cost short (suffix short) ≤ r + 1 := by
    intro short hshort
    rcases hshort with rfl | rfl
    · simpa [hsuffixZero] using hleftBound
    · simpa [hsuffixOne] using hrightBound
  have hshortComparison : ∀ short other : Fin 4, short = 0 ∨ short = 1 →
      other = 0 ∨ other = 1 → short ≠ other →
      additiveChoreCost cost short (suffix short) - 1 ≤
        additiveChoreCost cost short (suffix other) := by
    intro short other hshort hother hne
    rcases hshort with rfl | rfl <;> rcases hother with rfl | rfl
    · exact (hne rfl).elim
    · simpa [hsuffixZero, hsuffixOne] using hleftComparison
    · simpa [hsuffixZero, hsuffixOne] using hrightComparison
    · exact (hne rfl).elim
  obtain ⟨hfinalAllocation, hfinalEFX⟩ :=
    efxForChores_union_of_supercanonicalShort01AndBoundedSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixTwo hsuffixThree
      hshortBound hshortComparison
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent, hfinalAllocation, hfinalEFX⟩

/-- Source Case B.3.2(a) when both short sides have a cross edge and the
long--long type is absent.  Every existing type is allocated to a short
endpoint: type `(0,1)` and the two cross types incident to `0` go to `0`, and
the two cross types incident to `1` go to `1`.  Simplicity gives the `3:2`
cardinality bounds needed by the controlled-short-pools kernel. -/
theorem existsEfxOfB2SimpleGraph_crossBoth_noLongType
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossZero : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOne : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (hlongEmpty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let leftPool := (pool01 ∪ pool02) ∪ pool03
  let rightPool := pool12 ∪ pool13
  have hpool01Card : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool02Card : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03Card : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool12Card : pool12.card ≤ 1 := hsimple ({1, 2} : Finset (Fin 4)) (by decide)
  have hpool13Card : pool13.card ≤ 1 := hsimple ({1, 3} : Finset (Fin 4)) (by decide)
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = leftPool ∪ rightPool := by
    simpa [hm2IsPool, leftPool, rightPool, pool01, pool02, pool03, pool12, pool13,
      hlongEmpty, Finset.union_assoc] using
      (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
  have hdisjoint : Disjoint leftPool rightPool := by
    rw [Finset.disjoint_left]
    intro item hleft hright
    simp only [leftPool, rightPool, Finset.mem_union] at hleft hright
    rcases hleft with (h01 | h02) | h03
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h01 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h01 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h02 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h02 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h03 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h03 h13).elim
  have hleftCard : leftPool.card ≤ 3 := by
    calc
      leftPool.card ≤ (pool01 ∪ pool02).card + pool03.card := Finset.card_union_le _ _
      _ ≤ (pool01.card + pool02.card) + pool03.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ 3 := by omega
  have hrightCard : rightPool.card ≤ 2 := by
    calc
      rightPool.card ≤ pool12.card + pool13.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hleftSmall : ∀ item ∈ leftPool, IsSmallChore cost 0 item := by
    intro item hitem
    simp only [leftPool, Finset.mem_union] at hitem
    rcases hitem with (h01 | h02) | h03
    · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 0 h01 (by simp)
    · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
        item 0 h02 (by simp)
    · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
        item 0 h03 (by simp)
  have hrightSmall : ∀ item ∈ rightPool, IsSmallChore cost 1 item := by
    intro item hitem
    simp only [rightPool, Finset.mem_union] at hitem
    rcases hitem with h12 | h13
    · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
        item 1 h12 (by simp)
    · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 3} : Finset (Fin 4))
        item 1 h13 (by simp)
  have hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool := by
    obtain ⟨item, hitem⟩ := hcrossZero
    simp only [Finset.mem_union] at hitem
    rcases hitem with h02 | h03
    · have hleft : item ∈ leftPool := by
        simp only [leftPool, Finset.mem_union]
        exact Or.inl (Or.inr h02)
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 2} : Finset (Fin 4)) item 1 hcost h02 (by decide)
      change cost 1 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hleft
    · have hleft : item ∈ leftPool := by
        simp only [leftPool, Finset.mem_union]
        exact Or.inr h03
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 3} : Finset (Fin 4)) item 1 hcost h03 (by decide)
      change cost 1 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hleft
  have hrightLargeForZero : r ≤ additiveChoreCost cost 0 rightPool := by
    obtain ⟨item, hitem⟩ := hcrossOne
    simp only [Finset.mem_union] at hitem
    rcases hitem with h12 | h13
    · have hright : item ∈ rightPool := by
        simp only [rightPool, Finset.mem_union]
        exact Or.inl h12
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 2} : Finset (Fin 4)) item 0 hcost h12 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hright
    · have hright : item ∈ rightPool := by
        simp only [rightPool, Finset.mem_union]
        exact Or.inr h13
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 3} : Finset (Fin 4)) item 0 hcost h13 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hright
  exact existsEfxOfB2SimpleGraphControlledShortPools Item r cost prefixChores m2Chores
    leftPool rightPool a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftCard hrightCard hleftSmall hrightSmall
    hleftLargeForOne hrightLargeForZero

/-- Source Case B.3.2(a) with no type `(0,1)` chore and a type `(2,3)` chore,
when short agent `0` has at most one cross chore.  The long--long chore is
given to that sparse short agent.  The remaining cross chores certify the two
short-to-short comparisons, while super-canonicity handles both long agents. -/
theorem existsEfxOfB2SimpleGraph_noShortType_longType_to_sparseZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hshortEmpty : m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) = ∅)
    (hcrossZero : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOne : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (hzeroCrossCard : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card ≤ 1)
    (hlongNonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let crossZero := pool02 ∪ pool03
  let rightPool := pool12 ∪ pool13
  let leftPool := pool23 ∪ crossZero
  have hpool12Card : pool12.card ≤ 1 := hsimple ({1, 2} : Finset (Fin 4)) (by decide)
  have hpool13Card : pool13.card ≤ 1 := hsimple ({1, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using hlongNonempty
  have hpool23CardPos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
  have hpool23Card : pool23.card = 1 := by omega
  have hpool01Empty : pool01 = ∅ := by simpa [pool01] using hshortEmpty
  have hcrossZeroNonempty : crossZero.Nonempty := by simpa [crossZero, pool02, pool03] using hcrossZero
  have hcrossZeroCard' : crossZero.card ≤ 1 := by simpa [crossZero, pool02, pool03] using hzeroCrossCard
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = leftPool ∪ rightPool := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = leftPool ∪ rightPool := by
        dsimp [leftPool, rightPool, crossZero]
        rw [hpool01Empty]
        simp only [Finset.empty_union]
        ac_rfl
  have h23CrossDisjoint : Disjoint pool23 crossZero := by
    rw [Finset.disjoint_left]
    intro item h23 hcross
    simp only [crossZero, Finset.mem_union] at hcross
    rcases hcross with h02 | h03
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
          ({0, 2} : Finset (Fin 4)) (by decide)) h23 h02).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
          ({0, 3} : Finset (Fin 4)) (by decide)) h23 h03).elim
  have hdisjoint : Disjoint leftPool rightPool := by
    rw [Finset.disjoint_left]
    intro item hleft hright
    simp only [leftPool, crossZero, rightPool, Finset.mem_union] at hleft hright
    rcases hleft with h23 | h02 | h03
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h23 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h23 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h02 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h02 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h03 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h03 h13).elim
  have hrightCard : rightPool.card ≤ 2 := by
    calc
      rightPool.card ≤ pool12.card + pool13.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hcrossZeroOwn : additiveChoreCost cost 0 crossZero = crossZero.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 crossZero 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [crossZero, Finset.mem_union] at hitem
      rcases hitem with h02 | h03
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
  have hcrossZeroCost : additiveChoreCost cost 0 crossZero ≤ 1 := by
    rw [hcrossZeroOwn]
    exact_mod_cast hcrossZeroCard'
  have hrightOwn : additiveChoreCost cost 1 rightPool = rightPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 rightPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [rightPool, Finset.mem_union] at hitem
      rcases hitem with h12 | h13
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 1 h12 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 3} : Finset (Fin 4))
          item 1 h13 (by simp)
  have hrightCost : additiveChoreCost cost 1 rightPool ≤ 2 := by
    rw [hrightOwn]
    exact_mod_cast hrightCard
  have hpool23CostZero : additiveChoreCost cost 0 pool23 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool23 r]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
        item 0 hcost hitem (by decide)
  have hleftCostZero : additiveChoreCost cost 0 leftPool =
      additiveChoreCost cost 0 pool23 + additiveChoreCost cost 0 crossZero := by
    exact additiveChoreCost_union cost 0 pool23 crossZero h23CrossDisjoint
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftCostZero, hpool23CostZero]
    linarith
  have hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1 := by linarith
  have hrightLargeForZero : r ≤ additiveChoreCost cost 0 rightPool := by
    obtain ⟨item, hitem⟩ := hcrossOne
    simp only [Finset.mem_union] at hitem
    rcases hitem with h12 | h13
    · have hright : item ∈ rightPool := by
        change item ∈ pool12 ∪ pool13
        simpa [pool12, pool13] using Or.inl h12
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 2} : Finset (Fin 4)) item 0 hcost h12 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hright
    · have hright : item ∈ rightPool := by
        change item ∈ pool12 ∪ pool13
        simpa [pool12, pool13] using Or.inr h13
      have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 3} : Finset (Fin 4)) item 0 hcost h13 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hright
  have hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool := by
    obtain ⟨item, hitem⟩ := hpool23Nonempty
    have hleft : item ∈ leftPool := by simp [leftPool, hitem]
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({2, 3} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    change cost 1 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hleft
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 rightPool := by
    rw [hleftCostZero, hpool23CostZero]
    linarith
  have hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    linarith
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    leftPool rightPool a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(a) when all four cross types and the long--long type
exist.  The long--long chore is given to long agent `2`; cross types `(0,3)`
and `(1,3)` give that agent the required large chore on each short bundle. -/
theorem existsEfxOfB2SimpleGraph_fourCrosses_longType_to_longTwo
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h12Nonempty : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty)
    (h13Nonempty : (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let leftPool := (pool02 ∪ pool03) ∪ pool01
  let rightPool := pool12 ∪ pool13
  have hpool01Card : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool02Card : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03Card : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool12Card : pool12.card ≤ 1 := hsimple ({1, 2} : Finset (Fin 4)) (by decide)
  have hpool13Card : pool13.card ≤ 1 := hsimple ({1, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using h23Nonempty
  have hpool23CardPos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
  have hpool23Card : pool23.card = 1 := by omega
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = (leftPool ∪ rightPool) ∪ pool23 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = (leftPool ∪ rightPool) ∪ pool23 := by
        dsimp [leftPool, rightPool]
        ac_rfl
  have hshortDisjoint : Disjoint leftPool rightPool := by
    rw [Finset.disjoint_left]
    intro item hleft hright
    simp only [leftPool, rightPool, Finset.mem_union] at hleft hright
    rcases hleft with (h02 | h03) | h01
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h02 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h02 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h03 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h03 h13).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
            ({1, 2} : Finset (Fin 4)) (by decide)) h01 h12).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
            ({1, 3} : Finset (Fin 4)) (by decide)) h01 h13).elim
  have hlongDisjoint : Disjoint (leftPool ∪ rightPool) pool23 := by
    rw [Finset.disjoint_left]
    intro item hshort h23
    simp only [leftPool, rightPool, Finset.mem_union] at hshort
    rcases hshort with hleft | hright
    · rcases hleft with (h02 | h03) | h01
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h02 h23).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h01 h23).elim
    · rcases hright with h12 | h13
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({1, 2} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h12 h23).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({1, 3} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h13 h23).elim
  have hleftCard : leftPool.card ≤ 3 := by
    calc
      leftPool.card ≤ (pool02 ∪ pool03).card + pool01.card := Finset.card_union_le _ _
      _ ≤ (pool02.card + pool03.card) + pool01.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ 3 := by omega
  have hrightCard : rightPool.card ≤ 2 := by
    calc
      rightPool.card ≤ pool12.card + pool13.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hleftOwn : additiveChoreCost cost 0 leftPool = leftPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 leftPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [leftPool, Finset.mem_union] at hitem
      rcases hitem with (h02 | h03) | h01
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 0 h01 (by simp)
  have hrightOwn : additiveChoreCost cost 1 rightPool = rightPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 rightPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [rightPool, Finset.mem_union] at hitem
      rcases hitem with h12 | h13
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 1 h12 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 3} : Finset (Fin 4))
          item 1 h13 (by simp)
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftOwn]
    have hcard : (leftPool.card : ℝ) ≤ 3 := by exact_mod_cast hleftCard
    linarith
  have hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1 := by
    rw [hrightOwn]
    have hcard : (rightPool.card : ℝ) ≤ 2 := by exact_mod_cast hrightCard
    linarith
  have hpool23TwoCost : additiveChoreCost cost 2 pool23 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 2 pool23 1]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
        item 2 hitem (by simp)
  have hrightLargeForZero : r ≤ additiveChoreCost cost 0 rightPool := by
    obtain ⟨item, hitem⟩ := h12Nonempty
    have hright : item ∈ rightPool := by
      change item ∈ pool12 ∪ pool13
      simpa [pool12, pool13] using Or.inl hitem
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({1, 2} : Finset (Fin 4)) item 0 hcost hitem (by decide)
    change cost 0 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hright
  have hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool := by
    obtain ⟨item, hitem⟩ := h02Nonempty
    have hleft : item ∈ leftPool := by
      change item ∈ (pool02 ∪ pool03) ∪ pool01
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_union.mpr (Or.inl hitem)
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 2} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    change cost 1 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hleft
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 rightPool := by
    rw [hleftOwn]
    have hcard : (leftPool.card : ℝ) ≤ 3 := by exact_mod_cast hleftCard
    linarith
  have hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    rw [hrightOwn]
    have hcard : (rightPool.card : ℝ) ≤ 2 := by exact_mod_cast hrightCard
    linarith
  have hlongTwoLeftLarge : r ≤ additiveChoreCost cost 2 leftPool := by
    obtain ⟨item, hitem⟩ := h03Nonempty
    have hleft : item ∈ leftPool := by
      change item ∈ (pool02 ∪ pool03) ∪ pool01
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_union.mpr (Or.inr hitem)
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 3} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hleft
  have hlongTwoRightLarge : r ≤ additiveChoreCost cost 2 rightPool := by
    obtain ⟨item, hitem⟩ := h13Nonempty
    have hright : item ∈ rightPool := by
      change item ∈ pool12 ∪ pool13
      simpa [pool12, pool13] using Or.inr hitem
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({1, 3} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hright
  exact existsEfxOfB2SimpleGraphBoundedShortPoolsWithSmallLong2 Item r cost
    prefixChores m2Chores leftPool rightPool pool23 a quota prefixAllocation hr hcost hprefixM2
    hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hcover hshortDisjoint hlongDisjoint
    hpool23TwoCost hlongTwoLeftLarge hlongTwoRightLarge hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), two cross types at short agent `0`, with both
same-side types present.  The two cross chores go to `0`, the type `(0,1)`
chore goes to `1`, and the type `(2,3)` chore goes to long agent `2`. -/
theorem existsEfxOfB2SimpleGraph_twoZeroCrosses_bothSameTypes
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h01Nonempty : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).Nonempty)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let leftPool := pool02 ∪ pool03
  have hpool01CardLe : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool02CardLe : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool01Nonempty : pool01.Nonempty := by simpa [pool01] using h01Nonempty
  have hpool02Nonempty : pool02.Nonempty := by simpa [pool02] using h02Nonempty
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using h23Nonempty
  have hpool01Card : pool01.card = 1 := by
    have hpos : 0 < pool01.card := Finset.card_pos.mpr hpool01Nonempty
    omega
  have hpool02Card : pool02.card = 1 := by
    have hpos : 0 < pool02.card := Finset.card_pos.mpr hpool02Nonempty
    omega
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool23Card : pool23.card = 1 := by
    have hpos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
    omega
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = (leftPool ∪ pool01) ∪ pool23 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = (leftPool ∪ pool01) ∪ pool23 := by
        dsimp [leftPool]
        rw [hpool12Empty, hpool13Empty]
        simp only [Finset.union_empty]
        ac_rfl
  have hleftDisjoint : Disjoint pool02 pool03 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
      ({0, 3} : Finset (Fin 4)) (by decide)
  have hshortDisjoint : Disjoint leftPool pool01 := by
    rw [Finset.disjoint_left]
    intro item hleft h01
    simp only [leftPool, Finset.mem_union] at hleft
    rcases hleft with h02 | h03
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h02 h01).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h03 h01).elim
  have hlongDisjoint : Disjoint (leftPool ∪ pool01) pool23 := by
    rw [Finset.disjoint_left]
    intro item hshort h23
    simp only [leftPool, Finset.mem_union] at hshort
    rcases hshort with hleft | h01
    · rcases hleft with h02 | h03
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h02 h23).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
            ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h01 h23).elim
  have hleftCard : leftPool.card = 2 := by
    change (pool02 ∪ pool03).card = 2
    rw [Finset.card_union_of_disjoint hleftDisjoint, hpool02Card, hpool03Card]
  have hleftOwn : additiveChoreCost cost 0 leftPool = leftPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 leftPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [leftPool, Finset.mem_union] at hitem
      rcases hitem with h02 | h03
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
  have hpool01CostZero : additiveChoreCost cost 0 pool01 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool01 1]
    · simp [hpool01Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [hpool01Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hpool23TwoCost : additiveChoreCost cost 2 pool23 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 2 pool23 1]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
        item 2 hitem (by simp)
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftOwn, hleftCard]
    norm_num at ⊢
    linarith
  have hrightBound : additiveChoreCost cost 1 pool01 ≤ r + 1 := by
    rw [hpool01CostOne]
    linarith
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 pool01 := by
    rw [hleftOwn, hleftCard, hpool01CostZero]
    norm_num
  have hrightComparison : additiveChoreCost cost 1 pool01 - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    rw [hpool01CostOne]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 1 leftPool
  have hlongTwoLeftLarge : r ≤ additiveChoreCost cost 2 leftPool := by
    obtain ⟨item, hitem⟩ := hpool03Nonempty
    have hleft : item ∈ leftPool := by
      change item ∈ pool02 ∪ pool03
      exact Finset.mem_union_right pool02 hitem
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 3} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hleft
  have hlongTwoRightLarge : r ≤ additiveChoreCost cost 2 pool01 := by
    obtain ⟨item, hitem⟩ := hpool01Nonempty
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 1} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hitem
  exact existsEfxOfB2SimpleGraphBoundedShortPoolsWithSmallLong2 Item r cost
    prefixChores m2Chores leftPool pool01 pool23 a quota prefixAllocation hr hcost hprefixM2
    hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hcover hshortDisjoint hlongDisjoint
    hpool23TwoCost hlongTwoLeftLarge hlongTwoRightLarge hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), two cross types at short agent `0`, with the
type `(0,1)` chore present and the type `(2,3)` chore absent. -/
theorem existsEfxOfB2SimpleGraph_twoZeroCrosses_shortTypeOnly
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h01Nonempty : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).Nonempty)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅)
    (h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let leftPool := pool02 ∪ pool03
  have hpool01CardLe : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool02CardLe : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool01Nonempty : pool01.Nonempty := by simpa [pool01] using h01Nonempty
  have hpool02Nonempty : pool02.Nonempty := by simpa [pool02] using h02Nonempty
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool01Card : pool01.card = 1 := by
    have hpos : 0 < pool01.card := Finset.card_pos.mpr hpool01Nonempty
    omega
  have hpool02Card : pool02.card = 1 := by
    have hpos : 0 < pool02.card := Finset.card_pos.mpr hpool02Nonempty
    omega
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hpool23Empty : pool23 = ∅ := by simpa [pool23] using h23Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = leftPool ∪ pool01 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = leftPool ∪ pool01 := by
        dsimp [leftPool]
        rw [hpool12Empty, hpool13Empty, hpool23Empty]
        simp only [Finset.union_empty]
        ac_rfl
  have hleftDisjoint : Disjoint pool02 pool03 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
      ({0, 3} : Finset (Fin 4)) (by decide)
  have hdisjoint : Disjoint leftPool pool01 := by
    rw [Finset.disjoint_left]
    intro item hleft h01
    simp only [leftPool, Finset.mem_union] at hleft
    rcases hleft with h02 | h03
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h02 h01).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h03 h01).elim
  have hleftCard : leftPool.card = 2 := by
    change (pool02 ∪ pool03).card = 2
    rw [Finset.card_union_of_disjoint hleftDisjoint, hpool02Card, hpool03Card]
  have hleftOwn : additiveChoreCost cost 0 leftPool = leftPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 leftPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [leftPool, Finset.mem_union] at hitem
      rcases hitem with h02 | h03
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
  have hpool01CostZero : additiveChoreCost cost 0 pool01 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool01 1]
    · simp [hpool01Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [hpool01Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftOwn, hleftCard]
    norm_num at ⊢
    linarith
  have hrightBound : additiveChoreCost cost 1 pool01 ≤ r + 1 := by
    rw [hpool01CostOne]
    linarith
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 pool01 := by
    rw [hleftOwn, hleftCard, hpool01CostZero]
    norm_num
  have hrightComparison : additiveChoreCost cost 1 pool01 - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    rw [hpool01CostOne]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 1 leftPool
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    leftPool pool01 a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), two cross types at short agent `0`, with no
type `(0,1)` chore and a type `(2,3)` chore.  The latter is assigned to short
agent `1`. -/
theorem existsEfxOfB2SimpleGraph_twoZeroCrosses_longTypeToOne
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty)
    (h01Empty : m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let leftPool := pool02 ∪ pool03
  have hpool02CardLe : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool02Nonempty : pool02.Nonempty := by simpa [pool02] using h02Nonempty
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using h23Nonempty
  have hpool02Card : pool02.card = 1 := by
    have hpos : 0 < pool02.card := Finset.card_pos.mpr hpool02Nonempty
    omega
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool23Card : pool23.card = 1 := by
    have hpos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
    omega
  have hpool01Empty : pool01 = ∅ := by simpa [pool01] using h01Empty
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = leftPool ∪ pool23 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = leftPool ∪ pool23 := by
        dsimp [leftPool]
        rw [hpool01Empty, hpool12Empty, hpool13Empty]
        simp only [Finset.empty_union, Finset.union_empty]
  have hleftDisjoint : Disjoint pool02 pool03 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
      ({0, 3} : Finset (Fin 4)) (by decide)
  have hdisjoint : Disjoint leftPool pool23 := by
    rw [Finset.disjoint_left]
    intro item hleft h23
    simp only [leftPool, Finset.mem_union] at hleft
    rcases hleft with h02 | h03
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h02 h23).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
  have hleftCard : leftPool.card = 2 := by
    change (pool02 ∪ pool03).card = 2
    rw [Finset.card_union_of_disjoint hleftDisjoint, hpool02Card, hpool03Card]
  have hleftOwn : additiveChoreCost cost 0 leftPool = leftPool.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 leftPool 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simp only [leftPool, Finset.mem_union] at hitem
      rcases hitem with h02 | h03
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
  have hpool23CostOne : additiveChoreCost cost 1 pool23 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool23 r]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
        item 1 hcost hitem (by decide)
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftOwn, hleftCard]
    norm_num at ⊢
    linarith
  have hrightBound : additiveChoreCost cost 1 pool23 ≤ r + 1 := by
    rw [hpool23CostOne]
    linarith
  have hrightLargeForZero : r ≤ additiveChoreCost cost 0 pool23 := by
    obtain ⟨item, hitem⟩ := hpool23Nonempty
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({2, 3} : Finset (Fin 4)) item 0 hcost hitem (by decide)
    change cost 0 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hitem
  have hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool := by
    obtain ⟨item, hitem⟩ := hpool02Nonempty
    have hleft : item ∈ leftPool := by
      change item ∈ pool02 ∪ pool03
      exact Finset.mem_union_left pool03 hitem
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 2} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    change cost 1 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hleft
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 pool23 := by
    rw [hleftOwn, hleftCard]
    norm_num at ⊢
    linarith
  have hrightComparison : additiveChoreCost cost 1 pool23 - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    rw [hpool23CostOne]
    linarith
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    leftPool pool23 a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), two cross types at short agent `0` and no same-side
type.  The two cross chores are split between the short agents. -/
theorem existsEfxOfB2SimpleGraph_twoZeroCrosses_crossSplit
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h01Empty : m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅)
    (h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have hpool02CardLe : pool02.card ≤ 1 := hsimple ({0, 2} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool02Nonempty : pool02.Nonempty := by simpa [pool02] using h02Nonempty
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool02Card : pool02.card = 1 := by
    have hpos : 0 < pool02.card := Finset.card_pos.mpr hpool02Nonempty
    omega
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool01Empty : pool01 = ∅ := by simpa [pool01] using h01Empty
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hpool23Empty : pool23 = ∅ := by simpa [pool23] using h23Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = pool02 ∪ pool03 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = pool02 ∪ pool03 := by
        rw [hpool01Empty, hpool12Empty, hpool13Empty, hpool23Empty]
        simp only [Finset.empty_union, Finset.union_empty]
  have hdisjoint : Disjoint pool02 pool03 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
      ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool02CostZero : additiveChoreCost cost 0 pool02 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool02 1]
    · simp [hpool02Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool03CostOne : additiveChoreCost cost 1 pool03 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool03 r]
    · simp [hpool03Card]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 3} : Finset (Fin 4))
        item 1 hcost hitem (by decide)
  have hleftBound : additiveChoreCost cost 0 pool02 ≤ r + 1 := by
    rw [hpool02CostZero]
    linarith
  have hrightBound : additiveChoreCost cost 1 pool03 ≤ r + 1 := by
    rw [hpool03CostOne]
    linarith
  have hleftComparison : additiveChoreCost cost 0 pool02 - 1 ≤
      additiveChoreCost cost 0 pool03 := by
    rw [hpool02CostZero]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 0 pool03
  have hrightComparison : additiveChoreCost cost 1 pool03 - 1 ≤
      additiveChoreCost cost 1 pool02 := by
    rw [hpool03CostOne]
    obtain ⟨item, hitem⟩ := hpool02Nonempty
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 2} : Finset (Fin 4)) item 1 hcost hitem (by decide)
    change cost 1 item = r at hlarge
    have hlower : r ≤ additiveChoreCost cost 1 pool02 := by
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore) hitem
    linarith
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    pool02 pool03 a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), unique cross type `(0,3)` with both same-side
types present.  The type `(2,3)` chore goes to long agent `2`, who sees both
short suffix bundles through a large chore. -/
theorem existsEfxOfB2SimpleGraph_unique03_bothSameTypes
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h01Nonempty : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).Nonempty)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty)
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have hpool01CardLe : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool01Nonempty : pool01.Nonempty := by simpa [pool01] using h01Nonempty
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using h23Nonempty
  have hpool01Card : pool01.card = 1 := by
    have hpos : 0 < pool01.card := Finset.card_pos.mpr hpool01Nonempty
    omega
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool23Card : pool23.card = 1 := by
    have hpos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
    omega
  have hpool02Empty : pool02 = ∅ := by simpa [pool02] using h02Empty
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = (pool03 ∪ pool01) ∪ pool23 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = (pool03 ∪ pool01) ∪ pool23 := by
        rw [hpool02Empty, hpool12Empty, hpool13Empty]
        simp only [Finset.union_empty]
        ac_rfl
  have hshortDisjoint : Disjoint pool03 pool01 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
      ({0, 1} : Finset (Fin 4)) (by decide)
  have hlongDisjoint : Disjoint (pool03 ∪ pool01) pool23 := by
    rw [Finset.disjoint_left]
    intro item hshort h23
    rcases Finset.mem_union.mp hshort with h03 | h01
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h01 h23).elim
  have hpool03CostZero : additiveChoreCost cost 0 pool03 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool03 1]
    · simp [hpool03Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [hpool01Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hpool23TwoCost : additiveChoreCost cost 2 pool23 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 2 pool23 1]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
        item 2 hitem (by simp)
  have hleftBound : additiveChoreCost cost 0 pool03 ≤ r + 1 := by
    rw [hpool03CostZero]
    linarith
  have hrightBound : additiveChoreCost cost 1 pool01 ≤ r + 1 := by
    rw [hpool01CostOne]
    linarith
  have hleftComparison : additiveChoreCost cost 0 pool03 - 1 ≤
      additiveChoreCost cost 0 pool01 := by
    rw [hpool03CostZero]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 0 pool01
  have hrightComparison : additiveChoreCost cost 1 pool01 - 1 ≤
      additiveChoreCost cost 1 pool03 := by
    rw [hpool01CostOne]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 1 pool03
  have hlongTwoLeftLarge : r ≤ additiveChoreCost cost 2 pool03 := by
    obtain ⟨item, hitem⟩ := hpool03Nonempty
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 3} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hitem
  have hlongTwoRightLarge : r ≤ additiveChoreCost cost 2 pool01 := by
    obtain ⟨item, hitem⟩ := hpool01Nonempty
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({0, 1} : Finset (Fin 4)) item 2 hcost hitem (by decide)
    change cost 2 item = r at hlarge
    rw [← hlarge]
    unfold additiveChoreCost
    exact Finset.single_le_sum
      (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 2 chore) hitem
  exact existsEfxOfB2SimpleGraphBoundedShortPoolsWithSmallLong2 Item r cost
    prefixChores m2Chores pool03 pool01 pool23 a quota prefixAllocation hr hcost hprefixM2
    hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hcover hshortDisjoint hlongDisjoint
    hpool23TwoCost hlongTwoLeftLarge hlongTwoRightLarge hleftBound hrightBound hleftComparison
    hrightComparison

/-- Source Case B.3.2(b), with the unique cross type `(0,3)`.  This direct
schedule packages all four possibilities for the same-side types: the cross
chore is assigned to short agent `0`, while the `(0,1)` and `(2,3)` chores,
when present, are assigned to short agent `1`.  The source's numerical EFX
checks give the displayed `r + 1` bound. -/
theorem existsEfxOfB2SimpleGraph_unique03_direct
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h03Nonempty : (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let rightPool := pool01 ∪ pool23
  have hpool01CardLe : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool03CardLe : pool03.card ≤ 1 := hsimple ({0, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool03Nonempty : pool03.Nonempty := by simpa [pool03] using h03Nonempty
  have hpool03Card : pool03.card = 1 := by
    have hpos : 0 < pool03.card := Finset.card_pos.mpr hpool03Nonempty
    omega
  have hpool02Empty : pool02 = ∅ := by simpa [pool02] using h02Empty
  have hpool12Empty : pool12 = ∅ := by simpa [pool12] using h12Empty
  have hpool13Empty : pool13 = ∅ := by simpa [pool13] using h13Empty
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = pool03 ∪ rightPool := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = pool03 ∪ rightPool := by
        dsimp [rightPool]
        rw [hpool02Empty, hpool12Empty, hpool13Empty]
        simp only [Finset.union_empty]
        ac_rfl
  have hdisjoint : Disjoint pool03 rightPool := by
    rw [Finset.disjoint_left]
    intro item h03 hright
    rcases Finset.mem_union.mp hright with h01 | h23
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h03 h01).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
  have hrightDisjoint : Disjoint pool01 pool23 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 1} : Finset (Fin 4))
      ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool03CostZero : additiveChoreCost cost 0 pool03 = 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool03 1]
    · simp [hpool03Card]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool03CostOne : additiveChoreCost cost 1 pool03 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool03 r]
    · simp [hpool03Card]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 3} : Finset (Fin 4))
        item 1 hcost hitem (by decide)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = pool01.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hpool23CostOne : additiveChoreCost cost 1 pool23 = pool23.card • r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool23 r]
    intro item hitem
    exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
      item 1 hcost hitem (by decide)
  have hpool01Bound : additiveChoreCost cost 1 pool01 ≤ 1 := by
    rw [hpool01CostOne]
    exact_mod_cast hpool01CardLe
  have hpool23Bound : additiveChoreCost cost 1 pool23 ≤ r := by
    rw [hpool23CostOne, nsmul_eq_mul]
    have hcard : (pool23.card : ℝ) ≤ 1 := by exact_mod_cast hpool23CardLe
    have hrnonneg : 0 ≤ r := by linarith
    nlinarith
  have hrightCost : additiveChoreCost cost 1 rightPool =
      additiveChoreCost cost 1 pool01 + additiveChoreCost cost 1 pool23 := by
    exact additiveChoreCost_union cost 1 pool01 pool23 hrightDisjoint
  have hleftBound : additiveChoreCost cost 0 pool03 ≤ r + 1 := by
    rw [hpool03CostZero]
    linarith
  have hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1 := by
    rw [hrightCost]
    linarith
  have hleftComparison : additiveChoreCost cost 0 pool03 - 1 ≤
      additiveChoreCost cost 0 rightPool := by
    rw [hpool03CostZero]
    norm_num at ⊢
    exact additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 0 rightPool
  have hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 pool03 := by
    rw [hpool03CostOne]
    linarith
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    pool03 rightPool a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint hleftBound hrightBound hleftComparison
    hrightComparison

/-- The direct unique-cross schedule is invariant under a relabelling of the
four displayed source agents.  This is the formal `without loss of
generality` bridge used for the other cross type and for the short-agent
symmetric branch. -/
theorem existsEfxOfB2SimpleGraph_unique03_direct_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a + 1) (hquota3 : quota (labels 3) = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores smallAgents).card ≤ 1)
    (h03Nonempty : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 3} : Finset (Fin 4))).Nonempty)
    (h02Empty : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 2} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2SimpleGraph_unique03_direct Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
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
  · exact hsimple
  · exact h03Nonempty
  · exact h02Empty
  · exact h12Empty
  · exact h13Empty

/-- Source Case B.3.2(b), with the unique cross type `(0,2)`.  Swapping the
two long labels turns it into the compiled unique-`(0,3)` direct schedule. -/
theorem existsEfxOfB2SimpleGraph_unique02_direct
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Nonempty : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty)
    (h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
  apply existsEfxOfB2SimpleGraph_unique03_direct_of_relabelled_typePools Item r cost labels
    prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
  · simpa [labels] using hquota0
  · simpa [labels] using hquota1
  · simpa [labels] using hquota3
  · simpa [labels] using hquota2
  · exact hsuper
  · intro smallAgents hcard
    rw [m2TypeChorePool_relabel labels cost m2Chores smallAgents]
    apply hsimple (smallAgents.map labels.toEmbedding)
    simpa using hcard
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 3} : Finset (Fin 4))]
    simpa [labels] using h02Nonempty
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4))]
    simpa [labels] using h03Empty
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4))]
    simpa [labels] using h13Empty
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 3} : Finset (Fin 4))]
    simpa [labels] using h12Empty

/-- Complete source Case B.3.2(b): all cross types are incident to short
agent `0` and at least one is present.  The two-cross and unique-cross
schedules above exhaust the simple graph's finite edge choices. -/
theorem existsEfxOfB2SimpleGraph_crossAtZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossNonempty :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases h02Nonempty : (m2TypeChorePool cost m2Chores
      ({0, 2} : Finset (Fin 4))).Nonempty
  · by_cases h03Nonempty : (m2TypeChorePool cost m2Chores
        ({0, 3} : Finset (Fin 4))).Nonempty
    · by_cases h01Nonempty : (m2TypeChorePool cost m2Chores
          ({0, 1} : Finset (Fin 4))).Nonempty
      · by_cases h23Nonempty : (m2TypeChorePool cost m2Chores
            ({2, 3} : Finset (Fin 4))).Nonempty
        · exact existsEfxOfB2SimpleGraph_twoZeroCrosses_bothSameTypes Item r cost
            prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
            hquota0 hquota1 hquota2 hquota3 hsuper hsimple h01Nonempty h02Nonempty h03Nonempty
            h23Nonempty h12Empty h13Empty
        · have h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp h23Nonempty
          exact existsEfxOfB2SimpleGraph_twoZeroCrosses_shortTypeOnly Item r cost
            prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
            hquota0 hquota1 hquota2 hquota3 hsuper hsimple h01Nonempty h02Nonempty h03Nonempty
            h12Empty h13Empty h23Empty
      · have h01Empty : m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp h01Nonempty
        by_cases h23Nonempty : (m2TypeChorePool cost m2Chores
            ({2, 3} : Finset (Fin 4))).Nonempty
        · exact existsEfxOfB2SimpleGraph_twoZeroCrosses_longTypeToOne Item r cost
            prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
            hquota0 hquota1 hquota2 hquota3 hsuper hsimple h02Nonempty h03Nonempty h23Nonempty
            h01Empty h12Empty h13Empty
        · have h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp h23Nonempty
          exact existsEfxOfB2SimpleGraph_twoZeroCrosses_crossSplit Item r cost
            prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
            hquota0 hquota1 hquota2 hquota3 hsuper hsimple h02Nonempty h03Nonempty h01Empty
            h12Empty h13Empty h23Empty
    · have h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp h03Nonempty
      exact existsEfxOfB2SimpleGraph_unique02_direct Item r cost prefixChores m2Chores a quota
        prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
        hsuper hsimple h02Nonempty h03Empty h12Empty h13Empty
  · have h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h02Nonempty
    by_cases h03Nonempty : (m2TypeChorePool cost m2Chores
        ({0, 3} : Finset (Fin 4))).Nonempty
    · exact existsEfxOfB2SimpleGraph_unique03_direct Item r cost prefixChores m2Chores a quota
        prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
        hsuper hsimple h03Nonempty h02Empty h12Empty h13Empty
    · exact (hcrossNonempty.elim (fun h02 => (h02Nonempty h02).elim)
        (fun h03 => (h03Nonempty h03).elim))

/-- The complete one-sided-cross case transports across a relabelling of the
displayed source labels. -/
theorem existsEfxOfB2SimpleGraph_crossAtZero_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a + 1) (hquota3 : quota (labels 3) = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores smallAgents).card ≤ 1)
    (hcrossNonempty :
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 3} : Finset (Fin 4))).Nonempty)
    (h12Empty : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2SimpleGraph_crossAtZero Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
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
  · exact hsimple
  · exact hcrossNonempty
  · exact h12Empty
  · exact h13Empty

/-- Complete source Case B.3.2(c), obtained from B.3.2(b) by interchanging
the two short agents. -/
theorem existsEfxOfB2SimpleGraph_crossAtOne
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossNonempty :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
  apply existsEfxOfB2SimpleGraph_crossAtZero_of_relabelled_typePools Item r cost labels
    prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
  · simpa [labels] using hquota1
  · simpa [labels] using hquota0
  · simpa [labels] using hquota2
  · simpa [labels] using hquota3
  · exact hsuper
  · intro smallAgents hcard
    rw [m2TypeChorePool_relabel labels cost m2Chores smallAgents]
    apply hsimple (smallAgents.map labels.toEmbedding)
    simpa using hcard
  · rcases hcrossNonempty with h12 | h13
    · left
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4))]
      simpa [labels] using h12
    · right
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 3} : Finset (Fin 4))]
      simpa [labels] using h13
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4))]
    simpa [labels] using h02Empty
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 3} : Finset (Fin 4))]
    simpa [labels] using h03Empty

/-- Source Case B.3.2(a) with a type-`(2,3)` chore and a sparse cross side
at short agent `0`.  Put that long--long chore with the sparse side; the
possible type-`(0,1)` chore joins the other short bundle.  The two suffix
bundles have own costs at most `r+1`, while each remaining short comparison
sees a large chore. -/
theorem existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossZeroNonempty :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOneNonempty :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (hcrossZeroCard : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card ≤ 1)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool02 := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))
  let pool03 := m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let pool12 := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let pool13 := m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let crossZero := pool02 ∪ pool03
  let crossOne := pool12 ∪ pool13
  let leftPool := crossZero ∪ pool23
  let rightPool := crossOne ∪ pool01
  have hpool01CardLe : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool12CardLe : pool12.card ≤ 1 := hsimple ({1, 2} : Finset (Fin 4)) (by decide)
  have hpool13CardLe : pool13.card ≤ 1 := hsimple ({1, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardLe : pool23.card ≤ 1 := hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hcrossZeroNonempty' : crossZero.Nonempty := by
    simpa [crossZero, pool02, pool03] using hcrossZeroNonempty
  have hcrossOneNonempty' : crossOne.Nonempty := by
    simpa [crossOne, pool12, pool13] using hcrossOneNonempty
  have hpool23Nonempty : pool23.Nonempty := by simpa [pool23] using h23Nonempty
  have hpool23Card : pool23.card = 1 := by
    have hpos : 0 < pool23.card := Finset.card_pos.mpr hpool23Nonempty
    omega
  have hcrossZeroCard' : crossZero.card ≤ 1 := by
    simpa [crossZero, pool02, pool03] using hcrossZeroCard
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = leftPool ∪ rightPool := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool02 ∪ pool03 ∪ pool12 ∪ pool13 ∪ pool23 := by
        simpa [pool01, pool02, pool03, pool12, pool13, pool23] using
          (m2ChorePool_eq_union_six_typeChorePools cost m2Chores)
      _ = leftPool ∪ rightPool := by
        dsimp [leftPool, rightPool, crossZero, crossOne]
        ac_rfl
  have hcrossZeroDisjoint : Disjoint pool02 pool03 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
      ({0, 3} : Finset (Fin 4)) (by decide)
  have hcrossOneDisjoint : Disjoint pool12 pool13 :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores ({1, 2} : Finset (Fin 4))
      ({1, 3} : Finset (Fin 4)) (by decide)
  have hleftDisjoint : Disjoint crossZero pool23 := by
    rw [Finset.disjoint_left]
    intro item hzero h23
    rcases Finset.mem_union.mp hzero with h02 | h03
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h02 h23).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
          ({2, 3} : Finset (Fin 4)) (by decide)) h03 h23).elim
  have hrightDisjoint : Disjoint crossOne pool01 := by
    rw [Finset.disjoint_left]
    intro item hone h01
    rcases Finset.mem_union.mp hone with h12 | h13
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({1, 2} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h12 h01).elim
    · exact (Finset.disjoint_left.mp
        (m2TypeChorePool_disjoint_of_ne cost m2Chores ({1, 3} : Finset (Fin 4))
          ({0, 1} : Finset (Fin 4)) (by decide)) h13 h01).elim
  have hcrossOneCard : crossOne.card ≤ 2 := by
    change (pool12 ∪ pool13).card ≤ 2
    rw [Finset.card_union_of_disjoint hcrossOneDisjoint]
    omega
  have hcrossZeroOwn : additiveChoreCost cost 0 crossZero = crossZero.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 crossZero 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      rcases Finset.mem_union.mp hitem with h02 | h03
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
          item 0 h02 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 3} : Finset (Fin 4))
          item 0 h03 (by simp)
  have hpool23CostZero : additiveChoreCost cost 0 pool23 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool23 r]
    · simp [hpool23Card]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
        item 0 hcost hitem (by decide)
  have hcrossOneOwn : additiveChoreCost cost 1 crossOne = crossOne.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 crossOne 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      rcases Finset.mem_union.mp hitem with h12 | h13
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 1 h12 (by simp)
      · exact m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 3} : Finset (Fin 4))
          item 1 h13 (by simp)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = pool01.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hleftCostZero : additiveChoreCost cost 0 leftPool =
      additiveChoreCost cost 0 crossZero + additiveChoreCost cost 0 pool23 := by
    exact additiveChoreCost_union cost 0 crossZero pool23 hleftDisjoint
  have hrightCostOne : additiveChoreCost cost 1 rightPool =
      additiveChoreCost cost 1 crossOne + additiveChoreCost cost 1 pool01 := by
    exact additiveChoreCost_union cost 1 crossOne pool01 hrightDisjoint
  have hleftBound : additiveChoreCost cost 0 leftPool ≤ r + 1 := by
    rw [hleftCostZero, hcrossZeroOwn, hpool23CostZero]
    have hcard : (crossZero.card : ℝ) ≤ 1 := by exact_mod_cast hcrossZeroCard'
    linarith
  have hrightBound : additiveChoreCost cost 1 rightPool ≤ r + 1 := by
    rw [hrightCostOne, hcrossOneOwn, hpool01CostOne]
    have hcrossCard : (crossOne.card : ℝ) ≤ 2 := by exact_mod_cast hcrossOneCard
    have hfirstCard : (pool01.card : ℝ) ≤ 1 := by exact_mod_cast hpool01CardLe
    linarith
  have hcrossOneLargeForZero : r ≤ additiveChoreCost cost 0 crossOne := by
    obtain ⟨item, hitem⟩ := hcrossOneNonempty'
    rcases Finset.mem_union.mp hitem with h12 | h13
    · have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 2} : Finset (Fin 4)) item 0 hcost h12 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hitem
    · have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({1, 3} : Finset (Fin 4)) item 0 hcost h13 (by decide)
      change cost 0 item = r at hlarge
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 0 chore) hitem
  have hrightLargeForZero : r ≤ additiveChoreCost cost 0 rightPool := by
    rw [additiveChoreCost_union cost 0 crossOne pool01 hrightDisjoint]
    have hnonneg := additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 0 pool01
    linarith
  have hleftLargeForOne : r ≤ additiveChoreCost cost 1 leftPool := by
    rw [additiveChoreCost_union cost 1 crossZero pool23 hleftDisjoint]
    have hnonneg := additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 1 crossZero
    have hlarge := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({2, 3} : Finset (Fin 4)) (Classical.choose hpool23Nonempty) 1 hcost
        (Classical.choose_spec hpool23Nonempty) (by decide)
    change cost 1 (Classical.choose hpool23Nonempty) = r at hlarge
    have hpoolLower : r ≤ additiveChoreCost cost 1 pool23 := by
      rw [← hlarge]
      unfold additiveChoreCost
      exact Finset.single_le_sum
        (fun chore _ => IsOneOrRChoreCost.nonneg cost r hcost (by linarith) 1 chore)
        (Classical.choose_spec hpool23Nonempty)
    linarith
  have hleftComparison : additiveChoreCost cost 0 leftPool - 1 ≤
      additiveChoreCost cost 0 rightPool := by
    linarith
  have hrightComparison : additiveChoreCost cost 1 rightPool - 1 ≤
      additiveChoreCost cost 1 leftPool := by
    linarith
  have hdisjoint : Disjoint leftPool rightPool := by
    rw [Finset.disjoint_left]
    intro item hleft hright
    dsimp [leftPool, rightPool, crossZero, crossOne] at hleft hright
    rcases Finset.mem_union.mp hleft with hzero | h23
    · rcases Finset.mem_union.mp hzero with h02 | h03
      · rcases Finset.mem_union.mp hright with hone | h01
        · rcases Finset.mem_union.mp hone with h12 | h13
          · exact (Finset.disjoint_left.mp
              (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
                ({1, 2} : Finset (Fin 4)) (by decide)) h02 h12).elim
          · exact (Finset.disjoint_left.mp
              (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
                ({1, 3} : Finset (Fin 4)) (by decide)) h02 h13).elim
        · exact (Finset.disjoint_left.mp
            (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 2} : Finset (Fin 4))
              ({0, 1} : Finset (Fin 4)) (by decide)) h02 h01).elim
      · rcases Finset.mem_union.mp hright with hone | h01
        · rcases Finset.mem_union.mp hone with h12 | h13
          · exact (Finset.disjoint_left.mp
              (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
                ({1, 2} : Finset (Fin 4)) (by decide)) h03 h12).elim
          · exact (Finset.disjoint_left.mp
              (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
                ({1, 3} : Finset (Fin 4)) (by decide)) h03 h13).elim
        · exact (Finset.disjoint_left.mp
            (m2TypeChorePool_disjoint_of_ne cost m2Chores ({0, 3} : Finset (Fin 4))
              ({0, 1} : Finset (Fin 4)) (by decide)) h03 h01).elim
    · rcases Finset.mem_union.mp hright with hone | h01
      · rcases Finset.mem_union.mp hone with h12 | h13
        · exact (Finset.disjoint_left.mp
            (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
              ({1, 2} : Finset (Fin 4)) (by decide)) h23 h12).elim
        · exact (Finset.disjoint_left.mp
            (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
              ({1, 3} : Finset (Fin 4)) (by decide)) h23 h13).elim
      · exact (Finset.disjoint_left.mp
          (m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
            ({0, 1} : Finset (Fin 4)) (by decide)) h23 h01).elim
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    leftPool rightPool a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hcover hdisjoint
    hleftBound hrightBound hleftComparison hrightComparison

/-- The sparse-side schedule with the sparse cross side at short agent `1`.
It is the short-agent relabelling of the preceding source schedule. -/
theorem existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseOne
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossZeroNonempty :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOneNonempty :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOneCard : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card ≤ 1)
    (h23Nonempty : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseZero Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a (relabelQuota labels quota)
    (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
  · exact hprefixM2
  · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
  · simpa [relabelQuota, labels] using hquota1
  · simpa [relabelQuota, labels] using hquota0
  · simpa [relabelQuota, labels] using hquota2
  · simpa [relabelQuota, labels] using hquota3
  · intro short long hshort hlong
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) (labels long) (by simpa [relabelQuota] using hshort)
        (by simpa [relabelQuota] using hlong)
  · intro smallAgents hcard
    rw [m2TypeChorePool_relabel labels cost m2Chores smallAgents]
    apply hsimple (smallAgents.map labels.toEmbedding)
    simpa using hcard
  · rcases hcrossOneNonempty with h12 | h13
    · left
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4))]
      simpa [labels] using h12
    · right
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 3} : Finset (Fin 4))]
      simpa [labels] using h13
  · rcases hcrossZeroNonempty with h02 | h03
    · left
      rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4))]
      simpa [labels] using h02
    · right
      rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 3} : Finset (Fin 4))]
      simpa [labels] using h03
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4)),
      m2TypeChorePool_relabel labels cost m2Chores ({0, 3} : Finset (Fin 4))]
    simpa [labels] using hcrossOneCard
  · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
    simpa [labels] using h23Nonempty

/-- Complete source Case B.3.2(a): both short sides have a cross type.  If
the long--long type is absent, the all-short schedule applies.  Otherwise,
the four-cross configuration uses the long-agent schedule, and every other
configuration has a sparse cross side covered by the preceding schedules. -/
theorem existsEfxOfB2SimpleGraph_crossBoth
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hcrossZero : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty)
    (hcrossOne : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
      m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hzeroOr :
      (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).Nonempty := by
    obtain ⟨item, hitem⟩ := hcrossZero
    rcases Finset.mem_union.mp hitem with h02 | h03
    · exact Or.inl ⟨item, h02⟩
    · exact Or.inr ⟨item, h03⟩
  have honeOr :
      (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))).Nonempty ∨
      (m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).Nonempty := by
    obtain ⟨item, hitem⟩ := hcrossOne
    rcases Finset.mem_union.mp hitem with h12 | h13
    · exact Or.inl ⟨item, h12⟩
    · exact Or.inr ⟨item, h13⟩
  by_cases h23Nonempty : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).Nonempty
  · by_cases h02Nonempty : (m2TypeChorePool cost m2Chores
        ({0, 2} : Finset (Fin 4))).Nonempty
    · by_cases h03Nonempty : (m2TypeChorePool cost m2Chores
          ({0, 3} : Finset (Fin 4))).Nonempty
      · by_cases h12Nonempty : (m2TypeChorePool cost m2Chores
            ({1, 2} : Finset (Fin 4))).Nonempty
        · by_cases h13Nonempty : (m2TypeChorePool cost m2Chores
              ({1, 3} : Finset (Fin 4))).Nonempty
          · exact existsEfxOfB2SimpleGraph_fourCrosses_longType_to_longTwo Item r cost
              prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
              hquota0 hquota1 hquota2 hquota3 hsuper hsimple h02Nonempty h03Nonempty
              h12Nonempty h13Nonempty h23Nonempty
          · have h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp h13Nonempty
            have honeSparse : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
                m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card ≤ 1 := by
              rw [h13Empty]
              simp [hsimple ({1, 2} : Finset (Fin 4)) (by decide)]
            exact existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseOne Item r cost
              prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
              hquota0 hquota1 hquota2 hquota3 hsuper hsimple hzeroOr honeOr honeSparse h23Nonempty
        · have h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp h12Nonempty
          have honeSparse : (m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
              m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))).card ≤ 1 := by
            rw [h12Empty]
            simp [hsimple ({1, 3} : Finset (Fin 4)) (by decide)]
          exact existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseOne Item r cost
            prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
            hquota0 hquota1 hquota2 hquota3 hsuper hsimple hzeroOr honeOr honeSparse h23Nonempty
      · have h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp h03Nonempty
        have hzeroSparse : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
            m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card ≤ 1 := by
          rw [h03Empty]
          simp [hsimple ({0, 2} : Finset (Fin 4)) (by decide)]
        exact existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseZero Item r cost
          prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
          hquota0 hquota1 hquota2 hquota3 hsuper hsimple hzeroOr honeOr hzeroSparse h23Nonempty
    · have h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp h02Nonempty
      have hzeroSparse : (m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
          m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))).card ≤ 1 := by
        rw [h02Empty]
        simp [hsimple ({0, 3} : Finset (Fin 4)) (by decide)]
      exact existsEfxOfB2SimpleGraph_crossBoth_longType_to_sparseZero Item r cost
        prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
        hquota0 hquota1 hquota2 hquota3 hsuper hsimple hzeroOr honeOr hzeroSparse h23Nonempty
  · have h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h23Nonempty
    exact existsEfxOfB2SimpleGraph_crossBoth_noLongType Item r cost prefixChores m2Chores a quota
      prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hsuper hsimple hcrossZero hcrossOne h23Empty

/-- The no-long-type subcase of source Case B.3.2(d).  With every cross type
and the type `(2,3)` absent, the sole possible M₂ fibre is `(0,1)`, whose
unit-cost bundle is harmless on one short agent. -/
theorem existsEfxOfB2SimpleGraph_sameSide_noLongType
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅)
    (h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = pool01 ∪ ∅ := by
    rw [← hm2IsPool]
    simpa [pool01] using m2ChorePool_eq_sameSide_typeChorePools_of_cross_empty cost m2Chores
      h02Empty h03Empty h12Empty h13Empty |>.trans (by rw [h23Empty, Finset.union_empty])
  have hpoolCard : pool01.card ≤ 1 := hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpoolCostZero : additiveChoreCost cost 0 pool01 = pool01.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool01 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hleftBound : additiveChoreCost cost 0 pool01 ≤ r + 1 := by
    rw [hpoolCostZero]
    have hcard : (pool01.card : ℝ) ≤ 1 := by exact_mod_cast hpoolCard
    linarith
  have hleftComparison : additiveChoreCost cost 0 pool01 - 1 ≤
      additiveChoreCost cost 0 (∅ : Finset Item) := by
    rw [hpoolCostZero]
    simp only [additiveChoreCost_empty]
    have hcard : (pool01.card : ℝ) ≤ 1 := by exact_mod_cast hpoolCard
    linarith
  have hrightComparison : additiveChoreCost cost 1 (∅ : Finset Item) - 1 ≤
      additiveChoreCost cost 1 pool01 := by
    simp only [additiveChoreCost_empty, zero_sub]
    exact le_trans (by norm_num) (additiveChoreCost_nonneg cost
      (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 1 pool01)
  exact existsEfxOfB2SimpleGraphBoundedShortPools Item r cost prefixChores m2Chores
    pool01 ∅ a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
    hquota3 hsuper hcover (by simp) hleftBound (by
      rw [additiveChoreCost_empty]
      linarith)
    hleftComparison hrightComparison

/-- The nonempty type-`(2,3)` part of source Case B.3.2(d), with that chore
given to short agent `0` and the possible type-`(0,1)` chore given to short
agent `1`.  The all-large-or-cross-advantage alternative is exactly the
source's choice of the recipient for the long--long chore. -/
theorem existsEfxOfB2SimpleGraph_sameSide_longType_to_zero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (hzeroCondition :
      (∀ item ∈ prefixAllocation 0, IsLargeChore cost r 0 item) ∨
      additiveChoreCost cost 0 (prefixAllocation 0) + (r - 1) ≤
        additiveChoreCost cost 0 (prefixAllocation 1))
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅)
    (h23Nonempty : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let pool01 := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let pool23 := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 pool23
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 pool01
  let suffix : Allocation (Fin 4) Item := fun agent => suffixZero agent ∪ suffixOne agent
  have hm2IsPool : m2ChorePool cost m2Chores = m2Chores := by
    ext item
    constructor
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mp hitem |>.1
    · intro hitem
      exact (mem_m2ChorePool cost m2Chores item).mpr ⟨hitem, hm2Small item hitem⟩
  have hcover : m2Chores = pool23 ∪ pool01 := by
    calc
      m2Chores = m2ChorePool cost m2Chores := hm2IsPool.symm
      _ = pool01 ∪ pool23 := by
        simpa [pool01, pool23] using
          (m2ChorePool_eq_sameSide_typeChorePools_of_cross_empty cost m2Chores
            h02Empty h03Empty h12Empty h13Empty)
      _ = pool23 ∪ pool01 := Finset.union_comm _ _
  have hpoolDisjoint : Disjoint pool23 pool01 := by
    exact m2TypeChorePool_disjoint_of_ne cost m2Chores ({2, 3} : Finset (Fin 4))
      ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool01Card : pool01.card ≤ 1 :=
    hsimple ({0, 1} : Finset (Fin 4)) (by decide)
  have hpool23Card : pool23.card ≤ 1 :=
    hsimple ({2, 3} : Finset (Fin 4)) (by decide)
  have hpool23CardOne : pool23.card = 1 := by
    have hpositive : 0 < pool23.card := Finset.card_pos.mpr (by simpa [pool23] using h23Nonempty)
    omega
  have hzeroAllocation : IsAllocationOf suffixZero pool23 :=
    isAllocationOf_allocateAllTo 0 pool23
  have honeAllocation : IsAllocationOf suffixOne pool01 :=
    isAllocationOf_allocateAllTo 1 pool01
  have hsuffixAllocation : IsAllocationOf suffix m2Chores := by
    rw [hcover]
    simpa [suffix] using isAllocationOf_union suffixZero suffixOne pool23 pool01
      hpoolDisjoint hzeroAllocation honeAllocation
  have hsuffixZero : suffix 0 = pool23 := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixOne : suffix 1 = pool01 := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixTwo : suffix 2 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hsuffixThree : suffix 3 = ∅ := by
    simp [suffix, suffixZero, suffixOne, allocateAllTo]
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hcostNonneg : ∀ agent item, 0 ≤ cost agent item :=
    IsOneOrRChoreCost.nonneg cost r hcost (by linarith)
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    IsOneOrRChoreCost.one_le cost r hcost (by linarith)
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
  have hpool23CostZero : additiveChoreCost cost 0 pool23 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool23 r]
    · simp [hpool23CardOne]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 0 hcost hitem (by decide)
  have hpool23CostOne : additiveChoreCost cost 1 pool23 = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool23 r]
    · simp [hpool23CardOne]
    · intro item hitem
      exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 1 hcost hitem (by decide)
  have hpool01CostZero : additiveChoreCost cost 0 pool01 = pool01.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 pool01 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 0 hitem (by simp)
  have hpool01CostOne : additiveChoreCost cost 1 pool01 = pool01.card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 pool01 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      exact m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
        item 1 hitem (by simp)
  have hsuffixZeroCostZero : additiveChoreCost cost 0 (suffix 0) = r := by
    simpa [hsuffixZero] using hpool23CostZero
  have hsuffixZeroCostOne : additiveChoreCost cost 1 (suffix 0) = r := by
    simpa [hsuffixZero] using hpool23CostOne
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = pool01.card := by
    simpa [hsuffixOne] using hpool01CostOne
  have hsuffixOneCostOneLe : additiveChoreCost cost 1 (suffix 1) ≤ 1 := by
    rw [hsuffixOneCostOne]
    exact_mod_cast hpool01Card
  have hsuffixZeroLarge : ∀ item ∈ suffix 0, IsLargeChore cost r 0 item := by
    intro item hitem
    rw [hsuffixZero] at hitem
    exact m2TypeChorePool_large_for_nonendpoint r cost m2Chores
      ({2, 3} : Finset (Fin 4)) item 0 hcost hitem (by decide)
  have hzeroVsOne (hnonempty : (prefixAllocation 0 ∪ suffix 0).Nonempty) :
      additiveChoreCost cost 0 (prefixAllocation 0) -
          additiveChoreCost cost 0 (prefixAllocation 1) ≤
        additiveChoreCost cost 0 (suffix 1) -
          additiveChoreCost cost 0 (suffix 0) +
          ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
            (Finset.image_nonempty.mpr hnonempty) := by
    have hminimumOne : 1 ≤ ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
      apply Finset.le_min'
      intro value hvalue
      obtain ⟨item, _hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
      rw [← hvalueEq]
      exact hcostLower 0 item
    have hsuffixOneNonneg : 0 ≤ additiveChoreCost cost 0 (suffix 1) :=
      additiveChoreCost_nonneg cost hcostNonneg 0 (suffix 1)
    rcases hzeroCondition with hzeroLarge | hzeroAdvantage
    · have hminimumLarge : r ≤ ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
          (Finset.image_nonempty.mpr hnonempty) := by
        apply Finset.le_min'
        intro value hvalue
        obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
        rw [← hvalueEq]
        rcases Finset.mem_union.mp hitem with hprefixItem | hsuffixItem
        · exact le_of_eq (hzeroLarge item hprefixItem).symm
        · exact le_of_eq (hsuffixZeroLarge item hsuffixItem).symm
      linarith [hprefixEqual 0 1 (by rw [hquota0, hquota1]), hsuffixZeroCostZero]
    · linarith [hsuffixZeroCostZero]
  have hfinalEFX : EFXForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ suffix agent) := by
    apply efxForChores_union_of_cost_gap cost prefixAllocation suffix hbundlesDisjoint
    intro own comparison hnonempty
    have hminimumOne : 1 ≤ ((prefixAllocation own ∪ suffix own).image (cost own)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
      apply Finset.le_min'
      intro value hvalue
      obtain ⟨item, _hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
      rw [← hvalueEq]
      exact hcostLower own item
    fin_cases own
    · fin_cases comparison
      · linarith
      · exact hzeroVsOne hnonempty
      · have hnonemptyZero : (prefixAllocation 0 ∪ suffix 0).Nonempty := by
          simpa using hnonempty
        have hminimumZero : 1 ≤ ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
            (Finset.image_nonempty.mpr hnonemptyZero) := by
          simpa using hminimumOne
        have hgap : additiveChoreCost cost 0 (prefixAllocation 0) -
            additiveChoreCost cost 0 (prefixAllocation 2) ≤ 0 - r +
              ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
                (Finset.image_nonempty.mpr hnonemptyZero) := by
          linarith [hsuper 0 2 hquota0 hquota2]
        change additiveChoreCost cost 0 (prefixAllocation 0) -
          additiveChoreCost cost 0 (prefixAllocation 2) ≤
            additiveChoreCost cost 0 (suffix 2) -
              additiveChoreCost cost 0 (suffix 0) + _
        simpa only [hsuffixTwo, additiveChoreCost_empty, hsuffixZeroCostZero] using hgap
      · have hnonemptyZero : (prefixAllocation 0 ∪ suffix 0).Nonempty := by
          simpa using hnonempty
        have hminimumZero : 1 ≤ ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
            (Finset.image_nonempty.mpr hnonemptyZero) := by
          simpa using hminimumOne
        have hgap : additiveChoreCost cost 0 (prefixAllocation 0) -
            additiveChoreCost cost 0 (prefixAllocation 3) ≤ 0 - r +
              ((prefixAllocation 0 ∪ suffix 0).image (cost 0)).min'
                (Finset.image_nonempty.mpr hnonemptyZero) := by
          linarith [hsuper 0 3 hquota0 hquota3]
        change additiveChoreCost cost 0 (prefixAllocation 0) -
          additiveChoreCost cost 0 (prefixAllocation 3) ≤
            additiveChoreCost cost 0 (suffix 3) -
              additiveChoreCost cost 0 (suffix 0) + _
        simpa only [hsuffixThree, additiveChoreCost_empty, hsuffixZeroCostZero] using hgap
    · fin_cases comparison
      · have hnonemptyOne : (prefixAllocation 1 ∪ suffix 1).Nonempty := by
          simpa using hnonempty
        have hminimumOne' : 1 ≤ ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
            (Finset.image_nonempty.mpr hnonemptyOne) := by
          simpa using hminimumOne
        have hgap : additiveChoreCost cost 1 (prefixAllocation 1) -
            additiveChoreCost cost 1 (prefixAllocation 0) ≤
              additiveChoreCost cost 1 (suffix 0) -
                additiveChoreCost cost 1 (suffix 1) +
                ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
                  (Finset.image_nonempty.mpr hnonemptyOne) := by
          linarith [hprefixEqual 1 0 (by rw [hquota1, hquota0]), hsuffixZeroCostOne,
            hsuffixOneCostOneLe]
        simpa using hgap
      · linarith
      · have hnonemptyOne : (prefixAllocation 1 ∪ suffix 1).Nonempty := by
          simpa using hnonempty
        have hminimumOne' : 1 ≤ ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
            (Finset.image_nonempty.mpr hnonemptyOne) := by
          simpa using hminimumOne
        have hgap : additiveChoreCost cost 1 (prefixAllocation 1) -
            additiveChoreCost cost 1 (prefixAllocation 2) ≤ 0 -
              additiveChoreCost cost 1 (suffix 1) +
                ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
                  (Finset.image_nonempty.mpr hnonemptyOne) := by
          linarith [hsuper 1 2 hquota1 hquota2, hsuffixOneCostOneLe]
        simpa only [hsuffixTwo, additiveChoreCost_empty] using hgap
      · have hnonemptyOne : (prefixAllocation 1 ∪ suffix 1).Nonempty := by
          simpa using hnonempty
        have hminimumOne' : 1 ≤ ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
            (Finset.image_nonempty.mpr hnonemptyOne) := by
          simpa using hminimumOne
        have hgap : additiveChoreCost cost 1 (prefixAllocation 1) -
            additiveChoreCost cost 1 (prefixAllocation 3) ≤ 0 -
              additiveChoreCost cost 1 (suffix 1) +
                ((prefixAllocation 1 ∪ suffix 1).image (cost 1)).min'
                  (Finset.image_nonempty.mpr hnonemptyOne) := by
          linarith [hsuper 1 3 hquota1 hquota3, hsuffixOneCostOneLe]
        simpa only [hsuffixThree, additiveChoreCost_empty] using hgap
    · have hnonemptyTwo : (prefixAllocation 2 ∪ suffix 2).Nonempty := by
        simpa using hnonempty
      have hprefixNonempty : (prefixAllocation 2).Nonempty := by
        simpa [hsuffixTwo] using hnonemptyTwo
      have hprefixGap := EFXForChores.additive_sub_le_min_cost cost hcostNonneg
        prefixAllocation hprefixEFX 2 comparison hprefixNonempty
      have hminimumEq : ((prefixAllocation 2 ∪ suffix 2).image (cost 2)).min'
          (Finset.image_nonempty.mpr hnonemptyTwo) =
          ((prefixAllocation 2).image (cost 2)).min'
            (Finset.image_nonempty.mpr hprefixNonempty) := by
        simp [hsuffixTwo]
      have hgap : additiveChoreCost cost 2 (prefixAllocation 2) -
          additiveChoreCost cost 2 (prefixAllocation comparison) ≤
            additiveChoreCost cost 2 (suffix comparison) - 0 +
              ((prefixAllocation 2 ∪ suffix 2).image (cost 2)).min'
                (Finset.image_nonempty.mpr hnonemptyTwo) := by
        rw [hminimumEq]
        linarith [additiveChoreCost_nonneg cost hcostNonneg 2 (suffix comparison)]
      change additiveChoreCost cost 2 (prefixAllocation 2) -
        additiveChoreCost cost 2 (prefixAllocation comparison) ≤
          additiveChoreCost cost 2 (suffix comparison) -
            additiveChoreCost cost 2 (suffix 2) +
              ((prefixAllocation 2 ∪ suffix 2).image (cost 2)).min'
                (Finset.image_nonempty.mpr hnonemptyTwo)
      have hsuffixTwoCost : additiveChoreCost cost 2 (suffix 2) = 0 := by
        rw [hsuffixTwo]
        exact additiveChoreCost_empty cost 2
      rw [hsuffixTwoCost]
      exact hgap
    · have hnonemptyThree : (prefixAllocation 3 ∪ suffix 3).Nonempty := by
        simpa using hnonempty
      have hprefixNonempty : (prefixAllocation 3).Nonempty := by
        simpa [hsuffixThree] using hnonemptyThree
      have hprefixGap := EFXForChores.additive_sub_le_min_cost cost hcostNonneg
        prefixAllocation hprefixEFX 3 comparison hprefixNonempty
      have hminimumEq : ((prefixAllocation 3 ∪ suffix 3).image (cost 3)).min'
          (Finset.image_nonempty.mpr hnonemptyThree) =
          ((prefixAllocation 3).image (cost 3)).min'
            (Finset.image_nonempty.mpr hprefixNonempty) := by
        simp [hsuffixThree]
      have hgap : additiveChoreCost cost 3 (prefixAllocation 3) -
          additiveChoreCost cost 3 (prefixAllocation comparison) ≤
            additiveChoreCost cost 3 (suffix comparison) - 0 +
              ((prefixAllocation 3 ∪ suffix 3).image (cost 3)).min'
                (Finset.image_nonempty.mpr hnonemptyThree) := by
        rw [hminimumEq]
        linarith [additiveChoreCost_nonneg cost hcostNonneg 3 (suffix comparison)]
      change additiveChoreCost cost 3 (prefixAllocation 3) -
        additiveChoreCost cost 3 (prefixAllocation comparison) ≤
          additiveChoreCost cost 3 (suffix comparison) -
            additiveChoreCost cost 3 (suffix 3) +
              ((prefixAllocation 3 ∪ suffix 3).image (cost 3)).min'
                (Finset.image_nonempty.mpr hnonemptyThree)
      have hsuffixThreeCost : additiveChoreCost cost 3 (suffix 3) = 0 := by
        rw [hsuffixThree]
        exact additiveChoreCost_empty cost 3
      rw [hsuffixThreeCost]
      exact hgap
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent,
    isAllocationOf_union prefixAllocation suffix prefixChores m2Chores hprefixM2
      hcanonical.1 hsuffixAllocation, hfinalEFX⟩

/-- Complete source Case B.3.2(d) when the type-`(2,3)` chore is present.
The recipient is a short agent with no own-small prefix chore when possible;
otherwise both short agents have one and the canonical cross-cost advantage
supplies the required `r - 1` compensation. -/
theorem existsEfxOfB2SimpleGraph_sameSide_longType
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1)
    (h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅)
    (h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅)
    (h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅)
    (h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅)
    (h23Nonempty : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).Nonempty) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hzeroSmall : ∃ item ∈ prefixAllocation 0, IsSmallChore cost 0 item
  · by_cases honeSmall : ∃ item ∈ prefixAllocation 1, IsSmallChore cost 1 item
    · have hadvantage : additiveChoreCost cost 0 (prefixAllocation 0) + (r - 1) ≤
          additiveChoreCost cost 0 (prefixAllocation 1) :=
        hcanonical.cross_cost_advantage_of_ownSmall cost r prefixChores quota prefixAllocation
          hcost (by linarith) hprefixSmall 0 1 (by decide)
          (hquota0.trans hquota1.symm) hzeroSmall honeSmall
      exact existsEfxOfB2SimpleGraph_sameSide_longType_to_zero Item r cost
        prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
        hquota0 hquota1 hquota2 hquota3 hsuper hsimple (Or.inr hadvantage) h02Empty h03Empty
        h12Empty h13Empty h23Nonempty
    · let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
      have hrelabeledLarge : ∀ item ∈ relabelAllocation labels prefixAllocation 0,
          IsLargeChore (relabelChoreCost labels cost) r 0 item := by
        intro item hitem
        have hitem' : item ∈ prefixAllocation 1 := by
          simpa [relabelAllocation, labels] using hitem
        have hlarge := IsOneOrRChoreCost.all_large_of_no_small cost r hcost 1
          (prefixAllocation 1) honeSmall item hitem'
        simpa [relabelChoreCost, IsLargeChore, labels] using hlarge
      apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
      apply existsEfxOfB2SimpleGraph_sameSide_longType_to_zero Item r
        (relabelChoreCost labels cost) prefixChores m2Chores a (relabelQuota labels quota)
        (relabelAllocation labels prefixAllocation)
      · exact hr
      · exact IsOneOrRChoreCost.relabel labels cost r hcost
      · intro item hitem
        exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
      · exact hprefixM2
      · exact hcanonical.relabel labels cost prefixChores quota prefixAllocation
      · simpa [relabelQuota, labels] using hquota1
      · simpa [relabelQuota, labels] using hquota0
      · simpa [relabelQuota, labels] using hquota2
      · simpa [relabelQuota, labels] using hquota3
      · intro short long hshort hlong
        simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
          hsuper (labels short) (labels long)
            (by simpa [relabelQuota] using hshort)
            (by simpa [relabelQuota] using hlong)
      · intro smallAgents hcard
        rw [m2TypeChorePool_relabel labels cost m2Chores smallAgents]
        apply hsimple (smallAgents.map labels.toEmbedding)
        simpa using hcard
      · exact Or.inl hrelabeledLarge
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4))]
        simpa [labels] using h12Empty
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 3} : Finset (Fin 4))]
        simpa [labels] using h13Empty
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 2} : Finset (Fin 4))]
        simpa [labels] using h02Empty
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({1, 3} : Finset (Fin 4))]
        simpa [labels] using h03Empty
      · rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4))]
        simpa [labels] using h23Nonempty
  · have hzeroLarge : ∀ item ∈ prefixAllocation 0, IsLargeChore cost r 0 item :=
      IsOneOrRChoreCost.all_large_of_no_small cost r hcost 0 (prefixAllocation 0) hzeroSmall
    exact existsEfxOfB2SimpleGraph_sameSide_longType_to_zero Item r cost
      prefixChores m2Chores a quota prefixAllocation hr hcost hm2Small hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsimple (Or.inl hzeroLarge) h02Empty h03Empty
      h12Empty h13Empty h23Nonempty

/-- Complete source Case B.3.2.  A simple M₂ graph is partitioned by whether
there is a cross type incident to each short agent; the no-cross branch is
the same-side schedule of B.3.2(d). -/
theorem existsEfxOfB2SimpleGraph
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let crossZero := m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) ∪
    m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4))
  let crossOne := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) ∪
    m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4))
  by_cases hcrossZero : crossZero.Nonempty
  · by_cases hcrossOne : crossOne.Nonempty
    · exact existsEfxOfB2SimpleGraph_crossBoth Item r cost prefixChores m2Chores a quota
        prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
        hsuper hsimple (by simpa [crossZero] using hcrossZero) (by simpa [crossOne] using hcrossOne)
    · have hcrossOneEmpty : crossOne = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcrossOne
      have hcrossOneParts :
          m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅ ∧
            m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅ :=
        Finset.union_eq_empty.mp (by simpa [crossOne] using hcrossOneEmpty)
      have h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅ := by
        exact hcrossOneParts.1
      have h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅ := by
        exact hcrossOneParts.2
      exact existsEfxOfB2SimpleGraph_crossAtZero Item r cost prefixChores m2Chores a quota
        prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
        hsuper hsimple (by simpa [crossZero] using hcrossZero) h12Empty h13Empty
  · have hcrossZeroEmpty : crossZero = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcrossZero
    have hcrossZeroParts :
        m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅ ∧
          m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅ :=
      Finset.union_eq_empty.mp (by simpa [crossZero] using hcrossZeroEmpty)
    have h02Empty : m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) = ∅ := by
      exact hcrossZeroParts.1
    have h03Empty : m2TypeChorePool cost m2Chores ({0, 3} : Finset (Fin 4)) = ∅ := by
      exact hcrossZeroParts.2
    by_cases hcrossOne : crossOne.Nonempty
    · exact existsEfxOfB2SimpleGraph_crossAtOne Item r cost prefixChores m2Chores a quota
        prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
        hsuper hsimple (by simpa [crossOne] using hcrossOne) h02Empty h03Empty
    · have hcrossOneEmpty : crossOne = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcrossOne
      have hcrossOneParts :
          m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅ ∧
            m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅ :=
        Finset.union_eq_empty.mp (by simpa [crossOne] using hcrossOneEmpty)
      have h12Empty : m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) = ∅ := by
        exact hcrossOneParts.1
      have h13Empty : m2TypeChorePool cost m2Chores ({1, 3} : Finset (Fin 4)) = ∅ := by
        exact hcrossOneParts.2
      by_cases h23Nonempty : (m2TypeChorePool cost m2Chores
          ({2, 3} : Finset (Fin 4))).Nonempty
      · exact existsEfxOfB2SimpleGraph_sameSide_longType Item r cost prefixChores m2Chores a quota
          prefixAllocation hr hcost hm2Small hprefixM2 hprefixSmall hcanonical hquota0 hquota1
          hquota2 hquota3 hsuper hsimple h02Empty h03Empty h12Empty h13Empty h23Nonempty
      · have h23Empty : m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp h23Nonempty
        exact existsEfxOfB2SimpleGraph_sameSide_noLongType Item r cost prefixChores m2Chores a quota
          prefixAllocation hr hcost hm2Small hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
          hsuper hsimple h02Empty h03Empty h12Empty h13Empty h23Empty

end HT26EFXChores
