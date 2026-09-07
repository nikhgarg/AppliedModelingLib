import HT26EFXChores.B1DirectAllocation

/-!
# The two small direct allocations in source Case B.2.1(b)

When the two disjoint M2 type pools have cardinalities (3,3) or (4,3), the
source uses a direct allocation instead of deleting three chores for the
ordinary gap-fill/residual construction.

Source: EFXadditivechores.tex, lines 2425--2439.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The direct B.2.1(b) schedule behind the source's two exceptional
multiplicities.  The two type-(0,1) chores in uZero go to agent 0, the
remaining one or two type-(0,1) chores in uOne go to agent 1, and the three
type-(2,3) chores in w go to agent 3.

Agent 2 is the long canonical agent and receives no M2 chore.  The only
non-canonical prefix comparison required by the direct verification is the
source's r-advantage of agent 3 over agent 2. -/
theorem existsEfxOfB1DisjointExceptionalDirect
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores uZero uOne w : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 2) - r)
    (hcover : m2Chores = (uZero ∪ uOne) ∪ w)
    (huZeroOne : Disjoint uZero uOne) (huZeroW : Disjoint uZero w)
    (huOneW : Disjoint uOne w)
    (huZeroCard : uZero.card = 2) (huOneLower : 1 ≤ uOne.card)
    (huOneUpper : uOne.card ≤ 2) (hwCard : w.card = 3)
    (hu : ∀ item ∈ uZero ∪ uOne,
      cost 0 item = 1 ∧ cost 1 item = 1 ∧ cost 2 item = r ∧ cost 3 item = r)
    (hw : ∀ item ∈ w,
      cost 0 item = r ∧ cost 1 item = r ∧ cost 2 item = 1 ∧ cost 3 item = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 uZero
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 uOne
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 w
  let suffixZeroOne : Allocation (Fin 4) Item :=
    fun agent => suffixZero agent ∪ suffixOne agent
  let suffix : Allocation (Fin 4) Item :=
    fun agent => suffixZeroOne agent ∪ suffixThree agent
  have huZeroOneAllocation : IsAllocationOf suffixZeroOne (uZero ∪ uOne) := by
    simpa [suffixZeroOne] using isAllocationOf_union suffixZero suffixOne uZero uOne
      huZeroOne (isAllocationOf_allocateAllTo 0 uZero) (isAllocationOf_allocateAllTo 1 uOne)
  have huZeroOneW : Disjoint (uZero ∪ uOne) w := by
    rw [Finset.disjoint_left]
    intro item hitem hitemW
    rcases Finset.mem_union.mp hitem with hitemZero | hitemOne
    · exact (Finset.disjoint_left.mp huZeroW hitemZero hitemW).elim
    · exact (Finset.disjoint_left.mp huOneW hitemOne hitemW).elim
  have hsuffixAllocation : IsAllocationOf suffix ((uZero ∪ uOne) ∪ w) := by
    simpa [suffix] using isAllocationOf_union suffixZeroOne suffixThree (uZero ∪ uOne) w
      huZeroOneW huZeroOneAllocation (isAllocationOf_allocateAllTo 3 w)
  have hsuffixZero : suffix 0 = uZero := by
    simp [suffix, suffixZeroOne, suffixZero, suffixOne, suffixThree, allocateAllTo]
  have hsuffixOne : suffix 1 = uOne := by
    simp [suffix, suffixZeroOne, suffixZero, suffixOne, suffixThree, allocateAllTo]
  have hsuffixTwo : suffix 2 = ∅ := by
    simp [suffix, suffixZeroOne, suffixZero, suffixOne, suffixThree, allocateAllTo]
  have hsuffixThree : suffix 3 = w := by
    simp [suffix, suffixZeroOne, suffixZero, suffixOne, suffixThree, allocateAllTo]
  have hprefixSuffix : Disjoint prefixChores ((uZero ∪ uOne) ∪ w) := by
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
  have hsuffixZeroCostZero : additiveChoreCost cost 0 (suffix 0) = 2 := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 0 uZero 1
      (fun item hitem => (hu item (Finset.mem_union_left _ hitem)).1), huZeroCard]
    norm_num [nsmul_eq_mul]
  have hsuffixZeroCostOne : additiveChoreCost cost 1 (suffix 0) = 2 := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 1 uZero 1
      (fun item hitem => (hu item (Finset.mem_union_left _ hitem)).2.1), huZeroCard]
    norm_num [nsmul_eq_mul]
  have hsuffixZeroCostThree : additiveChoreCost cost 3 (suffix 0) = 2 * r := by
    rw [hsuffixZero, additiveChoreCost_eq_card_nsmul_of_constant cost 3 uZero r
      (fun item hitem => (hu item (Finset.mem_union_left _ hitem)).2.2.2), huZeroCard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostZero : additiveChoreCost cost 0 (suffix 1) = (uOne.card : ℝ) := by
    rw [hsuffixOne, additiveChoreCost_eq_card_nsmul_of_constant cost 0 uOne 1
      (fun item hitem => (hu item (Finset.mem_union_right _ hitem)).1)]
    simp [nsmul_eq_mul]
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = (uOne.card : ℝ) := by
    rw [hsuffixOne, additiveChoreCost_eq_card_nsmul_of_constant cost 1 uOne 1
      (fun item hitem => (hu item (Finset.mem_union_right _ hitem)).2.1)]
    simp [nsmul_eq_mul]
  have hsuffixOneCostThree : additiveChoreCost cost 3 (suffix 1) = (uOne.card : ℝ) * r := by
    rw [hsuffixOne, additiveChoreCost_eq_card_nsmul_of_constant cost 3 uOne r
      (fun item hitem => (hu item (Finset.mem_union_right _ hitem)).2.2.2)]
    simp [nsmul_eq_mul]
  have hsuffixThreeCostZero : additiveChoreCost cost 0 (suffix 3) = 3 * r := by
    rw [hsuffixThree, additiveChoreCost_eq_card_nsmul_of_constant cost 0 w r
      (fun item hitem => (hw item hitem).1), hwCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = 3 * r := by
    rw [hsuffixThree, additiveChoreCost_eq_card_nsmul_of_constant cost 1 w r
      (fun item hitem => (hw item hitem).2.1), hwCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 3 := by
    rw [hsuffixThree, additiveChoreCost_eq_card_nsmul_of_constant cost 3 w 1
      (fun item hitem => (hw item hitem).2.2.2), hwCard]
    norm_num [nsmul_eq_mul]
  have huOneLowerReal : (1 : ℝ) ≤ uOne.card := by exact_mod_cast huOneLower
  have huOneUpperReal : (uOne.card : ℝ) ≤ 2 := by exact_mod_cast huOneUpper
  have huOneTimesRLower : (2 : ℝ) ≤ (uOne.card : ℝ) * r := by
    calc
      (2 : ℝ) ≤ r := le_of_lt hr
      _ = 1 * r := by ring
      _ ≤ (uOne.card : ℝ) * r :=
        mul_le_mul_of_nonneg_right huOneLowerReal (by linarith)
  have hprefixZeroOne : additiveChoreCost cost 0 (prefixAllocation 0) ≤
      additiveChoreCost cost 0 (prefixAllocation 1) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 0 1 (by rw [hquota0, hquota1])
  have hprefixZeroThree : additiveChoreCost cost 0 (prefixAllocation 0) ≤
      additiveChoreCost cost 0 (prefixAllocation 3) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 0 3 (by rw [hquota0, hquota3])
  have hprefixOneZero : additiveChoreCost cost 1 (prefixAllocation 1) ≤
      additiveChoreCost cost 1 (prefixAllocation 0) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 1 0 (by rw [hquota1, hquota0])
  have hprefixOneThree : additiveChoreCost cost 1 (prefixAllocation 1) ≤
      additiveChoreCost cost 1 (prefixAllocation 3) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 1 3 (by rw [hquota1, hquota3])
  have hprefixThreeZero : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 0) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 3 0 (by rw [hquota3, hquota0])
  have hprefixThreeOne : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 1) :=
    hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation hcost
      (by linarith) 3 1 (by rw [hquota3, hquota1])
  have hprefixZeroTwo : additiveChoreCost cost 0 (prefixAllocation 0) + 1 ≤
      additiveChoreCost cost 0 (prefixAllocation 2) :=
    hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota prefixAllocation
      hcost (by linarith) 0 2 (by rw [hquota2, hquota0])
  have hprefixOneTwo : additiveChoreCost cost 1 (prefixAllocation 1) + 1 ≤
      additiveChoreCost cost 1 (prefixAllocation 2) :=
    hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota prefixAllocation
      hcost (by linarith) 1 2 (by rw [hquota2, hquota1])
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      (by
        intro first second
        fin_cases first <;> fin_cases second <;>
          simp [hquota0, hquota1, hquota2, hquota3] <;> omega)
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf
      (fun agent => prefixAllocation agent ∪ suffix agent) (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union prefixAllocation suffix prefixChores
      ((uZero ∪ uOne) ∪ w) hprefixSuffix hcanonical.1 hsuffixAllocation
    simpa [hcover] using hcombined
  refine ⟨fun agent => prefixAllocation agent ∪ suffix agent, hfinalAllocation, ?_⟩
  intro agent comparison
  fin_cases agent
  · right
    intro item hitem
    have hitemFinal : item ∈ prefixAllocation 0 ∪ suffix 0 := by simpa using hitem
    have herase := additiveChoreCost_erase cost 0 (prefixAllocation 0 ∪ suffix 0) item hitemFinal
    change additiveChoreCost cost 0 ((prefixAllocation 0 ∪ suffix 0) \ {item}) ≤
      additiveChoreCost cost 0 (prefixAllocation comparison ∪ suffix comparison)
    rw [herase, hfinalCost 0 0,
      hsuffixZeroCostZero, hfinalCost 0 comparison]
    have hitemLower := hcostLower 0 item
    fin_cases comparison
    · change additiveChoreCost cost 0 (prefixAllocation 0) + 2 - cost 0 item ≤
        additiveChoreCost cost 0 (prefixAllocation 0) +
          additiveChoreCost cost 0 (suffix 0)
      rw [hsuffixZeroCostZero]
      linarith
    · change additiveChoreCost cost 0 (prefixAllocation 0) + 2 - cost 0 item ≤
        additiveChoreCost cost 0 (prefixAllocation 1) +
          additiveChoreCost cost 0 (suffix 1)
      rw [hsuffixOneCostZero]
      linarith
    · change additiveChoreCost cost 0 (prefixAllocation 0) + 2 - cost 0 item ≤
        additiveChoreCost cost 0 (prefixAllocation 2) +
          additiveChoreCost cost 0 (suffix 2)
      rw [hsuffixTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · change additiveChoreCost cost 0 (prefixAllocation 0) + 2 - cost 0 item ≤
        additiveChoreCost cost 0 (prefixAllocation 3) +
          additiveChoreCost cost 0 (suffix 3)
      rw [hsuffixThreeCostZero]
      linarith
  · right
    intro item hitem
    have hitemFinal : item ∈ prefixAllocation 1 ∪ suffix 1 := by simpa using hitem
    have herase := additiveChoreCost_erase cost 1 (prefixAllocation 1 ∪ suffix 1) item hitemFinal
    change additiveChoreCost cost 1 ((prefixAllocation 1 ∪ suffix 1) \ {item}) ≤
      additiveChoreCost cost 1 (prefixAllocation comparison ∪ suffix comparison)
    rw [herase, hfinalCost 1 1,
      hsuffixOneCostOne, hfinalCost 1 comparison]
    have hitemLower := hcostLower 1 item
    fin_cases comparison
    · change additiveChoreCost cost 1 (prefixAllocation 1) + (uOne.card : ℝ) - cost 1 item ≤
        additiveChoreCost cost 1 (prefixAllocation 0) +
          additiveChoreCost cost 1 (suffix 0)
      rw [hsuffixZeroCostOne]
      linarith
    · change additiveChoreCost cost 1 (prefixAllocation 1) + (uOne.card : ℝ) - cost 1 item ≤
        additiveChoreCost cost 1 (prefixAllocation 1) +
          additiveChoreCost cost 1 (suffix 1)
      rw [hsuffixOneCostOne]
      linarith
    · change additiveChoreCost cost 1 (prefixAllocation 1) + (uOne.card : ℝ) - cost 1 item ≤
        additiveChoreCost cost 1 (prefixAllocation 2) +
          additiveChoreCost cost 1 (suffix 2)
      rw [hsuffixTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · change additiveChoreCost cost 1 (prefixAllocation 1) + (uOne.card : ℝ) - cost 1 item ≤
        additiveChoreCost cost 1 (prefixAllocation 3) +
          additiveChoreCost cost 1 (suffix 3)
      rw [hsuffixThreeCostOne]
      linarith
  · by_cases hempty : prefixAllocation 2 = ∅
    · left
      simpa [hsuffixTwo] using hempty
    · right
      intro item hitem
      have hitemPrefix : item ∈ prefixAllocation 2 := by simpa [hsuffixTwo] using hitem
      rcases hprefixEFX 2 comparison with hprefixEmpty | hprefixBound
      · exact (hempty hprefixEmpty).elim
      · change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2) \ {item}) ≤
          additiveChoreCost cost 2 (prefixAllocation comparison ∪ suffix comparison)
        rw [hsuffixTwo, Finset.union_empty]
        calc
          additiveChoreCost cost 2 (prefixAllocation 2 \ {item}) ≤
              additiveChoreCost cost 2 (prefixAllocation comparison) :=
            hprefixBound item hitemPrefix
          _ ≤ additiveChoreCost cost 2 (prefixAllocation comparison ∪ suffix comparison) := by
            rw [hfinalCost 2 comparison]
            have hnonneg : 0 ≤ additiveChoreCost cost 2 (suffix comparison) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) 2 (suffix comparison)
            linarith
  · right
    intro item hitem
    have hitemFinal : item ∈ prefixAllocation 3 ∪ suffix 3 := by simpa using hitem
    have herase := additiveChoreCost_erase cost 3 (prefixAllocation 3 ∪ suffix 3) item hitemFinal
    change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3) \ {item}) ≤
      additiveChoreCost cost 3 (prefixAllocation comparison ∪ suffix comparison)
    rw [herase, hfinalCost 3 3,
      hsuffixThreeCostThree, hfinalCost 3 comparison]
    have hitemLower := hcostLower 3 item
    fin_cases comparison
    · change additiveChoreCost cost 3 (prefixAllocation 3) + 3 - cost 3 item ≤
        additiveChoreCost cost 3 (prefixAllocation 0) +
          additiveChoreCost cost 3 (suffix 0)
      rw [hsuffixZeroCostThree]
      linarith
    · change additiveChoreCost cost 3 (prefixAllocation 3) + 3 - cost 3 item ≤
        additiveChoreCost cost 3 (prefixAllocation 1) +
          additiveChoreCost cost 3 (suffix 1)
      rw [hsuffixOneCostThree]
      linarith
    · change additiveChoreCost cost 3 (prefixAllocation 3) + 3 - cost 3 item ≤
        additiveChoreCost cost 3 (prefixAllocation 2) +
          additiveChoreCost cost 3 (suffix 2)
      rw [hsuffixTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · change additiveChoreCost cost 3 (prefixAllocation 3) + 3 - cost 3 item ≤
        additiveChoreCost cost 3 (prefixAllocation 3) +
          additiveChoreCost cost 3 (suffix 3)
      rw [hsuffixThreeCostThree]
      linarith

/-- The two B.2.1(b) exceptional schedules stated with the library's M₂ type
pools.  The source's (3,3) and (4,3) multiplicities give a two-chore block
for agent 0, a one- or two-chore remainder for agent 1, and the three
complementary chores for agent 3. -/
theorem existsEfxOfB1DisjointExceptionalDirect_of_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 2) - r)
    (hcover : m2Chores =
      m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool cost m2Chores
      ({0, 1} : Finset (Fin 4))).card = 3 ∨
      (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card = 4)
    (hsecondCard : (m2TypeChorePool cost m2Chores
      ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let u := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let w := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have huCardLower : 2 ≤ u.card := by
    rcases hfirstCard with hthree | hfour
    · rw [show u.card = 3 by simpa [u] using hthree]
      omega
    · rw [show u.card = 4 by simpa [u] using hfour]
      omega
  obtain ⟨uZero, huZeroSub, huZeroCard⟩ := u.exists_subset_card_eq huCardLower
  let uOne := u \ uZero
  have huCover : uZero ∪ uOne = u := by
    simpa [uOne] using Finset.union_sdiff_of_subset huZeroSub
  have huZeroOne : Disjoint uZero uOne := by
    simpa [uOne] using (Finset.disjoint_sdiff : Disjoint uZero (u \ uZero))
  have huOneCard : uOne.card = u.card - 2 := by
    rw [show uOne = u \ uZero by rfl, Finset.card_sdiff_of_subset huZeroSub,
      huZeroCard]
  have huOneLower : 1 ≤ uOne.card := by
    rcases hfirstCard with hthree | hfour
    · rw [huOneCard, show u.card = 3 by simpa [u] using hthree]
    · rw [huOneCard, show u.card = 4 by simpa [u] using hfour]
      omega
  have huOneUpper : uOne.card ≤ 2 := by
    rcases hfirstCard with hthree | hfour
    · rw [huOneCard, show u.card = 3 by simpa [u] using hthree]
      omega
    · rw [huOneCard, show u.card = 4 by simpa [u] using hfour]
  have huw : Disjoint u w := by
    simpa [u, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  have huZeroW : Disjoint uZero w := Disjoint.mono huZeroSub (by rfl) huw
  have huOneW : Disjoint uOne w := by
    exact Disjoint.mono (by simpa [uOne] using (Finset.sdiff_subset : u \ uZero ⊆ u))
      (by rfl) huw
  have hcover' : m2Chores = (uZero ∪ uOne) ∪ w := by
    calc
      m2Chores = u ∪ w := by simpa [u, w] using hcover
      _ = (uZero ∪ uOne) ∪ w := by rw [huCover]
  apply existsEfxOfB1DisjointExceptionalDirect Item r cost prefixChores m2Chores
    uZero uOne w a quota prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hshortAdvantage hcover' huZeroOne huZeroW huOneW huZeroCard huOneLower
    huOneUpper (by simpa [w] using hsecondCard)
  · intro item hitem
    have hitemU : item ∈ u := by
      rw [← huCover]
      exact hitem
    have hitem' : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) := by
      simpa [u] using hitemU
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
      simpa [w] using hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 0 hcost hitem' (by decide)
    · simpa [IsLargeChore] using m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 1 hcost hitem' (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 2 hitem' (by decide)
    · simpa [IsSmallChore] using m2TypeChorePool_small_for_endpoint cost m2Chores
        ({2, 3} : Finset (Fin 4)) item 3 hitem' (by decide)

/-- The exceptional B.2.1(b) direct schedules transport back across the
identity-or-swap relabelling used to orient the canonical prefix. -/
theorem existsEfxOfB1DisjointExceptionalDirect_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost (relabelChoreCost labels cost) 3
      (prefixAllocation 3) ≤
        additiveChoreCost (relabelChoreCost labels cost) 3 (prefixAllocation 2) - r)
    (hcover : m2Chores =
      m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)) ∪
        m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4)))
    (hfirstCard : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card = 3 ∨
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4))).card = 4)
    (hsecondCard : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4))).card = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfB1DisjointExceptionalDirect_of_typePools Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a quota prefixAllocation hr
    (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hshortAdvantage hcover hfirstCard hsecondCard

end HT26EFXChores
