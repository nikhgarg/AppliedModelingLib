import HT26EFXChores.HighRatioGapFilling
import HT26EFXChores.M2SmallMatching

/-!
# The exceptional direct allocation in Case B.2.1(a)

This module records the seven-chore allocation used when the residual
exceptional pair is the high-multiplicity type itself.  The source replaces
the ordinary gap-fill/residual composition by this direct allocation.

Source: `EFXadditivechores.tex`, Case B.2.1(a), lines 2291--2324.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The representative direct allocation in source Case B.2.1(a), with
agent `0` the long agent.  The `u`, `v`, and `w` pools are respectively the
three type-`(0,1)` chores, the one type-`(1,2)` chore, and the three
type-`(2,3)` chores from the source's exceptional seven-chore configuration.

The statement spells out the resulting `{1,r}` type table instead of hiding
the finite construction in an allocation certificate. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u, cost 0 item = 1 ∧ cost 1 item = 1 ∧
      cost 2 item = r ∧ cost 3 item = r)
    (hv : ∀ item ∈ v, cost 0 item = r ∧ cost 1 item = 1 ∧
      cost 2 item = 1 ∧ cost 3 item = r)
    (hw : ∀ item ∈ w, cost 0 item = r ∧ cost 1 item = r ∧
      cost 2 item = 1 ∧ cost 3 item = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let wRest : Finset Item := w.erase head
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 u
  let suffixTwo : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 (v ∪ {head})
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 wRest
  let suffixTwelve : Allocation (Fin 4) Item := fun agent => suffixOne agent ∪ suffixTwo agent
  let suffix : Allocation (Fin 4) Item := fun agent => suffixTwelve agent ∪ suffixThree agent
  have huvHead : Disjoint u (v ∪ {head}) := by
    rw [Finset.disjoint_left]
    intro item huItem hright
    rcases Finset.mem_union.mp hright with hvItem | hheadItem
    · exact (Finset.disjoint_left.mp huv huItem hvItem).elim
    · have hitemEq : item = head := Finset.mem_singleton.mp hheadItem
      have hwItem : item ∈ w := by simpa [hitemEq] using hhead
      exact (Finset.disjoint_left.mp huw huItem hwItem).elim
  have hvHeadRest : Disjoint (v ∪ {head}) wRest := by
    rw [Finset.disjoint_left]
    intro item hleft hrest
    rcases Finset.mem_union.mp hleft with hvItem | hheadItem
    · have hrestW : item ∈ w := by
        exact Finset.erase_subset head w (by simpa [wRest] using hrest)
      exact (Finset.disjoint_left.mp hvw hvItem hrestW).elim
    · have hitemEq : item = head := Finset.mem_singleton.mp hheadItem
      subst item
      simpa [wRest] using hrest
  have hsuffixOne : IsAllocationOf suffixOne u := isAllocationOf_allocateAllTo 1 u
  have hsuffixTwo : IsAllocationOf suffixTwo (v ∪ {head}) :=
    isAllocationOf_allocateAllTo 2 (v ∪ {head})
  have hsuffixThree : IsAllocationOf suffixThree wRest :=
    isAllocationOf_allocateAllTo 3 wRest
  have hsuffixTwelve : IsAllocationOf suffixTwelve (u ∪ (v ∪ {head})) := by
    simpa [suffixTwelve] using isAllocationOf_union suffixOne suffixTwo u (v ∪ {head})
      huvHead hsuffixOne hsuffixTwo
  have huvHeadRest : Disjoint (u ∪ (v ∪ {head})) wRest := by
    rw [Finset.disjoint_left]
    intro item hleft hrest
    rcases Finset.mem_union.mp hleft with huItem | hvHeadItem
    · have hrestW : item ∈ w :=
        Finset.erase_subset head w (by simpa [wRest] using hrest)
      exact (Finset.disjoint_left.mp huw huItem hrestW).elim
    · exact (Finset.disjoint_left.mp hvHeadRest hvHeadItem hrest).elim
  have hsuffixAllocation : IsAllocationOf suffix (u ∪ v ∪ w) := by
    have hcombined := isAllocationOf_union suffixTwelve suffixThree
      (u ∪ (v ∪ {head})) wRest huvHeadRest hsuffixTwelve hsuffixThree
    have hgoods : (u ∪ (v ∪ {head})) ∪ wRest = u ∪ v ∪ w := by
      have hwDecomposition : ({head} : Finset Item) ∪ wRest = w := by
        simpa [wRest] using Finset.insert_erase hhead
      rw [← hwDecomposition]
      ac_rfl
    rw [hgoods] at hcombined
    simpa only [suffix] using hcombined
  have hsuffixZero : suffix 0 = ∅ := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixOneEq : suffix 1 = u := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixTwoEq : suffix 2 = v ∪ {head} := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixThreeEq : suffix 3 = wRest := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hprefixSuffix : Disjoint prefixChores (u ∪ v ∪ w) := by
    rw [← hcover]
    exact hprefixM2
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixSuffix
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hwRestCard : wRest.card = 2 := by
    dsimp [wRest]
    rw [Finset.card_erase_of_mem hhead, hwcard]
  have hvHeadDisjoint : Disjoint v ({head} : Finset Item) := by
    rw [Finset.disjoint_singleton_right]
    intro hvHead
    exact (Finset.disjoint_left.mp hvw hvHead hhead).elim
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = 3 := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 u 1
        (fun item hitem => (hu item hitem).2.1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostTwo : additiveChoreCost cost 2 (suffix 1) = 3 * r := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 u r
        (fun item hitem => (hu item hitem).2.2.1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostThree : additiveChoreCost cost 3 (suffix 1) = 3 * r := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 u r
        (fun item hitem => (hu item hitem).2.2.2), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixTwoCostOne : additiveChoreCost cost 1 (suffix 2) = r + 1 := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 1 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 v 1
        (fun item hitem => (hv item hitem).2.1), hvcard]
    simp [additiveChoreCost, hw head hhead |>.2.1, nsmul_eq_mul]
    ring
  have hsuffixTwoCostTwo : additiveChoreCost cost 2 (suffix 2) = 2 := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 2 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 v 1
        (fun item hitem => (hv item hitem).2.2.1), hvcard]
    simp [additiveChoreCost, hw head hhead |>.2.2.1, nsmul_eq_mul]
    norm_num
  have hsuffixTwoCostThree : additiveChoreCost cost 3 (suffix 2) = r + 1 := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 3 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 v r
        (fun item hitem => (hv item hitem).2.2.2), hvcard]
    simp [additiveChoreCost, hw head hhead |>.2.2.2, nsmul_eq_mul]
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = 2 * r := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 wRest r
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = 2 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 2 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.2), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hprefixEqual : ∀ first second : Fin 4, first ≠ 0 → second ≠ 0 →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second (by
        fin_cases first <;> fin_cases second <;>
          simp [hquota0, hquota1, hquota2, hquota3] at hfirst hsecond ⊢)
  have hshortUnit : ∀ agent : Fin 4, agent ≠ 0 → ∀ other,
      additiveChoreCost cost agent (prefixAllocation agent ∪ suffix agent) ≤
        additiveChoreCost cost agent (prefixAllocation other ∪ suffix other) + 1 := by
    intro agent hagent other
    fin_cases agent
    · exact (hagent rfl).elim
    · fin_cases other
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 1 1, hfinalCost 1 0, hsuffixOneCostOne, hsuffixZero]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 1 (by decide)]
      · linarith
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 1 1, hfinalCost 1 2, hsuffixOneCostOne, hsuffixTwoCostOne]
        linarith [hprefixEqual 1 2 (by decide) (by decide)]
      · change additiveChoreCost cost 1 (prefixAllocation 1 ∪ suffix 1) ≤
          additiveChoreCost cost 1 (prefixAllocation 3 ∪ suffix 3) + 1
        rw [hfinalCost 1 1, hfinalCost 1 3, hsuffixOneCostOne, hsuffixThreeCostOne]
        linarith [hprefixEqual 1 3 (by decide) (by decide)]
    · fin_cases other
      · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) ≤
          additiveChoreCost cost 2 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 2 2, hfinalCost 2 0, hsuffixTwoCostTwo, hsuffixZero]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 2 (by decide)]
      · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) ≤
          additiveChoreCost cost 2 (prefixAllocation 1 ∪ suffix 1) + 1
        rw [hfinalCost 2 2, hfinalCost 2 1, hsuffixTwoCostTwo, hsuffixOneCostTwo]
        linarith [hprefixEqual 2 1 (by decide) (by decide)]
      · linarith
      · change additiveChoreCost cost 2 (prefixAllocation 2 ∪ suffix 2) ≤
          additiveChoreCost cost 2 (prefixAllocation 3 ∪ suffix 3) + 1
        rw [hfinalCost 2 2, hfinalCost 2 3, hsuffixTwoCostTwo, hsuffixThreeCostTwo]
        linarith [hprefixEqual 2 3 (by decide) (by decide)]
    · fin_cases other
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 0 ∪ suffix 0) + 1
        rw [hfinalCost 3 3, hfinalCost 3 0, hsuffixThreeCostThree, hsuffixZero]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 3 (by decide)]
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 1 ∪ suffix 1) + 1
        rw [hfinalCost 3 3, hfinalCost 3 1, hsuffixThreeCostThree, hsuffixOneCostThree]
        linarith [hprefixEqual 3 1 (by decide) (by decide)]
      · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ suffix 3) ≤
          additiveChoreCost cost 3 (prefixAllocation 2 ∪ suffix 2) + 1
        rw [hfinalCost 3 3, hfinalCost 3 2, hsuffixThreeCostThree, hsuffixTwoCostThree]
        linarith [hprefixEqual 3 2 (by decide) (by decide)]
      · linarith
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf
      (fun agent => prefixAllocation agent ∪ suffix agent) (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union prefixAllocation suffix prefixChores (u ∪ v ∪ w)
      hprefixSuffix hcanonical.1 hsuffixAllocation
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
        have hprefixBound' :
            additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
              additiveChoreCost cost 0 (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost 0 (prefixAllocation 0) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
              additiveChoreCost cost 0 (prefixAllocation other) :=
            hprefixBound'
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
    linarith [hshortUnit 1 (by decide) other, hcostLower 1 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2).erase item) ≤
      additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 2 ∪ suffix 2 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 2 (prefixAllocation 2 ∪ suffix 2) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 2 (by decide) other, hcostLower 2 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
      additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 3 ∪ suffix 3 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3 ∪ suffix 3) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hshortUnit 3 (by decide) other, hcostLower 3 item]

/-- The counting deduction in source Case B.2.1(a).  After deleting two
chores of the maximum type `u` and one intersecting-type chore `v`, the
exceptional residue contains one `u` chore and `4q+3` chores of the disjoint
complementary type `w`.  As `u` was maximum, this forces `q = 0`, hence the
whole M₂ instance has the source's `3,1,3` type multiplicities.

This is stated for three disjoint finite pools so that the graph/type-fibre
identification is kept at the caller boundary rather than encoded in an
opaque exceptional-configuration certificate. -/
theorem b1_intersecting_exceptional_forces_313
    (Item : Type) [DecidableEq Item]
    (m2Chores u v w : Finset Item) (first second middle surviving : Item) (q : ℕ)
    (huSub : u ⊆ m2Chores) (hvSub : v ⊆ m2Chores) (hwSub : w ⊆ m2Chores)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hfirst : first ∈ u) (hsecond : second ∈ u) (hmiddle : middle ∈ v)
    (hsurviving : surviving ∈ u) (hfirstSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second, middle} = {surviving} ∪ w)
    (hwcardFormula : w.card = 4 * q + 3) (hmaximum : w.card ≤ u.card) :
    m2Chores = u ∪ v ∪ w ∧ u.card = 3 ∧ v.card = 1 ∧ w.card = 3 := by
  classical
  have hsurvivingResidue : surviving ∈ m2Chores \ {first, second, middle} := by
    rw [hresidue]
    simp
  have hsurvivingNotGap : surviving ∉ ({first, second, middle} : Finset Item) :=
    (Finset.mem_sdiff.mp hsurvivingResidue).2
  have hsurvivingFirst : surviving ≠ first := by
    intro hEq
    subst surviving
    exact hsurvivingNotGap (by simp)
  have hsurvivingSecond : surviving ≠ second := by
    intro hEq
    subst surviving
    exact hsurvivingNotGap (by simp)
  have huEq : u = {first, second, surviving} := by
    apply Finset.Subset.antisymm
    · intro item hitem
      have hitemM2 : item ∈ m2Chores := huSub hitem
      by_cases hgap : item ∈ ({first, second, middle} : Finset Item)
      · rcases (by simpa using hgap : item = first ∨ item = second ∨ item = middle) with
          hitemFirst | hitemSecond | hitemMiddle
        · simp [hitemFirst]
        · simp [hitemSecond]
        · subst item
          exact (Finset.disjoint_left.mp huv hitem hmiddle).elim
      · have hitemResidue : item ∈ m2Chores \ {first, second, middle} :=
          Finset.mem_sdiff.mpr ⟨hitemM2, hgap⟩
        rw [hresidue] at hitemResidue
        rcases Finset.mem_union.mp hitemResidue with hitemSurviving | hitemW
        · simp at hitemSurviving
          simp [hitemSurviving]
        · exact (Finset.disjoint_left.mp huw hitem hitemW).elim
    · intro item hitem
      rcases (by simpa using hitem : item = first ∨ item = second ∨ item = surviving) with
        hitemFirst | hitemSecond | hitemSurviving
      · simpa [hitemFirst] using hfirst
      · simpa [hitemSecond] using hsecond
      · simpa [hitemSurviving] using hsurviving
  have hucard : u.card = 3 := by
    rw [huEq]
    have hfirstNotRest : first ∉ ({second, surviving} : Finset Item) := by
      simp [hfirstSecond, hsurvivingFirst.symm]
    have hsecondNotSurviving : second ∉ ({surviving} : Finset Item) := by
      simp [hsurvivingSecond.symm]
    rw [Finset.card_insert_of_notMem hfirstNotRest,
      Finset.card_insert_of_notMem hsecondNotSurviving]
    norm_num
  have hqzero : q = 0 := by
    omega
  have hwcard : w.card = 3 := by
    omega
  have hvEq : v = {middle} := by
    apply Finset.Subset.antisymm
    · intro item hitem
      have hitemM2 : item ∈ m2Chores := hvSub hitem
      by_cases hgap : item ∈ ({first, second, middle} : Finset Item)
      · rcases (by simpa using hgap : item = first ∨ item = second ∨ item = middle) with
          hitemFirst | hitemSecond | hitemMiddle
        · subst item
          exact (Finset.disjoint_left.mp huv hfirst hitem).elim
        · subst item
          exact (Finset.disjoint_left.mp huv hsecond hitem).elim
        · simp [hitemMiddle]
      · have hitemResidue : item ∈ m2Chores \ {first, second, middle} :=
          Finset.mem_sdiff.mpr ⟨hitemM2, hgap⟩
        rw [hresidue] at hitemResidue
        rcases Finset.mem_union.mp hitemResidue with hitemSurviving | hitemW
        · simp at hitemSurviving
          subst item
          exact (Finset.disjoint_left.mp huv hsurviving hitem).elim
        · exact (Finset.disjoint_left.mp hvw hitem hitemW).elim
    · intro item hitem
      have hitemEq : item = middle := by simpa using hitem
      simpa [hitemEq] using hmiddle
  have hvcard : v.card = 1 := by simp [hvEq]
  refine ⟨?_, hucard, hvcard, hwcard⟩
  apply Finset.Subset.antisymm
  · intro item hitem
    by_cases hgap : item ∈ ({first, second, middle} : Finset Item)
    · rcases (by simpa using hgap : item = first ∨ item = second ∨ item = middle) with
        hitemFirst | hitemSecond | hitemMiddle
      · rw [hitemFirst]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hfirst)
      · rw [hitemSecond]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hsecond)
      · rw [hitemMiddle]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hmiddle)
    · have hitemResidue : item ∈ m2Chores \ {first, second, middle} :=
        Finset.mem_sdiff.mpr ⟨hitem, hgap⟩
      rw [hresidue] at hitemResidue
      rcases Finset.mem_union.mp hitemResidue with hitemSurviving | hitemW
      · have hitemEq : item = surviving := by simpa using hitemSurviving
        rw [hitemEq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hsurviving)
      · exact Finset.mem_union_right _ hitemW
  · intro item hitem
    rcases Finset.mem_union.mp hitem with hitemUV | hitemW
    · rcases Finset.mem_union.mp hitemUV with hitemU | hitemV
      · exact huSub hitemU
      · exact hvSub hitemV
    · exact hwSub hitemW

/-- A reusable direct-composition kernel for the one-long-agent
super-canonical cases in source Case B.2.2(b).  It keeps the displayed suffix
allocation explicit: short agents must have at most `r+1` suffix cost against
the empty long suffix and must be within one unit of every other short
suffix.  These are exactly the finite checks made by the two four-chore
schedules in the source. -/
theorem efxForChores_union_of_supercanonicalLongZeroAndControlledSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixZero : suffix 0 = ∅)
    (hshortLong : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤ r + 1)
    (hshortUnit : ∀ short other : Fin 4, short ≠ 0 → other ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤
        additiveChoreCost cost short (suffix other) + 1) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ m2Chores) ∧
      EFXForChores (additiveChoreCost cost) (fun agent => prefixAllocation agent ∪ suffix agent) := by
  classical
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
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
  have hprefixEqual : ∀ first second : Fin 4, first ≠ 0 → second ≠ 0 →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second (by
        fin_cases first <;> fin_cases second <;>
          simp [hquota0, hquota1, hquota2, hquota3] at hfirst hsecond ⊢)
  have hfinalShortUnit : ∀ short : Fin 4, short ≠ 0 → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    by_cases hother : other = 0
    · subst other
      rw [hfinalCost short short, hfinalCost short 0, hsuffixZero]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper short hshort, hshortLong short hshort]
    · rw [hfinalCost short short, hfinalCost short other]
      linarith [hprefixEqual short other hshort hother, hshortUnit short other hshort hother]
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores m2Chores hprefixM2
    hcanonical.1 hsuffixAllocation, ?_⟩
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
        have hprefixBound' :
            additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
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
    linarith [hfinalShortUnit 1 (by decide) other, hcostLower 1 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2).erase item) ≤
      additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 2 ∪ suffix 2 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 2 (prefixAllocation 2 ∪ suffix 2) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit 2 (by decide) other, hcostLower 2 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
      additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 3 ∪ suffix 3 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3 ∪ suffix 3) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit 3 (by decide) other, hcostLower 3 item]

/-- A label-independent form of the controlled-suffix composition used in
source Case B.2.1(a).  A super-canonical prefix has one long agent, whose
suffix is empty; every short suffix is within one unit of every other short
suffix and costs at most `r + 1` to its owner.  These numerical conditions
are precisely what is needed to retain EFX after the direct finite schedule.
-/
theorem efxForChores_union_of_supercanonicalLongAndControlledSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (long : Fin 4) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquotaLong : quota long = a + 1)
    (hquotaShort : ∀ short : Fin 4, short ≠ long → quota short = a)
    (hsuper : ∀ short : Fin 4, short ≠ long →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixLong : suffix long = ∅)
    (hshortLong : ∀ short : Fin 4, short ≠ long →
      additiveChoreCost cost short (suffix short) ≤ r + 1)
    (hshortUnit : ∀ short other : Fin 4, short ≠ long → other ≠ long →
      additiveChoreCost cost short (suffix short) ≤
        additiveChoreCost cost short (suffix other) + 1) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ m2Chores) ∧
      EFXForChores (additiveChoreCost cost) (fun agent => prefixAllocation agent ∪ suffix agent) := by
  classical
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    by_cases hown : own = long
    · subst own
      by_cases hcomparison : comparison = long
      · subst comparison
        omega
      · rw [hquotaLong, hquotaShort comparison hcomparison]
    · by_cases hcomparison : comparison = long
      · subst comparison
        rw [hquotaShort own hown, hquotaLong]
        omega
      · rw [hquotaShort own hown, hquotaShort comparison hcomparison]
        omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hprefixEqual : ∀ first second : Fin 4, first ≠ long → second ≠ long →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    apply hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second
    rw [hquotaShort first hfirst, hquotaShort second hsecond]
  have hfinalShortUnit : ∀ short : Fin 4, short ≠ long → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    by_cases hother : other = long
    · subst other
      rw [hfinalCost short short, hfinalCost short long, hsuffixLong]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper short hshort, hshortLong short hshort]
    · rw [hfinalCost short short, hfinalCost short other]
      linarith [hprefixEqual short other hshort hother, hshortUnit short other hshort hother]
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores m2Chores hprefixM2
    hcanonical.1 hsuffixAllocation, ?_⟩
  intro agent other
  by_cases hagent : agent = long
  · subst agent
    by_cases hempty : prefixAllocation long = ∅
    · left
      simpa [hsuffixLong] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation long := by simpa [hsuffixLong] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX long other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost long ((prefixAllocation long ∪ suffix long).erase item) ≤
          additiveChoreCost cost long (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost long (prefixAllocation long) item hprefixItem
        rw [hsuffixLong, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' :
            additiveChoreCost cost long (prefixAllocation long) - cost long item ≤
              additiveChoreCost cost long (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost long (prefixAllocation long) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost long (prefixAllocation long) - cost long item ≤
              additiveChoreCost cost long (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost long (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost long other]
            have hnonneg : 0 ≤ additiveChoreCost cost long (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) long (suffix other)
            linarith
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    have hitem' : item ∈ prefixAllocation agent ∪ suffix agent := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost agent (prefixAllocation agent ∪ suffix agent)
      item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit agent hagent other, hcostLower agent item]

/-- The second direct schedule in source Case B.2.1(a), where the internal
agent `1` is long.  The source assigns the three type-`(0,1)` chores to
agent `0`, leaves the long agent without an M₂ chore, and uses the same two
right-hand bundles as in the endpoint-long schedule. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longOne
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 1) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u, cost 0 item = 1 ∧ cost 1 item = 1 ∧
      cost 2 item = r ∧ cost 3 item = r)
    (hv : ∀ item ∈ v, cost 0 item = r ∧ cost 1 item = 1 ∧
      cost 2 item = 1 ∧ cost 3 item = r)
    (hw : ∀ item ∈ w, cost 0 item = r ∧ cost 1 item = r ∧
      cost 2 item = 1 ∧ cost 3 item = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let wRest : Finset Item := w.erase head
  let suffixZero : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 u
  let suffixTwo : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 (v ∪ {head})
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 wRest
  let suffixZeroTwo : Allocation (Fin 4) Item := fun agent => suffixZero agent ∪ suffixTwo agent
  let suffix : Allocation (Fin 4) Item := fun agent => suffixZeroTwo agent ∪ suffixThree agent
  have huvHead : Disjoint u (v ∪ {head}) := by
    rw [Finset.disjoint_left]
    intro item huItem hright
    rcases Finset.mem_union.mp hright with hvItem | hheadItem
    · exact (Finset.disjoint_left.mp huv huItem hvItem).elim
    · have hitemEq : item = head := Finset.mem_singleton.mp hheadItem
      have hwItem : item ∈ w := by simpa [hitemEq] using hhead
      exact (Finset.disjoint_left.mp huw huItem hwItem).elim
  have hvHeadRest : Disjoint (v ∪ {head}) wRest := by
    rw [Finset.disjoint_left]
    intro item hleft hrest
    rcases Finset.mem_union.mp hleft with hvItem | hheadItem
    · have hrestW : item ∈ w :=
        Finset.erase_subset head w (by simpa [wRest] using hrest)
      exact (Finset.disjoint_left.mp hvw hvItem hrestW).elim
    · have hitemEq : item = head := Finset.mem_singleton.mp hheadItem
      subst item
      simpa [wRest] using hrest
  have hsuffixZero : IsAllocationOf suffixZero u := isAllocationOf_allocateAllTo 0 u
  have hsuffixTwo : IsAllocationOf suffixTwo (v ∪ {head}) :=
    isAllocationOf_allocateAllTo 2 (v ∪ {head})
  have hsuffixThree : IsAllocationOf suffixThree wRest :=
    isAllocationOf_allocateAllTo 3 wRest
  have hsuffixZeroTwo : IsAllocationOf suffixZeroTwo (u ∪ (v ∪ {head})) := by
    simpa [suffixZeroTwo] using isAllocationOf_union suffixZero suffixTwo u (v ∪ {head})
      huvHead hsuffixZero hsuffixTwo
  have hzeroTwoRest : Disjoint (u ∪ (v ∪ {head})) wRest := by
    rw [Finset.disjoint_left]
    intro item hleft hrest
    rcases Finset.mem_union.mp hleft with huItem | hvHeadItem
    · have hrestW : item ∈ w :=
        Finset.erase_subset head w (by simpa [wRest] using hrest)
      exact (Finset.disjoint_left.mp huw huItem hrestW).elim
    · exact (Finset.disjoint_left.mp hvHeadRest hvHeadItem hrest).elim
  have hsuffixAllocation : IsAllocationOf suffix (u ∪ v ∪ w) := by
    have hcombined := isAllocationOf_union suffixZeroTwo suffixThree
      (u ∪ (v ∪ {head})) wRest hzeroTwoRest hsuffixZeroTwo hsuffixThree
    have hgoods : (u ∪ (v ∪ {head})) ∪ wRest = u ∪ v ∪ w := by
      have hwDecomposition : ({head} : Finset Item) ∪ wRest = w := by
        simpa [wRest] using Finset.insert_erase hhead
      rw [← hwDecomposition]
      ac_rfl
    rw [hgoods] at hcombined
    simpa only [suffix] using hcombined
  have hsuffixZeroEq : suffix 0 = u := by
    simp [suffix, suffixZeroTwo, suffixZero, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixOneEq : suffix 1 = ∅ := by
    simp [suffix, suffixZeroTwo, suffixZero, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixTwoEq : suffix 2 = v ∪ {head} := by
    simp [suffix, suffixZeroTwo, suffixZero, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixThreeEq : suffix 3 = wRest := by
    simp [suffix, suffixZeroTwo, suffixZero, suffixTwo, suffixThree, allocateAllTo]
  have hwRestCard : wRest.card = 2 := by
    dsimp [wRest]
    rw [Finset.card_erase_of_mem hhead, hwcard]
  have hvHeadDisjoint : Disjoint v ({head} : Finset Item) := by
    rw [Finset.disjoint_singleton_right]
    intro hvHead
    exact (Finset.disjoint_left.mp hvw hvHead hhead).elim
  have hsuffixZeroCostZero : additiveChoreCost cost 0 (suffix 0) = 3 := by
    rw [hsuffixZeroEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 u 1
        (fun item hitem => (hu item hitem).1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixZeroCostTwo : additiveChoreCost cost 2 (suffix 0) = 3 * r := by
    rw [hsuffixZeroEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 u r
        (fun item hitem => (hu item hitem).2.2.1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixZeroCostThree : additiveChoreCost cost 3 (suffix 0) = 3 * r := by
    rw [hsuffixZeroEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 u r
        (fun item hitem => (hu item hitem).2.2.2), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixTwoCostZero : additiveChoreCost cost 0 (suffix 2) = 2 * r := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 0 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 v r
        (fun item hitem => (hv item hitem).1), hvcard]
    simp [additiveChoreCost, hw head hhead |>.1, nsmul_eq_mul]
    ring
  have hsuffixTwoCostTwo : additiveChoreCost cost 2 (suffix 2) = 2 := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 2 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 v 1
        (fun item hitem => (hv item hitem).2.2.1), hvcard]
    simp [additiveChoreCost, hw head hhead |>.2.2.1, nsmul_eq_mul]
    norm_num
  have hsuffixTwoCostThree : additiveChoreCost cost 3 (suffix 2) = r + 1 := by
    rw [hsuffixTwoEq, additiveChoreCost_union cost 3 v {head} hvHeadDisjoint,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 v r
        (fun item hitem => (hv item hitem).2.2.2), hvcard]
    simp [additiveChoreCost, hw head hhead |>.2.2.2, nsmul_eq_mul]
  have hsuffixThreeCostZero : additiveChoreCost cost 0 (suffix 3) = 2 * r := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 wRest r
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = 2 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 2 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.2), hwRestCard]
    norm_num [nsmul_eq_mul]
  refine ⟨fun agent => prefixAllocation agent ∪ suffix agent, ?_⟩
  exact efxForChores_union_of_supercanonicalLongAndControlledSuffix Item r cost
    prefixChores m2Chores a 1 quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
    hquota1 (by
      intro short hshort
      fin_cases short
      · exact hquota0
      · exact (hshort rfl).elim
      · exact hquota2
      · exact hquota3) hsuper (by simpa [hcover] using hsuffixAllocation) hsuffixOneEq
    (by
      intro short hshort
      fin_cases short
      · change additiveChoreCost cost 0 (suffix 0) ≤ r + 1
        rw [hsuffixZeroCostZero]
        linarith
      · exact (hshort rfl).elim
      · change additiveChoreCost cost 2 (suffix 2) ≤ r + 1
        rw [hsuffixTwoCostTwo]
        linarith
      · change additiveChoreCost cost 3 (suffix 3) ≤ r + 1
        rw [hsuffixThreeCostThree]
        linarith)
    (by
      intro short other hshort hother
      fin_cases short
      · fin_cases other
        · linarith
        · exact (hother rfl).elim
        · change additiveChoreCost cost 0 (suffix 0) ≤
            additiveChoreCost cost 0 (suffix 2) + 1
          rw [hsuffixZeroCostZero, hsuffixTwoCostZero]
          linarith
        · change additiveChoreCost cost 0 (suffix 0) ≤
            additiveChoreCost cost 0 (suffix 3) + 1
          rw [hsuffixZeroCostZero, hsuffixThreeCostZero]
          linarith
      · exact (hshort rfl).elim
      · fin_cases other
        · change additiveChoreCost cost 2 (suffix 2) ≤
            additiveChoreCost cost 2 (suffix 0) + 1
          rw [hsuffixTwoCostTwo, hsuffixZeroCostTwo]
          linarith
        · exact (hother rfl).elim
        · linarith
        · change additiveChoreCost cost 2 (suffix 2) ≤
            additiveChoreCost cost 2 (suffix 3) + 1
          rw [hsuffixTwoCostTwo, hsuffixThreeCostTwo]
          linarith
      · fin_cases other
        · change additiveChoreCost cost 3 (suffix 3) ≤
            additiveChoreCost cost 3 (suffix 0) + 1
          rw [hsuffixThreeCostThree, hsuffixZeroCostThree]
          linarith
        · exact (hother rfl).elim
        · change additiveChoreCost cost 3 (suffix 3) ≤
            additiveChoreCost cost 3 (suffix 2) + 1
          rw [hsuffixThreeCostThree, hsuffixTwoCostThree]
          linarith
        · linarith)

/-- The source-faithful composition used for the `|M₂| ≤ 3` branch of
Case B.2.2(b).  The prefix is merely canonical: a short agent has one fewer
small chore than the long agent, so receiving at most one small M₂ chore
still leaves her no more costly than the long bundle. -/
theorem efxForChores_union_of_canonicalLongZeroAndUnitSmallSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixZero : suffix 0 = ∅)
    (hshortSmall : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ suffix short,
      IsSmallChore cost short item)
    (hshortCard : ∀ short : Fin 4, short ≠ 0 → (suffix short).card ≤ 1) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ m2Chores) ∧
      EFXForChores (additiveChoreCost cost) (fun agent => prefixAllocation agent ∪ suffix agent) := by
  classical
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
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
  have hprefixEqual : ∀ first second : Fin 4, first ≠ 0 → second ≠ 0 →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second (by
        fin_cases first <;> fin_cases second <;>
          simp [hquota0, hquota1, hquota2, hquota3] at hfirst hsecond ⊢)
  have hshortCost (short : Fin 4) (hshort : short ≠ 0) :
      additiveChoreCost cost short (suffix short) = (suffix short).card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost short (suffix short) 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simpa [IsSmallChore] using hshortSmall short hshort item hitem
  have hfinalShortUnit : ∀ short : Fin 4, short ≠ 0 → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    by_cases hother : other = 0
    · subst other
      rw [hfinalCost short short, hfinalCost short 0, hsuffixZero]
      simp only [additiveChoreCost_empty, add_zero]
      have hquotaSucc : quota 0 = quota short + 1 := by
        fin_cases short <;> simp [hquota0, hquota1, hquota2, hquota3] at hshort ⊢
      have hprefixGap := hcanonical.additive_add_one_le_of_quota_succ cost r
        prefixChores quota prefixAllocation hcost (by linarith) short 0 hquotaSucc
      rw [hshortCost short hshort]
      have hcard := hshortCard short hshort
      have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith
    · rw [hfinalCost short short, hfinalCost short other]
      rw [hshortCost short hshort]
      have hcard := hshortCard short hshort
      have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have hnonneg : 0 ≤ additiveChoreCost cost short (suffix other) :=
        additiveChoreCost_nonneg cost
          (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) short (suffix other)
      linarith [hprefixEqual short other hshort hother]
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores m2Chores hprefixM2
    hcanonical.1 hsuffixAllocation, ?_⟩
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
        have hprefixBound' :
            additiveChoreCost cost 0 (prefixAllocation 0) - cost 0 item ≤
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
    linarith [hfinalShortUnit 1 (by decide) other, hcostLower 1 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 2 ((prefixAllocation 2 ∪ suffix 2).erase item) ≤
      additiveChoreCost cost 2 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 2 ∪ suffix 2 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 2 (prefixAllocation 2 ∪ suffix 2) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit 2 (by decide) other, hcostLower 2 item]
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    change additiveChoreCost cost 3 ((prefixAllocation 3 ∪ suffix 3).erase item) ≤
      additiveChoreCost cost 3 (prefixAllocation other ∪ suffix other)
    have hitem' : item ∈ prefixAllocation 3 ∪ suffix 3 := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost 3 (prefixAllocation 3 ∪ suffix 3) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit 3 (by decide) other, hcostLower 3 item]

/-- The direct-matching kernel used in source Case B.2.2(b) when at most
three M₂ chores remain.  A suffix allocation that leaves the long agent empty
and gives each short agent at most one chore that is small for her composes
with a super-canonical prefix to an EFX allocation. -/
theorem existsEfxOfB1LowMultiplicity_smallMatching_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixZero : suffix 0 = ∅)
    (hshortSmall : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ suffix short,
      IsSmallChore cost short item)
    (hshortCard : ∀ short : Fin 4, short ≠ 0 → (suffix short).card ≤ 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hshortCost (short : Fin 4) (hshort : short ≠ 0) :
      additiveChoreCost cost short (suffix short) = (suffix short).card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost short (suffix short) 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simpa [IsSmallChore] using hshortSmall short hshort item hitem
  have hshortLong : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤ r + 1 := by
    intro short hshort
    rw [hshortCost short hshort]
    have hcard := hshortCard short hshort
    have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    linarith
  have hshortUnit : ∀ short other : Fin 4, short ≠ 0 → other ≠ 0 →
      additiveChoreCost cost short (suffix short) ≤
        additiveChoreCost cost short (suffix other) + 1 := by
    intro short other hshort _hother
    rw [hshortCost short hshort]
    have hcard := hshortCard short hshort
    have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have hnonneg : 0 ≤ additiveChoreCost cost short (suffix other) :=
      additiveChoreCost_nonneg cost
        (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) short (suffix other)
    linarith
  refine ⟨fun agent => prefixAllocation agent ∪ suffix agent, ?_, ?_⟩
  · exact (efxForChores_union_of_supercanonicalLongZeroAndControlledSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixZero hshortLong hshortUnit).1
  · exact (efxForChores_union_of_supercanonicalLongZeroAndControlledSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hsuffixAllocation hsuffixZero hshortLong hshortUnit).2

/-- The source's `|M₂|≤3` direct allocation, expressed through an injective
choice of small endpoints.  The endpoint allocation is concrete, and the
unused endpoint is the long agent of the super-canonical prefix. -/
theorem existsEfxOfB1LowMultiplicity_smallMatchingOfEndpoint_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (endpoint : { item // item ∈ m2Chores } → Fin 4)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hinjective : Function.Injective endpoint)
    (hendpointSmall : ∀ item, IsSmallChore cost (endpoint item) item)
    (hunused : ∀ item, endpoint item ≠ 0) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfB1LowMultiplicity_smallMatching_longZero Item r cost
    prefixChores m2Chores a quota prefixAllocation (smallEndpointAllocation m2Chores endpoint)
    hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper
  · exact isAllocationOf_smallEndpointAllocation Item m2Chores endpoint
  · exact smallEndpointAllocation_eq_empty_of_unused Item m2Chores endpoint 0 hunused
  · intro short hshort item hitem
    exact smallEndpointAllocation_mem_small Item cost m2Chores endpoint hendpointSmall short item hitem
  · intro short _hshort
    exact smallEndpointAllocation_card_le_one_of_injective Item m2Chores endpoint hinjective short

/-- The direct-matching kernel used in source Case B.2.2(b) when at most
three M₂ chores remain.  Unlike the preceding auxiliary result, this is the
paper's canonical-prefix argument: the long agent has quota `a + 1`, each
short agent quota `a`, and every matched M₂ chore is small for its endpoint. -/
theorem existsEfxOfB1LowMultiplicity_smallMatchingCanonical_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixZero : suffix 0 = ∅)
    (hshortSmall : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ suffix short,
      IsSmallChore cost short item)
    (hshortCard : ∀ short : Fin 4, short ≠ 0 → (suffix short).card ≤ 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent,
    efxForChores_union_of_canonicalLongZeroAndUnitSmallSuffix Item r cost
      prefixChores m2Chores a quota prefixAllocation suffix hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuffixAllocation hsuffixZero hshortSmall hshortCard⟩

/-- The source's `|M₂|≤3` direct allocation, expressed through an injective
choice of small endpoints.  The unused endpoint is the long agent of the
canonical prefix. -/
theorem existsEfxOfB1LowMultiplicity_smallMatchingOfEndpointCanonical_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (endpoint : { item // item ∈ m2Chores } → Fin 4)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hinjective : Function.Injective endpoint)
    (hendpointSmall : ∀ item, IsSmallChore cost (endpoint item) item)
    (hunused : ∀ item, endpoint item ≠ 0) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfB1LowMultiplicity_smallMatchingCanonical_longZero Item r cost
    prefixChores m2Chores a quota prefixAllocation (smallEndpointAllocation m2Chores endpoint)
    hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
  · exact isAllocationOf_smallEndpointAllocation Item m2Chores endpoint
  · exact smallEndpointAllocation_eq_empty_of_unused Item m2Chores endpoint 0 hunused
  · intro short hshort item hitem
    exact smallEndpointAllocation_mem_small Item cost m2Chores endpoint hendpointSmall short item hitem
  · intro short _hshort
    exact smallEndpointAllocation_card_le_one_of_injective Item m2Chores endpoint hinjective short

/-- The canonical-prefix composition for an arbitrary choice of long agent.
This is the label-invariant form of the source's `|M₂|≤3` matching argument. -/
theorem efxForChores_union_of_canonicalLongAndUnitSmallSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (long : Fin 4) (quota : Fin 4 → ℕ)
    (prefixAllocation suffix : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquotaLong : quota long = a + 1)
    (hquotaShort : ∀ short : Fin 4, short ≠ long → quota short = a)
    (hsuffixAllocation : IsAllocationOf suffix m2Chores) (hsuffixLong : suffix long = ∅)
    (hshortSmall : ∀ short : Fin 4, short ≠ long → ∀ item ∈ suffix short,
      IsSmallChore cost short item)
    (hshortCard : ∀ short : Fin 4, short ≠ long → (suffix short).card ≤ 1) :
    IsAllocationOf (fun agent => prefixAllocation agent ∪ suffix agent)
      (prefixChores ∪ m2Chores) ∧
      EFXForChores (additiveChoreCost cost) (fun agent => prefixAllocation agent ∪ suffix agent) := by
  classical
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ suffix owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (suffix owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (suffix owner)
      (hbundlesDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    by_cases hown : own = long
    · subst own
      by_cases hcomparison : comparison = long
      · subst comparison
        omega
      · rw [hquotaLong, hquotaShort comparison hcomparison]
    · by_cases hcomparison : comparison = long
      · subst comparison
        rw [hquotaShort own hown, hquotaLong]
        omega
      · rw [hquotaShort own hown, hquotaShort comparison hcomparison]
        omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hprefixEqual : ∀ first second : Fin 4, first ≠ long → second ≠ long →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    apply hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second
    rw [hquotaShort first hfirst, hquotaShort second hsecond]
  have hshortCost (short : Fin 4) (hshort : short ≠ long) :
      additiveChoreCost cost short (suffix short) = (suffix short).card := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost short (suffix short) 1]
    · simp [nsmul_eq_mul]
    · intro item hitem
      simpa [IsSmallChore] using hshortSmall short hshort item hitem
  have hfinalShortUnit : ∀ short : Fin 4, short ≠ long → ∀ other,
      additiveChoreCost cost short (prefixAllocation short ∪ suffix short) ≤
        additiveChoreCost cost short (prefixAllocation other ∪ suffix other) + 1 := by
    intro short hshort other
    by_cases hother : other = long
    · subst other
      rw [hfinalCost short short, hfinalCost short long, hsuffixLong]
      simp only [additiveChoreCost_empty, add_zero]
      have hquotaSucc : quota long = quota short + 1 := by
        rw [hquotaLong, hquotaShort short hshort]
      have hprefixGap := hcanonical.additive_add_one_le_of_quota_succ cost r
        prefixChores quota prefixAllocation hcost (by linarith) short long hquotaSucc
      rw [hshortCost short hshort]
      have hcard := hshortCard short hshort
      have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith
    · rw [hfinalCost short short, hfinalCost short other]
      rw [hshortCost short hshort]
      have hcard := hshortCard short hshort
      have hcardReal : ((suffix short).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have hnonneg : 0 ≤ additiveChoreCost cost short (suffix other) :=
        additiveChoreCost_nonneg cost
          (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) short (suffix other)
      linarith [hprefixEqual short other hshort hother]
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  refine ⟨isAllocationOf_union prefixAllocation suffix prefixChores m2Chores hprefixM2
    hcanonical.1 hsuffixAllocation, ?_⟩
  intro agent other
  by_cases hagent : agent = long
  · subst agent
    by_cases hempty : prefixAllocation long = ∅
    · left
      simpa [hsuffixLong] using hempty
    · right
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation long := by simpa [hsuffixLong] using hitem
      obtain hprefixEmpty | hprefixBound := hprefixEFX long other
      · exact (hempty hprefixEmpty).elim
      · simp only [Finset.sdiff_singleton_eq_erase]
        change additiveChoreCost cost long ((prefixAllocation long ∪ suffix long).erase item) ≤
          additiveChoreCost cost long (prefixAllocation other ∪ suffix other)
        have hremoved := additiveChoreCost_erase cost long (prefixAllocation long) item hprefixItem
        rw [hsuffixLong, Finset.union_empty, ← Finset.sdiff_singleton_eq_erase, hremoved]
        have hprefixBound' :
            additiveChoreCost cost long (prefixAllocation long) - cost long item ≤
              additiveChoreCost cost long (prefixAllocation other) := by
          rw [← additiveChoreCost_erase cost long (prefixAllocation long) item hprefixItem]
          exact hprefixBound item hprefixItem
        calc
          additiveChoreCost cost long (prefixAllocation long) - cost long item ≤
              additiveChoreCost cost long (prefixAllocation other) := hprefixBound'
          _ ≤ additiveChoreCost cost long (prefixAllocation other ∪ suffix other) := by
            rw [hfinalCost long other]
            have hnonneg : 0 ≤ additiveChoreCost cost long (suffix other) :=
              additiveChoreCost_nonneg cost
                (IsOneOrRChoreCost.nonneg cost r hcost (by linarith)) long (suffix other)
            linarith
  · right
    intro item hitem
    simp only [Finset.sdiff_singleton_eq_erase]
    have hitem' : item ∈ prefixAllocation agent ∪ suffix agent := by simpa using hitem
    have hremoved := additiveChoreCost_erase cost agent (prefixAllocation agent ∪ suffix agent) item hitem'
    rw [← Finset.sdiff_singleton_eq_erase, hremoved]
    linarith [hfinalShortUnit agent hagent other, hcostLower agent item]

/-- The first explicit four-chore schedule in source Case B.2.2(b): two
type-`(0,1)` chores go to short agent `1`, and the two type-`(2,3)` chores go
one each to short agents `2` and `3`; agent `0` is long and receives no M₂
chore. -/
theorem existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hcover : m2Chores = u ∪ w) (huw : Disjoint u w)
    (hucard : u.card = 2) (hwcard : w.card = 2) (hhead : head ∈ w)
    (hu : ∀ item ∈ u, cost 0 item = 1 ∧ cost 1 item = 1 ∧
      cost 2 item = r ∧ cost 3 item = r)
    (hw : ∀ item ∈ w, cost 0 item = r ∧ cost 1 item = r ∧
      cost 2 item = 1 ∧ cost 3 item = 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let wRest : Finset Item := w.erase head
  let suffixOne : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 u
  let suffixTwo : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 {head}
  let suffixThree : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 wRest
  let suffixTwelve : Allocation (Fin 4) Item := fun agent => suffixOne agent ∪ suffixTwo agent
  let suffix : Allocation (Fin 4) Item := fun agent => suffixTwelve agent ∪ suffixThree agent
  have huHead : Disjoint u ({head} : Finset Item) := by
    rw [Finset.disjoint_singleton_right]
    intro hitem
    exact (Finset.disjoint_left.mp huw hitem hhead).elim
  have hheadWRest : Disjoint ({head} : Finset Item) wRest := by
    rw [Finset.disjoint_singleton_left]
    simpa [wRest]
  have huWRest : Disjoint u wRest := by
    apply Disjoint.mono (le_rfl) (Finset.erase_subset head w)
    exact huw
  have huHeadWRest : Disjoint (u ∪ ({head} : Finset Item)) wRest := by
    rw [Finset.disjoint_left]
    intro item hleft hrest
    rcases Finset.mem_union.mp hleft with hitemU | hitemHead
    · exact (Finset.disjoint_left.mp huWRest hitemU hrest).elim
    · exact (Finset.disjoint_left.mp hheadWRest hitemHead hrest).elim
  have hsuffixOne : IsAllocationOf suffixOne u := isAllocationOf_allocateAllTo 1 u
  have hsuffixTwo : IsAllocationOf suffixTwo {head} := isAllocationOf_allocateAllTo 2 {head}
  have hsuffixThree : IsAllocationOf suffixThree wRest := isAllocationOf_allocateAllTo 3 wRest
  have hsuffixTwelve : IsAllocationOf suffixTwelve (u ∪ {head}) := by
    simpa [suffixTwelve] using isAllocationOf_union suffixOne suffixTwo u {head}
      huHead hsuffixOne hsuffixTwo
  have hsuffixAllocation : IsAllocationOf suffix (u ∪ w) := by
    have hcombined := isAllocationOf_union suffixTwelve suffixThree (u ∪ {head}) wRest
      huHeadWRest hsuffixTwelve hsuffixThree
    have hwDecomposition : ({head} : Finset Item) ∪ wRest = w := by
      simpa [wRest] using Finset.insert_erase hhead
    have hgoods : (u ∪ ({head} : Finset Item)) ∪ wRest = u ∪ w := by
      rw [← hwDecomposition]
      ac_rfl
    rw [hgoods] at hcombined
    simpa only [suffix] using hcombined
  have hsuffixZero : suffix 0 = ∅ := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixOneEq : suffix 1 = u := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixTwoEq : suffix 2 = {head} := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hsuffixThreeEq : suffix 3 = wRest := by
    simp [suffix, suffixTwelve, suffixOne, suffixTwo, suffixThree, allocateAllTo]
  have hwRestCard : wRest.card = 1 := by
    dsimp [wRest]
    rw [Finset.card_erase_of_mem hhead, hwcard]
  have hsuffixOneCostOne : additiveChoreCost cost 1 (suffix 1) = 2 := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 u 1
        (fun item hitem => (hu item hitem).2.1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostTwo : additiveChoreCost cost 2 (suffix 1) = 2 * r := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 u r
        (fun item hitem => (hu item hitem).2.2.1), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixOneCostThree : additiveChoreCost cost 3 (suffix 1) = 2 * r := by
    rw [hsuffixOneEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 u r
        (fun item hitem => (hu item hitem).2.2.2), hucard]
    norm_num [nsmul_eq_mul]
  have hsuffixTwoCostOne : additiveChoreCost cost 1 (suffix 2) = r := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, hw head hhead |>.2.1]
  have hsuffixTwoCostTwo : additiveChoreCost cost 2 (suffix 2) = 1 := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, hw head hhead |>.2.2.1]
  have hsuffixTwoCostThree : additiveChoreCost cost 3 (suffix 2) = 1 := by
    rw [hsuffixTwoEq]
    simp [additiveChoreCost, hw head hhead |>.2.2.2]
  have hsuffixThreeCostOne : additiveChoreCost cost 1 (suffix 3) = r := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 1 wRest r
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostTwo : additiveChoreCost cost 2 (suffix 3) = 1 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 2 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.1), hwRestCard]
    norm_num [nsmul_eq_mul]
  have hsuffixThreeCostThree : additiveChoreCost cost 3 (suffix 3) = 1 := by
    rw [hsuffixThreeEq,
      additiveChoreCost_eq_card_nsmul_of_constant cost 3 wRest 1
        (fun item hitem => (hw item
          (Finset.mem_erase.mp (by simpa [wRest] using hitem)).2).2.2.2), hwRestCard]
    norm_num [nsmul_eq_mul]
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
    prefixChores (u ∪ w) a quota prefixAllocation suffix hr hcost
    (by simpa [hcover] using hprefixM2) hcanonical hquota0 hquota1 hquota2 hquota3 hsuper
    hsuffixAllocation hsuffixZero hshortLong hshortUnit
  exact ⟨fun agent => prefixAllocation agent ∪ suffix agent,
    (by simpa [hcover] using hfinal.1), (by simpa [hcover] using hfinal.2)⟩

/-- The preceding B.2.2(b) double-disjoint schedule, stated directly with
the M₂ type fibres used by AppliedModelingLib. -/
theorem existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero_of_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hcover : m2Chores = u ∪ w) (hucard : u.card = 2) (hwcard : w.card = 2)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero Item r cost
    prefixChores m2Chores u w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hcover
  · exact Disjoint.mono (fun item hitem => hu item hitem) (fun item hitem => hw item hitem)
      (m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide))
  · exact hucard
  · exact hwcard
  · exact hhead
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 0 (hu item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 1 (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 2 hcost (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 3 hcost (hu item hitem) (by simp)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using
      m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 0 hcost (hw item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 1 hcost (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 2 (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 3 (hw item hitem) (by simp)

/-- The double-disjoint B.2.2(b) schedule is label-invariant, including the
choice of the long agent and the two disjoint edge types. -/
theorem existsEfxOfB1LowMultiplicity_doubleDisjoint_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores u w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (hcover : m2Chores = u ∪ w) (hucard : u.card = 2) (hwcard : w.card = 2)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_doubleDisjoint_longZero_of_typePools Item r
    (relabelChoreCost labels cost) prefixChores m2Chores u w head a
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
  · exact hcover
  · exact hucard
  · exact hwcard
  · exact hhead
  · exact hu
  · exact hw

/-- Source Case B.2.1(a)'s exceptional direct schedule stated with the
library's M₂ edge fibres.  The three pools have source types `(0,1)`,
`(1,2)`, and `(2,3)` respectively; their fibre memberships derive the
explicit bi-valued table used by the direct allocation. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longZero_of_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hv : ∀ item ∈ v,
      item ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfB1IntersectingExceptionalDirect_longZero Item r cost
    prefixChores m2Chores u v w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hcover huv huw hvw hucard hvcard hwcard hhead
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 0 (hu item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 1 (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 2 hcost (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 3 hcost (hu item hitem) (by simp)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
          item 0 hcost (hv item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 1 (hv item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 2 (hv item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
          item 3 hcost (hv item hitem) (by simp)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 0 hcost (hw item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 1 hcost (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 2 (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
      m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 3 (hw item hitem) (by simp)

/-- The internal-long direct schedule stated with the library's M₂ edge
fibres.  It is the distinct source allocation used when the long agent is
the second endpoint of the first edge in the `(0,1),(1,2),(2,3)` chain. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longOne_of_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 1) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hv : ∀ item ∈ v,
      item ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply existsEfxOfB1IntersectingExceptionalDirect_longOne Item r cost
    prefixChores m2Chores u v w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hcover huv huw hvw hucard hvcard hwcard hhead
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 0 (hu item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          item 1 (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 2 hcost (hu item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          item 3 hcost (hu item hitem) (by simp)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
          item 0 hcost (hv item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 1 (hv item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
          item 2 (hv item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
          item 3 hcost (hv item hitem) (by simp)
  · intro item hitem
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 0 hcost (hw item hitem) (by simp)
    · simpa [IsLargeChore] using
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({2, 3} : Finset (Fin 4))
          item 1 hcost (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 2 (hw item hitem) (by simp)
    · simpa [IsSmallChore] using
        m2TypeChorePool_small_for_endpoint cost m2Chores ({2, 3} : Finset (Fin 4))
          item 3 (hw item hitem) (by simp)

/-- The source-to-model bridge for the special direct allocation in Case
B.2.1(a), with source agent `1` (Lean agent `0`) long.  The first residual
exceptional shape says precisely that, after deleting the displayed two
maximum-type chores and one intersecting chore, the residue is one surviving
maximum-type chore together with `4q+3` chores of the complementary type.
The preceding finite counting lemma turns those paper hypotheses into the
`3,1,3` type-pool inputs of the direct schedule. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longZero_of_exceptionalResidue
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (first second middle surviving : Item) (q : ℕ)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hsuper : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation 0) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hmiddle : middle ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hsurviving : surviving ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second, middle} = {surviving} ∪
      m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hresidueCard : (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card =
      4 * q + 3)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let u := m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  let v := m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))
  let w := m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))
  have huSub : u ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp
      (by simpa [u] using hitem) |>.1
  have hvSub : v ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) item).mp
      (by simpa [v] using hitem) |>.1
  have hwSub : w ⊆ m2Chores := by
    intro item hitem
    exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
      (by simpa [w] using hitem) |>.1
  have huv : Disjoint u v := by
    simpa [u, v] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) (by decide)
  have huw : Disjoint u w := by
    simpa [u, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  have hvw : Disjoint v w := by
    simpa [v, w] using m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({1, 2} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide)
  obtain ⟨hcover, hucard, hvcard, hwcard⟩ :=
    b1_intersecting_exceptional_forces_313 Item m2Chores u v w first second middle surviving q
      huSub hvSub hwSub huv huw hvw (by simpa [u] using hfirst) (by simpa [u] using hsecond)
      (by simpa [v] using hmiddle) (by simpa [u] using hsurviving) hfirstSecond
      (by simpa [u, w] using hresidue) (by simpa [w] using hresidueCard)
      (by simpa [u, w] using hmaximum ({2, 3} : Finset (Fin 4)))
  have hwNonempty : w.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨head, hhead⟩ := hwNonempty
  exact existsEfxOfB1IntersectingExceptionalDirect_longZero_of_typePools Item r cost
    prefixChores m2Chores u v w head a quota prefixAllocation hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hcover huv huw hvw hucard hvcard hwcard hhead
    (by intro item hitem; simpa [u] using hitem)
    (by intro item hitem; simpa [v] using hitem)
    (by intro item hitem; simpa [w] using hitem)

/-- The direct exceptional schedule is label-invariant.  Here `labels` maps
the displayed source labels `0,1,2,3` to the corresponding agents in the
original instance, so this theorem covers each possible long agent without
duplicating the source's symmetric schedules. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)))
    (hv : ∀ item ∈ v,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({1, 2} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1IntersectingExceptionalDirect_longZero_of_typePools Item r
    (relabelChoreCost labels cost) prefixChores m2Chores u v w head a
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
      intro heq
      apply hshort
      exact labels.injective heq
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) hshortOriginal
  · exact hcover
  · exact huv
  · exact huw
  · exact hvw
  · exact hucard
  · exact hvcard
  · exact hwcard
  · exact hhead
  · exact hu
  · exact hv
  · exact hw

/-- The internal-long exceptional schedule is invariant under a relabelling
of the displayed three-edge chain.  Together with the endpoint-long wrapper,
this covers all four possible long agents in the source's `3,1,3` case. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_longOne_of_relabelled_typePools
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores u v w : Finset Item) (head : Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a) (hquota1 : quota (labels 1) = a + 1)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 1)) - r)
    (hcover : m2Chores = u ∪ v ∪ w)
    (huv : Disjoint u v) (huw : Disjoint u w) (hvw : Disjoint v w)
    (hucard : u.card = 3) (hvcard : v.card = 1) (hwcard : w.card = 3)
    (hhead : head ∈ w)
    (hu : ∀ item ∈ u,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4)))
    (hv : ∀ item ∈ v,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({1, 2} : Finset (Fin 4)))
    (hw : ∀ item ∈ w,
      item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1IntersectingExceptionalDirect_longOne_of_typePools Item r
    (relabelChoreCost labels cost) prefixChores m2Chores u v w head a
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
    have hshortOriginal : labels short ≠ labels 1 := by
      intro heq
      apply hshort
      exact labels.injective heq
    simpa [relabelChoreCost, relabelAllocation, additiveChoreCost] using
      hsuper (labels short) hshortOriginal
  · exact hcover
  · exact huv
  · exact huw
  · exact hvw
  · exact hucard
  · exact hvcard
  · exact hwcard
  · exact hhead
  · exact hu
  · exact hv
  · exact hw

/-- The exceptional-residue direct branch of Case B.2.1(a) is invariant under
source-label relabelling.  This is the formal counterpart of the paper's
sentence that the cases with another long agent are symmetric. -/
theorem existsEfxOfB1IntersectingExceptionalDirect_of_relabelled_exceptionalResidue
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (first second middle surviving : Item) (q : ℕ)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hsuper : ∀ short : Fin 4, short ≠ labels 0 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation (labels 0)) - r)
    (hfirst : first ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hmiddle : middle ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({1, 2} : Finset (Fin 4)))
    (hsurviving : surviving ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hfirstSecond : first ≠ second)
    (hresidue : m2Chores \ {first, second, middle} = {surviving} ∪
      m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4)))
    (hresidueCard :
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({2, 3} : Finset (Fin 4))).card =
        4 * q + 3)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores edgeType).card ≤
        (m2TypeChorePool (relabelChoreCost labels cost) m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1IntersectingExceptionalDirect_longZero_of_exceptionalResidue Item r
    (relabelChoreCost labels cost) prefixChores m2Chores first second middle surviving q a
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
  · exact hfirst
  · exact hsecond
  · exact hmiddle
  · exact hsurviving
  · exact hfirstSecond
  · exact hresidue
  · exact hresidueCard
  · exact hmaximum

end HT26EFXChores
