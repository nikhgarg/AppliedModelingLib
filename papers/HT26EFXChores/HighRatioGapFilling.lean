import HT26EFXChores.NonexceptionalCombination
import HT26EFXChores.ExceptionalCombination
import HT26EFXChores.PoolPartition

/-!
# High-ratio gap filling

The `r > 2` portion of He--Tao's four-agent proof allocates a few M₂ edge
chores before using the residual M₂ theorem.  This module records the finite
edge-fibre facts shared by those source case analyses.

Source: `EFXadditivechores.tex`, lines 2224--3501.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- If no two-agent edge fibre has three chores, then the M₂ residue cannot
have either of the exceptional shapes from the source.  Both shapes contain a
dominant two-agent fibre of size `4q+3`, hence at least three chores. -/
theorem not_isM2Exceptional_of_m2TypeCard_le_two
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (hbound : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost chores smallAgents).card ≤ 2) :
    ¬ IsM2Exceptional cost chores := by
  intro hexceptional
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, _hauxiliary,
    _hdisjoint, hshape⟩
  have hdominantBound := hbound dominant hdominant
  rcases hshape with ⟨htype, hcard⟩ | ⟨exceptionalItem, _hitem, _hitemType,
      houtsideType, houtsideCard⟩
  · have htypeEq : m2TypeChorePool cost chores dominant = chores := by
      apply Finset.filter_eq_self.mpr
      intro item hitem
      simpa [m2TypeChorePool] using htype item hitem
    rw [htypeEq, hcard] at hdominantBound
    omega
  · have hsubset : chores.erase exceptionalItem ⊆
        m2TypeChorePool cost chores dominant := by
      intro item hitem
      exact (mem_m2TypeChorePool cost chores dominant item).mpr
        ⟨Finset.erase_subset exceptionalItem chores hitem, houtsideType item hitem⟩
    have hcardLower := Finset.card_le_card hsubset
    rw [houtsideCard] at hcardLower
    omega

/-- A bound on every edge fibre of the original M₂ pool also rules out an
exceptional shape after any gap-filling deletion. -/
theorem not_isM2Exceptional_of_m2TypeCard_le_two_of_subset
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores residue : Finset Item) (hsubset : residue ⊆ chores)
    (hbound : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost chores smallAgents).card ≤ 2) :
    ¬ IsM2Exceptional cost residue := by
  apply not_isM2Exceptional_of_m2TypeCard_le_two Item cost residue
  intro smallAgents hsmallAgents
  exact (Finset.card_le_card
    (m2TypeChorePool_mono cost smallAgents hsubset)).trans
      (hbound smallAgents hsmallAgents)

/-- The gap-filling construction in source Case B.4.1(a).  A
super-canonical prefix has agent `0` short.  Giving her one type-`(0,1)` and
one type-`(0,2)` chore makes the resulting prefix envy-free. -/
theorem existsGapFill_b3_intersecting
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap ({first, second} : Finset Item) ∧
        EnvyFreeForChores (additiveChoreCost cost)
          (fun agent => prefixAllocation agent ∪ gap agent) ∧
        gap 0 = ({first, second} : Finset Item) ∧
        (∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅) := by
  classical
  let gapChores : Finset Item := {first, second}
  let gap : Allocation (Fin 4) Item := fun agent =>
    if agent = 0 then gapChores else ∅
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.1
  have htypesNe : ({0, 1} : Finset (Fin 4)) ≠ {0, 2} := by
    intro heq
    have hone : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
    rw [heq] at hone
    norm_num at hone
    have honeNat : (1 : ℕ) = 2 := congrArg Fin.val hone
    omega
  have hfirstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact (Finset.disjoint_left.mp
      (m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) htypesNe) hfirst hsecond).elim
  have hgapAllocation : IsAllocationOf gap gapChores := by
    constructor
    · intro agent item hitem
      fin_cases agent
      · simpa [gap] using hitem
      · simp [gap] at hitem
      · simp [gap] at hitem
      · simp [gap] at hitem
    · intro item hitem
      refine ⟨0, ?_, ?_⟩
      · simpa [gap, gapChores] using hitem
      · intro agent howned
        fin_cases agent
        · rfl
        · simp [gap] at howned
        · simp [gap] at howned
        · simp [gap] at howned
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hprefix hgap
    have hprefixPool : item ∈ prefixChores := hcanonical.1.1 agent item hprefix
    fin_cases agent
    · have hgap' : item = first ∨ item = second := by
        simpa [gap, gapChores] using hgap
      rcases hgap' with hfirstItem | hsecondItem
      · subst item
        exact (Finset.disjoint_left.mp hprefixM2 hprefixPool hfirstM2).elim
      · subst item
        exact (Finset.disjoint_left.mp hprefixM2 hprefixPool hsecondM2).elim
    · simp [gap] at hgap
    · simp [gap] at hgap
    · simp [gap] at hgap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hgapZero : gap 0 = {first, second} := by simp [gap, gapChores]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅ := by
    intro agent hne
    simp [gap, hne]
  have hfirstSmallZero : cost 0 first = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      first 0 hfirst (by simp)
  have hsecondSmallZero : cost 0 second = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 2} : Finset (Fin 4))
      second 0 hsecond (by simp)
  have hgapZeroCost : additiveChoreCost cost 0 (gap 0) = 2 := by
    rw [hgapZero]
    unfold additiveChoreCost
    rw [Finset.sum_insert (by simp [hfirstNeSecond])]
    simp only [Finset.sum_singleton]
    norm_num [hfirstSmallZero, hsecondSmallZero]
  have hcostNonneg : ∀ agent item, 0 ≤ cost agent item :=
    IsOneOrRChoreCost.nonneg cost r hcost (by linarith)
  have hsecondLargeOne : cost 1 second = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 2} : Finset (Fin 4))
      second 1 hcost hsecond (by simp)
  have hfirstLargeTwo : cost 2 first = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      first 2 hcost hfirst (by simp)
  have hfirstLargeThree : cost 3 first = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      first 3 hcost hfirst (by simp)
  have hgapOneAtLeast : r ≤ additiveChoreCost cost 1 (gap 0) := by
    rw [hgapZero]
    unfold additiveChoreCost
    rw [Finset.sum_insert (by simp [hfirstNeSecond])]
    simp only [Finset.sum_singleton]
    rw [hsecondLargeOne]
    linarith [hcostNonneg 1 first]
  have hgapTwoAtLeast : r ≤ additiveChoreCost cost 2 (gap 0) := by
    rw [hgapZero]
    unfold additiveChoreCost
    rw [Finset.sum_insert (by simp [hfirstNeSecond])]
    simp only [Finset.sum_singleton]
    rw [hfirstLargeTwo]
    linarith [hcostNonneg 2 second]
  have hgapThreeAtLeast : r ≤ additiveChoreCost cost 3 (gap 0) := by
    rw [hgapZero]
    unfold additiveChoreCost
    rw [Finset.sum_insert (by simp [hfirstNeSecond])]
    simp only [Finset.sum_singleton]
    rw [hfirstLargeThree]
    linarith [hcostNonneg 3 second]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hgapLongAtLeast : ∀ agent : Fin 4, agent ≠ 0 →
      r ≤ additiveChoreCost cost agent (gap 0) := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hgapOneAtLeast
    · exact hgapTwoAtLeast
    · exact hgapThreeAtLeast
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    change ∀ own comparison,
      additiveChoreCost cost own (prefixAllocation own ∪ gap own) ≤
        additiveChoreCost cost own (prefixAllocation comparison ∪ gap comparison)
    intro own comparison
    by_cases hown : own = 0
    · subst own
      by_cases hcomparison : comparison = 0
      · subst comparison
        exact le_rfl
      · rw [hleftCost 0 0, hleftCost 0 comparison, hgapZeroCost,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 0 comparison hquota0 (hquotaLong comparison hcomparison)]
    · by_cases hcomparison : comparison = 0
      · subst comparison
        rw [hleftCost own own, hleftCost own 0, hgapOther own hown]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
          (by linarith) own 0, hgapLongAtLeast own hown]
      · rw [hleftCost own own, hleftCost own comparison, hgapOther own hown,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
          prefixAllocation hcost (by linarith) own comparison
          ((hquotaLong own hown).trans (hquotaLong comparison hcomparison).symm)
  refine ⟨gap, ?_, hleftEnvyFree, ?_, hgapOther⟩
  · simpa [gapChores] using hgapAllocation
  · simpa [gapChores] using hgapZero

/-- The one-item gap fill in source Case B.4.1(b).  The designated short
agent `1` receives a type-`(0,1)` chore.  The former short agent `0` is now
long and has an all-small canonical bundle, which is exactly the additional
invariant needed to make the gap-filled prefix envy-free. -/
theorem existsGapFill_b3_intersecting_nonsupercanonical
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap {item} ∧
      EnvyFreeForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ gap agent) ∧
      gap 1 = {item} ∧
      (∀ agent : Fin 4, agent ≠ 1 → gap agent = ∅) := by
  classical
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 {item}
  have hgapAllocation : IsAllocationOf gap {item} := isAllocationOf_allocateAllTo 1 {item}
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hprefixGap : Disjoint prefixChores {item} := by
    rw [Finset.disjoint_singleton_right]
    intro hitemPrefix
    exact (Finset.disjoint_left.mp hprefixM2 hitemPrefix hitemM2).elim
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hgapOne : gap 1 = {item} := by simp [gap, allocateAllTo]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 1 → gap agent = ∅ := by
    intro agent hne
    simp [gap, allocateAllTo, hne]
  have hitemSmallZero : cost 0 item = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      item 0 hitem (by simp)
  have hitemSmallOne : cost 1 item = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      item 1 hitem (by simp)
  have hitemLargeTwo : cost 2 item = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      item 2 hcost hitem (by simp)
  have hitemLargeThree : cost 3 item = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      item 3 hcost hitem (by simp)
  have hgapOneZero : additiveChoreCost cost 0 (gap 1) = 1 := by
    rw [hgapOne]
    simp [additiveChoreCost, hitemSmallZero]
  have hgapOneOne : additiveChoreCost cost 1 (gap 1) = 1 := by
    rw [hgapOne]
    simp [additiveChoreCost, hitemSmallOne]
  have hgapOneTwo : additiveChoreCost cost 2 (gap 1) = r := by
    rw [hgapOne]
    simp [additiveChoreCost, hitemLargeTwo]
  have hgapOneThree : additiveChoreCost cost 3 (gap 1) = r := by
    rw [hgapOne]
    simp [additiveChoreCost, hitemLargeThree]
  have hprefixZeroCard : (prefixAllocation 0).card = a + 1 := by
    rw [hcanonical.2 0 |>.1, hquota0]
  have hprefixOneCard : (prefixAllocation 1).card = a := by
    rw [hcanonical.2 1 |>.1, hquota1]
  have hprefixZeroCost : additiveChoreCost cost 0 (prefixAllocation 0) = (a : ℝ) + 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (prefixAllocation 0) 1
      (fun chore hchore => by simpa [IsSmallChore] using hprefixZeroSmall chore hchore),
      hprefixZeroCard]
    norm_num [nsmul_eq_mul]
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hprefixOneLowerZero : (a : ℝ) ≤ additiveChoreCost cost 0 (prefixAllocation 1) := by
    have hbound := card_nsmul_le_additiveChoreCost_of_le cost 0 (prefixAllocation 1) 1
      (fun chore hchore => hcostLower 0 chore)
    rw [hprefixOneCard] at hbound
    norm_num [nsmul_eq_mul] at hbound
    exact hbound
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 1 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact (hne rfl).elim
    · exact hquota2
    · exact hquota3
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith) (by
      intro own comparison
      fin_cases own <;> fin_cases comparison <;>
        simp [hquota0, hquota1, hquota2, hquota3] <;> omega)
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    intro own comparison
    by_cases hown : own = 1
    · subst own
      by_cases hcomparison : comparison = 1
      · subst comparison
        exact le_rfl
      · rw [hleftCost 1 1, hleftCost 1 comparison, hgapOneOne,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
          prefixAllocation hcost (by linarith) 1 comparison
          (by rw [hquotaLong comparison hcomparison, hquota1])
    · by_cases hcomparison : comparison = 1
      · subst comparison
        have hownCases : own = 0 ∨ own = 2 ∨ own = 3 := by
          fin_cases own
          · exact Or.inl rfl
          · exact (hown rfl).elim
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        rcases hownCases with rfl | rfl | rfl
        · rw [hleftCost 0 0, hleftCost 0 1, hgapOther 0 (by decide), hgapOneZero]
          simp only [additiveChoreCost_empty, add_zero]
          linarith
        · rw [hleftCost 2 2, hleftCost 2 1, hgapOther 2 (by decide), hgapOneTwo]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 2 1]
        · rw [hleftCost 3 3, hleftCost 3 1, hgapOther 3 (by decide), hgapOneThree]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 3 1]
      · rw [hleftCost own own, hleftCost own comparison, hgapOther own hown,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
          prefixAllocation hcost (by linarith) own comparison
          ((hquotaLong own hown).trans (hquotaLong comparison hcomparison).symm)
  exact ⟨gap, hgapAllocation, hleftEnvyFree, hgapOne, hgapOther⟩

/-- An exceptional M₂ shape together with an ordered pair of its auxiliary
endpoints.  The underlying exceptional predicate intentionally omits this
order; source gap-filling cases need it to identify the possible
large-removal agents. -/
def IsM2ExceptionalWithEndpoints {Item : Type} [DecidableEq Item]
    (cost : ChoreCost (Fin 4) Item) (chores : Finset Item)
    (first second : Fin 4) : Prop :=
  ∃ dominant auxiliary : Finset (Fin 4), ∃ q : ℕ,
    dominant.card = 2 ∧ auxiliary.card = 2 ∧ Disjoint dominant auxiliary ∧
      first ∈ auxiliary ∧ second ∈ auxiliary ∧
      (((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧
          chores.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ chores,
          smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ chores.erase exceptionalItem,
            smallAgentSet cost item = dominant) ∧
          (chores.erase exceptionalItem).card = 4 * q + 3))

/-- The nonexceptional residual outcome of source Case B.4.1(b). -/
theorem existsEfxOfM01M2_b3_intersecting_nonsupercanonical_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {item})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapOne, _hgapOther⟩ :=
    existsGapFill_b3_intersecting_nonsupercanonical Item r cost prefixChores m2Chores a quota
      prefixAllocation item hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hitem hprefixZeroSmall
  let gapChores : Finset Item := {item}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ chore ∈ residueChores, IsSmallForExactlyTwo cost chore := by
    intro chore hchore
    exact hm2Small chore (Finset.sdiff_subset hchore)
  have hnotExceptional' : ¬ IsM2Exceptional cost residueChores := by
    simpa [residueChores, gapChores] using hnotExceptional
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hcanonical.1 (by simpa [gapChores] using hgapAllocation)
    hleftEnvyFree hresidueSmall hnotExceptional'

/-- The identified exceptional outcome of source Case B.4.1(b).  Its only
possible exceptional pair is the two long agents `0` and `2`, so the standard
exceptional-residue concatenation applies to the same envy-free prefix. -/
theorem existsEfxOfM01M2_b3_intersecting_nonsupercanonical_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {item}) 0 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapOne, hgapOther⟩ :=
    existsGapFill_b3_intersecting_nonsupercanonical Item r cost prefixChores m2Chores a quota
      prefixAllocation item hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hitem hprefixZeroSmall
  let gapChores : Finset Item := {item}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hquotaCases : ∀ agent : Fin 4, quota agent = a ∨ quota agent = a + 1 := by
    intro agent
    fin_cases agent
    · exact Or.inr hquota0
    · exact Or.inl hquota1
    · exact Or.inr hquota2
    · exact Or.inr hquota3
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 1 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact (hne rfl).elim
    · exact hquota2
    · exact hquota3
  have hgapShort : ∀ agent : Fin 4, quota agent ≠ a → gap agent = ∅ := by
    intro agent hquotaNe
    by_cases hone : agent = 1
    · subst agent
      exact (hquotaNe hquota1).elim
    · exact hgapOther agent hone
  have hexceptional' : IsM2ExceptionalWithEndpoints cost residueChores 0 2 := by
    simpa [residueChores, gapChores] using hexceptional
  exact exceptional_residue_combination_proof Item r cost prefixChores m2Chores
    gapChores residueChores a quota prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hprefixSmall hcanonical hquotaCases
    (by simpa [gapChores] using hgapAllocation) hgapShort hleftEnvyFree
    0 2 (by simpa [IsM2ExceptionalWithEndpoints] using hexceptional') (by decide)
    (hquotaLong 0 (by decide)) (hquotaLong 2 (by decide))

/-- The nonexceptional-residue conclusion of source Case B.4.1(a), obtained
by composing its explicit intersecting-edge gap fill with the standard M₂
certificate. -/
theorem existsEfxOfM01M2_b3_intersecting_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOther⟩ :=
    existsGapFill_b3_intersecting Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hsuper hfirst hsecond
  let gapChores : Finset Item := {first, second}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro item hitem
    have hitem' : item = first ∨ item = second := by
      simpa [gapChores] using hitem
    rcases hitem' with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hgapResidue : Disjoint gapChores residueChores := by
    exact Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores := by
    exact Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ item ∈ residueChores, IsSmallForExactlyTwo cost item := by
    intro item hitem
    exact hm2Small item (Finset.sdiff_subset hitem)
  have hnotExceptional' : ¬ IsM2Exceptional cost residueChores := by
    simpa [residueChores, gapChores] using hnotExceptional
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hcanonical.1 (by simpa [gapChores] using hgapAllocation)
    hleftEnvyFree hresidueSmall hnotExceptional'

/-- The exceptional-residue branch of source Case B.4.1(a) when the
exceptional pair avoids the short agent.  The shared intersecting-edge gap
fill is envy-free, and both exceptional agents have the long M₀₁ quota, so the
controlled exceptional-residue composition applies. -/
theorem existsEfxOfM01M2_b3_intersecting_exceptional_away_short
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (exceptionalI exceptionalJ : Fin 4)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second})
      exceptionalI exceptionalJ)
    (hij : exceptionalI ≠ exceptionalJ)
    (hIneZero : exceptionalI ≠ 0) (hJneZero : exceptionalJ ≠ 0) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, hgapOther⟩ :=
    existsGapFill_b3_intersecting Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hsuper hfirst hsecond
  let gapChores : Finset Item := {first, second}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro item hitem
    have hitem' : item = first ∨ item = second := by
      simpa [gapChores] using hitem
    rcases hitem' with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hgapResidue : Disjoint gapChores residueChores := by
    exact Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores := by
    exact Finset.union_sdiff_of_subset hgapSubset
  have hquotaCases : ∀ agent : Fin 4, quota agent = a ∨ quota agent = a + 1 := by
    intro agent
    fin_cases agent
    · exact Or.inl hquota0
    · exact Or.inr hquota1
    · exact Or.inr hquota2
    · exact Or.inr hquota3
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hgapShort : ∀ agent : Fin 4, quota agent ≠ a → gap agent = ∅ := by
    intro agent hquotaNe
    by_cases hzero : agent = 0
    · subst agent
      exact (hquotaNe hquota0).elim
    · exact hgapOther agent hzero
  have hexceptional' : IsM2ExceptionalWithEndpoints cost residueChores
      exceptionalI exceptionalJ := by
    simpa [residueChores, gapChores] using hexceptional
  exact exceptional_residue_combination_proof Item r cost prefixChores m2Chores
    gapChores residueChores a quota prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hprefixSmall hcanonical hquotaCases
    (by simpa [gapChores] using hgapAllocation) hgapShort hleftEnvyFree
    exceptionalI exceptionalJ (by simpa [IsM2ExceptionalWithEndpoints] using hexceptional')
    hij (hquotaLong exceptionalI hIneZero) (hquotaLong exceptionalJ hJneZero)

/-- The remaining exceptional branch of source Case B.4.1(a), with the short
agent in the exceptional pair.  The other exceptional endpoint is selected as
the controlled all-large residual owner.  If its prefix has a small chore,
the two gap chores supply the needed `r - 1` cross-bundle advantage; otherwise
its whole left bundle is already large. -/
theorem existsEfxOfM01M2_b3_intersecting_exceptional_with_short
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (exceptionalI : Fin 4)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second})
      exceptionalI 0)
    (hIneZero : exceptionalI ≠ 0) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, hgapZero, hgapOther⟩ :=
    existsGapFill_b3_intersecting Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hsuper hfirst hsecond
  let gapChores : Finset Item := {first, second}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.1
  have htypesNe : ({0, 1} : Finset (Fin 4)) ≠ {0, 2} := by
    intro heq
    have hone : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
    rw [heq] at hone
    norm_num at hone
    have honeNat : (1 : ℕ) = 2 := congrArg Fin.val hone
    omega
  have hfirstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact (Finset.disjoint_left.mp
      (m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) htypesNe) hfirst hsecond).elim
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro item hitem
    have hitem' : item = first ∨ item = second := by
      simpa [gapChores] using hitem
    rcases hitem' with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent)
      (by simpa [gapChores] using hprefixGap)
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hcostNonneg : ∀ agent item, 0 ≤ cost agent item :=
    IsOneOrRChoreCost.nonneg cost r hcost (by linarith)
  have hgapLongAtLeast : ∀ agent : Fin 4, agent ≠ 0 →
      r ≤ additiveChoreCost cost agent (gap 0) := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · have hlarge : cost 1 second = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores
          ({0, 2} : Finset (Fin 4)) second 1 hcost hsecond (by simp)
      rw [hgapZero]
      unfold additiveChoreCost
      rw [Finset.sum_insert (by simp [hfirstNeSecond])]
      simp only [Finset.sum_singleton]
      change r ≤ cost 1 first + cost 1 second
      rw [hlarge]
      linarith [hcostNonneg 1 first]
    · have hlarge : cost 2 first = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores
          ({0, 1} : Finset (Fin 4)) first 2 hcost hfirst (by simp)
      rw [hgapZero]
      unfold additiveChoreCost
      rw [Finset.sum_insert (by simp [hfirstNeSecond])]
      simp only [Finset.sum_singleton]
      change r ≤ cost 2 first + cost 2 second
      rw [hlarge]
      linarith [hcostNonneg 2 second]
    · have hlarge : cost 3 first = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores
          ({0, 1} : Finset (Fin 4)) first 3 hcost hfirst (by simp)
      rw [hgapZero]
      unfold additiveChoreCost
      rw [Finset.sum_insert (by simp [hfirstNeSecond])]
      simp only [Finset.sum_singleton]
      change r ≤ cost 3 first + cost 3 second
      rw [hlarge]
      linarith [hcostNonneg 3 second]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary, htypesDisjoint,
    hmemI, hmemZero, hshape⟩
  obtain ⟨right, hrightAllocation, hunit, hrightLarge, hrightAway, hrightComparison⟩ :=
    existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q
      (by linarith) hcost hdominant hauxiliary htypesDisjoint hshape exceptionalI 0
      hmemI hmemZero hIneZero
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 (by simpa [gapChores] using hgapAllocation)
  have hgapResidue : Disjoint gapChores residueChores := by
    exact Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores := by
    exact Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right (Finset.sdiff_subset)
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro item hleftItem hresidueItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue hprefixItem hresidueItem).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgapItem hresidueItem).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftItem hrightItem
    have hrightPool : item ∈ residueChores := hrightAllocation.1 agent item hrightItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent item hprefixItem) hrightPool).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        ((by simpa [gapChores] using hgapAllocation.1 agent item hgapItem)) hrightPool).elim
  have hspecialLeft :
      (∀ item ∈ left exceptionalI, IsLargeChore cost r exceptionalI item) ∨
        additiveChoreCost cost exceptionalI (left exceptionalI) + (r - 1) ≤
          additiveChoreCost cost exceptionalI (left 0) := by
    by_cases hsmall : ∃ item ∈ prefixAllocation exceptionalI,
        IsSmallChore cost exceptionalI item
    · right
      obtain ⟨item, hitem, hitemSmall⟩ := hsmall
      have hprefixSlack := EFXForChores.additive_sub_one_le_of_small cost prefixAllocation
        hprefixEFX exceptionalI 0 item hitem hitemSmall
      change additiveChoreCost cost exceptionalI (prefixAllocation exceptionalI ∪ gap exceptionalI) +
          (r - 1) ≤ additiveChoreCost cost exceptionalI (prefixAllocation 0 ∪ gap 0)
      rw [hleftCost exceptionalI exceptionalI, hleftCost exceptionalI 0,
        hgapOther exceptionalI hIneZero]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hprefixSlack, hgapLongAtLeast exceptionalI hIneZero]
    · left
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation exceptionalI := by
        simpa [left, hgapOther exceptionalI hIneZero] using hitem
      rcases hcost exceptionalI item with hsmallItem | hlargeItem
      · exact (hsmall ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmallItem⟩).elim
      · simpa [IsLargeChore] using hlargeItem
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_controlled_exceptional Item r cost left right exceptionalI 0
    hbundlesDisjoint hcostLower (by simpa [left] using hleftEnvyFree) hunit hrightLarge
    hrightAway hrightComparison hspecialLeft

/-- The gap-filling calculation in source Case B.4.2(b).  The two M₂ types
are disjoint, agents `0` and `1` are the source's heavy endpoints, and agent
`3` is short in the super-canonical M₀₁ prefix.  Giving a type-`(0,1)` chore
to agent `3` makes the gap-filled prefix envy-free. -/
theorem existsGapFill_b3_disjoint_heavyEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap {item} ∧
      EnvyFreeForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ gap agent) ∧
      gap 3 = {item} ∧
      (∀ agent : Fin 4, agent ≠ 3 → gap agent = ∅) := by
  classical
  let gapChores : Finset Item := {item}
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapAllocation : IsAllocationOf gap gapChores := by
    exact isAllocationOf_allocateAllTo 3 gapChores
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hprefixGapPool : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGapPool
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hgapThree : gap 3 = gapChores := by simp [gap, allocateAllTo]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 3 → gap agent = ∅ := by
    intro agent hne
    simp [gap, allocateAllTo, hne]
  have hitemSmallZero : cost 0 item = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      item 0 hitem (by simp)
  have hitemSmallOne : cost 1 item = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      item 1 hitem (by simp)
  have hitemLargeTwo : cost 2 item = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      item 2 hcost hitem (by simp)
  have hitemLargeThree : cost 3 item = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      item 3 hcost hitem (by simp)
  have hgapThreeZero : additiveChoreCost cost 0 (gap 3) = 1 := by
    simp [hgapThree, gapChores, additiveChoreCost, hitemSmallZero]
  have hgapThreeOne : additiveChoreCost cost 1 (gap 3) = 1 := by
    simp [hgapThree, gapChores, additiveChoreCost, hitemSmallOne]
  have hgapThreeTwo : additiveChoreCost cost 2 (gap 3) = r := by
    simp [hgapThree, gapChores, additiveChoreCost, hitemLargeTwo]
  have hgapThreeThree : additiveChoreCost cost 3 (gap 3) = r := by
    simp [hgapThree, gapChores, additiveChoreCost, hitemLargeThree]
  have hprefixZeroCard : (prefixAllocation 0).card = a + 1 := by
    rw [hcanonical.2 0 |>.1, hquota0]
  have hprefixOneCard : (prefixAllocation 1).card = a + 1 := by
    rw [hcanonical.2 1 |>.1, hquota1]
  have hprefixThreeCard : (prefixAllocation 3).card = a := by
    rw [hcanonical.2 3 |>.1, hquota3]
  have hprefixZeroCost : additiveChoreCost cost 0 (prefixAllocation 0) = (a : ℝ) + 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (prefixAllocation 0) 1
      (fun chore hchore => by simpa [IsSmallChore] using hprefixZeroSmall chore hchore),
      hprefixZeroCard]
    norm_num [nsmul_eq_mul]
  have hprefixOneCost : additiveChoreCost cost 1 (prefixAllocation 1) = (a : ℝ) + 1 := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (prefixAllocation 1) 1
      (fun chore hchore => by simpa [IsSmallChore] using hprefixOneSmall chore hchore),
      hprefixOneCard]
    norm_num [nsmul_eq_mul]
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hprefixThreeLowerZero : (a : ℝ) ≤ additiveChoreCost cost 0 (prefixAllocation 3) := by
    have hbound := card_nsmul_le_additiveChoreCost_of_le cost 0 (prefixAllocation 3) 1
      (fun chore hchore => hcostLower 0 chore)
    rw [hprefixThreeCard] at hbound
    norm_num [nsmul_eq_mul] at hbound
    exact hbound
  have hprefixThreeLowerOne : (a : ℝ) ≤ additiveChoreCost cost 1 (prefixAllocation 3) := by
    have hbound := card_nsmul_le_additiveChoreCost_of_le cost 1 (prefixAllocation 3) 1
      (fun chore hchore => hcostLower 1 chore)
    rw [hprefixThreeCard] at hbound
    norm_num [nsmul_eq_mul] at hbound
    exact hbound
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 3 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact hquota1
    · exact hquota2
    · exact (hne rfl).elim
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    change ∀ own comparison,
      additiveChoreCost cost own (prefixAllocation own ∪ gap own) ≤
        additiveChoreCost cost own (prefixAllocation comparison ∪ gap comparison)
    intro own comparison
    by_cases hown : own = 3
    · subst own
      by_cases hcomparison : comparison = 3
      · subst comparison
        exact le_rfl
      · rw [hleftCost 3 3, hleftCost 3 comparison, hgapThreeThree,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        linarith [hsuper 3 comparison hquota3 (hquotaLong comparison hcomparison)]
    · by_cases hcomparison : comparison = 3
      · subst comparison
        have hownCases : own = 0 ∨ own = 1 ∨ own = 2 := by
          fin_cases own
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact (hown rfl).elim
        rcases hownCases with rfl | rfl | rfl
        · rw [hleftCost 0 0, hleftCost 0 3, hgapOther 0 (by decide), hgapThreeZero]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixZeroCost, hprefixThreeLowerZero]
        · rw [hleftCost 1 1, hleftCost 1 3, hgapOther 1 (by decide), hgapThreeOne]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixOneCost, hprefixThreeLowerOne]
        · rw [hleftCost 2 2, hleftCost 2 3, hgapOther 2 (by decide), hgapThreeTwo]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 2 3]
      · rw [hleftCost own own, hleftCost own comparison, hgapOther own hown,
          hgapOther comparison hcomparison]
        simp only [additiveChoreCost_empty, add_zero]
        exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
          prefixAllocation hcost (by linarith) own comparison
          ((hquotaLong own hown).trans (hquotaLong comparison hcomparison).symm)
  refine ⟨gap, ?_, hleftEnvyFree, ?_, hgapOther⟩
  · simpa [gapChores] using hgapAllocation
  · simpa [gapChores] using hgapThree

/-- The nonexceptional-residue subcase of source Case B.4.2(b).  Its shared
gap fill is envy-free, so the standard small-removal M₂ allocation composes
directly with the prefix. -/
theorem existsEfxOfM01M2_b3_disjoint_heavyEndpoints_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {item})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapThree, _hgapOther⟩ :=
    existsGapFill_b3_disjoint_heavyEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation item hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
      hquota3 hsuper hitem hprefixZeroSmall hprefixOneSmall
  let gapChores : Finset Item := {item}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ chore ∈ residueChores, IsSmallForExactlyTwo cost chore := by
    intro chore hchore
    exact hm2Small chore (Finset.sdiff_subset hchore)
  have hnotExceptional' : ¬ IsM2Exceptional cost residueChores := by
    simpa [residueChores, gapChores] using hnotExceptional
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hcanonical.1 (by simpa [gapChores] using hgapAllocation)
    hleftEnvyFree hresidueSmall hnotExceptional'

/-- The exceptional-residue subcase of source Case B.4.2(b).  Once the
source's multiplicity comparison identifies the residual exceptional endpoints
as the two heavy agents `0` and `1`, both carry the long M₀₁ quota; the
exceptional-residue concatenation lemma therefore applies to the shared
envy-free gap fill. -/
theorem existsEfxOfM01M2_b3_disjoint_heavyEndpoints_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {item}) 0 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapThree, hgapOther⟩ :=
    existsGapFill_b3_disjoint_heavyEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation item hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
      hquota3 hsuper hitem hprefixZeroSmall hprefixOneSmall
  let gapChores : Finset Item := {item}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hquotaCases : ∀ agent : Fin 4, quota agent = a ∨ quota agent = a + 1 := by
    intro agent
    fin_cases agent
    · exact Or.inr hquota0
    · exact Or.inr hquota1
    · exact Or.inr hquota2
    · exact Or.inl hquota3
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 3 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact hquota1
    · exact hquota2
    · exact (hne rfl).elim
  have hgapShort : ∀ agent : Fin 4, quota agent ≠ a → gap agent = ∅ := by
    intro agent hquotaNe
    by_cases hthree : agent = 3
    · subst agent
      exact (hquotaNe hquota3).elim
    · exact hgapOther agent hthree
  have hexceptional' : IsM2ExceptionalWithEndpoints cost residueChores 0 1 := by
    simpa [residueChores, gapChores] using hexceptional
  exact exceptional_residue_combination_proof Item r cost prefixChores m2Chores
    gapChores residueChores a quota prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hprefixSmall hcanonical hquotaCases
    (by simpa [gapChores] using hgapAllocation) hgapShort hleftEnvyFree
    0 1 (by simpa [IsM2ExceptionalWithEndpoints] using hexceptional') (by decide)
    hquota0 hquota1

/-- Source Case B.4.3(b), nonexceptional-residue branch.  For one fixed M₂
type, the source's residual congruence condition other than `3 mod 4` rules
out both exceptional shapes, so the common heavy-endpoint gap fill composes
with the standard M₂ certificate. -/
theorem existsEfxOfM01M2_b3_oneType_heavyEndpoints_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (residueQ residueRemainder : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hresidueCard : (m2Chores \ {item}).card = 4 * residueQ + residueRemainder)
    (hresidueRemainder : residueRemainder < 4)
    (hresidueNotThree : residueRemainder ≠ 3)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hresidueType : ∀ chore ∈ m2Chores \ {item},
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    exact hm2Type chore (Finset.sdiff_subset hchore)
  have hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {item}) :=
    not_isM2Exceptional_of_fixedSmallType_remainder_ne_three Item cost
      (m2Chores \ {item}) ({0, 1} : Finset (Fin 4)) residueQ residueRemainder
      hresidueType hresidueCard hresidueRemainder hresidueNotThree
  exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints_nonexceptional Item r cost
    prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hitem hm2Small hprefixZeroSmall
    hprefixOneSmall hnotExceptional

/-- The floor-sized gap-fill invariant in source Case B.4.3(a).  Agent `0` is
short and every supplied gap chore has type `(0,1)`.  Giving a pool of at most
`r` such chores to agent `0` is EFX with the canonical prefix: super-canonicity
handles agent `0`, and the prefix EFX inequalities handle every long agent. -/
theorem existsGapFill_b3_oneType_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hcard : (m2Chores.card : ℝ) ≤ r) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap m2Chores ∧
      EFXForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ gap agent) ∧
      gap 0 = m2Chores ∧
      (∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅) := by
  classical
  let suffix : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 m2Chores
  have hsuffixAllocation : IsAllocationOf suffix m2Chores :=
    isAllocationOf_allocateAllTo 0 m2Chores
  have hsuffixZero : suffix 0 = m2Chores := by simp [suffix, allocateAllTo]
  have hsuffixOther : ∀ agent : Fin 4, agent ≠ 0 → suffix agent = ∅ := by
    intro agent hne
    simp [suffix, allocateAllTo, hne]
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (suffix agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hsuffixAllocation.1 agent) hprefixM2
  have hcostNonneg : ∀ agent chore, 0 ≤ cost agent chore :=
    IsOneOrRChoreCost.nonneg cost r hcost (by linarith)
  have hsmallZero : ∀ chore ∈ m2Chores, IsSmallChore cost 0 chore := by
    intro chore hchore
    have hmem : (0 : Fin 4) ∈ smallAgentSet cost chore := by
      rw [hm2Type chore hchore]
      simp
    simpa [smallAgentSet] using hmem
  have hsuffixZeroCost : additiveChoreCost cost 0 (suffix 0) = (m2Chores.card : ℝ) := by
    rw [hsuffixZero,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 m2Chores 1
        (fun chore hchore => by simpa [IsSmallChore] using hsmallZero chore hchore)]
    norm_num [nsmul_eq_mul]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hfinalEFX : EFXForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ suffix agent) := by
    apply efxForChores_union_of_cost_gap cost prefixAllocation suffix hbundlesDisjoint
    intro own comparison hnonempty
    have hminimumNonneg : 0 ≤
        ((prefixAllocation own ∪ suffix own).image (cost own)).min'
          (Finset.image_nonempty.mpr hnonempty) := by
      apply Finset.le_min'
      intro value hvalue
      obtain ⟨chore, _hchore, hvalueEq⟩ := Finset.mem_image.mp hvalue
      rw [← hvalueEq]
      exact hcostNonneg own chore
    by_cases hown : own = 0
    · subst own
      by_cases hcomparison : comparison = 0
      · subst comparison
        linarith
      · rw [hsuffixOther comparison hcomparison, additiveChoreCost_empty,
          hsuffixZeroCost]
        linarith [hsuper 0 comparison hquota0 (hquotaLong comparison hcomparison)]
    · have hsuffixOwn : suffix own = ∅ := hsuffixOther own hown
      obtain ⟨chore, hchore, hminimumEq⟩ := Finset.mem_image.mp
        (Finset.min'_mem ((prefixAllocation own ∪ suffix own).image (cost own))
          (Finset.image_nonempty.mpr hnonempty))
      have hprefixChore : chore ∈ prefixAllocation own := by
        simpa [hsuffixOwn] using hchore
      have hprefixComparison : additiveChoreCost cost own
          (prefixAllocation own \ {chore}) ≤
          additiveChoreCost cost own (prefixAllocation comparison) := by
        exact (hprefixEFX own comparison).resolve_left (by
          intro hempty
          simpa [hsuffixOwn, hempty] using hchore) chore hprefixChore
      rw [additiveChoreCost_erase cost own (prefixAllocation own) chore hprefixChore] at hprefixComparison
      have hsuffixOwnCost : additiveChoreCost cost own (suffix own) = 0 := by
        rw [hsuffixOwn]
        exact additiveChoreCost_empty cost own
      linarith [additiveChoreCost_nonneg cost hcostNonneg own (suffix comparison),
        hminimumEq]
  exact ⟨suffix, hsuffixAllocation, hfinalEFX, hsuffixZero, hsuffixOther⟩

/-- If a finite pool has more than `r` chores, it contains a subpool of exactly
`⌊r⌋₊` chores.  This is the source's explicit gap-pool choice in the large-pool
branch of Case B.4.3(a). -/
theorem exists_floorCard_subset_of_card_gt
    (Item : Type) [DecidableEq Item] (chores : Finset Item) (r : ℝ)
    (hr : 0 ≤ r) (hcard : r < (chores.card : ℝ)) :
    ∃ gapChores ⊆ chores, gapChores.card = ⌊r⌋₊ := by
  have hfloorLe : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr
  have hfloorLt : (⌊r⌋₊ : ℝ) < chores.card := hfloorLe.trans_lt hcard
  have hfloorCard : ⌊r⌋₊ ≤ chores.card := by
    exact_mod_cast (le_of_lt hfloorLt)
  exact Finset.exists_subset_card_eq hfloorCard

/-- In the one-short-agent canonical prefix, assigning any disjoint gap pool
to the short agent gives every long agent at most `r - |gap|` extra cost over
that short bundle.  This is the numerical invariant used after choosing the
`⌊r⌋₊` gap pool in source Case B.4.3(a). -/
theorem canonical_gap_long_cost_le_short_add_r_sub_card
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores gapChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixGap : Disjoint prefixChores gapChores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1) :
    ∀ agent : Fin 4, agent ≠ 0 →
      additiveChoreCost cost agent (prefixAllocation agent ∪
        (allocateAllTo (Fin 4) Item 0 gapChores) agent) ≤
      additiveChoreCost cost agent (prefixAllocation 0 ∪
        (allocateAllTo (Fin 4) Item 0 gapChores) 0) +
        (r - (gapChores.card : ℝ)) := by
  classical
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 gapChores
  have hgapAllocation : IsAllocationOf gap gapChores := isAllocationOf_allocateAllTo 0 gapChores
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hbundlesDisjoint owner)
  have hgapOther : ∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅ := by
    intro agent hne
    simp [gap, allocateAllTo, hne]
  have hgapZero : gap 0 = gapChores := by simp [gap, allocateAllTo]
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hgapLower : ∀ agent : Fin 4,
      (gapChores.card : ℝ) ≤ additiveChoreCost cost agent (gap 0) := by
    intro agent
    rw [hgapZero]
    have hbound := card_nsmul_le_additiveChoreCost_of_le cost agent gapChores 1
      (fun chore hchore => hcostLower agent chore)
    norm_num [nsmul_eq_mul] at hbound
    exact hbound
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  intro agent hne
  change additiveChoreCost cost agent (prefixAllocation agent ∪ gap agent) ≤
    additiveChoreCost cost agent (prefixAllocation 0 ∪ gap 0) +
      (r - (gapChores.card : ℝ))
  rw [hleftCost agent agent, hleftCost agent 0, hgapOther agent hne]
  simp only [additiveChoreCost_empty, add_zero]
  linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
    (by linarith) agent 0, hgapLower agent]

/-- The small-pool subcase of source Case B.4.3(a), obtained by taking the
entire one-type M₂ pool as the gap fill. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_smallPool
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hcard : (m2Chores.card : ℝ) ≤ r) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hgapEFX, _hgapZero, _hgapOther⟩ :=
    existsGapFill_b3_oneType_shortEndpoint Item r cost prefixChores m2Chores a quota
      prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hsuper hm2Type hcard
  refine ⟨fun agent => prefixAllocation agent ∪ gap agent, ?_, hgapEFX⟩
  exact isAllocationOf_union prefixAllocation gap prefixChores m2Chores hprefixM2
    hcanonical.1 hgapAllocation

/-- The large-pool, nonexceptional residual branch of source Case B.4.3(a).
The gap has exactly `⌊r⌋₊` type-`(0,1)` chores and is given to the short
endpoint `0`.  When the remaining pool has residue `0`, `1`, or `2` modulo
four, the source order `0,1,2,3` gives every extra residual quota to a small
agent, so its unit-slack allocation composes with the canonical gap prefix. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores gapChores : Finset Item) (a residueQ residueRemainder : ℕ)
    (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hgapSubset : gapChores ⊆ m2Chores) (hgapCard : gapChores.card = ⌊r⌋₊)
    (hresidueCard : (m2Chores \ gapChores).card = 4 * residueQ + residueRemainder)
    (hresidueRemainder : residueRemainder < 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 gapChores
  let residueChores : Finset Item := m2Chores \ gapChores
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  let longAgents : Finset (Fin 4) := m2EarlyRoundLongAgents residueRemainder
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hgapAllocation : IsAllocationOf gap gapChores := isAllocationOf_allocateAllTo 0 gapChores
  have hgapZero : gap 0 = gapChores := by simp [gap, allocateAllTo]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅ := by
    intro agent hne
    simp [gap, allocateAllTo, hne]
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (left owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) := by
    exact additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hgapSmallZero : ∀ chore ∈ gapChores, cost 0 chore = 1 := by
    intro chore hchore
    have hmem : (0 : Fin 4) ∈ smallAgentSet cost chore := by
      rw [hm2Type chore (hgapSubset hchore)]
      simp
    simpa [smallAgentSet] using hmem
  have hgapZeroCost : additiveChoreCost cost 0 (gap 0) = (gapChores.card : ℝ) := by
    rw [hgapZero,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 gapChores 1 hgapSmallZero]
    norm_num [nsmul_eq_mul]
  have hgapLe : (gapChores.card : ℝ) ≤ r := by
    rw [hgapCard]
    exact Nat.floor_le (by linarith)
  have hleftShort : ∀ other,
      additiveChoreCost cost 0 (left 0) ≤ additiveChoreCost cost 0 (left other) := by
    intro other
    by_cases hother : other = 0
    · subst other
      exact le_rfl
    · rw [hleftCost 0 0, hleftCost 0 other, hgapZeroCost, hgapOther other hother]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 other hquota0 (hquotaLong other hother)]
  have hleftOther : ∀ agent, agent ≠ 0 → ∀ other, other ≠ 0 →
      additiveChoreCost cost agent (left agent) ≤ additiveChoreCost cost agent (left other) := by
    intro agent hagent other hother
    rw [hleftCost agent agent, hleftCost agent other, hgapOther agent hagent,
      hgapOther other hother]
    simp only [additiveChoreCost_empty, add_zero]
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) agent other
      ((hquotaLong agent hagent).trans (hquotaLong other hother).symm)
  have hgapCardReal : (gapChores.card : ℝ) = (⌊r⌋₊ : ℝ) := by
    exact_mod_cast hgapCard
  have hfloorLt : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
  have hleftToShort : ∀ agent, agent ≠ 0 →
      additiveChoreCost cost agent (left agent) ≤ additiveChoreCost cost agent (left 0) + 1 := by
    intro agent hagent
    have hslack := canonical_gap_long_cost_le_short_add_r_sub_card Item r cost
      prefixChores gapChores a quota prefixAllocation hr hcost hprefixGap hcanonical
      hquota0 hquota1 hquota2 hquota3 agent hagent
    have hslack' : additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left 0) + (r - (gapChores.card : ℝ)) := by
      simpa [left, gap] using hslack
    rw [hgapCardReal] at hslack'
    linarith
  have hresidueType : ∀ chore ∈ residueChores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    exact hm2Type chore (Finset.sdiff_subset hchore)
  have hlongCard : longAgents.card = residueRemainder := by
    exact m2EarlyRoundLongAgents_card residueRemainder hresidueRemainder
  have hresidueDecompose : residueChores.card = 4 * residueQ + longAgents.card := by
    rw [show residueChores = m2Chores \ gapChores by rfl, hresidueCard, hlongCard]
  have hlongSubset : longAgents ⊆ ({0, 1} : Finset (Fin 4)) := by
    exact m2EarlyRoundLongAgents_subset_smallType residueRemainder
  obtain ⟨right, hrightAllocation, hrightQuota, hrightUnit, _hrightEFX⟩ :=
    existsM2SingleSmallType_quotaAllocation_unitSlack Item r cost residueChores residueQ
      ({0, 1} : Finset (Fin 4)) longAgents hr hcost hresidueType hresidueDecompose hlongSubset
  have hrightSmallOne : ∀ owner item, item ∈ right owner → cost 1 item = 1 := by
    intro owner item hitem
    have hmem : (1 : Fin 4) ∈ smallAgentSet cost item := by
      rw [hresidueType item (hrightAllocation.1 owner item hitem)]
      simp
    simpa [smallAgentSet] using hmem
  have hrightLarge (agent : Fin 4) (hagent : agent ∉ ({0, 1} : Finset (Fin 4))) :
      ∀ owner item, item ∈ right owner → cost agent item = r := by
    intro owner item hitem
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [hresidueType item (hrightAllocation.1 owner item hitem)] using hmem
    · exact hlarge
  have hrightQuotaLeZero : ∀ agent : Fin 4, agent ≠ 0 →
      (right agent).card ≤ (right 0).card := by
    intro agent hagent
    have hquotaLe := m2EarlyRoundLongAgents_quota_le_zero residueQ residueRemainder
      hresidueRemainder agent hagent
    simpa [hrightQuota] using hquotaLe
  have hrightShortDominates : ∀ agent : Fin 4, agent ≠ 0 →
      additiveChoreCost cost agent (right agent) ≤ additiveChoreCost cost agent (right 0) := by
    intro agent hagent
    fin_cases agent
    · exact (hagent rfl).elim
    · change additiveChoreCost cost 1 (right 1) ≤ additiveChoreCost cost 1 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (right 1) 1
          (fun item hitem => hrightSmallOne 1 item hitem),
          additiveChoreCost_eq_card_nsmul_of_constant cost 1 (right 0) 1
            (fun item hitem => hrightSmallOne 0 item hitem)]
      norm_num [nsmul_eq_mul]
      exact_mod_cast hrightQuotaLeZero 1 (by decide)
    · change additiveChoreCost cost 2 (right 2) ≤ additiveChoreCost cost 2 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 2 (right 2) r
          (hrightLarge 2 (by decide) 2),
          additiveChoreCost_eq_card_nsmul_of_constant cost 2 (right 0) r
            (hrightLarge 2 (by decide) 0)]
      simp only [nsmul_eq_mul]
      have hcard := hrightQuotaLeZero 2 (by decide)
      have hrnonneg : 0 ≤ r := by linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hrnonneg
    · change additiveChoreCost cost 3 (right 3) ≤ additiveChoreCost cost 3 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 3 (right 3) r
          (hrightLarge 3 (by decide) 3),
          additiveChoreCost_eq_card_nsmul_of_constant cost 3 (right 0) r
            (hrightLarge 3 (by decide) 0)]
      simp only [nsmul_eq_mul]
      have hcard := hrightQuotaLeZero 3 (by decide)
      have hrnonneg : 0 ≤ r := by linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hrnonneg
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 hgapAllocation
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro chore hleft hresidue
    rcases Finset.mem_union.mp hleft with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue hprefix hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgap hresidue).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro chore hleft hright
    have hresidue : chore ∈ residueChores := hrightAllocation.1 agent chore hright
    rcases Finset.mem_union.mp hleft with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent chore hprefix) hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        (hgapAllocation.1 agent chore hgap) hresidue).elim
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efxForChores_union_of_short_unit_slack_and_right_dominance cost left right 0
    hbundlesDisjoint hcostLower hleftShort hleftOther hleftToShort hrightUnit
    hrightShortDominates

/-- Source Case B.4.3(a) with a large fixed-type M₂ pool and a nonexceptional
residual.  The `⌊r⌋₊` gap subset is selected from the pool, and the displayed
remainder condition is exactly the source branch in which the remaining
round-robin allocation has no large-removal exception. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_nonexceptional_of_card_gt
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hlargePool : r < (m2Chores.card : ℝ))
    (hresidueRemainder : (m2Chores.card - ⌊r⌋₊) % 4 < 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gapChores, hgapSubset, hgapCard⟩ :=
    exists_floorCard_subset_of_card_gt Item m2Chores r (by linarith) hlargePool
  let residueChores : Finset Item := m2Chores \ gapChores
  let residueQ : ℕ := residueChores.card / 4
  let residueRemainder : ℕ := residueChores.card % 4
  have hresidueCardNat : residueChores.card = m2Chores.card - gapChores.card := by
    exact Finset.card_sdiff_of_subset hgapSubset
  have hresidueRemainder' : residueRemainder < 3 := by
    dsimp [residueRemainder]
    rw [hresidueCardNat, hgapCard]
    exact hresidueRemainder
  have hresidueCard : residueChores.card = 4 * residueQ + residueRemainder := by
    dsimp [residueQ, residueRemainder]
    have hmod := Nat.mod_add_div residueChores.card 4
    omega
  exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_nonexceptional
    Item r cost prefixChores m2Chores gapChores a residueQ residueRemainder quota
    prefixAllocation hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
    hsuper hm2Type hgapSubset hgapCard (by simpa [residueChores] using hresidueCard)
    hresidueRemainder'

/-- The controlled remainder-three composition in source Case B.4.3(a).
The residual fixed-type schedule gives the chosen auxiliary endpoint its extra
large chore.  The final prefix premise is discharged by the source's choice
between the two round-robin orders in
`existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_of_card_gt`.
-/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_controlled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores gapChores : Finset Item) (a residueQ : ℕ)
    (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (special companion : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hgapSubset : gapChores ⊆ m2Chores) (hgapCard : gapChores.card = ⌊r⌋₊)
    (hresidueCard : (m2Chores \ gapChores).card = 4 * residueQ + 3)
    (hspecial : special ∈ ({2, 3} : Finset (Fin 4)))
    (hcompanion : companion ∈ ({2, 3} : Finset (Fin 4)))
    (hne : special ≠ companion)
    (hspecialPrefix :
      (∀ item ∈ prefixAllocation special, IsLargeChore cost r special item) ∨
      additiveChoreCost cost special (prefixAllocation special) + (r - 1) ≤
        additiveChoreCost cost special (prefixAllocation companion)) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 gapChores
  let residueChores : Finset Item := m2Chores \ gapChores
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hgapAllocation : IsAllocationOf gap gapChores := isAllocationOf_allocateAllTo 0 gapChores
  have hgapZero : gap 0 = gapChores := by simp [gap, allocateAllTo]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅ := by
    intro agent hne
    simp [gap, allocateAllTo, hne]
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (left owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) := by
    exact additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hne
    fin_cases agent
    · exact (hne rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hgapSmallZero : ∀ chore ∈ gapChores, cost 0 chore = 1 := by
    intro chore hchore
    have hmem : (0 : Fin 4) ∈ smallAgentSet cost chore := by
      rw [hm2Type chore (hgapSubset hchore)]
      simp
    simpa [smallAgentSet] using hmem
  have hgapZeroCost : additiveChoreCost cost 0 (gap 0) = (gapChores.card : ℝ) := by
    rw [hgapZero,
      additiveChoreCost_eq_card_nsmul_of_constant cost 0 gapChores 1 hgapSmallZero]
    norm_num [nsmul_eq_mul]
  have hgapLe : (gapChores.card : ℝ) ≤ r := by
    rw [hgapCard]
    exact Nat.floor_le (by linarith)
  have hleftShort : ∀ other,
      additiveChoreCost cost 0 (left 0) ≤ additiveChoreCost cost 0 (left other) := by
    intro other
    by_cases hother : other = 0
    · subst other
      exact le_rfl
    · rw [hleftCost 0 0, hleftCost 0 other, hgapZeroCost, hgapOther other hother]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 other hquota0 (hquotaLong other hother)]
  have hleftOther : ∀ agent, agent ≠ 0 → ∀ other, other ≠ 0 →
      additiveChoreCost cost agent (left agent) ≤ additiveChoreCost cost agent (left other) := by
    intro agent hagent other hother
    rw [hleftCost agent agent, hleftCost agent other, hgapOther agent hagent,
      hgapOther other hother]
    simp only [additiveChoreCost_empty, add_zero]
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) agent other
      ((hquotaLong agent hagent).trans (hquotaLong other hother).symm)
  have hgapCardReal : (gapChores.card : ℝ) = (⌊r⌋₊ : ℝ) := by
    exact_mod_cast hgapCard
  have hfloorLt : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
  have hleftToShort : ∀ agent, agent ≠ 0 →
      additiveChoreCost cost agent (left agent) ≤ additiveChoreCost cost agent (left 0) + 1 := by
    intro agent hagent
    have hslack := canonical_gap_long_cost_le_short_add_r_sub_card Item r cost
      prefixChores gapChores a quota prefixAllocation hr hcost hprefixGap hcanonical
      hquota0 hquota1 hquota2 hquota3 agent hagent
    have hslack' : additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left 0) + (r - (gapChores.card : ℝ)) := by
      simpa [left, gap] using hslack
    rw [hgapCardReal] at hslack'
    linarith
  have hresidueType : ∀ chore ∈ residueChores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    exact hm2Type chore (Finset.sdiff_subset hchore)
  obtain ⟨right, hrightAllocation, hrightQuota, hrightUnit, hrightLarge,
    hrightAway, hrightCompanion⟩ :=
    existsM2Type01_remainderThree_controlled Item r cost residueChores residueQ special companion
      hr hcost hresidueType (by simpa [residueChores] using hresidueCard)
      hspecial hcompanion hne
  have hspecialNonzero : special ≠ 0 := by
    fin_cases special <;> simp_all
  have hcompanionNonzero : companion ≠ 0 := by
    fin_cases companion <;> simp_all
  have hrightSmallOne : ∀ owner item, item ∈ right owner → cost 1 item = 1 := by
    intro owner item hitem
    have hmem : (1 : Fin 4) ∈ smallAgentSet cost item := by
      rw [hresidueType item (hrightAllocation.1 owner item hitem)]
      simp
    simpa [smallAgentSet] using hmem
  have hrightLargeFor (agent : Fin 4)
      (hagent : agent ∉ ({0, 1} : Finset (Fin 4))) :
      ∀ owner item, item ∈ right owner → cost agent item = r := by
    intro owner item hitem
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [hresidueType item (hrightAllocation.1 owner item hitem)] using hmem
    · exact hlarge
  have hrightQuotaLeZero : ∀ agent : Fin 4,
      (right agent).card ≤ (right 0).card := by
    intro agent
    rw [hrightQuota agent, hrightQuota 0]
    change residueQ + (if agent ∈ (Finset.univ.erase companion) then 1 else 0) ≤
      residueQ + (if (0 : Fin 4) ∈ (Finset.univ.erase companion) then 1 else 0)
    rw [if_pos (Finset.mem_erase.mpr ⟨Ne.symm hcompanionNonzero, Finset.mem_univ 0⟩)]
    split <;> omega
  have hrightShortDominates : ∀ agent : Fin 4, agent ≠ 0 →
      additiveChoreCost cost agent (right agent) ≤ additiveChoreCost cost agent (right 0) := by
    intro agent hagent
    fin_cases agent
    · exact (hagent rfl).elim
    · change additiveChoreCost cost 1 (right 1) ≤ additiveChoreCost cost 1 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 1 (right 1) 1
          (fun item hitem => hrightSmallOne 1 item hitem),
          additiveChoreCost_eq_card_nsmul_of_constant cost 1 (right 0) 1
            (fun item hitem => hrightSmallOne 0 item hitem)]
      norm_num [nsmul_eq_mul]
      exact_mod_cast hrightQuotaLeZero 1
    · change additiveChoreCost cost 2 (right 2) ≤ additiveChoreCost cost 2 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 2 (right 2) r
          (hrightLargeFor 2 (by decide) 2),
          additiveChoreCost_eq_card_nsmul_of_constant cost 2 (right 0) r
            (hrightLargeFor 2 (by decide) 0)]
      simp only [nsmul_eq_mul]
      have hcard := hrightQuotaLeZero 2
      have hrnonneg : 0 ≤ r := by linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hrnonneg
    · change additiveChoreCost cost 3 (right 3) ≤ additiveChoreCost cost 3 (right 0)
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 3 (right 3) r
          (hrightLargeFor 3 (by decide) 3),
          additiveChoreCost_eq_card_nsmul_of_constant cost 3 (right 0) r
            (hrightLargeFor 3 (by decide) 0)]
      simp only [nsmul_eq_mul]
      have hcard := hrightQuotaLeZero 3
      have hrnonneg : 0 ≤ r := by linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hrnonneg
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 hgapAllocation
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro chore hleft hresidue
    rcases Finset.mem_union.mp hleft with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue hprefix hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgap hresidue).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro chore hleft hright
    have hresidue : chore ∈ residueChores := hrightAllocation.1 agent chore hright
    rcases Finset.mem_union.mp hleft with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent chore hprefix) hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        (hgapAllocation.1 agent chore hgap) hresidue).elim
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  have hspecialLeft :
      (∀ item ∈ left special, IsLargeChore cost r special item) ∨
      additiveChoreCost cost special (left special) + (r - 1) ≤
        additiveChoreCost cost special (left companion) := by
    rcases hspecialPrefix with hlarge | hadvantage
    · left
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation special := by
        simpa [left, hgapOther special hspecialNonzero] using hitem
      exact hlarge item hprefixItem
    · right
      simpa [left, hgapOther special hspecialNonzero,
        hgapOther companion hcompanionNonzero] using hadvantage
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_short_unit_slack_and_controlled_exceptional Item r cost left right
    0 special companion (by simpa using hspecialNonzero.symm)
    (by simpa using hcompanionNonzero.symm) hbundlesDisjoint hcostLower hleftShort
    hleftOther hleftToShort hrightShortDominates hrightUnit hrightLarge hrightAway
    hrightCompanion hspecialLeft

/-- Source Case B.4.3(a) with a large fixed-type M₂ pool whose residual has
remainder three.  The two source round-robin orders are selected by whether
the first auxiliary prefix bundle contains an own-small chore.  If both
auxiliary prefix bundles do, the canonical M₀₁ cross-cost lemma supplies the
exact `r - 1` compensation for the selected all-large residual comparison. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_of_card_gt
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hlargePool : r < (m2Chores.card : ℝ))
    (hresidueRemainder : (m2Chores.card - ⌊r⌋₊) % 4 = 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gapChores, hgapSubset, hgapCard⟩ :=
    exists_floorCard_subset_of_card_gt Item m2Chores r (by linarith) hlargePool
  let residueChores : Finset Item := m2Chores \ gapChores
  let residueQ : ℕ := residueChores.card / 4
  have hresidueCardNat : residueChores.card = m2Chores.card - gapChores.card := by
    exact Finset.card_sdiff_of_subset hgapSubset
  have hresidueRemainder' : residueChores.card % 4 = 3 := by
    rw [hresidueCardNat, hgapCard]
    exact hresidueRemainder
  have hresidueCard : residueChores.card = 4 * residueQ + 3 := by
    dsimp [residueQ]
    have hmod := Nat.mod_add_div residueChores.card 4
    omega
  by_cases htwoSmall : ∃ item ∈ prefixAllocation 2, IsSmallChore cost 2 item
  · by_cases hthreeSmall : ∃ item ∈ prefixAllocation 3, IsSmallChore cost 3 item
    · have hadvantage : additiveChoreCost cost 3 (prefixAllocation 3) + (r - 1) ≤
        additiveChoreCost cost 3 (prefixAllocation 2) := by
        exact hcanonical.cross_cost_advantage_of_ownSmall cost r prefixChores quota
          prefixAllocation hcost (by linarith) hprefixSmall 3 2 (by decide)
          (hquota3.trans hquota2.symm) hthreeSmall htwoSmall
      exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_controlled
        Item r cost prefixChores m2Chores gapChores a residueQ quota prefixAllocation 3 2
        hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2Type
        hgapSubset hgapCard (by simpa [residueChores] using hresidueCard) (by decide)
        (by decide) (by decide) (Or.inr hadvantage)
    · have hthreeLarge : ∀ item ∈ prefixAllocation 3,
        IsLargeChore cost r 3 item := by
        intro item hitem
        rcases hcost 3 item with hsmall | hlarge
        · exact (hthreeSmall ⟨item, hitem, by simpa [IsSmallChore] using hsmall⟩).elim
        · exact hlarge
      exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_controlled
        Item r cost prefixChores m2Chores gapChores a residueQ quota prefixAllocation 3 2
        hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2Type
        hgapSubset hgapCard (by simpa [residueChores] using hresidueCard) (by decide)
        (by decide) (by decide) (Or.inl hthreeLarge)
  · have htwoLarge : ∀ item ∈ prefixAllocation 2,
      IsLargeChore cost r 2 item := by
      intro item hitem
      rcases hcost 2 item with hsmall | hlarge
      · exact (htwoSmall ⟨item, hitem, by simpa [IsSmallChore] using hsmall⟩).elim
      · exact hlarge
    exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_controlled
      Item r cost prefixChores m2Chores gapChores a residueQ quota prefixAllocation 2 3
      hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2Type
      hgapSubset hgapCard (by simpa [residueChores] using hresidueCard) (by decide)
      (by decide) (by decide) (Or.inl htwoLarge)

/-- The three-item intersecting-edge gap fill in source Case B.2.1(a).  The
first three agents are the short canonical agents; each receives one own-small
M₂ chore, while the remaining long agent regards all three gap chores as
large. -/
theorem existsGapFill_b1_intersecting
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4))) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap ({first, second, third} : Finset Item) ∧
      EnvyFreeForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ gap agent) ∧
      gap 0 = {first} ∧ gap 1 = {second} ∧ gap 2 = {third} ∧ gap 3 = ∅ := by
  classical
  let gap0 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 {first}
  let gap1 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 {second}
  let gap2 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 2 {third}
  let gap01 : Allocation (Fin 4) Item := fun agent => gap0 agent ∪ gap1 agent
  let gap : Allocation (Fin 4) Item := fun agent => gap01 agent ∪ gap2 agent
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) third).mp hthird |>.1
  have htypesNe : ({0, 1} : Finset (Fin 4)) ≠ {1, 2} := by decide
  have hfirstNeThird : first ≠ third := by
    intro heq
    subst third
    exact (Finset.disjoint_left.mp (m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) htypesNe) hfirst hthird).elim
  have hsecondNeThird : second ≠ third := by
    intro heq
    subst third
    exact (Finset.disjoint_left.mp (m2TypeChorePool_disjoint_of_ne cost m2Chores
      ({0, 1} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) htypesNe) hsecond hthird).elim
  have hgap0Allocation : IsAllocationOf gap0 {first} := isAllocationOf_allocateAllTo 0 {first}
  have hgap1Allocation : IsAllocationOf gap1 {second} := isAllocationOf_allocateAllTo 1 {second}
  have hgap2Allocation : IsAllocationOf gap2 {third} := isAllocationOf_allocateAllTo 2 {third}
  have hfirstSecondDisjoint : Disjoint ({first} : Finset Item) {second} := by
    rw [Finset.disjoint_singleton_right]
    simpa only [Finset.mem_singleton] using Ne.symm hfirstNeSecond
  have hfirstSecondThirdDisjoint : Disjoint ({first, second} : Finset Item) {third} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hfirstNeThird, Ne.symm hsecondNeThird⟩
  have hgap01Allocation : IsAllocationOf gap01 ({first, second} : Finset Item) := by
    simpa [gap01] using isAllocationOf_union gap0 gap1 {first} {second}
      hfirstSecondDisjoint hgap0Allocation hgap1Allocation
  have hgapAllocation : IsAllocationOf gap ({first, second, third} : Finset Item) := by
    simpa [gap] using isAllocationOf_union gap01 gap2 ({first, second} : Finset Item) {third}
      hfirstSecondThirdDisjoint hgap01Allocation hgap2Allocation
  have hgapZero : gap 0 = {first} := by simp [gap, gap01, gap0, gap1, gap2, allocateAllTo]
  have hgapOne : gap 1 = {second} := by simp [gap, gap01, gap0, gap1, gap2, allocateAllTo]
  have hgapTwo : gap 2 = {third} := by simp [gap, gap01, gap0, gap1, gap2, allocateAllTo]
  have hgapThree : gap 3 = ∅ := by simp [gap, gap01, gap0, gap1, gap2, allocateAllTo]
  have hgapPool : ({first, second, third} : Finset Item) ⊆ m2Chores := by
    intro chore hchore
    simp only [Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hprefixGap : Disjoint prefixChores ({first, second, third} : Finset Item) :=
    hprefixM2.mono_right hgapPool
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hfirstSmallZero : cost 0 first = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      first 0 hfirst (by simp)
  have hsecondSmallOne : cost 1 second = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
      second 1 hsecond (by simp)
  have hthirdSmallTwo : cost 2 third = 1 :=
    m2TypeChorePool_small_for_endpoint cost m2Chores ({1, 2} : Finset (Fin 4))
      third 2 hthird (by simp)
  have hgapOwnCost : additiveChoreCost cost 0 (gap 0) = 1 ∧
      additiveChoreCost cost 1 (gap 1) = 1 ∧
      additiveChoreCost cost 2 (gap 2) = 1 := by
    constructor
    · rw [hgapZero]
      simp [additiveChoreCost, hfirstSmallZero]
    constructor
    · rw [hgapOne]
      simp [additiveChoreCost, hsecondSmallOne]
    · rw [hgapTwo]
      simp [additiveChoreCost, hthirdSmallTwo]
  have hgapLongCost : additiveChoreCost cost 3 (gap 0) = r ∧
      additiveChoreCost cost 3 (gap 1) = r ∧
      additiveChoreCost cost 3 (gap 2) = r := by
    have hfirstLarge : cost 3 first = r :=
      m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
        first 3 hcost hfirst (by simp)
    have hsecondLarge : cost 3 second = r :=
      m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
        second 3 hcost hsecond (by simp)
    have hthirdLarge : cost 3 third = r :=
      m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
        third 3 hcost hthird (by simp)
    constructor
    · rw [hgapZero]
      simp [additiveChoreCost, hfirstLarge]
    constructor
    · rw [hgapOne]
      simp [additiveChoreCost, hsecondLarge]
    · rw [hgapTwo]
      simp [additiveChoreCost, hthirdLarge]
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hgapShortLower : ∀ observer owner : Fin 4, owner ≠ 3 →
      1 ≤ additiveChoreCost cost observer (gap owner) := by
    intro observer owner howner
    fin_cases owner
    · change 1 ≤ additiveChoreCost cost observer (gap 0)
      rw [hgapZero]
      simp [additiveChoreCost, hcostLower observer first]
    · change 1 ≤ additiveChoreCost cost observer (gap 1)
      rw [hgapOne]
      simp [additiveChoreCost, hcostLower observer second]
    · change 1 ≤ additiveChoreCost cost observer (gap 2)
      rw [hgapTwo]
      simp [additiveChoreCost, hcostLower observer third]
    · exact (howner rfl).elim
  have hgapShortOwnCost : ∀ owner : Fin 4, owner ≠ 3 →
      additiveChoreCost cost owner (gap owner) = 1 := by
    intro owner howner
    fin_cases owner
    · change additiveChoreCost cost 0 (gap 0) = 1
      exact hgapOwnCost.1
    · change additiveChoreCost cost 1 (gap 1) = 1
      exact hgapOwnCost.2.1
    · change additiveChoreCost cost 2 (gap 2) = 1
      exact hgapOwnCost.2.2
    · exact (howner rfl).elim
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith) (by
      intro own comparison
      fin_cases own <;> fin_cases comparison <;>
        simp [hquota0, hquota1, hquota2, hquota3] <;> omega)
  have hquotaShort : ∀ agent : Fin 4, agent ≠ 3 → quota agent = a := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact hquota1
    · exact hquota2
    · exact (hne rfl).elim
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    intro own comparison
    by_cases hownLong : own = 3
    · subst own
      by_cases hcomparisonLong : comparison = 3
      · subst comparison
        exact le_rfl
      · fin_cases comparison
        · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ gap 3) ≤
            additiveChoreCost cost 3 (prefixAllocation 0 ∪ gap 0)
          rw [hleftCost 3 3, hleftCost 3 0, hgapLongCost.1, hgapThree]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 3 0]
        · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ gap 3) ≤
            additiveChoreCost cost 3 (prefixAllocation 1 ∪ gap 1)
          rw [hleftCost 3 3, hleftCost 3 1, hgapLongCost.2.1, hgapThree]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 3 1]
        · change additiveChoreCost cost 3 (prefixAllocation 3 ∪ gap 3) ≤
            additiveChoreCost cost 3 (prefixAllocation 2 ∪ gap 2)
          rw [hleftCost 3 3, hleftCost 3 2, hgapLongCost.2.2, hgapThree]
          simp only [additiveChoreCost_empty, add_zero]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 3 2]
        · exact (hcomparisonLong rfl).elim
    · by_cases hcomparisonLong : comparison = 3
      · subst comparison
        rw [hleftCost own own, hleftCost own 3, hgapThree]
        simp only [additiveChoreCost_empty, add_zero]
        fin_cases own
        · simpa [hgapOwnCost.1] using
            hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
              prefixAllocation hcost (by linarith) 0 3 (by rw [hquota3, hquota0])
        · simpa [hgapOwnCost.2.1] using
            hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
              prefixAllocation hcost (by linarith) 1 3 (by rw [hquota3, hquota1])
        · simpa [hgapOwnCost.2.2] using
            hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
              prefixAllocation hcost (by linarith) 2 3 (by rw [hquota3, hquota2])
        · exact (hownLong rfl).elim
      · rw [hleftCost own own, hleftCost own comparison]
        have hprefixLe := hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
          prefixAllocation hcost (by linarith) own comparison
          ((hquotaShort own hownLong).trans (hquotaShort comparison hcomparisonLong).symm)
        have hownGap := hgapShortOwnCost own hownLong
        have hcomparisonGap := hgapShortLower own comparison hcomparisonLong
        linarith
  exact ⟨gap, hgapAllocation, hleftEnvyFree, hgapZero, hgapOne, hgapTwo, hgapThree⟩

/-- The nonexceptional residual outcome of source Case B.2.1(a). -/
theorem existsEfxOfM01M2_b1_intersecting_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second, third})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOne, _hgapTwo, _hgapThree⟩ :=
    existsGapFill_b1_intersecting Item r cost prefixChores m2Chores a quota prefixAllocation
      first second third hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hfirst hsecond hfirstNeSecond hthird
  let gapChores : Finset Item := {first, second, third}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) third).mp hthird |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ chore ∈ residueChores, IsSmallForExactlyTwo cost chore := by
    intro chore hchore
    exact hm2Small chore (Finset.sdiff_subset hchore)
  have hnotExceptional' : ¬ IsM2Exceptional cost residueChores := by
    simpa [residueChores, gapChores] using hnotExceptional
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hcanonical.1 (by simpa [gapChores] using hgapAllocation)
    hleftEnvyFree hresidueSmall hnotExceptional'

/-- The regular exceptional outcome of source Case B.2.1(a), whose
exceptional pair is the unaffected edge `(2,3)`.  Agent `3` is selected as
the all-large residual owner; if her canonical prefix contains a small item,
the type-`(1,2)` gap chore on agent `2` supplies the required `r - 1` slack. -/
theorem existsEfxOfM01M2_b1_intersecting_exceptional_unaffectedEdge
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)))
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second, third}) 3 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOne, hgapTwo, hgapThree⟩ :=
    existsGapFill_b1_intersecting Item r cost prefixChores m2Chores a quota prefixAllocation
      first second third hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hfirst hsecond hfirstNeSecond hthird
  let gapChores : Finset Item := {first, second, third}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({1, 2} : Finset (Fin 4)) third).mp hthird |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent)
      (by simpa [gapChores] using hprefixGap)
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hthirdLargeThree : cost 3 third = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({1, 2} : Finset (Fin 4))
      third 3 hcost hthird (by simp)
  have hgapTwoThree : additiveChoreCost cost 3 (gap 2) = r := by
    rw [hgapTwo]
    simp [additiveChoreCost, hthirdLargeThree]
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary, htypesDisjoint,
    hmemThree, hmemTwo, hshape⟩
  obtain ⟨right, hrightAllocation, hunit, hrightLarge, hrightAway, hrightComparison⟩ :=
    existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q
      (by linarith) hcost hdominant hauxiliary htypesDisjoint hshape 3 2
      hmemThree hmemTwo (by decide)
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 (by simpa [gapChores] using hgapAllocation)
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro item hleftItem hresidueItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue hprefixItem hresidueItem).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgapItem hresidueItem).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftItem hrightItem
    have hrightPool : item ∈ residueChores := hrightAllocation.1 agent item hrightItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent item hprefixItem) hrightPool).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        ((by simpa [gapChores] using hgapAllocation.1 agent item hgapItem)) hrightPool).elim
  have hspecialLeft :
      (∀ item ∈ left 3, IsLargeChore cost r 3 item) ∨
        additiveChoreCost cost 3 (left 3) + (r - 1) ≤
          additiveChoreCost cost 3 (left 2) := by
    by_cases hsmall : ∃ item ∈ prefixAllocation 3, IsSmallChore cost 3 item
    · right
      obtain ⟨item, hitem, hitemSmall⟩ := hsmall
      have hprefixSlack := EFXForChores.additive_sub_one_le_of_small cost prefixAllocation
        hprefixEFX 3 2 item hitem hitemSmall
      change additiveChoreCost cost 3 (prefixAllocation 3 ∪ gap 3) + (r - 1) ≤
        additiveChoreCost cost 3 (prefixAllocation 2 ∪ gap 2)
      rw [hleftCost 3 3, hleftCost 3 2, hgapThree, hgapTwoThree]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · left
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 3 := by
        simpa [left, hgapThree] using hitem
      rcases hcost 3 item with hsmallItem | hlargeItem
      · exact (hsmall ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmallItem⟩).elim
      · simpa [IsLargeChore] using hlargeItem
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_controlled_exceptional Item r cost left right 3 2
    hbundlesDisjoint hcostLower (by simpa [left] using hleftEnvyFree) hunit hrightLarge
    hrightAway hrightComparison hspecialLeft

/-- The three type-`(0,1)` gap chores in source Case B.2.1(b).  Agents `0`
and `1` receive own-small chores, while short agent `3` receives a large
chore exactly offset by her assumed `r` prefix advantage over long agent `2`. -/
theorem existsGapFill_b1_disjoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 2) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap ({first, second, third} : Finset Item) ∧
      EnvyFreeForChores (additiveChoreCost cost)
        (fun agent => prefixAllocation agent ∪ gap agent) ∧
      gap 0 = {first} ∧ gap 1 = {second} ∧ gap 2 = ∅ ∧ gap 3 = {third} := by
  classical
  let gap0 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 {first}
  let gap1 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 1 {second}
  let gap3 : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 3 {third}
  let gap01 : Allocation (Fin 4) Item := fun agent => gap0 agent ∪ gap1 agent
  let gap : Allocation (Fin 4) Item := fun agent => gap01 agent ∪ gap3 agent
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) third).mp hthird |>.1
  have hgap0Allocation : IsAllocationOf gap0 {first} := isAllocationOf_allocateAllTo 0 {first}
  have hgap1Allocation : IsAllocationOf gap1 {second} := isAllocationOf_allocateAllTo 1 {second}
  have hgap3Allocation : IsAllocationOf gap3 {third} := isAllocationOf_allocateAllTo 3 {third}
  have hfirstSecondDisjoint : Disjoint ({first} : Finset Item) {second} := by
    rw [Finset.disjoint_singleton_right]
    simpa only [Finset.mem_singleton] using Ne.symm hfirstNeSecond
  have hfirstSecondThirdDisjoint : Disjoint ({first, second} : Finset Item) {third} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hfirstNeThird, Ne.symm hsecondNeThird⟩
  have hgap01Allocation : IsAllocationOf gap01 ({first, second} : Finset Item) := by
    simpa [gap01] using isAllocationOf_union gap0 gap1 {first} {second}
      hfirstSecondDisjoint hgap0Allocation hgap1Allocation
  have hgapAllocation : IsAllocationOf gap ({first, second, third} : Finset Item) := by
    simpa [gap] using isAllocationOf_union gap01 gap3 ({first, second} : Finset Item) {third}
      hfirstSecondThirdDisjoint hgap01Allocation hgap3Allocation
  have hgapZero : gap 0 = {first} := by simp [gap, gap01, gap0, gap1, gap3, allocateAllTo]
  have hgapOne : gap 1 = {second} := by simp [gap, gap01, gap0, gap1, gap3, allocateAllTo]
  have hgapTwo : gap 2 = ∅ := by simp [gap, gap01, gap0, gap1, gap3, allocateAllTo]
  have hgapThree : gap 3 = {third} := by simp [gap, gap01, gap0, gap1, gap3, allocateAllTo]
  have hgapPool : ({first, second, third} : Finset Item) ⊆ m2Chores := by
    intro chore hchore
    simp only [Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hprefixGap : Disjoint prefixChores ({first, second, third} : Finset Item) :=
    hprefixM2.mono_right hgapPool
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hsmallGap (observer owner : Fin 4) (hobserver : observer = 0 ∨ observer = 1)
      (howner : owner = 0 ∨ owner = 1 ∨ owner = 3) :
      additiveChoreCost cost observer (gap owner) = 1 := by
    have hmem : observer ∈ ({0, 1} : Finset (Fin 4)) := by
      rcases hobserver with hzero | hone
      · subst observer
        simp
      · subst observer
        simp
    rcases howner with hzero | hone | hthree
    · subst owner
      rw [hgapZero]
      have hsmall : cost observer first = 1 :=
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          first observer hfirst hmem
      simp [additiveChoreCost, hsmall]
    · subst owner
      rw [hgapOne]
      have hsmall : cost observer second = 1 :=
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          second observer hsecond hmem
      simp [additiveChoreCost, hsmall]
    · subst owner
      rw [hgapThree]
      have hsmall : cost observer third = 1 :=
        m2TypeChorePool_small_for_endpoint cost m2Chores ({0, 1} : Finset (Fin 4))
          third observer hthird hmem
      simp [additiveChoreCost, hsmall]
  have hlargeGap (observer owner : Fin 4)
      (hobserver : observer = 2 ∨ observer = 3)
      (howner : owner = 0 ∨ owner = 1 ∨ owner = 3) :
      additiveChoreCost cost observer (gap owner) = r := by
    have hnotmem : observer ∉ ({0, 1} : Finset (Fin 4)) := by
      rcases hobserver with htwo | hthree
      · subst observer
        decide
      · subst observer
        decide
    rcases howner with hzero | hone | hthree
    · subst owner
      rw [hgapZero]
      have hlarge : cost observer first = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          first observer hcost hfirst hnotmem
      simp [additiveChoreCost, hlarge]
    · subst owner
      rw [hgapOne]
      have hlarge : cost observer second = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          second observer hcost hsecond hnotmem
      simp [additiveChoreCost, hlarge]
    · subst owner
      rw [hgapThree]
      have hlarge : cost observer third = r :=
        m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
          third observer hcost hthird hnotmem
      simp [additiveChoreCost, hlarge]
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith) (by
      intro own comparison
      fin_cases own <;> fin_cases comparison <;>
        simp [hquota0, hquota1, hquota2, hquota3] <;> omega)
  have hquotaShort : ∀ agent : Fin 4, agent ≠ 2 → quota agent = a := by
    intro agent hne
    fin_cases agent
    · exact hquota0
    · exact hquota1
    · exact (hne rfl).elim
    · exact hquota3
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    intro own comparison
    by_cases hownLong : own = 2
    · subst own
      by_cases hcomparisonLong : comparison = 2
      · subst comparison
        exact le_rfl
      · rw [hleftCost 2 2, hleftCost 2 comparison, hgapTwo]
        simp only [additiveChoreCost_empty, add_zero]
        fin_cases comparison
        · change additiveChoreCost cost 2 (prefixAllocation 2) ≤
            additiveChoreCost cost 2 (prefixAllocation 0) + additiveChoreCost cost 2 (gap 0)
          rw [hlargeGap 2 0 (Or.inl rfl) (Or.inl rfl)]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 2 0]
        · change additiveChoreCost cost 2 (prefixAllocation 2) ≤
            additiveChoreCost cost 2 (prefixAllocation 1) + additiveChoreCost cost 2 (gap 1)
          rw [hlargeGap 2 1 (Or.inl rfl) (Or.inr (Or.inl rfl))]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 2 1]
        · exact (hcomparisonLong rfl).elim
        · change additiveChoreCost cost 2 (prefixAllocation 2) ≤
            additiveChoreCost cost 2 (prefixAllocation 3) + additiveChoreCost cost 2 (gap 3)
          rw [hlargeGap 2 3 (Or.inl rfl) (Or.inr (Or.inr rfl))]
          linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
            (by linarith) 2 3]
    · by_cases hownThree : own = 3
      · subst own
        by_cases hcomparisonLong : comparison = 2
        · subst comparison
          rw [hleftCost 3 3, hleftCost 3 2,
            hlargeGap 3 3 (Or.inr rfl) (Or.inr (Or.inr rfl)), hgapTwo]
          simp only [additiveChoreCost_empty, add_zero]
          linarith
        · have hcomparisonShort : comparison = 0 ∨ comparison = 1 ∨ comparison = 3 := by
            fin_cases comparison
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact (hcomparisonLong rfl).elim
            · exact Or.inr (Or.inr rfl)
          rw [hleftCost 3 3, hleftCost 3 comparison,
            hlargeGap 3 3 (Or.inr rfl) (Or.inr (Or.inr rfl)),
            hlargeGap 3 comparison (Or.inr rfl) hcomparisonShort]
          simpa [add_comm] using add_le_add_right
            (hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
              prefixAllocation hcost (by linarith) 3 comparison
              ((hquotaShort 3 (by decide)).trans (hquotaShort comparison hcomparisonLong).symm)) r
      · by_cases hcomparisonLong : comparison = 2
        · subst comparison
          have hownShort : own = 0 ∨ own = 1 := by
            fin_cases own
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact (hownLong rfl).elim
            · exact (hownThree rfl).elim
          rw [hleftCost own own, hleftCost own 2, hgapTwo]
          simp only [additiveChoreCost_empty, add_zero]
          rw [hsmallGap own own hownShort (by rcases hownShort with rfl | rfl <;> simp)]
          exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
            prefixAllocation hcost (by linarith) own 2
            (by rw [hquota2, hquotaShort own (by rcases hownShort with rfl | rfl <;> decide)])
        · have hownShort : own = 0 ∨ own = 1 := by
            fin_cases own
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact (hownLong rfl).elim
            · exact (hownThree rfl).elim
          have hcomparisonShort : comparison = 0 ∨ comparison = 1 ∨ comparison = 3 := by
            fin_cases comparison
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact (hcomparisonLong rfl).elim
            · exact Or.inr (Or.inr rfl)
          rw [hleftCost own own, hleftCost own comparison,
            hsmallGap own own hownShort (by rcases hownShort with rfl | rfl <;> simp),
            hsmallGap own comparison hownShort hcomparisonShort]
          simpa [add_comm] using add_le_add_right
            (hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
              prefixAllocation hcost (by linarith) own comparison
              ((hquotaShort own (by rcases hownShort with rfl | rfl <;> decide)).trans
                (hquotaShort comparison hcomparisonLong).symm)) 1
  exact ⟨gap, hgapAllocation, hleftEnvyFree, hgapZero, hgapOne, hgapTwo, hgapThree⟩

/-- The nonexceptional residual outcome of source Case B.2.1(b). -/
theorem existsEfxOfM01M2_b1_disjoint_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 2) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second, third})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOne, _hgapTwo, _hgapThree⟩ :=
    existsGapFill_b1_disjoint Item r cost prefixChores m2Chores a quota prefixAllocation
      first second third hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hshortAdvantage hfirst hsecond hthird hfirstNeSecond hfirstNeThird hsecondNeThird
  let gapChores : Finset Item := {first, second, third}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) third).mp hthird |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ chore ∈ residueChores, IsSmallForExactlyTwo cost chore := by
    intro chore hchore
    exact hm2Small chore (Finset.sdiff_subset hchore)
  have hnotExceptional' : ¬ IsM2Exceptional cost residueChores := by
    simpa [residueChores, gapChores] using hnotExceptional
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hcanonical.1 (by simpa [gapChores] using hgapAllocation)
    hleftEnvyFree hresidueSmall hnotExceptional'

/-- The regular exceptional residual outcome of source Case B.2.1(b).  The
long endpoint `2` is selected as the all-large residual owner, and the gap
chore on its short companion `3` provides the `r - 1` fallback. -/
theorem existsEfxOfM01M2_b1_disjoint_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second third : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hshortAdvantage : additiveChoreCost cost 3 (prefixAllocation 3) ≤
      additiveChoreCost cost 3 (prefixAllocation 2) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hthird : third ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) (hfirstNeThird : first ≠ third)
    (hsecondNeThird : second ≠ third)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second, third}) 2 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOne, hgapTwo, hgapThree⟩ :=
    existsGapFill_b1_disjoint Item r cost prefixChores m2Chores a quota prefixAllocation
      first second third hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hshortAdvantage hfirst hsecond hthird hfirstNeSecond hfirstNeThird hsecondNeThird
  let gapChores : Finset Item := {first, second, third}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hthirdM2 : third ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) third).mp hthird |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
    · exact hthirdM2
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent)
      (by simpa [gapChores] using hprefixGap)
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hthirdLargeTwo : cost 2 third = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      third 2 hcost hthird (by simp)
  have hgapThreeTwo : additiveChoreCost cost 2 (gap 3) = r := by
    rw [hgapThree]
    simp [additiveChoreCost, hthirdLargeTwo]
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary, htypesDisjoint,
    hmemTwo, hmemThree, hshape⟩
  obtain ⟨right, hrightAllocation, hunit, hrightLarge, hrightAway, hrightComparison⟩ :=
    existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q
      (by linarith) hcost hdominant hauxiliary htypesDisjoint hshape 2 3
      hmemTwo hmemThree (by decide)
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 (by simpa [gapChores] using hgapAllocation)
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro item hleftItem hresidueItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue hprefixItem hresidueItem).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgapItem hresidueItem).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftItem hrightItem
    have hrightPool : item ∈ residueChores := hrightAllocation.1 agent item hrightItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent item hprefixItem) hrightPool).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        ((by simpa [gapChores] using hgapAllocation.1 agent item hgapItem)) hrightPool).elim
  have hspecialLeft :
      (∀ item ∈ left 2, IsLargeChore cost r 2 item) ∨
        additiveChoreCost cost 2 (left 2) + (r - 1) ≤
          additiveChoreCost cost 2 (left 3) := by
    by_cases hsmall : ∃ item ∈ prefixAllocation 2, IsSmallChore cost 2 item
    · right
      obtain ⟨item, hitem, hitemSmall⟩ := hsmall
      have hprefixSlack := EFXForChores.additive_sub_one_le_of_small cost prefixAllocation
        hprefixEFX 2 3 item hitem hitemSmall
      change additiveChoreCost cost 2 (prefixAllocation 2 ∪ gap 2) + (r - 1) ≤
        additiveChoreCost cost 2 (prefixAllocation 3 ∪ gap 3)
      rw [hleftCost 2 2, hleftCost 2 3, hgapTwo, hgapThreeTwo]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · left
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 2 := by
        simpa [left, hgapTwo] using hitem
      rcases hcost 2 item with hsmallItem | hlargeItem
      · exact (hsmall ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmallItem⟩).elim
      · simpa [IsLargeChore] using hlargeItem
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_controlled_exceptional Item r cost left right 2 3
    hbundlesDisjoint hcostLower (by simpa [left] using hleftEnvyFree) hunit hrightLarge
    hrightAway hrightComparison hspecialLeft

theorem existsEfxOfM01M2_b3_oneType_heavyEndpoints_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {item}) 2 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, hgapThree, hgapOther⟩ :=
    existsGapFill_b3_disjoint_heavyEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation item hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
      hquota3 hsuper hitem hprefixZeroSmall hprefixOneSmall
  let gapChores : Finset Item := {item}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    have : chore = item := by simpa [gapChores] using hchore
    subst chore
    exact hitemM2
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hprefixGapDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    apply Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent)
      (by simpa [gapChores] using hprefixGap)
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hprefixGapDisjoint owner)
  have hitemLargeTwo : cost 2 item = r :=
    m2TypeChorePool_large_for_nonendpoint r cost m2Chores ({0, 1} : Finset (Fin 4))
      item 2 hcost hitem (by simp)
  have hgapThreeTwo : additiveChoreCost cost 2 (gap 3) = r := by
    rw [hgapThree]
    simp [additiveChoreCost, hitemLargeTwo]
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary, htypesDisjoint,
    hmemTwo, hmemThree, hshape⟩
  obtain ⟨right, hrightAllocation, hunit, hrightLarge, hrightAway, hrightComparison⟩ :=
    existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q
      (by linarith) hcost hdominant hauxiliary htypesDisjoint hshape 2 3
      hmemTwo hmemThree (by decide)
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ gapChores) := by
    exact isAllocationOf_union prefixAllocation gap prefixChores gapChores hprefixGap
      hcanonical.1 (by simpa [gapChores] using hgapAllocation)
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro chore hleftItem hresidueItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue hprefixItem hresidueItem).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgapItem hresidueItem).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro chore hleftItem hrightItem
    have hrightPool : chore ∈ residueChores := hrightAllocation.1 agent chore hrightItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue
        (hcanonical.1.1 agent chore hprefixItem) hrightPool).elim
    · exact (Finset.disjoint_left.mp hgapResidue
        ((by simpa [gapChores] using hgapAllocation.1 agent chore hgapItem)) hrightPool).elim
  have hspecialLeft :
      (∀ chore ∈ left 2, IsLargeChore cost r 2 chore) ∨
        additiveChoreCost cost 2 (left 2) + (r - 1) ≤
          additiveChoreCost cost 2 (left 3) := by
    by_cases hsmall : ∃ chore ∈ prefixAllocation 2, IsSmallChore cost 2 chore
    · right
      obtain ⟨chore, hchore, hchoreSmall⟩ := hsmall
      have hprefixSlack := EFXForChores.additive_sub_one_le_of_small cost prefixAllocation
        hprefixEFX 2 3 chore hchore hchoreSmall
      change additiveChoreCost cost 2 (prefixAllocation 2 ∪ gap 2) + (r - 1) ≤
          additiveChoreCost cost 2 (prefixAllocation 3 ∪ gap 3)
      rw [hleftCost 2 2, hleftCost 2 3, hgapOther 2 (by decide)]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hprefixSlack, hgapThreeTwo]
    · left
      intro chore hchore
      have hprefixChore : chore ∈ prefixAllocation 2 := by
        simpa [left, hgapOther 2 (by decide)] using hchore
      rcases hcost 2 chore with hsmallChore | hlargeChore
      · exact (hsmall ⟨chore, hprefixChore,
          by simpa [IsSmallChore] using hsmallChore⟩).elim
      · simpa [IsLargeChore] using hlargeChore
  have hcostLower : ∀ agent chore, 1 ≤ cost agent chore :=
    fun agent chore => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent chore
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores)
      residueChores hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_controlled_exceptional Item r cost left right 2 3
    hbundlesDisjoint hcostLower (by simpa [left] using hleftEnvyFree) hunit hrightLarge
    hrightAway hrightComparison hspecialLeft

end HT26EFXChores
