import HT26EFXChores.HighRatioGapFilling

/-!
# The parallel-edge gap fill in source Case B.3.1

When the maximum M₂ edge type has multiplicity at least two, the source gives
two such chores to its two short endpoints before allocating a nonexceptional
residue.  This file records the envy-free prefix calculation.

Source: `EFXadditivechores.tex`, lines 2552--2611.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Two distinct type-`(0,1)` chores, one assigned to each short endpoint,
make a canonical `a,a,a+1,a+1` prefix envy-free. -/
theorem existsGapFill_b2_parallelShortEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap ({first, second} : Finset Item) ∧
        EnvyFreeForChores (additiveChoreCost cost)
          (fun agent => prefixAllocation agent ∪ gap agent) ∧
        gap 0 = {first} ∧ gap 1 = {second} ∧ gap 2 = ∅ ∧ gap 3 = ∅ := by
  classical
  let gap0 := allocateAllTo (Fin 4) Item 0 {first}
  let gap1 := allocateAllTo (Fin 4) Item 1 {second}
  let gap : Allocation (Fin 4) Item := fun agent => gap0 agent ∪ gap1 agent
  have hfirstM2 := (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 := (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hsingletons : Disjoint ({first} : Finset Item) {second} := by
    rw [Finset.disjoint_singleton_right]
    simpa using Ne.symm hfirstNeSecond
  have hgapAllocation : IsAllocationOf gap ({first, second} : Finset Item) := by
    simpa [gap] using isAllocationOf_union gap0 gap1 {first} {second} hsingletons
      (isAllocationOf_allocateAllTo 0 {first}) (isAllocationOf_allocateAllTo 1 {second})
  have hgap0 : gap 0 = {first} := by simp [gap, gap0, gap1, allocateAllTo]
  have hgap1 : gap 1 = {second} := by simp [gap, gap0, gap1, allocateAllTo]
  have hgap2 : gap 2 = ∅ := by simp [gap, gap0, gap1, allocateAllTo]
  have hgap3 : gap 3 = ∅ := by simp [gap, gap0, gap1, allocateAllTo]
  have hprefixGap : Disjoint prefixChores ({first, second} : Finset Item) := by
    apply hprefixM2.mono_right
    intro item hitem
    rcases Finset.mem_insert.mp hitem with rfl | hsecond'
    · exact hfirstM2
    · exact Finset.mem_singleton.mp hsecond' ▸ hsecondM2
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hbundlesDisjoint owner)
  have hsmall (observer owner : Fin 4) (hobserver : observer = 0 ∨ observer = 1)
      (howner : owner = 0 ∨ owner = 1) :
      additiveChoreCost cost observer (gap owner) = 1 := by
    rcases howner with rfl | rfl
    · rw [hgap0]
      have hmem : observer ∈ ({0, 1} : Finset (Fin 4)) := by rcases hobserver with rfl | rfl <;> simp
      have hcost' := m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) first observer hfirst hmem
      simpa only [additiveChoreCost, Finset.sum_singleton, IsSmallChore] using hcost'
    · rw [hgap1]
      have hmem : observer ∈ ({0, 1} : Finset (Fin 4)) := by rcases hobserver with rfl | rfl <;> simp
      have hcost' := m2TypeChorePool_small_for_endpoint cost m2Chores
        ({0, 1} : Finset (Fin 4)) second observer hsecond hmem
      simpa only [additiveChoreCost, Finset.sum_singleton, IsSmallChore] using hcost'
  have hlarge (observer owner : Fin 4) (hobserver : observer = 2 ∨ observer = 3)
      (howner : owner = 0 ∨ owner = 1) :
      additiveChoreCost cost observer (gap owner) = r := by
    rcases howner with rfl | rfl
    · rw [hgap0]
      have hnot : observer ∉ ({0, 1} : Finset (Fin 4)) := by rcases hobserver with rfl | rfl <;> decide
      have hcost' := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) first observer hcost hfirst hnot
      simpa only [additiveChoreCost, Finset.sum_singleton, IsLargeChore] using hcost'
    · rw [hgap1]
      have hnot : observer ∉ ({0, 1} : Finset (Fin 4)) := by rcases hobserver with rfl | rfl <;> decide
      have hcost' := m2TypeChorePool_large_for_nonendpoint r cost m2Chores
        ({0, 1} : Finset (Fin 4)) second observer hcost hsecond hnot
      simpa only [additiveChoreCost, Finset.sum_singleton, IsLargeChore] using hcost'
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith) (by
      intro own comparison
      fin_cases own <;> fin_cases comparison <;>
        simp [hquota0, hquota1, hquota2, hquota3] <;> omega)
  have hequal : ∀ first second : Fin 4, quota first = quota second →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hquota
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second hquota
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
    change ∀ own comparison,
      additiveChoreCost cost own (prefixAllocation own ∪ gap own) ≤
        additiveChoreCost cost own (prefixAllocation comparison ∪ gap comparison)
    intro own comparison
    have hagentCases (agent : Fin 4) :
        agent = 0 ∨ agent = 1 ∨ agent = 2 ∨ agent = 3 := by
      fin_cases agent <;> simp
    rcases hagentCases own with (rfl | rfl | rfl | rfl) <;>
      rcases hagentCases comparison with (rfl | rfl | rfl | rfl)
    · exact le_rfl
    · rw [hfinalCost 0 0, hfinalCost 0 1, hsmall 0 0 (Or.inl rfl) (Or.inl rfl),
        hsmall 0 1 (Or.inl rfl) (Or.inr rfl)]
      linarith [hequal 0 1 (by rw [hquota0, hquota1])]
    · rw [hfinalCost 0 0, hfinalCost 0 2, hgap2, hsmall 0 0 (Or.inl rfl) (Or.inl rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
        prefixAllocation hcost (by linarith) 0 2 (by rw [hquota2, hquota0])
    · rw [hfinalCost 0 0, hfinalCost 0 3, hgap3, hsmall 0 0 (Or.inl rfl) (Or.inl rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
        prefixAllocation hcost (by linarith) 0 3 (by rw [hquota3, hquota0])
    · rw [hfinalCost 1 1, hfinalCost 1 0, hsmall 1 1 (Or.inr rfl) (Or.inr rfl),
        hsmall 1 0 (Or.inr rfl) (Or.inl rfl)]
      linarith [hequal 1 0 (by rw [hquota1, hquota0])]
    · exact le_rfl
    · rw [hfinalCost 1 1, hfinalCost 1 2, hgap2, hsmall 1 1 (Or.inr rfl) (Or.inr rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
        prefixAllocation hcost (by linarith) 1 2 (by rw [hquota2, hquota1])
    · rw [hfinalCost 1 1, hfinalCost 1 3, hgap3, hsmall 1 1 (Or.inr rfl) (Or.inr rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
        prefixAllocation hcost (by linarith) 1 3 (by rw [hquota3, hquota1])
    · rw [hfinalCost 2 2, hfinalCost 2 0, hgap2, hlarge 2 0 (Or.inl rfl) (Or.inl rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith) 2 0
    · rw [hfinalCost 2 2, hfinalCost 2 1, hgap2, hlarge 2 1 (Or.inl rfl) (Or.inr rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith) 2 1
    · exact le_rfl
    · rw [hfinalCost 2 2, hfinalCost 2 3, hgap2, hgap3]
      simp only [additiveChoreCost_empty, add_zero]
      exact hequal 2 3 (by rw [hquota2, hquota3])
    · rw [hfinalCost 3 3, hfinalCost 3 0, hgap3, hlarge 3 0 (Or.inr rfl) (Or.inl rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith) 3 0
    · rw [hfinalCost 3 3, hfinalCost 3 1, hgap3, hlarge 3 1 (Or.inr rfl) (Or.inr rfl)]
      simp only [additiveChoreCost_empty, add_zero]
      exact hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost (by linarith) 3 1
    · rw [hfinalCost 3 3, hfinalCost 3 2, hgap3, hgap2]
      simp only [additiveChoreCost_empty, add_zero]
      exact hequal 3 2 (by rw [hquota3, hquota2])
    · exact le_rfl
  exact ⟨gap, hgapAllocation, hleftEnvyFree, hgap0, hgap1, hgap2, hgap3⟩

/-- The nonexceptional-residual part of source Case B.3.1: after two parallel
type-`(0,1)` chores are given to their small endpoints, the generic M₂
composition theorem completes the allocation. -/
theorem existsEfxOfB2_parallelShortEndpoints_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, _hgapZero, _hgapOne, _hgapTwo, _hgapThree⟩ :=
    existsGapFill_b2_parallelShortEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hfirst hsecond hfirstNeSecond
  let gapChores : Finset Item := {first, second}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
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

/-- The exceptional-residual subcase of source Case B.3.1 when its exceptional
pair is the two long prefix agents.  The two gap chores remain on the short
agents, so the exceptional-residue combination lemma applies unchanged. -/
theorem existsEfxOfB2_parallelShortEndpoints_exceptional_longPair
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hfirstNeSecond : first ≠ second)
    (hexceptional : IsM2ExceptionalWithEndpoints cost (m2Chores \ {first, second}) 2 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hleftEnvyFree, hgapZero, hgapOne, hgapTwo, hgapThree⟩ :=
    existsGapFill_b2_parallelShortEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1
      hquota2 hquota3 hfirst hsecond hfirstNeSecond
  let gapChores : Finset Item := {first, second}
  let residueChores : Finset Item := m2Chores \ gapChores
  have hfirstM2 : first ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) second).mp hsecond |>.1
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro chore hchore
    simp only [gapChores, Finset.mem_insert, Finset.mem_singleton] at hchore
    rcases hchore with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hgapResidue : Disjoint gapChores residueChores := Finset.disjoint_sdiff
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hquotaCases : ∀ agent : Fin 4, quota agent = a ∨ quota agent = a + 1 := by
    intro agent
    fin_cases agent
    · exact Or.inl hquota0
    · exact Or.inl hquota1
    · exact Or.inr hquota2
    · exact Or.inr hquota3
  have hgapLong : ∀ agent : Fin 4, quota agent ≠ a → gap agent = ∅ := by
    intro agent hquotaNe
    fin_cases agent
    · exact (hquotaNe hquota0).elim
    · exact (hquotaNe hquota1).elim
    · exact hgapTwo
    · exact hgapThree
  have hexceptional' : IsM2ExceptionalWithEndpoints cost residueChores 2 3 := by
    simpa [residueChores, gapChores] using hexceptional
  exact exceptional_residue_combination_proof Item r cost prefixChores m2Chores
    gapChores residueChores a quota prefixAllocation gap hr hcost hprefixM2 hgapResidue
    hgapResidueUnion hprefixSmall hcanonical hquotaCases
    (by simpa [gapChores] using hgapAllocation) hgapLong hleftEnvyFree
    2 3 (by simpa [IsM2ExceptionalWithEndpoints] using hexceptional') (by decide)
    hquota2 hquota3

end HT26EFXChores
