import HT26EFXChores.Canonical

/-!
# Exceptional M2 residue combination

This module formalizes the exceptional-residue allocation used in the paper's
concatenation argument.  Its public bridge will keep the one large-removal
comparison explicit, rather than concealing it in a generic EFX witness.

Source: `EFXadditivechores.tex`, lines 1700--1729.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

private theorem exceptional_quota_sum (q : ℕ) (companion : Fin 4) :
    Finset.univ.sum (m2Quota q (Finset.univ.erase companion)) = 4 * q + 3 := by
  fin_cases companion <;>
    simp [m2Quota, Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm] <;>
    decide

private theorem auxiliary_eq_pair (auxiliary : Finset (Fin 4)) (special companion : Fin 4)
    (hcard : auxiliary.card = 2) (hspecial : special ∈ auxiliary)
    (hcompanion : companion ∈ auxiliary) (hne : special ≠ companion) :
    auxiliary = {special, companion} := by
  have hsubset : ({special, companion} : Finset (Fin 4)) ⊆ auxiliary := by
    intro agent hagent
    simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with rfl | rfl
    · exact hspecial
    · exact hcompanion
  have hpairCard : ({special, companion} : Finset (Fin 4)).card = 2 := by simp [hne]
  exact (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm

private theorem mem_dominant_of_not_auxiliary (dominant auxiliary : Finset (Fin 4))
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary) (agent : Fin 4) (hnotAuxiliary : agent ∉ auxiliary) :
    agent ∈ dominant := by
  have hunion : dominant ∪ auxiliary = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisjoint, hdominant, hauxiliary]
    norm_num
  have hmem : agent ∈ dominant ∪ auxiliary := by simp [hunion]
  rcases Finset.mem_union.mp hmem with hdominantMem | hauxiliaryMem
  · exact hdominantMem
  · exact (hnotAuxiliary hauxiliaryMem).elim

/-- A fixed-type exceptional residue has a balanced allocation in which a
chosen auxiliary endpoint is the only possible large-removal endpoint. -/
private theorem exists_fixed_exceptional_controlled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (dominant auxiliary : Finset (Fin 4)) (q : ℕ)
    (special companion : Fin 4)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary)
    (hspecial : special ∈ auxiliary) (hcompanion : companion ∈ auxiliary)
    (hne : special ≠ companion)
    (htype : ∀ item ∈ chores, smallAgentSet cost item = dominant)
    (hcard : chores.card = 4 * q + 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
        additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) ∧
      (∀ other, additiveChoreCost cost companion (allocation companion) ≤
        additiveChoreCost cost companion (allocation other)) ∧
      ∀ agent, (allocation agent).card = if agent = companion then q else q + 1 := by
  classical
  let longAgents : Finset (Fin 4) := Finset.univ.erase companion
  let quota := m2Quota q longAgents
  have hsum : Finset.univ.sum quota = chores.card := by
    rw [show quota = m2Quota q (Finset.univ.erase companion) by rfl,
      exceptional_quota_sum, hcard]
  obtain ⟨allocation, halloc, hquota⟩ :=
    existsAllocationOfQuota (Fin 4) Item chores quota hsum
  have hauxEq : auxiliary = {special, companion} :=
    auxiliary_eq_pair auxiliary special companion hauxiliary hspecial hcompanion hne
  have hspecialNotDominant : special ∉ dominant := by
    intro hspecialDominant
    exact (Finset.disjoint_left.mp hdisjoint hspecialDominant hspecial).elim
  have hcompanionNotDominant : companion ∉ dominant := by
    intro hcompanionDominant
    exact (Finset.disjoint_left.mp hdisjoint hcompanionDominant hcompanion).elim
  have hcostSmall (agent : Fin 4) (hagent : agent ∈ dominant)
      (item : Item) (hitem : item ∈ chores) : IsSmallChore cost agent item := by
    have hmem : agent ∈ smallAgentSet cost item := by
      simpa [htype item hitem] using hagent
    simpa [smallAgentSet] using hmem
  have hcostLarge (agent : Fin 4) (hagent : agent ∉ dominant)
      (item : Item) (hitem : item ∈ chores) : IsLargeChore cost r agent item := by
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [htype item hitem] using hmem
    · simpa [IsLargeChore] using hlarge
  have hcardSpecial : (allocation special).card = q + 1 := by
    rw [hquota]
    simp [quota, longAgents, m2Quota, hne]
  have hcardCompanion : (allocation companion).card = q := by
    rw [hquota]
    simp [quota, longAgents, m2Quota]
  have hcardDominant (agent : Fin 4) (hagent : agent ∈ dominant) :
      (allocation agent).card = q + 1 := by
    have hneCompanion : agent ≠ companion := by
      intro heq
      subst agent
      exact hcompanionNotDominant hagent
    rw [hquota]
    simp [quota, longAgents, m2Quota, hneCompanion]
  have hcardLower (agent : Fin 4) : q ≤ (allocation agent).card := by
    rw [hquota]
    simp [quota, longAgents, m2Quota]
  have hspecialLarge : ∀ item ∈ allocation special, IsLargeChore cost r special item := by
    intro item hitem
    exact hcostLarge special hspecialNotDominant item (halloc.1 special item hitem)
  have hcompanionLarge : ∀ item ∈ allocation companion,
      IsLargeChore cost r companion item := by
    intro item hitem
    exact hcostLarge companion hcompanionNotDominant item (halloc.1 companion item hitem)
  have hcompanionLargeForSpecial : ∀ item ∈ allocation companion,
      IsLargeChore cost r special item := by
    intro item hitem
    exact hcostLarge special hspecialNotDominant item (halloc.1 companion item hitem)
  have hspecialCost : additiveChoreCost cost special (allocation special) =
      ((q + 1 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation special) r
      (fun item hitem => hspecialLarge item hitem), hcardSpecial]
    simp only [nsmul_eq_mul]
  have hcompanionCost : additiveChoreCost cost companion (allocation companion) =
      (q : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost companion (allocation companion) r
      (fun item hitem => hcompanionLarge item hitem), hcardCompanion]
    simp only [nsmul_eq_mul]
  have hcompanionCostForSpecial : additiveChoreCost cost special (allocation companion) =
      (q : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation companion) r
      (fun item hitem => hcompanionLargeForSpecial item hitem), hcardCompanion]
    simp only [nsmul_eq_mul]
  refine ⟨allocation, halloc, ?_, hspecialLarge, ?_, ?_, ?_, ?_⟩
  · intro agent hneSpecial
    by_cases hagentCompanion : agent = companion
    · intro other
      subst agent
      have hotherLarge : ∀ item ∈ allocation other, cost companion item = r := by
        intro item hitem
        exact hcostLarge companion hcompanionNotDominant item (halloc.1 other item hitem)
      rw [hcompanionCost,
        additiveChoreCost_eq_card_nsmul_of_constant cost companion (allocation other) r
          hotherLarge]
      simp only [nsmul_eq_mul]
      have hcardReal : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      have henvyFree := mul_le_mul_of_nonneg_right hcardReal (by linarith : 0 ≤ r)
      linarith
    · intro other
      have hagentNotAuxiliary : agent ∉ auxiliary := by
        rw [hauxEq]
        simp [hneSpecial, hagentCompanion]
      have hagentDominant : agent ∈ dominant :=
        mem_dominant_of_not_auxiliary dominant auxiliary hdominant hauxiliary hdisjoint agent
          hagentNotAuxiliary
      have hcardAgent : (allocation agent).card = q + 1 :=
        hcardDominant agent hagentDominant
      have hagentCost : additiveChoreCost cost agent (allocation agent) = (q + 1 : ℕ) := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) 1
          (fun item hitem => hcostSmall agent hagentDominant item (halloc.1 agent item hitem)),
          hcardAgent]
        norm_num
      have hotherCost : additiveChoreCost cost agent (allocation other) =
          (allocation other).card := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation other) 1
          (fun item hitem => hcostSmall agent hagentDominant item (halloc.1 other item hitem))]
        norm_num
      rw [hagentCost, hotherCost]
      have hcardReal : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      push_cast
      linarith
  · intro other hneOther
    by_cases hotherSpecial : other = special
    · subst other
      exact le_rfl
    · have hotherNotAuxiliary : other ∉ auxiliary := by
        rw [hauxEq]
        simp [hotherSpecial, hneOther]
      have hotherDominant : other ∈ dominant :=
        mem_dominant_of_not_auxiliary dominant auxiliary hdominant hauxiliary hdisjoint other
          hotherNotAuxiliary
      have hotherCard : (allocation other).card = q + 1 :=
        hcardDominant other hotherDominant
      have hotherLargeForSpecial : ∀ item ∈ allocation other, cost special item = r := by
        intro item hitem
        exact hcostLarge special hspecialNotDominant item (halloc.1 other item hitem)
      rw [hspecialCost,
        additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation other) r
          hotherLargeForSpecial, hotherCard]
      simp only [nsmul_eq_mul]
      exact le_rfl
  · rw [hspecialCost, hcompanionCostForSpecial]
    push_cast
    ring_nf
    exact le_rfl
  · intro other
    by_cases hotherCompanion : other = companion
    · subst other
      exact le_rfl
    · have hotherLarge : ∀ item ∈ allocation other, cost companion item = r := by
        intro item hitem
        exact hcostLarge companion hcompanionNotDominant item (halloc.1 other item hitem)
      rw [hcompanionCost,
        additiveChoreCost_eq_card_nsmul_of_constant cost companion (allocation other) r
          hotherLarge]
      simp only [nsmul_eq_mul]
      have hcardReal : (q : ℝ) ≤ (allocation other).card := by
        exact_mod_cast hcardLower other
      exact mul_le_mul_of_nonneg_right hcardReal (by linarith)
  · intro agent
    by_cases hagent : agent = companion
    · subst agent
      simpa using hcardCompanion
    · rw [hquota]
      simp [quota, longAgents, m2Quota, hagent]

/-- The second exceptional shape has one auxiliary-small chore.  Giving it to
the companion leaves the chosen auxiliary endpoint all-large and confines the
large-removal comparison to that ordered pair. -/
private theorem exists_one_auxiliary_exceptional_controlled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (dominant auxiliary : Finset (Fin 4)) (q : ℕ)
    (exceptionalItem : Item) (special companion : Fin 4)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary)
    (hspecial : special ∈ auxiliary) (hcompanion : companion ∈ auxiliary)
    (hne : special ≠ companion)
    (hitem : exceptionalItem ∈ chores)
    (hitemType : smallAgentSet cost exceptionalItem = auxiliary)
    (houtsideType : ∀ item ∈ chores.erase exceptionalItem,
      smallAgentSet cost item = dominant)
    (houtsideCard : (chores.erase exceptionalItem).card = 4 * q + 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
        additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) ∧
      (∀ other, additiveChoreCost cost companion (allocation companion) ≤
        additiveChoreCost cost companion (allocation other)) ∧
      exceptionalItem ∈ allocation companion ∧
      ∀ agent, (allocation agent).card = q + 1 := by
  classical
  let outside : Finset Item := chores.erase exceptionalItem
  let longAgents : Finset (Fin 4) := Finset.univ.erase companion
  let quota := m2Quota q longAgents
  have hsum : Finset.univ.sum quota = outside.card := by
    rw [show quota = m2Quota q (Finset.univ.erase companion) by rfl,
      exceptional_quota_sum]
    simpa [outside] using houtsideCard.symm
  obtain ⟨outsideAllocation, houtsideAllocation, houtsideQuota⟩ :=
    existsAllocationOfQuota (Fin 4) Item outside quota hsum
  let singletonAllocation := allocateAllTo (Fin 4) Item companion ({exceptionalItem} : Finset Item)
  let allocation : Allocation (Fin 4) Item := fun agent =>
    outsideAllocation agent ∪ singletonAllocation agent
  have houtsideDisjoint : Disjoint outside ({exceptionalItem} : Finset Item) := by
    rw [Finset.disjoint_left]
    intro item houtside hsingleton
    have hneItem : item ≠ exceptionalItem := (Finset.mem_erase.mp houtside).1
    have heqItem : item = exceptionalItem := by simpa using hsingleton
    exact (hneItem heqItem).elim
  have houtsideUnion : outside ∪ ({exceptionalItem} : Finset Item) = chores := by
    ext item
    simp [outside, hitem]
  have hsingletonAllocation : IsAllocationOf singletonAllocation ({exceptionalItem} : Finset Item) :=
    isAllocationOf_allocateAllTo companion ({exceptionalItem} : Finset Item)
  have halloc : IsAllocationOf allocation chores := by
    have hcombined := isAllocationOf_union outsideAllocation singletonAllocation outside
      ({exceptionalItem} : Finset Item) houtsideDisjoint houtsideAllocation hsingletonAllocation
    simpa [allocation, houtsideUnion] using hcombined
  have hauxEq : auxiliary = {special, companion} :=
    auxiliary_eq_pair auxiliary special companion hauxiliary hspecial hcompanion hne
  have hspecialNotDominant : special ∉ dominant := by
    intro hspecialDominant
    exact (Finset.disjoint_left.mp hdisjoint hspecialDominant hspecial).elim
  have hcompanionNotDominant : companion ∉ dominant := by
    intro hcompanionDominant
    exact (Finset.disjoint_left.mp hdisjoint hcompanionDominant hcompanion).elim
  have hcostSmallOutside (agent : Fin 4) (hagent : agent ∈ dominant)
      (item : Item) (hitemOutside : item ∈ outside) : IsSmallChore cost agent item := by
    have hmem : agent ∈ smallAgentSet cost item := by
      simpa [outside, houtsideType item hitemOutside] using hagent
    simpa [smallAgentSet] using hmem
  have hcostLargeOutside (agent : Fin 4) (hagent : agent ∉ dominant)
      (item : Item) (hitemOutside : item ∈ outside) : IsLargeChore cost r agent item := by
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hagent
      have hmem : agent ∈ smallAgentSet cost item := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [outside, houtsideType item hitemOutside] using hmem
    · simpa [IsLargeChore] using hlarge
  have hitemSmall (agent : Fin 4) (hagent : agent ∈ auxiliary) :
      IsSmallChore cost agent exceptionalItem := by
    have hmem : agent ∈ smallAgentSet cost exceptionalItem := by
      simpa [hitemType] using hagent
    simpa [smallAgentSet] using hmem
  have hcardOutsideSpecial : (outsideAllocation special).card = q + 1 := by
    rw [houtsideQuota]
    simp [quota, longAgents, m2Quota, hne]
  have hcardOutsideCompanion : (outsideAllocation companion).card = q := by
    rw [houtsideQuota]
    simp [quota, longAgents, m2Quota]
  have hcardOutsideDominant (agent : Fin 4) (hagent : agent ∈ dominant) :
      (outsideAllocation agent).card = q + 1 := by
    have hneCompanion : agent ≠ companion := by
      intro heq
      subst agent
      exact hcompanionNotDominant hagent
    rw [houtsideQuota]
    simp [quota, longAgents, m2Quota, hneCompanion]
  have houtsideCardLower (agent : Fin 4) : q ≤ (outsideAllocation agent).card := by
    rw [houtsideQuota]
    simp [quota, longAgents, m2Quota]
  have houtsideNoItem (agent : Fin 4) : exceptionalItem ∉ outsideAllocation agent := by
    intro hmem
    have houtsideMem : exceptionalItem ∈ outside := houtsideAllocation.1 agent exceptionalItem hmem
    exact (Finset.mem_erase.mp houtsideMem).1 rfl
  have hsingletonSpecial : singletonAllocation special = ∅ := by
    simp [singletonAllocation, allocateAllTo, hne]
  have hsingletonDominant (agent : Fin 4) (hagent : agent ∈ dominant) :
      singletonAllocation agent = ∅ := by
    have hneCompanion : agent ≠ companion := by
      intro heq
      subst agent
      exact hcompanionNotDominant hagent
    simp [singletonAllocation, allocateAllTo, hneCompanion]
  have hcardSpecial : (allocation special).card = q + 1 := by
    simp only [allocation, hsingletonSpecial, Finset.union_empty]
    exact hcardOutsideSpecial
  have hcardCompanion : (allocation companion).card = q + 1 := by
    have hdisjointBundle : Disjoint (outsideAllocation companion)
        (singletonAllocation companion) := by
      simp [singletonAllocation, allocateAllTo, Finset.disjoint_singleton_right,
        houtsideNoItem companion]
    change (outsideAllocation companion ∪ singletonAllocation companion).card = q + 1
    rw [Finset.card_union_of_disjoint hdisjointBundle]
    simp [singletonAllocation, allocateAllTo, hcardOutsideCompanion]
  have hcardDominant (agent : Fin 4) (hagent : agent ∈ dominant) :
      (allocation agent).card = q + 1 := by
    change (outsideAllocation agent ∪ singletonAllocation agent).card = q + 1
    rw [hsingletonDominant agent hagent, Finset.union_empty]
    exact hcardOutsideDominant agent hagent
  have hcardNotCompanion (agent : Fin 4) (hagent : agent ≠ companion) :
      (allocation agent).card = q + 1 := by
    by_cases hagentSpecial : agent = special
    · subst agent
      exact hcardSpecial
    · have hagentNotAuxiliary : agent ∉ auxiliary := by
        rw [hauxEq]
        simp [hagentSpecial, hagent]
      have hagentDominant : agent ∈ dominant :=
        mem_dominant_of_not_auxiliary dominant auxiliary hdominant hauxiliary hdisjoint agent
          hagentNotAuxiliary
      exact hcardDominant agent hagentDominant
  have hitemLargeForDominant (agent : Fin 4) (hagent : agent ∈ dominant) :
      IsLargeChore cost r agent exceptionalItem := by
    rcases hcost agent exceptionalItem with hsmall | hlarge
    · exfalso
      apply (Finset.disjoint_left.mp hdisjoint hagent)
      have hmem : agent ∈ smallAgentSet cost exceptionalItem := by
        simpa [smallAgentSet, IsSmallChore] using hsmall
      simpa [hitemType] using hmem
    · simpa [IsLargeChore] using hlarge
  have hspecialLarge : ∀ item ∈ allocation special, IsLargeChore cost r special item := by
    intro item hitem
    have houtsideItem : item ∈ outsideAllocation special := by
      simpa [allocation, hsingletonSpecial] using hitem
    exact hcostLargeOutside special hspecialNotDominant item
      (houtsideAllocation.1 special item houtsideItem)
  have hspecialCost : additiveChoreCost cost special (allocation special) =
      ((q + 1 : ℕ) : ℝ) * r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation special) r
      (fun item hitem => hspecialLarge item hitem), hcardSpecial]
    simp only [nsmul_eq_mul]
  have hcompanionOutsideLargeForSpecial : ∀ item ∈ outsideAllocation companion,
      IsLargeChore cost r special item := by
    intro item hitem
    exact hcostLargeOutside special hspecialNotDominant item
      (houtsideAllocation.1 companion item hitem)
  have hcompanionCostForSpecial : additiveChoreCost cost special (allocation companion) =
      1 + (q : ℝ) * r := by
    have hdisjointBundle : Disjoint (outsideAllocation companion)
        (singletonAllocation companion) := by
      simp [singletonAllocation, allocateAllTo, Finset.disjoint_singleton_right,
        houtsideNoItem companion]
    change additiveChoreCost cost special
      (outsideAllocation companion ∪ singletonAllocation companion) = 1 + (q : ℝ) * r
    rw [additiveChoreCost_union cost special (outsideAllocation companion)
      (singletonAllocation companion) hdisjointBundle]
    have hsingletonCompanion : singletonAllocation companion = {exceptionalItem} := by
      simp [singletonAllocation, allocateAllTo]
    have hspecialItemCost : cost special exceptionalItem = 1 :=
      hitemSmall special hspecial
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost special (outsideAllocation companion) r
      (fun item hitem => hcompanionOutsideLargeForSpecial item hitem),
      hcardOutsideCompanion, hsingletonCompanion]
    simp [additiveChoreCost, hspecialItemCost, nsmul_eq_mul]
    ring
  have hcompanionCost : additiveChoreCost cost companion (allocation companion) =
      1 + (q : ℝ) * r := by
    have hdisjointBundle : Disjoint (outsideAllocation companion)
        (singletonAllocation companion) := by
      simp [singletonAllocation, allocateAllTo, Finset.disjoint_singleton_right,
        houtsideNoItem companion]
    change additiveChoreCost cost companion
      (outsideAllocation companion ∪ singletonAllocation companion) = 1 + (q : ℝ) * r
    rw [additiveChoreCost_union cost companion (outsideAllocation companion)
      (singletonAllocation companion) hdisjointBundle]
    have hsingletonCompanion : singletonAllocation companion = {exceptionalItem} := by
      simp [singletonAllocation, allocateAllTo]
    have hcompanionItemCost : cost companion exceptionalItem = 1 :=
      hitemSmall companion hcompanion
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost companion
      (outsideAllocation companion) r
      (fun item hitem => hcostLargeOutside companion hcompanionNotDominant item
        (houtsideAllocation.1 companion item hitem)),
      hcardOutsideCompanion, hsingletonCompanion]
    simp [additiveChoreCost, hcompanionItemCost, nsmul_eq_mul]
    ring
  refine ⟨allocation, halloc, ?_, hspecialLarge, ?_, ?_, ?_, ?_, ?_⟩
  · intro agent hneSpecial
    by_cases hagentCompanion : agent = companion
    · intro other
      subst agent
      by_cases hotherCompanion : other = companion
      · subst other
        rw [hcompanionCost]
        linarith
      · have hotherCard : (allocation other).card = q + 1 :=
          hcardNotCompanion other hotherCompanion
        have hsingletonOther : singletonAllocation other = ∅ := by
          simp [singletonAllocation, allocateAllTo, hotherCompanion]
        have hotherLarge : ∀ item ∈ allocation other, cost companion item = r := by
          intro item hitem
          have houtsideItem : item ∈ outsideAllocation other := by
            simpa [allocation, hsingletonOther] using hitem
          exact hcostLargeOutside companion hcompanionNotDominant item
            (houtsideAllocation.1 other item houtsideItem)
        rw [hcompanionCost,
          additiveChoreCost_eq_card_nsmul_of_constant cost companion (allocation other) r
            hotherLarge, hotherCard]
        simp only [nsmul_eq_mul]
        push_cast
        nlinarith
    · intro other
      have hagentNotAuxiliary : agent ∉ auxiliary := by
        rw [hauxEq]
        simp [hneSpecial, hagentCompanion]
      have hagentDominant : agent ∈ dominant :=
        mem_dominant_of_not_auxiliary dominant auxiliary hdominant hauxiliary hdisjoint agent
          hagentNotAuxiliary
      have hagentCost : additiveChoreCost cost agent (allocation agent) = (q + 1 : ℕ) := by
        rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation agent) 1
          (fun item hitem => by
            have houtsideItem : item ∈ outsideAllocation agent := by
              simpa [allocation, hsingletonDominant agent hagentDominant] using hitem
            exact hcostSmallOutside agent hagentDominant item
              (houtsideAllocation.1 agent item houtsideItem)),
          hcardDominant agent hagentDominant]
        norm_num
      by_cases hotherCompanion : other = companion
      · subst other
        have hdisjointBundle : Disjoint (outsideAllocation companion)
            (singletonAllocation companion) := by
          simp [singletonAllocation, allocateAllTo, Finset.disjoint_singleton_right,
            houtsideNoItem companion]
        have hcompanionCostForAgent : additiveChoreCost cost agent (allocation companion) =
            (q : ℝ) + r := by
          change additiveChoreCost cost agent
            (outsideAllocation companion ∪ singletonAllocation companion) = (q : ℝ) + r
          rw [additiveChoreCost_union cost agent (outsideAllocation companion)
            (singletonAllocation companion) hdisjointBundle]
          have hsingletonCompanion : singletonAllocation companion = {exceptionalItem} := by
            simp [singletonAllocation, allocateAllTo]
          have hitemCost : cost agent exceptionalItem = r :=
            hitemLargeForDominant agent hagentDominant
          rw [additiveChoreCost_eq_card_nsmul_of_constant cost agent
            (outsideAllocation companion) 1
            (fun item hitem => hcostSmallOutside agent hagentDominant item
              (houtsideAllocation.1 companion item hitem)),
            hcardOutsideCompanion, hsingletonCompanion]
          simp [additiveChoreCost, hitemCost, nsmul_eq_mul]
        rw [hagentCost, hcompanionCostForAgent]
        push_cast
        linarith
      · have hotherCard : (allocation other).card = q + 1 :=
          hcardNotCompanion other hotherCompanion
        have hsingletonOther : singletonAllocation other = ∅ := by
          simp [singletonAllocation, allocateAllTo, hotherCompanion]
        have hotherSmall : ∀ item ∈ allocation other, cost agent item = 1 := by
          intro item hitem
          have houtsideItem : item ∈ outsideAllocation other := by
            simpa [allocation, hsingletonOther] using hitem
          exact hcostSmallOutside agent hagentDominant item
            (houtsideAllocation.1 other item houtsideItem)
        rw [hagentCost,
          additiveChoreCost_eq_card_nsmul_of_constant cost agent (allocation other) 1
            hotherSmall, hotherCard]
        norm_num
  · intro other hneOther
    by_cases hotherSpecial : other = special
    · subst other
      exact le_rfl
    · have hotherNotAuxiliary : other ∉ auxiliary := by
        rw [hauxEq]
        simp [hotherSpecial, hneOther]
      have hotherDominant : other ∈ dominant :=
        mem_dominant_of_not_auxiliary dominant auxiliary hdominant hauxiliary hdisjoint other
          hotherNotAuxiliary
      have hotherCard : (allocation other).card = q + 1 :=
        hcardDominant other hotherDominant
      have hotherLargeForSpecial : ∀ item ∈ allocation other, cost special item = r := by
        intro item hitem
        have houtsideItem : item ∈ outsideAllocation other := by
          simpa [allocation, hsingletonDominant other hotherDominant] using hitem
        exact hcostLargeOutside special hspecialNotDominant item
          (houtsideAllocation.1 other item houtsideItem)
      rw [hspecialCost,
        additiveChoreCost_eq_card_nsmul_of_constant cost special (allocation other) r
          hotherLargeForSpecial, hotherCard]
      simp only [nsmul_eq_mul]
      exact le_rfl
  · rw [hspecialCost, hcompanionCostForSpecial]
    push_cast
    ring_nf
    linarith
  · intro other
    by_cases hotherCompanion : other = companion
    · subst other
      exact le_rfl
    · have hotherCard : (allocation other).card = q + 1 :=
        hcardNotCompanion other hotherCompanion
      have hsingletonOther : singletonAllocation other = ∅ := by
        simp [singletonAllocation, allocateAllTo, hotherCompanion]
      have hotherLarge : ∀ item ∈ allocation other, cost companion item = r := by
        intro item hitem
        have houtsideItem : item ∈ outsideAllocation other := by
          simpa [allocation, hsingletonOther] using hitem
        exact hcostLargeOutside companion hcompanionNotDominant item
          (houtsideAllocation.1 other item houtsideItem)
      rw [hcompanionCost,
        additiveChoreCost_eq_card_nsmul_of_constant cost companion (allocation other) r
          hotherLarge, hotherCard]
      simp only [nsmul_eq_mul]
      push_cast
      nlinarith
  · simp [allocation, singletonAllocation, allocateAllTo]
  · intro agent
    by_cases hagent : agent = companion
    · subst agent
      exact hcardCompanion
    · exact hcardNotCompanion agent hagent

/-- In either exceptional M2 configuration, either exceptional endpoint can be
chosen as the all-large endpoint whose only non-unit comparison is directed to
the other exceptional endpoint. -/
theorem existsExceptionalM2Allocation_controlled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (dominant auxiliary : Finset (Fin 4)) (q : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary)
    (hshape :
      ((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧ chores.card = 4 * q + 3) ∨
      (∃ exceptionalItem ∈ chores, smallAgentSet cost exceptionalItem = auxiliary ∧
        (∀ item ∈ chores.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
        (chores.erase exceptionalItem).card = 4 * q + 3))
    (special companion : Fin 4) (hspecial : special ∈ auxiliary)
    (hcompanion : companion ∈ auxiliary)
    (hne : special ≠ companion) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
          additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) := by
  rcases hshape with hfixed | hsingle
  · obtain ⟨htype, hcard⟩ := hfixed
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite, _hcards⟩ :=
      exists_fixed_exceptional_controlled Item r cost chores dominant auxiliary q special companion
        hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne htype hcard
    exact ⟨allocation, halloc, hunit, hlarge, haway, hcomparison⟩
  · obtain ⟨exceptionalItem, hitem, hitemType, houtsideType, houtsideCard⟩ := hsingle
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite, _hitem, _hcards⟩ :=
      exists_one_auxiliary_exceptional_controlled Item r cost chores dominant auxiliary q
        exceptionalItem special companion hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne
        hitem hitemType houtsideType houtsideCard
    exact ⟨allocation, halloc, hunit, hlarge, haway, hcomparison⟩

/-- The controlled exceptional certificates imply chore EFX for the same
allocation.  Unit slack handles every non-special agent because every
`(1,r)` chore costs at least one; the selected all-large agent uses the
displayed `r`-removal comparison only against the companion. -/
private theorem efx_of_controlled_exceptional_residue
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (allocation : Allocation (Fin 4) Item) (special companion : Fin 4)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hunit : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (allocation agent) - 1 ≤
        additiveChoreCost cost agent (allocation other))
    (hspecialLarge : ∀ item ∈ allocation special,
      IsLargeChore cost r special item)
    (hspecialAway : ∀ other, other ≠ companion →
      additiveChoreCost cost special (allocation special) ≤
        additiveChoreCost cost special (allocation other))
    (hspecialCompanion : additiveChoreCost cost special (allocation special) - r ≤
      additiveChoreCost cost special (allocation companion)) :
    EFXForChores (additiveChoreCost cost) allocation := by
  rw [efxForChores_iff_forall_doesNotStronglyEnvy]
  intro agent other
  by_cases hagent : agent = special
  · subst agent
    by_cases hother : other = companion
    · subst other
      right
      intro item hitem
      rw [additiveChoreCost_erase cost special (allocation special) item hitem]
      have hitemCost : cost special item = r := by
        simpa [IsLargeChore] using hspecialLarge item hitem
      rw [hitemCost]
      exact hspecialCompanion
    · right
      intro item hitem
      rw [additiveChoreCost_erase cost special (allocation special) item hitem]
      have hnonneg : 0 ≤ cost special item :=
        IsOneOrRChoreCost.nonneg cost r hcost (by linarith) special item
      linarith [hspecialAway other hother]
  · right
    intro item hitem
    rw [additiveChoreCost_erase cost agent (allocation agent) item hitem]
    have hcostLower : 1 ≤ cost agent item :=
      IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
    linarith [hunit agent hagent other]

/--
The two exceptional schedules in Lemma M2-properties(ii), with the source's
cardinality and designated-item information kept visible.  The caller chooses
either auxiliary endpoint as `special`; that endpoint is the only one allowed
to rely on a large-item removal.
-/
theorem existsExceptionalM2Allocation_sourceSchedule
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (dominant auxiliary : Finset (Fin 4)) (q : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary)
    (hshape :
      ((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧ chores.card = 4 * q + 3) ∨
      (∃ exceptionalItem ∈ chores, smallAgentSet cost exceptionalItem = auxiliary ∧
        (∀ item ∈ chores.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
        (chores.erase exceptionalItem).card = 4 * q + 3))
    (special companion : Fin 4) (hspecial : special ∈ auxiliary)
    (hcompanion : companion ∈ auxiliary) (hne : special ≠ companion) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      EFXForChores (additiveChoreCost cost) allocation ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
          additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) ∧
      (((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧ chores.card = 4 * q + 3 ∧
          (∀ agent, (allocation agent).card = if agent = companion then q else q + 1)) ∨
        (∃ exceptionalItem ∈ chores,
          smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ chores.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
          (chores.erase exceptionalItem).card = 4 * q + 3 ∧
          exceptionalItem ∈ allocation companion ∧
          (∀ agent, (allocation agent).card = q + 1))) := by
  rcases hshape with hfixed | hsingle
  · obtain ⟨htype, hcard⟩ := hfixed
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, _hfavorite, hcards⟩ :=
      exists_fixed_exceptional_controlled Item r cost chores dominant auxiliary q special companion
        hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne htype hcard
    refine ⟨allocation, halloc, ?_, hunit, hlarge, haway, hcomparison, Or.inl ?_⟩
    · exact efx_of_controlled_exceptional_residue Item r cost allocation special companion
        hr hcost hunit hlarge haway hcomparison
    · exact ⟨htype, hcard, hcards⟩
  · obtain ⟨exceptionalItem, hitem, hitemType, houtsideType, houtsideCard⟩ := hsingle
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, _hfavorite, hassigned,
      hcards⟩ :=
      exists_one_auxiliary_exceptional_controlled Item r cost chores dominant auxiliary q
        exceptionalItem special companion hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne
        hitem hitemType houtsideType houtsideCard
    refine ⟨allocation, halloc, ?_, hunit, hlarge, haway, hcomparison, Or.inr ?_⟩
    · exact efx_of_controlled_exceptional_residue Item r cost allocation special companion
        hr hcost hunit hlarge haway hcomparison
    · exact ⟨exceptionalItem, hitem, hitemType, houtsideType, houtsideCard, hassigned, hcards⟩

/-- The controlled exceptional allocation can simultaneously make the
companion residual-favorite.  This is the strengthened source witness used
when the short B.4.2(a) prefix endpoint is that companion. -/
theorem existsExceptionalM2Allocation_controlled_with_companionFavorite
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (dominant auxiliary : Finset (Fin 4)) (q : ℕ)
    (hr : 1 < r) (hcost : IsOneOrRChoreCost cost r)
    (hdominant : dominant.card = 2) (hauxiliary : auxiliary.card = 2)
    (hdisjoint : Disjoint dominant auxiliary)
    (hshape :
      ((∀ item ∈ chores, smallAgentSet cost item = dominant) ∧ chores.card = 4 * q + 3) ∨
      (∃ exceptionalItem ∈ chores, smallAgentSet cost exceptionalItem = auxiliary ∧
        (∀ item ∈ chores.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
        (chores.erase exceptionalItem).card = 4 * q + 3))
    (special companion : Fin 4) (hspecial : special ∈ auxiliary)
    (hcompanion : companion ∈ auxiliary)
    (hne : special ≠ companion) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧
      (∀ agent, agent ≠ special → ∀ other,
        additiveChoreCost cost agent (allocation agent) - 1 ≤
          additiveChoreCost cost agent (allocation other)) ∧
      (∀ item ∈ allocation special, IsLargeChore cost r special item) ∧
      (∀ other, other ≠ companion →
        additiveChoreCost cost special (allocation special) ≤
          additiveChoreCost cost special (allocation other)) ∧
      additiveChoreCost cost special (allocation special) - r ≤
        additiveChoreCost cost special (allocation companion) ∧
      ∀ other, additiveChoreCost cost companion (allocation companion) ≤
        additiveChoreCost cost companion (allocation other) := by
  rcases hshape with hfixed | hsingle
  · obtain ⟨htype, hcard⟩ := hfixed
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite, _hcards⟩ :=
      exists_fixed_exceptional_controlled Item r cost chores dominant auxiliary q special companion
        hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne htype hcard
    exact ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite⟩
  · obtain ⟨exceptionalItem, hitem, hitemType, houtsideType, houtsideCard⟩ := hsingle
    obtain ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite, _hitem, _hcards⟩ :=
      exists_one_auxiliary_exceptional_controlled Item r cost chores dominant auxiliary q
        exceptionalItem special companion hr hcost hdominant hauxiliary hdisjoint hspecial hcompanion hne
        hitem hitemType houtsideType houtsideCard
    exact ⟨allocation, halloc, hunit, hlarge, haway, hcomparison, hfavorite⟩

/- Composition specialized to the exceptional M2 allocation.  Every
non-special residual comparison has unit slack; the sole large-removal
comparison is covered either because the combined special bundle is all large
or because the left allocation supplies an `r - 1` advantage. -/
/-- The EFX composition calculation for a controlled exceptional M₂ residue.

This is the common proof kernel behind the source's exceptional-combination
arguments.  It is public because the `b = 0` M₀₁--M₂ branch has no gap-filling
items, but needs exactly the same all-large-or-`r - 1` prefix alternative. -/
theorem efx_union_of_controlled_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (left right : Allocation (Fin 4) Item) (special companion : Fin 4)
    (hdisjoint : ∀ agent, Disjoint (left agent) (right agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleft : EnvyFreeForChores (additiveChoreCost cost) left)
    (hunit : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (right agent) - 1 ≤
        additiveChoreCost cost agent (right other))
    (hspecialLarge : ∀ item ∈ right special, IsLargeChore cost r special item)
    (hspecialAway : ∀ other, other ≠ companion →
      additiveChoreCost cost special (right special) ≤
        additiveChoreCost cost special (right other))
    (hspecialCompanion : additiveChoreCost cost special (right special) - r ≤
      additiveChoreCost cost special (right companion))
    (hspecialLeft :
      (∀ item ∈ left special, IsLargeChore cost r special item) ∨
      additiveChoreCost cost special (left special) + (r - 1) ≤
        additiveChoreCost cost special (left companion)) :
    EFXForChores (additiveChoreCost cost) (fun agent => left agent ∪ right agent) := by
  apply efxForChores_union_of_cost_gap cost left right hdisjoint
  intro agent other hnonempty
  have hminimumOne : 1 ≤
      ((left agent ∪ right agent).image (cost agent)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
    rw [← hvalueEq]
    exact hcostLower agent item
  have hleftGap : additiveChoreCost cost agent (left agent) -
      additiveChoreCost cost agent (left other) ≤ 0 := by
    linarith [hleft agent other]
  by_cases hagent : agent = special
  · subst agent
    by_cases hother : other = companion
    · subst other
      rcases hspecialLeft with hleftLarge | hleftAdvantage
      · have hminimumLarge : r ≤
            ((left special ∪ right special).image (cost special)).min'
              (Finset.image_nonempty.mpr hnonempty) := by
          apply Finset.le_min'
          intro value hvalue
          obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
          rw [← hvalueEq]
          rcases Finset.mem_union.mp hitem with hleftItem | hrightItem
          · exact le_of_eq (hleftLarge item hleftItem).symm
          · exact le_of_eq (hspecialLarge item hrightItem).symm
        linarith [hleft special companion, hspecialCompanion, hminimumLarge]
      · linarith [hleftAdvantage, hspecialCompanion, hminimumOne]
    · linarith [hleft special other, hspecialAway other hother, hminimumOne]
  · linarith [hleftGap, hunit agent hagent other, hminimumOne]

/-- A controlled exceptional residue also composes with a prefix whose one
short bundle has one-small-item slack.  The short residual bundle must be no
more costly than the other residual bundles; this is the round-robin invariant
used when gap-filling items were assigned to the short endpoint. -/
theorem efx_union_of_short_unit_slack_and_controlled_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (left right : Allocation (Fin 4) Item) (short special companion : Fin 4)
    (hshortNeSpecial : short ≠ special) (hshortNeCompanion : short ≠ companion)
    (hdisjoint : ∀ agent, Disjoint (left agent) (right agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleftShort : ∀ other,
      additiveChoreCost cost short (left short) ≤
        additiveChoreCost cost short (left other))
    (hleftOther : ∀ agent, agent ≠ short → ∀ other, other ≠ short →
      additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left other))
    (hleftToShort : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left short) + 1)
    (hrightShortDominates : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (right agent) ≤
        additiveChoreCost cost agent (right short))
    (hunit : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (right agent) - 1 ≤
        additiveChoreCost cost agent (right other))
    (hspecialLarge : ∀ item ∈ right special, IsLargeChore cost r special item)
    (hspecialAway : ∀ other, other ≠ companion →
      additiveChoreCost cost special (right special) ≤
        additiveChoreCost cost special (right other))
    (hspecialCompanion : additiveChoreCost cost special (right special) - r ≤
      additiveChoreCost cost special (right companion))
    (hspecialLeft :
      (∀ item ∈ left special, IsLargeChore cost r special item) ∨
      additiveChoreCost cost special (left special) + (r - 1) ≤
        additiveChoreCost cost special (left companion)) :
    EFXForChores (additiveChoreCost cost) (fun agent => left agent ∪ right agent) := by
  apply efxForChores_union_of_cost_gap cost left right hdisjoint
  intro agent other hnonempty
  have hminimumOne : 1 ≤
      ((left agent ∪ right agent).image (cost agent)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
    rw [← hvalueEq]
    exact hcostLower agent item
  by_cases hagentShort : agent = short
  · subst agent
    linarith [hleftShort other, hunit short hshortNeSpecial other, hminimumOne]
  by_cases hagentSpecial : agent = special
  · subst agent
    by_cases hotherCompanion : other = companion
    · subst other
      rcases hspecialLeft with hleftLarge | hleftAdvantage
      · have hminimumLarge : r ≤
            ((left special ∪ right special).image (cost special)).min'
              (Finset.image_nonempty.mpr hnonempty) := by
          apply Finset.le_min'
          intro value hvalue
          obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
          rw [← hvalueEq]
          rcases Finset.mem_union.mp hitem with hleftItem | hrightItem
          · exact le_of_eq (hleftLarge item hleftItem).symm
          · exact le_of_eq (hspecialLarge item hrightItem).symm
        linarith [hleftOther special (by simpa using hshortNeSpecial.symm)
          companion (by simpa using hshortNeCompanion.symm), hspecialCompanion,
          hminimumLarge]
      · linarith [hleftAdvantage, hspecialCompanion, hminimumOne]
    · by_cases hotherShort : other = short
      · subst other
        linarith [hleftToShort special (by simpa using hshortNeSpecial.symm),
          hspecialAway short hshortNeCompanion, hminimumOne]
      · linarith [hleftOther special (by simpa using hshortNeSpecial.symm)
          other hotherShort, hspecialAway other hotherCompanion, hminimumOne]
  · by_cases hotherShort : other = short
    · subst other
      linarith [hleftToShort agent hagentShort,
        hrightShortDominates agent hagentShort, hminimumOne]
    · linarith [hleftOther agent hagentShort other hotherShort,
        hunit agent hagentSpecial other, hminimumOne]

/-- The B.4.2(a) exceptional composition.  The short prefix endpoint is also
the companion of the controlled exceptional residue: its residual-favorite
property absorbs the prefix's one-small-item slack, while the special endpoint
uses either an all-large bundle or the source's `r - 1` advantage. -/
theorem efx_union_of_short_unit_slack_and_controlled_exceptional_with_favorite
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (left right : Allocation (Fin 4) Item) (short special : Fin 4)
    (hshortNeSpecial : short ≠ special)
    (hdisjoint : ∀ agent, Disjoint (left agent) (right agent))
    (hcostLower : ∀ agent item, 1 ≤ cost agent item)
    (hleftShort : ∀ other,
      additiveChoreCost cost short (left short) - 1 ≤
        additiveChoreCost cost short (left other))
    (hleftOther : ∀ agent, agent ≠ short → ∀ other, other ≠ short →
      additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left other))
    (hleftToShort : ∀ agent, agent ≠ short →
      additiveChoreCost cost agent (left agent) ≤
        additiveChoreCost cost agent (left short))
    (hrightFavorite : ∀ other,
      additiveChoreCost cost short (right short) ≤
        additiveChoreCost cost short (right other))
    (hunit : ∀ agent, agent ≠ special → ∀ other,
      additiveChoreCost cost agent (right agent) - 1 ≤
        additiveChoreCost cost agent (right other))
    (hspecialLarge : ∀ item ∈ right special, IsLargeChore cost r special item)
    (hspecialAway : ∀ other, other ≠ short →
      additiveChoreCost cost special (right special) ≤
        additiveChoreCost cost special (right other))
    (hspecialCompanion : additiveChoreCost cost special (right special) - r ≤
      additiveChoreCost cost special (right short))
    (hspecialLeft :
      (∀ item ∈ left special, IsLargeChore cost r special item) ∨
      additiveChoreCost cost special (left special) + (r - 1) ≤
        additiveChoreCost cost special (left short)) :
    EFXForChores (additiveChoreCost cost) (fun agent => left agent ∪ right agent) := by
  apply efxForChores_union_of_cost_gap cost left right hdisjoint
  intro agent other hnonempty
  have hminimumOne : 1 ≤
      ((left agent ∪ right agent).image (cost agent)).min'
        (Finset.image_nonempty.mpr hnonempty) := by
    apply Finset.le_min'
    intro value hvalue
    obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
    rw [← hvalueEq]
    exact hcostLower agent item
  by_cases hagentShort : agent = short
  · subst agent
    linarith [hleftShort other, hrightFavorite other, hminimumOne]
  by_cases hagentSpecial : agent = special
  · subst agent
    by_cases hotherShort : other = short
    · subst other
      rcases hspecialLeft with hleftLarge | hleftAdvantage
      · have hminimumLarge : r ≤
            ((left special ∪ right special).image (cost special)).min'
              (Finset.image_nonempty.mpr hnonempty) := by
          apply Finset.le_min'
          intro value hvalue
          obtain ⟨item, hitem, hvalueEq⟩ := Finset.mem_image.mp hvalue
          rw [← hvalueEq]
          rcases Finset.mem_union.mp hitem with hleftItem | hrightItem
          · exact le_of_eq (hleftLarge item hleftItem).symm
          · exact le_of_eq (hspecialLarge item hrightItem).symm
        linarith [hleftToShort special hshortNeSpecial.symm, hspecialCompanion,
          hminimumLarge]
      · linarith [hleftAdvantage, hspecialCompanion, hminimumOne]
    · linarith [hleftOther special hshortNeSpecial.symm other hotherShort,
        hspecialAway other hotherShort, hminimumOne]
  · by_cases hotherShort : other = short
    · subst other
      linarith [hleftToShort agent hagentShort,
        hunit agent hagentSpecial short, hminimumOne]
    · linarith [hleftOther agent hagentShort other hotherShort,
        hunit agent hagentSpecial other, hminimumOne]

/-- The paper's exceptional-residue concatenation lemma.  The explicit
`IsSmallForAtMostOne` hypothesis is the source-to-model content of the
prefix name `M₀₁`: it is needed precisely for the canonical `r - 1`
cross-bundle advantage. -/
theorem exceptional_residue_combination_proof
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores gapChores residueChores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation gap : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hgapResidue : Disjoint gapChores residueChores)
    (hgapResidueUnion : gapChores ∪ residueChores = m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (_hquota : ∀ agent, quota agent = a ∨ quota agent = a + 1)
    (hgapAllocation : IsAllocationOf gap gapChores)
    (hgapShort : ∀ agent, quota agent ≠ a → gap agent = ∅)
    (hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent))
    (exceptionalI exceptionalJ : Fin 4)
    (hexceptional : ∃ dominant auxiliary : Finset (Fin 4), ∃ q : ℕ,
      dominant.card = 2 ∧ auxiliary.card = 2 ∧ Disjoint dominant auxiliary ∧
      exceptionalI ∈ auxiliary ∧ exceptionalJ ∈ auxiliary ∧
      (((∀ item ∈ residueChores, smallAgentSet cost item = dominant) ∧
          residueChores.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ residueChores,
          smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ residueChores.erase exceptionalItem,
            smallAgentSet cost item = dominant) ∧
          (residueChores.erase exceptionalItem).card = 4 * q + 3)))
    (hij : exceptionalI ≠ exceptionalJ)
    (hquotaI : quota exceptionalI = a + 1)
    (hquotaJ : quota exceptionalJ = a + 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
      EFXForChores (additiveChoreCost cost) allocation := by
  classical
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
      hcanonical.isAllocationOf hgapAllocation
  have hprefixResidue : Disjoint prefixChores residueChores :=
    hprefixM2.mono_right hresidueSubset
  have hleftResidue : Disjoint (prefixChores ∪ gapChores) residueChores := by
    rw [Finset.disjoint_left]
    intro item hleftItem hresidueItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · exact (Finset.disjoint_left.mp hprefixResidue hprefixItem hresidueItem).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgapItem hresidueItem).elim
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint,
    hmemI, hmemJ, hshape⟩
  have hgapI : gap exceptionalI = ∅ := by
    apply hgapShort exceptionalI
    rw [hquotaI]
    omega
  have hgapJ : gap exceptionalJ = ∅ := by
    apply hgapShort exceptionalJ
    rw [hquotaJ]
    omega
  have hrightDisjoint (right : Allocation (Fin 4) Item)
      (hright : IsAllocationOf right residueChores) :
      ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftItem hrightItem
    have hrightResidue : item ∈ residueChores := hright.1 agent item hrightItem
    rcases Finset.mem_union.mp hleftItem with hprefixItem | hgapItem
    · have hprefixGood : item ∈ prefixChores := hcanonical.isAllocationOf.1 agent item hprefixItem
      exact (Finset.disjoint_left.mp hprefixResidue hprefixGood hrightResidue).elim
    · have hgapGood : item ∈ gapChores := hgapAllocation.1 agent item hgapItem
      exact (Finset.disjoint_left.mp hgapResidue hgapGood hrightResidue).elim
  have hfinalAllocation (right : Allocation (Fin 4) Item)
      (hright : IsAllocationOf right residueChores)
      (hbundles : ∀ agent, Disjoint (left agent) (right agent)) :
      IsAllocationOf (fun agent => left agent ∪ right agent) (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right (prefixChores ∪ gapChores) residueChores
      hleftResidue hleftAllocation hright
    have hgoods : (prefixChores ∪ gapChores) ∪ residueChores = prefixChores ∪ m2Chores := by
      rw [← hgapResidueUnion]
      ac_rfl
    simpa [hgoods] using hcombined
  by_cases hsmallI : ∃ item ∈ prefixAllocation exceptionalI,
      IsSmallChore cost exceptionalI item
  · by_cases hsmallJ : ∃ item ∈ prefixAllocation exceptionalJ,
        IsSmallChore cost exceptionalJ item
    · obtain ⟨right, hright, hunit, hlarge, haway, hcompanion⟩ :=
        existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q (by linarith) hcost
          hdominant hauxiliary hdisjoint hshape exceptionalI exceptionalJ hmemI hmemJ hij
      have hadvantagePrefix : additiveChoreCost cost exceptionalI
          (prefixAllocation exceptionalI) + (r - 1) ≤
          additiveChoreCost cost exceptionalI (prefixAllocation exceptionalJ) :=
        hcanonical.cross_cost_advantage_of_ownSmall cost r prefixChores quota prefixAllocation
          hcost (by linarith) hprefixSmall exceptionalI exceptionalJ hij
          (by rw [hquotaI, hquotaJ]) hsmallI hsmallJ
      have hadvantageLeft : additiveChoreCost cost exceptionalI (left exceptionalI) + (r - 1) ≤
          additiveChoreCost cost exceptionalI (left exceptionalJ) := by
        simpa [left, hgapI, hgapJ] using hadvantagePrefix
      refine ⟨fun agent => left agent ∪ right agent,
        hfinalAllocation right hright (hrightDisjoint right hright), ?_⟩
      exact efx_union_of_controlled_exceptional Item r cost left right exceptionalI exceptionalJ
        (hrightDisjoint right hright) hcostLower hleftEnvyFree hunit hlarge haway hcompanion
        (Or.inr hadvantageLeft)
    · obtain ⟨right, hright, hunit, hlarge, haway, hcompanion⟩ :=
        existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q (by linarith) hcost
          hdominant hauxiliary hdisjoint hshape exceptionalJ exceptionalI hmemJ hmemI hij.symm
      have hleftLarge : ∀ item ∈ left exceptionalJ,
          IsLargeChore cost r exceptionalJ item := by
        intro item hitem
        rcases Finset.mem_union.mp hitem with hprefixItem | hgapItem
        · rcases hcost exceptionalJ item with hsmall | hlarge
          · exact (hsmallJ ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmall⟩).elim
          · simpa [IsLargeChore] using hlarge
        · rw [hgapJ] at hgapItem
          simp at hgapItem
      refine ⟨fun agent => left agent ∪ right agent,
        hfinalAllocation right hright (hrightDisjoint right hright), ?_⟩
      exact efx_union_of_controlled_exceptional Item r cost left right exceptionalJ exceptionalI
        (hrightDisjoint right hright) hcostLower hleftEnvyFree hunit hlarge haway hcompanion
        (Or.inl hleftLarge)
  · obtain ⟨right, hright, hunit, hlarge, haway, hcompanion⟩ :=
      existsExceptionalM2Allocation_controlled Item r cost residueChores dominant auxiliary q (by linarith) hcost
        hdominant hauxiliary hdisjoint hshape exceptionalI exceptionalJ hmemI hmemJ hij
    have hleftLarge : ∀ item ∈ left exceptionalI,
        IsLargeChore cost r exceptionalI item := by
      intro item hitem
      rcases Finset.mem_union.mp hitem with hprefixItem | hgapItem
      · rcases hcost exceptionalI item with hsmall | hlarge
        · exact (hsmallI ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmall⟩).elim
        · simpa [IsLargeChore] using hlarge
      · rw [hgapI] at hgapItem
        simp at hgapItem
    refine ⟨fun agent => left agent ∪ right agent,
      hfinalAllocation right hright (hrightDisjoint right hright), ?_⟩
    exact efx_union_of_controlled_exceptional Item r cost left right exceptionalI exceptionalJ
      (hrightDisjoint right hright) hcostLower hleftEnvyFree hunit hlarge haway hcompanion
      (Or.inl hleftLarge)

end HT26EFXChores
