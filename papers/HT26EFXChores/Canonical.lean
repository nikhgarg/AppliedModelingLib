import HT26EFXChores.M2Orientation

/-!
# Canonical allocations of the M01 pool

This module supplies the finite allocation bridge used by the paper's
canonical-prefix argument.  When every chore is small for at most one agent,
the uniquely small chores selected for distinct agents are disjoint; the
remaining chores can therefore be filled to arbitrary residual quotas.

Source: `EFXadditivechores.tex`, lines 730--770.
-/

namespace HT26EFXChores

open scoped BigOperators
open AppliedModelingLib.FairDivision

/-- A quota vector of the full chore-pool size admits a canonical allocation
whenever every chore is small for at most one agent.  First reserve the
maximum permitted number of own-small chores for each agent, then allocate the
disjoint residual pool to the residual quotas. -/
theorem existsCanonicalSmallChoreAllocation
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (quota : Fin 4 → ℕ)
    (hsum : Finset.univ.sum quota = chores.card)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsCanonicalSmallChoreAllocation cost chores quota allocation := by
  classical
  let own : Fin 4 → Finset Item := fun agent => ownSmallChoreSet cost chores agent
  have hchoose : ∀ agent : Fin 4, ∃ selected ⊆ own agent,
      selected.card = min (quota agent) (own agent).card := by
    intro agent
    exact Finset.exists_subset_card_eq (Nat.min_le_right _ _)
  choose selected hselectedSubset hselectedCard using hchoose
  let selectedGoods : Finset Item := (Finset.univ : Finset (Fin 4)).biUnion selected
  have hselectedDisjoint : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      selected := by
    intro first _ second _ hne
    change Disjoint (selected first) (selected second)
    rw [Finset.disjoint_left]
    intro item hfirst hsecond
    have hfirstOwn : item ∈ own first := hselectedSubset first hfirst
    have hsecondOwn : item ∈ own second := hselectedSubset second hsecond
    have hitem : item ∈ chores := (Finset.mem_filter.mp hfirstOwn).1
    have hfirstSmall : first ∈ smallAgentSet cost item := by
      simpa [own, ownSmallChoreSet, smallAgentSet, IsSmallChore] using
        (Finset.mem_filter.mp hfirstOwn).2
    have hsecondSmall : second ∈ smallAgentSet cost item := by
      simpa [own, ownSmallChoreSet, smallAgentSet, IsSmallChore] using
        (Finset.mem_filter.mp hsecondOwn).2
    have hsubset : ({first, second} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact hfirstSmall
      · exact hsecondSmall
    have hcard := Finset.card_le_card hsubset
    have hpairCard : ({first, second} : Finset (Fin 4)).card = 2 := by simp [hne]
    have hsmallCard := hsmall item hitem
    change (smallAgentSet cost item).card ≤ 1 at hsmallCard
    omega
  have hselectedGoodsSubset : selectedGoods ⊆ chores := by
    intro item hitem
    obtain ⟨agent, _, hselected⟩ := Finset.mem_biUnion.mp hitem
    exact (Finset.mem_filter.mp (hselectedSubset agent hselected)).1
  let selectedAllocation : Allocation (Fin 4) Item := fun agent => selected agent
  have hselectedAllocation : IsAllocationOf selectedAllocation selectedGoods := by
    constructor
    · intro agent item hitem
      exact Finset.mem_biUnion.mpr ⟨agent, Finset.mem_univ _, hitem⟩
    · intro item hitem
      obtain ⟨agent, _, hagent⟩ := Finset.mem_biUnion.mp hitem
      refine ⟨agent, hagent, ?_⟩
      intro other hother
      by_cases hEq : other = agent
      · exact hEq
      · exact False.elim ((Finset.disjoint_left.mp
          (hselectedDisjoint (Finset.mem_univ other) (Finset.mem_univ agent) hEq)) hother hagent)
  have hselectedCardSum : Finset.univ.sum (fun agent => (selected agent).card) =
      selectedGoods.card := by
    change ∑ agent ∈ (Finset.univ : Finset (Fin 4)), (selected agent).card = selectedGoods.card
    rw [← Finset.card_biUnion hselectedDisjoint]
  have hselectedLeQuota : ∀ agent, (selected agent).card ≤ quota agent := by
    intro agent
    rw [hselectedCard]
    exact Nat.min_le_left _ _
  let residualGoods : Finset Item := chores \ selectedGoods
  let residualQuota : Fin 4 → ℕ := fun agent => quota agent - (selected agent).card
  have hresidualSum : Finset.univ.sum residualQuota = residualGoods.card := by
    change (∑ agent ∈ (Finset.univ : Finset (Fin 4)),
        (quota agent - (selected agent).card)) = (chores \ selectedGoods).card
    rw [Finset.sum_tsub_distrib _ (by
      intro agent _
      exact hselectedLeQuota agent), hsum, hselectedCardSum,
      Finset.card_sdiff_of_subset hselectedGoodsSubset]
  obtain ⟨residualAllocation, hresidualAllocation, hresidualCard⟩ :=
    existsAllocationOfQuota (Fin 4) Item residualGoods residualQuota hresidualSum
  let allocation : Allocation (Fin 4) Item := fun agent =>
    selectedAllocation agent ∪ residualAllocation agent
  have hgoodsDisjoint : Disjoint selectedGoods residualGoods := by
    change Disjoint selectedGoods (chores \ selectedGoods)
    exact Finset.disjoint_sdiff
  have hallocation : IsAllocationOf allocation chores := by
    have hunion : selectedGoods ∪ residualGoods = chores := by
      change selectedGoods ∪ (chores \ selectedGoods) = chores
      exact Finset.union_sdiff_of_subset hselectedGoodsSubset
    rw [← hunion]
    exact isAllocationOf_union selectedAllocation residualAllocation selectedGoods residualGoods
      hgoodsDisjoint hselectedAllocation hresidualAllocation
  refine ⟨allocation, hallocation, ?_⟩
  intro agent
  have hselectedResidualDisjoint : Disjoint (selectedAllocation agent)
      (residualAllocation agent) := by
    apply Disjoint.mono
    · intro item hitem
      exact Finset.mem_biUnion.mpr ⟨agent, Finset.mem_univ _, hitem⟩
    · intro item hitem
      exact hresidualAllocation.1 agent item hitem
    · exact hgoodsDisjoint
  constructor
  · change (selectedAllocation agent ∪ residualAllocation agent).card = quota agent
    rw [Finset.card_union_of_disjoint hselectedResidualDisjoint, hresidualCard agent]
    change (selected agent).card + (quota agent - (selected agent).card) = quota agent
    exact Nat.add_sub_of_le (hselectedLeQuota agent)
  · by_cases hquotaSmall : quota agent ≤ (own agent).card
    · have hselectedFull : (selected agent).card = quota agent := by
        rw [hselectedCard, Nat.min_eq_left hquotaSmall]
      have hresidualZero : residualQuota agent = 0 := by
        change quota agent - (selected agent).card = 0
        omega
      have hresidualEmpty : residualAllocation agent = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [hresidualCard]
        exact hresidualZero
      have hallocationEq : allocation agent = selected agent := by
        simp [allocation, selectedAllocation, hresidualEmpty]
      have hselectedOwn : selected agent ⊆ ownSmallChoreSet cost (selected agent) agent := by
        intro item hitem
        have hown := hselectedSubset agent hitem
        exact Finset.mem_filter.mpr ⟨hitem, (Finset.mem_filter.mp hown).2⟩
      have hsmallEq : ownSmallChoreSet cost (selected agent) agent = selected agent := by
        apply Finset.Subset.antisymm
        · intro item hitem
          exact (Finset.mem_filter.mp hitem).1
        · exact hselectedOwn
      rw [hallocationEq, hsmallEq, hselectedCard]
    · have hsmallQuota : (own agent).card ≤ quota agent := by omega
      have hselectedEqOwn : selected agent = own agent := by
        apply Finset.eq_of_subset_of_card_le (hselectedSubset agent)
        rw [hselectedCard, Nat.min_eq_right hsmallQuota]
      have hresidualNoOwn : Disjoint (residualAllocation agent)
          (ownSmallChoreSet cost chores agent) := by
        apply Disjoint.mono
          (by
            intro item hitem
            exact hresidualAllocation.1 agent item hitem)
          (by
            intro item hitem
            have hselected : item ∈ selected agent := by
              simpa [own, ← hselectedEqOwn] using hitem
            exact Finset.mem_biUnion.mpr ⟨agent, Finset.mem_univ _, hselected⟩)
        exact hgoodsDisjoint.symm
      have hsmallUnion : ownSmallChoreSet cost (allocation agent) agent = selected agent := by
        apply Finset.eq_of_subset_of_card_le
        · intro item hitem
          have hitemAllocation : item ∈ allocation agent := (Finset.mem_filter.mp hitem).1
          rcases Finset.mem_union.mp hitemAllocation with hselected | hresidual
          · exact hselected
          · exfalso
            apply (Finset.disjoint_left.mp hresidualNoOwn hresidual)
            have hsmallItem : IsSmallChore cost agent item :=
              (Finset.mem_filter.mp hitem).2
            simp [ownSmallChoreSet]
            exact ⟨hallocation.1 agent item hitemAllocation, hsmallItem⟩
        · exact Finset.card_le_card (by
            intro item hitem
            exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hitem,
              (Finset.mem_filter.mp (hselectedSubset agent hitem)).2⟩)
      rw [hsmallUnion, hselectedCard, Nat.min_eq_right hsmallQuota]

/-- The fairness half of the paper's canonical-prefix lemma.  Canonical
allocations with adjacent quotas are EFX; if the pool size is divisible by
four, feasibility forces every quota to be equal and the allocation is
envy-free. -/
theorem canonicalSmallChoreAllocation_fair
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a b : ℕ)
    (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r) (hb : b ≤ 3)
    (hchores : chores.card = 4 * a + b)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    (∀ quota allocation, (∀ agent, quota agent = a ∨ quota agent = a + 1) →
      IsCanonicalSmallChoreAllocation cost chores quota allocation →
        EFXForChores (additiveChoreCost cost) allocation) ∧
    (b = 0 → ∀ quota allocation, (∀ agent, quota agent = a) →
      IsCanonicalSmallChoreAllocation cost chores quota allocation →
        EnvyFreeForChores (additiveChoreCost cost) allocation) := by
  constructor
  · intro quota allocation hquota hcanonical
    apply IsCanonicalSmallChoreAllocation.efxForChores cost r chores quota allocation hcost hr
      (by
        intro first second
        rcases hquota first with hfirst | hfirst <;>
          rcases hquota second with hsecond | hsecond <;> omega)
      hcanonical
  · intro hzero quota allocation hquota hcanonical
    exact IsCanonicalSmallChoreAllocation.envyFreeForChores cost r chores quota allocation a
      hcost hr hquota hcanonical

/-- The source's quota vector associated with a prescribed set of long agents. -/
def canonicalQuota (a : ℕ) (longAgents : Finset (Fin 4)) (agent : Fin 4) : ℕ :=
  a + if agent ∈ longAgents then 1 else 0

private theorem canonicalQuota_range (a : ℕ) (longAgents : Finset (Fin 4)) :
    ∀ agent, canonicalQuota a longAgents agent = a ∨
      canonicalQuota a longAgents agent = a + 1 := by
  intro agent
  by_cases hlong : agent ∈ longAgents <;> simp [canonicalQuota, hlong]

/-- The source canonical quota vector has total size `4a + |longAgents|`. -/
theorem canonicalQuota_sum (a : ℕ) (longAgents : Finset (Fin 4)) :
    Finset.univ.sum (canonicalQuota a longAgents) = 4 * a + longAgents.card := by
  simp [canonicalQuota, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_const, Nat.mul_comm]

/-- Under the M01 condition, distinct agents' own-small chore pools are
disjoint. -/
private theorem ownSmallChoreSet_disjoint_of_atMostOne
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4) (hne : first ≠ second)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    Disjoint (ownSmallChoreSet cost chores first) (ownSmallChoreSet cost chores second) := by
  classical
  rw [Finset.disjoint_left]
  intro item hfirst hsecond
  have hitem : item ∈ chores := (Finset.mem_filter.mp hfirst).1
  have hfirstSmall : first ∈ smallAgentSet cost item := by
    simpa [smallAgentSet, IsSmallChore] using (Finset.mem_filter.mp hfirst).2
  have hsecondSmall : second ∈ smallAgentSet cost item := by
    simpa [smallAgentSet, IsSmallChore] using (Finset.mem_filter.mp hsecond).2
  have hsubset : ({first, second} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
    intro agent hagent
    simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
    rcases hagent with rfl | rfl
    · exact hfirstSmall
    · exact hsecondSmall
  have hcard := Finset.card_le_card hsubset
  have hpairCard : ({first, second} : Finset (Fin 4)).card = 2 := by simp [hne]
  have hsmallCard := hsmall item hitem
  change (smallAgentSet cost item).card ≤ 1 at hsmallCard
  omega

/-- In an M01 pool, the own-small chore sets of distinct agents are disjoint,
so their total cardinality is bounded by the size of the pool. -/
private theorem sum_ownSmallChoreSet_card_le
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    Finset.univ.sum (fun agent => (ownSmallChoreSet cost chores agent).card) ≤ chores.card := by
  classical
  let own : Fin 4 → Finset Item := fun agent => ownSmallChoreSet cost chores agent
  have hdisjoint : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint own := by
    intro first _ second _ hne
    change Disjoint (own first) (own second)
    rw [Finset.disjoint_left]
    intro item hfirst hsecond
    have hitem : item ∈ chores := (Finset.mem_filter.mp hfirst).1
    have hfirstSmall : first ∈ smallAgentSet cost item := by
      simpa [own, ownSmallChoreSet, smallAgentSet, IsSmallChore] using
        (Finset.mem_filter.mp hfirst).2
    have hsecondSmall : second ∈ smallAgentSet cost item := by
      simpa [own, ownSmallChoreSet, smallAgentSet, IsSmallChore] using
        (Finset.mem_filter.mp hsecond).2
    have hsubset : ({first, second} : Finset (Fin 4)) ⊆ smallAgentSet cost item := by
      intro agent hagent
      simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
      rcases hagent with rfl | rfl
      · exact hfirstSmall
      · exact hsecondSmall
    have hcard := Finset.card_le_card hsubset
    have hpairCard : ({first, second} : Finset (Fin 4)).card = 2 := by simp [hne]
    have hsmallCard := hsmall item hitem
    change (smallAgentSet cost item).card ≤ 1 at hsmallCard
    omega
  let ownGoods : Finset Item := (Finset.univ : Finset (Fin 4)).biUnion own
  have hsubset : ownGoods ⊆ chores := by
    intro item hitem
    obtain ⟨agent, _, hown⟩ := Finset.mem_biUnion.mp hitem
    exact (Finset.mem_filter.mp hown).1
  calc
    Finset.univ.sum (fun agent => (ownSmallChoreSet cost chores agent).card) = ownGoods.card := by
      change ∑ agent ∈ (Finset.univ : Finset (Fin 4)), (own agent).card = ownGoods.card
      rw [← Finset.card_biUnion hdisjoint]
    _ ≤ chores.card := Finset.card_le_card hsubset

/-- The source's light-agent counting argument: with `0 < b ≤ 3`, at least
`4-b` agents have at most `2a` own-small chores. -/
private theorem existsShortLightAgents
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a b : ℕ) (hbpos : 0 < b) (hb : b ≤ 3)
    (hchores : chores.card = 4 * a + b)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    ∃ shortAgents : Finset (Fin 4), shortAgents.card = 4 - b ∧
      ∀ agent ∈ shortAgents, (ownSmallChoreSet cost chores agent).card ≤ 2 * a := by
  classical
  let heavy : Finset (Fin 4) := (Finset.univ : Finset (Fin 4)).filter fun agent =>
    2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card
  have hheavyLower : heavy.card * (2 * a + 1) ≤
      heavy.sum (fun agent => (ownSmallChoreSet cost chores agent).card) := by
    calc
      heavy.card * (2 * a + 1) = heavy.sum fun _agent => 2 * a + 1 := by
        simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ heavy.sum (fun agent => (ownSmallChoreSet cost chores agent).card) := by
        apply Finset.sum_le_sum
        intro agent hagent
        exact (Finset.mem_filter.mp hagent).2
  have hheavyTotal : heavy.sum (fun agent => (ownSmallChoreSet cost chores agent).card) ≤
      Finset.univ.sum (fun agent => (ownSmallChoreSet cost chores agent).card) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro agent _ _
      omega
  have htotal := sum_ownSmallChoreSet_card_le Item cost chores hsmall
  have hheavyCard : heavy.card ≤ b := by
    by_contra hnot
    have hlarge : b + 1 ≤ heavy.card := by omega
    have hbound : (b + 1) * (2 * a + 1) ≤ chores.card := by
      calc
        (b + 1) * (2 * a + 1) ≤ heavy.card * (2 * a + 1) :=
          Nat.mul_le_mul_right (2 * a + 1) hlarge
        _ ≤ heavy.sum (fun agent => (ownSmallChoreSet cost chores agent).card) := hheavyLower
        _ ≤ Finset.univ.sum (fun agent => (ownSmallChoreSet cost chores agent).card) := hheavyTotal
        _ ≤ chores.card := htotal
    rw [hchores] at hbound
    interval_cases b <;> omega
  let light : Finset (Fin 4) := Finset.univ \ heavy
  have hlightCard : 4 - b ≤ light.card := by
    have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [show light = Finset.univ \ heavy by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ heavy), huniv]
    omega
  obtain ⟨shortAgents, hshortSubset, hshortCard⟩ := light.exists_subset_card_eq hlightCard
  refine ⟨shortAgents, hshortCard, ?_⟩
  intro agent hagent
  have hlightMem : agent ∈ light := hshortSubset hagent
  have hnotHeavy : agent ∉ heavy := by
    change agent ∈ Finset.univ \ heavy at hlightMem
    exact (Finset.mem_sdiff.mp hlightMem).2
  have hnotLarge : ¬ 2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card := by
    intro hlarge
    apply hnotHeavy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlarge⟩
  omega

/-- The numerical part of source Lemma `canonical`(b): once the short agents
are chosen among those with at most `2a` own-small chores, every canonical
allocation at the induced quotas is super-canonical. -/
theorem existsSuperCanonicalOfShortLight
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (shortAgents longAgents : Finset (Fin 4)) (a b : ℕ)
    (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r) (hb : b ≤ 3)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item)
    (hchores : chores.card = 4 * a + b)
    (hlong : longAgents = Finset.univ \ shortAgents)
    (hshortCard : shortAgents.card = 4 - b)
    (hshortLight : ∀ agent ∈ shortAgents,
      (ownSmallChoreSet cost chores agent).card ≤ 2 * a) :
    ∃ allocation,
      IsCanonicalSmallChoreAllocation cost chores (canonicalQuota a longAgents) allocation ∧
      ∀ i j, canonicalQuota a longAgents i = a → canonicalQuota a longAgents j = a + 1 →
        additiveChoreCost cost i (allocation i) ≤
          additiveChoreCost cost i (allocation j) - r := by
  classical
  let quota : Fin 4 → ℕ := canonicalQuota a longAgents
  have hlongCard : longAgents.card = b := by
    rw [hlong, Finset.card_sdiff_of_subset (Finset.subset_univ shortAgents)]
    have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    omega
  have hquotaSum : Finset.univ.sum quota = chores.card := by
    rw [show quota = canonicalQuota a longAgents by rfl, canonicalQuota_sum,
      hlongCard, hchores]
  obtain ⟨allocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost chores quota hquotaSum hsmall
  refine ⟨allocation, hcanonical, ?_⟩
  intro i j hquotaI hquotaJ
  have hquotaI' : quota i = a := by
    simpa [quota] using hquotaI
  have hquotaJ' : quota j = a + 1 := by
    simpa [quota] using hquotaJ
  have hiLong : i ∉ longAgents := by
    intro hi
    dsimp [quota, canonicalQuota] at hquotaI
    simp [hi] at hquotaI
  have hjLong : j ∈ longAgents := by
    by_contra hj
    dsimp [quota, canonicalQuota] at hquotaJ
    simp [hj] at hquotaJ
  have hiShort : i ∈ shortAgents := by
    rw [hlong] at hiLong
    simpa using hiLong
  have hshortLongDisjoint : Disjoint shortAgents longAgents := by
    rw [hlong]
    exact Finset.disjoint_sdiff
  have hij : i ≠ j := by
    intro hEq
    subst j
    exact (Finset.disjoint_left.mp hshortLongDisjoint hiShort hjLong).elim
  have hcardI : (allocation i).card = a := by
    rw [hcanonical.2 i |>.1, hquotaI']
  have hcardJ : (allocation j).card = a + 1 := by
    rw [hcanonical.2 j |>.1, hquotaJ']
  have hlight : (ownSmallChoreSet cost chores i).card ≤ 2 * a :=
    hshortLight i hiShort
  by_cases hsmallFew : (ownSmallChoreSet cost chores i).card < a
  · have hcanonicalOwn :
        (ownSmallChoreSet cost (allocation i) i).card =
          (ownSmallChoreSet cost chores i).card := by
      rw [hcanonical.2 i |>.2, hquotaI', Nat.min_eq_right hsmallFew.le]
    have hallocationSubset : allocation i ⊆ chores := by
      intro item hitem
      exact hcanonical.1.1 i item hitem
    have hownEq : ownSmallChoreSet cost (allocation i) i =
        ownSmallChoreSet cost chores i :=
      ownSmallChoreSet_eq_of_subset_and_card cost i hallocationSubset hcanonicalOwn
    have hotherLarge : ∀ item ∈ allocation j, IsLargeChore cost r i item := by
      intro item hitem
      rcases hcost i item with hitemSmall | hitemLarge
      · exfalso
        have hitemChores : item ∈ chores := hcanonical.1.1 j item hitem
        have hitemOwn : item ∈ ownSmallChoreSet cost chores i := by
          exact Finset.mem_filter.mpr ⟨hitemChores, hitemSmall⟩
        have hitemI : item ∈ allocation i := by
          have hsmallI : item ∈ ownSmallChoreSet cost (allocation i) i := by
            rw [hownEq]
            exact hitemOwn
          exact (Finset.mem_filter.mp hsmallI).1
        exact hij (isAllocationOf_owner_unique hcanonical.1 hitemChores hitemI hitem)
      · exact hitemLarge
    have hcostI : additiveChoreCost cost i (allocation i) ≤ (a : ℝ) * r := by
      calc
        additiveChoreCost cost i (allocation i) ≤ (allocation i).card • r :=
          additiveChoreCost_le_card_nsmul_of_le cost i (allocation i) r
            (fun item hitem => IsOneOrRChoreCost.le_r cost r hcost hr i item)
        _ = (a : ℝ) * r := by rw [hcardI]; simp [nsmul_eq_mul]
    have hcostJ : additiveChoreCost cost i (allocation j) = (a + 1 : ℕ) • r := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation j) r hotherLarge,
        hcardJ]
    calc
      additiveChoreCost cost i (allocation i) ≤ (a : ℝ) * r := hcostI
      _ = ((a + 1 : ℕ) : ℝ) * r - r := by push_cast; ring
      _ = (a + 1 : ℕ) • r - r := by simp [nsmul_eq_mul]
      _ = additiveChoreCost cost i (allocation j) - r := by rw [hcostJ]
  · have hsmallEnough : a ≤ (ownSmallChoreSet cost chores i).card := by omega
    have hcanonicalOwn : (ownSmallChoreSet cost (allocation i) i).card = a := by
      rw [hcanonical.2 i |>.2, hquotaI', Nat.min_eq_left hsmallEnough]
    have hownIeq : ownSmallChoreSet cost (allocation i) i = allocation i := by
      apply Finset.eq_of_subset_of_card_le
      · intro item hitem
        exact (Finset.mem_filter.mp hitem).1
      · rw [hcanonicalOwn, hcardI]
    have hownI : ∀ item ∈ allocation i, IsSmallChore cost i item := by
      intro item hitem
      have hsmallItem : item ∈ ownSmallChoreSet cost (allocation i) i := by
        rw [hownIeq]
        exact hitem
      exact (Finset.mem_filter.mp hsmallItem).2
    have hdisjointBundles : Disjoint (allocation i) (allocation j) := by
      rw [Finset.disjoint_left]
      intro item hi hj
      exact hij (isAllocationOf_owner_unique hcanonical.1
        (hcanonical.1.1 i item hi) hi hj)
    have hlargeExists : ∃ item ∈ allocation j, IsLargeChore cost r i item := by
      by_contra hnone
      push Not at hnone
      have hotherSmall : ∀ item ∈ allocation j, IsSmallChore cost i item := by
        intro item hitem
        rcases hcost i item with hitemSmall | hitemLarge
        · exact hitemSmall
        · exact False.elim (hnone item hitem hitemLarge)
      have hsubset : allocation i ∪ allocation j ⊆ ownSmallChoreSet cost chores i := by
        intro item hitem
        rcases Finset.mem_union.mp hitem with hitemI | hitemJ
        · exact Finset.mem_filter.mpr ⟨hcanonical.1.1 i item hitemI, hownI item hitemI⟩
        · exact Finset.mem_filter.mpr ⟨hcanonical.1.1 j item hitemJ,
            hotherSmall item hitemJ⟩
      have hcardUnion : (allocation i ∪ allocation j).card = 2 * a + 1 := by
        rw [Finset.card_union_of_disjoint hdisjointBundles, hcardI, hcardJ]
        omega
      have hcardLe := Finset.card_le_card hsubset
      omega
    obtain ⟨largeItem, hlargeItem, hlargeCost⟩ := hlargeExists
    have hcostI : additiveChoreCost cost i (allocation i) = a := by
      have hcostConst : ∀ item ∈ allocation i, cost i item = 1 := hownI
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost i (allocation i) 1 hcostConst,
        hcardI]
      norm_num [nsmul_eq_mul]
    have heraseCard : (allocation j \ {largeItem}).card = a := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hlargeItem, hcardJ]
      omega
    have heraseLower : (a : ℝ) ≤
        additiveChoreCost cost i (allocation j \ {largeItem}) := by
      calc
        (a : ℝ) = (allocation j \ {largeItem}).card • (1 : ℝ) := by
          rw [heraseCard]
          norm_num [nsmul_eq_mul]
        _ ≤ additiveChoreCost cost i (allocation j \ {largeItem}) :=
          card_nsmul_le_additiveChoreCost_of_le cost i (allocation j \ {largeItem}) 1
            (fun item hitem => IsOneOrRChoreCost.one_le cost r hcost hr i item)
    have heraseCost : additiveChoreCost cost i (allocation j \ {largeItem}) =
        additiveChoreCost cost i (allocation j) - r := by
      rw [additiveChoreCost_erase cost i (allocation j) largeItem hlargeItem, hlargeCost]
    rw [hcostI]
    linarith

/-- Source Lemma `canonical`(b): whenever `b>0`, an M01 pool has a
super-canonical allocation.  The light-agent selection is the source's
heavy-count argument, followed by the super-canonical estimate above. -/
theorem existsSuperCanonicalSmallChoreAllocation
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a b : ℕ)
    (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r) (hb : b ≤ 3) (hbpos : 0 < b)
    (hchores : chores.card = 4 * a + b)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item) :
    ∃ quota allocation,
      (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧
      IsCanonicalSmallChoreAllocation cost chores quota allocation ∧
      ∀ i j, quota i = a → quota j = a + 1 →
        additiveChoreCost cost i (allocation i) ≤
          additiveChoreCost cost i (allocation j) - r := by
  obtain ⟨shortAgents, hshortCard, hshortLight⟩ :=
    existsShortLightAgents Item cost chores a b hbpos hb hchores hsmall
  obtain ⟨allocation, hcanonical, hsuper⟩ :=
    existsSuperCanonicalOfShortLight Item r cost chores shortAgents
      (Finset.univ \ shortAgents) a b hr hcost hb hsmall hchores rfl hshortCard hshortLight
  refine ⟨canonicalQuota a (Finset.univ \ shortAgents), allocation,
    canonicalQuota_range a (Finset.univ \ shortAgents), hcanonical, hsuper⟩

/-- The exceptional configuration in Lemma `canonical`(c).  Two agents own
all `4a+2` uniquely-small chores, with `2a+1` each; splitting their residual
chores crosswise yields one prescribed short agent on each side. -/
private theorem existsSuperCanonicalOfHeavyPair
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ) (i k j l : Fin 4)
    (ha : 0 < a) (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r)
    (hagents : ({i, k, j, l} : Finset (Fin 4)) = Finset.univ)
    (hownDisjoint : Disjoint (ownSmallChoreSet cost chores i)
      (ownSmallChoreSet cost chores k))
    (hcover : ownSmallChoreSet cost chores i ∪ ownSmallChoreSet cost chores k = chores)
    (hiCard : (ownSmallChoreSet cost chores i).card = 2 * a + 1)
    (hkCard : (ownSmallChoreSet cost chores k).card = 2 * a + 1)
    (hjEmpty : ownSmallChoreSet cost chores j = ∅)
    (hlEmpty : ownSmallChoreSet cost chores l = ∅) :
    ∃ allocation,
      IsCanonicalSmallChoreAllocation cost chores (canonicalQuota a {k, l}) allocation ∧
      ∀ x y, canonicalQuota a {k, l} x = a → canonicalQuota a {k, l} y = a + 1 →
        additiveChoreCost cost x (allocation x) ≤
          additiveChoreCost cost x (allocation y) - r := by
  classical
  let ownI := ownSmallChoreSet cost chores i
  let ownK := ownSmallChoreSet cost chores k
  change Disjoint ownI ownK at hownDisjoint
  change ownI ∪ ownK = chores at hcover
  change ownI.card = 2 * a + 1 at hiCard
  change ownK.card = 2 * a + 1 at hkCard
  have hfour : ({i, k, j, l} : Finset (Fin 4)).card = 4 := by
    rw [hagents]
    decide
  have card_three_le (first second third : Fin 4) :
      ({first, second, third} : Finset (Fin 4)).card ≤ 3 := by
    calc
      ({first, second, third} : Finset (Fin 4)).card ≤
          ({second, third} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({third} : Finset (Fin 4)).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  have hik : i ≠ k := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({i, j, l} : Finset (Fin 4)).card :=
          by simp [hEq]
        _ ≤ 3 := card_three_le i j l
    omega
  have hij : i ≠ j := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({i, k, l} : Finset (Fin 4)).card :=
          by
            congr 1
            ext agent
            simp only [Finset.mem_insert, Finset.mem_singleton]
            aesop
        _ ≤ 3 := card_three_le i k l
    omega
  have hil : i ≠ l := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({k, j, l} : Finset (Fin 4)).card :=
          by
            congr 1
            ext agent
            simp [hEq]
        _ ≤ 3 := card_three_le k j l
    omega
  have hkj : k ≠ j := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({i, k, l} : Finset (Fin 4)).card :=
          by simp [hEq]
        _ ≤ 3 := card_three_le i k l
    omega
  have hkl : k ≠ l := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({i, j, l} : Finset (Fin 4)).card :=
          by
            congr 1
            ext agent
            simp [hEq]
        _ ≤ 3 := card_three_le i j l
    omega
  have hjl : j ≠ l := by
    intro hEq
    have hle : ({i, k, j, l} : Finset (Fin 4)).card ≤ 3 := by
      calc
        ({i, k, j, l} : Finset (Fin 4)).card = ({i, k, j} : Finset (Fin 4)).card :=
          by simp [hEq]
        _ ≤ 3 := card_three_le i k j
    omega
  have hAgents : ∀ agent : Fin 4, agent = i ∨ agent = k ∨ agent = j ∨ agent = l := by
    intro agent
    have hmem : agent ∈ ({i, k, j, l} : Finset (Fin 4)) := by rw [hagents]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  obtain ⟨iBundle, hiBundleSub, hiBundleCard⟩ :=
    ownI.exists_subset_card_eq (by rw [hiCard]; omega : a ≤ ownI.card)
  let remI := ownI \ iBundle
  have hremICard : remI.card = a + 1 := by
    rw [show remI = ownI \ iBundle by rfl, Finset.card_sdiff_of_subset hiBundleSub,
      hiCard, hiBundleCard]
    omega
  obtain ⟨lFromI, hlFromISub, hlFromICard⟩ : ∃ selected ⊆ remI, selected.card = a :=
    remI.exists_subset_card_eq (by rw [hremICard]; omega)
  let jFromI := remI \ lFromI
  have hjFromICard : jFromI.card = 1 := by
    rw [show jFromI = remI \ lFromI by rfl,
      Finset.card_sdiff_of_subset hlFromISub, hremICard, hlFromICard]
    omega
  obtain ⟨kBundle, hkBundleSub, hkBundleCard⟩ :=
    ownK.exists_subset_card_eq (by rw [hkCard]; omega : a + 1 ≤ ownK.card)
  let remK := ownK \ kBundle
  have hremKCard : remK.card = a := by
    rw [show remK = ownK \ kBundle by rfl, Finset.card_sdiff_of_subset hkBundleSub,
      hkCard, hkBundleCard]
    omega
  obtain ⟨lFromK, hlFromKSub, hlFromKCard⟩ : ∃ selected ⊆ remK, selected.card = 1 :=
    remK.exists_subset_card_eq (by rw [hremKCard]; omega)
  let jFromK := remK \ lFromK
  have hjFromKCard : jFromK.card = a - 1 := by
    rw [show jFromK = remK \ lFromK by rfl,
      Finset.card_sdiff_of_subset hlFromKSub, hremKCard, hlFromKCard]
  let lBundle := lFromI ∪ lFromK
  let jBundle := jFromI ∪ jFromK
  let allocation : Allocation (Fin 4) Item := fun agent =>
    if agent = i then iBundle else if agent = k then kBundle else
      if agent = j then jBundle else lBundle
  have hremIPart : lFromI ∪ jFromI = remI :=
    Finset.union_sdiff_of_subset hlFromISub
  have hremKPart : lFromK ∪ jFromK = remK :=
    Finset.union_sdiff_of_subset hlFromKSub
  have hpartI : (iBundle ∪ lFromI) ∪ jFromI = ownI := by
    rw [Finset.union_assoc, hremIPart]
    exact Finset.union_sdiff_of_subset hiBundleSub
  have hpartK : (kBundle ∪ lFromK) ∪ jFromK = ownK := by
    rw [Finset.union_assoc, hremKPart]
    exact Finset.union_sdiff_of_subset hkBundleSub
  have hiRemDisjoint : Disjoint iBundle remI := by
    change Disjoint iBundle (ownI \ iBundle)
    exact Finset.disjoint_sdiff
  have hkRemDisjoint : Disjoint kBundle remK := by
    change Disjoint kBundle (ownK \ kBundle)
    exact Finset.disjoint_sdiff
  have hlIRemDisjoint : Disjoint lFromI jFromI := by
    change Disjoint lFromI (remI \ lFromI)
    exact Finset.disjoint_sdiff
  have hlKRemDisjoint : Disjoint lFromK jFromK := by
    change Disjoint lFromK (remK \ lFromK)
    exact Finset.disjoint_sdiff
  have hlFromIOwn : lFromI ⊆ ownI := hlFromISub.trans Finset.sdiff_subset
  have hjFromIOwn : jFromI ⊆ ownI := Finset.sdiff_subset.trans Finset.sdiff_subset
  have hlFromKOwn : lFromK ⊆ ownK := hlFromKSub.trans Finset.sdiff_subset
  have hjFromKOwn : jFromK ⊆ ownK := Finset.sdiff_subset.trans Finset.sdiff_subset
  have hIJK : Disjoint iBundle kBundle := Disjoint.mono hiBundleSub hkBundleSub hownDisjoint
  have hIL : Disjoint iBundle lBundle := by
    rw [show lBundle = lFromI ∪ lFromK by rfl, Finset.disjoint_union_right]
    constructor
    · exact Disjoint.mono (by rfl) hlFromISub hiRemDisjoint
    · exact Disjoint.mono hiBundleSub hlFromKOwn hownDisjoint
  have hIJ : Disjoint iBundle jBundle := by
    rw [show jBundle = jFromI ∪ jFromK by rfl, Finset.disjoint_union_right]
    constructor
    · exact Disjoint.mono (by rfl) Finset.sdiff_subset hiRemDisjoint
    · exact Disjoint.mono hiBundleSub hjFromKOwn hownDisjoint
  have hKL : Disjoint kBundle lBundle := by
    rw [show lBundle = lFromI ∪ lFromK by rfl, Finset.disjoint_union_right]
    constructor
    · exact Disjoint.mono hkBundleSub hlFromIOwn hownDisjoint.symm
    · exact Disjoint.mono (by rfl) hlFromKSub hkRemDisjoint
  have hKJ : Disjoint kBundle jBundle := by
    rw [show jBundle = jFromI ∪ jFromK by rfl, Finset.disjoint_union_right]
    constructor
    · exact Disjoint.mono hkBundleSub hjFromIOwn hownDisjoint.symm
    · exact Disjoint.mono (by rfl) Finset.sdiff_subset hkRemDisjoint
  have hLJ : Disjoint lBundle jBundle := by
    rw [show lBundle = lFromI ∪ lFromK by rfl,
      show jBundle = jFromI ∪ jFromK by rfl, Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_union_right]
      constructor
      · exact hlIRemDisjoint
      · exact Disjoint.mono hlFromIOwn hjFromKOwn hownDisjoint
    · rw [Finset.disjoint_union_right]
      constructor
      · exact Disjoint.mono hlFromKOwn (Finset.sdiff_subset.trans Finset.sdiff_subset)
          hownDisjoint.symm
      · exact hlKRemDisjoint
  have hallocI : allocation i = iBundle := by simp [allocation]
  have hallocK : allocation k = kBundle := by simp [allocation, hik.symm]
  have hallocJ : allocation j = jBundle := by simp [allocation, hij.symm, hkj.symm]
  have hallocL : allocation l = lBundle := by
    simp [allocation, hil.symm, hkl.symm, hjl.symm]
  have hdisjointAllocation :
      ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint allocation := by
    intro first _ second _ hne
    change Disjoint (allocation first) (allocation second)
    rcases hAgents first with rfl | rfl | rfl | rfl <;>
      rcases hAgents second with rfl | rfl | rfl | rfl
    all_goals try { exact (hne rfl).elim }
    · rw [hallocI, hallocK]; exact hIJK
    · rw [hallocI, hallocJ]; exact hIJ
    · rw [hallocI, hallocL]; exact hIL
    · rw [hallocK, hallocI]; exact hIJK.symm
    · rw [hallocK, hallocJ]; exact hKJ
    · rw [hallocK, hallocL]; exact hKL
    · rw [hallocJ, hallocI]; exact hIJ.symm
    · rw [hallocJ, hallocK]; exact hKJ.symm
    · rw [hallocJ, hallocL]; exact hLJ.symm
    · rw [hallocL, hallocI]; exact hIL.symm
    · rw [hallocL, hallocK]; exact hKL.symm
    · rw [hallocL, hallocJ]; exact hLJ
  have hbiChores : iBundle ⊆ chores := by
    intro item hitem
    exact (Finset.mem_filter.mp (hiBundleSub hitem)).1
  have hbkChores : kBundle ⊆ chores := by
    intro item hitem
    exact (Finset.mem_filter.mp (hkBundleSub hitem)).1
  have hlChores : lBundle ⊆ chores := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hitemI | hitemK
    · exact (Finset.mem_filter.mp (hlFromIOwn hitemI)).1
    · exact (Finset.mem_filter.mp (hlFromKOwn hitemK)).1
  have hjChores : jBundle ⊆ chores := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hitemI | hitemK
    · exact (Finset.mem_filter.mp (hjFromIOwn hitemI)).1
    · exact (Finset.mem_filter.mp (hjFromKOwn hitemK)).1
  have hunionAllocation : (Finset.univ : Finset (Fin 4)).biUnion allocation = chores := by
    ext item
    constructor
    · intro hitem
      obtain ⟨agent, _, hagent⟩ := Finset.mem_biUnion.mp hitem
      rcases hAgents agent with rfl | rfl | rfl | rfl
      · rw [hallocI] at hagent
        exact hbiChores hagent
      · rw [hallocK] at hagent
        exact hbkChores hagent
      · rw [hallocJ] at hagent
        exact hjChores hagent
      · rw [hallocL] at hagent
        exact hlChores hagent
    · intro hitem
      rw [← hcover] at hitem
      rcases Finset.mem_union.mp hitem with hitemI | hitemK
      · rw [← hpartI] at hitemI
        rcases Finset.mem_union.mp hitemI with hitemI | hitemJ
        · rcases Finset.mem_union.mp hitemI with hitemBundle | hitemL
          · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by rw [hallocI]; exact hitemBundle⟩
          · exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, by
              rw [hallocL]; exact Finset.mem_union_left _ hitemL⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
            rw [hallocJ]; exact Finset.mem_union_left _ hitemJ⟩
      · rw [← hpartK] at hitemK
        rcases Finset.mem_union.mp hitemK with hitemK | hitemJ
        · rcases Finset.mem_union.mp hitemK with hitemBundle | hitemL
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, by rw [hallocK]; exact hitemBundle⟩
          · exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, by
              rw [hallocL]; exact Finset.mem_union_right _ hitemL⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
            rw [hallocJ]; exact Finset.mem_union_right _ hitemJ⟩
  have hallocation : IsAllocationOf allocation chores :=
    isAllocationOf_of_pairwiseDisjoint_biUnion allocation chores hdisjointAllocation hunionAllocation
  have hlFromIDisjointK : Disjoint lFromI lFromK :=
    Disjoint.mono hlFromIOwn hlFromKOwn hownDisjoint
  have hjFromIDisjointK : Disjoint jFromI jFromK :=
    Disjoint.mono hjFromIOwn hjFromKOwn hownDisjoint
  have hlBundleCard : lBundle.card = a + 1 := by
    rw [show lBundle = lFromI ∪ lFromK by rfl,
      Finset.card_union_of_disjoint hlFromIDisjointK, hlFromICard, hlFromKCard]
  have hjBundleCard : jBundle.card = a := by
    rw [show jBundle = jFromI ∪ jFromK by rfl,
      Finset.card_union_of_disjoint hjFromIDisjointK, hjFromICard, hjFromKCard]
    omega
  have hsmallI : ∀ item ∈ iBundle, IsSmallChore cost i item := by
    intro item hitem
    exact (Finset.mem_filter.mp (hiBundleSub hitem)).2
  have hsmallK : ∀ item ∈ kBundle, IsSmallChore cost k item := by
    intro item hitem
    exact (Finset.mem_filter.mp (hkBundleSub hitem)).2
  have hownIBundle : ownSmallChoreSet cost iBundle i = iBundle := by
    apply Finset.Subset.antisymm
    · intro item hitem
      exact (Finset.mem_filter.mp hitem).1
    · intro item hitem
      exact Finset.mem_filter.mpr ⟨hitem, hsmallI item hitem⟩
  have hownKBundle : ownSmallChoreSet cost kBundle k = kBundle := by
    apply Finset.Subset.antisymm
    · intro item hitem
      exact (Finset.mem_filter.mp hitem).1
    · intro item hitem
      exact Finset.mem_filter.mpr ⟨hitem, hsmallK item hitem⟩
  have hownJBundleEmpty : ownSmallChoreSet cost jBundle j = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨item, hitem⟩
    have hsmallItem := (Finset.mem_filter.mp hitem).2
    have hitemBundle := (Finset.mem_filter.mp hitem).1
    have hitemChores := hjChores hitemBundle
    have hitemOwn : item ∈ ownSmallChoreSet cost chores j :=
      Finset.mem_filter.mpr ⟨hitemChores, hsmallItem⟩
    rw [hjEmpty] at hitemOwn
    simp at hitemOwn
  have hownLBundleEmpty : ownSmallChoreSet cost lBundle l = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨item, hitem⟩
    have hsmallItem := (Finset.mem_filter.mp hitem).2
    have hitemBundle := (Finset.mem_filter.mp hitem).1
    have hitemChores := hlChores hitemBundle
    have hitemOwn : item ∈ ownSmallChoreSet cost chores l :=
      Finset.mem_filter.mpr ⟨hitemChores, hsmallItem⟩
    rw [hlEmpty] at hitemOwn
    simp at hitemOwn
  have hquotaI : canonicalQuota a {k, l} i = a := by
    simp [canonicalQuota, hik, hil]
  have hquotaK : canonicalQuota a {k, l} k = a + 1 := by
    simp [canonicalQuota]
  have hquotaJ : canonicalQuota a {k, l} j = a := by
    simp [canonicalQuota, hkj.symm, hjl]
  have hquotaL : canonicalQuota a {k, l} l = a + 1 := by
    simp [canonicalQuota]
  have hcanonical :
      IsCanonicalSmallChoreAllocation cost chores (canonicalQuota a {k, l}) allocation := by
    constructor
    · exact hallocation
    · intro agent
      rcases hAgents agent with hagent | hagent | hagent | hagent <;> subst agent
      · rw [hallocI]
        constructor
        · rw [hquotaI]
          exact hiBundleCard
        · rw [hownIBundle, hquotaI, hiCard, Nat.min_eq_left (by omega)]
          exact hiBundleCard
      · rw [hallocK]
        constructor
        · rw [hquotaK]
          exact hkBundleCard
        · rw [hownKBundle, hquotaK, hkCard, Nat.min_eq_left (by omega)]
          exact hkBundleCard
      · rw [hallocJ]
        constructor
        · rw [hquotaJ]
          exact hjBundleCard
        · rw [hownJBundleEmpty, hquotaJ, hjEmpty]
          simp
      · rw [hallocL]
        constructor
        · rw [hquotaL]
          exact hlBundleCard
        · rw [hownLBundleEmpty, hquotaL, hlEmpty]
          simp
  refine ⟨allocation, hcanonical, ?_⟩
  intro x y hx hy
  have hshort_of_not_long : ∀ agent : Fin 4, agent ∉ ({k, l} : Finset (Fin 4)) →
      agent = i ∨ agent = j := by
    intro agent hnotLong
    rcases hAgents agent with hagent | hagent | hagent | hagent
    · exact Or.inl hagent
    · exfalso
      apply hnotLong
      simp [hagent]
    · exact Or.inr hagent
    · exfalso
      apply hnotLong
      simp [hagent]
  have hxNotLong : x ∉ ({k, l} : Finset (Fin 4)) := by
    intro hxLong
    rcases Finset.mem_insert.mp hxLong with hEq | hEq
    · subst x
      rw [hquotaK] at hx
      omega
    · have hEq' : x = l := by simpa using hEq
      subst x
      rw [hquotaL] at hx
      omega
  have hxShort : x = i ∨ x = j := hshort_of_not_long x hxNotLong
  have hyLongMem : y ∈ ({k, l} : Finset (Fin 4)) := by
    by_contra hyNotLong
    rcases hshort_of_not_long y hyNotLong with hEq | hEq
    · subst y
      rw [hquotaI] at hy
      omega
    · subst y
      rw [hquotaJ] at hy
      omega
  have hyLong : y = k ∨ y = l := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hyLongMem
  have hlargeIOnK : ∀ item ∈ kBundle, cost i item = r := by
    intro item hitem
    rcases hcost i item with hitemSmall | hitemLarge
    · exfalso
      have hitemK : item ∈ ownK := hkBundleSub hitem
      have hitemI : item ∈ ownI := by
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hitemK).1, hitemSmall⟩
      exact (Finset.disjoint_left.mp hownDisjoint hitemI hitemK).elim
    · exact hitemLarge
  have hlargeIOnLFromK : ∀ item ∈ lFromK, cost i item = r := by
    intro item hitem
    rcases hcost i item with hitemSmall | hitemLarge
    · exfalso
      have hitemK : item ∈ ownK := hlFromKOwn hitem
      have hitemI : item ∈ ownI := by
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hitemK).1, hitemSmall⟩
      exact (Finset.disjoint_left.mp hownDisjoint hitemI hitemK).elim
    · exact hitemLarge
  have hsmallIOnLFromI : ∀ item ∈ lFromI, cost i item = 1 := by
    intro item hitem
    exact (Finset.mem_filter.mp (hlFromIOwn hitem)).2
  have hcostI : additiveChoreCost cost i iBundle = a := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost i iBundle 1 hsmallI,
      hiBundleCard]
    norm_num [nsmul_eq_mul]
  have hcostIK : additiveChoreCost cost i kBundle = (a + 1 : ℕ) • r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost i kBundle r hlargeIOnK,
      hkBundleCard]
  have hcostILFromI : additiveChoreCost cost i lFromI = a := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost i lFromI 1 hsmallIOnLFromI,
      hlFromICard]
    norm_num [nsmul_eq_mul]
  have hcostILFromK : additiveChoreCost cost i lFromK = r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost i lFromK r hlargeIOnLFromK,
      hlFromKCard]
    simp
  have hcostIL : additiveChoreCost cost i lBundle = a + r := by
    rw [show lBundle = lFromI ∪ lFromK by rfl,
      additiveChoreCost_union cost i lFromI lFromK hlFromIDisjointK,
      hcostILFromI, hcostILFromK]
  have hjLarge : ∀ item ∈ chores, cost j item = r := by
    intro item hitem
    rcases hcost j item with hitemSmall | hitemLarge
    · exfalso
      have hitemOwn : item ∈ ownSmallChoreSet cost chores j :=
        Finset.mem_filter.mpr ⟨hitem, hitemSmall⟩
      rw [hjEmpty] at hitemOwn
      simp at hitemOwn
    · exact hitemLarge
  have hcostJ : additiveChoreCost cost j jBundle = a • r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost j jBundle r
      (fun item hitem => hjLarge item (hjChores hitem)), hjBundleCard]
  have hcostJK : additiveChoreCost cost j kBundle = (a + 1) • r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost j kBundle r
      (fun item hitem => hjLarge item (hbkChores hitem)), hkBundleCard]
  have hcostJL : additiveChoreCost cost j lBundle = (a + 1) • r := by
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost j lBundle r
      (fun item hitem => hjLarge item (hlChores hitem)), hlBundleCard]
  rcases hxShort with rfl | rfl <;> rcases hyLong with rfl | rfl
  · rw [hallocI, hallocK, hcostI, hcostIK]
    simp only [nsmul_eq_mul]
    push_cast
    nlinarith
  · rw [hallocI, hallocL, hcostI, hcostIL]
    linarith
  · rw [hallocJ, hallocK, hcostJ, hcostJK]
    simp only [nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  · rw [hallocJ, hallocL, hcostJ, hcostJL]
    simp only [nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl

/-- If both agents on one side of a two-by-two partition are heavy, the
exceptional construction supplies a super-canonical allocation with one short
agent on each side. -/
private theorem existsSuperCanonicalOfHeavySide
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (heavySide otherSide : Finset (Fin 4)) (a : ℕ)
    (ha : 0 < a) (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r)
    (hunion : heavySide ∪ otherSide = Finset.univ) (hdisjoint : Disjoint heavySide otherSide)
    (hheavyCard : heavySide.card = 2) (hotherCard : otherSide.card = 2)
    (hchores : chores.card = 4 * a + 2)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item)
    (hheavy : ∀ agent ∈ heavySide, 2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card) :
    ∃ heavyShort ∈ heavySide, ∃ otherShort ∈ otherSide, ∃ quota allocation,
      (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧
      IsCanonicalSmallChoreAllocation cost chores quota allocation ∧
      (∀ x y, quota x = a → quota y = a + 1 →
        additiveChoreCost cost x (allocation x) ≤ additiveChoreCost cost x (allocation y) - r) ∧
      quota heavyShort = a ∧ quota otherShort = a := by
  classical
  obtain ⟨p, q, hpq, hheavySide⟩ := Finset.card_eq_two.mp hheavyCard
  obtain ⟨j, l, hjl, hotherSide⟩ := Finset.card_eq_two.mp hotherCard
  have hpHeavy : p ∈ heavySide := by rw [hheavySide]; simp
  have hqHeavy : q ∈ heavySide := by rw [hheavySide]; simp
  have hjOther : j ∈ otherSide := by rw [hotherSide]; simp
  have hlOther : l ∈ otherSide := by rw [hotherSide]; simp
  have hpj : p ≠ j := by
    intro hEq
    subst j
    exact (Finset.disjoint_left.mp hdisjoint hpHeavy hjOther).elim
  have hpl : p ≠ l := by
    intro hEq
    subst l
    exact (Finset.disjoint_left.mp hdisjoint hpHeavy hlOther).elim
  have hqj : q ≠ j := by
    intro hEq
    subst j
    exact (Finset.disjoint_left.mp hdisjoint hqHeavy hjOther).elim
  have hql : q ≠ l := by
    intro hEq
    subst l
    exact (Finset.disjoint_left.mp hdisjoint hqHeavy hlOther).elim
  have hagents : ({p, q, j, l} : Finset (Fin 4)) = Finset.univ := by
    calc
      ({p, q, j, l} : Finset (Fin 4)) = {p, q} ∪ {j, l} := by
        ext agent
        simp [or_left_comm]
      _ = heavySide ∪ otherSide := by rw [← hheavySide, ← hotherSide]
      _ = Finset.univ := hunion
  have hpLower := hheavy p hpHeavy
  have hqLower := hheavy q hqHeavy
  have hpqOwnDisjoint :=
    ownSmallChoreSet_disjoint_of_atMostOne Item cost chores p q hpq hsmall
  have hpqOwnSubset : ownSmallChoreSet cost chores p ∪ ownSmallChoreSet cost chores q ⊆ chores := by
    intro item hitem
    rcases Finset.mem_union.mp hitem with hitemP | hitemQ
    · exact (Finset.mem_filter.mp hitemP).1
    · exact (Finset.mem_filter.mp hitemQ).1
  have hpqCardLe : (ownSmallChoreSet cost chores p).card +
      (ownSmallChoreSet cost chores q).card ≤ chores.card := by
    calc
      (ownSmallChoreSet cost chores p).card + (ownSmallChoreSet cost chores q).card =
          (ownSmallChoreSet cost chores p ∪ ownSmallChoreSet cost chores q).card :=
        (Finset.card_union_of_disjoint hpqOwnDisjoint).symm
      _ ≤ chores.card := Finset.card_le_card hpqOwnSubset
  have hpCard : (ownSmallChoreSet cost chores p).card = 2 * a + 1 := by
    omega
  have hqCard : (ownSmallChoreSet cost chores q).card = 2 * a + 1 := by
    omega
  have hpqUnionCard : (ownSmallChoreSet cost chores p ∪ ownSmallChoreSet cost chores q).card =
      chores.card := by
    rw [Finset.card_union_of_disjoint hpqOwnDisjoint, hpCard, hqCard, hchores]
    omega
  have hpqCover : ownSmallChoreSet cost chores p ∪ ownSmallChoreSet cost chores q = chores := by
    apply Finset.eq_of_subset_of_card_le hpqOwnSubset
    rw [hpqUnionCard]
  have hjEmpty : ownSmallChoreSet cost chores j = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨item, hitem⟩
    have hitemChores : item ∈ chores := (Finset.mem_filter.mp hitem).1
    rw [← hpqCover] at hitemChores
    rcases Finset.mem_union.mp hitemChores with hitemP | hitemQ
    · have hdisjointPJ :=
        ownSmallChoreSet_disjoint_of_atMostOne Item cost chores p j hpj hsmall
      exact (Finset.disjoint_left.mp hdisjointPJ hitemP hitem).elim
    · have hdisjointQJ :=
        ownSmallChoreSet_disjoint_of_atMostOne Item cost chores q j hqj hsmall
      exact (Finset.disjoint_left.mp hdisjointQJ hitemQ hitem).elim
  have hlEmpty : ownSmallChoreSet cost chores l = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨item, hitem⟩
    have hitemChores : item ∈ chores := (Finset.mem_filter.mp hitem).1
    rw [← hpqCover] at hitemChores
    rcases Finset.mem_union.mp hitemChores with hitemP | hitemQ
    · have hdisjointPL :=
        ownSmallChoreSet_disjoint_of_atMostOne Item cost chores p l hpl hsmall
      exact (Finset.disjoint_left.mp hdisjointPL hitemP hitem).elim
    · have hdisjointQL :=
        ownSmallChoreSet_disjoint_of_atMostOne Item cost chores q l hql hsmall
      exact (Finset.disjoint_left.mp hdisjointQL hitemQ hitem).elim
  obtain ⟨allocation, hcanonical, hsuper⟩ :=
    existsSuperCanonicalOfHeavyPair Item r cost chores a p q j l ha hr hcost hagents
      hpqOwnDisjoint hpqCover hpCard hqCard hjEmpty hlEmpty
  refine ⟨p, hpHeavy, j, hjOther, canonicalQuota a {q, l}, allocation,
    canonicalQuota_range a {q, l}, hcanonical, hsuper, ?_, ?_⟩
  · simp [canonicalQuota, hpq, hpl]
  · simp [canonicalQuota, hqj.symm, hjl]

/-- Source Lemma `canonical`(c): for every two-by-two partition, a
super-canonical M01 allocation can make one agent on each side short. -/
theorem existsSuperCanonicalOneShortEachSide
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (ha : 0 < a) (hr : 1 ≤ r) (hcost : IsOneOrRChoreCost cost r)
    (hchores : chores.card = 4 * a + 2)
    (hsmall : ∀ item ∈ chores, IsSmallForAtMostOne cost item)
    (N1 N2 : Finset (Fin 4)) (hunion : N1 ∪ N2 = Finset.univ)
    (hdisjoint : Disjoint N1 N2) (hN1Card : N1.card = 2) (hN2Card : N2.card = 2) :
    ∃ i ∈ N1, ∃ j ∈ N2, ∃ quota allocation,
      (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧
      IsCanonicalSmallChoreAllocation cost chores quota allocation ∧
      (∀ x y, quota x = a → quota y = a + 1 →
        additiveChoreCost cost x (allocation x) ≤ additiveChoreCost cost x (allocation y) - r) ∧
      quota i = a ∧ quota j = a := by
  classical
  by_cases hlightN1 : ∃ agent ∈ N1, (ownSmallChoreSet cost chores agent).card ≤ 2 * a
  · by_cases hlightN2 : ∃ agent ∈ N2, (ownSmallChoreSet cost chores agent).card ≤ 2 * a
    · obtain ⟨i, hiN1, hiLight⟩ := hlightN1
      obtain ⟨j, hjN2, hjLight⟩ := hlightN2
      have hij : i ≠ j := by
        intro hEq
        subst j
        exact (Finset.disjoint_left.mp hdisjoint hiN1 hjN2).elim
      have hshortCard : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hij]
      have hshortLight : ∀ agent ∈ ({i, j} : Finset (Fin 4)),
          (ownSmallChoreSet cost chores agent).card ≤ 2 * a := by
        intro agent hagent
        simp only [Finset.mem_insert, Finset.mem_singleton] at hagent
        rcases hagent with rfl | rfl
        · exact hiLight
        · exact hjLight
      obtain ⟨allocation, hcanonical, hsuper⟩ :=
        existsSuperCanonicalOfShortLight Item r cost chores {i, j}
          (Finset.univ \ {i, j}) a 2 hr hcost (by omega) hsmall hchores rfl hshortCard
          hshortLight
      refine ⟨i, hiN1, j, hjN2, canonicalQuota a (Finset.univ \ {i, j}), allocation,
        canonicalQuota_range a (Finset.univ \ {i, j}), hcanonical, hsuper, ?_, ?_⟩
      · simp [canonicalQuota]
      · simp [canonicalQuota]
    · have hheavyN2 : ∀ agent ∈ N2,
          2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card := by
        intro agent hagent
        by_contra hnotHeavy
        apply hlightN2
        refine ⟨agent, hagent, ?_⟩
        omega
      obtain ⟨heavyShort, hheavyShort, otherShort, hotherShort, quota, allocation,
        hquota, hcanonical, hsuper, hheavyQuota, hotherQuota⟩ :=
        existsSuperCanonicalOfHeavySide Item r cost chores N2 N1 a ha hr hcost
          (by simpa [Finset.union_comm] using hunion) hdisjoint.symm hN2Card hN1Card
          hchores hsmall hheavyN2
      exact ⟨otherShort, hotherShort, heavyShort, hheavyShort, quota, allocation,
        hquota, hcanonical, hsuper, hotherQuota, hheavyQuota⟩
  · have hheavyN1 : ∀ agent ∈ N1,
        2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card := by
      intro agent hagent
      by_contra hnotHeavy
      apply hlightN1
      refine ⟨agent, hagent, ?_⟩
      omega
    obtain ⟨heavyShort, hheavyShort, otherShort, hotherShort, quota, allocation,
      hquota, hcanonical, hsuper, hheavyQuota, hotherQuota⟩ :=
      existsSuperCanonicalOfHeavySide Item r cost chores N1 N2 a ha hr hcost hunion hdisjoint
        hN1Card hN2Card hchores hsmall hheavyN1
    exact ⟨heavyShort, hheavyShort, otherShort, hotherShort, quota, allocation,
      hquota, hcanonical, hsuper, hheavyQuota, hotherQuota⟩

end HT26EFXChores
