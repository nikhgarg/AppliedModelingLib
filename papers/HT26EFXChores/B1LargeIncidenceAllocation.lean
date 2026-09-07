import HT26EFXChores.B1DirectAllocation

/-!
# The large-incidence gap fill in source Case B.2.2(a)

Source Case B.2.2(a) gives one selected M₂ chore to each short agent of a
canonical prefix.  Each selected chore is small for its recipient and large
for the long agent.  This module records the resulting envy-free prefix as a
reusable, source-level allocation lemma.

Source: `EFXadditivechores.tex`, lines 2472--2504.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A canonical prefix with agent `0` long becomes envy-free after each short
agent receives one own-small chore that is large for agent `0`.  This is the
gap-filling calculation in source Case B.2.2(a), stated independently of the
combinatorial matching used to select the three chores. -/
theorem envyFreeOfCanonicalLongZeroAndTripleSmallSuffix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores gapChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation gap : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hgapSubset : gapChores ⊆ m2Chores)
    (hgapAllocation : IsAllocationOf gap gapChores)
    (hgapZero : gap 0 = ∅)
    (hshortSmall : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ gap short,
      IsSmallChore cost short item)
    (hshortCard : ∀ short : Fin 4, short ≠ 0 → (gap short).card = 1)
    (hshortLarge : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ gap short,
      IsLargeChore cost r 0 item) :
    EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) := by
  classical
  have hprefixGap : Disjoint prefixChores gapChores := hprefixM2.mono_right hgapSubset
  have hbundlesDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hfinalCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hbundlesDisjoint owner)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hquotaShort : ∀ short : Fin 4, short ≠ 0 → quota short = a := by
    intro short hshort
    fin_cases short
    · exact (hshort rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hprefixEqual : ∀ first second : Fin 4, first ≠ 0 → second ≠ 0 →
      additiveChoreCost cost first (prefixAllocation first) ≤
        additiveChoreCost cost first (prefixAllocation second) := by
    intro first second hfirst hsecond
    apply hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota
      prefixAllocation hcost (by linarith) first second
    rw [hquotaShort first hfirst, hquotaShort second hsecond]
  have hshortOwnCost : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost short (gap short) = 1 := by
    intro short hshort
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost short (gap short) 1]
    · simp [hshortCard short hshort]
    · intro item hitem
      simpa [IsSmallChore] using hshortSmall short hshort item hitem
  have hshortLongCost : ∀ short : Fin 4, short ≠ 0 →
      additiveChoreCost cost 0 (gap short) = r := by
    intro short hshort
    rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0 (gap short) r]
    · simp [hshortCard short hshort]
    · intro item hitem
      simpa [IsLargeChore] using hshortLarge short hshort item hitem
  have hshortCostAtLeastOne : ∀ observer short : Fin 4, short ≠ 0 →
      1 ≤ additiveChoreCost cost observer (gap short) := by
    intro observer short hshort
    have hcostLower : ∀ item ∈ gap short, 1 ≤ cost observer item := by
      intro item hitem
      exact IsOneOrRChoreCost.one_le cost r hcost (by linarith) observer item
    have hbound := card_nsmul_le_additiveChoreCost_of_le cost observer (gap short) 1 hcostLower
    simpa [hshortCard short hshort, nsmul_eq_mul] using hbound
  intro own comparison
  by_cases hownZero : own = 0
  · subst own
    by_cases hcomparisonZero : comparison = 0
    · subst comparison
      exact le_rfl
    · rw [hfinalCost 0 0, hfinalCost 0 comparison, hgapZero]
      simp only [additiveChoreCost_empty, add_zero]
      rw [hshortLongCost comparison hcomparisonZero]
      exact hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
        (by linarith) 0 comparison
  · by_cases hcomparisonZero : comparison = 0
    · subst comparison
      rw [hfinalCost own own, hfinalCost own 0, hgapZero]
      simp only [additiveChoreCost_empty, add_zero]
      rw [hshortOwnCost own hownZero]
      apply hcanonical.additive_add_one_le_of_quota_succ cost r prefixChores quota
        prefixAllocation hcost (by linarith) own 0
      rw [hquota0, hquotaShort own hownZero]
    · rw [hfinalCost own own, hfinalCost own comparison,
      hshortOwnCost own hownZero]
      linarith [hprefixEqual own comparison hownZero hcomparisonZero,
        hshortCostAtLeastOne own comparison hcomparisonZero]

/-- Three M₂ chores that are all large for agent `0` can be assigned one each
to agents `1`, `2`, and `3` whenever no edge fibre has multiplicity above two.
The endpoint matching is a bijection onto the three short agents, rather than
an additional certificate assumed by the source-case allocation. -/
theorem existsTripleSmallSuffix_of_card_three_allLargeForZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (m2Chores gapChores : Finset Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hgapSubset : gapChores ⊆ m2Chores) (hgapCard : gapChores.card = 3)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2)
    (hlargeZero : ∀ item ∈ gapChores, IsLargeChore cost r 0 item) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap gapChores ∧ gap 0 = ∅ ∧
        (∀ short : Fin 4, short ≠ 0 → (gap short).card = 1) ∧
        (∀ short : Fin 4, short ≠ 0 → ∀ item ∈ gap short,
          IsSmallChore cost short item ∧ IsLargeChore cost r 0 item) := by
  classical
  have hgapSmall : ∀ item ∈ gapChores, IsSmallForExactlyTwo cost item := by
    intro item hitem
    exact hm2Small item (hgapSubset hitem)
  have hgapTypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost gapChores smallAgents).card ≤ 2 := by
    intro smallAgents
    exact (Finset.card_le_card
      (m2TypeChorePool_mono cost smallAgents hgapSubset)).trans (htypeCard smallAgents)
  obtain ⟨endpoint, hinjective, hendpointSmall⟩ :=
    exists_injective_smallEndpoint_of_m2_card_le_three Item cost gapChores hgapSmall
      hgapTypeCard (by omega)
  have hendpointNeZero : ∀ item, endpoint item ≠ 0 := by
    intro item hzero
    have hsmallCost : cost 0 item = 1 := by
      simpa [hzero, IsSmallChore] using hendpointSmall item
    have hlargeCost : cost 0 item = r := hlargeZero item item.property
    linarith
  let shortEndpoint : { item // item ∈ gapChores } → { short : Fin 4 // short ≠ 0 } :=
    fun item => ⟨endpoint item, hendpointNeZero item⟩
  have hshortEndpointInjective : Function.Injective shortEndpoint := by
    intro first second hEq
    apply hinjective
    exact congrArg Subtype.val hEq
  have hdomainCard : Fintype.card { item // item ∈ gapChores } = 3 := by
    simpa only [Fintype.card_coe] using hgapCard
  have hshortCard : Fintype.card { short : Fin 4 // short ≠ 0 } = 3 := by
    decide
  have hshortEndpointBijective : Function.Bijective shortEndpoint :=
    Fintype.bijective_iff_injective_and_card shortEndpoint |>.mpr
      ⟨hshortEndpointInjective, hdomainCard.trans hshortCard.symm⟩
  let gap := smallEndpointAllocation gapChores endpoint
  have hgapAllocation : IsAllocationOf gap gapChores := by
    simpa [gap] using isAllocationOf_smallEndpointAllocation Item gapChores endpoint
  have hgapZero : gap 0 = ∅ := by
    apply smallEndpointAllocation_eq_empty_of_unused Item gapChores endpoint 0
    exact hendpointNeZero
  have hgapShortSmall : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ gap short,
      IsSmallChore cost short item := by
    intro short hshort item hitem
    exact smallEndpointAllocation_mem_small Item cost gapChores endpoint hendpointSmall short item
      (by simpa [gap] using hitem)
  have hgapShortLarge : ∀ short : Fin 4, short ≠ 0 → ∀ item ∈ gap short,
      IsLargeChore cost r 0 item := by
    intro short _hshort item hitem
    exact hlargeZero item (hgapAllocation.1 short item hitem)
  have hgapShortCard : ∀ short : Fin 4, short ≠ 0 → (gap short).card = 1 := by
    intro short hshort
    have hsurjective := hshortEndpointBijective.2 ⟨short, hshort⟩
    obtain ⟨item, hitem⟩ := hsurjective
    have hendpointEq : endpoint item = short := congrArg Subtype.val hitem
    have hmem : item.val ∈ gap short := by
      apply Finset.mem_map.mpr
      refine ⟨item, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hendpointEq⟩
    have hpos : 0 < (gap short).card := Finset.card_pos.mpr ⟨item.val, hmem⟩
    have hle : (gap short).card ≤ 1 := by
      simpa [gap] using
        smallEndpointAllocation_card_le_one_of_injective Item gapChores endpoint hinjective short
    omega
  exact ⟨gap, hgapAllocation, hgapZero, hgapShortCard,
    fun short hshort item hitem =>
      ⟨hgapShortSmall short hshort item hitem, hgapShortLarge short hshort item hitem⟩⟩

/-- Source Case B.2.2(a), with the agent who has at least three large M₂
chores displayed as agent `0`.  Three of those chores admit a matching onto
the other agents; the resulting envy-free prefix combines with the
nonexceptional residual M₂ allocation. -/
theorem existsEfxOfB1LowMultiplicity_threeLargeForZero
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a)
    (hquota2 : quota 2 = a) (hquota3 : quota 3 = a)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2)
    (hthreeLarge : 3 ≤ (largeChoreSet cost r 0 m2Chores).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  obtain ⟨gapChores, hgapSubsetLarge, hgapCard⟩ :=
    Finset.exists_subset_card_eq hthreeLarge
  have hgapSubset : gapChores ⊆ m2Chores := by
    intro item hitem
    exact largeChoreSet_subset_bundle cost r 0 m2Chores (hgapSubsetLarge hitem)
  have hgapLarge : ∀ item ∈ gapChores, IsLargeChore cost r 0 item := by
    intro item hitem
    have hlarge : item ∈ m2Chores ∧ IsLargeChore cost r 0 item := by
      simpa [largeChoreSet] using hgapSubsetLarge hitem
    exact hlarge.2
  obtain ⟨gap, hgapAllocation, hgapZero, hgapShortCard, hgapType⟩ :=
    existsTripleSmallSuffix_of_card_three_allLargeForZero Item r cost m2Chores gapChores
      hr hcost hgapSubset hgapCard hm2Small htypeCard hgapLarge
  have hleftEnvyFree : EnvyFreeForChores (additiveChoreCost cost)
      (fun agent => prefixAllocation agent ∪ gap agent) :=
    envyFreeOfCanonicalLongZeroAndTripleSmallSuffix Item r cost prefixChores m2Chores
      gapChores a quota prefixAllocation gap hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hgapSubset hgapAllocation hgapZero
      (fun short hshort item hitem => (hgapType short hshort item hitem).1)
      hgapShortCard
      (fun short hshort item hitem => (hgapType short hshort item hitem).2)
  let residueChores := m2Chores \ gapChores
  have hgapResidue : Disjoint gapChores residueChores := by
    simpa [residueChores] using (Finset.disjoint_sdiff : Disjoint gapChores (m2Chores \ gapChores))
  have hgapResidueUnion : gapChores ∪ residueChores = m2Chores := by
    simpa [residueChores] using Finset.union_sdiff_of_subset hgapSubset
  have hresidueSmall : ∀ item ∈ residueChores, IsSmallForExactlyTwo cost item := by
    intro item hitem
    exact hm2Small item (Finset.sdiff_subset hitem)
  have hnotExceptional : ¬ IsM2Exceptional cost residueChores := by
    apply not_isM2Exceptional_of_m2TypeCard_le_two_of_subset Item cost m2Chores residueChores
      (Finset.sdiff_subset)
    intro smallAgents hsmallAgents
    exact htypeCard smallAgents
  exact existsEfxOfPrefixGapAndNonexceptionalM2 Item r cost prefixChores m2Chores
    gapChores residueChores prefixAllocation gap hr hcost hprefixM2 hgapResidue hgapResidueUnion
    hcanonical.1 hgapAllocation hleftEnvyFree hresidueSmall hnotExceptional

/-- The B.2.2(a) large-incidence schedule is invariant under a relabelling of
agents.  This is the formal form of the source's ``without loss of
generality'' choice of the long, high-incidence agent. -/
theorem existsEfxOfB1LowMultiplicity_threeLarge_of_relabelled
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a + 1) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a) (hquota3 : quota (labels 3) = a)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 2)
    (hthreeLarge : 3 ≤ (largeChoreSet cost r (labels 0) m2Chores).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB1LowMultiplicity_threeLargeForZero Item r
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
  · intro item hitem
    exact (hm2Small item hitem).relabel labels cost item
  · intro smallAgents
    rw [m2TypeChorePool_relabel]
    exact htypeCard (smallAgents.map labels.toEmbedding)
  · simpa only [largeChoreSet_relabel] using hthreeLarge

end HT26EFXChores
