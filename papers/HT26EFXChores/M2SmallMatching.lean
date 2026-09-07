import Mathlib.Combinatorics.Hall.Finite
import HT26EFXChores.PoolPartition

/-!
# Small-endpoint matchings for tiny M₂ pools

The low-multiplicity branch of the source needs a matching from M₂ chores to
distinct agents who view them as small.  Hall's theorem reduces the only
nontrivial three-chore obstruction to three parallel edge-fibre chores, which
is excluded by the source's multiplicity-two assumption.

Source: `EFXadditivechores.tex`, Case B.2.2(b), lines 2506--2524.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- A pool of at most three M₂ chores admits distinct small endpoints when no
type fibre has multiplicity more than two.  This is the matching assertion
used before the source chooses an unmatched agent to be long. -/
theorem exists_injective_smallEndpoint_of_m2_card_le_three
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost chores smallAgents).card ≤ 2)
    (hcard : chores.card ≤ 3) :
    ∃ endpoint : { item // item ∈ chores } → Fin 4,
      Function.Injective endpoint ∧
        ∀ item, IsSmallChore cost (endpoint item) item := by
  classical
  let endpoints : { item // item ∈ chores } → Finset (Fin 4) :=
    fun item => smallAgentSet cost item
  have hsubtypeCard : (Finset.univ : Finset { item // item ∈ chores }).card = chores.card := by
    simpa using Fintype.card_coe chores
  have hhall : ∀ s : Finset { item // item ∈ chores },
      s.card ≤ (Finset.biUnion s endpoints).card := by
    intro s
    have hsle : s.card ≤ 3 := by
      calc
        s.card ≤ (Finset.univ : Finset { item // item ∈ chores }).card := Finset.card_le_univ _
        _ = chores.card := hsubtypeCard
        _ ≤ 3 := hcard
    by_cases hs0 : s.card = 0
    · rw [Finset.card_eq_zero.mp hs0]
      simp
    by_cases hs1 : s.card = 1
    · obtain ⟨item, hsEq⟩ := Finset.card_eq_one.mp hs1
      have hitem : item ∈ s := by rw [hsEq]; simp
      have hitemSub : endpoints item ⊆ (Finset.biUnion s endpoints) :=
        Finset.subset_biUnion_of_mem endpoints hitem
      have hitemCard : (endpoints item).card = 2 := by
        simpa [endpoints, IsSmallForExactlyTwo] using hsmall item item.property
      calc
        s.card = 1 := hs1
        _ ≤ (endpoints item).card := by omega
        _ ≤ (Finset.biUnion s endpoints).card := Finset.card_le_card hitemSub
    by_cases hs2 : s.card = 2
    · have hsNonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
        intro hempty
        have hemptyCard : s.card = 0 := Finset.card_eq_zero.mpr hempty
        omega)
      obtain ⟨item, hitem⟩ := hsNonempty
      have hitemSub : endpoints item ⊆ (Finset.biUnion s endpoints) :=
        Finset.subset_biUnion_of_mem endpoints hitem
      have hitemCard : (endpoints item).card = 2 := by
        simpa [endpoints, IsSmallForExactlyTwo] using hsmall item item.property
      rw [hs2]
      calc
        2 = (endpoints item).card := hitemCard.symm
        _ ≤ (Finset.biUnion s endpoints).card := Finset.card_le_card hitemSub
    have hs3 : s.card = 3 := by omega
    have hsNonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro hempty
      have hemptyCard : s.card = 0 := Finset.card_eq_zero.mpr hempty
      omega)
    obtain ⟨item, hitem⟩ := hsNonempty
    have hitemSub : endpoints item ⊆ (Finset.biUnion s endpoints) :=
      Finset.subset_biUnion_of_mem endpoints hitem
    have hitemCard : (endpoints item).card = 2 := by
      simpa [endpoints, IsSmallForExactlyTwo] using hsmall item item.property
    by_contra hnot
    have hbiUnionLe : (Finset.biUnion s endpoints).card ≤ 2 := by omega
    have hbiUnionEq : Finset.biUnion s endpoints = endpoints item := by
      exact (Finset.eq_of_subset_of_card_le hitemSub (by
        rw [hitemCard]
        exact hbiUnionLe)).symm
    have hsameType : ∀ other ∈ s, endpoints other = endpoints item := by
      intro other hother
      have hotherSub : endpoints other ⊆ (Finset.biUnion s endpoints) :=
        Finset.subset_biUnion_of_mem endpoints hother
      have hotherCard : (endpoints other).card = 2 := by
        simpa [endpoints, IsSmallForExactlyTwo] using hsmall other other.property
      apply Finset.eq_of_subset_of_card_le
      · simpa [hbiUnionEq] using hotherSub
      · rw [hotherCard, hitemCard]
    let lift : { item // item ∈ chores } ↪ Item := ⟨Subtype.val, Subtype.val_injective⟩
    have hmapSub : s.map lift ⊆ m2TypeChorePool cost chores (endpoints item) := by
      intro chore hchore
      obtain ⟨other, hother, hEq⟩ := Finset.mem_map.mp hchore
      subst chore
      apply (mem_m2TypeChorePool cost chores (endpoints item) other).mpr
      refine ⟨other.property, ?_⟩
      exact hsameType other hother
    have hlargeFibre : 3 ≤ (m2TypeChorePool cost chores (endpoints item)).card := by
      calc
        3 = s.card := hs3.symm
        _ = (s.map lift).card := (Finset.card_map lift).symm
        _ ≤ (m2TypeChorePool cost chores (endpoints item)).card := Finset.card_le_card hmapSub
    have htypeBound := htypeCard (endpoints item)
    omega
  obtain ⟨endpoint, hinjective, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' endpoints).mp hhall
  refine ⟨endpoint, hinjective, ?_⟩
  intro item
  simpa [endpoints, smallAgentSet, IsSmallChore] using hmem item

/-- An injective assignment of at most three chores to four agents leaves an
agent unused.  In the source this unused agent is selected as the long agent
for the super-canonical M₀₁ prefix. -/
theorem exists_unused_agent_of_injective_endpoint
    (Item : Type) [DecidableEq Item] (chores : Finset Item)
    (endpoint : { item // item ∈ chores } → Fin 4)
    (hinjective : Function.Injective endpoint) (hcard : chores.card ≤ 3) :
    ∃ agent : Fin 4, ∀ item, endpoint item ≠ agent := by
  classical
  have hsubtypeCard : (Finset.univ : Finset { item // item ∈ chores }).card = chores.card := by
    simpa using Fintype.card_coe chores
  by_contra hunused
  push Not at hunused
  have hcover : (Finset.univ : Finset (Fin 4)) ⊆ Finset.univ.image endpoint := by
    intro agent _
    obtain ⟨item, hitem⟩ := hunused agent
    exact Finset.mem_image.mpr ⟨item, Finset.mem_univ _, hitem⟩
  have himageCard : (Finset.univ.image endpoint).card = chores.card := by
    calc
      (Finset.univ.image endpoint).card = (Finset.univ : Finset { item // item ∈ chores }).card :=
        Finset.card_image_of_injective _ hinjective
      _ = chores.card := hsubtypeCard
  have hcardLe := Finset.card_le_card hcover
  have hunivCard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  rw [himageCard, hunivCard] at hcardLe
  omega

/-- Combining the small-endpoint matching with the unused-agent count gives
the exact combinatorial object used in source Case B.2.2(b): an injective
assignment of M₂ chores to small endpoints together with an agent receiving
no M₂ chore. -/
theorem exists_smallEndpointMatching_with_unused_of_m2_card_le_three
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item)
    (hsmall : ∀ item ∈ chores, IsSmallForExactlyTwo cost item)
    (htypeCard : ∀ smallAgents : Finset (Fin 4),
      (m2TypeChorePool cost chores smallAgents).card ≤ 2)
    (hcard : chores.card ≤ 3) :
    ∃ (endpoint : { item // item ∈ chores } → Fin 4) (unused : Fin 4),
      Function.Injective endpoint ∧
        (∀ item, IsSmallChore cost (endpoint item) item) ∧
        ∀ item, endpoint item ≠ unused := by
  obtain ⟨endpoint, hinjective, hsmallEndpoint⟩ :=
    exists_injective_smallEndpoint_of_m2_card_le_three Item cost chores hsmall htypeCard hcard
  obtain ⟨unused, hunused⟩ :=
    exists_unused_agent_of_injective_endpoint Item chores endpoint hinjective hcard
  exact ⟨endpoint, unused, hinjective, hsmallEndpoint, hunused⟩

/-- The concrete allocation induced by an assignment of each chore to one
agent.  It is defined on the subtype of the displayed chore pool so that its
feasibility and one-chore-per-agent facts do not depend on an arbitrary
default assignment outside that pool. -/
noncomputable def smallEndpointAllocation {Item : Type} [DecidableEq Item]
    (chores : Finset Item) (endpoint : { item // item ∈ chores } → Fin 4) :
    Allocation (Fin 4) Item :=
  fun agent => (Finset.univ.filter fun item => endpoint item = agent).map
    ⟨Subtype.val, Subtype.val_injective⟩

/-- An endpoint assignment induces a feasible allocation of precisely the
chores in its domain. -/
theorem isAllocationOf_smallEndpointAllocation
    (Item : Type) [DecidableEq Item] (chores : Finset Item)
    (endpoint : { item // item ∈ chores } → Fin 4) :
    IsAllocationOf (smallEndpointAllocation chores endpoint) chores := by
  classical
  constructor
  · intro agent item hitem
    obtain ⟨source, _hsource, hEq⟩ := Finset.mem_map.mp hitem
    change source.val = item at hEq
    simpa [← hEq] using source.property
  · intro item hitem
    refine ⟨endpoint ⟨item, hitem⟩, ?_, ?_⟩
    · apply Finset.mem_map.mpr
      refine ⟨⟨item, hitem⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · intro agent hagent
      obtain ⟨source, hsource, hEq⟩ := Finset.mem_map.mp hagent
      have hassigned : endpoint source = agent := (Finset.mem_filter.mp hsource).2
      have hsourceEq : source = ⟨item, hitem⟩ := Subtype.ext hEq
      simpa [hsourceEq] using hassigned.symm

/-- If an agent is outside the range of an endpoint assignment, her induced
bundle is empty. -/
theorem smallEndpointAllocation_eq_empty_of_unused
    (Item : Type) [DecidableEq Item] (chores : Finset Item)
    (endpoint : { item // item ∈ chores } → Fin 4) (agent : Fin 4)
    (hunused : ∀ item, endpoint item ≠ agent) :
    smallEndpointAllocation chores endpoint agent = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro item hitem
  obtain ⟨source, hsource, _hEq⟩ := Finset.mem_map.mp hitem
  exact hunused source (Finset.mem_filter.mp hsource).2

/-- Every item in an induced endpoint bundle is assigned to that endpoint. -/
theorem smallEndpointAllocation_mem_small
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (endpoint : { item // item ∈ chores } → Fin 4)
    (hsmall : ∀ item, IsSmallChore cost (endpoint item) item)
    (agent : Fin 4) (item : Item)
    (hitem : item ∈ smallEndpointAllocation chores endpoint agent) :
    IsSmallChore cost agent item := by
  classical
  obtain ⟨source, hsource, hEq⟩ := Finset.mem_map.mp hitem
  change source.val = item at hEq
  have hassigned : endpoint source = agent := (Finset.mem_filter.mp hsource).2
  simpa [hEq, hassigned] using hsmall source

/-- An injective endpoint assignment gives every agent at most one induced
chore. -/
theorem smallEndpointAllocation_card_le_one_of_injective
    (Item : Type) [DecidableEq Item] (chores : Finset Item)
    (endpoint : { item // item ∈ chores } → Fin 4)
    (hinjective : Function.Injective endpoint) (agent : Fin 4) :
    (smallEndpointAllocation chores endpoint agent).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro first hfirst second hsecond
  obtain ⟨firstSource, hfirstSource, hfirstEq⟩ := Finset.mem_map.mp hfirst
  obtain ⟨secondSource, hsecondSource, hsecondEq⟩ := Finset.mem_map.mp hsecond
  change firstSource.val = first at hfirstEq
  change secondSource.val = second at hsecondEq
  have hfirstAssigned : endpoint firstSource = agent := (Finset.mem_filter.mp hfirstSource).2
  have hsecondAssigned : endpoint secondSource = agent := (Finset.mem_filter.mp hsecondSource).2
  have hsources : firstSource = secondSource := hinjective (hfirstAssigned.trans hsecondAssigned.symm)
  calc
    first = firstSource.val := hfirstEq.symm
    _ = secondSource.val := congrArg Subtype.val hsources
    _ = second := hsecondEq

end HT26EFXChores
