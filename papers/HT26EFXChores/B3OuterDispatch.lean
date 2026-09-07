import HT26EFXChores.B3Dispatch
import HT26EFXChores.B3GraphClassification

/-!
# Outer matching transport for the high-ratio `b = 3` branch

This module turns an abstract matching of two M₂ edge types into the displayed
`(0,1),(2,3)` working labels used in source Case B.4.2(a).  It intentionally
does not choose the canonical prefix: that source choice is the next outer
dispatcher step, after the finite graph normalization below.

Source: `EFXadditivechores.tex`, lines 3200--3214.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Deleting one chore from each of two disjoint M₂ types preserves their
weak multiplicity order.  This is the cardinal bookkeeping used before the
B.4.2(a) residual allocation. -/
theorem matching_residual_type_count_le
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second : Item)
    (firstType secondType : Finset (Fin 4))
    (hfirstCard : firstType.card = 2)
    (hdisjoint : Disjoint firstType secondType)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores firstType)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores secondType)
    (hcount : (m2TypeChorePool cost m2Chores firstType).card ≤
      (m2TypeChorePool cost m2Chores secondType).card) :
    ((m2Chores \ {first, second}).filter fun item =>
      smallAgentSet cost item = firstType).card ≤
      ((m2Chores \ {first, second}).filter fun item =>
        smallAgentSet cost item = secondType).card := by
  have hpoolDisjoint : Disjoint (m2TypeChorePool cost m2Chores firstType)
      (m2TypeChorePool cost m2Chores secondType) :=
    m2TypeChorePool_disjoint_of_ne cost m2Chores firstType secondType (by
      intro heq
      subst secondType
      have hempty : firstType = ∅ := disjoint_self.mp hdisjoint
      rw [hempty] at hfirstCard
      simp at hfirstCard)
  have hfirstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact (Finset.disjoint_left.mp hpoolDisjoint hfirst hsecond).elim
  have hfirstNotSecondPool : first ∉ m2TypeChorePool cost m2Chores secondType :=
    fun hfirstSecond => Finset.disjoint_left.mp hpoolDisjoint hfirst hfirstSecond
  have hsecondNotFirstPool : second ∉ m2TypeChorePool cost m2Chores firstType :=
    fun hsecondFirst => Finset.disjoint_left.mp hpoolDisjoint hsecondFirst hsecond
  have hfirstFilter : (m2Chores \ {first, second}).filter
      (fun item => smallAgentSet cost item = firstType) =
      (m2TypeChorePool cost m2Chores firstType).erase first := by
    ext item
    constructor
    · intro hitem
      obtain ⟨hitemResidue, hitemType⟩ := Finset.mem_filter.mp hitem
      have hitemNeFirst : item ≠ first := by
        intro heq
        subst item
        exact (Finset.mem_sdiff.mp hitemResidue).2 (by simp)
      exact Finset.mem_erase.mpr ⟨hitemNeFirst,
        (mem_m2TypeChorePool cost m2Chores firstType item).mpr
          ⟨Finset.sdiff_subset hitemResidue, hitemType⟩⟩
    · intro hitem
      obtain ⟨hitemNeFirst, hitemPool⟩ := Finset.mem_erase.mp hitem
      obtain ⟨hitemBase, hitemType⟩ :=
        (mem_m2TypeChorePool cost m2Chores firstType item).mp hitemPool
      have hitemNeSecond : item ≠ second := by
        intro heq
        subst item
        exact hsecondNotFirstPool hitemPool
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hitemBase, ?_⟩, hitemType⟩
      simp [hitemNeFirst, hitemNeSecond]
  have hsecondFilter : (m2Chores \ {first, second}).filter
      (fun item => smallAgentSet cost item = secondType) =
      (m2TypeChorePool cost m2Chores secondType).erase second := by
    ext item
    constructor
    · intro hitem
      obtain ⟨hitemResidue, hitemType⟩ := Finset.mem_filter.mp hitem
      have hitemNeSecond : item ≠ second := by
        intro heq
        subst item
        exact (Finset.mem_sdiff.mp hitemResidue).2 (by simp)
      exact Finset.mem_erase.mpr ⟨hitemNeSecond,
        (mem_m2TypeChorePool cost m2Chores secondType item).mpr
          ⟨Finset.sdiff_subset hitemResidue, hitemType⟩⟩
    · intro hitem
      obtain ⟨hitemNeSecond, hitemPool⟩ := Finset.mem_erase.mp hitem
      obtain ⟨hitemBase, hitemType⟩ :=
        (mem_m2TypeChorePool cost m2Chores secondType item).mp hitemPool
      have hitemNeFirst : item ≠ first := by
        intro heq
        subst item
        exact hfirstNotSecondPool hitemPool
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hitemBase, ?_⟩, hitemType⟩
      simp [hitemNeFirst, hitemNeSecond]
  rw [hfirstFilter, hsecondFilter, Finset.card_erase_of_mem hfirst,
    Finset.card_erase_of_mem hsecond]
  exact Nat.sub_le_sub_right hcount 1

/-- Transport B.4.2(a) from displayed matching labels to any two disjoint M₂
types.  The supplied prefix is already in working labels, so all allocation
proofs run there and `exists_efx_relabel_back` returns to the original agents. -/
theorem existsEfxOfM01M2_b3_matching_shortEndpoint_of_normalized_prefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (first second : Item) (firstType secondType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hmapFirst : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType)
    (hmapSecond : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = secondType)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores firstType)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores secondType)
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = firstType ∨ smallAgentSet cost item = secondType)
    (hcount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet cost item = firstType).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet cost item = secondType).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hfirstWorking : first ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
    exact hfirst
  have hsecondWorking : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
    exact hsecond
  have htypesWorking : ∀ item ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet (relabelChoreCost labels cost) item = ({2, 3} : Finset (Fin 4)) := by
    intro item hitem
    rcases htypes item hitem with hfirstType | hsecondType
    · left
      have hmemOriginal : item ∈ m2TypeChorePool cost m2Chores firstType :=
        (mem_m2TypeChorePool cost m2Chores firstType item).mpr ⟨hitem, hfirstType⟩
      have hmemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
        exact hmemOriginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) item).mp hmemWorking |>.2
    · right
      have hmemOriginal : item ∈ m2TypeChorePool cost m2Chores secondType :=
        (mem_m2TypeChorePool cost m2Chores secondType item).mpr ⟨hitem, hsecondType⟩
      have hmemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({2, 3} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
        exact hmemOriginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4)) item).mp hmemWorking |>.2
  have hfirstFilter : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet (relabelChoreCost labels cost) item =
        ({0, 1} : Finset (Fin 4))) =
      ((m2Chores \ {first, second}).filter fun item => smallAgentSet cost item = firstType) := by
    simpa [m2TypeChorePool, hmapFirst] using
      m2TypeChorePool_relabel labels cost (m2Chores \ {first, second})
        ({0, 1} : Finset (Fin 4))
  have hsecondFilter : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet (relabelChoreCost labels cost) item =
        ({2, 3} : Finset (Fin 4))) =
      ((m2Chores \ {first, second}).filter fun item => smallAgentSet cost item = secondType) := by
    simpa [m2TypeChorePool, hmapSecond] using
      m2TypeChorePool_relabel labels cost (m2Chores \ {first, second})
        ({2, 3} : Finset (Fin 4))
  have hcountWorking : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet (relabelChoreCost labels cost) item =
        ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet (relabelChoreCost labels cost) item =
          ({2, 3} : Finset (Fin 4))).card := by
    rw [hfirstFilter, hsecondFilter]
    exact hcount
  exact existsEfxOfM01M2_b3_disjoint_shortEndpoint_of_relabelled_types Item r cost labels
    prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hfirstWorking hsecondWorking htypesWorking
    hcountWorking

/-- Transport B.4.2(b) from displayed matching labels to arbitrary two-type
matching support.  The prefix is supplied in the working labels, where agents
`0,1` are the heavy endpoints and agent `3` is short. -/
theorem existsEfxOfM01M2_b3_matching_heavyEndpoints_of_normalized_prefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (item second : Item) (firstType secondType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hmapFirst : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType)
    (hmapSecond : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = secondType)
    (hprefixSmall : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores firstType)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores secondType)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = firstType ∨ smallAgentSet cost chore = secondType)
    (hcount : (m2TypeChorePool cost m2Chores firstType).card ≤
      (m2TypeChorePool cost m2Chores secondType).card)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0,
      IsSmallChore (relabelChoreCost labels cost) 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1,
      IsSmallChore (relabelChoreCost labels cost) 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hitemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
    exact hitem
  have hsecondWorking : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
    exact hsecond
  have hm2SmallWorking : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact (hm2Small chore hchore).relabel labels cost chore
  have htypesWorking : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet (relabelChoreCost labels cost) chore = ({2, 3} : Finset (Fin 4)) := by
    intro chore hchore
    rcases htypes chore hchore with hfirstType | hsecondType
    · left
      have hmemOriginal : chore ∈ m2TypeChorePool cost m2Chores firstType :=
        (mem_m2TypeChorePool cost m2Chores firstType chore).mpr ⟨hchore, hfirstType⟩
      have hmemWorking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
        exact hmemOriginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) chore).mp hmemWorking |>.2
    · right
      have hmemOriginal : chore ∈ m2TypeChorePool cost m2Chores secondType :=
        (mem_m2TypeChorePool cost m2Chores secondType chore).mpr ⟨hchore, hsecondType⟩
      have hmemWorking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({2, 3} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
        exact hmemOriginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4)) chore).mp hmemWorking |>.2
  have hfirstPool : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) = m2TypeChorePool cost m2Chores firstType := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
  have hsecondPool : m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)) = m2TypeChorePool cost m2Chores secondType := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
  have hcountWorking : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4))).card := by
    rw [hfirstPool, hsecondPool]
    exact hcount
  exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints_of_relabelled_types Item r cost labels
    prefixChores m2Chores a quota prefixAllocation item second hr hcost hprefixM2 hprefixSmall
    hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hitemWorking hsecondWorking
    hm2SmallWorking htypesWorking hcountWorking hprefixZeroSmall hprefixOneSmall

/-- The M01 own-small sets are disjoint across distinct agents, so their
aggregate cardinality is at most the prefix size.  This local copy makes the
counting fact available to the B.4 outer dispatcher without widening the
upstream library surface. -/
private theorem b3_sum_ownSmallChoreSet_card_le
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

/-- In the B.4.2(b) alternative, two heavy endpoints of the first matching
edge leave a light endpoint on the other matching edge.  This is the M01
ownership count which selects the short agent for the heavy-endpoint prefix. -/
theorem b3_matching_light_otherEndpoint_of_heavy
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (a : ℕ)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hheavyZero : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card)
    (hheavyOne : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 1).card) :
    (ownSmallChoreSet cost prefixChores 2).card ≤ 2 * a ∨
      (ownSmallChoreSet cost prefixChores 3).card ≤ 2 * a := by
  have htotal : (ownSmallChoreSet cost prefixChores 0).card +
      (ownSmallChoreSet cost prefixChores 1).card +
      (ownSmallChoreSet cost prefixChores 2).card +
      (ownSmallChoreSet cost prefixChores 3).card ≤ prefixChores.card := by
    simpa [Fin.sum_univ_four, Nat.add_assoc] using
      b3_sum_ownSmallChoreSet_card_le Item cost prefixChores hprefixSmall
  by_cases hlightTwo : (ownSmallChoreSet cost prefixChores 2).card ≤ 2 * a
  · exact Or.inl hlightTwo
  right
  by_contra hnotLightThree
  have hheavyTwo : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 2).card := by
    omega
  have hheavyThree : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 3).card := by
    omega
  rw [hprefixCard] at htotal
  omega

/-- Select the super-canonical B.4.2(b) prefix after the endpoints `0,1` of
the first matching type have been shown heavy.  The returned working labels
are either the identity or the swap of `2,3`, so both matching edge types
retain their displayed names. -/
theorem existsB3MatchingHeavyPrefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hheavyZero : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card)
    (hheavyOne : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 1).card) :
    ∃ labels : Fin 4 ≃ Fin 4, ∃ quota : Fin 4 → ℕ,
      ∃ prefixAllocation : Allocation (Fin 4) Item,
        (labels = Equiv.refl (Fin 4) ∨ labels = Equiv.swap 2 3) ∧
        IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
          prefixChores quota prefixAllocation ∧
        quota 0 = a + 1 ∧ quota 1 = a + 1 ∧ quota 2 = a + 1 ∧ quota 3 = a ∧
        (∀ own comparison, quota own = a → quota comparison = a + 1 →
          additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
            additiveChoreCost (relabelChoreCost labels cost) own
              (prefixAllocation comparison) - r) ∧
        (∀ chore ∈ prefixAllocation 0,
          IsSmallChore (relabelChoreCost labels cost) 0 chore) ∧
        (∀ chore ∈ prefixAllocation 1,
          IsSmallChore (relabelChoreCost labels cost) 1 chore) := by
  rcases b3_matching_light_otherEndpoint_of_heavy Item cost prefixChores a hprefixCard
      hprefixSmall hheavyZero hheavyOne with hlightTwo | hlightThree
  · let originalQuota : Fin 4 → ℕ :=
      canonicalQuota a (Finset.univ \ ({2} : Finset (Fin 4)))
    obtain ⟨originalPrefix, horiginalCanonical, horiginalSuper⟩ :=
      existsSuperCanonicalOfShortLight Item r cost prefixChores ({2} : Finset (Fin 4))
        (Finset.univ \ ({2} : Finset (Fin 4))) a 3 (by linarith) hcost (by omega)
        hprefixSmall hprefixCard rfl (by simp) (by simpa using hlightTwo)
    have horiginalZeroQuota : originalQuota 0 = a + 1 := by
      simp [originalQuota, canonicalQuota]
    have horiginalOneQuota : originalQuota 1 = a + 1 := by
      simp [originalQuota, canonicalQuota]
    have horiginalZeroSmall : ∀ chore ∈ originalPrefix 0, IsSmallChore cost 0 chore :=
      canonical_bundle_all_small_of_quota_le_ownSmall Item cost prefixChores originalQuota
        originalPrefix 0 horiginalCanonical (by rw [horiginalZeroQuota]; omega)
    have horiginalOneSmall : ∀ chore ∈ originalPrefix 1, IsSmallChore cost 1 chore :=
      canonical_bundle_all_small_of_quota_le_ownSmall Item cost prefixChores originalQuota
        originalPrefix 1 horiginalCanonical (by rw [horiginalOneQuota]; omega)
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
    let quota : Fin 4 → ℕ := relabelQuota labels originalQuota
    let prefixAllocation : Allocation (Fin 4) Item := relabelAllocation labels originalPrefix
    refine ⟨labels, quota, prefixAllocation, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [quota, prefixAllocation] using
        horiginalCanonical.relabel labels cost prefixChores originalQuota originalPrefix
    · simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    · simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    · simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    · simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    · intro own comparison hown hcomparison
      exact horiginalSuper (labels own) (labels comparison)
        (by simpa [quota, relabelQuota] using hown)
        (by simpa [quota, relabelQuota] using hcomparison)
    · simpa [labels, prefixAllocation, relabelAllocation, relabelChoreCost,
        Equiv.swap_apply_def] using horiginalZeroSmall
    · simpa [labels, prefixAllocation, relabelAllocation, relabelChoreCost,
        Equiv.swap_apply_def] using horiginalOneSmall
  · let quota : Fin 4 → ℕ := canonicalQuota a (Finset.univ \ ({3} : Finset (Fin 4)))
    obtain ⟨prefixAllocation, hcanonical, hsuper⟩ :=
      existsSuperCanonicalOfShortLight Item r cost prefixChores ({3} : Finset (Fin 4))
        (Finset.univ \ ({3} : Finset (Fin 4))) a 3 (by linarith) hcost (by omega)
        hprefixSmall hprefixCard rfl (by simp) (by simpa using hlightThree)
    have hquota0 : quota 0 = a + 1 := by simp [quota, canonicalQuota]
    have hquota1 : quota 1 = a + 1 := by simp [quota, canonicalQuota]
    have hzeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore :=
      canonical_bundle_all_small_of_quota_le_ownSmall Item cost prefixChores quota
        prefixAllocation 0 hcanonical (by rw [hquota0]; omega)
    have honeSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore :=
      canonical_bundle_all_small_of_quota_le_ownSmall Item cost prefixChores quota
        prefixAllocation 1 hcanonical (by rw [hquota1]; omega)
    refine ⟨Equiv.refl (Fin 4), quota, prefixAllocation, Or.inl rfl, ?_,
      hquota0, hquota1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [relabelChoreCost] using hcanonical
    · simp [quota, canonicalQuota]
    · simp [quota, canonicalQuota]
    · simpa [relabelChoreCost] using hsuper
    · simpa [relabelChoreCost] using hzeroSmall
    · simpa [relabelChoreCost] using honeSmall

/-- The B.4.2(b) source alternative is now closed from its literal premise:
neither endpoint of the first matching type is short in a super-canonical
M01 prefix.  The heavy-count prefix selector above supplies the working-label
prefix, and the relabelled heavy-endpoint schedule finishes the M01--M2 pool. -/
theorem existsEfxOfM01M2_b3_disjoint_heavyEndpoints_of_no_short
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (item second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost chore = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card)
    (hnoSuperZero : ¬ ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hnoSuperOne : ¬ ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hheavyZero : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card :=
    heavy_ownSmall_of_no_supercanonical_short Item r cost prefixChores a 0 hr hcost
      hprefixCard hprefixSmall hnoSuperZero
  have hheavyOne : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 1).card :=
    heavy_ownSmall_of_no_supercanonical_short Item r cost prefixChores a 1 hr hcost
      hprefixCard hprefixSmall hnoSuperOne
  obtain ⟨labels, quota, prefixAllocation, hlabels, hcanonical, hquota0, hquota1,
    hquota2, hquota3, hsuper, hzeroSmall, honeSmall⟩ :=
    existsB3MatchingHeavyPrefix Item r cost prefixChores a hr hcost hprefixCard hprefixSmall
      hheavyZero hheavyOne
  have hprefixSmallWorking : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForAtMostOne.relabel labels cost chore (hprefixSmall chore hchore)
  have hmapFirst : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding =
      ({0, 1} : Finset (Fin 4)) := by
    rcases hlabels with rfl | rfl <;> decide
  have hmapSecond : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding =
      ({2, 3} : Finset (Fin 4)) := by
    rcases hlabels with rfl | rfl <;> decide
  exact existsEfxOfM01M2_b3_matching_heavyEndpoints_of_normalized_prefix Item r cost
    labels prefixChores m2Chores a quota prefixAllocation item second
    ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) hr hcost hprefixM2 hmapFirst
    hmapSecond hprefixSmallWorking hcanonical hquota0 hquota1 hquota2 hquota3 hsuper
    hitem hsecond hm2Small htypes hcount hzeroSmall honeSmall

/-- Complete fixed-label source Case B.4.2.  The first two branches are
B.4.2(a), choosing a super-canonical prefix with endpoint `0` or `1` short.
If neither exists, the source's B.4.2(b) heavy-endpoint construction applies. -/
theorem existsEfxOfM01M2_b3_disjoint_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (item second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost chore = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hresidueCount : ((m2Chores \ {item, second}).filter
      fun chore => smallAgentSet cost chore = ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {item, second}).filter
        fun chore => smallAgentSet cost chore = ({2, 3} : Finset (Fin 4))).card :=
    matching_residual_type_count_le Item cost m2Chores item second
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) (by decide) (by decide)
      hitem hsecond hcount
  by_cases hshortZero : ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r
  · obtain ⟨prefixAllocation, hcanonical, hsuper⟩ := hshortZero
    exact existsEfxOfM01M2_b3_disjoint_shortEndpoint Item r cost prefixChores m2Chores a
      (canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))) prefixAllocation item second
      hr hcost hprefixM2 hcanonical (by simp [canonicalQuota]) (by simp [canonicalQuota])
      (by simp [canonicalQuota]) (by simp [canonicalQuota]) hsuper hitem hsecond htypes
      hresidueCount
  by_cases hshortOne : ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r
  · obtain ⟨originalPrefix, horiginalCanonical, horiginalSuper⟩ := hshortOne
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
    let originalQuota : Fin 4 → ℕ :=
      canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4)))
    let quota : Fin 4 → ℕ := relabelQuota labels originalQuota
    let prefixAllocation : Allocation (Fin 4) Item := relabelAllocation labels originalPrefix
    have hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
        prefixChores quota prefixAllocation := by
      simpa [quota, prefixAllocation, originalQuota] using
        horiginalCanonical.relabel labels cost prefixChores originalQuota originalPrefix
    have hquota0 : quota 0 = a := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    have hquota1 : quota 1 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    have hquota2 : quota 2 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    have hquota3 : quota 3 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    have hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
          additiveChoreCost (relabelChoreCost labels cost) own
            (prefixAllocation comparison) - r := by
      intro own comparison hown hcomparison
      exact horiginalSuper (labels own) (labels comparison)
        (by simpa [quota, relabelQuota, originalQuota] using hown)
        (by simpa [quota, relabelQuota, originalQuota] using hcomparison)
    exact existsEfxOfM01M2_b3_matching_shortEndpoint_of_normalized_prefix Item r cost
      labels prefixChores m2Chores a quota prefixAllocation item second
      ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) hr hcost hprefixM2
      (by
        simpa [labels] using
          (by decide : ({0, 1} : Finset (Fin 4)).map (Equiv.swap 0 1).toEmbedding =
            ({0, 1} : Finset (Fin 4))))
      (by
        simpa [labels] using
          (by decide : ({2, 3} : Finset (Fin 4)).map (Equiv.swap 0 1).toEmbedding =
            ({2, 3} : Finset (Fin 4)))) hcanonical hquota0 hquota1 hquota2 hquota3
      hsuper hitem hsecond htypes hresidueCount
  exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints_of_no_short Item r cost
    prefixChores m2Chores a item second hr hcost hprefixM2 hprefixCard hprefixSmall hitem
    hsecond hm2Small htypes hcount hshortZero hshortOne

/-- Complete fixed-label source Case B.4.3.  As in the matching case, a
super-canonical prefix with endpoint `0` or `1` short enters B.4.3(a); if
neither exists, the two endpoints are heavy and B.4.3(b) applies. -/
theorem existsEfxOfM01M2_b3_oneType_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hshortZero : ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r
  · obtain ⟨prefixAllocation, hcanonical, hsuper⟩ := hshortZero
    exact existsEfxOfM01M2_b3_oneType_shortEndpoint Item r cost prefixChores m2Chores a
      (canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))) prefixAllocation
      hr hcost hprefixM2 hprefixSmall hcanonical (by simp [canonicalQuota])
      (by simp [canonicalQuota]) (by simp [canonicalQuota]) (by simp [canonicalQuota])
      hsuper hm2Type
  by_cases hshortOne : ∃ prefixAllocation,
      IsCanonicalSmallChoreAllocation cost prefixChores
        (canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4)))) prefixAllocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) own = a →
        canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4))) comparison = a + 1 →
        additiveChoreCost cost own (prefixAllocation own) ≤
          additiveChoreCost cost own (prefixAllocation comparison) - r
  · obtain ⟨originalPrefix, horiginalCanonical, horiginalSuper⟩ := hshortOne
    let labels : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
    let originalQuota : Fin 4 → ℕ :=
      canonicalQuota a (Finset.univ \ ({1} : Finset (Fin 4)))
    let quota : Fin 4 → ℕ := relabelQuota labels originalQuota
    let prefixAllocation : Allocation (Fin 4) Item := relabelAllocation labels originalPrefix
    have hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
        prefixChores quota prefixAllocation := by
      simpa [quota, prefixAllocation, originalQuota] using
        horiginalCanonical.relabel labels cost prefixChores originalQuota originalPrefix
    have hquota0 : quota 0 = a := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    have hquota1 : quota 1 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota]
    have hquota2 : quota 2 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    have hquota3 : quota 3 = a + 1 := by
      simp [labels, quota, originalQuota, relabelQuota, canonicalQuota, Equiv.swap_apply_def]
    have hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
          additiveChoreCost (relabelChoreCost labels cost) own
            (prefixAllocation comparison) - r := by
      intro own comparison hown hcomparison
      exact horiginalSuper (labels own) (labels comparison)
        (by simpa [quota, relabelQuota, originalQuota] using hown)
        (by simpa [quota, relabelQuota, originalQuota] using hcomparison)
    have hprefixSmallWorking : ∀ chore ∈ prefixChores,
        IsSmallForAtMostOne (relabelChoreCost labels cost) chore := by
      intro chore hchore
      exact IsSmallForAtMostOne.relabel labels cost chore (hprefixSmall chore hchore)
    have htypeMap : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding =
        ({0, 1} : Finset (Fin 4)) := by
      simpa [labels] using
        (by decide : ({0, 1} : Finset (Fin 4)).map (Equiv.swap 0 1).toEmbedding =
          ({0, 1} : Finset (Fin 4)))
    have hm2TypeWorking : ∀ chore ∈ m2Chores,
        smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) := by
      intro chore hchore
      have horiginal : chore ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) :=
        (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) chore).mpr
          ⟨hchore, hm2Type chore hchore⟩
      have hworking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), htypeMap]
        exact horiginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) chore).mp hworking |>.2
    exact existsEfxOfM01M2_b3_oneType_shortEndpoint_of_relabelled_type Item r cost labels
      prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2 hprefixSmallWorking
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2TypeWorking
  have hheavyZero : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card :=
    heavy_ownSmall_of_no_supercanonical_short Item r cost prefixChores a 0 hr hcost
      hprefixCard hprefixSmall hshortZero
  have hheavyOne : 2 * a + 1 ≤ (ownSmallChoreSet cost prefixChores 1).card :=
    heavy_ownSmall_of_no_supercanonical_short Item r cost prefixChores a 1 hr hcost
      hprefixCard hprefixSmall hshortOne
  obtain ⟨labels, quota, prefixAllocation, hlabels, hcanonical, hquota0, hquota1,
    hquota2, hquota3, hsuper, hzeroSmall, honeSmall⟩ :=
    existsB3MatchingHeavyPrefix Item r cost prefixChores a hr hcost hprefixCard hprefixSmall
      hheavyZero hheavyOne
  have htypeMap : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding =
      ({0, 1} : Finset (Fin 4)) := by
    rcases hlabels with rfl | rfl <;> decide
  have hitemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), htypeMap]
    exact hitem
  have hm2SmallWorking : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForExactlyTwo.relabel labels cost chore (hm2Small chore hchore)
  have hm2TypeWorking : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    have horiginal : chore ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) :=
      (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) chore).mpr
        ⟨hchore, hm2Type chore hchore⟩
    have hworking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) := by
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), htypeMap]
      exact horiginal
    exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) chore).mp hworking |>.2
  exact existsEfxOfM01M2_b3_oneType_heavyEndpoints_of_relabelled_type Item r cost labels
    prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hcanonical hquota0
    hquota1 hquota2 hquota3 hsuper hitemWorking hm2SmallWorking hm2TypeWorking hzeroSmall
    honeSmall

/-- Transport the complete B.4.2 matching dispatcher from the displayed
working labels to arbitrary two-type matching support. -/
theorem existsEfxOfM01M2_b3_matching_dispatch_of_relabelled_types
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (item second : Item) (firstType secondType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hmapFirst : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType)
    (hmapSecond : ({2, 3} : Finset (Fin 4)).map labels.toEmbedding = secondType)
    (hitem : item ∈ m2TypeChorePool cost m2Chores firstType)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores secondType)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = firstType ∨ smallAgentSet cost chore = secondType)
    (hcount : (m2TypeChorePool cost m2Chores firstType).card ≤
      (m2TypeChorePool cost m2Chores secondType).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hprefixSmallWorking : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForAtMostOne.relabel labels cost chore (hprefixSmall chore hchore)
  have hitemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
    exact hitem
  have hsecondWorking : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
    exact hsecond
  have hm2SmallWorking : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForExactlyTwo.relabel labels cost chore (hm2Small chore hchore)
  have htypesWorking : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet (relabelChoreCost labels cost) chore = ({2, 3} : Finset (Fin 4)) := by
    intro chore hchore
    rcases htypes chore hchore with hfirstType | hsecondType
    · left
      have horiginal : chore ∈ m2TypeChorePool cost m2Chores firstType :=
        (mem_m2TypeChorePool cost m2Chores firstType chore).mpr ⟨hchore, hfirstType⟩
      have hworking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
        exact horiginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) chore).mp hworking |>.2
    · right
      have horiginal : chore ∈ m2TypeChorePool cost m2Chores secondType :=
        (mem_m2TypeChorePool cost m2Chores secondType chore).mpr ⟨hchore, hsecondType⟩
      have hworking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({2, 3} : Finset (Fin 4)) := by
        rw [m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
        exact horiginal
      exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4)) chore).mp hworking |>.2
  have hcountWorking : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4))).card := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst,
      m2TypeChorePool_relabel labels cost m2Chores ({2, 3} : Finset (Fin 4)), hmapSecond]
    exact hcount
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_disjoint_dispatch Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a item second hr (IsOneOrRChoreCost.relabel labels cost r hcost)
    hprefixM2 hprefixCard hprefixSmallWorking hitemWorking hsecondWorking hm2SmallWorking
    htypesWorking hcountWorking

/-- Transport the complete B.4.3 fixed-type dispatcher from working type
`(0,1)` to an arbitrary two-agent M₂ type. -/
theorem existsEfxOfM01M2_b3_oneType_dispatch_of_relabelled_type
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (item : Item) (edgeType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hmap : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = edgeType)
    (hitem : item ∈ m2TypeChorePool cost m2Chores edgeType)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm2Type : ∀ chore ∈ m2Chores, smallAgentSet cost chore = edgeType) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hprefixSmallWorking : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForAtMostOne.relabel labels cost chore (hprefixSmall chore hchore)
  have hitemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap]
    exact hitem
  have hm2SmallWorking : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForExactlyTwo.relabel labels cost chore (hm2Small chore hchore)
  have hm2TypeWorking : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    have horiginal : chore ∈ m2TypeChorePool cost m2Chores edgeType :=
      (mem_m2TypeChorePool cost m2Chores edgeType chore).mpr ⟨hchore, hm2Type chore hchore⟩
    have hworking : chore ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({0, 1} : Finset (Fin 4)) := by
      rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmap]
      exact horiginal
    exact (mem_m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) chore).mp hworking |>.2
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_oneType_dispatch Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a item hr (IsOneOrRChoreCost.relabel labels cost r hcost)
    hprefixM2 hprefixCard hprefixSmallWorking hitemWorking hm2SmallWorking hm2TypeWorking

/-- Transport the complete B.4.1 dispatcher from a maximum intersecting pair
named `(0,1),(0,2)` in working labels to arbitrary original edge types. -/
theorem existsEfxOfM01M2_b3_intersectingMaximum_of_relabelled_types
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (item second : Item) (firstType secondType : Finset (Fin 4))
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hmapFirst : ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = firstType)
    (hmapSecond : ({0, 2} : Finset (Fin 4)).map labels.toEmbedding = secondType)
    (hitem : item ∈ m2TypeChorePool cost m2Chores firstType)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores secondType)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores firstType).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  have hprefixSmallWorking : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForAtMostOne.relabel labels cost chore (hprefixSmall chore hchore)
  have hitemWorking : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
    exact hitem
  have hsecondWorking : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 2} : Finset (Fin 4)) := by
    rw [m2TypeChorePool_relabel labels cost m2Chores ({0, 2} : Finset (Fin 4)), hmapSecond]
    exact hsecond
  have hm2SmallWorking : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore := by
    intro chore hchore
    exact IsSmallForExactlyTwo.relabel labels cost chore (hm2Small chore hchore)
  have hmaximumWorking : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores edgeType).card ≤
        (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
          ({0, 1} : Finset (Fin 4))).card := by
    intro edgeType
    rw [m2TypeChorePool_relabel labels cost m2Chores edgeType,
      m2TypeChorePool_relabel labels cost m2Chores ({0, 1} : Finset (Fin 4)), hmapFirst]
    exact hmaximum (edgeType.map labels.toEmbedding)
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_intersectingMaximum Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a item second hr (IsOneOrRChoreCost.relabel labels cost r hcost)
    hprefixM2 hprefixCard hprefixSmallWorking hm2SmallWorking hitemWorking hsecondWorking
    hmaximumWorking

/-- Complete source Case B.4.  A maximum M₂ edge type is selected over the
six two-agent types.  Intersecting support is routed through B.4.1, exactly
two disjoint support types through B.4.2 (in multiplicity order), and a fixed
type through B.4.3. -/
theorem existsEfxOfB3_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hprefixM2 : Disjoint prefixChores m2Chores) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  classical
  let edgeTypes : Finset (Finset (Fin 4)) :=
    (Finset.univ : Finset (Finset (Fin 4))).filter fun edgeType => edgeType.card = 2
  have hedgeTypesNonempty : edgeTypes.Nonempty := by
    refine ⟨({0, 1} : Finset (Fin 4)), ?_⟩
    simp [edgeTypes]
  obtain ⟨maximumType, hmaximumMem, hmaximum⟩ := Finset.exists_max_image edgeTypes
    (fun edgeType => (m2TypeChorePool cost m2Chores edgeType).card) hedgeTypesNonempty
  have hmaximumCard : maximumType.card = 2 := by
    simpa [edgeTypes] using hmaximumMem
  have hnonPairEmpty : ∀ edgeType : Finset (Fin 4), edgeType.card ≠ 2 →
      m2TypeChorePool cost m2Chores edgeType = ∅ := by
    intro edgeType hcard
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨chore, hchore⟩ := hnonempty
    obtain ⟨hm2, htype⟩ := (mem_m2TypeChorePool cost m2Chores edgeType chore).mp hchore
    have hsmall : (smallAgentSet cost chore).card = 2 := hm2Small chore hm2
    exact hcard (by rw [← htype]; exact hsmall)
  have hmaximumAll : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores maximumType).card := by
    intro edgeType
    by_cases hcard : edgeType.card = 2
    · exact hmaximum edgeType (by simpa [edgeTypes] using hcard)
    · rw [hnonPairEmpty edgeType hcard]
      exact Nat.zero_le _
  rcases m2_graph_intersecting_or_matching_or_fixed Item cost m2Chores hm2Small with
      hintersecting | hmatching | hfixed
  · rcases hintersecting with ⟨firstType, secondType, hfirstCard, hsecondCard,
        hfirstNeSecond, hnotDisjoint, hfirstNonempty, hsecondNonempty⟩
    have hneighbor : ∃ neighborType : Finset (Fin 4), neighborType.card = 2 ∧
        neighborType ≠ maximumType ∧ ¬ Disjoint maximumType neighborType ∧
        (m2TypeChorePool cost m2Chores neighborType).Nonempty := by
      by_cases hmaxFirst : maximumType = firstType
      · refine ⟨secondType, hsecondCard, ?_, ?_, hsecondNonempty⟩
        · intro hsecondMaximum
          apply hfirstNeSecond
          exact hmaxFirst.symm.trans hsecondMaximum.symm
        · simpa [hmaxFirst] using hnotDisjoint
      by_cases hmaxSecond : maximumType = secondType
      · refine ⟨firstType, hfirstCard, ?_, ?_, hfirstNonempty⟩
        · intro hfirstMaximum
          apply hfirstNeSecond
          exact hfirstMaximum.trans hmaxSecond
        · intro hdisjoint
          apply hnotDisjoint
          simpa [hmaxSecond] using hdisjoint.symm
      by_cases hinterFirst : ¬ Disjoint maximumType firstType
      · exact ⟨firstType, hfirstCard, Ne.symm hmaxFirst, hinterFirst, hfirstNonempty⟩
      by_cases hinterSecond : ¬ Disjoint maximumType secondType
      · exact ⟨secondType, hsecondCard, Ne.symm hmaxSecond, hinterSecond, hsecondNonempty⟩
      have hdisjointFirst : Disjoint maximumType firstType := not_not.mp hinterFirst
      have hdisjointSecond : Disjoint maximumType secondType := not_not.mp hinterSecond
      have hfirstComplement : firstType = maximumTypeᶜ := by
        have hsubset : firstType ⊆ maximumTypeᶜ := by
          intro agent hfirst
          simp only [Finset.mem_compl]
          intro hmaximum
          exact (Finset.disjoint_left.mp hdisjointFirst hmaximum hfirst).elim
        apply Finset.eq_of_subset_of_card_le hsubset
        rw [Finset.card_compl, hmaximumCard, hfirstCard]
        norm_num
      have hsecondComplement : secondType = maximumTypeᶜ := by
        have hsubset : secondType ⊆ maximumTypeᶜ := by
          intro agent hsecond
          simp only [Finset.mem_compl]
          intro hmaximum
          exact (Finset.disjoint_left.mp hdisjointSecond hmaximum hsecond).elim
        apply Finset.eq_of_subset_of_card_le hsubset
        rw [Finset.card_compl, hmaximumCard, hsecondCard]
        norm_num
      exact False.elim (hfirstNeSecond (hfirstComplement.trans hsecondComplement.symm))
    obtain ⟨neighborType, hneighborCard, hmaximumNeNeighbor, hneighborIntersects,
      hneighborNonempty⟩ := hneighbor
    have hmaximumPositive : 0 < (m2TypeChorePool cost m2Chores maximumType).card := by
      have hfirstPositive : 0 < (m2TypeChorePool cost m2Chores firstType).card :=
        Finset.card_pos.mpr hfirstNonempty
      exact lt_of_lt_of_le hfirstPositive (hmaximumAll firstType)
    obtain ⟨item, hitem⟩ := Finset.card_pos.mp hmaximumPositive
    obtain ⟨second, hsecond⟩ := hneighborNonempty
    obtain ⟨labels, hmapFirst, hmapSecond⟩ :=
      exists_intersecting_type_relabelling maximumType neighborType hmaximumCard hneighborCard
        hmaximumNeNeighbor.symm hneighborIntersects
    exact existsEfxOfM01M2_b3_intersectingMaximum_of_relabelled_types Item r cost labels
      prefixChores m2Chores a item second maximumType neighborType hr hcost hprefixM2
      hprefixCard hprefixSmall hmapFirst hmapSecond hitem hsecond hm2Small hmaximumAll
  · rcases hmatching with ⟨firstType, secondType, hfirstCard, hsecondCard, hdisjoint,
        hfirstNonempty, hsecondNonempty, htypes⟩
    obtain ⟨first, hfirst⟩ := hfirstNonempty
    obtain ⟨second, hsecond⟩ := hsecondNonempty
    by_cases hcount : (m2TypeChorePool cost m2Chores firstType).card ≤
        (m2TypeChorePool cost m2Chores secondType).card
    · obtain ⟨labels, hmapFirst, hmapSecond⟩ :=
        exists_matching_type_relabelling firstType secondType hfirstCard hsecondCard hdisjoint
      exact existsEfxOfM01M2_b3_matching_dispatch_of_relabelled_types Item r cost labels
        prefixChores m2Chores a first second firstType secondType hr hcost hprefixM2 hprefixCard
        hprefixSmall hmapFirst hmapSecond hfirst hsecond hm2Small htypes hcount
    · have hreverseCount : (m2TypeChorePool cost m2Chores secondType).card ≤
          (m2TypeChorePool cost m2Chores firstType).card := by omega
      obtain ⟨labels, hmapSecond, hmapFirst⟩ :=
        exists_matching_type_relabelling secondType firstType hsecondCard hfirstCard hdisjoint.symm
      have htypesReverse : ∀ chore ∈ m2Chores,
          smallAgentSet cost chore = secondType ∨ smallAgentSet cost chore = firstType := by
        intro chore hchore
        rcases htypes chore hchore with hfirstType | hsecondType
        · exact Or.inr hfirstType
        · exact Or.inl hsecondType
      exact existsEfxOfM01M2_b3_matching_dispatch_of_relabelled_types Item r cost labels
        prefixChores m2Chores a second first secondType firstType hr hcost hprefixM2 hprefixCard
        hprefixSmall hmapSecond hmapFirst hsecond hfirst hm2Small htypesReverse hreverseCount
  · rcases hfixed with ⟨edgeType, hedgeCard, hm2Type⟩
    by_cases hm2Empty : m2Chores = ∅
    · let quota : Fin 4 → ℕ := canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4)))
      have hlongCard : (Finset.univ \ ({0} : Finset (Fin 4))).card = 3 := by decide
      have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
        rw [show quota = canonicalQuota a (Finset.univ \ ({0} : Finset (Fin 4))) by rfl,
          canonicalQuota_sum, hlongCard, hprefixCard]
      obtain ⟨prefixAllocation, hcanonical⟩ :=
        existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
      have hbalanced : ∀ first second, quota first ≤ quota second + 1 := by
        intro first second
        by_cases hfirst : first = 0 <;> by_cases hsecond : second = 0 <;>
          simp [quota, canonicalQuota, hfirst, hsecond] <;> omega
      have hefx : EFXForChores (additiveChoreCost cost) prefixAllocation :=
        hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
          hbalanced
      exact ⟨prefixAllocation, by simpa [hm2Empty] using hcanonical.1, hefx⟩
    obtain ⟨item, hitemM2⟩ := Finset.nonempty_iff_ne_empty.mpr hm2Empty
    have hitem : item ∈ m2TypeChorePool cost m2Chores edgeType :=
      (mem_m2TypeChorePool cost m2Chores edgeType item).mpr ⟨hitemM2, hm2Type item hitemM2⟩
    have hcomplementCard : edgeTypeᶜ.card = 2 := by
      rw [Finset.card_compl, hedgeCard]
      norm_num
    obtain ⟨labels, hmap, _⟩ :=
      exists_matching_type_relabelling edgeType edgeTypeᶜ hedgeCard hcomplementCard (by
        rw [Finset.disjoint_left]
        intro agent hedge hcomplement
        simp only [Finset.mem_compl] at hcomplement
        exact hcomplement hedge)
    exact existsEfxOfM01M2_b3_oneType_dispatch_of_relabelled_type Item r cost labels
      prefixChores m2Chores a item edgeType hr hcost hprefixM2 hprefixCard hprefixSmall hmap
      hitem hm2Small hm2Type

/-- The complete B.4 dispatcher remains valid after the paper's final M34
insertion phase. -/
theorem existsEfxOfM01M2M34_b3
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm34Small : ∀ chore ∈ m34Chores, IsSmallForAtLeastThree cost chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfB3_dispatch Item r cost prefixChores m2Chores a hr hcost hprefixCard
      hprefixSmall hm2Small hprefixM2
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro chore hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Every normalized high-ratio instance whose M01 pool has remainder three
admits EFX. -/
theorem existsEfxOfOneOrR_b3
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcard : (m01ChorePool cost chores).card = 4 * a + 3) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M2M34_b3 Item r cost (m01ChorePool cost chores)
      (m2ChorePool cost chores) (m34ChorePool cost chores) a hr hcost
      (m01ChorePool_disjoint_m2ChorePool cost chores)
      (m01ChorePool_disjoint_m34ChorePool cost chores)
      (m2ChorePool_disjoint_m34ChorePool cost chores) hcard
      (m01ChorePool_small cost chores) (m2ChorePool_small cost chores)
      (m34ChorePool_small cost chores)
  refine ⟨allocation, ?_, hefx⟩
  simpa only [← Finset.union_assoc, m01_m2_m34_union_eq] using hallocation

end HT26EFXChores
