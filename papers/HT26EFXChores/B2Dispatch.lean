import HT26EFXChores.B2MaxMultiplicityDispatch
import HT26EFXChores.M34Extension

/-!
# Outer dispatch for source Case B.3

The source's `b = 2` analysis first fixes the two short prefix agents by a
relabelling.  This module keeps that relabelling bridge explicit before
combining the maximum-multiplicity and simple-graph source cases.

Source: `EFXadditivechores.tex`, lines 2543--2996.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- The complete simple-graph B.3.2 schedule transports across a relabelling
that names its two short prefix agents `0` and `1`. -/
theorem existsEfxOfB2SimpleGraph_of_relabelled_prefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota (labels 0) = a) (hquota1 : quota (labels 1) = a)
    (hquota2 : quota (labels 2) = a + 1) (hquota3 : quota (labels 3) = a + 1)
    (hsuper : ∀ short long : Fin 4, quota short = a → quota long = a + 1 →
      additiveChoreCost cost short (prefixAllocation short) ≤
        additiveChoreCost cost short (prefixAllocation long) - r)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores smallAgents).card ≤ 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  apply existsEfxOfB2SimpleGraph Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a (relabelQuota labels quota) (relabelAllocation labels prefixAllocation)
  · exact hr
  · exact IsOneOrRChoreCost.relabel labels cost r hcost
  · intro item hitem
    exact IsSmallForExactlyTwo.relabel labels cost item (hm2Small item hitem)
  · exact hprefixM2
  · intro item hitem
    exact IsSmallForAtMostOne.relabel labels cost item (hprefixSmall item hitem)
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

/-- A quota vector of total size `4a+2` with entries in `{a,a+1}` has two
short and two long agents.  This finite relabelling names the short agents
`0,1` and the long agents `2,3`. -/
theorem exists_b2_quota_relabelling
    (a : ℕ) (quota : Fin 4 → ℕ)
    (hquota : ∀ agent, quota agent = a ∨ quota agent = a + 1)
    (hsum : Finset.univ.sum quota = 4 * a + 2) :
    ∃ labels : Fin 4 ≃ Fin 4,
      quota (labels 0) = a ∧ quota (labels 1) = a ∧
        quota (labels 2) = a + 1 ∧ quota (labels 3) = a + 1 := by
  have hsumFour : quota 0 + quota 1 + quota 2 + quota 3 = 4 * a + 2 := by
    simpa [Fin.sum_univ_four, Nat.add_assoc] using hsum
  rcases hquota 0 with h0 | h0
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3 <;> omega
      · rcases hquota 3 with h3 | h3
        · omega
        · exact ⟨Equiv.refl (Fin 4), h0, h1, h2, h3⟩
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · omega
        · refine ⟨Equiv.swap 1 2, ?_, ?_, ?_, ?_⟩
          · simpa [Equiv.swap_apply_def] using h0
          · simpa [Equiv.swap_apply_def] using h2
          · simpa [Equiv.swap_apply_def] using h1
          · simpa [Equiv.swap_apply_def] using h3
      · rcases hquota 3 with h3 | h3
        · refine ⟨Equiv.swap 1 3, ?_, ?_, ?_, ?_⟩
          · simpa [Equiv.swap_apply_def] using h0
          · simpa [Equiv.swap_apply_def] using h3
          · simpa [Equiv.swap_apply_def] using h2
          · simpa [Equiv.swap_apply_def] using h1
        · omega
  · rcases hquota 1 with h1 | h1
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · omega
        · refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), ?_, ?_, ?_, ?_⟩
          · simpa [Equiv.swap_apply_def] using h1
          · simpa [Equiv.swap_apply_def] using h2
          · simpa [Equiv.swap_apply_def] using h0
          · simpa [Equiv.swap_apply_def] using h3
      · rcases hquota 3 with h3 | h3
        · refine ⟨(Equiv.swap 1 3).trans (Equiv.swap 0 1), ?_, ?_, ?_, ?_⟩
          · simpa [Equiv.swap_apply_def] using h1
          · simpa [Equiv.swap_apply_def] using h3
          · simpa [Equiv.swap_apply_def] using h2
          · simpa [Equiv.swap_apply_def] using h0
        · omega
    · rcases hquota 2 with h2 | h2
      · rcases hquota 3 with h3 | h3
        · refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), ?_, ?_, ?_, ?_⟩
          · simpa [Equiv.swap_apply_def] using h2
          · simpa [Equiv.swap_apply_def] using h3
          · simpa [Equiv.swap_apply_def] using h0
          · simpa [Equiv.swap_apply_def] using h1
        · omega
      · rcases hquota 3 with h3 | h3 <;> omega

/-- Complete source Case B.3.2 for a simple M₂ graph.  A super-canonical
prefix is first relabelled so that its two short agents are the displayed
source labels, then the exhaustive simple-graph scheduler applies. -/
theorem existsEfxOfB2SimpleGraph_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hsimple : ∀ smallAgents : Finset (Fin 4), smallAgents.card = 2 →
      (m2TypeChorePool cost m2Chores smallAgents).card ≤ 1) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨quota, prefixAllocation, hquota, hcanonical, hsuper⟩ :=
    existsSuperCanonicalSmallChoreAllocation Item r cost prefixChores a 2 (by linarith)
      hcost (by omega) (by omega) hprefixCard hprefixSmall
  have hquotaSum : Finset.univ.sum quota = 4 * a + 2 := by
    calc
      Finset.univ.sum quota = Finset.univ.sum (fun agent => (prefixAllocation agent).card) := by
        apply Finset.sum_congr rfl
        intro agent _
        symm
        exact (hcanonical.2 agent).1
      _ = prefixChores.card :=
        sum_card_allocation_eq_card_of_isAllocation prefixAllocation prefixChores hcanonical.1
      _ = 4 * a + 2 := hprefixCard
  obtain ⟨labels, hquota0, hquota1, hquota2, hquota3⟩ :=
    exists_b2_quota_relabelling a quota hquota hquotaSum
  apply existsEfxOfB2SimpleGraph_of_relabelled_prefix Item r cost labels prefixChores m2Chores
    a quota prefixAllocation hr hcost hm2Small hprefixM2 hprefixSmall hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper
  intro smallAgents hsmallAgents
  rw [m2TypeChorePool_relabel labels cost m2Chores smallAgents]
  exact hsimple (smallAgents.map labels.toEmbedding) (by simpa using hsmallAgents)

/-- Every two-element subset of the four source labels is the image of the
displayed pair `(0,1)` under a finite relabelling. -/
theorem exists_b2_type_relabelling
    (edgeType : Finset (Fin 4)) (hcard : edgeType.card = 2) :
    ∃ labels : Fin 4 ≃ Fin 4,
      ({0, 1} : Finset (Fin 4)).map labels.toEmbedding = edgeType := by
  rcases finset_fin4_card_two_eq_one_of_six edgeType hcard with h01 | h02 | h03 | h12 | h13 | h23
  · subst edgeType
    exact ⟨Equiv.refl (Fin 4), by decide⟩
  · subst edgeType
    exact ⟨Equiv.swap 1 2, by decide⟩
  · subst edgeType
    exact ⟨Equiv.swap 1 3, by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 1 3).trans (Equiv.swap 0 1), by decide⟩
  · subst edgeType
    exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), by decide⟩

/-- Complete source Case B.3.  Among the six M₂ edge fibres, choose one of
maximum multiplicity.  If it has at least two chores, B.3.1 applies after a
relabeling; otherwise every fibre is simple and B.3.2 applies. -/
theorem existsEfxOfB2_dispatch
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
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
  have hmaximumTypeCard : maximumType.card = 2 := by
    simpa [edgeTypes] using hmaximumMem
  have hnonPairEmpty : ∀ edgeType : Finset (Fin 4), edgeType.card ≠ 2 →
      m2TypeChorePool cost m2Chores edgeType = ∅ := by
    intro edgeType hcard
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨item, hitem⟩ := hnonempty
    obtain ⟨hm2, htype⟩ := (mem_m2TypeChorePool cost m2Chores edgeType item).mp hitem
    have hsmall : (smallAgentSet cost item).card = 2 := hm2Small item hm2
    exact hcard (by rw [← htype]; exact hsmall)
  have hmaximumAll : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores maximumType).card := by
    intro edgeType
    by_cases hcard : edgeType.card = 2
    · exact hmaximum edgeType (by simpa [edgeTypes] using hcard)
    · rw [hnonPairEmpty edgeType hcard]
      exact Nat.zero_le _
  by_cases hmaximumSmall :
      (m2TypeChorePool cost m2Chores maximumType).card ≤ 1
  · apply existsEfxOfB2SimpleGraph_dispatch Item r cost prefixChores m2Chores a hr hcost
      hprefixCard hprefixSmall hm2Small hprefixM2
    intro edgeType hcard
    exact (hmaximumAll edgeType).trans hmaximumSmall
  · have hmaximumCard : 2 ≤ (m2TypeChorePool cost m2Chores maximumType).card := by
      omega
    obtain ⟨labels, hlabels⟩ := exists_b2_type_relabelling maximumType hmaximumTypeCard
    exact existsEfxOfB2MaximumMultiplicity_of_relabelled_maximum Item r cost labels
      prefixChores m2Chores a maximumType hr hcost hprefixCard hprefixSmall hm2Small hprefixM2
      hmaximumAll hmaximumCard hlabels

/-- The complete `b = 2` source case after restoring M₃₄ chores by the
paper's iterated insertion lemma. -/
theorem existsEfxOfM01M2M34_b2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixM34 : Disjoint prefixChores m34Chores)
    (hm2M34 : Disjoint m2Chores m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 2)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEFX⟩ :=
    existsEfxOfB2_dispatch Item r cost prefixChores m2Chores a hr hcost hprefixCard
      hprefixSmall hm2Small hprefixM2
  have hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores := by
    rw [Finset.disjoint_left]
    intro item hbase hm34
    rcases Finset.mem_union.mp hbase with hprefix | hm2
    · exact (Finset.disjoint_left.mp hprefixM34 hprefix hm34).elim
    · exact (Finset.disjoint_left.mp hm2M34 hm2 hm34).elim
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEFX

/-- Every normalized instance whose M₀₁ pool has remainder two admits EFX. -/
theorem existsEfxOfOneOrR_b2
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcard : (m01ChorePool cost chores).card = 4 * a + 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation chores ∧ EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨allocation, hallocation, hefx⟩ :=
    existsEfxOfM01M2M34_b2 Item r cost (m01ChorePool cost chores)
      (m2ChorePool cost chores) (m34ChorePool cost chores) a hr hcost
      (m01ChorePool_disjoint_m2ChorePool cost chores)
      (m01ChorePool_disjoint_m34ChorePool cost chores)
      (m2ChorePool_disjoint_m34ChorePool cost chores) hcard
      (m01ChorePool_small cost chores) (m2ChorePool_small cost chores)
      (m34ChorePool_small cost chores)
  refine ⟨allocation, ?_, hefx⟩
  simpa only [← Finset.union_assoc, m01_m2_m34_union_eq] using hallocation

end HT26EFXChores
