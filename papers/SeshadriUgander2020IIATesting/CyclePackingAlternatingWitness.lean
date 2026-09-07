import SeshadriUgander2020IIATesting.CyclePackingDecomposition
import SeshadriUgander2020IIATesting.AlternatingCycles

/-!
# Alternating witnesses for concrete incidence-cycle packings

A complete packing of normalized simple incidence cycles provides the concrete
alternating traversal used by source Lemma 2.  This module proves that bridge
directly from the packed graph walks and their endpoint pairings.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

open AppliedModelingLib.Foundations.Graph

variable (F : ChoiceFrame)

noncomputable def packingCycleVertex
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (cycle : P.Cycle) : Type :=
  {position : Fin (((F.normalizedPacking P).walk cycle).2.length) | Even position.1}

/-- An even cycle position represents one choice-set vertex; its incoming
incidence is the positive (`false`) edge and its outgoing incidence the
negative (`true`) edge. -/
noncomputable def packingCycleAlternatingEdgeParamEquiv
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (cycle : P.Cycle) :
    Fin (((F.normalizedPacking P).walk cycle).2.length) ≃
      (F.packingCycleVertex P cycle × Bool) := by
  let walk := (F.normalizedPacking P).walk cycle |>.2
  have hcycle : walk.IsCycle := (F.normalizedPacking P).isCycle cycle
  have hlen : Even walk.length := F.incidence_simpleCycle_even_length hcycle
  exact
    { toFun := fun position =>
        if heven : Even position.1 then (⟨position, heven⟩, true)
        else (⟨simpleCycleNextPosition hcycle position,
          (F.even_nextPosition_iff_not_even hcycle hlen position).mpr heven⟩, false)
      invFun := fun vertex =>
        match vertex.2 with
        | false => simpleCyclePreviousPosition hcycle vertex.1.1
        | true => vertex.1.1
      left_inv := by
        intro position
        by_cases heven : Even position.1
        · dsimp
          rw [dif_pos heven]
        · dsimp
          rw [dif_neg heven]
          exact simpleCyclePrevious_next hcycle position
      right_inv := by
        rintro ⟨vertex, (_ | _)⟩
        · dsimp
          have hpreviousNot : ¬ Even
              (simpleCyclePreviousPosition hcycle vertex.1).1 := by
            intro hprevious
            exact (F.even_previousPosition_iff_not_even hcycle hlen vertex.1).mp
              hprevious vertex.2
          rw [dif_neg hpreviousNot]
          apply Prod.ext
          · apply Subtype.ext
            exact simpleCycleNext_previous hcycle vertex.1
          · rfl
        · simp only
          have heven : Even vertex.1.1 := vertex.2
          rw [dif_pos heven]
          apply Prod.ext
          · apply Subtype.ext
            rfl
          · rfl }

noncomputable def packingCycleAlternatingSuccessor
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (cycle : P.Cycle) : Equiv.Perm (F.packingCycleVertex P cycle) := by
  let walk := (F.normalizedPacking P).walk cycle |>.2
  have hcycle : walk.IsCycle := (F.normalizedPacking P).isCycle cycle
  have hlen : Even walk.length := F.incidence_simpleCycle_even_length hcycle
  refine
    { toFun := fun vertex => ⟨simpleCycleNextPosition hcycle
          (simpleCycleNextPosition hcycle vertex.1), ?_⟩
      invFun := fun vertex => ⟨simpleCyclePreviousPosition hcycle
          (simpleCyclePreviousPosition hcycle vertex.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hnextNot : ¬ Even (simpleCycleNextPosition hcycle vertex.1).1 := by
      intro hnext
      exact (F.even_nextPosition_iff_not_even hcycle hlen vertex.1).mp hnext vertex.2
    exact (F.even_nextPosition_iff_not_even hcycle hlen
      (simpleCycleNextPosition hcycle vertex.1)).mpr hnextNot
  · have hpreviousNot : ¬ Even (simpleCyclePreviousPosition hcycle vertex.1).1 := by
      intro hprevious
      exact (F.even_previousPosition_iff_not_even hcycle hlen vertex.1).mp
        hprevious vertex.2
    exact (F.even_previousPosition_iff_not_even hcycle hlen
      (simpleCyclePreviousPosition hcycle vertex.1)).mpr hpreviousNot
  · intro vertex
    apply Subtype.ext
    dsimp
    rw [simpleCyclePrevious_next hcycle
      (simpleCycleNextPosition hcycle vertex.1)]
    rw [simpleCyclePrevious_next hcycle vertex.1]
  · intro vertex
    apply Subtype.ext
    dsimp
    rw [simpleCycleNext_previous hcycle
      (simpleCyclePreviousPosition hcycle vertex.1)]
    rw [simpleCycleNext_previous hcycle vertex.1]

noncomputable def packingCycleAlternatingSetAt
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) : F.SetId :=
  (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, vertex.1⟩).1

noncomputable def packingCycleAlternatingItemAt
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) : F.Item :=
  (F.normalizedObservationPositionEquiv P hcomplete
    ⟨cycle, simpleCyclePreviousPosition ((F.normalizedPacking P).isCycle cycle) vertex.1⟩).2.1

theorem packingCycleAlternatingCurrent_mem
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    F.packingCycleAlternatingItemAt P hcomplete cycle vertex ∈
      F.members (F.packingCycleAlternatingSetAt P hcomplete cycle vertex) := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  have hcycle := (F.normalizedPacking P).isCycle cycle
  have hset := F.normalizedObservationPosition_setMate_same_set
    P hcomplete cycle vertex.1
  unfold incidenceSetMatePosition at hset
  have heven : Even vertex.1.1 := vertex.2
  simp only [if_pos heven] at hset
  change (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩).1 =
    (E ⟨cycle, vertex.1⟩).1 at hset
  change (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩).2.1 ∈
    F.members (E ⟨cycle, vertex.1⟩).1
  simpa [hset] using (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩).2.2

theorem packingCycleAlternatingSuccessor_mem
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    F.packingCycleAlternatingItemAt P hcomplete cycle
        (F.packingCycleAlternatingSuccessor P cycle vertex) ∈
      F.members (F.packingCycleAlternatingSetAt P hcomplete cycle vertex) := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  have hcycle := (F.normalizedPacking P).isCycle cycle
  have hitem := F.normalizedObservationPosition_itemMate_same_item
    P hcomplete cycle vertex.1
  unfold incidenceItemMatePosition at hitem
  have heven : Even vertex.1.1 := vertex.2
  change (E ⟨cycle, if Even vertex.1.1 then
      simpleCycleNextPosition hcycle vertex.1 else
      simpleCyclePreviousPosition hcycle vertex.1⟩).2.1 =
    (E ⟨cycle, vertex.1⟩).2.1 at hitem
  rw [if_pos heven] at hitem
  change (E ⟨cycle, simpleCycleNextPosition hcycle vertex.1⟩).2.1 =
    (E ⟨cycle, vertex.1⟩).2.1 at hitem
  have hpreviousNextNext : simpleCyclePreviousPosition hcycle
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle vertex.1)) =
        simpleCycleNextPosition hcycle vertex.1 :=
    simpleCyclePrevious_next hcycle (simpleCycleNextPosition hcycle vertex.1)
  change (E ⟨cycle, simpleCyclePreviousPosition hcycle
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle vertex.1))⟩).2.1 ∈
    F.members (E ⟨cycle, vertex.1⟩).1
  rw [hpreviousNextNext, hitem]
  exact (E ⟨cycle, vertex.1⟩).2.2

theorem packingCycleAlternatingFalse_observation_eq
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, simpleCyclePreviousPosition ((F.normalizedPacking P).isCycle cycle) vertex.1⟩ =
      ⟨F.packingCycleAlternatingSetAt P hcomplete cycle vertex,
        ⟨F.packingCycleAlternatingItemAt P hcomplete cycle vertex,
          F.packingCycleAlternatingCurrent_mem P hcomplete cycle vertex⟩⟩ := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  have hcycle := (F.normalizedPacking P).isCycle cycle
  have hset := F.normalizedObservationPosition_setMate_same_set
    P hcomplete cycle vertex.1
  unfold incidenceSetMatePosition at hset
  have heven : Even vertex.1.1 := vertex.2
  simp only [if_pos heven] at hset
  change (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩).1 =
    (E ⟨cycle, vertex.1⟩).1 at hset
  refine Sigma.ext hset ?_
  apply (Subtype.heq_iff_coe_eq (fun candidate => by
    change candidate ∈ F.members
        (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩).1 ↔
      candidate ∈ F.members (E ⟨cycle, vertex.1⟩).1
    rw [hset])).mpr
  rfl

theorem packingCycleAlternatingTrue_observation_eq
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, vertex.1⟩ =
      ⟨F.packingCycleAlternatingSetAt P hcomplete cycle vertex,
        ⟨F.packingCycleAlternatingItemAt P hcomplete cycle
            (F.packingCycleAlternatingSuccessor P cycle vertex),
          F.packingCycleAlternatingSuccessor_mem P hcomplete cycle vertex⟩⟩ := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  have hcycle := (F.normalizedPacking P).isCycle cycle
  have hitem := F.normalizedObservationPosition_itemMate_same_item
    P hcomplete cycle vertex.1
  unfold incidenceItemMatePosition at hitem
  have heven : Even vertex.1.1 := vertex.2
  change (E ⟨cycle, if Even vertex.1.1 then
      simpleCycleNextPosition hcycle vertex.1 else
      simpleCyclePreviousPosition hcycle vertex.1⟩).2.1 =
    (E ⟨cycle, vertex.1⟩).2.1 at hitem
  rw [if_pos heven] at hitem
  have hpreviousNextNext : simpleCyclePreviousPosition hcycle
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle vertex.1)) =
        simpleCycleNextPosition hcycle vertex.1 :=
    simpleCyclePrevious_next hcycle (simpleCycleNextPosition hcycle vertex.1)
  refine Sigma.ext rfl ?_
  apply (Subtype.heq_iff_coe_eq (fun candidate => by rfl)).mpr
  change (E ⟨cycle, vertex.1⟩).2.1 =
    (E ⟨cycle, simpleCyclePreviousPosition hcycle
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle vertex.1))⟩).2.1
  rw [hpreviousNextNext]
  exact hitem.symm

theorem packingCycleAlternatingBase_false
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    (F.cycleDecompositionOfCompletePacking P hcomplete).base
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCyclePreviousPosition ((F.normalizedPacking P).isCycle cycle) vertex.1⟩) = 1 := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  have hcycle := (F.normalizedPacking P).isCycle cycle
  have hlen : Even ((F.normalizedPacking P).walk cycle).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  have hpreviousNot : ¬ Even
      (simpleCyclePreviousPosition hcycle vertex.1).1 := by
    intro hprevious
    exact (F.even_previousPosition_iff_not_even hcycle hlen vertex.1).mp
      hprevious vertex.2
  change F.normalizedPackingBase P hcomplete
    (E ⟨cycle, simpleCyclePreviousPosition hcycle vertex.1⟩) = 1
  unfold normalizedPackingBase
  rw [E.symm_apply_apply]
  unfold incidenceCyclePositionBase
  exact if_neg hpreviousNot

theorem packingCycleAlternatingBase_true
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (vertex : F.packingCycleVertex P cycle) :
    (F.cycleDecompositionOfCompletePacking P hcomplete).base
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, vertex.1⟩) = -1 := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  change F.normalizedPackingBase P hcomplete (E ⟨cycle, vertex.1⟩) = -1
  unfold normalizedPackingBase
  rw [E.symm_apply_apply]
  unfold incidenceCyclePositionBase
  exact if_pos vertex.2

/-- The complete packing's signed decomposition has an explicit alternating
cycle witness, so the source Lemma 2 lower bound applies with the concrete
graph-cycle lengths. -/
noncomputable def cycleDecompositionOfCompletePacking_alternatingCycleWitness
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) :
    (F.cycleDecompositionOfCompletePacking P hcomplete).AlternatingCycleWitness := by
  refine
    { Vertex := F.packingCycleVertex P
      instFintypeVertex := fun cycle => by
        classical
        exact Subtype.fintype _
      instDecidableEqVertex := fun cycle => Classical.decEq (F.packingCycleVertex P cycle)
      successor := F.packingCycleAlternatingSuccessor P
      setAt := F.packingCycleAlternatingSetAt P hcomplete
      itemAt := F.packingCycleAlternatingItemAt P hcomplete
      current_mem := F.packingCycleAlternatingCurrent_mem P hcomplete
      successor_mem := F.packingCycleAlternatingSuccessor_mem P hcomplete
      edgeParamEquiv := F.packingCycleAlternatingEdgeParamEquiv P
      false_edge := ?_
      true_edge := ?_
      base_false := ?_
      base_true := ?_ }
  · intro cycle vertex
    change F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, simpleCyclePreviousPosition ((F.normalizedPacking P).isCycle cycle) vertex.1⟩ = _
    exact F.packingCycleAlternatingFalse_observation_eq P hcomplete cycle vertex
  · intro cycle vertex
    change F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, vertex.1⟩ = _
    exact F.packingCycleAlternatingTrue_observation_eq P hcomplete cycle vertex
  · intro cycle vertex
    change (F.cycleDecompositionOfCompletePacking P hcomplete).base
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCyclePreviousPosition ((F.normalizedPacking P).isCycle cycle) vertex.1⟩) = 1
    exact F.packingCycleAlternatingBase_false P hcomplete cycle vertex
  · intro cycle vertex
    change (F.cycleDecompositionOfCompletePacking P hcomplete).base
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, vertex.1⟩) = -1
    exact F.packingCycleAlternatingBase_true P hcomplete cycle vertex

/-- For an Eulerian choice frame, the source's bounded cycle packing yields a
balanced signed decomposition together with the explicit traversal needed by
Lemma 2.  Every concrete cycle has at most `2 |X|` incidences. -/
theorem eulerian_incidenceGraph_exists_bounded_alternatingCycleDecomposition
    (hEulerian : F.Eulerian) :
    ∃ (P : PartialSimpleCyclePacking F.incidenceGraph (2 * Fintype.card F.Item))
      (hcomplete : P.IsComplete),
      ∃ W : (F.cycleDecompositionOfCompletePacking P hcomplete).AlternatingCycleWitness,
        (∀ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
          (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle ≤
            2 * Fintype.card F.Item) ∧
        (∑ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
          (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle) = F.incidenceCount := by
  obtain ⟨P, hcomplete⟩ := F.eulerian_incidenceGraph_has_complete_cycle_packing hEulerian
  refine ⟨P, hcomplete, F.cycleDecompositionOfCompletePacking_alternatingCycleWitness
    P hcomplete, ?_, F.cycleDecompositionOfCompletePacking_total_length P hcomplete⟩
  intro cycle
  rw [F.cycleDecompositionOfCompletePacking_length]
  exact P.length_le cycle

end ChoiceFrame

end SeshadriUgander2020IIATesting
