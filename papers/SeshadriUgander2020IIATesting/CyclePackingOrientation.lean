import SeshadriUgander2020IIATesting.AppendixCycleBounds

/-!
# Alternating orientations of normalized incidence cycles

A packed incidence cycle is rotated to begin at a choice-set vertex in
`AppendixCycleBounds`.  Its even positions then alternate with item positions.
This file makes the two local endpoint pairings and their opposite signs
explicit, which is the combinatorial conservation step behind the source's
Eulerian alternating-cycle orientation.
-/

namespace SeshadriUgander2020IIATesting

open SimpleGraph

namespace ChoiceFrame

open AppliedModelingLib.Foundations.Graph

variable (F : ChoiceFrame)

/-- The alternating base sign on a normalized incidence cycle.  Choice-set
outgoing edge positions are even and receive `-1`; the preceding incoming
edge positions are odd and receive `1`. -/
noncomputable def incidenceCyclePositionBase
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (position : Fin cycle.length) : ℝ :=
  if Even position.1 then -1 else 1

theorem incidenceCyclePositionBase_eq_one_or_neg_one
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (position : Fin cycle.length) :
    F.incidenceCyclePositionBase position = 1 ∨ F.incidenceCyclePositionBase position = -1 := by
  unfold incidenceCyclePositionBase
  split <;> simp

/-- Decode the item coordinate of an observation from an incidence edge in
the standard item--choice-set order. -/
theorem observation_item_eq_of_observationEdge_eq_inl_inr
    (o : F.Observation) (item : F.Item) (setId : F.SetId)
    (hedge : F.observationEdge o = s(Sum.inl item, Sum.inr setId)) :
    o.2.1 = item := by
  rcases Sym2.eq_iff.mp hedge with hs | hs
  · exact Sum.inl.inj hs.1
  · exact (Sum.inl_ne_inr hs.1).elim

/-- Decode the item coordinate when the same incidence edge is written in
the reverse choice-set--item order. -/
theorem observation_item_eq_of_observationEdge_eq_inr_inl
    (o : F.Observation) (setId : F.SetId) (item : F.Item)
    (hedge : F.observationEdge o = s(Sum.inr setId, Sum.inl item)) :
    o.2.1 = item := by
  rcases Sym2.eq_iff.mp hedge with hs | hs
  · exact (Sum.inl_ne_inr hs.1).elim
  · exact Sum.inl.inj hs.1

/-- Decode the choice-set coordinate of an observation from a standard
item--choice-set incidence edge. -/
theorem observation_set_eq_of_observationEdge_eq_inl_inr
    (o : F.Observation) (item : F.Item) (setId : F.SetId)
    (hedge : F.observationEdge o = s(Sum.inl item, Sum.inr setId)) :
    o.1 = setId := by
  rcases Sym2.eq_iff.mp hedge with hs | hs
  · exact Sum.inr.inj hs.2
  · exact (Sum.inr_ne_inl hs.2).elim

/-- Decode the choice-set coordinate when the incidence edge is written in
the reverse choice-set--item order. -/
theorem observation_set_eq_of_observationEdge_eq_inr_inl
    (o : F.Observation) (setId : F.SetId) (item : F.Item)
    (hedge : F.observationEdge o = s(Sum.inr setId, Sum.inl item)) :
    o.1 = setId := by
  rcases Sym2.eq_iff.mp hedge with hs | hs
  · exact (Sum.inr_ne_inl hs.2).elim
  · exact Sum.inr.inj hs.2

/-- Advancing one modular cycle position reverses its parity when the cycle
length is even. -/
theorem even_nextPosition_iff_not_even
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    Even (simpleCycleNextPosition hcycle position).1 ↔ ¬ Even position.1 := by
  unfold simpleCycleNextPosition
  change Even ((position.1 + 1) % cycle.length) ↔ ¬ Even position.1
  rw [Even.mod_even_iff hlen, Nat.even_add_one]

/-- Moving back one modular cycle position also reverses parity. -/
theorem even_previousPosition_iff_not_even
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    Even (simpleCyclePreviousPosition hcycle position).1 ↔ ¬ Even position.1 := by
  classical
  by_cases hzero : position.1 = 0
  · rw [simpleCyclePreviousPosition_val_of_zero hcycle position hzero, hzero]
    constructor
    · intro hprevious _
      have hlength : Even ((cycle.length - 1) + 1) := by
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt
          (SimpleGraph.Walk.not_nil_iff_lt_length.mp hcycle.not_nil))]
        exact hlen
      exact (Nat.even_add_one.mp hlength) hprevious
    · intro hnot
      exact (hnot ⟨0, by simp⟩).elim
  · rw [simpleCyclePreviousPosition_val_of_ne_zero hcycle position hzero]
    have hposition : position.1 - 1 + 1 = position.1 := by omega
    have hrelation : Even position.1 ↔ ¬ Even (position.1 - 1) := by
      simpa only [hposition] using (Nat.even_add_one (n := position.1 - 1))
    constructor
    · intro hprevious heven
      exact (hrelation.mp heven) hprevious
    · intro hnot
      by_contra hpreviousNot
      apply hnot
      exact hrelation.mpr hpreviousNot

/-- Pair the two cycle edges incident to their common item endpoint. -/
noncomputable def incidenceItemMatePosition
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (position : Fin cycle.length) : Fin cycle.length :=
  if Even position.1 then simpleCycleNextPosition hcycle position
  else simpleCyclePreviousPosition hcycle position

/-- Pair the two cycle edges incident to their common choice-set endpoint. -/
noncomputable def incidenceSetMatePosition
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (position : Fin cycle.length) : Fin cycle.length :=
  if Even position.1 then simpleCyclePreviousPosition hcycle position
  else simpleCycleNextPosition hcycle position

theorem incidenceItemMatePosition_apply_apply
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceItemMatePosition hcycle (F.incidenceItemMatePosition hcycle position) = position := by
  unfold incidenceItemMatePosition
  by_cases heven : Even position.1
  · rw [if_pos heven]
    have hnextnot : ¬ Even (simpleCycleNextPosition hcycle position).1 := by
      intro hnext
      exact (F.even_nextPosition_iff_not_even hcycle hlen position).mp hnext heven
    rw [if_neg hnextnot]
    exact simpleCyclePrevious_next hcycle position
  · rw [if_neg heven]
    have hpreven : Even (simpleCyclePreviousPosition hcycle position).1 :=
      (F.even_previousPosition_iff_not_even hcycle hlen position).mpr heven
    rw [if_pos hpreven]
    exact simpleCycleNext_previous hcycle position

theorem incidenceSetMatePosition_apply_apply
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceSetMatePosition hcycle (F.incidenceSetMatePosition hcycle position) = position := by
  unfold incidenceSetMatePosition
  by_cases heven : Even position.1
  · rw [if_pos heven]
    have hprevnot : ¬ Even (simpleCyclePreviousPosition hcycle position).1 := by
      intro hprev
      exact (F.even_previousPosition_iff_not_even hcycle hlen position).mp hprev heven
    rw [if_neg hprevnot]
    exact simpleCycleNext_previous hcycle position
  · rw [if_neg heven]
    have hnextEven : Even (simpleCycleNextPosition hcycle position).1 :=
      (F.even_nextPosition_iff_not_even hcycle hlen position).mpr heven
    rw [if_pos hnextEven]
    exact simpleCyclePrevious_next hcycle position

/-- The item endpoint mate has exactly the opposite alternating base sign. -/
theorem incidenceCyclePositionBase_itemMate_neg
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceCyclePositionBase (F.incidenceItemMatePosition hcycle position) =
      -F.incidenceCyclePositionBase position := by
  unfold incidenceItemMatePosition
  by_cases heven : Even position.1
  · rw [if_pos heven]
    have hnextnot : ¬ Even (simpleCycleNextPosition hcycle position).1 := by
      intro hnext
      exact (F.even_nextPosition_iff_not_even hcycle hlen position).mp hnext heven
    simp [incidenceCyclePositionBase, heven, hnextnot]
  · rw [if_neg heven]
    have hpreven : Even (simpleCyclePreviousPosition hcycle position).1 :=
      (F.even_previousPosition_iff_not_even hcycle hlen position).mpr heven
    simp [incidenceCyclePositionBase, heven, hpreven]

/-- The choice-set endpoint mate has exactly the opposite alternating base
sign. -/
theorem incidenceCyclePositionBase_setMate_neg
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceCyclePositionBase (F.incidenceSetMatePosition hcycle position) =
      -F.incidenceCyclePositionBase position := by
  unfold incidenceSetMatePosition
  by_cases heven : Even position.1
  · rw [if_pos heven]
    have hprevnot : ¬ Even (simpleCyclePreviousPosition hcycle position).1 := by
      intro hprev
      exact (F.even_previousPosition_iff_not_even hcycle hlen position).mp hprev heven
    simp [incidenceCyclePositionBase, heven, hprevnot]
  · rw [if_neg heven]
    have hnextEven : Even (simpleCycleNextPosition hcycle position).1 :=
      (F.even_nextPosition_iff_not_even hcycle hlen position).mpr heven
    simp [incidenceCyclePositionBase, heven, hnextEven]

theorem incidenceItemMatePosition_ne
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceItemMatePosition hcycle position ≠ position := by
  intro heq
  have hsign := F.incidenceCyclePositionBase_itemMate_neg hcycle hlen position
  rw [heq] at hsign
  unfold incidenceCyclePositionBase at hsign
  by_cases heven : Even position.1 <;> simp [heven] at hsign <;> norm_num at hsign

theorem incidenceSetMatePosition_ne
    {baseSet : F.SetId} {cycle : F.incidenceGraph.Walk (Sum.inr baseSet) (Sum.inr baseSet)}
    (hcycle : cycle.IsCycle) (hlen : Even cycle.length)
    (position : Fin cycle.length) :
    F.incidenceSetMatePosition hcycle position ≠ position := by
  intro heq
  have hsign := F.incidenceCyclePositionBase_setMate_neg hcycle hlen position
  rw [heq] at hsign
  unfold incidenceCyclePositionBase at hsign
  by_cases heven : Even position.1 <;> simp [heven] at hsign <;> norm_num at hsign

/-- The observation indexing of a complete packing after independently
recentering all of its cycles at choice-set vertices. -/
noncomputable def normalizedObservationPositionEquiv
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) :
    (Sigma fun cycle => Fin (((F.normalizedPacking P).walk cycle).2.length)) ≃ F.Observation :=
  F.observationPositionEquiv (F.normalizedPacking P) (F.normalizedPacking_isComplete P hcomplete)

theorem observationEdge_normalizedObservationPositionEquiv_apply
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin (((F.normalizedPacking P).walk cycle).2.length)) :
    F.observationEdge (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
      simpleCycleEdgeAt ((F.normalizedPacking P).walk cycle).2 position := by
  unfold normalizedObservationPositionEquiv
  rw [F.observationEdge_observationPositionEquiv_apply]
  rw [simpleCycleEdgePositionEquiv_apply_edgeAt]

/-- The two position-paired observations at an item endpoint have the same
item coordinate. -/
theorem normalizedObservationPosition_itemMate_same_item
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin (((F.normalizedPacking P).walk cycle).2.length)) :
    (F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, F.incidenceItemMatePosition
        ((F.normalizedPacking P).isCycle cycle) position⟩).2.1 =
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩).2.1 := by
  let walk := F.normalizedPackingCycleWalk P cycle
  have hcycle : walk.IsCycle := F.normalizedPackingCycleWalk_isCycle P cycle
  have hlen : Even walk.length := F.incidence_simpleCycle_even_length hcycle
  change (F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, F.incidenceItemMatePosition hcycle position⟩).2.1 =
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩).2.1
  by_cases heven : Even position.1
  · unfold incidenceItemMatePosition
    rw [if_pos heven]
    have hnextnot : ¬ Even (simpleCycleNextPosition hcycle position).1 := by
      intro hnext
      exact (F.even_nextPosition_iff_not_even hcycle hlen position).mp hnext heven
    have hnextodd : Odd (simpleCycleNextPosition hcycle position).1 :=
      Nat.not_even_iff_odd.mp hnextnot
    obtain ⟨setId, hset⟩ :=
      F.incidenceWalk_getVert_even_is_set walk position heven
    obtain ⟨item, hitem⟩ :=
      F.incidenceWalk_getVert_odd_is_item walk
        (simpleCycleNextPosition hcycle position) hnextodd
    have hedgePosition := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          simpleCycleEdgeAt walk position at hedgePosition
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle position] at hedgePosition
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          s(walk.getVert position.1,
            walk.getVert (simpleCycleNextPosition hcycle position).1) at hedgePosition
    rw [hset, hitem] at hedgePosition
    have hitemPosition := F.observation_item_eq_of_observationEdge_eq_inr_inl
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩)
      setId item hedgePosition
    have hnextEven : Even
        (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle position)).1 :=
      (F.even_nextPosition_iff_not_even hcycle hlen
        (simpleCycleNextPosition hcycle position)).mpr hnextnot
    obtain ⟨nextSet, hnextSet⟩ := F.incidenceWalk_getVert_even_is_set walk
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle position)) hnextEven
    have hedgeNext := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle (simpleCycleNextPosition hcycle position)
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCycleNextPosition hcycle position⟩) =
          simpleCycleEdgeAt walk (simpleCycleNextPosition hcycle position) at hedgeNext
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle
      (simpleCycleNextPosition hcycle position)] at hedgeNext
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCycleNextPosition hcycle position⟩) =
          s(walk.getVert (simpleCycleNextPosition hcycle position).1,
            walk.getVert (simpleCycleNextPosition hcycle
              (simpleCycleNextPosition hcycle position)).1) at hedgeNext
    rw [hitem, hnextSet] at hedgeNext
    have hitemNext := F.observation_item_eq_of_observationEdge_eq_inl_inr
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCycleNextPosition hcycle position⟩)
      item nextSet hedgeNext
    exact hitemNext.trans hitemPosition.symm
  · unfold incidenceItemMatePosition
    rw [if_neg heven]
    have hodd : Odd position.1 := Nat.not_even_iff_odd.mp heven
    have hpreviousEven : Even (simpleCyclePreviousPosition hcycle position).1 :=
      (F.even_previousPosition_iff_not_even hcycle hlen position).mpr heven
    obtain ⟨setId, hset⟩ := F.incidenceWalk_getVert_even_is_set walk
      (simpleCyclePreviousPosition hcycle position) hpreviousEven
    obtain ⟨item, hitem⟩ := F.incidenceWalk_getVert_odd_is_item walk position hodd
    have hedgePrevious := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle (simpleCyclePreviousPosition hcycle position)
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCyclePreviousPosition hcycle position⟩) =
          simpleCycleEdgeAt walk (simpleCyclePreviousPosition hcycle position) at hedgePrevious
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle
      (simpleCyclePreviousPosition hcycle position)] at hedgePrevious
    have hpreviousNext : simpleCycleNextPosition hcycle
        (simpleCyclePreviousPosition hcycle position) = position :=
      simpleCycleNext_previous hcycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCyclePreviousPosition hcycle position⟩) =
          s(walk.getVert (simpleCyclePreviousPosition hcycle position).1,
            walk.getVert (simpleCycleNextPosition hcycle
              (simpleCyclePreviousPosition hcycle position)).1) at hedgePrevious
    rw [hpreviousNext, hset, hitem] at hedgePrevious
    have hitemPrevious := F.observation_item_eq_of_observationEdge_eq_inr_inl
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCyclePreviousPosition hcycle position⟩)
      setId item hedgePrevious
    have hnextEven : Even (simpleCycleNextPosition hcycle position).1 :=
      (F.even_nextPosition_iff_not_even hcycle hlen position).mpr heven
    obtain ⟨nextSet, hnextSet⟩ := F.incidenceWalk_getVert_even_is_set walk
      (simpleCycleNextPosition hcycle position) hnextEven
    have hedgePosition := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          simpleCycleEdgeAt walk position at hedgePosition
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle position] at hedgePosition
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          s(walk.getVert position.1,
            walk.getVert (simpleCycleNextPosition hcycle position).1) at hedgePosition
    rw [hitem, hnextSet] at hedgePosition
    have hitemPosition := F.observation_item_eq_of_observationEdge_eq_inl_inr
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩)
      item nextSet hedgePosition
    exact hitemPrevious.trans hitemPosition.symm

/-- The two position-paired observations at a choice-set endpoint have the
same choice-set coordinate. -/
theorem normalizedObservationPosition_setMate_same_set
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin (((F.normalizedPacking P).walk cycle).2.length)) :
    (F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, F.incidenceSetMatePosition
        ((F.normalizedPacking P).isCycle cycle) position⟩).1 =
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩).1 := by
  let walk := F.normalizedPackingCycleWalk P cycle
  have hcycle : walk.IsCycle := F.normalizedPackingCycleWalk_isCycle P cycle
  have hlen : Even walk.length := F.incidence_simpleCycle_even_length hcycle
  change (F.normalizedObservationPositionEquiv P hcomplete
      ⟨cycle, F.incidenceSetMatePosition hcycle position⟩).1 =
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩).1
  by_cases heven : Even position.1
  · unfold incidenceSetMatePosition
    rw [if_pos heven]
    have hpreviousnot : ¬ Even (simpleCyclePreviousPosition hcycle position).1 := by
      intro hprevious
      exact (F.even_previousPosition_iff_not_even hcycle hlen position).mp hprevious heven
    have hpreviousOdd : Odd (simpleCyclePreviousPosition hcycle position).1 :=
      Nat.not_even_iff_odd.mp hpreviousnot
    obtain ⟨setId, hset⟩ := F.incidenceWalk_getVert_even_is_set walk position heven
    obtain ⟨item, hitem⟩ := F.incidenceWalk_getVert_odd_is_item walk
      (simpleCyclePreviousPosition hcycle position) hpreviousOdd
    have hedgePrevious := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle (simpleCyclePreviousPosition hcycle position)
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCyclePreviousPosition hcycle position⟩) =
          simpleCycleEdgeAt walk (simpleCyclePreviousPosition hcycle position) at hedgePrevious
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle
      (simpleCyclePreviousPosition hcycle position)] at hedgePrevious
    have hpreviousNext : simpleCycleNextPosition hcycle
        (simpleCyclePreviousPosition hcycle position) = position :=
      simpleCycleNext_previous hcycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCyclePreviousPosition hcycle position⟩) =
          s(walk.getVert (simpleCyclePreviousPosition hcycle position).1,
            walk.getVert (simpleCycleNextPosition hcycle
              (simpleCyclePreviousPosition hcycle position)).1) at hedgePrevious
    rw [hpreviousNext, hitem, hset] at hedgePrevious
    have hsetPrevious := F.observation_set_eq_of_observationEdge_eq_inl_inr
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCyclePreviousPosition hcycle position⟩)
      item setId hedgePrevious
    have hnextNot : ¬ Even (simpleCycleNextPosition hcycle position).1 := by
      intro hnext
      exact (F.even_nextPosition_iff_not_even hcycle hlen position).mp hnext heven
    have hnextOdd : Odd (simpleCycleNextPosition hcycle position).1 :=
      Nat.not_even_iff_odd.mp hnextNot
    obtain ⟨nextItem, hnextItem⟩ := F.incidenceWalk_getVert_odd_is_item walk
      (simpleCycleNextPosition hcycle position) hnextOdd
    have hedgePosition := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          simpleCycleEdgeAt walk position at hedgePosition
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle position] at hedgePosition
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          s(walk.getVert position.1,
            walk.getVert (simpleCycleNextPosition hcycle position).1) at hedgePosition
    rw [hset, hnextItem] at hedgePosition
    have hsetPosition := F.observation_set_eq_of_observationEdge_eq_inr_inl
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩)
      setId nextItem hedgePosition
    exact hsetPrevious.trans hsetPosition.symm
  · unfold incidenceSetMatePosition
    rw [if_neg heven]
    have hodd : Odd position.1 := Nat.not_even_iff_odd.mp heven
    have hnextEven : Even (simpleCycleNextPosition hcycle position).1 :=
      (F.even_nextPosition_iff_not_even hcycle hlen position).mpr heven
    obtain ⟨item, hitem⟩ := F.incidenceWalk_getVert_odd_is_item walk position hodd
    obtain ⟨setId, hset⟩ := F.incidenceWalk_getVert_even_is_set walk
      (simpleCycleNextPosition hcycle position) hnextEven
    have hedgePosition := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle position
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          simpleCycleEdgeAt walk position at hedgePosition
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle position] at hedgePosition
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
          s(walk.getVert position.1,
            walk.getVert (simpleCycleNextPosition hcycle position).1) at hedgePosition
    rw [hitem, hset] at hedgePosition
    have hsetPosition := F.observation_set_eq_of_observationEdge_eq_inl_inr
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩)
      item setId hedgePosition
    have hnextNot : ¬ Even
        (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle position)).1 := by
      intro hnextNext
      exact (F.even_nextPosition_iff_not_even hcycle hlen
        (simpleCycleNextPosition hcycle position)).mp hnextNext hnextEven
    have hnextOdd : Odd
        (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle position)).1 :=
      Nat.not_even_iff_odd.mp hnextNot
    obtain ⟨nextItem, hnextItem⟩ := F.incidenceWalk_getVert_odd_is_item walk
      (simpleCycleNextPosition hcycle (simpleCycleNextPosition hcycle position)) hnextOdd
    have hedgeNext := F.observationEdge_normalizedObservationPositionEquiv_apply
      P hcomplete cycle (simpleCycleNextPosition hcycle position)
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCycleNextPosition hcycle position⟩) =
          simpleCycleEdgeAt walk (simpleCycleNextPosition hcycle position) at hedgeNext
    rw [simpleCycleEdgeAt_eq_cycleVertexAt_succ walk hcycle
      (simpleCycleNextPosition hcycle position)] at hedgeNext
    change F.observationEdge
        (F.normalizedObservationPositionEquiv P hcomplete
          ⟨cycle, simpleCycleNextPosition hcycle position⟩) =
          s(walk.getVert (simpleCycleNextPosition hcycle position).1,
            walk.getVert (simpleCycleNextPosition hcycle
              (simpleCycleNextPosition hcycle position)).1) at hedgeNext
    rw [hset, hnextItem] at hedgeNext
    have hsetNext := F.observation_set_eq_of_observationEdge_eq_inr_inl
      (F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, simpleCycleNextPosition hcycle position⟩)
      setId nextItem hedgeNext
    exact hsetNext.trans hsetPosition.symm

end ChoiceFrame

end SeshadriUgander2020IIATesting
