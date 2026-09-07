import SeshadriUgander2020IIATesting.CyclePackingOrientation
import SeshadriUgander2020IIATesting.CycleDecomposition

/-!
# Signed decompositions from complete incidence-cycle packings

This module turns a complete packing of concrete simple cycles in the
comparison incidence graph into the balanced signed `CycleDecomposition`
used by the paper's lower-bound argument.  The endpoint pairings below are
induced directly by consecutive edges in each normalized cycle.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

open AppliedModelingLib.Foundations.Graph

variable (F : ChoiceFrame)

noncomputable def normalizedPackingItemMatePosition
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength) :
    (Sigma fun cycle => Fin (((F.normalizedPacking P).walk cycle).2.length)) →
      (Sigma fun cycle => Fin (((F.normalizedPacking P).walk cycle).2.length)) :=
  fun position => ⟨position.1, F.incidenceItemMatePosition
    ((F.normalizedPacking P).isCycle position.1) position.2⟩

noncomputable def normalizedPackingSetMatePosition
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength) :
    (Sigma fun cycle => Fin (((F.normalizedPacking P).walk cycle).2.length)) →
      (Sigma fun cycle => Fin (((F.normalizedPacking P).walk cycle).2.length)) :=
  fun position => ⟨position.1, F.incidenceSetMatePosition
    ((F.normalizedPacking P).isCycle position.1) position.2⟩

noncomputable def normalizedPackingItemMate
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) : F.Observation :=
  F.normalizedObservationPositionEquiv P hcomplete
    (F.normalizedPackingItemMatePosition P
      ((F.normalizedObservationPositionEquiv P hcomplete).symm o))

noncomputable def normalizedPackingSetMate
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) : F.Observation :=
  F.normalizedObservationPositionEquiv P hcomplete
    (F.normalizedPackingSetMatePosition P
      ((F.normalizedObservationPositionEquiv P hcomplete).symm o))

theorem normalizedPackingItemMate_apply_position
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin (((F.normalizedPacking P).walk cycle).2.length)) :
    F.normalizedPackingItemMate P hcomplete
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
      F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, F.incidenceItemMatePosition
          ((F.normalizedPacking P).isCycle cycle) position⟩ := by
  unfold normalizedPackingItemMate
  have hp := (F.normalizedObservationPositionEquiv P hcomplete).symm_apply_apply ⟨cycle, position⟩
  rw [show F.normalizedPackingItemMatePosition P
      ((F.normalizedObservationPositionEquiv P hcomplete).symm
        ((F.normalizedObservationPositionEquiv P hcomplete) ⟨cycle, position⟩)) =
        F.normalizedPackingItemMatePosition P ⟨cycle, position⟩ from
      congrArg (F.normalizedPackingItemMatePosition P) hp]
  rfl

theorem normalizedPackingSetMate_apply_position
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle)
    (position : Fin (((F.normalizedPacking P).walk cycle).2.length)) :
    F.normalizedPackingSetMate P hcomplete
      (F.normalizedObservationPositionEquiv P hcomplete ⟨cycle, position⟩) =
      F.normalizedObservationPositionEquiv P hcomplete
        ⟨cycle, F.incidenceSetMatePosition
          ((F.normalizedPacking P).isCycle cycle) position⟩ := by
  unfold normalizedPackingSetMate
  have hp := (F.normalizedObservationPositionEquiv P hcomplete).symm_apply_apply ⟨cycle, position⟩
  rw [show F.normalizedPackingSetMatePosition P
      ((F.normalizedObservationPositionEquiv P hcomplete).symm
        ((F.normalizedObservationPositionEquiv P hcomplete) ⟨cycle, position⟩)) =
        F.normalizedPackingSetMatePosition P ⟨cycle, position⟩ from
      congrArg (F.normalizedPackingSetMatePosition P) hp]
  rfl

theorem normalizedPackingItemMate_apply_apply
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingItemMate P hcomplete
      (F.normalizedPackingItemMate P hcomplete o) = o := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  have hfirst : F.normalizedPackingItemMate P hcomplete (E ⟨position.1, position.2⟩) =
      E ⟨position.1, F.incidenceItemMatePosition hcycle position.2⟩ := by
    exact F.normalizedPackingItemMate_apply_position P hcomplete position.1 position.2
  have hsecond := F.normalizedPackingItemMate_apply_position P hcomplete position.1
    (F.incidenceItemMatePosition hcycle position.2)
  change F.normalizedPackingItemMate P hcomplete
      (F.normalizedPackingItemMate P hcomplete o) = o
  rw [← E.apply_symm_apply o, hfirst, hsecond]
  rw [F.incidenceItemMatePosition_apply_apply hcycle hlen]

theorem normalizedPackingSetMate_apply_apply
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingSetMate P hcomplete
      (F.normalizedPackingSetMate P hcomplete o) = o := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  have hfirst : F.normalizedPackingSetMate P hcomplete (E ⟨position.1, position.2⟩) =
      E ⟨position.1, F.incidenceSetMatePosition hcycle position.2⟩ := by
    exact F.normalizedPackingSetMate_apply_position P hcomplete position.1 position.2
  have hsecond := F.normalizedPackingSetMate_apply_position P hcomplete position.1
    (F.incidenceSetMatePosition hcycle position.2)
  change F.normalizedPackingSetMate P hcomplete
      (F.normalizedPackingSetMate P hcomplete o) = o
  rw [← E.apply_symm_apply o, hfirst, hsecond]
  rw [F.incidenceSetMatePosition_apply_apply hcycle hlen]

theorem normalizedPackingItemMate_item
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    (F.normalizedPackingItemMate P hcomplete o).2.1 = o.2.1 := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hposition : E position = o := E.apply_symm_apply o
  calc
    (F.normalizedPackingItemMate P hcomplete o).2.1 =
        (F.normalizedPackingItemMate P hcomplete (E position)).2.1 := by rw [hposition]
    _ = (E position).2.1 := by
      rw [F.normalizedPackingItemMate_apply_position P hcomplete position.1 position.2]
      exact F.normalizedObservationPosition_itemMate_same_item P hcomplete position.1 position.2
    _ = o.2.1 := by rw [hposition]

theorem normalizedPackingSetMate_set
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    (F.normalizedPackingSetMate P hcomplete o).1 = o.1 := by
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hposition : E position = o := E.apply_symm_apply o
  calc
    (F.normalizedPackingSetMate P hcomplete o).1 =
        (F.normalizedPackingSetMate P hcomplete (E position)).1 := by rw [hposition]
    _ = (E position).1 := by
      rw [F.normalizedPackingSetMate_apply_position P hcomplete position.1 position.2]
      exact F.normalizedObservationPosition_setMate_same_set P hcomplete position.1 position.2
    _ = o.1 := by rw [hposition]

theorem normalizedPackingItemMate_ne
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingItemMate P hcomplete o ≠ o := by
  intro heq
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  have hposition : E position = o := E.apply_symm_apply o
  have hlocal : E ⟨position.1, F.incidenceItemMatePosition hcycle position.2⟩ =
      E ⟨position.1, position.2⟩ := by
    rw [← F.normalizedPackingItemMate_apply_position P hcomplete position.1 position.2]
    change F.normalizedPackingItemMate P hcomplete (E position) = E position
    rw [hposition]
    exact heq
  have hmate : F.incidenceItemMatePosition hcycle position.2 = position.2 := by
    have hpair := E.injective hlocal
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpair |>.2)
  exact F.incidenceItemMatePosition_ne hcycle hlen position.2 hmate

theorem normalizedPackingSetMate_ne
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingSetMate P hcomplete o ≠ o := by
  intro heq
  let E := F.normalizedObservationPositionEquiv P hcomplete
  let position := E.symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  have hposition : E position = o := E.apply_symm_apply o
  have hlocal : E ⟨position.1, F.incidenceSetMatePosition hcycle position.2⟩ =
      E ⟨position.1, position.2⟩ := by
    rw [← F.normalizedPackingSetMate_apply_position P hcomplete position.1 position.2]
    change F.normalizedPackingSetMate P hcomplete (E position) = E position
    rw [hposition]
    exact heq
  have hmate : F.incidenceSetMatePosition hcycle position.2 = position.2 := by
    have hpair := E.injective hlocal
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpair |>.2)
  exact F.incidenceSetMatePosition_ne hcycle hlen position.2 hmate

noncomputable def normalizedPackingSetMateAt
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (setId : F.SetId)
    (item : {x : F.Item // x ∈ F.members setId}) :
    {x : F.Item // x ∈ F.members setId} :=
  ⟨(F.normalizedPackingSetMate P hcomplete ⟨setId, item⟩).2.1, by
    have hset := F.normalizedPackingSetMate_set P hcomplete ⟨setId, item⟩
    simpa [hset] using (F.normalizedPackingSetMate P hcomplete ⟨setId, item⟩).2.2⟩

theorem normalizedPackingSetMateAt_observation
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (setId : F.SetId)
    (item : {x : F.Item // x ∈ F.members setId}) :
    F.normalizedPackingSetMate P hcomplete ⟨setId, item⟩ =
      ⟨setId, F.normalizedPackingSetMateAt P hcomplete setId item⟩ := by
  have hset := F.normalizedPackingSetMate_set P hcomplete ⟨setId, item⟩
  refine Sigma.ext hset ?_
  apply (Subtype.heq_iff_coe_eq (fun x => by simpa [hset])).mpr
  rfl

noncomputable def normalizedPackingSetEvenPairing
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (setId : F.SetId) :
    EvenPairing {x : F.Item // x ∈ F.members setId} where
  perm :=
    { toFun := F.normalizedPackingSetMateAt P hcomplete setId
      invFun := F.normalizedPackingSetMateAt P hcomplete setId
      left_inv := by
        intro item
        apply Subtype.ext
        have hmate := F.normalizedPackingSetMate_apply_apply P hcomplete ⟨setId, item⟩
        rw [F.normalizedPackingSetMateAt_observation P hcomplete setId item] at hmate
        rw [F.normalizedPackingSetMateAt_observation P hcomplete setId
          (F.normalizedPackingSetMateAt P hcomplete setId item)] at hmate
        exact congrArg (fun o : F.Observation => o.2.1) hmate
      right_inv := by
        intro item
        apply Subtype.ext
        have hmate := F.normalizedPackingSetMate_apply_apply P hcomplete ⟨setId, item⟩
        rw [F.normalizedPackingSetMateAt_observation P hcomplete setId item] at hmate
        rw [F.normalizedPackingSetMateAt_observation P hcomplete setId
          (F.normalizedPackingSetMateAt P hcomplete setId item)] at hmate
        exact congrArg (fun o : F.Observation => o.2.1) hmate }
  apply_apply := by
    intro item
    apply Subtype.ext
    have hmate := F.normalizedPackingSetMate_apply_apply P hcomplete ⟨setId, item⟩
    rw [F.normalizedPackingSetMateAt_observation P hcomplete setId item] at hmate
    rw [F.normalizedPackingSetMateAt_observation P hcomplete setId
      (F.normalizedPackingSetMateAt P hcomplete setId item)] at hmate
    exact congrArg (fun o : F.Observation => o.2.1) hmate
  apply_ne := by
    intro item hfixed
    apply F.normalizedPackingSetMate_ne P hcomplete ⟨setId, item⟩
    rw [F.normalizedPackingSetMateAt_observation P hcomplete setId item]
    apply Sigma.ext
    · rfl
    · apply (Subtype.heq_iff_coe_eq (fun _ => Iff.rfl)).mpr
      exact congrArg Subtype.val hfixed

noncomputable def normalizedPackingItemMateAt
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (item : F.Item)
    (setId : {C : F.SetId // item ∈ F.members C}) :
    {C : F.SetId // item ∈ F.members C} :=
  ⟨(F.normalizedPackingItemMate P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩).1, by
    have hitem := F.normalizedPackingItemMate_item P hcomplete
      ⟨setId.1, ⟨item, setId.2⟩⟩
    have hmem := (F.normalizedPackingItemMate P hcomplete
      ⟨setId.1, ⟨item, setId.2⟩⟩).2.2
    simpa [hitem] using hmem⟩

theorem normalizedPackingItemMateAt_observation
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (item : F.Item)
    (setId : {C : F.SetId // item ∈ F.members C}) :
    F.normalizedPackingItemMate P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩ =
      ⟨F.normalizedPackingItemMateAt P hcomplete item setId,
        ⟨item, (F.normalizedPackingItemMateAt P hcomplete item setId).2⟩⟩ := by
  refine Sigma.ext rfl ?_
  apply (Subtype.heq_iff_coe_eq (fun _ => Iff.rfl)).mpr
  exact F.normalizedPackingItemMate_item P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩

noncomputable def normalizedPackingItemEvenPairing
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (item : F.Item) :
    EvenPairing {C : F.SetId // item ∈ F.members C} where
  perm :=
    { toFun := F.normalizedPackingItemMateAt P hcomplete item
      invFun := F.normalizedPackingItemMateAt P hcomplete item
      left_inv := by
        intro setId
        apply Subtype.ext
        have hmate := F.normalizedPackingItemMate_apply_apply P hcomplete
          ⟨setId.1, ⟨item, setId.2⟩⟩
        rw [F.normalizedPackingItemMateAt_observation P hcomplete item setId] at hmate
        rw [F.normalizedPackingItemMateAt_observation P hcomplete item
          (F.normalizedPackingItemMateAt P hcomplete item setId)] at hmate
        exact congrArg Sigma.fst hmate
      right_inv := by
        intro setId
        apply Subtype.ext
        have hmate := F.normalizedPackingItemMate_apply_apply P hcomplete
          ⟨setId.1, ⟨item, setId.2⟩⟩
        rw [F.normalizedPackingItemMateAt_observation P hcomplete item setId] at hmate
        rw [F.normalizedPackingItemMateAt_observation P hcomplete item
          (F.normalizedPackingItemMateAt P hcomplete item setId)] at hmate
        exact congrArg Sigma.fst hmate }
  apply_apply := by
    intro setId
    apply Subtype.ext
    have hmate := F.normalizedPackingItemMate_apply_apply P hcomplete
      ⟨setId.1, ⟨item, setId.2⟩⟩
    rw [F.normalizedPackingItemMateAt_observation P hcomplete item setId] at hmate
    rw [F.normalizedPackingItemMateAt_observation P hcomplete item
      (F.normalizedPackingItemMateAt P hcomplete item setId)] at hmate
    exact congrArg Sigma.fst hmate
  apply_ne := by
    intro setId hfixed
    apply F.normalizedPackingItemMate_ne P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩
    rw [F.normalizedPackingItemMateAt_observation P hcomplete item setId]
    refine Sigma.ext (congrArg Subtype.val hfixed) ?_
    have hC := congrArg Subtype.val hfixed
    change (F.normalizedPackingItemMateAt P hcomplete item setId).1 = setId.1 at hC
    have hpred : (fun candidate : F.Item => candidate ∈
        F.members (F.normalizedPackingItemMateAt P hcomplete item setId).1) =
        (fun candidate : F.Item => candidate ∈ F.members setId.1) := by
      rw [hC]
    exact (Subtype.heq_iff_coe_heq rfl (heq_of_eq hpred)).mpr HEq.rfl

theorem normalizedPackingItemMate_position
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    (F.normalizedObservationPositionEquiv P hcomplete).symm
      (F.normalizedPackingItemMate P hcomplete o) =
      F.normalizedPackingItemMatePosition P
        ((F.normalizedObservationPositionEquiv P hcomplete).symm o) := by
  unfold normalizedPackingItemMate
  rw [(F.normalizedObservationPositionEquiv P hcomplete).symm_apply_apply]

theorem normalizedPackingSetMate_position
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    (F.normalizedObservationPositionEquiv P hcomplete).symm
      (F.normalizedPackingSetMate P hcomplete o) =
      F.normalizedPackingSetMatePosition P
        ((F.normalizedObservationPositionEquiv P hcomplete).symm o) := by
  unfold normalizedPackingSetMate
  rw [(F.normalizedObservationPositionEquiv P hcomplete).symm_apply_apply]

noncomputable def normalizedPackingBase
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) : ℝ :=
  F.incidenceCyclePositionBase
    ((F.normalizedObservationPositionEquiv P hcomplete).symm o).2

theorem normalizedPackingBase_eq_one_or_neg_one
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingBase P hcomplete o = 1 ∨ F.normalizedPackingBase P hcomplete o = -1 :=
  F.incidenceCyclePositionBase_eq_one_or_neg_one
    ((F.normalizedObservationPositionEquiv P hcomplete).symm o).2

theorem normalizedPackingBase_itemMate_neg
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingBase P hcomplete (F.normalizedPackingItemMate P hcomplete o) =
      -F.normalizedPackingBase P hcomplete o := by
  let position := (F.normalizedObservationPositionEquiv P hcomplete).symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  unfold normalizedPackingBase
  rw [F.normalizedPackingItemMate_position]
  exact F.incidenceCyclePositionBase_itemMate_neg hcycle hlen position.2

theorem normalizedPackingBase_setMate_neg
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    F.normalizedPackingBase P hcomplete (F.normalizedPackingSetMate P hcomplete o) =
      -F.normalizedPackingBase P hcomplete o := by
  let position := (F.normalizedObservationPositionEquiv P hcomplete).symm o
  have hcycle : ((F.normalizedPacking P).walk position.1).2.IsCycle :=
    (F.normalizedPacking P).isCycle position.1
  have hlen : Even ((F.normalizedPacking P).walk position.1).2.length :=
    F.incidence_simpleCycle_even_length hcycle
  unfold normalizedPackingBase
  rw [F.normalizedPackingSetMate_position]
  exact F.incidenceCyclePositionBase_setMate_neg hcycle hlen position.2

theorem normalizedPackingItemMate_cycle
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    ((F.normalizedObservationPositionEquiv P hcomplete).symm
      (F.normalizedPackingItemMate P hcomplete o)).1 =
      ((F.normalizedObservationPositionEquiv P hcomplete).symm o).1 := by
  rw [F.normalizedPackingItemMate_position]
  rfl

theorem normalizedPackingSetMate_cycle
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (o : F.Observation) :
    ((F.normalizedObservationPositionEquiv P hcomplete).symm
      (F.normalizedPackingSetMate P hcomplete o)).1 =
      ((F.normalizedObservationPositionEquiv P hcomplete).symm o).1 := by
  rw [F.normalizedPackingSetMate_position]
  rfl

/-- A complete simple-cycle packing of the Eulerian incidence graph induces
the paper's observation-indexed signed cycle decomposition.  Its signs and
two balance laws are constructed from the actual consecutive edges of each
normalized graph cycle. -/
noncomputable def cycleDecompositionOfCompletePacking
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) : ChoiceSystem.CycleDecomposition F := by
  let normalized := F.normalizedPacking P
  let edgeEquiv := F.normalizedObservationPositionEquiv P hcomplete
  exact
    { Cycle := P.Cycle
      instFintypeCycle := P.instFintypeCycle
      instDecidableEqCycle := P.instDecidableEqCycle
      length := fun cycle => (normalized.walk cycle).2.length
      length_pos := by
        intro cycle
        exact SimpleGraph.Walk.not_nil_iff_lt_length.mp
          (normalized.isCycle cycle).not_nil
      edgeEquiv := edgeEquiv
      base := F.normalizedPackingBase P hcomplete
      base_eq_one_or_neg_one := F.normalizedPackingBase_eq_one_or_neg_one P hcomplete
      set_balance := by
        intro a setId
        let pairing := F.normalizedPackingSetEvenPairing P hcomplete setId
        let f : {x : F.Item // x ∈ F.members setId} → ℝ := fun item =>
          F.normalizedPackingBase P hcomplete ⟨setId, item⟩ *
            Rademacher.sign (a (edgeEquiv.symm ⟨setId, item⟩).1)
        apply EvenPairing.sum_eq_zero_of_apply_neg pairing f
        intro item
        dsimp [f, pairing]
        change F.normalizedPackingBase P hcomplete
            ⟨setId, F.normalizedPackingSetMateAt P hcomplete setId item⟩ *
            Rademacher.sign (a (edgeEquiv.symm
              ⟨setId, F.normalizedPackingSetMateAt P hcomplete setId item⟩).1) =
            -(F.normalizedPackingBase P hcomplete ⟨setId, item⟩ *
              Rademacher.sign (a (edgeEquiv.symm ⟨setId, item⟩).1))
        have hobs := F.normalizedPackingSetMateAt_observation P hcomplete setId item
        rw [← hobs]
        rw [F.normalizedPackingBase_setMate_neg,
          F.normalizedPackingSetMate_cycle]
        ring
      item_balance := by
        intro a item
        let pairing := F.normalizedPackingItemEvenPairing P hcomplete item
        let f : {setId : F.SetId // item ∈ F.members setId} → ℝ := fun setId =>
          F.normalizedPackingBase P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩ *
            Rademacher.sign (a (edgeEquiv.symm ⟨setId.1, ⟨item, setId.2⟩⟩).1)
        apply EvenPairing.sum_eq_zero_of_apply_neg pairing f
        intro setId
        dsimp [f, pairing]
        change F.normalizedPackingBase P hcomplete
            ⟨(F.normalizedPackingItemMateAt P hcomplete item setId).1,
              ⟨item, (F.normalizedPackingItemMateAt P hcomplete item setId).2⟩⟩ *
            Rademacher.sign (a (edgeEquiv.symm
              ⟨(F.normalizedPackingItemMateAt P hcomplete item setId).1,
                ⟨item, (F.normalizedPackingItemMateAt P hcomplete item setId).2⟩⟩).1) =
            -(F.normalizedPackingBase P hcomplete ⟨setId.1, ⟨item, setId.2⟩⟩ *
              Rademacher.sign (a (edgeEquiv.symm ⟨setId.1, ⟨item, setId.2⟩⟩).1))
        have hobs := F.normalizedPackingItemMateAt_observation P hcomplete item setId
        rw [← hobs]
        rw [F.normalizedPackingBase_itemMate_neg,
          F.normalizedPackingItemMate_cycle]
        ring }

theorem cycleDecompositionOfCompletePacking_length
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) (cycle : P.Cycle) :
    (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle =
      (P.walk cycle).2.length := by
  change ((F.normalizedPacking P).walk cycle).2.length = (P.walk cycle).2.length
  exact F.normalizedPackingCycleWalk_length P cycle

theorem cycleDecompositionOfCompletePacking_total_length
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength)
    (hcomplete : P.IsComplete) :
    (∑ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
      (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle) = F.incidenceCount := by
  calc
    (∑ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
      (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle) =
        ∑ cycle : P.Cycle, (P.walk cycle).2.length := by
      apply Finset.sum_congr rfl
      intro cycle _
      exact F.cycleDecompositionOfCompletePacking_length P hcomplete cycle
    _ = Fintype.card F.incidenceGraph.edgeSet :=
      P.sum_length_eq_edgeSet_card hcomplete
    _ = F.incidenceGraph.edgeFinset.card := SimpleGraph.edgeFinset_card.symm
    _ = F.incidenceCount := F.incidenceGraph_edgeFinset_card

/-- Appendix Lemma 10's graph packing yields the paper's full balanced signed
cycle decomposition, while preserving the source `2n` cap and total
incidence length. -/
theorem eulerian_incidenceGraph_exists_bounded_cycleDecomposition
    (hEulerian : F.Eulerian) :
    ∃ (P : PartialSimpleCyclePacking F.incidenceGraph (2 * Fintype.card F.Item))
      (hcomplete : P.IsComplete),
      (∀ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
        (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle ≤
          2 * Fintype.card F.Item) ∧
      (∑ cycle : (F.cycleDecompositionOfCompletePacking P hcomplete).Cycle,
        (F.cycleDecompositionOfCompletePacking P hcomplete).length cycle) = F.incidenceCount := by
  obtain ⟨P, hcomplete⟩ := F.eulerian_incidenceGraph_has_complete_cycle_packing hEulerian
  refine ⟨P, hcomplete, ?_, F.cycleDecompositionOfCompletePacking_total_length P hcomplete⟩
  intro cycle
  rw [F.cycleDecompositionOfCompletePacking_length]
  exact P.length_le cycle

end ChoiceFrame

end SeshadriUgander2020IIATesting
