import AppliedModelingLib.Markets.Matching.Affordability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

def theorem4CoalitionAffordanceEvent {C : ℕ}
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ) :
    ℝ × (Fin (C + 1) → ℝ) → Prop :=
  fun coordinates =>
    cutoffCrossedOn active (noisyScore coordinates.1 coordinates.2) cutoff

private theorem theorem4_coalition_affordance_event_measurable
    {C : ℕ} (active : Finset (Fin (C + 1)))
    (cutoff : Fin (C + 1) → ℝ) :
    MeasurableSet (theorem4CoalitionAffordanceEvent active cutoff) := by
  classical
  let collegeEvent : Fin (C + 1) → Set (ℝ × (Fin (C + 1) → ℝ)) :=
    fun c => {coordinates | cutoff c < coordinates.1 + coordinates.2 c}
  have hset :
      (theorem4CoalitionAffordanceEvent active cutoff :
          Set (ℝ × (Fin (C + 1) → ℝ))) =
        ⋃ c ∈ active, collegeEvent c := by
    ext coordinates
    change
      (∃ c ∈ active, cutoff c < coordinates.1 + coordinates.2 c) ↔ _
    constructor
    · rintro ⟨c, hc, hscore⟩
      exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, hscore⟩⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨c, h⟩
      rcases Set.mem_iUnion.mp h with ⟨hc, hscore⟩
      exact ⟨c, hc, hscore⟩
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore : Measurable (fun coordinates : ℝ × (Fin (C + 1) → ℝ) =>
      coordinates.1 + coordinates.2 c) := by
    fun_prop
  change MeasurableSet {coordinates : ℝ × (Fin (C + 1) → ℝ) |
    cutoff c < coordinates.1 + coordinates.2 c}
  exact measurableSet_Ioi.preimage hscore

private theorem theorem4_coalition_affordance_section_measurable
    {C : ℕ} (active : Finset (Fin (C + 1))) (v : ℝ)
    (cutoff : Fin (C + 1) → ℝ) :
    MeasurableSet {noise : Fin (C + 1) → ℝ |
      cutoffCrossedOn active (noisyScore v noise) cutoff} := by
  classical
  let collegeEvent : Fin (C + 1) → Set (Fin (C + 1) → ℝ) :=
    fun c => {noise | cutoff c < v + noise c}
  have hset :
      {noise : Fin (C + 1) → ℝ |
        cutoffCrossedOn active (noisyScore v noise) cutoff} =
        ⋃ c ∈ active, collegeEvent c := by
    ext noise
    change (∃ c ∈ active, cutoff c < v + noise c) ↔ _
    constructor
    · rintro ⟨c, hc, hscore⟩
      exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, hscore⟩⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨c, h⟩
      rcases Set.mem_iUnion.mp h with ⟨hc, hscore⟩
      exact ⟨c, hc, hscore⟩
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore : Measurable (fun noise : Fin (C + 1) → ℝ => v + noise c) := by
    fun_prop
  change MeasurableSet {noise : Fin (C + 1) → ℝ | cutoff c < v + noise c}
  exact measurableSet_Ioi.preimage hscore

/--
The local iid coordinates may be a measurable marginal of an arbitrary full
outcome space.  Their affordance mass is the value-integrated local crossing
probability; no independence is required for unprojected global coordinates.
-/
theorem theorem4_integrated_coalition_affordance_eq_projected_event_mass
    {C : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hlocalCoordinates_measurable : Measurable localCoordinates)
    (hlocalCoordinates_map :
      Measure.map localCoordinates outcomeLaw =
        valueLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ) :
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) =
      eventMass outcomeLaw
        (fun outcome => theorem4CoalitionAffordanceEvent active cutoff
          (localCoordinates outcome)) := by
  let noiseProduct : Measure (Fin (C + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (C + 1) => noiseLaw)
  let event : Set (ℝ × (Fin (C + 1) → ℝ)) :=
    theorem4CoalitionAffordanceEvent active cutoff
  have hevent : MeasurableSet event :=
    theorem4_coalition_affordance_event_measurable active cutoff
  have hpreserves :
      MeasurePreserving localCoordinates outcomeLaw (valueLaw.prod noiseProduct) :=
    ⟨hlocalCoordinates_measurable, by
      simpa [noiseProduct] using hlocalCoordinates_map⟩
  have hpullback :
      eventMass outcomeLaw (fun outcome => event (localCoordinates outcome)) =
        eventMass (valueLaw.prod noiseProduct) event := by
    exact AppliedModelingLib.measureProb_preimage_of_measurePreserving
      localCoordinates hpreserves event hevent
  have hintegrable :
      Integrable (event.indicator (fun _ : ℝ × (Fin (C + 1) → ℝ) => (1 : ℝ)))
        (valueLaw.prod noiseProduct) :=
    (integrable_const _).indicator hevent
  have hfubini :=
    integral_prod
      (event.indicator (fun _ : ℝ × (Fin (C + 1) → ℝ) => (1 : ℝ)))
      hintegrable
  have hproduct :
      eventMass (valueLaw.prod noiseProduct) event =
        ∫ value : ℝ,
          cutoffCrossingProbability noiseProduct active value cutoff ∂valueLaw := by
    change (valueLaw.prod noiseProduct).real event = _
    calc
      (valueLaw.prod noiseProduct).real event =
          ∫ coordinates : ℝ × (Fin (C + 1) → ℝ),
            event.indicator (fun _ : ℝ × (Fin (C + 1) → ℝ) => (1 : ℝ))
              coordinates ∂(valueLaw.prod noiseProduct) :=
        (integral_indicator_one hevent).symm
      _ = ∫ value : ℝ,
          ∫ noise : Fin (C + 1) → ℝ,
            event.indicator (fun _ : ℝ × (Fin (C + 1) → ℝ) => (1 : ℝ))
              (value, noise) ∂noiseProduct ∂valueLaw := hfubini
      _ = ∫ value : ℝ,
          cutoffCrossingProbability noiseProduct active value cutoff ∂valueLaw := by
        apply integral_congr_ae
        filter_upwards with value
        let crossing : Set (Fin (C + 1) → ℝ) :=
          {noise | cutoffCrossedOn active (noisyScore value noise) cutoff}
        have hcrossing : MeasurableSet crossing :=
          theorem4_coalition_affordance_section_measurable active value cutoff
        have hsection :
            (fun noise : Fin (C + 1) → ℝ =>
              event.indicator
                (fun _ : ℝ × (Fin (C + 1) → ℝ) => (1 : ℝ))
                (value, noise)) =
              crossing.indicator (fun _ : Fin (C + 1) → ℝ => (1 : ℝ)) := by
          funext noise
          by_cases hcross :
              cutoffCrossedOn active (noisyScore value noise) cutoff
          · have hevent_mem : (value, noise) ∈ event := by
              exact hcross
            have hcrossing_mem : noise ∈ crossing := by
              exact hcross
            rw [Set.indicator_of_mem hevent_mem,
              Set.indicator_of_mem hcrossing_mem]
          · have hevent_not_mem : (value, noise) ∉ event := by
              exact hcross
            have hcrossing_not_mem : noise ∉ crossing := by
              exact hcross
            rw [Set.indicator_of_notMem hevent_not_mem,
              Set.indicator_of_notMem hcrossing_not_mem]
        rw [hsection]
        calc
          ∫ noise : Fin (C + 1) → ℝ,
              crossing.indicator (fun _ : Fin (C + 1) → ℝ => (1 : ℝ)) noise
              ∂noiseProduct = noiseProduct.real crossing := by
            simpa using (integral_indicator_one (μ := noiseProduct) hcrossing)
          _ = cutoffCrossingProbability noiseProduct active value cutoff := by
            rfl
  calc
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) =
        eventMass (valueLaw.prod noiseProduct) event := by
      simpa [noiseProduct] using hproduct.symm
    _ = eventMass outcomeLaw (fun outcome => event (localCoordinates outcome)) :=
      hpullback.symm
    _ = eventMass outcomeLaw
        (fun outcome => theorem4CoalitionAffordanceEvent active cutoff
          (localCoordinates outcome)) := by
      rfl

/--
Local coalition affordability can be charged to global matching whenever the
source choice semantics sends every locally affordable projected outcome to a
globally selected college.  External preferences and external noise remain in
`Outcome`; only the stated local marginal is used.
-/
theorem theorem4_integrated_coalition_affordance_le_global_matched_mass
    {C : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsFiniteMeasure outcomeLaw]
    {GlobalCollege : Type*} [Fintype GlobalCollege]
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hlocalCoordinates_measurable : Measurable localCoordinates)
    (hlocalCoordinates_map :
      Measure.map localCoordinates outcomeLaw =
        valueLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ)
    (hlocal_affordance_implies_global_match :
      ∀ outcome : Outcome,
        theorem4CoalitionAffordanceEvent active cutoff (localCoordinates outcome) →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) :
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) ≤
      eventMass outcomeLaw
        (chosenInActive globalChoice (Finset.univ : Finset GlobalCollege)) := by
  calc
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) =
        eventMass outcomeLaw
          (fun outcome => theorem4CoalitionAffordanceEvent active cutoff
            (localCoordinates outcome)) :=
      theorem4_integrated_coalition_affordance_eq_projected_event_mass
        valueLaw noiseLaw outcomeLaw localCoordinates
        hlocalCoordinates_measurable hlocalCoordinates_map active cutoff
    _ ≤ eventMass outcomeLaw
        (chosenInActive globalChoice (Finset.univ : Finset GlobalCollege)) :=
      eventMass_mono outcomeLaw hlocal_affordance_implies_global_match

theorem theorem4_integrated_coalition_affordance_global_match_witness
    {C : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsFiniteMeasure outcomeLaw]
    {GlobalCollege : Type*} [Fintype GlobalCollege]
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hlocalCoordinates_measurable : Measurable localCoordinates)
    (hlocalCoordinates_map :
      Measure.map localCoordinates outcomeLaw =
        valueLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ)
    (hlocal_affordance_implies_global_match :
      ∀ outcome : Outcome,
        theorem4CoalitionAffordanceEvent active cutoff (localCoordinates outcome) →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) :
    ∃ event : Outcome → Prop,
      (∫ value : ℝ,
        cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
          ∂valueLaw) ≤ eventMass outcomeLaw event ∧
        (∀ outcome : Outcome, event outcome →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) := by
  refine ⟨fun outcome => theorem4CoalitionAffordanceEvent active cutoff
    (localCoordinates outcome), ?_, hlocal_affordance_implies_global_match⟩
  exact le_of_eq
    (theorem4_integrated_coalition_affordance_eq_projected_event_mass
      valueLaw noiseLaw outcomeLaw localCoordinates
      hlocalCoordinates_measurable hlocalCoordinates_map active cutoff)

end

end PG24NoisyMatchingMarkets
