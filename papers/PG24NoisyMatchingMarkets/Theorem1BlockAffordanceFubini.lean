import PG24NoisyMatchingMarkets.Theorem1SourceDemandBridge
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
Fubini for a value-restricted affordance event on an arbitrary cutoff block.
This does not identify affordability with a choice: it is the direction needed
when a student chose a block only after being feasible for a college in it.
-/
theorem theorem1_sourceDemand_value_restricted_affordance_mass_eq_integral_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧
            cutoffCrossedOn active
              (noisyScore (value outcome.1) outcome.2) cutoff) =
      ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff) v
        ∂valueLaw := by
  classical
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  let event : Set (StudentType × (Fin n -> ℝ)) :=
    {outcome |
      value outcome.1 ∈ region ∧
        cutoffCrossedOn active
          (noisyScore (value outcome.1) outcome.2) cutoff}
  have hevent : MeasurableSet event := by
    let collegeEvent : Fin n -> Set (StudentType × (Fin n -> ℝ)) :=
      fun c => {outcome |
        value outcome.1 ∈ region ∧
          cutoff c < value outcome.1 + outcome.2 c}
    have hset : event = ⋃ c ∈ active, collegeEvent c := by
      ext outcome
      simp [event, collegeEvent, cutoffCrossedOn, noisyScore]
    rw [hset]
    refine Finset.measurableSet_biUnion active ?_
    intro c hc
    have hvalue_first :
        Measurable (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1) :=
      hvalue.comp measurable_fst
    have hnoise_c :
        Measurable (fun outcome : StudentType × (Fin n -> ℝ) => outcome.2 c) := by
      fun_prop
    have hscore :
        Measurable (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 + outcome.2 c) :=
      hvalue_first.add hnoise_c
    have hregion_preimage : MeasurableSet
        {outcome : StudentType × (Fin n -> ℝ) | value outcome.1 ∈ region} := by
      change MeasurableSet
        ((fun outcome : StudentType × (Fin n -> ℝ) => value outcome.1) ⁻¹' region)
      exact hregion.preimage hvalue_first
    change MeasurableSet
      ({outcome : StudentType × (Fin n -> ℝ) | value outcome.1 ∈ region} ∩
        {outcome : StudentType × (Fin n -> ℝ) |
          cutoff c < value outcome.1 + outcome.2 c})
    exact hregion_preimage.inter (measurableSet_Ioi.preimage hscore)
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
        (studentLaw.prod productLaw) :=
    (integrable_const _).indicator hevent
  have hfubini := integral_prod
    (f := event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
    hintegrable
  let affordance : ℝ -> ℝ :=
    fun v => cutoffAffordanceProbability productLaw active v cutoff
  have haffordance_integrable : Integrable affordance valueLaw := by
    simpa [affordance, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw active cutoff)
  have hregion_integrable :
      Integrable (region.indicator affordance) valueLaw :=
    haffordance_integrable.indicator hregion
  have hproduct_integral :
      (∫ outcome : StudentType × (Fin n -> ℝ),
        event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
        ∂(studentLaw.prod productLaw)) =
        ∫ student : StudentType,
          region.indicator affordance (value student) ∂studentLaw := by
    rw [hfubini]
    apply integral_congr_ae
    filter_upwards with student
    let crossing : Set (Fin n -> ℝ) :=
      {noise |
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff}
    have hcrossing : MeasurableSet crossing := by
      let collegeEvent : Fin n -> Set (Fin n -> ℝ) :=
        fun c => {noise | cutoff c < value student + noise c}
      have hset : crossing = ⋃ c ∈ active, collegeEvent c := by
        ext noise
        simp [crossing, collegeEvent, cutoffCrossedOn, noisyScore]
      rw [hset]
      refine Finset.measurableSet_biUnion active ?_
      intro c hc
      have hscore :
          Measurable (fun noise : Fin n -> ℝ => value student + noise c) := by
        fun_prop
      change MeasurableSet
        {noise : Fin n -> ℝ | cutoff c < value student + noise c}
      exact measurableSet_Ioi.preimage hscore
    by_cases hstudent : value student ∈ region
    · rw [Set.indicator_of_mem hstudent]
      have hsection :
          (fun noise : Fin n -> ℝ =>
            event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ))
              (student, noise)) =
            crossing.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) := by
        funext noise
        by_cases hcrossing_mem : noise ∈ crossing
        · have hevent_mem : (student, noise) ∈ event := by
            change value student ∈ region ∧
              cutoffCrossedOn active
                (noisyScore (value student) noise) cutoff
            exact ⟨hstudent, hcrossing_mem⟩
          rw [Set.indicator_of_mem hevent_mem,
            Set.indicator_of_mem hcrossing_mem]
        · have hevent_not_mem : (student, noise) ∉ event := by
            intro hevent_mem
            exact hcrossing_mem hevent_mem.2
          rw [Set.indicator_of_notMem hevent_not_mem,
            Set.indicator_of_notMem hcrossing_mem]
      rw [hsection]
      calc
        ∫ noise : Fin n -> ℝ,
            crossing.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) noise
            ∂productLaw = productLaw.real crossing := by
          simpa using (integral_indicator_one (μ := productLaw) hcrossing)
        _ = affordance (value student) := by
          rfl
    · rw [Set.indicator_of_notMem hstudent]
      have hsection :
          (fun noise : Fin n -> ℝ =>
            event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ))
              (student, noise)) =
            fun _ : Fin n -> ℝ => (0 : ℝ) := by
        funext noise
        have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          exact hstudent hevent_mem.1
        rw [Set.indicator_of_notMem hevent_not_mem]
      rw [hsection]
      simp
  have hmap_integral :
      (∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw) =
        ∫ v : ℝ, region.indicator affordance v ∂valueLaw := by
    calc
      (∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw) =
          ∫ v : ℝ, region.indicator affordance v
            ∂Measure.map value studentLaw := by
        symm
        exact integral_map hvalue.aemeasurable (by
          rw [hvalue_marginal]
          exact hregion_integrable.aestronglyMeasurable)
      _ = ∫ v : ℝ, region.indicator affordance v ∂valueLaw := by
        rw [hvalue_marginal]
  change (studentLaw.prod productLaw).real event = _
  calc
    (studentLaw.prod productLaw).real event =
        ∫ outcome : StudentType × (Fin n -> ℝ),
          event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
          ∂(studentLaw.prod productLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw :=
      hproduct_integral
    _ = ∫ v : ℝ, region.indicator affordance v ∂valueLaw := hmap_integral
    _ = ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff) v
        ∂valueLaw := by
      rfl

end

end PG24NoisyMatchingMarkets
