import PG24NoisyMatchingMarkets.Theorem2TwoScaleIidBlockEvent
import Mathlib.MeasureTheory.Integral.Prod

/-!
# PG24 Theorem 2 two-scale source-model bridge

This module constructs the small-only event in the actual source sampling
space `StudentType × noise`.  Student preferences remain in `StudentType` and
may depend arbitrarily on value; only the measurable value marginal is fixed.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/-- The source-model small-only event with arbitrary student types. -/
def theorem2StudentTypeSmallOnlyEvent
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (small large : Finset (Fin n))
    (cutoff : Fin n -> ℝ) : StudentType × (Fin n -> ℝ) -> Prop :=
  fun outcome =>
    theorem2SmallOnlyAffordanceEvent small large (value outcome.1) cutoff outcome.2

private theorem theorem2_studentType_crossing_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : StudentType × (Fin n -> ℝ) |
        cutoffCrossedOn active
          (noisyScore (value outcome.1) outcome.2) cutoff} := by
  classical
  let collegeEvent : Fin n -> Set (StudentType × (Fin n -> ℝ)) :=
    fun c => {outcome | cutoff c < value outcome.1 + outcome.2 c}
  have hset :
      {outcome : StudentType × (Fin n -> ℝ) |
        cutoffCrossedOn active
          (noisyScore (value outcome.1) outcome.2) cutoff} =
        ⋃ c ∈ active, collegeEvent c := by
    ext outcome
    simp [collegeEvent, cutoffCrossedOn, noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hvalue_first :
      Measurable (fun outcome : StudentType × (Fin n -> ℝ) => value outcome.1) :=
    hvalue.comp measurable_fst
  have hnoise_c :
      Measurable (fun outcome : StudentType × (Fin n -> ℝ) => outcome.2 c) := by
    fun_prop
  have hscore :
      Measurable (fun outcome : StudentType × (Fin n -> ℝ) =>
        value outcome.1 + outcome.2 c) :=
    hvalue_first.add hnoise_c
  change MeasurableSet
    {outcome : StudentType × (Fin n -> ℝ) |
      cutoff c < value outcome.1 + outcome.2 c}
  exact measurableSet_Ioi.preimage hscore

/-- The arbitrary-student-type small-only event is measurable. -/
theorem theorem2StudentTypeSmallOnlyEvent_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (small large : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : StudentType × (Fin n -> ℝ) |
        theorem2StudentTypeSmallOnlyEvent value small large cutoff outcome} := by
  change MeasurableSet
    ({outcome : StudentType × (Fin n -> ℝ) |
      cutoffCrossedOn small
        (noisyScore (value outcome.1) outcome.2) cutoff} ∩
      {outcome : StudentType × (Fin n -> ℝ) |
        cutoffCrossedOn large
          (noisyScore (value outcome.1) outcome.2) cutoff}ᶜ)
  exact (theorem2_studentType_crossing_measurable value hvalue small cutoff).inter
    (theorem2_studentType_crossing_measurable value hvalue large cutoff).compl

/--
The source demand rules force the small-only event into choices of the small
block.  `demand = none` exactly characterizes no affordability, while a chosen
college must be affordable; neither condition contains an asymptotic claim.
-/
theorem theorem2_sourceDemand_chosenInSmall_of_smallOnly
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (small large : Finset (Fin n))
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college) :
    ∀ outcome : StudentType × (Fin n -> ℝ),
      theorem2StudentTypeSmallOnlyEvent value small large cutoff outcome ->
        chosenInActive demand small outcome := by
  intro outcome hsmallOnly
  rcases hsmallOnly with ⟨hsmall, hnot_large⟩
  have hwhole_cross :
      cutoffCrossedOn (Finset.univ : Finset (Fin n))
        (noisyScore (value outcome.1) outcome.2) cutoff := by
    rcases hsmall with ⟨college, hcollege_small, hcross⟩
    exact ⟨college, by simp, hcross⟩
  have hnot_none : demand outcome ≠ none := by
    intro hnone
    exact ((hdemand_none_iff_no_crossed outcome).mp hnone) hwhole_cross
  cases hdemand : demand outcome with
  | none => exact False.elim (hnot_none hdemand)
  | some college =>
      refine ⟨college, ?_, hdemand⟩
      have hcollege_cross : cutoff college < value outcome.1 + outcome.2 college :=
        hchosen_feasible outcome college hdemand
      have hcollege_union : college ∈ small ∪ large := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hcollege_union with hcollege_small | hcollege_large
      · exact hcollege_small
      · exfalso
        apply hnot_large
        exact ⟨college, hcollege_large, by
          simpa [noisyScore] using hcollege_cross⟩

/--
The small-only event has the expected value-indexed iid-noise integral even
when preferences are carried by an arbitrary student-type coordinate.  This
uses only the value marginal; it does not factor student preferences from
values.
-/
theorem theorem2_sourceModel_smallOnly_eventMass_eq_integral
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    (cutoff : Fin n -> ℝ) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) =
      ∫ v : ℝ,
        (Measure.pi (fun _ : Fin n => noiseLaw)).real
          {noise : Fin n -> ℝ |
            theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
        ∂valueLaw := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let event : Set (StudentType × (Fin n -> ℝ)) :=
    {outcome |
      theorem2StudentTypeSmallOnlyEvent value small large cutoff outcome}
  have hevent : MeasurableSet event := by
    simpa [event] using
      (theorem2StudentTypeSmallOnlyEvent_measurable
        value hvalue small large cutoff)
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
        (studentLaw.prod productLaw) :=
    (integrable_const _).indicator hevent
  have hfubini := integral_prod
    (f := event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
    hintegrable
  let kernel : ℝ -> ℝ :=
    fun v => productLaw.real
      {noise : Fin n -> ℝ |
        theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
  have hkernel_integrable : Integrable kernel valueLaw := by
    simpa [kernel, productLaw] using
      (theorem2_iid_smallOnly_probability_integrable
        valueLaw noiseLaw small large hdisjoint cutoff)
  have hproduct_integral :
      (∫ outcome : StudentType × (Fin n -> ℝ),
        event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
        ∂(studentLaw.prod productLaw)) =
        ∫ student : StudentType, kernel (value student) ∂studentLaw := by
    rw [hfubini]
    apply integral_congr_ae
    filter_upwards with student
    let sectionSet : Set (Fin n -> ℝ) :=
      {noise |
        theorem2SmallOnlyAffordanceEvent small large (value student) cutoff noise}
    have hsection : MeasurableSet sectionSet := by
      simpa [sectionSet, theorem2SmallOnlyAffordanceProductEvent] using
        (theorem2SmallOnlyAffordanceProductEvent_section_measurable
          small large (value student) cutoff)
    have hsection_eq :
        (fun noise : Fin n -> ℝ =>
          event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ))
            (student, noise)) =
          sectionSet.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) := by
      funext noise
      by_cases hmem : noise ∈ sectionSet
      · have hevent_mem : (student, noise) ∈ event := by
          simpa [event, sectionSet, theorem2StudentTypeSmallOnlyEvent] using hmem
        rw [Set.indicator_of_mem hevent_mem, Set.indicator_of_mem hmem]
      · have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          apply hmem
          simpa [event, sectionSet, theorem2StudentTypeSmallOnlyEvent] using hevent_mem
        rw [Set.indicator_of_notMem hevent_not_mem, Set.indicator_of_notMem hmem]
    rw [hsection_eq]
    calc
      ∫ noise : Fin n -> ℝ,
          sectionSet.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) noise
          ∂productLaw = productLaw.real sectionSet := by
        simpa using (integral_indicator_one (μ := productLaw) hsection)
      _ = kernel (value student) := by
        rfl
  have hmap_integral :
      (∫ student : StudentType, kernel (value student) ∂studentLaw) =
        ∫ v : ℝ, kernel v ∂valueLaw := by
    calc
      (∫ student : StudentType, kernel (value student) ∂studentLaw) =
          ∫ v : ℝ, kernel v ∂Measure.map value studentLaw := by
        symm
        exact integral_map hvalue.aemeasurable (by
          rw [hvalue_marginal]
          exact hkernel_integrable.aestronglyMeasurable)
      _ = ∫ v : ℝ, kernel v ∂valueLaw := by
        rw [hvalue_marginal]
  change (studentLaw.prod productLaw).real event = _
  calc
    (studentLaw.prod productLaw).real event =
        ∫ outcome : StudentType × (Fin n -> ℝ),
          event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
          ∂(studentLaw.prod productLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ student : StudentType, kernel (value student) ∂studentLaw :=
      hproduct_integral
    _ = ∫ v : ℝ, kernel v ∂valueLaw := hmap_integral
    _ = ∫ v : ℝ,
        (Measure.pi (fun _ : Fin n => noiseLaw)).real
          {noise : Fin n -> ℝ |
            theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
        ∂valueLaw := by
      rfl

/--
The iid small-only lower bound lifts to the actual source sampling space.
The conclusion is obtained by the product-noise calculation and the proved
value-marginal transport above, rather than by a local event-mass assumption.
-/
theorem theorem2_twoScale_integral_le_sourceModel_smallOnly_eventMass
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    {totalSupply delta endpoint sigma : ℝ} (cutoff : Fin n -> ℝ)
    (hresidual : ∀ v : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff) :
    (∫ v : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) small v cutoff
      ∂valueLaw) ≤
      eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  have hvalue_event :
      eventMass (valueLaw.prod productLaw)
        (theorem2SmallOnlyAffordanceProductEvent small large cutoff) =
        ∫ v : ℝ,
          productLaw.real
            {noise : Fin n -> ℝ |
              theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
          ∂valueLaw := by
    exact theorem2_eventMass_eq_integral_section_probability
      valueLaw productLaw
      (theorem2SmallOnlyAffordanceProductEvent small large cutoff)
      (theorem2SmallOnlyAffordanceProductEvent_measurable small large cutoff)
      (fun v =>
        theorem2SmallOnlyAffordanceProductEvent_section_measurable
          small large v cutoff)
  have hsource_event :
      eventMass (studentLaw.prod productLaw)
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) =
        ∫ v : ℝ,
          productLaw.real
            {noise : Fin n -> ℝ |
              theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
          ∂valueLaw := by
    simpa [productLaw] using
      (theorem2_sourceModel_smallOnly_eventMass_eq_integral
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
        small large hdisjoint cutoff)
  calc
    (∫ v : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        cutoffAffordanceProbability productLaw small v cutoff
      ∂valueLaw) ≤
        eventMass (valueLaw.prod productLaw)
          (theorem2SmallOnlyAffordanceProductEvent small large cutoff) := by
      simpa [productLaw] using
        (theorem2_twoScale_integral_le_smallOnly_eventMass_of_iid
          valueLaw noiseLaw small large hdisjoint cutoff hresidual)
    _ = ∫ v : ℝ,
        productLaw.real
          {noise : Fin n -> ℝ |
            theorem2SmallOnlyAffordanceEvent small large v cutoff noise}
        ∂valueLaw := hvalue_event
    _ = eventMass
        (studentLaw.prod productLaw)
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) :=
      hsource_event.symm

/--
Once the source demand rule is connected to a chosen college and clearing,
the source-model small-only event has at most the small block's capacity.
-/
theorem theorem2_sourceModel_smallOnly_eventMass_le_activeCapacity
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand small = ∑ c ∈ small, aggregateDemand c)
    (hclearing : ∀ c ∈ small, aggregateDemand c = capacity c) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) ≤
      activeCapacity small capacity := by
  exact theorem2_eventMass_le_activeCapacity_of_choice_and_clearing
    (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
    demand
    (theorem2StudentTypeSmallOnlyEvent value small large cutoff)
    small aggregateDemand capacity
    (theorem2_sourceDemand_chosenInSmall_of_smallOnly
      value small large hcover cutoff demand
      hdemand_none_iff_no_crossed hchosen_feasible)
    hchoice_mass hclearing

/--
The complete repaired small-block capacity inequality on the source sampling
space.  Its analytic and probability components are proved from the actual
value marginal and iid noise; the remaining hypotheses are the source
market's interval, residual, demand, and clearing facts.
-/
theorem theorem2_twoScale_sourceModel_smallFirm_capacity_lower_bound
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {region : Set ℝ} (hregion_meas : MeasurableSet region)
    {totalSupply delta endpoint sigma vStar : ℝ} (cutoff : Fin n -> ℝ)
    (hregion_mass : Real.sqrt delta ≤ valueLaw.real region)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vStar ≤ w)
    (hresidual : ∀ v : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand small = ∑ c ∈ small, aggregateDemand c)
    (hclearing : ∀ c ∈ small, aggregateDemand c = capacity c) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) small vStar cutoff ≤
      activeCapacity small capacity := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pSmall : ℝ -> ℝ :=
    fun v => cutoffAffordanceProbability productLaw small v cutoff
  have hpSmall_integrable : Integrable pSmall valueLaw := by
    simpa [pSmall, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw small cutoff)
  have hintegrable : Integrable
      (fun w : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall w) valueLaw := by
    simpa using hpSmall_integrable.const_mul
      (theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
  have hp_star_nonneg : 0 ≤ pSmall vStar := by
    exact cutoffAffordanceProbability_nonneg productLaw small vStar cutoff
  have hp_mono : Monotone pSmall := by
    intro v w hvw
    exact cutoffAffordanceProbability_mono_value productLaw hvw
  have hnonneg_compl : ∀ w : ℝ, w ∉ region ->
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        pSmall w := by
    intro w _
    exact mul_nonneg hdenom_nonneg
      (cutoffAffordanceProbability_nonneg productLaw small w cutoff)
  have hintegral_le_event :
      (∫ w : ℝ,
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall w ∂valueLaw) ≤
        eventMass (studentLaw.prod productLaw)
          (theorem2StudentTypeSmallOnlyEvent value small large cutoff) := by
    simpa [pSmall, productLaw] using
      (theorem2_twoScale_integral_le_sourceModel_smallOnly_eventMass
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
        small large hdisjoint cutoff hresidual)
  have hevent_le_capacity :
      eventMass (studentLaw.prod productLaw)
        (theorem2StudentTypeSmallOnlyEvent value small large cutoff) ≤
        activeCapacity small capacity := by
    simpa [productLaw] using
      (theorem2_sourceModel_smallOnly_eventMass_le_activeCapacity
        studentLaw value noiseLaw small large hcover cutoff demand
        hdemand_none_iff_no_crossed hchosen_feasible aggregateDemand capacity
        hchoice_mass hclearing)
  change Real.sqrt delta *
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        pSmall vStar ≤ activeCapacity small capacity
  have hinterval_le_event :
      Real.sqrt delta *
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
            pSmall vStar ≤
        eventMass (studentLaw.prod productLaw)
          (theorem2StudentTypeSmallOnlyEvent value small large cutoff) :=
    theorem2_twoScale_smallFirm_matchedMass_lower_bound_of_interval_integral
      valueLaw hregion_meas hintegrable hregion_mass hdenom_nonneg hp_star_nonneg
      hp_mono hregion_ge hnonneg_compl hintegral_le_event
  exact hinterval_le_event.trans hevent_le_capacity

end

end PG24NoisyMatchingMarkets
