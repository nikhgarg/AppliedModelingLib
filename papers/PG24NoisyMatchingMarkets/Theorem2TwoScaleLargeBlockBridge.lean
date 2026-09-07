import PG24NoisyMatchingMarkets.Theorem2TwoScaleSourceModelBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# PG24 Theorem 2 two-scale large-block bridge

This module proves the capacity side of the large-block estimate on the
source sampling space.  In particular, it derives the integral upper bound
from iid value/noise sampling, demand semantics, and global clearing rather
than taking a large-endpoint event inequality as a package assumption.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/-- A source-model event that a student can afford some college in `active`. -/
def theorem2StudentTypeAffordanceEvent
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (active : Finset (Fin n))
    (cutoff : Fin n -> ℝ) : StudentType × (Fin n -> ℝ) -> Prop :=
  fun outcome =>
    cutoffCrossedOn active
      (noisyScore (value outcome.1) outcome.2) cutoff

/-- The arbitrary-student-type affordance event is measurable. -/
theorem theorem2StudentTypeAffordanceEvent_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : StudentType × (Fin n -> ℝ) |
        theorem2StudentTypeAffordanceEvent value active cutoff outcome} := by
  classical
  let collegeEvent : Fin n -> Set (StudentType × (Fin n -> ℝ)) :=
    fun c => {outcome | cutoff c < value outcome.1 + outcome.2 c}
  have hset :
      {outcome : StudentType × (Fin n -> ℝ) |
        theorem2StudentTypeAffordanceEvent value active cutoff outcome} =
        ⋃ c ∈ active, collegeEvent c := by
    ext outcome
    simp [theorem2StudentTypeAffordanceEvent, collegeEvent,
      cutoffCrossedOn, noisyScore]
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

/--
Fubini and the prescribed value marginal identify the source-model mass of a
block-affordance event with the corresponding value integral.  Preferences
remain arbitrary in `StudentType`.
-/
theorem theorem2_sourceModel_affordance_eventMass_eq_integral
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeAffordanceEvent value active cutoff) =
      ∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff
        ∂valueLaw := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let event : Set (StudentType × (Fin n -> ℝ)) :=
    {outcome | theorem2StudentTypeAffordanceEvent value active cutoff outcome}
  have hevent : MeasurableSet event := by
    simpa [event] using
      (theorem2StudentTypeAffordanceEvent_measurable value hvalue active cutoff)
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
        (studentLaw.prod productLaw) :=
    (integrable_const _).indicator hevent
  have hfubini := integral_prod
    (f := event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
    hintegrable
  let kernel : ℝ -> ℝ :=
    fun v => cutoffAffordanceProbability productLaw active v cutoff
  have hkernel_integrable : Integrable kernel valueLaw := by
    simpa [kernel, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw active cutoff)
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
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff}
    have hsection : MeasurableSet sectionSet := by
      classical
      let collegeEvent : Fin n -> Set (Fin n -> ℝ) :=
        fun c => {noise | cutoff c < value student + noise c}
      have hset : sectionSet = ⋃ c ∈ active, collegeEvent c := by
        ext noise
        simp [sectionSet, collegeEvent, cutoffCrossedOn, noisyScore]
      rw [hset]
      refine Finset.measurableSet_biUnion active ?_
      intro c hc
      have hscore : Measurable (fun noise : Fin n -> ℝ => value student + noise c) := by
        fun_prop
      change MeasurableSet {noise : Fin n -> ℝ | value student + noise c ∈ Set.Ioi (cutoff c)}
      exact measurableSet_Ioi.preimage hscore
    have hsection_eq :
        (fun noise : Fin n -> ℝ =>
          event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ))
            (student, noise)) =
          sectionSet.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) := by
      funext noise
      by_cases hmem : noise ∈ sectionSet
      · have hevent_mem : (student, noise) ∈ event := by
          simpa [event, sectionSet, theorem2StudentTypeAffordanceEvent] using hmem
        rw [Set.indicator_of_mem hevent_mem, Set.indicator_of_mem hmem]
      · have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          apply hmem
          simpa [event, sectionSet, theorem2StudentTypeAffordanceEvent] using hevent_mem
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
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff
        ∂valueLaw := by
      rfl

/-- Affording any member of an active block forces a nonempty source demand. -/
theorem theorem2_sourceDemand_chosenSome_of_affordance
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (active : Finset (Fin n))
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff) :
    ∀ outcome : StudentType × (Fin n -> ℝ),
      theorem2StudentTypeAffordanceEvent value active cutoff outcome ->
        chosenInActive demand (Finset.univ : Finset (Fin n)) outcome := by
  intro outcome hafford
  have hwhole_cross :
      cutoffCrossedOn (Finset.univ : Finset (Fin n))
        (noisyScore (value outcome.1) outcome.2) cutoff := by
    rcases hafford with ⟨college, hcollege_active, hcross⟩
    exact ⟨college, by simp, hcross⟩
  have hnot_none : demand outcome ≠ none := by
    intro hnone
    exact ((hdemand_none_iff_no_crossed outcome).mp hnone) hwhole_cross
  cases hdemand : demand outcome with
  | none => exact False.elim (hnot_none hdemand)
  | some college => exact ⟨college, by simp, hdemand⟩

/--
Global clearing bounds the mass of a block-affordance event by total supply.
The event need only imply that some college is demanded; it does not need to
identify which college the student chooses.
-/
theorem theorem2_sourceModel_affordance_eventMass_le_totalSupply
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (totalSupply : ℝ) (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeAffordanceEvent value active cutoff) ≤ totalSupply := by
  have hevent_capacity :
      eventMass
          (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
          (theorem2StudentTypeAffordanceEvent value active cutoff) ≤
        activeCapacity (Finset.univ : Finset (Fin n)) capacity := by
    exact theorem2_eventMass_le_activeCapacity_of_choice_and_clearing
      (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
      demand
      (theorem2StudentTypeAffordanceEvent value active cutoff)
      (Finset.univ : Finset (Fin n)) aggregateDemand capacity
      (theorem2_sourceDemand_chosenSome_of_affordance
        value active cutoff demand hdemand_none_iff_no_crossed)
      hchoice_mass
      (fun c hc => hclearing c)
  calc
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeAffordanceEvent value active cutoff) ≤
      activeCapacity (Finset.univ : Finset (Fin n)) capacity := hevent_capacity
    _ = ∑ c : Fin n, capacity c := by
      simp [activeCapacity]
    _ = totalSupply := htotal_capacity

/--
The actual iid source model therefore supplies the large-block integral upper
bound used in `proof-amplifying.tex:174-181`.
-/
theorem theorem2_sourceModel_integral_affordance_le_totalSupply
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (totalSupply : ℝ) (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    (∫ v : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff
      ∂valueLaw) ≤ totalSupply := by
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff
      ∂valueLaw) =
        eventMass
          (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
          (theorem2StudentTypeAffordanceEvent value active cutoff) := by
      symm
      exact theorem2_sourceModel_affordance_eventMass_eq_integral
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw active cutoff
    _ ≤ totalSupply :=
      theorem2_sourceModel_affordance_eventMass_le_totalSupply
        studentLaw value noiseLaw active cutoff demand
        hdemand_none_iff_no_crossed aggregateDemand capacity hchoice_mass
        hclearing totalSupply htotal_capacity

/--
The low endpoint of the large block is at most `totalSupply + delta` once its
affordance integral is at most total supply on a value interval of mass at
least `1 - delta`.  This is the scalar capacity calculation at
`proof-amplifying.tex:174-181`.
-/
theorem theorem2_twoScale_largeLowEndpoint_upper_of_interval_integral
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {region : Set ℝ} {delta totalSupply vLow : ℝ}
    {pLarge : ℝ -> ℝ}
    (hregion_meas : MeasurableSet region)
    (hintegrable : Integrable pLarge valueLaw)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hp_low_nonneg : 0 ≤ pLarge vLow)
    (hp_mono : Monotone pLarge)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vLow ≤ w)
    (hnonneg_compl : ∀ w : ℝ, w ∉ region -> 0 ≤ pLarge w)
    (hintegral_le_supply : (∫ w : ℝ, pLarge w ∂valueLaw) ≤ totalSupply)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1) :
    pLarge vLow ≤ totalSupply + delta := by
  have hmass_upper : (1 - delta) * pLarge vLow ≤ totalSupply := by
    exact le_trans
      (theorem2_largeFirm_interval_integral_lower_bound
        valueLaw hregion_meas hintegrable hregion_mass hp_low_nonneg hp_mono
        hregion_ge hnonneg_compl)
      hintegral_le_supply
  exact theorem2_lowEndpoint_upper_of_interval_mass_bound
    hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hmass_upper

/--
The previous interval calculation specializes to the actual source model:
global clearing, rather than a conclusion-shaped local event package, supplies
the integral upper bound.
-/
theorem theorem2_twoScale_largeLowEndpoint_upper_of_sourceModel_globalClearing
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (large : Finset (Fin n))
    {region : Set ℝ} {delta totalSupply vLow : ℝ}
    (cutoff : Fin n -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vLow ≤ w)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
      totalSupply + delta := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pLarge : ℝ -> ℝ :=
    fun v => cutoffAffordanceProbability productLaw large v cutoff
  have hintegrable : Integrable pLarge valueLaw := by
    simpa [pLarge, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw large cutoff)
  have hp_low_nonneg : 0 ≤ pLarge vLow := by
    exact cutoffAffordanceProbability_nonneg productLaw large vLow cutoff
  have hp_mono : Monotone pLarge := by
    intro x y hxy
    exact cutoffAffordanceProbability_mono_value productLaw hxy
  have hnonneg_compl : ∀ w : ℝ, w ∉ region -> 0 ≤ pLarge w := by
    intro w _
    exact cutoffAffordanceProbability_nonneg productLaw large w cutoff
  have hintegral_le_supply :
      (∫ w : ℝ, pLarge w ∂valueLaw) ≤ totalSupply := by
    simpa [pLarge, productLaw] using
      (theorem2_sourceModel_integral_affordance_le_totalSupply
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff
        demand hdemand_none_iff_no_crossed aggregateDemand capacity
        hchoice_mass hclearing totalSupply htotal_capacity)
  change pLarge vLow ≤ totalSupply + delta
  exact theorem2_twoScale_largeLowEndpoint_upper_of_interval_integral
    valueLaw hregion_meas hintegrable hregion_mass hp_low_nonneg hp_mono
    hregion_ge hnonneg_compl hintegral_le_supply hdelta_pos
    htotalSupply_nonneg htotalSupply_delta_lt_one

/--
An upper bound at the low endpoint and the independent-noise endpoint gap
give the residual no-large-affordance mass required by the repaired small
block argument.  The split `delta` and comparison endpoint remain separate.
-/
theorem theorem2_twoScale_residual_of_largeLowEndpoint_and_endpoint_gap
    {pLarge : ℝ -> ℝ}
    {totalSupply delta endpoint sigma vLow vHigh v : ℝ}
    (hp_mono : Monotone pLarge)
    (hv_high : v ≤ vHigh)
    (hlow : pLarge vLow ≤ totalSupply + delta)
    (hgap :
      pLarge vHigh - pLarge vLow ≤
        theorem2_twoScaleProductGap endpoint sigma) :
    theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
      1 - pLarge v := by
  have hhigh : pLarge v ≤ pLarge vHigh := hp_mono hv_high
  unfold theorem2_twoScaleDenominator
  linarith

/--
The iid failure-ratio calculation behind `lt-approx-F2`, specialized to the
separate comparison endpoint.  Its hypotheses are per-college tail facts, not
a conclusion about the large-block affordability probability.
-/
theorem theorem2_twoScale_iidLargeEndpointGap_of_failureRatio
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (large : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    {endpoint sigma vLow vHigh : ℝ}
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hn_pos : 0 < (n : ℝ))
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / (n : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow) ≤ 1) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
      theorem2_twoScaleProductGap endpoint sigma := by
  let qLow : Fin n -> ℝ :=
    fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow)
  let qHigh : Fin n -> ℝ :=
    fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh)
  have hcard : (large.card : ℝ) ≤ (n : ℝ) := by
    have hcard_nat : large.card ≤ Fintype.card (Fin n) :=
      Finset.card_le_univ large
    simpa using (show (large.card : ℝ) ≤ (Fintype.card (Fin n) : ℝ) from by
      exact_mod_cast hcard_nat)
  have hratio : ∀ c ∈ large,
      Real.exp (-(2 * endpoint * sigma / (n : ℝ))) ≤
        (1 - qHigh c) / (1 - qLow c) := by
    intro c hc
    simpa [qLow, qHigh] using hfailure_ratio c hc
  have hlow_pos : ∀ c ∈ large, 0 < 1 - qLow c := by
    intro c hc
    simpa [qLow] using hlow_failure_pos c hc
  have hlow_le_one : ∀ c ∈ large, 1 - qLow c ≤ 1 := by
    intro c hc
    simpa [qLow] using hlow_failure_le_one c hc
  have hproduct_gap :=
    independentAffordanceProbability_difference_le_exp_error
      large qLow qHigh (C := n) hendpoint_nonneg hsigma_nonneg hn_pos hcard
      hratio hlow_pos hlow_le_one
  have hhigh_eq :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff =
        independentAffordanceProbability large qHigh := by
    simpa [qHigh] using
      (cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw large vHigh cutoff)
  have hlow_eq :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff =
        independentAffordanceProbability large qLow := by
    simpa [qLow] using
      (cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw large vLow cutoff)
  calc
    cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff =
        independentAffordanceProbability large qHigh -
          independentAffordanceProbability large qLow := by
      rw [hhigh_eq, hlow_eq]
    _ ≤ 1 - Real.exp (-(2 * endpoint * sigma)) := hproduct_gap
    _ = theorem2_twoScaleProductGap endpoint sigma := by
      rfl

/--
The source-model large-block capacity argument, combined with a separately
proved long-tail product comparison, yields the residual inequality consumed
by the small-only event proof.
-/
theorem theorem2_twoScale_residual_of_sourceModel_globalClearing_and_endpoint_gap
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (large : Finset (Fin n))
    {region : Set ℝ} {totalSupply delta endpoint sigma vLow vHigh v : ℝ}
    (cutoff : Fin n -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vLow ≤ w)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hv_high : v ≤ vHigh)
    (hgap :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
        theorem2_twoScaleProductGap endpoint sigma)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
      1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pLarge : ℝ -> ℝ :=
    fun x => cutoffAffordanceProbability productLaw large x cutoff
  have hp_mono : Monotone pLarge := by
    intro x y hxy
    exact cutoffAffordanceProbability_mono_value productLaw hxy
  have hlow : pLarge vLow ≤ totalSupply + delta := by
    simpa [pLarge, productLaw] using
      (theorem2_twoScale_largeLowEndpoint_upper_of_sourceModel_globalClearing
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff
        hregion_meas hregion_mass hregion_ge hdelta_pos htotalSupply_nonneg
        htotalSupply_delta_lt_one demand hdemand_none_iff_no_crossed
        aggregateDemand capacity hchoice_mass hclearing htotal_capacity)
  have hgap' : pLarge vHigh - pLarge vLow ≤
      theorem2_twoScaleProductGap endpoint sigma := by
    simpa [pLarge, productLaw] using hgap
  change theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
    1 - pLarge v
  exact theorem2_twoScale_residual_of_largeLowEndpoint_and_endpoint_gap
    hp_mono hv_high hlow hgap'

/--
Fully primitive residual bridge: combine source iid sampling and global
clearing with the per-college failure-ratio conditions from the long-tail
comparison.  No endpoint-window or local-event conclusion is assumed.
-/
theorem theorem2_twoScale_residual_of_sourceModel_globalClearing_and_failureRatio
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (large : Finset (Fin n))
    {region : Set ℝ} {totalSupply delta endpoint sigma vLow vHigh v : ℝ}
    (cutoff : Fin n -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hregion_mass : 1 - delta ≤ valueLaw.real region)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vLow ≤ w)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hv_high : v ≤ vHigh)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hn_pos : 0 < (n : ℝ))
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / (n : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow) ≤ 1)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
      1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff := by
  have hgap :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
        theorem2_twoScaleProductGap endpoint sigma :=
    theorem2_twoScale_iidLargeEndpointGap_of_failureRatio
      noiseLaw large cutoff hendpoint_nonneg hsigma_nonneg hn_pos
      hfailure_ratio hlow_failure_pos hlow_failure_le_one
  exact theorem2_twoScale_residual_of_sourceModel_globalClearing_and_endpoint_gap
    studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff
    hregion_meas hregion_mass hregion_ge hdelta_pos htotalSupply_nonneg
    htotalSupply_delta_lt_one hv_high hgap demand
    hdemand_none_iff_no_crossed aggregateDemand capacity hchoice_mass hclearing
    htotal_capacity

end

end PG24NoisyMatchingMarkets
