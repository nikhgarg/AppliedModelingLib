import PG24NoisyMatchingMarkets.Theorem2TwoScaleSourcePackage
import PG24NoisyMatchingMarkets.Theorem1SourceModelMassBridge

/-!
# PG24 Theorem 2 two-scale primitive bridge

This file keeps the repaired small-firm argument below the paper-facing
theorem surface.  It derives the interval-to-event-to-capacity chain from
ordinary measure, choice, and clearing semantics with `delta` reserved for
the split and `endpoint` reserved for the long-tail comparison.
-/

open Filter MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The residual unmatched-mass factor in the repaired small-firm argument. -/
def theorem2_twoScaleDenominator
    (totalSupply delta endpoint sigma : ℝ) : ℝ :=
  1 - totalSupply - delta - theorem2_twoScaleProductGap endpoint sigma

/--
The measure-theoretic interval step in `proof-amplifying.tex:220-250`, with
the endpoint comparison error independent of the split fraction.
-/
theorem theorem2_twoScale_smallFirm_matchedMass_lower_bound_of_interval_integral
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    {region : Set ℝ} {delta endpoint sigma totalSupply matchedMass : ℝ}
    {pSmall : ℝ -> ℝ} {vStar : ℝ}
    (hregion_meas : MeasurableSet region)
    (hintegrable : Integrable
      (fun w : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w)
      eta)
    (hmass : Real.sqrt delta ≤ eta.real region)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hp_star_nonneg : 0 ≤ pSmall vStar)
    (hp_mono : Monotone pSmall)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vStar ≤ w)
    (hnonneg_compl : ∀ w : ℝ, w ∉ region →
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w)
    (hintegral_le_matched :
      (∫ w : ℝ,
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w
        ∂eta) ≤ matchedMass) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall vStar ≤ matchedMass := by
  simpa using
    (theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
      eta hregion_meas hintegrable hmass hdenom_nonneg hp_star_nonneg hp_mono
      hregion_ge hnonneg_compl hintegral_le_matched)

/--
An event contained in choices of an active block has mass at most that block's
capacity when singleton choice masses identify aggregate demand and the
cutoff clears the market.  These are primitive market semantics, not an
endpoint estimate.
-/
theorem theorem2_eventMass_le_activeCapacity_of_choice_and_clearing
    {Omega College : Type*} [MeasurableSpace Omega]
    (outcomeLaw : Measure Omega) [IsFiniteMeasure outcomeLaw]
    (choice : Omega -> Option College) (event : Omega -> Prop)
    (active : Finset College) (aggregateDemand capacity : College -> ℝ)
    (hevent_chosen : ∀ omega, event omega -> chosenInActive choice active omega)
    (hchoice_mass :
      choiceMass outcomeLaw choice active = ∑ c ∈ active, aggregateDemand c)
    (hclearing : ∀ c ∈ active, aggregateDemand c = capacity c) :
    eventMass outcomeLaw event ≤ activeCapacity active capacity := by
  calc
    eventMass outcomeLaw event ≤ choiceMass outcomeLaw choice active :=
      eventMass_le_choiceMass_of_imp outcomeLaw hevent_chosen
    _ = ∑ c ∈ active, aggregateDemand c := hchoice_mass
    _ = ∑ c ∈ active, capacity c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact hclearing c hc
    _ = activeCapacity active capacity := by rfl

/--
Combining the interval integral with the actual chosen-small-block event and
exact clearing produces the repaired off-diagonal capacity lower bound.
-/
theorem theorem2_twoScale_smallFirm_capacity_lower_bound_of_interval_choice_semantics
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    {region : Set ℝ} {delta endpoint sigma totalSupply : ℝ}
    {pSmall : ℝ -> ℝ} {vStar : ℝ}
    {Omega College : Type*} [MeasurableSpace Omega]
    (outcomeLaw : Measure Omega) [IsFiniteMeasure outcomeLaw]
    (choice : Omega -> Option College) (smallMatchedEvent : Omega -> Prop)
    (active : Finset College) (aggregateDemand capacity : College -> ℝ)
    (hregion_meas : MeasurableSet region)
    (hintegrable : Integrable
      (fun w : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w)
      eta)
    (hmass : Real.sqrt delta ≤ eta.real region)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hp_star_nonneg : 0 ≤ pSmall vStar)
    (hp_mono : Monotone pSmall)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vStar ≤ w)
    (hnonneg_compl : ∀ w : ℝ, w ∉ region →
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w)
    (hintegral_le_event :
      (∫ w : ℝ,
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall w
        ∂eta) ≤ eventMass outcomeLaw smallMatchedEvent)
    (hevent_chosen : ∀ omega, smallMatchedEvent omega ->
      chosenInActive choice active omega)
    (hchoice_mass :
      choiceMass outcomeLaw choice active = ∑ c ∈ active, aggregateDemand c)
    (hclearing : ∀ c ∈ active, aggregateDemand c = capacity c) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall vStar ≤ activeCapacity active capacity := by
  calc
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall vStar ≤ eventMass outcomeLaw smallMatchedEvent :=
      theorem2_twoScale_smallFirm_matchedMass_lower_bound_of_interval_integral
        eta hregion_meas hintegrable hmass hdenom_nonneg hp_star_nonneg hp_mono
        hregion_ge hnonneg_compl hintegral_le_event
    _ ≤ activeCapacity active capacity :=
      theorem2_eventMass_le_activeCapacity_of_choice_and_clearing
        outcomeLaw choice smallMatchedEvent active aggregateDemand capacity
        hevent_chosen hchoice_mass hclearing

/--
The regular-capacity calculation preserves the two-scale denominator exactly:
only the split fraction controls the small active block's capacity.
-/
theorem theorem2_twoScale_capacity_mass_le_delta_mul_alpha
    {College : Type*} (active : Finset College) (capacity : College -> ℝ)
    {delta endpoint sigma totalSupply alpha p : ℝ} {C : ℕ}
    (hcard : (active.card : ℝ) ≤ delta * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ))
    (hlower :
      Real.sqrt delta *
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma * p ≤
        activeCapacity active capacity) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma * p ≤
      delta * alpha := by
  exact le_trans hlower
    (smallActiveSet_capacity_le_epsilon_mul_alpha
      active capacity hcard halpha_nonneg hC_pos hcap)

/--
Dividing the repaired capacity inequality yields the off-diagonal small-firm
probability bound.  This is pure scalar algebra once the interval/event and
capacity semantics have been established.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_of_capacity_mass
    {totalSupply alpha delta endpoint sigma p : ℝ}
    (hdelta_pos : 0 < delta)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hcapacity_mass :
      Real.sqrt delta *
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma * p ≤
        delta * alpha) :
    theorem2_twoScaleSmallFirmSourceBound
      totalSupply alpha delta endpoint sigma p := by
  have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta_pos
  have hmul_pos :
      0 < Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma :=
    mul_pos hsqrt_pos hden_pos
  have hdiv :
      p ≤ (delta * alpha) /
        (Real.sqrt delta *
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma) := by
    rw [le_div_iff₀ hmul_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcapacity_mass
  have hrewrite :
      (delta * alpha) /
          (Real.sqrt delta *
            theorem2_twoScaleDenominator totalSupply delta endpoint sigma) =
        alpha * Real.sqrt delta /
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma := by
    field_simp [ne_of_gt hsqrt_pos, ne_of_gt hden_pos]
    rw [Real.sq_sqrt hdelta_pos.le]
    ring
  simpa [theorem2_twoScaleSmallFirmSourceBound, hrewrite] using hdiv

/--
Fubini in the form needed to construct a local matched event from primitive
value/noise semantics.  The event is an actual subset of the product outcome
space; its section probabilities are not supplied as a theorem-shaped
amplification conclusion.
-/
theorem theorem2_eventMass_eq_integral_section_probability
    {Noise : Type*} [MeasurableSpace Noise]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure Noise) [IsProbabilityMeasure noiseLaw]
    (event : ℝ × Noise -> Prop)
    (hevent : MeasurableSet {outcome : ℝ × Noise | event outcome})
    (hsection : ∀ value : ℝ,
      MeasurableSet {noise : Noise | event (value, noise)}) :
    eventMass (valueLaw.prod noiseLaw) event =
      ∫ value : ℝ,
        noiseLaw.real {noise : Noise | event (value, noise)} ∂valueLaw := by
  let eventSet : Set (ℝ × Noise) := {outcome | event outcome}
  have hintegrable :
      Integrable
        (eventSet.indicator (fun _ : ℝ × Noise => (1 : ℝ)))
        (valueLaw.prod noiseLaw) :=
    (integrable_const _).indicator hevent
  have hfubini := integral_prod
    (f := eventSet.indicator (fun _ : ℝ × Noise => (1 : ℝ))) hintegrable
  change (valueLaw.prod noiseLaw).real eventSet = _
  calc
    (valueLaw.prod noiseLaw).real eventSet =
        ∫ outcome : ℝ × Noise,
          eventSet.indicator (fun _ : ℝ × Noise => (1 : ℝ)) outcome
          ∂(valueLaw.prod noiseLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ value : ℝ,
        ∫ noise : Noise,
          eventSet.indicator (fun _ : ℝ × Noise => (1 : ℝ)) (value, noise)
          ∂noiseLaw ∂valueLaw := hfubini
    _ = ∫ value : ℝ,
        noiseLaw.real {noise : Noise | event (value, noise)} ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with value
      let sectionSet : Set Noise := {noise | event (value, noise)}
      have hsection_meas : MeasurableSet sectionSet := hsection value
      have hsection_eq :
          (fun noise : Noise =>
            eventSet.indicator (fun _ : ℝ × Noise => (1 : ℝ)) (value, noise)) =
            sectionSet.indicator (fun _ : Noise => (1 : ℝ)) := by
        funext noise
        by_cases hmem : event (value, noise)
        · have hevent_mem : (value, noise) ∈ eventSet := hmem
          have hsection_mem : noise ∈ sectionSet := hmem
          rw [Set.indicator_of_mem hevent_mem, Set.indicator_of_mem hsection_mem]
        · have hevent_not_mem : (value, noise) ∉ eventSet := hmem
          have hsection_not_mem : noise ∉ sectionSet := hmem
          rw [Set.indicator_of_notMem hevent_not_mem,
            Set.indicator_of_notMem hsection_not_mem]
      rw [hsection_eq]
      simpa [sectionSet] using
        (integral_indicator_one (μ := noiseLaw) hsection_meas)

/--
Once a concrete product-space event has been constructed, pointwise lower
bounds on its noise-section probabilities lift to the exact off-diagonal
integral-to-event inequality.  The only analytic side condition is ordinary
integrability of the measurable section-probability kernel.
-/
theorem theorem2_twoScale_integral_le_eventMass_of_pointwise_section_bound
    {Noise : Type*} [MeasurableSpace Noise]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure Noise) [IsProbabilityMeasure noiseLaw]
    {delta endpoint sigma totalSupply : ℝ} {pSmall : ℝ -> ℝ}
    (event : ℝ × Noise -> Prop)
    (hevent : MeasurableSet {outcome : ℝ × Noise | event outcome})
    (hsection : ∀ value : ℝ,
      MeasurableSet {noise : Noise | event (value, noise)})
    (hkernel_integrable : Integrable
      (fun value : ℝ => noiseLaw.real {noise : Noise | event (value, noise)})
      valueLaw)
    (hintegrable : Integrable
      (fun value : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall value) valueLaw)
    (hpointwise : ∀ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall value ≤
        noiseLaw.real {noise : Noise | event (value, noise)}) :
    (∫ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        pSmall value ∂valueLaw) ≤
      eventMass (valueLaw.prod noiseLaw) event := by
  have hintegral :
      (∫ value : ℝ,
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall value ∂valueLaw) ≤
        ∫ value : ℝ,
          noiseLaw.real {noise : Noise | event (value, noise)} ∂valueLaw := by
    exact integral_mono hintegrable hkernel_integrable hpointwise
  calc
    (∫ value : ℝ,
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        pSmall value ∂valueLaw) ≤
        ∫ value : ℝ,
          noiseLaw.real {noise : Noise | event (value, noise)} ∂valueLaw :=
      hintegral
    _ = eventMass (valueLaw.prod noiseLaw) event :=
      (theorem2_eventMass_eq_integral_section_probability
        valueLaw noiseLaw event hevent hsection).symm

end

end PG24NoisyMatchingMarkets
