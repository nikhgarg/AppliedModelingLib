import PG24NoisyMatchingMarkets.Theorem2TwoScaleLargeBlockBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# PG24 Theorem 2 two-scale regional small-block bridge

The paper's large-block residual estimate is established only on the value
window used for the small-block argument.  This module keeps that domain
restriction explicit throughout the event, Fubini, and capacity steps.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/-- The small-only event restricted to the value region used in the proof. -/
def theorem2StudentTypeSmallOnlyInRegionEvent
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (region : Set ℝ)
    (small large : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    StudentType × (Fin n -> ℝ) -> Prop :=
  fun outcome =>
    value outcome.1 ∈ region ∧
      theorem2StudentTypeSmallOnlyEvent value small large cutoff outcome

/-- The regional small-only source event is measurable. -/
theorem theorem2StudentTypeSmallOnlyInRegionEvent_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    {region : Set ℝ} (hregion : MeasurableSet region)
    (small large : Finset (Fin n)) (cutoff : Fin n -> ℝ) :
    MeasurableSet
      {outcome : StudentType × (Fin n -> ℝ) |
        theorem2StudentTypeSmallOnlyInRegionEvent
          value region small large cutoff outcome} := by
  have hvalue_region :
      MeasurableSet
        {outcome : StudentType × (Fin n -> ℝ) | value outcome.1 ∈ region} := by
    change MeasurableSet
      ((fun outcome : StudentType × (Fin n -> ℝ) => value outcome.1) ⁻¹' region)
    exact hregion.preimage (hvalue.comp measurable_fst)
  change MeasurableSet
    ({outcome : StudentType × (Fin n -> ℝ) | value outcome.1 ∈ region} ∩
      {outcome : StudentType × (Fin n -> ℝ) |
        theorem2StudentTypeSmallOnlyEvent value small large cutoff outcome})
  exact hvalue_region.inter
    (theorem2StudentTypeSmallOnlyEvent_measurable value hvalue small large cutoff)

/--
Fubini for the regional small-only event.  The right side is explicitly
restricted by `region`; this is the domain on which the source proves the
large-block residual estimate.
-/
theorem theorem2_sourceModel_smallOnlyInRegion_eventMass_eq_integral
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {region : Set ℝ} (hregion : MeasurableSet region)
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    (cutoff : Fin n -> ℝ) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeSmallOnlyInRegionEvent
          value region small large cutoff) =
      ∫ v : ℝ,
        region.indicator
          (fun w : ℝ =>
            (Measure.pi (fun _ : Fin n => noiseLaw)).real
              {noise : Fin n -> ℝ |
                theorem2SmallOnlyAffordanceEvent small large w cutoff noise}) v
        ∂valueLaw := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let event : Set (StudentType × (Fin n -> ℝ)) :=
    {outcome |
      theorem2StudentTypeSmallOnlyInRegionEvent
        value region small large cutoff outcome}
  have hevent : MeasurableSet event := by
    simpa [event] using
      (theorem2StudentTypeSmallOnlyInRegionEvent_measurable
        value hvalue hregion small large cutoff)
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
        (studentLaw.prod productLaw) :=
    (integrable_const _).indicator hevent
  have hfubini := integral_prod
    (f := event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)))
    hintegrable
  let kernel : ℝ -> ℝ :=
    fun w => productLaw.real
      {noise : Fin n -> ℝ |
        theorem2SmallOnlyAffordanceEvent small large w cutoff noise}
  have hkernel_integrable : Integrable kernel valueLaw := by
    simpa [kernel, productLaw] using
      (theorem2_iid_smallOnly_probability_integrable
        valueLaw noiseLaw small large hdisjoint cutoff)
  have hregion_kernel_integrable :
      Integrable (region.indicator kernel) valueLaw :=
    hkernel_integrable.indicator hregion
  have hproduct_integral :
      (∫ outcome : StudentType × (Fin n -> ℝ),
        event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
        ∂(studentLaw.prod productLaw)) =
        ∫ student : StudentType,
          region.indicator kernel (value student) ∂studentLaw := by
    rw [hfubini]
    apply integral_congr_ae
    filter_upwards with student
    by_cases hstudent : value student ∈ region
    · rw [Set.indicator_of_mem hstudent]
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
            change value student ∈ region ∧
              theorem2SmallOnlyAffordanceEvent
                small large (value student) cutoff noise
            exact ⟨hstudent, hmem⟩
          rw [Set.indicator_of_mem hevent_mem, Set.indicator_of_mem hmem]
        · have hevent_not_mem : (student, noise) ∉ event := by
            intro hevent_mem
            apply hmem
            exact hevent_mem.2
          rw [Set.indicator_of_notMem hevent_not_mem,
            Set.indicator_of_notMem hmem]
      rw [hsection_eq]
      calc
        ∫ noise : Fin n -> ℝ,
            sectionSet.indicator (fun _ : Fin n -> ℝ => (1 : ℝ)) noise
            ∂productLaw = productLaw.real sectionSet := by
          simpa using (integral_indicator_one (μ := productLaw) hsection)
        _ = kernel (value student) := by
          rfl
    · rw [Set.indicator_of_notMem hstudent]
      have hsection_eq :
          (fun noise : Fin n -> ℝ =>
            event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ))
              (student, noise)) =
            fun _ : Fin n -> ℝ => (0 : ℝ) := by
        funext noise
        have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          exact hstudent hevent_mem.1
        rw [Set.indicator_of_notMem hevent_not_mem]
      rw [hsection_eq]
      simp
  have hmap_integral :
      (∫ student : StudentType,
        region.indicator kernel (value student) ∂studentLaw) =
        ∫ w : ℝ, region.indicator kernel w ∂valueLaw := by
    calc
      (∫ student : StudentType,
        region.indicator kernel (value student) ∂studentLaw) =
          ∫ w : ℝ, region.indicator kernel w ∂Measure.map value studentLaw := by
        symm
        exact integral_map hvalue.aemeasurable (by
          rw [hvalue_marginal]
          exact hregion_kernel_integrable.aestronglyMeasurable)
      _ = ∫ w : ℝ, region.indicator kernel w ∂valueLaw := by
        rw [hvalue_marginal]
  change (studentLaw.prod productLaw).real event = _
  calc
    (studentLaw.prod productLaw).real event =
        ∫ outcome : StudentType × (Fin n -> ℝ),
          event.indicator (fun _ : StudentType × (Fin n -> ℝ) => (1 : ℝ)) outcome
          ∂(studentLaw.prod productLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ student : StudentType,
        region.indicator kernel (value student) ∂studentLaw :=
      hproduct_integral
    _ = ∫ w : ℝ, region.indicator kernel w ∂valueLaw := hmap_integral
    _ = ∫ w : ℝ,
        region.indicator
          (fun x : ℝ =>
            (Measure.pi (fun _ : Fin n => noiseLaw)).real
              {noise : Fin n -> ℝ |
                theorem2SmallOnlyAffordanceEvent small large x cutoff noise}) w
        ∂valueLaw := by
      rfl

/--
The off-diagonal small-only probability estimate lifts on precisely the
regional domain where the large-block residual is available.
-/
theorem theorem2_twoScale_restricted_integral_le_sourceModel_smallOnly_eventMass
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {region : Set ℝ} (hregion : MeasurableSet region)
    (small large : Finset (Fin n)) (hdisjoint : Disjoint small large)
    {totalSupply delta endpoint sigma : ℝ} (cutoff : Fin n -> ℝ)
    (hresidual : ∀ w : ℝ, w ∈ region ->
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large w cutoff) :
    (∫ w : ℝ,
      region.indicator
        (fun x : ℝ =>
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw)) small x cutoff) w
      ∂valueLaw) ≤
      eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (theorem2StudentTypeSmallOnlyInRegionEvent
          value region small large cutoff) := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pSmall : ℝ -> ℝ :=
    fun x => cutoffAffordanceProbability productLaw small x cutoff
  let kernel : ℝ -> ℝ :=
    fun x => productLaw.real
      {noise : Fin n -> ℝ |
        theorem2SmallOnlyAffordanceEvent small large x cutoff noise}
  have hpSmall_integrable : Integrable pSmall valueLaw := by
    simpa [pSmall, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw valueLaw small cutoff)
  have hleft_integrable : Integrable
      (region.indicator (fun x : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall x)) valueLaw := by
    exact
      (hpSmall_integrable.const_mul
        (theorem2_twoScaleDenominator totalSupply delta endpoint sigma)).indicator
        hregion
  have hkernel_integrable : Integrable kernel valueLaw := by
    simpa [kernel, productLaw] using
      (theorem2_iid_smallOnly_probability_integrable
        valueLaw noiseLaw small large hdisjoint cutoff)
  have hright_integrable : Integrable (region.indicator kernel) valueLaw :=
    hkernel_integrable.indicator hregion
  have hpointwise : ∀ w : ℝ,
      region.indicator (fun x : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall x) w ≤
        region.indicator kernel w := by
    intro w
    by_cases hw : w ∈ region
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      simpa [pSmall, kernel, productLaw] using
        (theorem2_twoScale_smallOnly_probability_lower_bound
          noiseLaw small large hdisjoint cutoff (hresidual w hw))
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  have hintegral :
      (∫ w : ℝ,
        region.indicator (fun x : ℝ =>
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
            pSmall x) w ∂valueLaw) ≤
        ∫ w : ℝ, region.indicator kernel w ∂valueLaw :=
    integral_mono hleft_integrable hright_integrable hpointwise
  calc
    (∫ w : ℝ,
      region.indicator (fun x : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall x) w ∂valueLaw) ≤
        ∫ w : ℝ, region.indicator kernel w ∂valueLaw := hintegral
    _ = eventMass
        (studentLaw.prod productLaw)
        (theorem2StudentTypeSmallOnlyInRegionEvent
          value region small large cutoff) := by
      symm
      simpa [kernel, productLaw] using
        (theorem2_sourceModel_smallOnlyInRegion_eventMass_eq_integral
          studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
          hregion small large hdisjoint cutoff)

/--
The interval lower bound for the small block, with the integral explicitly
restricted to the source value region.  No residual estimate is needed off
that region.
-/
theorem theorem2_twoScale_restricted_smallFirm_interval_lower_bound
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {region : Set ℝ} {delta totalSupply endpoint sigma vStar : ℝ}
    {pSmall : ℝ -> ℝ}
    (hregion : MeasurableSet region)
    (hintegrable : Integrable
      (fun w : ℝ =>
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall w) valueLaw)
    (hmass : Real.sqrt delta ≤ valueLaw.real region)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hp_star_nonneg : 0 ≤ pSmall vStar)
    (hp_mono : Monotone pSmall)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vStar ≤ w) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall vStar ≤
      ∫ w : ℝ,
        region.indicator
          (fun x : ℝ =>
            theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
              pSmall x) w
        ∂valueLaw := by
  let lowerBound : ℝ :=
    theorem2_twoScaleDenominator totalSupply delta endpoint sigma * pSmall vStar
  let integrand : ℝ -> ℝ :=
    fun w => theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
      pSmall w
  have hindicator_integrable :
      Integrable (region.indicator integrand) valueLaw := by
    exact hintegrable.indicator hregion
  have hlow : ∀ w : ℝ, w ∈ region -> lowerBound ≤
      region.indicator integrand w := by
    intro w hw
    rw [Set.indicator_of_mem hw]
    dsimp [lowerBound, integrand]
    exact mul_le_mul_of_nonneg_left (hp_mono (hregion_ge w hw)) hdenom_nonneg
  have hnonneg_compl : ∀ w : ℝ, w ∉ region ->
      0 ≤ region.indicator integrand w := by
    intro w hw
    rw [Set.indicator_of_notMem hw]
  have hregion_integral :
      lowerBound * valueLaw.real region ≤
        ∫ w : ℝ, region.indicator integrand w ∂valueLaw := by
    exact AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
      valueLaw hregion hindicator_integrable hlow hnonneg_compl
  have hlower_nonneg : 0 ≤ lowerBound := by
    dsimp [lowerBound]
    exact mul_nonneg hdenom_nonneg hp_star_nonneg
  calc
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          pSmall vStar = lowerBound * Real.sqrt delta := by
      dsimp [lowerBound]
      ring
    _ ≤ lowerBound * valueLaw.real region :=
      mul_le_mul_of_nonneg_left hmass hlower_nonneg
    _ ≤ ∫ w : ℝ, region.indicator integrand w ∂valueLaw := hregion_integral
    _ = ∫ w : ℝ,
        region.indicator
          (fun x : ℝ =>
            theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
              pSmall x) w
        ∂valueLaw := by
      rfl

/-- The regional small-only event still forces a choice in the small block. -/
theorem theorem2_sourceDemand_chosenInSmall_of_smallOnlyInRegion
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (region : Set ℝ)
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
          cutoff college < value outcome.1 + outcome.2 college) :
    ∀ outcome : StudentType × (Fin n -> ℝ),
      theorem2StudentTypeSmallOnlyInRegionEvent
        value region small large cutoff outcome ->
        chosenInActive demand small outcome := by
  intro outcome hregion_smallOnly
  exact theorem2_sourceDemand_chosenInSmall_of_smallOnly
    value small large hcover cutoff demand hdemand_none_iff_no_crossed
    hchosen_feasible outcome hregion_smallOnly.2

/--
Complete regional small-block capacity bridge.  Its residual premise is
pointwise only on `region`, matching the source proof's value window.
-/
theorem theorem2_twoScale_sourceModel_regional_smallFirm_capacity_lower_bound
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {region : Set ℝ} (hregion : MeasurableSet region)
    {totalSupply delta endpoint sigma vStar : ℝ} (cutoff : Fin n -> ℝ)
    (hmass : Real.sqrt delta ≤ valueLaw.real region)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hregion_ge : ∀ w : ℝ, w ∈ region -> vStar ≤ w)
    (hresidual : ∀ w : ℝ, w ∈ region ->
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large w cutoff)
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
    fun w => cutoffAffordanceProbability productLaw small w cutoff
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
    intro x y hxy
    exact cutoffAffordanceProbability_mono_value productLaw hxy
  have hintegral_le_event :
      (∫ w : ℝ,
        region.indicator (fun x : ℝ =>
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
            pSmall x) w ∂valueLaw) ≤
        eventMass (studentLaw.prod productLaw)
          (theorem2StudentTypeSmallOnlyInRegionEvent
            value region small large cutoff) := by
    simpa [pSmall, productLaw] using
      (theorem2_twoScale_restricted_integral_le_sourceModel_smallOnly_eventMass
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw hregion
        small large hdisjoint cutoff hresidual)
  have hevent_le_capacity :
      eventMass (studentLaw.prod productLaw)
        (theorem2StudentTypeSmallOnlyInRegionEvent
          value region small large cutoff) ≤
        activeCapacity small capacity := by
    exact theorem2_eventMass_le_activeCapacity_of_choice_and_clearing
      (studentLaw.prod productLaw)
      demand
      (theorem2StudentTypeSmallOnlyInRegionEvent
        value region small large cutoff)
      small aggregateDemand capacity
      (theorem2_sourceDemand_chosenInSmall_of_smallOnlyInRegion
        value region small large hcover cutoff demand
        hdemand_none_iff_no_crossed hchosen_feasible)
      (by simpa [productLaw] using hchoice_mass)
      hclearing
  change Real.sqrt delta *
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
        pSmall vStar ≤ activeCapacity small capacity
  exact (theorem2_twoScale_restricted_smallFirm_interval_lower_bound
    valueLaw hregion hintegrable hmass hdenom_nonneg hp_star_nonneg hp_mono
    hregion_ge).trans
      (hintegral_le_event.trans hevent_le_capacity)

/--
The source-faithful two-scale small-firm capacity inequality.  The large-block
residual is derived from iid failure ratios and global clearing on the large
interval, then used only on the small interval contained below `vHigh`.
-/
theorem theorem2_twoScale_sourceModel_regional_smallFirm_capacity_lower_bound_of_global_largeResidual
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {largeRegion smallRegion : Set ℝ}
    {totalSupply delta endpoint sigma vLow vHigh vStar : ℝ}
    (cutoff : Fin n -> ℝ)
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ valueLaw.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ valueLaw.real smallRegion)
    (hsmallRegion_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hsmallRegion_le_high : ∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
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
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hglobal_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hsmall_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand small = ∑ c ∈ small, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply) :
    Real.sqrt delta *
        theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) small vStar cutoff ≤
      activeCapacity small capacity := by
  have hresidual : ∀ w : ℝ, w ∈ smallRegion ->
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large w cutoff := by
    intro w hw
    exact theorem2_twoScale_residual_of_sourceModel_globalClearing_and_failureRatio
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff
      hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hdelta_pos
      htotalSupply_nonneg htotalSupply_delta_lt_one
      (hsmallRegion_le_high w hw) hendpoint_nonneg hsigma_nonneg hn_pos
      hfailure_ratio hlow_failure_pos hlow_failure_le_one demand
      hdemand_none_iff_no_crossed aggregateDemand capacity hglobal_choice_mass
      hclearing htotal_capacity
  exact theorem2_twoScale_sourceModel_regional_smallFirm_capacity_lower_bound
    studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
    small large hdisjoint hcover hsmallRegion_meas cutoff hsmallRegion_mass
    hdenom_nonneg hsmallRegion_ge hresidual demand
    hdemand_none_iff_no_crossed hchosen_feasible aggregateDemand capacity
    hsmall_choice_mass (fun c _hc => hclearing c)

end

end PG24NoisyMatchingMarkets
