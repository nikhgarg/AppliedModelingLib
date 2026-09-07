import PG24NoisyMatchingMarkets.Theorem1SourceModelMassBridge
import PG24NoisyMatchingMarkets.Theorem1SourceProofHelpers
import Mathlib.MeasureTheory.Integral.Prod

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
Affordance in the source economy before student preferences choose among the
affordable colleges.  The student-type coordinate is intentionally arbitrary:
PG24 allows preferences to be correlated with value.
-/
def theorem1TypeNoiseAffordanceEvent
    {StudentType : Type u} {n : ℕ}
    (value : StudentType → ℝ)
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ) :
    StudentType × (Fin n → ℝ) → Prop :=
  fun outcome =>
    cutoffCrossedOn active
      (noisyScore (value outcome.1) outcome.2) cutoff

private theorem theorem1_type_noise_affordance_section_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType → ℝ)
    (active : Finset (Fin n)) (student : StudentType)
    (cutoff : Fin n → ℝ) :
    MeasurableSet
      {noise : Fin n → ℝ |
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff} := by
  classical
  let collegeEvent : Fin n → Set (Fin n → ℝ) :=
    fun c => {noise | cutoff c < value student + noise c}
  have hset :
      {noise : Fin n → ℝ |
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff} =
        ⋃ c ∈ active, collegeEvent c := by
    ext noise
    simp [collegeEvent, cutoffCrossedOn, noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore :
      Measurable (fun noise : Fin n → ℝ => value student + noise c) := by
    fun_prop
  change MeasurableSet
    {noise : Fin n → ℝ | cutoff c < value student + noise c}
  exact measurableSet_Ioi.preimage hscore

private theorem theorem1_type_noise_region_affordance_measurable
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    MeasurableSet
      {outcome : StudentType × (Fin n → ℝ) |
        value outcome.1 ∈ region ∧
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome} := by
  classical
  let collegeEvent : Fin n → Set (StudentType × (Fin n → ℝ)) :=
    fun c =>
      {outcome |
        value outcome.1 ∈ region ∧
          cutoff c < value outcome.1 + outcome.2 c}
  have hset :
      {outcome : StudentType × (Fin n → ℝ) |
        value outcome.1 ∈ region ∧
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome} =
        ⋃ c ∈ active, collegeEvent c := by
    ext outcome
    simp [collegeEvent, theorem1TypeNoiseAffordanceEvent, cutoffCrossedOn,
      noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hvalue_first :
      Measurable (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1) :=
    hvalue.comp measurable_fst
  have hnoise_c :
      Measurable (fun outcome : StudentType × (Fin n → ℝ) => outcome.2 c) := by
    fun_prop
  have hscore :
      Measurable (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 + outcome.2 c) :=
    hvalue_first.add hnoise_c
  have hvalue_region :
      MeasurableSet
        {outcome : StudentType × (Fin n → ℝ) | value outcome.1 ∈ region} := by
    change MeasurableSet
      ((fun outcome : StudentType × (Fin n → ℝ) => value outcome.1) ⁻¹' region)
    exact hregion.preimage hvalue_first
  change MeasurableSet
    ({outcome : StudentType × (Fin n → ℝ) | value outcome.1 ∈ region} ∩
      {outcome : StudentType × (Fin n → ℝ) |
        cutoff c < value outcome.1 + outcome.2 c})
  exact hvalue_region.inter (measurableSet_Ioi.preimage hscore)

/--
The model-correct PG24 mass bridge.  Student preferences remain in the
arbitrary `StudentType` coordinate; only its measurable value projection has
the fixed marginal `valueLaw`.  Thus no independence between value and
preferences is assumed.
-/
theorem theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ region ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  let event : Set (StudentType × (Fin n → ℝ)) :=
    {outcome |
      value outcome.1 ∈ region ∧
        theorem1TypeNoiseAffordanceEvent value active cutoff outcome}
  have hevent : MeasurableSet event :=
    theorem1_type_noise_region_affordance_measurable
      value hvalue active cutoff hregion
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)))
        (studentLaw.prod noiseLaw) :=
    (integrable_const _).indicator hevent
  have hfubini :=
    integral_prod
      (f := event.indicator
        (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)))
      hintegrable
  have hproduct_integral :
      (∫ outcome : StudentType × (Fin n → ℝ),
        event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) outcome
        ∂(studentLaw.prod noiseLaw)) =
        ∫ student : StudentType,
          region.indicator
            (fun v => cutoffAffordanceProbability noiseLaw active v cutoff)
            (value student) ∂studentLaw := by
    rw [hfubini]
    apply integral_congr_ae
    filter_upwards with student
    let crossing : Set (Fin n → ℝ) :=
      {noise |
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff}
    have hcrossing : MeasurableSet crossing :=
      theorem1_type_noise_affordance_section_measurable
        value active student cutoff
    by_cases hstudent : value student ∈ region
    · rw [Set.indicator_of_mem hstudent]
      have hsection :
          (fun noise : Fin n → ℝ =>
            event.indicator
              (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) (student, noise)) =
            crossing.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) := by
        funext noise
        by_cases hcrossing_mem : noise ∈ crossing
        · have hevent_mem : (student, noise) ∈ event := by
            change value student ∈ region ∧
              theorem1TypeNoiseAffordanceEvent value active cutoff
                (student, noise)
            exact ⟨hstudent, hcrossing_mem⟩
          have hcrossing_mem' : noise ∈ crossing := hcrossing_mem
          rw [Set.indicator_of_mem hevent_mem,
            Set.indicator_of_mem hcrossing_mem']
        · have hevent_not_mem : (student, noise) ∉ event := by
            intro hevent_mem
            apply hcrossing_mem
            exact hevent_mem.2
          have hcrossing_not_mem : noise ∉ crossing := hcrossing_mem
          rw [Set.indicator_of_notMem hevent_not_mem,
            Set.indicator_of_notMem hcrossing_not_mem]
      rw [hsection]
      calc
        ∫ noise : Fin n → ℝ,
            crossing.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) noise
            ∂noiseLaw = noiseLaw.real crossing := by
          simpa using (integral_indicator_one (μ := noiseLaw) hcrossing)
        _ = cutoffAffordanceProbability noiseLaw active (value student) cutoff := by
          rfl
    · rw [Set.indicator_of_notMem hstudent]
      have hsection :
          (fun noise : Fin n → ℝ =>
            event.indicator
              (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) (student, noise)) =
            fun _ : Fin n → ℝ => (0 : ℝ) := by
        funext noise
        have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          exact hstudent hevent_mem.1
        rw [Set.indicator_of_notMem hevent_not_mem]
      rw [hsection]
      simp
  let affordance : ℝ → ℝ :=
    fun v => cutoffAffordanceProbability noiseLaw active v cutoff
  have haffordance_integrable : Integrable affordance valueLaw := by
    simpa [affordance, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw active cutoff)
  have hregion_integrable :
      Integrable (region.indicator affordance) valueLaw :=
    haffordance_integrable.indicator hregion
  have hmap_integral :
      (∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw) =
        ∫ v : ℝ, region.indicator affordance v ∂valueLaw := by
    calc
      (∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw) =
          ∫ v : ℝ, region.indicator affordance v ∂Measure.map value studentLaw := by
        symm
        exact integral_map hvalue.aemeasurable (by
          rw [hvalue_marginal]
          exact hregion_integrable.aestronglyMeasurable)
      _ = ∫ v : ℝ, region.indicator affordance v ∂valueLaw := by
        rw [hvalue_marginal]
  have hchoice_event :
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ region ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ region ∧
            theorem1TypeNoiseAffordanceEvent value active cutoff outcome) := by
    funext outcome
    apply propext
    constructor
    · intro h
      exact ⟨h.1, (hmatch_iff_affordance outcome).mp h.2⟩
    · intro h
      exact ⟨h.1, (hmatch_iff_affordance outcome).mpr h.2⟩
  rw [hchoice_event]
  change (studentLaw.prod noiseLaw).real event = _
  calc
    (studentLaw.prod noiseLaw).real event =
        ∫ outcome : StudentType × (Fin n → ℝ),
          event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) outcome
          ∂(studentLaw.prod noiseLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ student : StudentType,
        region.indicator affordance (value student) ∂studentLaw := by
      simpa [affordance] using hproduct_integral
    _ = ∫ v : ℝ, region.indicator affordance v ∂valueLaw := hmap_integral
    _ = ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability noiseLaw active v cutoff) v
          ∂valueLaw := by
      rfl

/--
The model-correct unmatched counterpart.  Preferences remain arbitrary and
possibly value-dependent; only the pointwise fact that unmatched means no
affordable college is used.
-/
theorem theorem1_source_model_value_restricted_unmatched_mass_eq_integral_affordance_complement
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ region ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v => 1 - cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  let event : Set (StudentType × (Fin n → ℝ)) :=
    {outcome |
      value outcome.1 ∈ region ∧
        ¬ theorem1TypeNoiseAffordanceEvent value active cutoff outcome}
  have hvalue_region :
      MeasurableSet
        {outcome : StudentType × (Fin n → ℝ) | value outcome.1 ∈ region} := by
    change MeasurableSet
      ((fun outcome : StudentType × (Fin n → ℝ) => value outcome.1) ⁻¹' region)
    exact hregion.preimage (hvalue.comp measurable_fst)
  have hcross :
      MeasurableSet
        {outcome : StudentType × (Fin n → ℝ) |
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome} := by
    simpa [theorem1TypeNoiseAffordanceEvent] using
      (theorem1_type_noise_region_affordance_measurable
        value hvalue active cutoff (region := Set.univ) MeasurableSet.univ)
  have hevent : MeasurableSet event := by
    change MeasurableSet
      ({outcome : StudentType × (Fin n → ℝ) | value outcome.1 ∈ region} ∩
        {outcome : StudentType × (Fin n → ℝ) |
          theorem1TypeNoiseAffordanceEvent value active cutoff outcome}ᶜ)
    exact hvalue_region.inter hcross.compl
  have hintegrable :
      Integrable
        (event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)))
        (studentLaw.prod noiseLaw) :=
    (integrable_const _).indicator hevent
  have hfubini :=
    integral_prod
      (f := event.indicator
        (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)))
      hintegrable
  have hproduct_integral :
      (∫ outcome : StudentType × (Fin n → ℝ),
        event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) outcome
        ∂(studentLaw.prod noiseLaw)) =
        ∫ student : StudentType,
          region.indicator
            (fun v => 1 - cutoffAffordanceProbability noiseLaw active v cutoff)
            (value student) ∂studentLaw := by
    rw [hfubini]
    apply integral_congr_ae
    filter_upwards with student
    let crossing : Set (Fin n → ℝ) :=
      {noise |
        cutoffCrossedOn active (noisyScore (value student) noise) cutoff}
    have hcrossing : MeasurableSet crossing :=
      theorem1_type_noise_affordance_section_measurable
        value active student cutoff
    by_cases hstudent : value student ∈ region
    · rw [Set.indicator_of_mem hstudent]
      have hsection :
          (fun noise : Fin n → ℝ =>
            event.indicator
              (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) (student, noise)) =
            crossingᶜ.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) := by
        funext noise
        by_cases hcrossing_mem : noise ∈ crossing
        · have hevent_not_mem : (student, noise) ∉ event := by
            intro hevent_mem
            apply hevent_mem.2
            exact hcrossing_mem
          have hcrossing_compl_not_mem : noise ∉ crossingᶜ := by
            intro hcrossing_compl_mem
            exact hcrossing_compl_mem hcrossing_mem
          rw [Set.indicator_of_notMem hevent_not_mem,
            Set.indicator_of_notMem hcrossing_compl_not_mem]
        · have hevent_mem : (student, noise) ∈ event := by
            change value student ∈ region ∧
              ¬ theorem1TypeNoiseAffordanceEvent value active cutoff
                (student, noise)
            constructor
            · exact hstudent
            · exact hcrossing_mem
          have hcrossing_compl_mem : noise ∈ crossingᶜ := hcrossing_mem
          rw [Set.indicator_of_mem hevent_mem,
            Set.indicator_of_mem hcrossing_compl_mem]
      rw [hsection]
      calc
        ∫ noise : Fin n → ℝ,
            crossingᶜ.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) noise
            ∂noiseLaw = noiseLaw.real crossingᶜ := by
          simpa using
            (integral_indicator_one (μ := noiseLaw) hcrossing.compl)
        _ = noiseLaw.real Set.univ - noiseLaw.real crossing :=
          measureReal_compl hcrossing
        _ = 1 - cutoffAffordanceProbability noiseLaw active (value student) cutoff := by
          rw [probReal_univ]
          rfl
    · rw [Set.indicator_of_notMem hstudent]
      have hsection :
          (fun noise : Fin n → ℝ =>
            event.indicator
              (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) (student, noise)) =
            fun _ : Fin n → ℝ => (0 : ℝ) := by
        funext noise
        have hevent_not_mem : (student, noise) ∉ event := by
          intro hevent_mem
          exact hstudent hevent_mem.1
        rw [Set.indicator_of_notMem hevent_not_mem]
      rw [hsection]
      simp
  let unaffordance : ℝ → ℝ :=
    fun v => 1 - cutoffAffordanceProbability noiseLaw active v cutoff
  have haffordance_integrable :
      Integrable
        (fun v => cutoffAffordanceProbability noiseLaw active v cutoff)
        valueLaw := by
    simpa [cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw active cutoff)
  have hunaffordance_integrable : Integrable unaffordance valueLaw := by
    exact (integrable_const _).sub haffordance_integrable
  have hregion_integrable :
      Integrable (region.indicator unaffordance) valueLaw :=
    hunaffordance_integrable.indicator hregion
  have hmap_integral :
      (∫ student : StudentType,
        region.indicator unaffordance (value student) ∂studentLaw) =
        ∫ v : ℝ, region.indicator unaffordance v ∂valueLaw := by
    calc
      (∫ student : StudentType,
        region.indicator unaffordance (value student) ∂studentLaw) =
          ∫ v : ℝ, region.indicator unaffordance v
            ∂Measure.map value studentLaw := by
        symm
        exact integral_map hvalue.aemeasurable (by
          rw [hvalue_marginal]
          exact hregion_integrable.aestronglyMeasurable)
      _ = ∫ v : ℝ, region.indicator unaffordance v ∂valueLaw := by
        rw [hvalue_marginal]
  have hchoice_event :
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ region ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ region ∧
            ¬ theorem1TypeNoiseAffordanceEvent value active cutoff outcome) := by
    funext outcome
    apply propext
    constructor
    · rintro ⟨hregion_mem, hnot_matched⟩
      refine ⟨hregion_mem, ?_⟩
      intro haffordable
      exact hnot_matched ((hmatch_iff_affordance outcome).mpr haffordable)
    · rintro ⟨hregion_mem, hnot_affordable⟩
      refine ⟨hregion_mem, ?_⟩
      intro hmatched
      exact hnot_affordable ((hmatch_iff_affordance outcome).mp hmatched)
  rw [hchoice_event]
  change (studentLaw.prod noiseLaw).real event = _
  calc
    (studentLaw.prod noiseLaw).real event =
        ∫ outcome : StudentType × (Fin n → ℝ),
          event.indicator (fun _ : StudentType × (Fin n → ℝ) => (1 : ℝ)) outcome
          ∂(studentLaw.prod noiseLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ student : StudentType,
        region.indicator unaffordance (value student) ∂studentLaw := by
      simpa [unaffordance] using hproduct_integral
    _ = ∫ v : ℝ, region.indicator unaffordance v ∂valueLaw := hmap_integral
    _ = ∫ v : ℝ,
        region.indicator
          (fun v => 1 - cutoffAffordanceProbability noiseLaw active v cutoff) v
          ∂valueLaw := by
      rfl

/--
At a source-model clearing cutoff, the integral of the whole-market
affordance probability is total capacity.  The preference/type coordinate is
never collapsed: the aggregate-demand premise is measured over the full
student law.
-/
theorem theorem1_source_model_whole_market_matched_mass_eq_total_capacity
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value
            (Finset.univ : Finset (Fin n)) cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (studentLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c) :
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw (Finset.univ : Finset (Fin n)) v
        cutoff ∂valueLaw) =
      ∑ c : Fin n, M.capacity c := by
  have hmatched :=
    theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      (Finset.univ : Finset (Fin n)) cutoff choice hmatch_iff_affordance
      (region := Set.univ) MeasurableSet.univ
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw (Finset.univ : Finset (Fin n)) v
        cutoff ∂valueLaw) =
        choiceMass (studentLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) := by
      simpa [choiceMass] using hmatched.symm
    _ = ∑ c : Fin n, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregate_demand
    _ = ∑ c : Fin n, M.capacity c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact K.aggregateDemand_eq_capacity hclearing c

/--
The whole-market source capacity bound applied to an arbitrary measurable
value region.  This is the exact mass inequality used when the paper says a
set of students cannot collectively match more often than total capacity.
-/
theorem theorem1_source_model_value_restricted_affordance_integral_le_total_capacity
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value
            (Finset.univ : Finset (Fin n)) cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (studentLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    (∫ v : ℝ,
      region.indicator
        (fun v => cutoffAffordanceProbability noiseLaw
          (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) ≤
      ∑ c : Fin n, M.capacity c := by
  have htail :=
    theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      (Finset.univ : Finset (Fin n)) cutoff choice hmatch_iff_affordance
      hregion
  calc
    (∫ v : ℝ,
      region.indicator
        (fun v => cutoffAffordanceProbability noiseLaw
          (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) =
        eventMass (studentLaw.prod noiseLaw)
          (fun outcome : StudentType × (Fin n → ℝ) =>
            value outcome.1 ∈ region ∧
              chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) :=
      htail.symm
    _ ≤ eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) :=
      eventMass_mono (studentLaw.prod noiseLaw) (fun _ h => h.2)
    _ = choiceMass (studentLaw.prod noiseLaw) choice
        (Finset.univ : Finset (Fin n)) := rfl
    _ = ∑ c : Fin n, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregate_demand
    _ = ∑ c : Fin n, M.capacity c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact K.aggregateDemand_eq_capacity hclearing c

/--
Population conservation for an arbitrary integrable match-probability
function.  The high set is literally the complement of the low set; this
keeps the threshold boundary explicit.
-/
theorem theorem1_integral_low_matched_eq_high_unmatched_of_total_mass
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (matchProbability : ℝ → ℝ)
    (hmatch_integrable : Integrable matchProbability valueLaw)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (htotal_mass :
      (∫ v : ℝ, matchProbability v ∂valueLaw) =
        valueLaw.real lowValuesᶜ) :
    (∫ v : ℝ, lowValues.indicator matchProbability v ∂valueLaw) =
      ∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - matchProbability v) v ∂valueLaw := by
  have hlow_integrable :
      Integrable (lowValues.indicator matchProbability) valueLaw :=
    hmatch_integrable.indicator hlowValues
  have hhigh_integrable :
      Integrable (lowValuesᶜ.indicator matchProbability) valueLaw :=
    hmatch_integrable.indicator hlowValues.compl
  have hhigh_one_integrable :
      Integrable (lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ))) valueLaw :=
    (integrable_const _).indicator hlowValues.compl
  have hpartition :
      (∫ v : ℝ, lowValues.indicator matchProbability v ∂valueLaw) +
        ∫ v : ℝ, lowValuesᶜ.indicator matchProbability v ∂valueLaw =
        ∫ v : ℝ, matchProbability v ∂valueLaw := by
    calc
      (∫ v : ℝ, lowValues.indicator matchProbability v ∂valueLaw) +
          ∫ v : ℝ, lowValuesᶜ.indicator matchProbability v ∂valueLaw =
          ∫ v : ℝ,
            lowValues.indicator matchProbability v +
              lowValuesᶜ.indicator matchProbability v ∂valueLaw := by
        rw [integral_add hlow_integrable hhigh_integrable]
      _ = ∫ v : ℝ, matchProbability v ∂valueLaw := by
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ lowValues
        · have hvcomp : v ∉ lowValuesᶜ := by
            intro hvcomp
            exact hvcomp hv
          rw [Set.indicator_of_mem hv, Set.indicator_of_notMem hvcomp]
          ring
        · have hvcomp : v ∈ lowValuesᶜ := hv
          rw [Set.indicator_of_notMem hv, Set.indicator_of_mem hvcomp]
          ring
  have hunmatched_high :
      (∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - matchProbability v) v ∂valueLaw) =
        valueLaw.real lowValuesᶜ -
          ∫ v : ℝ, lowValuesᶜ.indicator matchProbability v ∂valueLaw := by
    calc
      (∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - matchProbability v) v ∂valueLaw) =
          ∫ v : ℝ,
            lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v -
              lowValuesᶜ.indicator matchProbability v ∂valueLaw := by
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ lowValuesᶜ
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv,
            Set.indicator_of_mem hv]
        · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv,
            Set.indicator_of_notMem hv]
          ring
      _ = (∫ v : ℝ,
          lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v ∂valueLaw) -
            ∫ v : ℝ, lowValuesᶜ.indicator matchProbability v ∂valueLaw :=
        integral_sub hhigh_one_integrable hhigh_integrable
      _ = valueLaw.real lowValuesᶜ -
          ∫ v : ℝ, lowValuesᶜ.indicator matchProbability v ∂valueLaw := by
        have hone :
            (∫ v : ℝ,
              lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v ∂valueLaw) =
              valueLaw.real lowValuesᶜ := by
          simpa using (integral_indicator_one (μ := valueLaw)
            hlowValues.compl)
        rw [hone]
  rw [hunmatched_high]
  linarith [hpartition, htotal_mass]

/--
The PG24 source-model conservation identity with arbitrary type/preference
distribution.  It is the route from a low matched tail estimate to the
complementary high unmatched tail estimate.
-/
theorem theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value
            (Finset.univ : Finset (Fin n)) cutoff outcome)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_balance :
      (∫ v : ℝ,
        cutoffAffordanceProbability noiseLaw
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
        valueLaw.real lowValuesᶜ) :
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ lowValues ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
  let affordance : ℝ → ℝ :=
    fun v => cutoffAffordanceProbability noiseLaw
      (Finset.univ : Finset (Fin n)) v cutoff
  have haffordance_integrable : Integrable affordance valueLaw := by
    simpa [affordance, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw (Finset.univ : Finset (Fin n)) cutoff)
  have hmass_balance :
      (∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw) =
        ∫ v : ℝ,
          lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw := by
    apply theorem1_integral_low_matched_eq_high_unmatched_of_total_mass
      valueLaw affordance haffordance_integrable hlowValues
    simpa [affordance] using hcapacity_balance
  calc
    eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ lowValues ∧
            chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        ∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw := by
      simpa [affordance] using
        (theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
          studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
          (Finset.univ : Finset (Fin n)) cutoff choice hmatch_iff_affordance
          hlowValues)
    _ = ∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw :=
      hmass_balance
    _ = eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
      symm
      simpa [affordance] using
        (theorem1_source_model_value_restricted_unmatched_mass_eq_integral_affordance_complement
          studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
          (Finset.univ : Finset (Fin n)) cutoff choice hmatch_iff_affordance
          hlowValues.compl)

/--
Market-clearing form of the conservation identity.  The threshold
normalization is exposed as an equality between total capacity and the value
mass of the literal complementary high set.
-/
theorem theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_market_clearing
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value
            (Finset.univ : Finset (Fin n)) cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (studentLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_eq_high_value_mass :
      (∑ c : Fin n, M.capacity c) = valueLaw.real lowValuesᶜ) :
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ lowValues ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
  apply theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
    studentLaw value hvalue valueLaw hvalue_marginal noiseLaw cutoff choice
    hmatch_iff_affordance hlowValues
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
        ∑ c : Fin n, M.capacity c :=
      theorem1_source_model_whole_market_matched_mass_eq_total_capacity
        M K hclearing studentLaw value hvalue valueLaw hvalue_marginal
        noiseLaw cutoff choice hmatch_iff_affordance
        hchoice_mass_eq_aggregate_demand
    _ = valueLaw.real lowValuesᶜ := hcapacity_eq_high_value_mass

/--
One-market integration of a concrete cutoff-affordance tail estimate.  The
first conclusion is the paper's low matched tail mass; the second follows by
the checked capacity conservation identity for the literal complementary
high-value set.
-/
theorem theorem1_source_model_low_high_tail_mass_le_of_cutoff_tail_bound
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : StudentType × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : StudentType × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1TypeNoiseAffordanceEvent value
            (Finset.univ : Finset (Fin n)) cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (studentLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_eq_high_value_mass :
      (∑ c : Fin n, M.capacity c) = valueLaw.real lowValuesᶜ)
    {tailBound : ℝ}
    (hcutoff_tail :
      (∫ v : ℝ,
        lowValues.indicator
          (fun v => cutoffAffordanceProbability noiseLaw
            (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) ≤
        tailBound) :
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ lowValues ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) ≤
      tailBound ∧
    eventMass (studentLaw.prod noiseLaw)
      (fun outcome : StudentType × (Fin n → ℝ) =>
        value outcome.1 ∈ lowValuesᶜ ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) ≤
      tailBound := by
  have hmatched_eq :=
    theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      (Finset.univ : Finset (Fin n)) cutoff choice hmatch_iff_affordance
      hlowValues
  have hlow_bound :
      eventMass (studentLaw.prod noiseLaw)
        (fun outcome : StudentType × (Fin n → ℝ) =>
          value outcome.1 ∈ lowValues ∧
            chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) ≤
        tailBound := by
    rw [hmatched_eq]
    exact hcutoff_tail
  have hconservation :=
    theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_market_clearing
      M K hclearing studentLaw value hvalue valueLaw hvalue_marginal
      noiseLaw cutoff choice hmatch_iff_affordance
      hchoice_mass_eq_aggregate_demand hlowValues
      hcapacity_eq_high_value_mass
  constructor
  · exact hlow_bound
  · rw [← hconservation]
    exact hlow_bound

/--
The checked polynomial-rate conversion applied simultaneously to the two
source-model tail masses.  The caller supplies a concrete cutoff-affordance
integral as `cutoffTail`; the relation of that integral to actual matching
mass is established by
`theorem1_source_model_low_high_tail_mass_le_of_cutoff_tail_bound` above.
-/
theorem theorem1_eventually_low_high_tail_mass_lt_of_uniform_K_cutoff_tail_bound
    {Admissible : ℕ → Type*}
    {lowMatchedMass highUnmatchedMass cutoffTail :
      ∀ C : ℕ, Admissible C → ℝ}
    {A beta gamma : ℝ} {N0 : ℕ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hbridge :
      ∀ C : ℕ, ∀ a : Admissible C,
        lowMatchedMass C a ≤ cutoffTail C a ∧
          highUnmatchedMass C a = lowMatchedMass C a)
    (hcutoff_tail_polynomial :
      ∀ C : ℕ, N0 ≤ C →
        ∀ a : Admissible C,
          cutoffTail C a ≤
            A * Real.rpow (((C + 1 : ℕ) : ℝ))
              (-(theorem1TailK beta gamma))) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          lowMatchedMass C a < epsilon ∧ highUnmatchedMass C a < epsilon := by
  intro epsilon hepsilon
  have hsmall := theorem1Tail_eventually_forall_lt_of_uniform_K_bound
    (α := Admissible) (f := cutoffTail) hbeta hgamma
    hcutoff_tail_polynomial epsilon hepsilon
  filter_upwards [hsmall] with C hsmallC a
  have hrelations := hbridge C a
  constructor
  · exact lt_of_le_of_lt hrelations.1 (hsmallC a)
  · rw [hrelations.2]
    exact lt_of_le_of_lt hrelations.1 (hsmallC a)

end
end PG24NoisyMatchingMarkets
