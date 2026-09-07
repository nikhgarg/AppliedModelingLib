import PG24NoisyMatchingMarkets.Assumptions
import Mathlib.MeasureTheory.Integral.Prod

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The source model's value/noise event that a student can afford at least one
college in the designated block.  For the whole market the block is
`Finset.univ`, exactly as in PG24's definition of `p_mu(v)`.
-/
def theorem1CutoffAffordanceEvent {n : ℕ}
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ) :
    ℝ × (Fin n → ℝ) → Prop :=
  fun outcome =>
    cutoffCrossedOn active (noisyScore outcome.1 outcome.2) cutoff

private theorem theorem1_cutoff_affordance_section_measurable
    {n : ℕ} (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) :
    MeasurableSet
      {noise : Fin n → ℝ |
        cutoffCrossedOn active (noisyScore v noise) cutoff} := by
  classical
  let collegeEvent : Fin n → Set (Fin n → ℝ) :=
    fun c => {noise | cutoff c < v + noise c}
  have hset :
      {noise : Fin n → ℝ |
        cutoffCrossedOn active (noisyScore v noise) cutoff} =
        ⋃ c ∈ active, collegeEvent c := by
    ext noise
    simp [collegeEvent, cutoffCrossedOn, noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore : Measurable (fun noise : Fin n → ℝ => v + noise c) := by
    fun_prop
  change MeasurableSet {noise : Fin n → ℝ | cutoff c < v + noise c}
  exact measurableSet_Ioi.preimage hscore

private theorem theorem1_region_cutoff_affordance_measurable
    {n : ℕ} (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    MeasurableSet
      {outcome : ℝ × (Fin n → ℝ) |
        outcome.1 ∈ region ∧
          theorem1CutoffAffordanceEvent active cutoff outcome} := by
  classical
  let collegeEvent : Fin n → Set (ℝ × (Fin n → ℝ)) :=
    fun c =>
      {outcome |
        outcome.1 ∈ region ∧ cutoff c < outcome.1 + outcome.2 c}
  have hset :
      {outcome : ℝ × (Fin n → ℝ) |
        outcome.1 ∈ region ∧
          theorem1CutoffAffordanceEvent active cutoff outcome} =
        ⋃ c ∈ active, collegeEvent c := by
    ext outcome
    simp [collegeEvent, theorem1CutoffAffordanceEvent, cutoffCrossedOn,
      noisyScore]
  rw [hset]
  refine Finset.measurableSet_biUnion active ?_
  intro c hc
  have hscore :
      Measurable (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 + outcome.2 c) := by
    fun_prop
  have hvalue :
      MeasurableSet {outcome : ℝ × (Fin n → ℝ) | outcome.1 ∈ region} := by
    change MeasurableSet ((fun outcome : ℝ × (Fin n → ℝ) => outcome.1) ⁻¹' region)
    exact hregion.preimage measurable_fst
  change MeasurableSet
    ({outcome : ℝ × (Fin n → ℝ) | outcome.1 ∈ region} ∩
      {outcome : ℝ × (Fin n → ℝ) | cutoff c < outcome.1 + outcome.2 c})
  exact hvalue.inter (measurableSet_Ioi.preimage hscore)

/--
Fubini bridge for the actual PG24 product source model.  The mass of students
whose values lie in `region` and who can afford a college is exactly the value
integral of the cutoff-affordance probability over that region.

This is a definition-level consequence of independent value/noise sampling;
it does not assume a cutoff sandwich or a tail estimate.
-/
theorem theorem1_value_restricted_cutoff_affordance_mass_eq_integral
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          theorem1CutoffAffordanceEvent active cutoff outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  let event : Set (ℝ × (Fin n → ℝ)) :=
    {outcome |
      outcome.1 ∈ region ∧
        theorem1CutoffAffordanceEvent active cutoff outcome}
  have hevent : MeasurableSet event :=
    theorem1_region_cutoff_affordance_measurable active cutoff hregion
  have hintegrable :
      Integrable (event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)))
        (valueLaw.prod noiseLaw) :=
    (integrable_const _).indicator hevent
  have hfubini :=
    integral_prod
      (f := event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)))
      hintegrable
  change (valueLaw.prod noiseLaw).real event = _
  calc
    (valueLaw.prod noiseLaw).real event =
        ∫ outcome : ℝ × (Fin n → ℝ),
          event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) outcome
          ∂(valueLaw.prod noiseLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ v : ℝ,
        ∫ noise : Fin n → ℝ,
          event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)
          ∂noiseLaw ∂valueLaw := hfubini
    _ = ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with v
      let crossing : Set (Fin n → ℝ) :=
        {noise |
          cutoffCrossedOn active (noisyScore v noise) cutoff}
      have hcrossing : MeasurableSet crossing :=
        theorem1_cutoff_affordance_section_measurable active v cutoff
      by_cases hv : v ∈ region
      · rw [Set.indicator_of_mem hv]
        have hsection :
            (fun noise : Fin n → ℝ =>
              event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)) =
              crossing.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) := by
          funext noise
          by_cases hcross :
              cutoffCrossedOn active (noisyScore v noise) cutoff
          · have hevent_mem : (v, noise) ∈ event := by
              change v ∈ region ∧
                theorem1CutoffAffordanceEvent active cutoff (v, noise)
              exact ⟨hv, hcross⟩
            have hcrossing_mem : noise ∈ crossing := by
              change cutoffCrossedOn active (noisyScore v noise) cutoff
              exact hcross
            rw [Set.indicator_of_mem hevent_mem,
              Set.indicator_of_mem hcrossing_mem]
          · have hevent_not_mem : (v, noise) ∉ event := by
              intro hevent_mem
              apply hcross
              exact hevent_mem.2
            have hcrossing_not_mem : noise ∉ crossing := by
              intro hcrossing_mem
              apply hcross
              exact hcrossing_mem
            rw [Set.indicator_of_notMem hevent_not_mem,
              Set.indicator_of_notMem hcrossing_not_mem]
        rw [hsection]
        calc
          ∫ noise : Fin n → ℝ,
              crossing.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) noise
              ∂noiseLaw = noiseLaw.real crossing := by
            simpa using (integral_indicator_one (μ := noiseLaw) hcrossing)
          _ = cutoffAffordanceProbability noiseLaw active v cutoff := by
            rfl
      · rw [Set.indicator_of_notMem hv]
        have hsection :
            (fun noise : Fin n → ℝ =>
              event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)) =
              fun _ : Fin n → ℝ => (0 : ℝ) := by
          funext noise
          simp [event, hv]
        rw [hsection]
        simp

/--
The preceding product-law identity expressed using the source model's actual
matching choice.  `hmatch_iff_affordance` is precisely PG24's model claim
that a student matches iff some college is affordable; it does not impose an
extra outcome-event implication.
-/
theorem theorem1_value_restricted_matched_mass_eq_integral_affordance
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  have hevent :
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ region ∧
            theorem1CutoffAffordanceEvent active cutoff outcome) := by
    funext outcome
    apply propext
    constructor
    · intro h
      exact ⟨h.1, (hmatch_iff_affordance outcome).mp h.2⟩
    · intro h
      exact ⟨h.1, (hmatch_iff_affordance outcome).mpr h.2⟩
  rw [hevent]
  exact theorem1_value_restricted_cutoff_affordance_mass_eq_integral
    valueLaw noiseLaw active cutoff hregion

/--
At an exactly clearing cutoff, whole-market matched mass equals total
capacity.  The proof combines the product-law mass identity, the source
match-iff-affordance semantics, and the model's aggregate-demand definition.

The remaining `hchoice_mass_eq_aggregate_demand` premise is a primitive model
identification: it says that the mass choosing each college is the market's
aggregate demand.  It is not a tail or cutoff conclusion.
-/
theorem theorem1_whole_market_matched_mass_eq_total_capacity
    {Student : Type*} {n : ℕ}
    (M : CutoffMarket Student (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent (Finset.univ : Finset (Fin n))
            cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (valueLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c) :
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw (Finset.univ : Finset (Fin n)) v
        cutoff ∂valueLaw) =
      ∑ c : Fin n, M.capacity c := by
  have hmatched :
      eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        ∫ v : ℝ,
          cutoffAffordanceProbability noiseLaw
            (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw := by
    simpa using
      (theorem1_value_restricted_matched_mass_eq_integral_affordance
        valueLaw noiseLaw (Finset.univ : Finset (Fin n)) cutoff choice
        hmatch_iff_affordance (region := Set.univ) MeasurableSet.univ)
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw (Finset.univ : Finset (Fin n)) v
        cutoff ∂valueLaw) =
        choiceMass (valueLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) := by
      simpa [choiceMass] using hmatched.symm
    _ = ∑ c : Fin n, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregate_demand
    _ = ∑ c : Fin n, M.capacity c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact K.aggregateDemand_eq_capacity hclearing c

/--
Every value-restricted integral of whole-market cutoff affordability is bounded
by total capacity at a clearing cutoff.  This is the source proof's legitimate
``there cannot be more matched mass than capacity'' step, expressed without a
pointwise match-event bridge.
-/
theorem theorem1_value_restricted_affordance_integral_le_total_capacity
    {Student : Type*} {n : ℕ}
    (M : CutoffMarket Student (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent (Finset.univ : Finset (Fin n))
            cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (valueLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    (∫ v : ℝ,
      region.indicator
        (fun v =>
          cutoffAffordanceProbability noiseLaw
            (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) ≤
      ∑ c : Fin n, M.capacity c := by
  have htail :=
    theorem1_value_restricted_matched_mass_eq_integral_affordance
      valueLaw noiseLaw (Finset.univ : Finset (Fin n)) cutoff choice
      hmatch_iff_affordance hregion
  calc
    (∫ v : ℝ,
      region.indicator
        (fun v =>
          cutoffAffordanceProbability noiseLaw
            (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) =
        eventMass (valueLaw.prod noiseLaw)
          (fun outcome : ℝ × (Fin n → ℝ) =>
            outcome.1 ∈ region ∧
              chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) :=
      htail.symm
    _ ≤ eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) :=
      eventMass_mono (valueLaw.prod noiseLaw) (fun _ h => h.2)
    _ = choiceMass (valueLaw.prod noiseLaw) choice
        (Finset.univ : Finset (Fin n)) := rfl
    _ = ∑ c : Fin n, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregate_demand
    _ = ∑ c : Fin n, M.capacity c := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact K.aggregateDemand_eq_capacity hclearing c

/--
The corresponding product-law identity for students who remain unmatched.
For each value, the complement of the affordability event has probability
`1 - cutoffAffordanceProbability` under the probability noise law.
-/
theorem theorem1_value_restricted_cutoff_unaffordance_mass_eq_integral
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          ¬ theorem1CutoffAffordanceEvent active cutoff outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v =>
            1 - cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  let event : Set (ℝ × (Fin n → ℝ)) :=
    {outcome |
      outcome.1 ∈ region ∧
        ¬ theorem1CutoffAffordanceEvent active cutoff outcome}
  have hvalue :
      MeasurableSet
        {outcome : ℝ × (Fin n → ℝ) | outcome.1 ∈ region} := by
    change MeasurableSet
      ((fun outcome : ℝ × (Fin n → ℝ) => outcome.1) ⁻¹' region)
    exact hregion.preimage measurable_fst
  have hcross :
      MeasurableSet
        {outcome : ℝ × (Fin n → ℝ) |
          theorem1CutoffAffordanceEvent active cutoff outcome} := by
    simpa [theorem1CutoffAffordanceEvent] using
      (theorem1_region_cutoff_affordance_measurable active cutoff
        (region := Set.univ) MeasurableSet.univ)
  have hevent : MeasurableSet event := by
    change MeasurableSet
      ({outcome : ℝ × (Fin n → ℝ) | outcome.1 ∈ region} ∩
        {outcome : ℝ × (Fin n → ℝ) |
          theorem1CutoffAffordanceEvent active cutoff outcome}ᶜ)
    exact hvalue.inter hcross.compl
  have hintegrable :
      Integrable (event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)))
        (valueLaw.prod noiseLaw) :=
    (integrable_const _).indicator hevent
  have hfubini :=
    integral_prod
      (f := event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)))
      hintegrable
  change (valueLaw.prod noiseLaw).real event = _
  calc
    (valueLaw.prod noiseLaw).real event =
        ∫ outcome : ℝ × (Fin n → ℝ),
          event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) outcome
          ∂(valueLaw.prod noiseLaw) :=
      (integral_indicator_one hevent).symm
    _ = ∫ v : ℝ,
        ∫ noise : Fin n → ℝ,
          event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)
          ∂noiseLaw ∂valueLaw := hfubini
    _ = ∫ v : ℝ,
        region.indicator
          (fun v =>
            1 - cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
      apply integral_congr_ae
      filter_upwards with v
      let crossing : Set (Fin n → ℝ) :=
        {noise |
          cutoffCrossedOn active (noisyScore v noise) cutoff}
      have hcrossing : MeasurableSet crossing :=
        theorem1_cutoff_affordance_section_measurable active v cutoff
      by_cases hv : v ∈ region
      · rw [Set.indicator_of_mem hv]
        have hsection :
            (fun noise : Fin n → ℝ =>
              event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)) =
              crossingᶜ.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) := by
          funext noise
          by_cases hcrossing_mem : noise ∈ crossing
          · have hevent_not_mem : (v, noise) ∉ event := by
              intro hevent_mem
              apply hevent_mem.2
              exact hcrossing_mem
            have hcrossing_compl_not_mem : noise ∉ crossingᶜ := by
              intro hcrossing_compl_mem
              exact hcrossing_compl_mem hcrossing_mem
            rw [Set.indicator_of_notMem hevent_not_mem,
              Set.indicator_of_notMem hcrossing_compl_not_mem]
          · have hevent_mem : (v, noise) ∈ event := by
              change v ∈ region ∧
                ¬ theorem1CutoffAffordanceEvent active cutoff (v, noise)
              constructor
              · exact hv
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
          _ = 1 - cutoffAffordanceProbability noiseLaw active v cutoff := by
            rw [probReal_univ]
            rfl
      · rw [Set.indicator_of_notMem hv]
        have hsection :
            (fun noise : Fin n → ℝ =>
              event.indicator (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)) (v, noise)) =
              fun _ : Fin n → ℝ => (0 : ℝ) := by
          funext noise
          have hevent_not_mem : (v, noise) ∉ event := by
            intro hevent_mem
            exact hv hevent_mem.1
          rw [Set.indicator_of_notMem hevent_not_mem]
        rw [hsection]
        simp

/--
The unmatched product-law identity expressed through the actual matching
choice and the source's exact match-iff-affordance statement.
-/
theorem theorem1_value_restricted_unmatched_mass_eq_integral_affordance_complement
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v =>
            1 - cutoffAffordanceProbability noiseLaw active v cutoff) v
        ∂valueLaw := by
  have hevent :
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ region ∧
            ¬ theorem1CutoffAffordanceEvent active cutoff outcome) := by
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
  rw [hevent]
  exact theorem1_value_restricted_cutoff_unaffordance_mass_eq_integral
    valueLaw noiseLaw active cutoff hregion

/--
A uniform low-value cutoff-affordance bound controls the actual mass of
matched students in that value region.  This is the direct population-level
bridge needed before a source proof turns cutoff estimates into tail masses.
-/
theorem theorem1_value_restricted_matched_mass_le_of_uniform_affordance
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region)
    {epsilon : ℝ} (hepsilon_nonneg : 0 ≤ epsilon)
    (hbound :
      ∀ v : ℝ, v ∈ region →
        cutoffAffordanceProbability noiseLaw active v cutoff ≤ epsilon) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) ≤
      epsilon := by
  let affordance : ℝ → ℝ :=
    fun v => cutoffAffordanceProbability noiseLaw active v cutoff
  have haffordance_integrable : Integrable affordance valueLaw := by
    simpa [affordance, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw active cutoff)
  have hregion_integrable :
      Integrable (region.indicator affordance) valueLaw :=
    haffordance_integrable.indicator hregion
  have hpointwise : ∀ v : ℝ, region.indicator affordance v ≤ epsilon := by
    intro v
    by_cases hv : v ∈ region
    · rw [Set.indicator_of_mem hv]
      exact hbound v hv
    · rw [Set.indicator_of_notMem hv]
      exact hepsilon_nonneg
  have hintegral :
      (∫ v : ℝ, region.indicator affordance v ∂valueLaw) ≤
        ∫ _v : ℝ, epsilon ∂valueLaw :=
    integral_mono hregion_integrable (integrable_const _) hpointwise
  calc
    eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ region ∧
            chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        ∫ v : ℝ, region.indicator affordance v ∂valueLaw := by
      simpa [affordance] using
        (theorem1_value_restricted_matched_mass_eq_integral_affordance
          valueLaw noiseLaw active cutoff choice hmatch_iff_affordance hregion)
    _ ≤ ∫ _v : ℝ, epsilon ∂valueLaw := hintegral
    _ = epsilon := by
      rw [integral_const, probReal_univ]
      simp

/--
The high-value counterpart: a uniform lower cutoff-affordance bound controls
the actual mass of unmatched students in that region.
-/
theorem theorem1_value_restricted_unmatched_mass_le_of_uniform_affordance
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent active cutoff outcome)
    {region : Set ℝ} (hregion : MeasurableSet region)
    {epsilon : ℝ} (hepsilon_nonneg : 0 ≤ epsilon)
    (hbound :
      ∀ v : ℝ, v ∈ region →
        1 - epsilon ≤
          cutoffAffordanceProbability noiseLaw active v cutoff) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ region ∧
          ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) ≤
      epsilon := by
  let unaffordance : ℝ → ℝ :=
    fun v => 1 - cutoffAffordanceProbability noiseLaw active v cutoff
  have haffordance_integrable :
      Integrable
        (fun v : ℝ => cutoffAffordanceProbability noiseLaw active v cutoff)
        valueLaw := by
    simpa [cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw active cutoff)
  have hunaffordance_integrable : Integrable unaffordance valueLaw := by
    exact (integrable_const _).sub haffordance_integrable
  have hregion_integrable :
      Integrable (region.indicator unaffordance) valueLaw :=
    hunaffordance_integrable.indicator hregion
  have hpointwise : ∀ v : ℝ, region.indicator unaffordance v ≤ epsilon := by
    intro v
    by_cases hv : v ∈ region
    · rw [Set.indicator_of_mem hv]
      dsimp [unaffordance]
      linarith [hbound v hv]
    · rw [Set.indicator_of_notMem hv]
      exact hepsilon_nonneg
  have hintegral :
      (∫ v : ℝ, region.indicator unaffordance v ∂valueLaw) ≤
        ∫ _v : ℝ, epsilon ∂valueLaw :=
    integral_mono hregion_integrable (integrable_const _) hpointwise
  calc
    eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ region ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        ∫ v : ℝ, region.indicator unaffordance v ∂valueLaw := by
      simpa [unaffordance] using
        (theorem1_value_restricted_unmatched_mass_eq_integral_affordance_complement
          valueLaw noiseLaw active cutoff choice hmatch_iff_affordance hregion)
    _ ≤ ∫ _v : ℝ, epsilon ∂valueLaw := hintegral
    _ = epsilon := by
      rw [integral_const, probReal_univ]
      simp

/--
If the total matched mass equals the value mass outside `lowValues`, then the
matched mass inside `lowValues` equals the unmatched mass outside it.  This is
the exact population conservation identity behind PG24's high-tail argument.

For a threshold application, use a low set whose complement is the source's
high-value set.  If the paper insists on strict inequalities on both sides,
the remaining boundary-atom issue must be proved separately rather than
silently discarded.
-/
theorem theorem1_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
    {n : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent (Finset.univ : Finset (Fin n))
            cutoff outcome)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_balance :
      (∫ v : ℝ,
        cutoffAffordanceProbability noiseLaw
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
        valueLaw.real lowValuesᶜ) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ lowValues ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
  let affordance : ℝ → ℝ :=
    fun v => cutoffAffordanceProbability noiseLaw
      (Finset.univ : Finset (Fin n)) v cutoff
  have haffordance_integrable : Integrable affordance valueLaw := by
    simpa [affordance, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        noiseLaw valueLaw (Finset.univ : Finset (Fin n)) cutoff)
  have hlow_integrable :
      Integrable (lowValues.indicator affordance) valueLaw :=
    haffordance_integrable.indicator hlowValues
  have hhigh_integrable :
      Integrable (lowValuesᶜ.indicator affordance) valueLaw :=
    haffordance_integrable.indicator hlowValues.compl
  have hhigh_one_integrable :
      Integrable (lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ))) valueLaw :=
    (integrable_const _).indicator hlowValues.compl
  have hpartition :
      (∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw) +
        ∫ v : ℝ, lowValuesᶜ.indicator affordance v ∂valueLaw =
        ∫ v : ℝ, affordance v ∂valueLaw := by
    calc
      (∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw) +
          ∫ v : ℝ, lowValuesᶜ.indicator affordance v ∂valueLaw =
          ∫ v : ℝ,
            lowValues.indicator affordance v +
              lowValuesᶜ.indicator affordance v ∂valueLaw := by
        rw [integral_add hlow_integrable hhigh_integrable]
      _ = ∫ v : ℝ, affordance v ∂valueLaw := by
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
        lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw) =
        valueLaw.real lowValuesᶜ -
          ∫ v : ℝ, lowValuesᶜ.indicator affordance v ∂valueLaw := by
    calc
      (∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw) =
          ∫ v : ℝ,
            lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v -
              lowValuesᶜ.indicator affordance v ∂valueLaw := by
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
            ∫ v : ℝ, lowValuesᶜ.indicator affordance v ∂valueLaw :=
        integral_sub hhigh_one_integrable hhigh_integrable
      _ = valueLaw.real lowValuesᶜ -
          ∫ v : ℝ, lowValuesᶜ.indicator affordance v ∂valueLaw := by
        have hone :
            (∫ v : ℝ,
              lowValuesᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v ∂valueLaw) =
              valueLaw.real lowValuesᶜ := by
          simpa using (integral_indicator_one (μ := valueLaw)
            hlowValues.compl)
        rw [hone]
  have hcapacity_balance' :
      (∫ v : ℝ, affordance v ∂valueLaw) = valueLaw.real lowValuesᶜ := by
    simpa [affordance] using hcapacity_balance
  have hmass_balance :
      (∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw) =
        ∫ v : ℝ,
          lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw := by
    rw [hunmatched_high]
    linarith [hpartition, hcapacity_balance']
  calc
    eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ lowValues ∧
            chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
        ∫ v : ℝ, lowValues.indicator affordance v ∂valueLaw := by
      simpa [affordance] using
        (theorem1_value_restricted_matched_mass_eq_integral_affordance
          valueLaw noiseLaw (Finset.univ : Finset (Fin n)) cutoff choice
          hmatch_iff_affordance hlowValues)
    _ = ∫ v : ℝ,
        lowValuesᶜ.indicator (fun v => 1 - affordance v) v ∂valueLaw :=
      hmass_balance
    _ = eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
      symm
      simpa [affordance] using
        (theorem1_value_restricted_unmatched_mass_eq_integral_affordance_complement
          valueLaw noiseLaw (Finset.univ : Finset (Fin n)) cutoff choice
          hmatch_iff_affordance hlowValues.compl)

/--
Market-clearing specialization of the conservation identity.  The explicit
`hcapacity_eq_high_value_mass` is the paper's threshold normalization; it is
kept visible so threshold atoms cannot be erased by the proof wrapper.
-/
theorem theorem1_low_matched_mass_eq_high_unmatched_mass_of_market_clearing
    {Student : Type*} {n : ℕ}
    (M : CutoffMarket Student (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure (Fin n → ℝ)) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ)
    (choice : ℝ × (Fin n → ℝ) → Option (Fin n))
    (hmatch_iff_affordance :
      ∀ outcome : ℝ × (Fin n → ℝ),
        chosenInActive choice (Finset.univ : Finset (Fin n)) outcome ↔
          theorem1CutoffAffordanceEvent (Finset.univ : Finset (Fin n))
            cutoff outcome)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass (valueLaw.prod noiseLaw) choice
          (Finset.univ : Finset (Fin n)) =
        ∑ c : Fin n, M.aggregateDemand P c)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_eq_high_value_mass :
      (∑ c : Fin n, M.capacity c) = valueLaw.real lowValuesᶜ) :
    eventMass (valueLaw.prod noiseLaw)
      (fun outcome : ℝ × (Fin n → ℝ) =>
        outcome.1 ∈ lowValues ∧
          chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) =
      eventMass (valueLaw.prod noiseLaw)
        (fun outcome : ℝ × (Fin n → ℝ) =>
          outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive choice (Finset.univ : Finset (Fin n)) outcome) := by
  apply theorem1_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
    valueLaw noiseLaw cutoff choice hmatch_iff_affordance hlowValues
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
        ∑ c : Fin n, M.capacity c :=
      theorem1_whole_market_matched_mass_eq_total_capacity
        M K hclearing valueLaw noiseLaw cutoff choice hmatch_iff_affordance
        hchoice_mass_eq_aggregate_demand
    _ = valueLaw.real lowValuesᶜ := hcapacity_eq_high_value_mass

end
end PG24NoisyMatchingMarkets
