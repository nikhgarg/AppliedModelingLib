import PG24NoisyMatchingMarkets.Theorem1BlockAffordanceFubini
import PG24NoisyMatchingMarkets.Theorem1CutoffPartition

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

private theorem theorem1_eventMass_or_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) {left right : Outcome -> Prop} :
    eventMass outcomeLaw (fun outcome => left outcome ∨ right outcome) ≤
      eventMass outcomeLaw left + eventMass outcomeLaw right := by
  unfold eventMass AppliedModelingLib.measureProb
  exact measureReal_union_le _ _

/--
The source choice rule lets the full matched event be split at any actual
cutoff partition.  The lower chosen block costs its clearing capacity; a
choice in the upper block is bounded only by the corresponding upper-block
affordance event.  Thus no false equivalence between choosing an upper college
and merely being able to afford one is used.
-/
theorem theorem1_sourceDemand_value_restricted_matched_mass_le_lower_capacity_add_upper_affordance_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (active lower upper : Finset (Fin n))
    (hpartition : active = lower ∪ upper)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand_lower :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand lower =
        ∑ college ∈ lower, M.aggregateDemand P college)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧ chosenInActive demand active outcome) ≤
      activeCapacity lower M.capacity +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff) v
          ∂valueLaw := by
  let outcomeLaw : Measure (StudentType × (Fin n -> ℝ)) :=
    studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw))
  let lowerChoice : StudentType × (Fin n -> ℝ) -> Prop :=
    fun outcome => chosenInActive demand lower outcome
  let upperAffordance : StudentType × (Fin n -> ℝ) -> Prop :=
    fun outcome =>
      value outcome.1 ∈ region ∧
        cutoffCrossedOn upper
          (noisyScore (value outcome.1) outcome.2) cutoff
  have hsplit : ∀ outcome : StudentType × (Fin n -> ℝ),
      value outcome.1 ∈ region ∧ chosenInActive demand active outcome ->
        lowerChoice outcome ∨ upperAffordance outcome := by
    intro outcome hmatched
    rcases hmatched.2 with ⟨college, hcollege_active, hchoice⟩
    have hcollege_partition : college ∈ lower ∪ upper := by
      rw [← hpartition]
      exact hcollege_active
    rcases Finset.mem_union.mp hcollege_partition with hcollege_lower | hcollege_upper
    · exact Or.inl ⟨college, hcollege_lower, hchoice⟩
    · refine Or.inr ⟨hmatched.1, college, hcollege_upper, ?_⟩
      simpa [noisyScore] using hchosen_feasible outcome college hchoice
  have hlower_capacity :
      eventMass outcomeLaw lowerChoice = activeCapacity lower M.capacity := by
    change choiceMass outcomeLaw demand lower = activeCapacity lower M.capacity
    exact sourceDemand_choiceMass_eq_activeCapacity_iid_of_marketClearing
      M K hclearing studentLaw noiseLaw demand lower
      hchoice_mass_eq_aggregate_demand_lower
  have hupper_affordance :
      eventMass outcomeLaw upperAffordance =
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff) v
          ∂valueLaw := by
    simpa [outcomeLaw, upperAffordance] using
      (theorem1_sourceDemand_value_restricted_affordance_mass_eq_integral_iid
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
        upper cutoff hregion)
  calc
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧ chosenInActive demand active outcome) ≤
        eventMass outcomeLaw (fun outcome =>
          lowerChoice outcome ∨ upperAffordance outcome) := by
      simpa [outcomeLaw] using (eventMass_mono outcomeLaw hsplit)
    _ ≤ eventMass outcomeLaw lowerChoice + eventMass outcomeLaw upperAffordance :=
      theorem1_eventMass_or_le outcomeLaw
    _ = activeCapacity lower M.capacity +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff) v
          ∂valueLaw := by
      rw [hlower_capacity, hupper_affordance]

end

end PG24NoisyMatchingMarkets
