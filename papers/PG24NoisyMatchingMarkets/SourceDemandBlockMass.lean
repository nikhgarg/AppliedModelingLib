import AppliedModelingLib.Markets.Matching.Affordability

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The two pointwise demand clauses used by the source model imply that choosing
some college is exactly the same as crossing some cutoff.  `StudentType` may
carry arbitrary preferences correlated with `value`; no independence between
those coordinates is used.
-/
theorem sourceDemand_chosenInAll_iff_cutoffCrossed
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (cutoff : Fin n -> ℝ)
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
      chosenInActive demand (Finset.univ : Finset (Fin n)) outcome ↔
        cutoffCrossedOn (Finset.univ : Finset (Fin n))
          (noisyScore (value outcome.1) outcome.2) cutoff := by
  intro outcome
  constructor
  · rintro ⟨college, hcollege, hdemand⟩
    refine ⟨college, hcollege, ?_⟩
    simpa [noisyScore] using hchosen_feasible outcome college hdemand
  · intro hcrossed
    have hnot_none : demand outcome ≠ none := by
      intro hnone
      exact ((hdemand_none_iff_no_crossed outcome).mp hnone) hcrossed
    cases hdemand : demand outcome with
    | none => exact False.elim (hnot_none hdemand)
    | some college => exact ⟨college, Finset.mem_univ _, hdemand⟩

/--
An arbitrary source event on `StudentType × iid noise` has mass at most the
capacity of a block whenever the event selects that block and its choice mass
is identified with clearing demand.  The theorem deliberately does not project
away `StudentType`, so preference/value correlation remains unrestricted.
-/
theorem sourceDemand_eventMass_le_activeCapacity_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (event : StudentType × (Fin n -> ℝ) -> Prop)
    (active : Finset (Fin n))
    (aggregateDemand capacity : Fin n -> ℝ)
    (hevent_chosen : ∀ outcome, event outcome -> chosenInActive demand active outcome)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active = ∑ college ∈ active, aggregateDemand college)
    (hclearing : ∀ college ∈ active, aggregateDemand college = capacity college) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw))) event ≤
      activeCapacity active capacity := by
  exact
    eventMass_le_activeCapacity_of_imp_aggregateDemand_eq_capacity
      (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
      demand active hevent_chosen hchoice_mass hclearing

/--
The selected block's source choice mass is exactly its capacity at a
market-clearing cutoff.  The equality connecting source choices to aggregate
demand is kept explicit rather than inferred from a function name.
-/
theorem sourceDemand_choiceMass_eq_activeCapacity_iid_of_marketClearing
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hmarketClearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (active : Finset (Fin n))
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active = ∑ college ∈ active, M.aggregateDemand P college) :
    choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active = activeCapacity active M.capacity := by
  exact
    choiceMass_eq_activeCapacity_of_aggregateDemand_eq_capacity
      (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
      demand active hchoice_mass
      (fun college _ => K.aggregateDemand_eq_capacity hmarketClearing college)

/--
The source event-to-capacity bound at an actual market-clearing cutoff.  This
is the form used for any named block, including a selected upper block.
-/
theorem sourceDemand_eventMass_le_activeCapacity_iid_of_marketClearing
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hmarketClearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (event : StudentType × (Fin n -> ℝ) -> Prop)
    (active : Finset (Fin n))
    (hevent_chosen : ∀ outcome, event outcome -> chosenInActive demand active outcome)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active = ∑ college ∈ active, M.aggregateDemand P college) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw))) event ≤
      activeCapacity active M.capacity := by
  exact
    sourceDemand_eventMass_le_activeCapacity_iid
      studentLaw noiseLaw demand event active (M.aggregateDemand P) M.capacity
      hevent_chosen hchoice_mass
      (fun college _ => K.aggregateDemand_eq_capacity hmarketClearing college)

/--
The selected cutoff representing a stable matching supplies the clearing fact
needed by `sourceDemand_eventMass_le_activeCapacity_iid_of_marketClearing`.
No conclusion is attached to a particular block name.
-/
theorem sourceDemand_selectedStable_eventMass_le_activeCapacity_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (event : StudentType × (Fin n -> ℝ) -> Prop)
    (active : Finset (Fin n))
    (hevent_chosen : ∀ outcome, event outcome -> chosenInActive demand active outcome)
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active =
          ∑ college ∈ active,
            M.aggregateDemand (I.marketClearingCutoffOfStable hstable) college) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw))) event ≤
      activeCapacity active M.capacity := by
  exact
    sourceDemand_eventMass_le_activeCapacity_iid_of_marketClearing
      M K (I.marketClearingCutoffOfStable_marketClearing hstable)
      studentLaw noiseLaw demand event active hevent_chosen hchoice_mass

/--
At the selected clearing cutoff, the source mass choosing any finite block is
exactly that block's capacity.  A caller may instantiate `active` with an
upper block, but the statement itself does not rely on that label.
-/
theorem sourceDemand_selectedStable_choiceMass_eq_activeCapacity_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (active : Finset (Fin n))
    (hchoice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active =
          ∑ college ∈ active,
            M.aggregateDemand (I.marketClearingCutoffOfStable hstable) college) :
    choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand active = activeCapacity active M.capacity := by
  exact
    sourceDemand_choiceMass_eq_activeCapacity_iid_of_marketClearing
      M K (I.marketClearingCutoffOfStable_marketClearing hstable)
      studentLaw noiseLaw demand active hchoice_mass

end

end PG24NoisyMatchingMarkets
