import PG24NoisyMatchingMarkets.Theorem1SourceDemandDecomposition
import PG24NoisyMatchingMarkets.Theorem1SelectedCutoffGeometry
import PG24NoisyMatchingMarkets.Theorem2LiteralBasicRegularWindow
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal selected-cutoff bridge

This file connects the T1 cutoff analysis to the source-defined finite
preference demand rule.  In particular, every block-demand equality below is
derived from singleton demand events at the literal selected cutoff.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

namespace PG24LiteralBasicTwoScaleInstance

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Cutoff : Type v}

/-- The analytic cutoff vector is exactly the literal selected cutoff's coordinates. -/
theorem theorem1_selectedCutoffVector_eq_literal_coordinates
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) :
    inst.selectedCutoffVector =
      inst.literal.demand.cutoffCoordinates inst.literal.selectedCutoff :=
  rfl

/--
At the literal selected cutoff, matching somewhere in the local market is
equivalent to crossing a local cutoff.  This is derived from the literal
unmatched rule and literal affordability of a selected college.
-/
theorem theorem1_selected_chosenInAll_iff_affordance
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff) :
    ∀ outcome : StudentType × (Fin (C + 1) → ℝ),
      chosenInActive
          (inst.literal.demand.demandAt inst.literal.selectedCutoff)
          (Finset.univ : Finset (Fin (C + 1))) outcome ↔
        theorem1TypeNoiseAffordanceEvent inst.value
          (Finset.univ : Finset (Fin (C + 1)))
          inst.selectedCutoffVector outcome := by
  exact theorem1_sourceDemand_chosenInAll_iff_affordance
    inst.value inst.selectedCutoffVector
    (inst.literal.demand.demandAt inst.literal.selectedCutoff)
    inst.selected_demand_none_iff_no_crossed inst.selected_demand_feasible

/--
The literal finite-preference model supplies the aggregate-demand identity on
every finite cutoff block, not only on the whole market.
-/
theorem theorem1_selected_choiceMass_eq_aggregateDemand_on
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (active : Finset (Fin (C + 1))) :
    choiceMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (inst.literal.demand.demandAt inst.literal.selectedCutoff) active =
      ∑ college ∈ active,
        inst.literal.demand.aggregateDemand inst.literal.selectedCutoff college :=
  inst.selected_choiceMass_eq_aggregateDemand active

/--
At the literal selected cutoff, the full iid affordance integral equals the
source total capacity.  The proof uses literal demand semantics and literal
clearing, with no separately supplied choice-mass equality.
-/
theorem theorem1_selected_full_affordance_integral_eq_totalSupply
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    [IsProbabilityMeasure noiseLaw] :
    (∫ value : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        inst.selectedCutoffVector ∂eta) = totalSupply := by
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← inst.value_marginal]
    exact Measure.isProbabilityMeasure_map inst.value_measurable.aemeasurable
  have hmatched :=
    theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
      inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
      noiseLaw inst.selectedCutoffVector
      (inst.literal.demand.demandAt inst.literal.selectedCutoff)
      inst.selected_demand_none_iff_no_crossed inst.selected_demand_feasible
      (region := Set.univ) MeasurableSet.univ
  calc
    (∫ value : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        inst.selectedCutoffVector ∂eta) =
        choiceMass
          (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (inst.literal.demand.demandAt inst.literal.selectedCutoff)
          (Finset.univ : Finset (Fin (C + 1))) := by
      simpa [choiceMass] using hmatched.symm
    _ = ∑ college : Fin (C + 1),
          inst.literal.demand.aggregateDemand inst.literal.selectedCutoff college := by
      simpa using inst.theorem1_selected_choiceMass_eq_aggregateDemand_on
        (Finset.univ : Finset (Fin (C + 1)))
    _ = ∑ college : Fin (C + 1), inst.literal.capacity college := by
      refine Finset.sum_congr rfl ?_
      intro college _
      exact inst.selected_clearing college
    _ = totalSupply := inst.literal.totalCapacity_eq

/--
Literal clearing and the source threshold identity conserve low matched mass
against high unmatched mass.  Both sides refer to the same literal selected
demand rule.
-/
theorem theorem1_selected_low_matched_mass_eq_high_unmatched_mass
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    [IsProbabilityMeasure noiseLaw]
    (vS : ℝ) (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) =
      eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ Set.Ioi vS ∧
            ¬ chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) := by
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← inst.value_marginal]
    exact Measure.isProbabilityMeasure_map inst.value_measurable.aemeasurable
  have hcapacity_balance :
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          inst.selectedCutoffVector ∂eta) = eta.real (Set.Iic vS)ᶜ := by
    calc
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          inst.selectedCutoffVector ∂eta) = totalSupply :=
        inst.theorem1_selected_full_affordance_integral_eq_totalSupply
      _ = eta.real (Set.Ioi vS) := htail_normalization.symm
      _ = eta.real (Set.Iic vS)ᶜ := by simp
  simpa using
    (theorem1_source_model_low_matched_mass_eq_high_unmatched_mass_of_capacity_balance
      inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) inst.selectedCutoffVector
      (inst.literal.demand.demandAt inst.literal.selectedCutoff)
      inst.theorem1_selected_chosenInAll_iff_affordance measurableSet_Iic
      hcapacity_balance)

/--
The literal selected demand rule gives the source's cutoff split directly.
The lower block is paid for by literal clearing capacity, while a choice in
the upper block is bounded only by the corresponding affordance event.
-/
theorem theorem1_selected_low_matched_mass_le_lower_capacity_add_upper_affordance
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    [IsProbabilityMeasure noiseLaw]
    (pivot : ℝ) {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ region ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      activeCapacity
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
          inst.selectedCutoffVector pivot)
        inst.literal.capacity +
        ∫ value : ℝ,
          region.indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1)))
                inst.selectedCutoffVector pivot)
              value inst.selectedCutoffVector) value
          ∂eta := by
  classical
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← inst.value_marginal]
    exact Measure.isProbabilityMeasure_map inst.value_measurable.aemeasurable
  let outcomeLaw : Measure (StudentType × (Fin (C + 1) → ℝ)) :=
    inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
  let active : Finset (Fin (C + 1)) := Finset.univ
  let lower : Finset (Fin (C + 1)) :=
    theorem1CutoffBelowBlock active inst.selectedCutoffVector pivot
  let upper : Finset (Fin (C + 1)) :=
    theorem1CutoffAtOrAboveBlock active inst.selectedCutoffVector pivot
  let lowerChoice : StudentType × (Fin (C + 1) → ℝ) → Prop :=
    fun outcome => chosenInActive
      (inst.literal.demand.demandAt inst.literal.selectedCutoff) lower outcome
  let upperAffordance : StudentType × (Fin (C + 1) → ℝ) → Prop :=
    fun outcome =>
      inst.value outcome.1 ∈ region ∧
        cutoffCrossedOn upper
          (noisyScore (inst.value outcome.1) outcome.2) inst.selectedCutoffVector
  have hpartition : active = lower ∪ upper := by
    dsimp [active, lower, upper]
    exact theorem1CutoffBelowBlock_union_atOrAboveBlock
      (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector pivot
  have hsplit : ∀ outcome : StudentType × (Fin (C + 1) → ℝ),
      inst.value outcome.1 ∈ region ∧
        chosenInActive
          (inst.literal.demand.demandAt inst.literal.selectedCutoff)
          active outcome ->
        lowerChoice outcome ∨ upperAffordance outcome := by
    intro outcome hmatched
    rcases hmatched.2 with ⟨college, hcollege_active, hchoice⟩
    have hcollege_partition : college ∈ lower ∪ upper := by
      rw [← hpartition]
      exact hcollege_active
    rcases Finset.mem_union.mp hcollege_partition with hcollege_lower | hcollege_upper
    · exact Or.inl ⟨college, hcollege_lower, hchoice⟩
    · refine Or.inr ⟨hmatched.1, college, hcollege_upper, ?_⟩
      simpa [noisyScore] using
        inst.selected_demand_feasible outcome college hchoice
  have hlower_capacity :
      eventMass outcomeLaw lowerChoice = activeCapacity lower inst.literal.capacity := by
    change choiceMass outcomeLaw
      (inst.literal.demand.demandAt inst.literal.selectedCutoff) lower = _
    calc
      choiceMass outcomeLaw
          (inst.literal.demand.demandAt inst.literal.selectedCutoff) lower =
          ∑ college ∈ lower,
            inst.literal.demand.aggregateDemand inst.literal.selectedCutoff college := by
        simpa [outcomeLaw] using
          inst.theorem1_selected_choiceMass_eq_aggregateDemand_on lower
      _ = activeCapacity lower inst.literal.capacity := by
        unfold activeCapacity
        refine Finset.sum_congr rfl ?_
        intro college _
        exact inst.selected_clearing college
  have hupper_affordance :
      eventMass outcomeLaw upperAffordance =
        ∫ value : ℝ,
          region.indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
              inst.selectedCutoffVector) value
          ∂eta := by
    simpa [outcomeLaw, upperAffordance] using
      (theorem1_sourceDemand_value_restricted_affordance_mass_eq_integral_iid
        inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
        noiseLaw upper inst.selectedCutoffVector hregion)
  have hresult :
      eventMass outcomeLaw (fun outcome => lowerChoice outcome ∨ upperAffordance outcome) ≤
        activeCapacity lower inst.literal.capacity +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
                inst.selectedCutoffVector) value
            ∂eta := by
    calc
      eventMass outcomeLaw (fun outcome => lowerChoice outcome ∨ upperAffordance outcome) ≤
          eventMass outcomeLaw lowerChoice + eventMass outcomeLaw upperAffordance :=
        by
          unfold eventMass AppliedModelingLib.measureProb
          exact measureReal_union_le _ _
      _ = activeCapacity lower inst.literal.capacity +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
                inst.selectedCutoffVector) value
            ∂eta := by rw [hlower_capacity, hupper_affordance]
  calc
    eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ region ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        eventMass outcomeLaw
          (fun outcome => lowerChoice outcome ∨ upperAffordance outcome) := by
      simpa [outcomeLaw, active] using (eventMass_mono outcomeLaw hsplit)
    _ ≤ activeCapacity lower inst.literal.capacity +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
                inst.selectedCutoffVector) value
            ∂eta := hresult
    _ = activeCapacity
          (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
            inst.selectedCutoffVector pivot)
          inst.literal.capacity +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  inst.selectedCutoffVector pivot)
                value inst.selectedCutoffVector) value
            ∂eta := by
      rfl

/--
The Case 2 ranked-prefix split on the literal selected cutoff.  The prefix
capacity estimate follows from its canonical rank bound and literal capacity
regularity; no block choice-mass equality is accepted as an input.
-/
theorem theorem1_selected_low_matched_mass_le_rankPrefix_components
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    [IsProbabilityMeasure noiseLaw]
    {beta gamma : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C)
    (halpha_nonneg : 0 ≤ alpha)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ region ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        ∫ value : ℝ,
          region.indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1)))
                inst.selectedCutoffVector
                (theorem3RankedCutoffNat C inst.selectedCutoffVector
                  (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
              value inst.selectedCutoffVector) value
          ∂eta := by
  let rankCut : ℕ := theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)
  have hprefix : rankCut ≤ C :=
    theorem1EarlyPrefixRank_le_marketIndex hbeta hgamma hC_pos
  have hsparse_nat :
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut)).card ≤ rankCut := by
    simpa [rankCut,
      theorem3RankedCutoffNat_eq_rankedCutoff C inst.selectedCutoffVector hprefix] using
      (theorem1CutoffBelowBlock_card_le_rank_start C rankCut
        inst.selectedCutoffVector hprefix)
  have hprefix_real : (rankCut : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    dsimp [rankCut]
    unfold theorem3EarlyPrefixRank
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hsparse_nat_real :
      ((theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut)).card : ℝ) ≤
        (rankCut : ℝ) := by
    exact_mod_cast hsparse_nat
  have hsparse_real :
      ((theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut)).card : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    exact hsparse_nat_real.trans hprefix_real
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_le_succ : (C : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ C
  have hregular_to_C : alpha / ((C + 1 : ℕ) : ℝ) ≤ alpha / (C : ℝ) :=
    div_le_div_of_nonneg_left halpha_nonneg hC_real_pos hC_le_succ
  have hcapacity : ∀ college ∈ (Finset.univ : Finset (Fin (C + 1))),
      inst.literal.capacity college ≤ alpha / (C : ℝ) := by
    intro college _
    exact (capacityRegular.le inst.capacity_regular college).trans hregular_to_C
  have hcomponents :=
    inst.theorem1_selected_low_matched_mass_le_lower_capacity_add_upper_affordance
      (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut) hregion
  have hcapacity_sparse :
      activeCapacity
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
          inst.selectedCutoffVector
          (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut))
        inst.literal.capacity ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    apply theorem1Tail_sparseBlock_capacity_le_alpha_rpow_neg_K
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut))
      inst.literal.capacity hC_real_pos halpha_nonneg hsparse_real
    intro college hcollege
    exact hcapacity college (Finset.mem_filter.mp hcollege).1
  calc
    eventMass
        (inst.studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ region ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        activeCapacity
          (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
            inst.selectedCutoffVector
            (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut))
          inst.literal.capacity +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  inst.selectedCutoffVector
                  (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut))
                value inst.selectedCutoffVector) value
            ∂eta := hcomponents
    _ ≤ alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  inst.selectedCutoffVector
                  (theorem3RankedCutoffNat C inst.selectedCutoffVector rankCut))
                value inst.selectedCutoffVector) value
            ∂eta := by
      gcongr
    _ = alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            region.indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  inst.selectedCutoffVector
                  (theorem3RankedCutoffNat C inst.selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value inst.selectedCutoffVector) value
            ∂eta := by
      rfl

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
