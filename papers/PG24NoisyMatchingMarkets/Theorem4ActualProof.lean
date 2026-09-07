import PG24NoisyMatchingMarkets.Theorem4IntegratedCapacity
import Mathlib.Tactic

/-!
# PG24 Theorem 4 source-model assembly

This module assembles the source's integrated capacity argument with the
semantic complement of the low-cutoff set.  Unlike the legacy suffix route,
it does not require college labels to be presorted: the large coalition is
defined by its cutoff property.
-/

open Filter
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u

/--
The integrated low-cutoff capacity certificate supplies the source-model
Theorem 4 coalition conclusion through the semantic non-low cutoff set.

The floor certificate is deliberately a separate input here.  The companion
integrated-capacity module derives it from the primitive long-tailed and
fixed-value-law assumptions; this assembly contains no pointwise
affordance-to-matching premise and no sorted-relabeling premise.
-/
theorem theorem4_coalition_amplification_from_integrated_capacity_nonLow
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply tol eps sigma vLow vHigh : ℝ}
    {lowerCutoff : ℕ → ℝ}
    (htol_pos : 0 < tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < (valueLaw C a).real (Set.Icc vLow vHigh))
    (houtcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (hchoice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_sum : source_assumption_total_capacity_sum Mseq totalSupply)
    (hvalue_probability : source_assumption_market_value_probability valueLaw)
    (hintegrated_affordance_event_bridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (hfloor :
      source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        totalSupply)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C - vHigh) ≤
            sigma / (((C + 1 : ℕ) : ℝ)) ) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability
                  (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have hselected_floor :
      source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        totalSupply :=
    source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply_of_market
      hfloor
  have hselected_integral :
      source_assumption_selected_stable_low_cutoff_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        totalSupply :=
    source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
      (source_assumption_market_value_finite_of_probability hvalue_probability)
      hselected_floor
  have hselected_bridge :
      source_assumption_selected_stable_integrated_affordance_event_bridge
        Mseq Iseq noiseLaw selected valueLaw cutoffOut OutcomeSeq outcomeLaw
        chosenCollege :=
    source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
      hintegrated_affordance_event_bridge
  have hcapacity_contradiction :
      source_assumption_selected_stable_low_cutoff_capacity_contradiction
        Mseq Iseq selected cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        OutcomeSeq outcomeLaw chosenCollege totalSupply :=
    source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
      hselected_integral hselected_bridge
  have hlow_count :
      source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff :=
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          houtcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        hchoice_mass_eq_aggregateDemand)
      hcapacity_clear hcapacity_sum hcapacity_contradiction
  have hclauses :=
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      (valueMass := fun C a S => (valueLaw C a).real S)
      Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlow_count
      hhigh_floor_le_sigma_div
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hmassC hcloseC a
  refine
    ⟨cutoffAffordanceProbability
        (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (nonLowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C))
        vLow
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)),
      nonLowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (lowerCutoff C),
      Set.Icc vLow vHigh, hlargeC a, hmassC a, ?_⟩
  intro v hvmem
  exact hcloseC a v hvmem

/--
The fixed-coalition-value-law Theorem 4 source model closes the integrated
capacity route.  It selects the regular interval and all analytic parameters
from the primitive source conditions; the only outcome-level input is the
integrated match/affordance semantics from the cutoff model.
-/
theorem theorem4_coalition_amplification_fixed_value_law_of_longTailed_integrated_capacity
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (eta : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure eta]
    (value_law_eq_eta :
      source_assumption_theorem4_value_law_eq_eta valueLaw eta)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply tol : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1)
    (houtcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (hchoice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_sum : source_assumption_total_capacity_sum Mseq totalSupply)
    (hintegrated_affordance_event_bridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability
                  (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hdelta_pos : 0 < tol / 2 := by
    linarith
  have hdelta_lt : tol / 2 < tol := by
    linarith
  rcases exists_regular_interval_measure_compl_le_of_probability eta hdelta_pos with
    ⟨vLow, vHigh, hv, heta_exception⟩
  rcases
      exists_theorem4_floor_pow_integral_capacity_certificate_at_vHigh_of_longTailed
        (Admissible := Admissible) Mseq noiseLaw hlong valueLaw eta
        value_law_eq_eta cutoffOut (vHigh := vHigh) htol_pos
        htotalSupply_lt_one with
    ⟨sigma, _valueFloor, hsigma_pos, _hvalueFloor_lt, hfloor⟩
  rcases exists_positive_epsilon_le_one_of_exp_error_lt htol_pos hsigma_pos with
    ⟨eps, heps_pos, heps_le_one, herror_lt⟩
  have hvalue_probability : source_assumption_market_value_probability valueLaw :=
    source_assumption_market_value_probability_of_theorem4_value_law_eq_eta
      eta value_law_eq_eta
  have hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := tol / 2) (vLow := vLow) (vHigh := vHigh) :=
    source_assumption_theorem4_regular_interval_measure_exception_bound_of_value_law_eq_eta
      eta value_law_eq_eta heta_exception
  have hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < (valueLaw C a).real (Set.Icc vLow vHigh) :=
    source_assumption_theorem4_regular_interval_mass_of_exception_bound
      (source_assumption_theorem4_regular_interval_exception_bound_of_measure
        hdelta_lt hvalue_probability hexception)
  exact
    theorem4_coalition_amplification_from_integrated_capacity_nonLow
      Mseq Iseq Kseq selected noiseLaw hlong cutoffOut valueLaw
      OutcomeSeq outcomeLaw chosenCollege htol_pos hmass houtcome_probability
      hchoice_mass_eq_aggregateDemand hcapacity_sum hvalue_probability
      hintegrated_affordance_event_bridge hfloor hv heps_pos heps_le_one
      hsigma_pos.le herror_lt
      (source_assumption_theorem4_high_tail_floor_rate_of_quantile_floor
        (Admissible := Admissible) noiseLaw hsigma_pos vHigh)

end PG24NoisyMatchingMarkets
