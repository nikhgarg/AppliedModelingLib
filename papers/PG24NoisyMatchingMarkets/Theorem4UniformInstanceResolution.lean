import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionAEMatchSemantics
import PG24NoisyMatchingMarkets.Theorem4UniformCapacityCertificate
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Uniform Instance Resolution

This module keeps the extended theorem's quantifier order explicit.  The
eventual threshold is chosen before an arbitrary finite broader market and an
arbitrary outcome carrier are supplied.
-/

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
One selected stable extended-model coalition instance.  The market's student
carrier is exactly `Outcome`; consequently the demand used in the capacity
argument is literally `market.demandAt`, rather than an unrelated external
choice function.

`matchingChoice` is the explicit source-model adapter from the selected
matching to that cutoff demand.  The generic cutoff interface alone only says
that a matching is represented by a cutoff, so this field records the semantic
identification required for the paper's `p_mu` notation.
-/
structure PG24ExtendedCoalitionStableInstance
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply : ℝ)
    (Outcome : Type u) [MeasurableSpace Outcome]
    (GlobalCollege : Type v) [Fintype GlobalCollege] where
  market : CutoffMarket.{u, v, w, x} Outcome GlobalCollege
  supplyDemand : SupplyDemandInterface market
  clearingCapacity : MarketClearingCapacityInterface market
  selected : { μ : market.Matching // market.Stable μ }
  outcomeLaw : market.Cutoff → Measure Outcome
  outcomeLaw_finite : ∀ P : market.Cutoff, IsFiniteMeasure (outcomeLaw P)
  choiceMass_eq_aggregateDemand :
    ∀ P : market.Cutoff, market.MarketClearing P →
      choiceMass (outcomeLaw P) (market.demandAt P)
          (Finset.univ : Finset GlobalCollege) =
        ∑ c : GlobalCollege, market.aggregateDemand P c
  totalCapacity_eq :
    (∑ c : GlobalCollege, market.capacity c) = totalSupply
  cutoffCoordinates : market.Cutoff → GlobalCollege → ℝ
  globalScore : market.Cutoff → Outcome → GlobalCollege → ℝ
  coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege
  localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ)
  localCoordinates_measurable : Measurable localCoordinates
  localCoordinates_map :
    Measure.map localCoordinates
        (outcomeLaw
          (supplyDemand.marketClearingCutoffOfStable
            (μ := selected.1) selected.2)) =
      eta.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
  coalition_score_ae :
    ∀ᵐ outcome ∂outcomeLaw
        (supplyDemand.marketClearingCutoffOfStable
          (μ := selected.1) selected.2),
      ∀ c : Fin (C + 1),
        globalScore
            (supplyDemand.marketClearingCutoffOfStable
              (μ := selected.1) selected.2)
            outcome (coalitionEmbedding c) =
          (localCoordinates outcome).1 + (localCoordinates outcome).2 c
  demand_none_iff_no_global_cutoff_crossing :
    ∀ outcome : Outcome,
      market.demandAt
          (supplyDemand.marketClearingCutoffOfStable
            (μ := selected.1) selected.2) outcome = none ↔
        ¬ cutoffCrossed
            (globalScore
              (supplyDemand.marketClearingCutoffOfStable
                (μ := selected.1) selected.2) outcome)
            (cutoffCoordinates
              (supplyDemand.marketClearingCutoffOfStable
                (μ := selected.1) selected.2))
  matchingChoice : market.Matching → Outcome → Option GlobalCollege
  selected_matchingChoice_eq_demandAt :
    ∀ outcome : Outcome,
      matchingChoice selected.1 outcome =
        market.demandAt
          (supplyDemand.marketClearingCutoffOfStable
            (μ := selected.1) selected.2) outcome

namespace PG24ExtendedCoalitionStableInstance

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {Outcome : Type u} [MeasurableSpace Outcome]
variable {GlobalCollege : Type v} [Fintype GlobalCollege]

/-- The selected stable matching's canonical clearing cutoff. -/
noncomputable def selectedCutoff
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege) : inst.market.Cutoff :=
  inst.supplyDemand.marketClearingCutoffOfStable
    (μ := inst.selected.1) inst.selected.2

/-- The canonical selected cutoff is market clearing. -/
theorem selectedCutoff_marketClearing
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege) :
    inst.market.MarketClearing inst.selectedCutoff :=
  inst.supplyDemand.marketClearingCutoffOfStable_marketClearing
    inst.selected.2

/-- The canonical selected cutoff represents the chosen stable matching. -/
theorem selectedCutoff_represents
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege) :
    inst.market.RepresentedByCutoff inst.selected.1
      inst.selectedCutoff :=
  inst.supplyDemand.marketClearingCutoffOfStable_represents
    inst.selected.2

/-- The local coalition cutoff vector inherited from the selected global cutoff. -/
noncomputable def localCutoff
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege) : Fin (C + 1) → ℝ :=
  coalitionCutoffRestriction inst.coalitionEmbedding
    inst.cutoffCoordinates inst.selectedCutoff

/-- The extended source's `p_mu(v,C')` at the selected stable cutoff. -/
noncomputable def pMu
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege)
    (value : ℝ) (active : Finset (Fin (C + 1))) : ℝ :=
  cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value
    inst.localCutoff

/-- The selected matching's source choice rule is exactly cutoff demand. -/
theorem selected_matchingChoice_eq_demandAt_selectedCutoff
    (inst :
      PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
        Outcome GlobalCollege) (outcome : Outcome) :
    inst.matchingChoice inst.selected.1 outcome =
      inst.market.demandAt inst.selectedCutoff outcome :=
  inst.selected_matchingChoice_eq_demandAt outcome

end PG24ExtendedCoalitionStableInstance

/--
The uniform capacity certificate applied to one arbitrary extended-model
instance.  Neither the global-college carrier nor the outcome carrier was
fixed when `sigma` and `valueFloor` were selected.
-/
theorem exists_eventually_theorem4_extended_instance_low_cutoff_count_of_longTailed
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ (Outcome : Type u) [MeasurableSpace Outcome]
            (GlobalCollege : Type v) [Fintype GlobalCollege]
            (inst :
              PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
                Outcome GlobalCollege),
            (lowCutoffIndexSet inst.localCutoff
              (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
                epsilonFloorSplitIndex (tol / 2) C := by
  rcases
      exists_theorem4_uniform_low_cutoff_integral_capacity_certificate_at_vHigh_of_longTailed
        noiseLaw hlong eta htol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, huniform⟩
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  filter_upwards [huniform] with C huniformC
  intro Outcome _ GlobalCollege _ inst
  let P : inst.market.Cutoff := inst.selectedCutoff
  let localCutoff : Fin (C + 1) → ℝ := inst.localCutoff
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet localCutoff
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C)
  letI : IsFiniteMeasure (inst.outcomeLaw P) :=
    inst.outcomeLaw_finite P
  have hintegrated :
      epsilonFloorSplitIndex (tol / 2) C < active.card →
        totalSupply <
          ∫ value : ℝ,
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              active value localCutoff ∂eta := by
    intro htoo_many
    simpa [active, cutoffAffordanceProbability] using
      (huniformC localCutoff (by simpa [active] using htoo_many))
  have haffordance_matched :
      ∀ᵐ outcome ∂inst.outcomeLaw P,
        theorem4CoalitionAffordanceEvent active localCutoff
            (inst.localCoordinates outcome) →
          chosenInActive (inst.market.demandAt P)
            (Finset.univ : Finset GlobalCollege) outcome := by
    simpa [P, localCutoff] using
      (theorem4_local_affordance_implies_global_match_ae_of_unmatched_iff_no_global_affordance
        (outcomeLaw := inst.outcomeLaw P)
        inst.coalitionEmbedding (inst.cutoffCoordinates P)
        (inst.globalScore P) (inst.market.demandAt P)
        inst.localCoordinates (by simpa [P] using inst.coalition_score_ae)
        (by simpa [P] using
          inst.demand_none_iff_no_global_cutoff_crossing)
        active localCutoff (fun _ => rfl))
  have hbridge :
      ∃ event : Outcome → Prop,
        (∫ value : ℝ,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active value localCutoff ∂eta) ≤
          eventMass (inst.outcomeLaw P) event ∧
          (∀ᵐ outcome ∂inst.outcomeLaw P, event outcome →
            chosenInActive (inst.market.demandAt P)
              (Finset.univ : Finset GlobalCollege) outcome) := by
    simpa [P, localCutoff, cutoffAffordanceProbability] using
      (theorem4_integrated_coalition_affordance_global_match_witness_ae
        eta noiseLaw (inst.outcomeLaw P) (inst.market.demandAt P)
        inst.localCoordinates inst.localCoordinates_measurable
        (by simpa [P] using inst.localCoordinates_map)
        active localCutoff haffordance_matched)
  have hcount :=
    theorem4_localLowCutoff_card_le_of_global_integrated_capacity_ae
      inst.supplyDemand inst.clearingCapacity inst.selected
      inst.coalitionEmbedding inst.cutoffCoordinates noiseLaw eta
      inst.outcomeLaw inst.market.demandAt
      (floor := vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (totalSupply := totalSupply)
      (splitIndex := epsilonFloorSplitIndex (tol / 2) C)
      inst.outcomeLaw_finite inst.choiceMass_eq_aggregateDemand
      inst.totalCapacity_eq (by
        simpa [P, localCutoff, active] using hintegrated) (by
        simpa [P, localCutoff, active] using hbridge)
  simpa [P, localCutoff, active] using hcount

/--
The long-tail endpoint comparison in a carrier-independent form.  The
quantification is over every local cutoff block satisfying the source's
high-value tail bound, rather than over one preselected sequence of blocks.
-/
theorem eventually_uniform_cutoffAffordance_endpoint_gap_of_longTailed
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {vLow vHigh endpointEpsilon sigma : ℝ}
    (hv : vLow < vHigh) (hendpointEpsilon_pos : 0 < endpointEpsilon)
    (hendpointEpsilon_le_one : endpointEpsilon ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma) :
    ∀ᶠ C : ℕ in atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        ∀ active : Finset (Fin (C + 1)),
          (∀ c ∈ active,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff c - vHigh) ≤ sigma / ((C + 1 : ℕ) : ℝ)) →
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                active vHigh cutoff -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                active vLow cutoff ≤
              1 - Real.exp (-(2 * endpointEpsilon * sigma)) := by
  let Block : ℕ → Type := fun C =>
    { data : (Fin (C + 1) → ℝ) × Finset (Fin (C + 1)) //
      ∀ c ∈ data.2,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (data.1 c - vHigh) ≤ sigma / ((C + 1 : ℕ) : ℝ) }
  let blockActive : ∀ C : ℕ, Block C → Finset (Fin (C + 1)) :=
    fun _ data => data.1.2
  let blockCutoff : ∀ C : ℕ, Block C → Fin (C + 1) → ℝ :=
    fun _ data => data.1.1
  have hhigh_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ block : Block C, ∀ c ∈ blockActive C block,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (blockCutoff C block c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) :=
    Filter.Eventually.of_forall (fun _ block c hc => block.2 c hc)
  have hgap :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      noiseLaw hlong (active := blockActive) (cutoff := blockCutoff)
      hv hendpointEpsilon_pos hendpointEpsilon_le_one hsigma_nonneg hhigh_bound
  filter_upwards [hgap] with C hgapC cutoff active hbound
  let block : Block C := ⟨(cutoff, active), hbound⟩
  have hhigh :=
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw active vHigh cutoff
  have hlow :=
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw active vLow cutoff
  rw [hhigh, hlow]
  simpa [block, blockActive, blockCutoff] using hgapC block

/--
The extended source conclusion at its actual quantifier boundary.  For a
given tolerance, the threshold `N` is chosen before the broader finite market,
outcome space, and selected stable instance are supplied.  The output
probability is the source `p_mu(v,C')` at that instance's selected cutoff.
-/
theorem theorem4_extended_coalition_amplification_pMu_uniform_of_longTailed
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (Outcome : Type u) [MeasurableSpace Outcome]
          (GlobalCollege : Type v) [Fintype GlobalCollege]
          (inst :
            PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
              Outcome GlobalCollege),
          ∃ effectiveSupply : ℝ,
          ∃ largeSubset : Finset (Fin (C + 1)),
          ∃ regularSet : Set ℝ,
            CoalitionLargeSubset
                (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
              eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |inst.pMu value largeSubset - effectiveSupply| < epsilon) := by
  intro epsilon hepsilon_pos
  have hhalf_epsilon_pos : 0 < epsilon / 2 := by
    linarith
  rcases exists_regular_interval_measure_compl_le_of_probability
      eta hhalf_epsilon_pos with
    ⟨vLow, vHigh, hv, hregular_half⟩
  have hregular : eta.real (Set.Icc vLow vHigh)ᶜ ≤ epsilon := by
    linarith
  rcases
      exists_eventually_theorem4_extended_instance_low_cutoff_count_of_longTailed
        noiseLaw eta hlong
        (tol := epsilon) hepsilon_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hlow_count⟩
  rcases exists_positive_epsilon_le_one_of_exp_error_lt
      hepsilon_pos hsigma_pos with
    ⟨endpointEpsilon, hendpointEpsilon_pos, hendpointEpsilon_le_one,
      hendpoint_error_lt⟩
  have hendpoint_gap :=
    eventually_uniform_cutoffAffordance_endpoint_gap_of_longTailed
      noiseLaw hlong hv hendpointEpsilon_pos hendpointEpsilon_le_one
      hsigma_pos.le
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards
        [theorem4HighTailQuantile_upperTailMass_le_eventually
          noiseLaw hsigma_pos] with C htailC
    simpa only [add_sub_cancel_left] using htailC
  have heventual :
      ∀ᶠ C : ℕ in atTop,
        ∀ (Outcome : Type u) [MeasurableSpace Outcome]
          (GlobalCollege : Type v) [Fintype GlobalCollege]
          (inst :
            PG24ExtendedCoalitionStableInstance C noiseLaw eta totalSupply
              Outcome GlobalCollege),
          ∃ effectiveSupply : ℝ,
          ∃ largeSubset : Finset (Fin (C + 1)),
          ∃ regularSet : Set ℝ,
            CoalitionLargeSubset
                (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
              eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |inst.pMu value largeSubset - effectiveSupply| < epsilon) := by
    filter_upwards [hlow_count, hendpoint_gap, hquantile_tail] with
      C hlow_countC hendpoint_gapC hquantile_tailC
    intro Outcome _ GlobalCollege _ inst
    let localCutoff : Fin (C + 1) → ℝ := inst.localCutoff
    let floor : ℝ :=
      vHigh + theorem4HighTailQuantile noiseLaw sigma C
    let largeSubset : Finset (Fin (C + 1)) :=
      nonLowCutoffIndexSet localCutoff floor
    have hlarge :
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          largeSubset epsilon := by
      apply coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
        hepsilon_pos
      simpa [largeSubset, floor, localCutoff] using
        (hlow_countC Outcome GlobalCollege inst)
    have hhigh_tail_bound :
        ∀ c ∈ largeSubset,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (localCutoff c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
      intro c hc
      calc
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (localCutoff c - vHigh) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw (floor - vHigh) :=
          AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
            (sub_le_sub_right
              (floor_le_of_mem_nonLowCutoffIndexSet hc) vHigh)
        _ = AppliedModelingLib.Probability.upperTailMass noiseLaw
            ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh) := by
          congr 1
        _ ≤ sigma / ((C + 1 : ℕ) : ℝ) := hquantile_tailC
    have hendpoint :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset vHigh localCutoff -
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset vLow localCutoff ≤
          1 - Real.exp (-(2 * endpointEpsilon * sigma)) :=
      hendpoint_gapC localCutoff largeSubset hhigh_tail_bound
    refine ⟨inst.pMu vLow largeSubset, largeSubset, Set.Icc vLow vHigh,
      hlarge, hregular, ?_⟩
    intro value hvalue
    have hlow_value :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset vLow localCutoff ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset value localCutoff :=
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) hvalue.1
    have hvalue_high :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset value localCutoff ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            largeSubset vHigh localCutoff :=
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) hvalue.2
    have hdiff_nonneg :
        0 ≤ cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset value localCutoff -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vLow localCutoff :=
      sub_nonneg.mpr hlow_value
    have hdiff_le :
        cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset value localCutoff -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vLow localCutoff ≤
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vHigh localCutoff -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vLow localCutoff :=
      sub_le_sub_right hvalue_high _
    have hdiff_lt :
        cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset value localCutoff -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vLow localCutoff < epsilon :=
      lt_of_le_of_lt (le_trans hdiff_le hendpoint) hendpoint_error_lt
    simpa [PG24ExtendedCoalitionStableInstance.pMu, localCutoff] using
      (show |cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset value localCutoff -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              largeSubset vLow localCutoff| < epsilon by
        rw [abs_of_nonneg hdiff_nonneg]
        exact hdiff_lt)
  rcases Filter.eventually_atTop.1 heventual with ⟨N, hN⟩
  exact ⟨N, fun C hC => hN C hC⟩

end

end PG24NoisyMatchingMarkets
