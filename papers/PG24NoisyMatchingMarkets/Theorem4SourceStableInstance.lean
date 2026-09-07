import PG24NoisyMatchingMarkets.Theorem4SourceModelAdapter
import PG24NoisyMatchingMarkets.Theorem4ExplicitSelectedCapacityBridge
import PG24NoisyMatchingMarkets.Theorem4UniformCapacityCertificate
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Source-Native Stable Instances

This is the extended paper model at the selected stable matching.  In
particular, a matching is literally an outcome-to-college map, its selected
cutoff is explicit, and the iid coalition marginal is derived from source
sampling data rather than stored as an analytic conclusion.
-/

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
The cutoff-market data whose matching objects are actual assignment maps.

The source permits arbitrary preference behavior and arbitrary colleges outside
the coalition through `demandAt`; the only structure imposed here is the
cutoff characterization of its selected stable assignment.
-/
structure PG24SourceCutoffMarket
    (Outcome : Type u) (GlobalCollege : Type v) (Cutoff : Type w) where
  demandAt : Cutoff → Outcome → Option GlobalCollege
  aggregateDemand : Cutoff → GlobalCollege → ℝ
  capacity : GlobalCollege → ℝ
  isStable : (Outcome → Option GlobalCollege) → Prop
  marketClearing : Cutoff → Prop
  representedByCutoff : (Outcome → Option GlobalCollege) → Cutoff → Prop

namespace PG24SourceCutoffMarket

variable {Outcome : Type u} {GlobalCollege : Type v} {Cutoff : Type w}

/-- Forget only that source matchings are functions, exposing the shared API. -/
def toCutoffMarket
    (sourceMarket : PG24SourceCutoffMarket.{u, v, w}
      Outcome GlobalCollege Cutoff) :
    CutoffMarket Outcome GlobalCollege where
  Cutoff := Cutoff
  Matching := Outcome → Option GlobalCollege
  demandAt := sourceMarket.demandAt
  aggregateDemand := sourceMarket.aggregateDemand
  capacity := sourceMarket.capacity
  isStable := sourceMarket.isStable
  marketClearing := sourceMarket.marketClearing
  representedByCutoff := sourceMarket.representedByCutoff

@[simp] theorem toCutoffMarket_demandAt
    (sourceMarket : PG24SourceCutoffMarket.{u, v, w}
      Outcome GlobalCollege Cutoff) :
    sourceMarket.toCutoffMarket.demandAt = sourceMarket.demandAt :=
  rfl

@[simp] theorem toCutoffMarket_aggregateDemand
    (sourceMarket : PG24SourceCutoffMarket.{u, v, w}
      Outcome GlobalCollege Cutoff) :
    sourceMarket.toCutoffMarket.aggregateDemand = sourceMarket.aggregateDemand :=
  rfl

@[simp] theorem toCutoffMarket_capacity
    (sourceMarket : PG24SourceCutoffMarket.{u, v, w}
      Outcome GlobalCollege Cutoff) :
    sourceMarket.toCutoffMarket.capacity = sourceMarket.capacity :=
  rfl

end PG24SourceCutoffMarket

/--
One source-native extended economy, coalition, and selected stable matching.

The full `StudentType` coordinate may carry all true values, preferences, and
external random state.  Thus no independence or preference restriction is
imposed outside the coalition.  The selected matching itself is a function,
so the equality to cutoff demand is an equality of the actual source matching
rather than an auxiliary evaluator.
-/
structure PG24ExtendedCoalitionSourceStableInstance
    (C : ℕ) (noiseLaw eta : Measure ℝ) (totalSupply : ℝ)
    (StudentType : Type u) [MeasurableSpace StudentType]
    (Outcome : Type v) [MeasurableSpace Outcome]
    (GlobalCollege : Type w) [Fintype GlobalCollege]
    (Cutoff : Type x) where
  sourceMarket : PG24SourceCutoffMarket Outcome GlobalCollege Cutoff
  supplyDemand : SupplyDemandInterface sourceMarket.toCutoffMarket
  clearingCapacity : MarketClearingCapacityInterface sourceMarket.toCutoffMarket
  sampling : PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome
  selectedMatching : Outcome → Option GlobalCollege
  selectedStable : sourceMarket.isStable selectedMatching
  selectedCutoff : Cutoff
  selectedCutoff_marketClearing : sourceMarket.marketClearing selectedCutoff
  selectedCutoff_represents :
    sourceMarket.representedByCutoff selectedMatching selectedCutoff
  selectedMatching_eq_demandAt :
    ∀ outcome : Outcome,
      selectedMatching outcome = sourceMarket.demandAt selectedCutoff outcome
  selected_choiceMass_eq_aggregateDemand :
    choiceMass sampling.outcomeLaw selectedMatching
        (Finset.univ : Finset GlobalCollege) =
      ∑ c : GlobalCollege, sourceMarket.aggregateDemand selectedCutoff c
  totalCapacity_eq :
    (∑ c : GlobalCollege, sourceMarket.capacity c) = totalSupply
  cutoffCoordinates : Cutoff → GlobalCollege → ℝ
  globalScore : Cutoff → Outcome → GlobalCollege → ℝ
  coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege
  coalition_score_ae :
    ∀ᵐ outcome ∂sampling.outcomeLaw,
      ∀ c : Fin (C + 1),
        globalScore selectedCutoff outcome (coalitionEmbedding c) =
          (sampling.localCoordinates outcome).1 +
            (sampling.localCoordinates outcome).2 c
  demand_none_iff_no_global_cutoff_crossing :
    ∀ outcome : Outcome,
      sourceMarket.demandAt selectedCutoff outcome = none ↔
        ¬ cutoffCrossed (globalScore selectedCutoff outcome)
          (cutoffCoordinates selectedCutoff)

namespace PG24ExtendedCoalitionSourceStableInstance

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/-- The selected global cutoff restricted to the source coalition. -/
def localCutoff
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) : Fin (C + 1) → ℝ :=
  coalitionCutoffRestriction (M := inst.sourceMarket.toCutoffMarket)
    inst.coalitionEmbedding inst.cutoffCoordinates
    inst.selectedCutoff

/-- The source's selected-matching affordability probability `p_mu(v,C')`. -/
def pMu
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (value : ℝ) (active : Finset (Fin (C + 1))) : ℝ :=
  cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value
    inst.localCutoff

/-- The actual selected matching is represented by the explicit cutoff. -/
theorem selectedMatching_represents_selectedCutoff
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) :
    inst.sourceMarket.toCutoffMarket.RepresentedByCutoff
      inst.selectedMatching inst.selectedCutoff :=
  inst.selectedCutoff_represents

/-- The selected matching's actual assignment rule is selected-cutoff demand. -/
theorem selectedMatching_eq_demandAt_selectedCutoff
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff) (outcome : Outcome) :
    inst.selectedMatching outcome =
      inst.sourceMarket.toCutoffMarket.demandAt inst.selectedCutoff outcome :=
  inst.selectedMatching_eq_demandAt outcome

/-- The source sampling data supplies the analytic eta-by-iid local law. -/
theorem localCoordinates_map_eq_eta_prod_iid
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    [IsProbabilityMeasure noiseLaw] :
    Measure.map inst.sampling.localCoordinates inst.sampling.outcomeLaw =
      eta.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) :=
  PG24CoalitionSourceSampling.localCoordinates_map_eq_eta_prod_iid
    inst.sampling

/-- A local coalition crossing leads to a globally matched selected assignment. -/
theorem local_affordance_implies_selected_match_ae
    (inst :
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (active : Finset (Fin (C + 1))) :
    ∀ᵐ outcome ∂inst.sampling.outcomeLaw,
      theorem4CoalitionAffordanceEvent active inst.localCutoff
          (inst.sampling.localCoordinates outcome) →
        chosenInActive inst.selectedMatching
          (Finset.univ : Finset GlobalCollege) outcome := by
  have hdemand :=
    theorem4_local_affordance_implies_global_match_ae_of_unmatched_iff_no_global_affordance
      (outcomeLaw := inst.sampling.outcomeLaw)
      inst.coalitionEmbedding (inst.cutoffCoordinates inst.selectedCutoff)
      (inst.globalScore inst.selectedCutoff)
      (inst.sourceMarket.demandAt inst.selectedCutoff)
      inst.sampling.localCoordinates inst.coalition_score_ae
      inst.demand_none_iff_no_global_cutoff_crossing active inst.localCutoff
      (fun _ => by simp [localCutoff, coalitionCutoffRestriction])
  filter_upwards [hdemand] with outcome houtcome hlocal
  rcases houtcome hlocal with ⟨college, hcollege, hdemand_eq⟩
  exact ⟨college, hcollege, by
    rw [inst.selectedMatching_eq_demandAt]
    exact hdemand_eq⟩

/--
The uniform capacity certificate at an arbitrary source-native extended
instance.  The eventual threshold is selected before the source state type,
outcome carrier, broader market, and selected stable matching are supplied.
-/
theorem exists_eventually_theorem4_source_instance_low_cutoff_count_of_longTailed
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ (StudentType : Type u) [MeasurableSpace StudentType]
            (Outcome : Type v) [MeasurableSpace Outcome]
            (GlobalCollege : Type w) [Fintype GlobalCollege]
            (Cutoff : Type x)
            (inst :
              PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
                StudentType Outcome GlobalCollege Cutoff),
            (lowCutoffIndexSet inst.localCutoff
              (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
                epsilonFloorSplitIndex (tol / 2) C := by
  rcases
      exists_theorem4_uniform_low_cutoff_integral_capacity_certificate_at_vHigh_of_longTailed
        noiseLaw hlong eta htol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, huniform⟩
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  filter_upwards [huniform] with C huniformC
  intro StudentType _ Outcome _ GlobalCollege _ Cutoff inst
  let P : Cutoff := inst.selectedCutoff
  let localCutoff : Fin (C + 1) → ℝ := inst.localCutoff
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet localCutoff
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C)
  letI : IsProbabilityMeasure inst.sampling.outcomeLaw :=
    inst.sampling.outcomeLaw_isProbability
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
      ∀ᵐ outcome ∂inst.sampling.outcomeLaw,
        theorem4CoalitionAffordanceEvent active localCutoff
            (inst.sampling.localCoordinates outcome) →
          chosenInActive inst.selectedMatching
            (Finset.univ : Finset GlobalCollege) outcome := by
    simpa [localCutoff] using
      (inst.local_affordance_implies_selected_match_ae active)
  have hbridge :
      ∃ event : Outcome → Prop,
        (∫ value : ℝ,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active value localCutoff ∂eta) ≤
          eventMass inst.sampling.outcomeLaw event ∧
        (∀ᵐ outcome ∂inst.sampling.outcomeLaw, event outcome →
          chosenInActive inst.selectedMatching
            (Finset.univ : Finset GlobalCollege) outcome) := by
    simpa [localCutoff, cutoffAffordanceProbability] using
      (theorem4_integrated_coalition_affordance_global_match_witness_ae
        eta noiseLaw inst.sampling.outcomeLaw inst.selectedMatching
        inst.sampling.localCoordinates
        (PG24CoalitionSourceSampling.localCoordinates_measurable inst.sampling)
        inst.localCoordinates_map_eq_eta_prod_iid active localCutoff
        haffordance_matched)
  have hcount :=
    theorem4_localLowCutoff_card_le_of_explicit_integrated_capacity_ae
      (M := inst.sourceMarket.toCutoffMarket)
      inst.clearingCapacity inst.selectedCutoff_marketClearing
      inst.coalitionEmbedding inst.cutoffCoordinates noiseLaw eta
      inst.sampling.outcomeLaw inst.selectedMatching
      (floor := vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (totalSupply := totalSupply)
      (splitIndex := epsilonFloorSplitIndex (tol / 2) C)
      inst.selected_choiceMass_eq_aggregateDemand inst.totalCapacity_eq
      (by simpa [P, localCutoff, active] using hintegrated)
      (by simpa [P, localCutoff, active] using hbridge)
  simpa [P, localCutoff, active] using hcount

/--
The long-tail endpoint comparison over every finite local cutoff block.  This
certificate has no market or source-instance parameters, so it can be
combined with the post-threshold arbitrary-instance quantifier directly.
-/
theorem eventually_theorem4_carrier_independent_endpoint_gap_of_longTailed
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
PG24 Theorem 4 at the source model's quantifier boundary.  The threshold is
chosen before an arbitrary rich student state space, outcome space, broader
market, cutoff type, and selected stable matching are supplied.
-/
theorem theorem4_source_native_coalition_amplification_pMu_uniform_of_longTailed
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (inst :
            PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
              StudentType Outcome GlobalCollege Cutoff),
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
      exists_eventually_theorem4_source_instance_low_cutoff_count_of_longTailed
        noiseLaw eta hlong
        (tol := epsilon) hepsilon_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hlow_count⟩
  rcases exists_positive_epsilon_le_one_of_exp_error_lt
      hepsilon_pos hsigma_pos with
    ⟨endpointEpsilon, hendpointEpsilon_pos, hendpointEpsilon_le_one,
      hendpoint_error_lt⟩
  have hendpoint_gap :=
    eventually_theorem4_carrier_independent_endpoint_gap_of_longTailed
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
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (inst :
            PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
              StudentType Outcome GlobalCollege Cutoff),
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
    intro StudentType _ Outcome _ GlobalCollege _ Cutoff inst
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
        (hlow_countC StudentType Outcome GlobalCollege Cutoff inst)
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
    simpa [pMu, localCutoff] using
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

end PG24ExtendedCoalitionSourceStableInstance

end

end PG24NoisyMatchingMarkets
