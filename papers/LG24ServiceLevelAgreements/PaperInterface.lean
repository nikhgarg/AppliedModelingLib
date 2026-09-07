import LG24ServiceLevelAgreements.SLA2026StationaryTailSLA
import LG24ServiceLevelAgreements.SLA2026RelativeCentralization
import Mathlib.Tactic

/-!
# Paper Interface: Redesigning Service Level Agreements

This is the compact review surface for the theory compiled by the private
Overleaf `main_msom.tex` revision `887a5ccdb076b6e811d8cbc34d3b0eed9b5bdb1a`.
It contains only source-facing model definitions, the five active named
propositions, and the displayed relative-centralization identity on which the
last proposition relies. Every `...Spec` definition states a paper result,
including its source-domain assumptions; the theorem with the same stem proves
that exact specification from primitive conditions.

The GPS response-tail estimate is proved from the literal selected-Palm,
remote-past GPS/FCFS construction.  Its response semantics, finite-replay
measurability, and tail inequality are all visible in the source-facing tail
contract below.  The legacy wrapper forest is retained separately in
`LegacyReviewSurface.lean` and is not imported here.
-/

namespace LG24ServiceLevelAgreements

open SLA2026BoroughQueueingInput
open scoped BigOperators

noncomputable section

/-! ## Source-facing model definitions -/

/-- `E(s) = C - sum s_{k,b}`. -/
abbrev paperExcessCapacity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (capacity : Real) (admitted : Category -> Borough -> Real) : Real :=
  sla2026ExcessCapacity capacity admitted

/-- The original fixed-load design-policy feasibility relation. -/
abbrev paperOriginalFixedLoadFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted delay : Category -> Borough -> Real) : Prop :=
  sla2026OriginalFixedLoadFeasible tail capacity admitted delay

/-- The tail-threshold-only reciprocal-capacity feasible set. -/
abbrev paperFixedLoadFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted delay : Category -> Borough -> Real) : Prop :=
  sla2026Feasible tail capacity admitted delay

/-- Per-request all-request burden `Cost_{k,b}(s,z)`. -/
abbrev paperCost
    {Category Borough : Type*}
    (arrival admitted priority noninspectionPenalty delay :
      Category -> Borough -> Real) : Category -> Borough -> Real :=
  sla2026Cost arrival admitted priority noninspectionPenalty delay

/-- Total all-request efficiency loss `G(s,z)`. -/
abbrev paperEfficiencyLoss
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category -> Borough -> Real) : Real :=
  sla2026Efficiency arrival admitted priority noninspectionPenalty delay

/-- Within-category geographic range loss `F(s,z)`. -/
abbrev paperEquityLoss
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category -> Borough -> Real) : Real :=
  sla2026Equity arrival admitted priority noninspectionPenalty delay

/-- The scalarized source objective `L_gamma`. -/
abbrev paperTradeoff
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (gamma : Real) (arrival admitted priority noninspectionPenalty delay :
      Category -> Borough -> Real) : Real :=
  sla2026Tradeoff gamma arrival admitted priority noninspectionPenalty delay

/-- The displayed Borough-efficient delay endpoint. -/
abbrev paperEfficientDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted priority : Category -> Borough -> Real) :
    Category -> Borough -> Real :=
  sla2026EfficientDelay tail capacity admitted priority

/-- The source's efficiency-best zero-disparity endpoint predicate. -/
abbrev paperEfficiencyBestEquitable
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (tail capacity : Real)
    (arrival admitted priority noninspectionPenalty delay :
      Category -> Borough -> Real) : Prop :=
  sla2026EfficiencyBestEquitable tail capacity arrival admitted priority
    noninspectionPenalty delay

/-- Capacity-share vector `q_{k,b}(z) = a / (E(s) z_{k,b})`. -/
abbrev paperCapacityShare
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted delay : Category -> Borough -> Real) :
    Category -> Borough -> Real :=
  sla2026CapacityShare tail capacity admitted delay

/-- Pearson chi-square divergence used in Proposition `costofequity`. -/
abbrev paperPearsonChiSquare
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (left right : Category -> Borough -> Real) : Real :=
  sla2026PearsonChiSquare left right

/-- Relative price of equity `G(s,z_eq) / G(s,z_eff) - 1`. -/
abbrev paperPriceOfEquity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty equitable efficient :
      Category -> Borough -> Real) : Real :=
  sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
    equitable efficient

/-- Fixed noninspection contribution to all-request efficiency loss. -/
abbrev paperFixedNoninspectionCost
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category -> Borough -> Real) : Real :=
  sla2026FixedNoninspectionCost arrival admitted priority noninspectionPenalty

/-- The city-budget reciprocal-capacity feasible set. -/
abbrev paperCityFeasible
    {Category : Type*} [Fintype Category]
    (tail excessCapacity : Real) (delay : Category -> Real) : Prop :=
  sla2026CityFeasible tail excessCapacity delay

/-- The city-budget total efficiency loss. -/
abbrev paperCityEfficiencyLoss
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real)
    (delay : Category -> Real) : Real :=
  sla2026CityEfficiency arrival admitted priority noninspectionPenalty delay

/-- The displayed city-efficient delay endpoint. -/
abbrev paperCityEfficientDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail excessCapacity : Real) (admitted priority : Category -> Borough -> Real) :
    Category -> Real :=
  sla2026CityEfficientDelay tail excessCapacity admitted priority

/-- Relative centralization gain
`1 - G_city(s,z_city) / G(s,z_eff)`. -/
abbrev paperRelativeCentralizationGain
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real)
    (boroughDelay : Category -> Borough -> Real) (cityDelay : Category -> Real) : Real :=
  sla2026RelativeCentralizationGain arrival admitted priority noninspectionPenalty
    boroughDelay cityDelay

/-- Source model vocabulary: the Borough-budget effective-load index
`A_eff(s) = sum_(k,b) sqrt(a * s_(k,b) * r_(k,b))`. -/
abbrev paperEffectiveLoad
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Real) (admitted priority : Category -> Borough -> Real) : Real :=
  sla2026EffectiveLoad tail admitted priority

/-- Source model vocabulary: the city-budget effective-load index
`A_city(s) = sum_k sqrt(a * sum_b s_(k,b) * r_(k,b))`. -/
abbrev paperCityEffectiveLoad
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Real) (admitted priority : Category -> Borough -> Real) : Real :=
  sla2026CityEffectiveLoad tail admitted priority

/-- The source condition for the capacity-scaling clause: fixed noninspection
burden is constant across Boroughs within each category. -/
abbrev paperCategorywiseFixedNoninspection
    {Category Borough : Type*}
    (arrival admitted priority noninspectionPenalty :
      Category -> Borough -> Real) : Prop :=
  sla2026CategorywiseFixedNoninspection arrival admitted priority noninspectionPenalty

/-- The source model conditions needed to interpret a tail display inside one
globally stationary SLA-class queue.  Positive SLA weights and strict total
admitted-load slack are the regularity conditions that make the paper's
"steady operation" language constructive for the full GPS replay.  The
displayed target margin remains a separate, target-local premise below.

The always-backlogged no-guarantee background work is not counted as an SLA
class in this condition: it consumes only residual capacity. -/
def paperGlobalSteadyGPSCondition
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real) : Prop :=
  0 <= capacity /\
    (forall k, 0 < weight k) /\
    (Finset.univ.sum weight <= 1) /\
    (Finset.univ.sum M.admittedRate < capacity)

/-- The displayed target-local GPS guaranteed-service margin
`s_k < C_b phi_k`.  It is distinct from global SLA-class stability and is
therefore a separate visible premise of the tail and SLA results. -/
def paperTargetGuaranteedSlack
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real) (target : Category) : Prop :=
  M.admittedRate target < capacity * weight target

/-- The source's typical-admitted-request stationary GPS response-tail
contract.  It packages the Borel selected-Palm response, its literal
remote-past GPS/FCFS semantics, and the printed exponential inequality. -/
def paperStationaryGPSResponseTail
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
    (hcondition : paperGlobalSteadyGPSCondition M capacity weight)
    (target : Category) (delay : Real) : Prop := by
  classical
  exact SLA2026StationaryGPSResponseTail M
    (SLA2026BoroughGPSParameters.ofAggregateSteady M capacity weight
      hcondition.1 hcondition.2.1 hcondition.2.2.1 hcondition.2.2.2)
    target delay

/-- The source's logarithmic sufficient SLA condition. -/
abbrev paperSufficientSLAConstraint := sla2026SufficientSLAConstraint

/-- The source's displayed all-request response rate-fraction expression. -/
abbrev paperAllRequestResponseFraction := sla2026AllRequestResponseFraction

/-! ## Constructed GPS tail and SLA consequence -/

/-- The source's exponential tail display for the constructed typical
admitted request.  The source's target-local guaranteed-rate margin is kept
separate from the global steady-queue condition, and the SLA threshold is
nonnegative as required by the displayed response-tail inequality. -/
def paper_stationary_gps_response_tailSpec
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
  (target : Category) (delay : Real) : Prop :=
  forall hcondition : paperGlobalSteadyGPSCondition M capacity weight,
    paperTargetGuaranteedSlack M capacity weight target ->
      0 <= delay ->
      paperStationaryGPSResponseTail M capacity weight hcondition target delay

/-- Evidence for the source's stationary ideal-fluid GPS/FCFS tail display.
No cited-tail proposition, response certificate, or replay witness is a
premise of this result. -/
theorem paper_stationary_gps_response_tail
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
    (target : Category) (delay : Real) :
    paper_stationary_gps_response_tailSpec M capacity weight target delay := by
  classical
  intro hcondition htarget hdelay
  exact stationaryGPSResponseTail_of_physicalSourceStabilization
    M (SLA2026BoroughGPSParameters.ofAggregateSteady M capacity weight
      hcondition.1 hcondition.2.1 hcondition.2.2.1 hcondition.2.2.2)
      target delay htarget hdelay

/-- The source's displayed all-request SLA rate-fraction conclusion, derived
from the internally constructed selected-Palm tail.  It records the source's
`alpha in (0,1)` domain and the displayed logarithmic sufficient constraint. -/
def paper_sla_from_stationary_gps_tailSpec
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
  (target : Category) (delay alpha : Real) : Prop :=
  letI : DecidableEq Category := Classical.decEq Category
  forall hcondition : paperGlobalSteadyGPSCondition M capacity weight,
    paperTargetGuaranteedSlack M capacity weight target ->
      0 <= delay ->
        0 < alpha -> alpha < 1 ->
        paperSufficientSLAConstraint
          (capacity * weight target - M.admittedRate target) delay alpha ->
        M.admittedRate target / M.arrivalRate target * (1 - alpha) <=
          paperAllRequestResponseFraction
            (M.arrivalRate target) (M.admittedRate target)
            ((M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag.real
              {z | delay < selectedPalmTaggedGPSFCFSRemotePastResponse M
                (SLA2026BoroughGPSParameters.ofAggregateSteady M capacity weight
                  hcondition.1 hcondition.2.1 hcondition.2.2.1 hcondition.2.2.2)
                target z})

/-- Checked source-level all-request SLA rate-fraction consequence of the
constructed stationary GPS response tail. -/
theorem paper_sla_from_stationary_gps_tail
    {Category : Type*} [Fintype Category]
    (M : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
    (target : Category) (delay alpha : Real) :
    paper_sla_from_stationary_gps_tailSpec M capacity weight target delay alpha := by
  classical
  intro hcondition htarget hdelay halpha _halpha_lt hsla
  exact sla2026_stationary_gps_tail_implies_all_request_sla
    M (SLA2026BoroughGPSParameters.ofAggregateSteady M capacity weight
      hcondition.1 hcondition.2.1 hcondition.2.2.1 hcondition.2.2.2)
      target delay alpha
    (stationaryGPSResponseTail_of_physicalSourceStabilization
      M (SLA2026BoroughGPSParameters.ofAggregateSteady M capacity weight
        hcondition.1 hcondition.2.1 hcondition.2.2.1 hcondition.2.2.2)
        target delay htarget hdelay)
    halpha hsla

/-! ## Proposition `opt-reformulation` -/

/-- Exact optimization-level reading of the equivalent reciprocal-capacity
representation.  It is stronger than the source's convex-loss version because
the feasible threshold sets agree for every loss. -/
def paper_prop_opt_reformulationSpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category]
    (a capacity : Real) (admitted : Category -> Borough -> Real)
    (loss : (Category -> Borough -> Real) -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 <= admitted k b) ->
    0 < paperExcessCapacity capacity admitted ->
    forall delay,
      AppliedModelingLib.Optimization.IsMinimizerOn
        (paperOriginalFixedLoadFeasible a capacity admitted) loss delay <->
      AppliedModelingLib.Optimization.IsMinimizerOn
        (paperFixedLoadFeasible a capacity admitted) loss delay

/-- Evidence for Proposition `opt-reformulation`. -/
theorem paper_prop_opt_reformulation
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category]
    (a capacity : Real) (admitted : Category -> Borough -> Real)
    (loss : (Category -> Borough -> Real) -> Real) :
    paper_prop_opt_reformulationSpec a capacity admitted loss := by
  intro ha hadmitted _hexcess delay
  exact sla2026_original_fixed_load_minimizer_iff loss ha hadmitted

/-! ## Proposition `extremeeff` -/

def paper_prop_extreme_efficiencySpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    (AppliedModelingLib.Optimization.IsMinimizerOn
        (paperFixedLoadFeasible a capacity admitted)
        (paperTradeoff 1 arrival admitted priority noninspectionPenalty)
        (paperEfficientDelay a capacity admitted priority) /\
      forall (delay : Category -> Borough -> Real),
        AppliedModelingLib.Optimization.IsMinimizerOn
          (paperFixedLoadFeasible a capacity admitted)
          (paperTradeoff 1 arrival admitted priority noninspectionPenalty)
          delay ->
        delay = paperEfficientDelay a capacity admitted priority)

/-- Evidence for Proposition `extremeeff`, including the source `gamma = 1`
objective rather than only its reduced efficiency subobjective. -/
theorem paper_prop_extreme_efficiency
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_prop_extreme_efficiencySpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  have hobjective :
      paperTradeoff 1 arrival admitted priority noninspectionPenalty =
        sla2026Efficiency arrival admitted priority noninspectionPenalty := by
    funext delay
    exact sla2026Tradeoff_one arrival admitted priority noninspectionPenalty delay
  constructor
  · rw [hobjective]
    exact sla2026_extreme_efficiency
      (tail := a) (capacity := capacity) (arrival := arrival)
      (admitted := admitted) (priority := priority)
      (noninspectionPenalty := noninspectionPenalty)
      ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  · intro delay hmin
    rw [hobjective] at hmin
    exact sla2026_extreme_efficiency_unique
      (tail := a) (capacity := capacity) (arrival := arrival)
      (admitted := admitted) (priority := priority)
      (noninspectionPenalty := noninspectionPenalty)
      ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hmin

/-! ## Proposition `extremefair` -/

def paper_prop_extreme_equitySpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    exists (delay : Category -> Borough -> Real) (level : Category -> Real),
      AppliedModelingLib.Optimization.IsMinimizerOn
        (paperFixedLoadFeasible a capacity admitted)
        (paperTradeoff 0 arrival admitted priority noninspectionPenalty) delay /\
      paperEfficiencyBestEquitable a capacity arrival admitted priority
        noninspectionPenalty delay /\
      forall k b, paperCost arrival admitted priority noninspectionPenalty
        delay k b = level k

/-- Evidence for Proposition `extremefair`: the constructed endpoint is both a
`gamma = 0` minimizer and the source's efficiency-best zero-disparity choice. -/
theorem paper_prop_extreme_equity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_prop_extreme_equitySpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  rcases sla2026_extreme_equity
      (tail := a) (capacity := capacity) (arrival := arrival)
      (admitted := admitted) (priority := priority)
      (noninspectionPenalty := noninspectionPenalty)
      ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess with
    ⟨delay, hbest, level, hlevel⟩
  refine ⟨delay, level, ?_, hbest, hlevel⟩
  constructor
  · exact hbest.1
  · intro other _hother
    have hnonneg : 0 <= sla2026Equity arrival admitted priority
        noninspectionPenalty other := by
      unfold sla2026Equity
      exact finiteAllRequestRangeObjective_nonneg _
    simpa [sla2026Tradeoff, hbest.2.1] using hnonneg

/-! ## Source-defined relative price nonnegativity -/

/-- The source defines the relative price of equity to be nonnegative before
the later named price proposition. Keep that source-context conclusion in a
separate specification rather than making it inherit every later clause. -/
def paper_relative_price_of_equity_nonnegativeSpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    forall (equitable : Category -> Borough -> Real),
      paperEfficiencyBestEquitable a capacity arrival admitted priority
        noninspectionPenalty equitable ->
      0 <= paperPriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (paperEfficientDelay a capacity admitted priority)

/-- Checked source-defined nonnegativity of relative price of equity. -/
theorem paper_relative_price_of_equity_nonnegative
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_relative_price_of_equity_nonnegativeSpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
    equitable hbest
  exact sla2026_relativePriceOfEquity_nonneg
    ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest

/-! ## Proposition `costofequity` -/

def paper_prop_price_of_equitySpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    ((forall (equitable : Category -> Borough -> Real),
      paperEfficiencyBestEquitable a capacity arrival admitted priority
        noninspectionPenalty equitable ->
      (paperPriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (paperEfficientDelay a capacity admitted priority) =
        paperEffectiveLoad a admitted priority ^ 2 /
            (paperExcessCapacity capacity admitted *
              paperEfficiencyLoss arrival admitted priority noninspectionPenalty
                (paperEfficientDelay a capacity admitted priority)) *
          paperPearsonChiSquare
            (paperCapacityShare a capacity admitted
              (paperEfficientDelay a capacity admitted priority))
            (paperCapacityShare a capacity admitted equitable) /\
        paperPriceOfEquity arrival admitted priority noninspectionPenalty
            equitable (paperEfficientDelay a capacity admitted priority) <=
          (1 / paperEfficiencyLoss arrival admitted priority noninspectionPenalty
            (paperEfficientDelay a capacity admitted priority)) *
            Finset.univ.sum (fun k => Finset.univ.sum (fun b => arrival k b *
              (finiteCategoryMaximum
                (paperCost arrival admitted priority noninspectionPenalty
                  (paperEfficientDelay a capacity admitted priority)) k -
                paperCost arrival admitted priority noninspectionPenalty
                  (paperEfficientDelay a capacity admitted priority) k b))) /\
        (paperPriceOfEquity arrival admitted priority noninspectionPenalty
            equitable (paperEfficientDelay a capacity admitted priority) = 0 <->
          paperCapacityShare a capacity admitted equitable =
            paperCapacityShare a capacity admitted
              (paperEfficientDelay a capacity admitted priority)) /\
        (paperCapacityShare a capacity admitted equitable =
            paperCapacityShare a capacity admitted
              (paperEfficientDelay a capacity admitted priority) <->
          exists (level : Category -> Real), forall k b,
            paperCost arrival admitted priority noninspectionPenalty
              (paperEfficientDelay a capacity admitted priority) k b = level k))) /\
    forall (capacity' : Real),
      (Finset.univ.sum (fun k => Finset.univ.sum (fun b => admitted k b))) < capacity ->
      capacity < capacity' ->
      paperCategorywiseFixedNoninspection arrival admitted priority
        noninspectionPenalty ->
      ((0 < paperFixedNoninspectionCost arrival admitted priority
        noninspectionPenalty ->
        (paperExcessCapacity capacity admitted /
          paperExcessCapacity capacity' admitted) *
          (paperEfficiencyLoss arrival admitted priority noninspectionPenalty
            (paperEfficientDelay a capacity admitted priority) /
            paperEfficiencyLoss arrival admitted priority noninspectionPenalty
              (paperEfficientDelay a capacity' admitted priority)) < 1) /\
        (paperFixedNoninspectionCost arrival admitted priority
          noninspectionPenalty = 0 ->
          (paperExcessCapacity capacity admitted /
            paperExcessCapacity capacity' admitted) *
            (paperEfficiencyLoss arrival admitted priority noninspectionPenalty
              (paperEfficientDelay a capacity admitted priority) /
              paperEfficiencyLoss arrival admitted priority noninspectionPenalty
                (paperEfficientDelay a capacity' admitted priority)) = 1) /\
        forall (equitable equitable' : Category -> Borough -> Real),
          paperEfficiencyBestEquitable a capacity arrival admitted priority
            noninspectionPenalty equitable ->
          paperEfficiencyBestEquitable a capacity' arrival admitted priority
            noninspectionPenalty equitable' ->
          paperPriceOfEquity arrival admitted priority noninspectionPenalty
              equitable' (paperEfficientDelay a capacity' admitted priority) =
            (paperExcessCapacity capacity admitted /
              paperExcessCapacity capacity' admitted) *
              (paperEfficiencyLoss arrival admitted priority noninspectionPenalty
                (paperEfficientDelay a capacity admitted priority) /
                paperEfficiencyLoss arrival admitted priority noninspectionPenalty
                  (paperEfficientDelay a capacity' admitted priority)) *
              paperPriceOfEquity arrival admitted priority noninspectionPenalty
                equitable (paperEfficientDelay a capacity admitted priority)))

/-- Evidence for all clauses of Proposition `costofequity`, including its
capacity-scaling statement.  Capacity binding is derived in the proof layer,
not supplied as a hypothesis here. -/
theorem paper_prop_price_of_equity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_prop_price_of_equitySpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  refine ⟨?_, ?_⟩
  · intro equitable hbest
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact sla2026_relativePriceOfEquity_chi_square
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest
    · exact sla2026_relativePriceOfEquity_le_efficient_cost_range
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest
    · exact sla2026_relativePriceOfEquity_eq_zero_iff_capacityShare_eq
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest
    · exact
        (sla2026_relativePriceOfEquity_eq_zero_iff_capacityShare_eq
          ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest).symm.trans
          (sla2026_relativePriceOfEquity_eq_zero_iff_efficient_cost_constant
            ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest)
  · intro capacity' hbase hcapacityIncrease hfixed
    rcases hfixed with ⟨offset, hoffset⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hfixedPositive
      exact sla2026RelativePriceOfEquity_capacity_scaling_factor_lt_one
        (tail := a) (capacity := capacity) (capacity' := capacity')
        (arrival := arrival) (admitted := admitted) (priority := priority)
        (noninspectionPenalty := noninspectionPenalty)
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty
          hbase hcapacityIncrease hfixedPositive
    · intro hfixedZero
      exact sla2026RelativePriceOfEquity_capacity_scaling_factor_eq_one
        (tail := a) (capacity := capacity) (capacity' := capacity')
        (arrival := arrival) (admitted := admitted) (priority := priority)
        (noninspectionPenalty := noninspectionPenalty)
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty
          hbase hcapacityIncrease hfixedZero
    · intro equitable equitable' hbest hbest'
      exact sla2026RelativePriceOfEquity_capacity_scale_of_efficiencyBestEquitable
        (tail := a) (capacity := capacity) (capacity' := capacity')
        (arrival := arrival) (admitted := admitted) (priority := priority)
        (noninspectionPenalty := noninspectionPenalty)
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty
          hbase hcapacityIncrease hoffset hbest hbest'

/-! ## Displayed relative-centralization identity -/

/-- Source-context optimizer for the city-budget program.  The manuscript
introduces `z_city` as an optimizer before the following displayed identity
and before the later proposition's two-Borough premise, so its review surface
must not inherit that stronger cardinality condition. -/
def paper_city_extreme_efficiencySpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    AppliedModelingLib.Optimization.IsMinimizerOn
      (paperCityFeasible a (paperExcessCapacity capacity admitted))
      (paperCityEfficiencyLoss arrival admitted priority noninspectionPenalty)
      (paperCityEfficientDelay a (paperExcessCapacity capacity admitted)
        admitted priority)

/-- Checked city-budget optimum used by the source's `z_city` notation. -/
theorem paper_city_extreme_efficiency
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_city_extreme_efficiencySpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  exact sla2026_city_extreme_efficiency
    (tail := a) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess

/-- The relative centralization-gain equation displayed immediately before the
named centralization proposition. Its source location has no two-Borough
restriction, so this specification intentionally requires only nonempty finite
index types. -/
def paper_relative_centralization_gain_identitySpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    paperRelativeCentralizationGain arrival admitted priority noninspectionPenalty
      (paperEfficientDelay a capacity admitted priority)
      (paperCityEfficientDelay a (paperExcessCapacity capacity admitted)
        admitted priority) =
      (paperEffectiveLoad a admitted priority ^ 2 -
        paperCityEffectiveLoad a admitted priority ^ 2) /
        (paperExcessCapacity capacity admitted *
          paperEfficiencyLoss arrival admitted priority noninspectionPenalty
            (paperEfficientDelay a capacity admitted priority))

/-- Evidence for the displayed relative centralization-gain identity. -/
theorem paper_relative_centralization_gain_identity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_relative_centralization_gain_identitySpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  exact sla2026_relativeCentralizationGain_eq
    (tail := a) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess

/-! ## Proposition `strict_improvements_from_centralization` -/

def paper_prop_centralizationSpec
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough] [Nontrivial Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) : Prop :=
  0 < a ->
    (forall k b, 0 < arrival k b) ->
    (forall k b, 0 < admitted k b) ->
    (forall k b, admitted k b <= arrival k b) ->
    (forall k b, 0 < priority k b) ->
    (forall k b, 0 <= noninspectionPenalty k b) ->
    0 < paperExcessCapacity capacity admitted ->
    ((forall k b,
        paperCityEfficientDelay a (paperExcessCapacity capacity admitted)
          admitted priority k <
        paperEfficientDelay a capacity admitted priority k b) /\
      forall (equitable : Category -> Borough -> Real),
        paperEfficiencyBestEquitable a capacity arrival admitted priority
          noninspectionPenalty equitable ->
        (paperRelativeCentralizationGain arrival admitted priority noninspectionPenalty
            (paperEfficientDelay a capacity admitted priority)
            (paperCityEfficientDelay a (paperExcessCapacity capacity admitted)
              admitted priority) >=
            paperPriceOfEquity arrival admitted priority noninspectionPenalty
              equitable (paperEfficientDelay a capacity admitted priority) <->
          1 - paperCityEffectiveLoad a admitted priority ^ 2 /
            paperEffectiveLoad a admitted priority ^ 2 >=
          paperPearsonChiSquare
              (paperCapacityShare a capacity admitted
                (paperEfficientDelay a capacity admitted priority))
              (paperCapacityShare a capacity admitted equitable)))

/-- Evidence for Proposition `strict_improvements_from_centralization`. -/
theorem paper_prop_centralization
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough] [Nontrivial Borough]
    (a capacity : Real)
    (arrival admitted priority noninspectionPenalty : Category -> Borough -> Real) :
    paper_prop_centralizationSpec a capacity arrival admitted priority
      noninspectionPenalty := by
  intro ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess
  refine ⟨?_, ?_⟩
  · intro k b
    exact sla2026_city_sla_strictly_shorter
      (tail := a) (capacity := capacity) (admitted := admitted)
      (priority := priority) ha hadmitted hpriority hexcess k b
  · intro equitable hbest
    exact sla2026_relativeCentralizationGain_ge_relativePrice_comparison
        (tail := a) (capacity := capacity) (arrival := arrival)
        (admitted := admitted) (priority := priority)
        (noninspectionPenalty := noninspectionPenalty)
        ha harrival hadmitted hadmitted_le_arrival hpriority hpenalty hexcess hbest

end

end LG24ServiceLevelAgreements
