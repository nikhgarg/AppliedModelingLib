import LG24ServiceLevelAgreements.CurrentDraftAlgebra
import LG24ServiceLevelAgreements.ProposedFixedLoad
import LG24ServiceLevelAgreements.ProposedPooling

/-!
# Paper-Facing Theorems: Redesigning Service Level Agreements

This is the first implementation ledger for the private draft campaign. The
source has two lanes:

* `current_...` declarations audit algebra in the tracked EC 2024 manuscript;
* `proposed_...` declarations audit theory proposed by the July 2026 GPT
  revision memo but not yet incorporated into the manuscript.

The wrappers below preserve the initial scalar surface. The comprehensive
finite endpoint, corrected reformulation, all-request range, parity, pooling,
and endogenous-admission results are exposed from `PaperInterface.lean` after
the later completion modules. The cited GPS response-tail theorem remains the
single explicit external analytical boundary.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

/-! ## Current tracked manuscript -/

/-- Corrected algebraic recovery step inside current Proposition 2.1. -/
theorem current_proposition2_1_corrected_recovery
    {x arrivalRate capacity : ℝ} (hcapacity : capacity ≠ 0) :
    gpsSlack capacity (recoveredGPSWeight x arrivalRate capacity) arrivalRate = x := by
  exact proposition2_1_recoveredGPSWeight_slack_eq hcapacity

/-- Lean-checked witness that the minus-sign recovery printed in Proposition 2.1 fails. -/
theorem current_proposition2_1_printed_recovery_is_false :
    printedMinusGPSWeight 3 2 10 = (1 / 10 : ℝ) ∧
      gpsSlack 10 (printedMinusGPSWeight 3 2 10) 2 = -1 ∧
      gpsSlack 10 (printedMinusGPSWeight 3 2 10) 2 ≠ 3 := by
  exact proposition2_1_printed_minus_recovery_counterexample

/-- Lean-checked witness that Proposition 2.3's two printed reciprocal terms differ. -/
theorem current_proposition2_3_printed_reciprocal_is_inconsistent :
    printedExtremeEquityReciprocalTerm 1 2 1 = (1 / 2 : ℝ) ∧
      costConsistentExtremeEquityReciprocalTerm 1 2 1 = 2 ∧
      printedExtremeEquityReciprocalTerm 1 2 1 ≠
        costConsistentExtremeEquityReciprocalTerm 1 2 1 := by
  exact currentDraft_extremeEquity_reciprocal_counterexample

/-- Algebraic conclusion of current Proposition 2.4, conditional on its endpoint formulas. -/
theorem current_proposition2_4_price_of_equity_formula
    (alpha slack u v : ℝ) (hslack : 0 < slack) :
    twoBoroughPriceOfEquity alpha slack u v =
      alpha / slack * (u - v) ^ 2 := by
  exact twoBorough_priceOfEquity_eq alpha slack u v hslack

/-- Algebraic conclusion of current Proposition 2.5 under its source ordering. -/
theorem current_proposition2_5_price_of_efficiency_formula
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ u) :
    twoBoroughPriceOfEfficiency alpha slack u v =
      alpha / slack * v * (u - v) := by
  exact twoBorough_priceOfEfficiency_eq_of_v_le_u halpha hslack hu hv huv

/-- Exact identity in current Proposition 2.7. -/
theorem current_proposition2_7_price_minus_pooling_formula
    (alpha slack u v : ℝ) (hslack : 0 < slack) :
    twoBoroughPriceMinusPooling alpha slack u v =
      alpha / slack * ((u - v) ^ 2 - 2 * u * v) := by
  exact twoBorough_priceMinusPooling_eq alpha slack u v hslack

/-- The current prose's universal ordering is false: pooling can be larger. -/
theorem current_pooling_can_exceed_price_of_equity :
    twoBoroughPriceOfEquity 1 1 1 1 < twoBoroughPoolingGain 1 1 1 1 := by
  exact twoBorough_poolingGain_gt_priceOfEquity_counterexample

/-- The reverse ordering can also occur for sufficiently unequal loads. -/
theorem current_price_of_equity_can_exceed_pooling :
    twoBoroughPoolingGain 1 1 4 1 < twoBoroughPriceOfEquity 1 1 4 1 := by
  exact twoBorough_priceOfEquity_gt_poolingGain_counterexample

/-! ## Proposed fixed-admitted-load revision theory -/

/-- Proposed per-cell reciprocal-capacity form of fixed-load SLA feasibility. -/
theorem proposed_fixed_load_feasibility_iff
    (mu admitted reliability delay : ℝ) (hdelay : 0 < delay) :
    reliability ≤ (mu - admitted) * delay ↔
      admitted + reliability / delay ≤ mu := by
  exact fixedLoadSLAFeasible_iff_effectiveCapacity_le
    mu admitted reliability delay hdelay

/-- Proposed accounting identity: efficiency is arrival-weighted all-request burden. -/
theorem proposed_efficiency_cell_cost_eq_arrival_mul_burden
    (arrival admitted risk inspectionProbability delay penalty : ℝ)
    (hadmitted : admitted = inspectionProbability * arrival) :
    admitted * risk * delay + (arrival - admitted) * risk * penalty =
      arrival * (risk *
        (inspectionProbability * delay + (1 - inspectionProbability) * penalty)) := by
  exact fixedLoadEfficiencyCellCost_eq_arrival_mul_allRequestBurden
    arrival admitted risk inspectionProbability delay penalty hadmitted

/-- Proposed exact-symmetry result for two Boroughs at the closed-form efficiency delay. -/
theorem proposed_exact_symmetry_zero_two_borough_range
    (aggregateRootWeight excessCapacity
      arrival₁ arrival₂ admitted₁ admitted₂ risk₁ risk₂
      reliability₁ reliability₂ penalty₁ penalty₂ : ℝ)
    (harrival : arrival₁ = arrival₂)
    (hadmitted : admitted₁ = admitted₂)
    (hrisk : risk₁ = risk₂)
    (hreliability : reliability₁ = reliability₂)
    (hpenalty : penalty₁ = penalty₂) :
    twoBoroughRange
        (fixedLoadAllRequestBurden arrival₁ admitted₁ risk₁
          (fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
            reliability₁ admitted₁ risk₁) penalty₁)
        (fixedLoadAllRequestBurden arrival₂ admitted₂ risk₂
          (fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
            reliability₂ admitted₂ risk₂) penalty₂) = 0 := by
  exact efficiencyAllRequest_twoBoroughRange_eq_zero
    aggregateRootWeight excessCapacity arrival₁ arrival₂ admitted₁ admitted₂
    risk₁ risk₂ reliability₁ reliability₂ penalty₁ penalty₂
    harrival hadmitted hrisk hreliability hpenalty

/-- Proposed exact one-period stranded-capacity identity. -/
theorem proposed_one_period_pooling_identity
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    poolingOpportunity backlog share capacity =
      (∑ b, positivePart (share b * capacity - backlog b)) -
        positivePart (capacity - ∑ b, backlog b) := by
  exact poolingOpportunity_eq_strandedCapacity backlog share capacity hshares

/-- Proposed one-period pooling opportunity is always nonnegative. -/
theorem proposed_one_period_pooling_nonnegative
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    0 ≤ poolingOpportunity backlog share capacity := by
  exact poolingOpportunity_nonneg backlog share capacity hshares

/-- Proposed outer admitted-load objective violates the midpoint convexity inequality. -/
theorem proposed_endogenous_admission_is_not_convex_witness :
    (endogenousAdmissionServedDelay (8 / 5) (2 / 5) +
        endogenousAdmissionServedDelay (2 / 5) (8 / 5)) / 2 <
      endogenousAdmissionServedDelay 1 1 := by
  exact endogenousAdmissionServedDelay_midpoint_convexity_fails

end LG24ServiceLevelAgreements
