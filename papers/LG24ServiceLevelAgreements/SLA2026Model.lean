import LG24ServiceLevelAgreements.ProposedParityExistence
import Mathlib.Data.Real.Sqrt

/-!
# Active 2026 SLA source model

This module is the transparent Lean vocabulary for the theory compiled by
`main_msom.tex` in the August 8, 2026 SLA revision.  It deliberately contains
only definitions: the paper-facing endpoint theorems are proved in the modules
that import this one.

All functions use the source orientation `Category -> Borough -> Real`.
`admitted` is the fixed responded-request rate `s`, and `arrival` is the total
request rate `lambda`.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Fixed-load Borough model -/

/-- `E(s)`: capacity left after the fixed admitted workload. -/
def sla2026ExcessCapacity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (capacity : ℝ) (admitted : Category → Borough → ℝ) : ℝ :=
  capacity - ∑ k, ∑ b, admitted k b

/-- The reduced SLA-feasible set in the active manuscript. -/
def sla2026Feasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : ℝ) (admitted : Category → Borough → ℝ)
    (delay : Category → Borough → ℝ) : Prop :=
  finiteMatrixReciprocalCapacityFeasible (fun _ _ ↦ tail)
    (sla2026ExcessCapacity capacity admitted) delay

/-- The independently admitted fraction `s_{k,b} / lambda_{k,b}`. -/
def sla2026InspectionProbability
    {Category Borough : Type*}
    (arrival admitted : Category → Borough → ℝ) : Category → Borough → ℝ :=
  fun k b ↦ admitted k b / arrival k b

/-- Per-request priority-weighted all-request cost `Cost_{k,b}(s,z)`. -/
def sla2026Cost
    {Category Borough : Type*}
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) : Category → Borough → ℝ :=
  fun k b ↦ allRequestBurden (priority k b)
    (sla2026InspectionProbability arrival admitted k b)
    (delay k b) (noninspectionPenalty k b)

/-- Total arrival-weighted all-request burden `G(s,z)`. -/
def sla2026Efficiency
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) : ℝ :=
  finiteArrivalWeightedBurden arrival
    (sla2026Cost arrival admitted priority noninspectionPenalty delay)

/-- Within-category geographic disparity `F(s,z)`. -/
def sla2026Equity
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) : ℝ :=
  finiteAllRequestRangeObjective
    (sla2026Cost arrival admitted priority noninspectionPenalty delay)

/-- The active manuscript's weighted efficiency-equity objective `L_gamma`. -/
def sla2026Tradeoff
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (gamma : ℝ) (arrival admitted priority noninspectionPenalty delay :
      Category → Borough → ℝ) : ℝ :=
  gamma * sla2026Efficiency arrival admitted priority noninspectionPenalty delay +
    (1 - gamma) * sla2026Equity arrival admitted priority
      noninspectionPenalty delay

/-- The fixed noninspection part of `G(s,z)`, which is constant in `z`. -/
def sla2026FixedNoninspectionCost
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, (arrival k b - admitted k b) * priority k b *
    noninspectionPenalty k b

/-- The delay-dependent part of `G(s,z)`. -/
def sla2026ServedDelayCost
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (admitted priority delay : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, admitted k b * priority k b * delay k b

/-- `A_eff(s)`, the source's Borough-budget square-root index. -/
def sla2026EffectiveLoad
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, Real.sqrt (tail * admitted k b * priority k b)

/-- The exact displayed extreme-efficiency SLA threshold. -/
def sla2026EfficientDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : ℝ) (admitted priority : Category → Borough → ℝ) :
    Category → Borough → ℝ :=
  fun k b ↦
    sla2026EffectiveLoad tail admitted priority /
      sla2026ExcessCapacity capacity admitted *
        Real.sqrt (tail / (admitted k b * priority k b))

/-! ## Price-of-equity quantities -/

/-- The source capacity-share vector `q_{k,b}(z) = a / (E(s) z_{k,b})`. -/
def sla2026CapacityShare
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : ℝ) (admitted : Category → Borough → ℝ)
    (delay : Category → Borough → ℝ) : Category → Borough → ℝ :=
  fun k b ↦ tail /
    (sla2026ExcessCapacity capacity admitted * delay k b)

/-- Pearson chi-square divergence on the finite category-Borough cell set. -/
def sla2026PearsonChiSquare
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (left right : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, (left k b - right k b) ^ 2 / right k b

/-- The additive efficiency gap between equitable and efficient endpoints.
This remains a reusable algebraic numerator for the current source's relative
price of equity. -/
def sla2026PriceOfEquity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    (equitable efficient : Category → Borough → ℝ) : ℝ :=
  sla2026Efficiency arrival admitted priority noninspectionPenalty equitable -
    sla2026Efficiency arrival admitted priority noninspectionPenalty efficient

/-- The active manuscript's relative price of equity:
`G(s,z_eq) / G(s,z_eff) - 1`.  The denominator is kept explicit rather than
being folded into a positivity-bearing model record. -/
def sla2026RelativePriceOfEquity
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    (equitable efficient : Category → Borough → ℝ) : ℝ :=
  sla2026Efficiency arrival admitted priority noninspectionPenalty equitable /
      sla2026Efficiency arrival admitted priority noninspectionPenalty efficient - 1

/-! ## City-budget model -/

/-- The city-budget reciprocal feasibility condition. -/
def sla2026CityFeasible
    {Category : Type*} [Fintype Category]
    (tail excessCapacity : ℝ) (delay : Category → ℝ) : Prop :=
  reciprocalCapacityFeasible (fun _ ↦ tail) excessCapacity delay

/-- The city-budget all-request efficiency objective. -/
def sla2026CityEfficiency
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ) (delay : Category → ℝ) : ℝ :=
  (∑ k, ∑ b, admitted k b * priority k b * delay k) +
    sla2026FixedNoninspectionCost arrival admitted priority noninspectionPenalty

/-- `A^city(s)`, the category-pooled square-root index. -/
def sla2026CityEffectiveLoad
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : ℝ) (admitted priority : Category → Borough → ℝ) : ℝ :=
  ∑ k, Real.sqrt (tail * ∑ b, admitted k b * priority k b)

/-- The city-budget square-root endpoint. -/
def sla2026CityEfficientDelay
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail excessCapacity : ℝ) (admitted priority : Category → Borough → ℝ) :
    Category → ℝ :=
  fun k ↦ sla2026CityEffectiveLoad tail admitted priority / excessCapacity *
    Real.sqrt (tail / ∑ b, admitted k b * priority k b)

/-- The active manuscript's relative centralization gain from the
Borough-efficient endpoint to the city-efficient endpoint. -/
def sla2026RelativeCentralizationGain
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted priority noninspectionPenalty :
      Category → Borough → ℝ)
    (boroughDelay : Category → Borough → ℝ) (cityDelay : Category → ℝ) : ℝ :=
  1 - sla2026CityEfficiency arrival admitted priority noninspectionPenalty cityDelay /
    sla2026Efficiency arrival admitted priority noninspectionPenalty boroughDelay

end

end LG24ServiceLevelAgreements
