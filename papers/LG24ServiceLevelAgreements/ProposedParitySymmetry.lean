import LG24ServiceLevelAgreements.ProposedOptimization
import LG24ServiceLevelAgreements.ProposedFixedLoad
import LG24ServiceLevelAgreements.RevisionBoundaries
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import Mathlib.Tactic

/-!
# Proposed theory: all-request parity and exact symmetry

This file closes two elementary seams in the July 2026 revision memo:

* exact reduction of an all-request parity target `u` to the delay
  `(u - offset) / (risk * inspectionProbability)`, including the reciprocal
  capacity term and the ARRIVAL-weighted efficiency coefficient; and
* finite exact symmetry across Boroughs within category, together with an
  abstract bridge showing that an efficient zero-range point has zero
  lexicographic price of equity.

All denominator assumptions are explicit. No near-symmetry or continuity
claim is made.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Exact all-request parity reduction -/

/-- The fixed non-inspection part of one cell's all-request burden. -/
def allRequestFixedOffset
    (risk inspectionProbability noninspectionPenalty : ℝ) : ℝ :=
  risk * (1 - inspectionProbability) * noninspectionPenalty

/-- The coefficient of conditional delay in one cell's all-request burden. -/
def allRequestDelaySlope (risk inspectionProbability : ℝ) : ℝ :=
  risk * inspectionProbability

/--
Conditional delay that attains common all-request burden `level`, provided the
risk-adjusted inspection probability is nonzero.
-/
def allRequestParityDelay
    (level risk inspectionProbability noninspectionPenalty : ℝ) : ℝ :=
  (level - allRequestFixedOffset risk inspectionProbability noninspectionPenalty) /
    allRequestDelaySlope risk inspectionProbability

/-- All-request burden is its fixed offset plus slope times conditional delay. -/
theorem allRequestBurden_eq_fixedOffset_add_slope_mul_delay
    (risk inspectionProbability conditionalDelay noninspectionPenalty : ℝ) :
    allRequestBurden risk inspectionProbability conditionalDelay noninspectionPenalty =
      allRequestFixedOffset risk inspectionProbability noninspectionPenalty +
        allRequestDelaySlope risk inspectionProbability * conditionalDelay := by
  rw [allRequestBurden_eq_offset_add_delay]
  unfold allRequestFixedOffset allRequestDelaySlope
  ring

/-- The parity delay gives exactly the requested common all-request burden. -/
theorem allRequestBurden_parityDelay_eq_level
    {level risk inspectionProbability noninspectionPenalty : ℝ}
    (hrisk : risk ≠ 0) (hprobability : inspectionProbability ≠ 0) :
    allRequestBurden risk inspectionProbability
        (allRequestParityDelay level risk inspectionProbability noninspectionPenalty)
        noninspectionPenalty = level := by
  rw [allRequestBurden_eq_fixedOffset_add_slope_mul_delay]
  unfold allRequestParityDelay allRequestDelaySlope
  field_simp [hrisk, hprobability]
  ring

/-- Coefficient in the parity-reduced reciprocal-capacity constraint. -/
def allRequestParityCapacityCoefficient
    (logTail risk inspectionProbability : ℝ) : ℝ :=
  logTail * risk * inspectionProbability

/--
Substituting the parity delay into `a / z` gives
`a * risk * probability / (level - offset)`.
-/
theorem logTail_div_parityDelay_eq
    {logTail level risk inspectionProbability noninspectionPenalty : ℝ}
    (hrisk : risk ≠ 0) (hprobability : inspectionProbability ≠ 0)
    (hlevel : level -
      allRequestFixedOffset risk inspectionProbability noninspectionPenalty ≠ 0) :
    logTail /
        allRequestParityDelay level risk inspectionProbability noninspectionPenalty =
      allRequestParityCapacityCoefficient logTail risk inspectionProbability /
        (level -
          allRequestFixedOffset risk inspectionProbability noninspectionPenalty) := by
  unfold allRequestParityDelay allRequestParityCapacityCoefficient
    allRequestDelaySlope
  field_simp [hrisk, hprobability, hlevel]

/--
At parity, one cell's full fixed-load efficiency contribution is ARRIVAL load
times the common burden level.
-/
theorem fixedLoadEfficiencyCellCost_parityDelay_eq_arrival_mul_level
    {arrival admitted risk inspectionProbability noninspectionPenalty level : ℝ}
    (hadmitted : admitted = inspectionProbability * arrival)
    (hrisk : risk ≠ 0) (hprobability : inspectionProbability ≠ 0) :
    fixedLoadEfficiencyCellCost arrival admitted risk
        (allRequestParityDelay level risk inspectionProbability noninspectionPenalty)
        noninspectionPenalty =
      arrival * level := by
  rw [fixedLoadEfficiencyCellCost_eq_arrival_mul_allRequestBurden
    arrival admitted risk inspectionProbability
    (allRequestParityDelay level risk inspectionProbability noninspectionPenalty)
    noninspectionPenalty hadmitted]
  rw [allRequestBurden_parityDelay_eq_level hrisk hprobability]

/--
Within one category, parity therefore uses total ARRIVAL weight
`(∑_b lambda_b) * u`, not total admitted load.
-/
theorem category_fixedLoadEfficiency_at_parity_eq_arrivalWeight
    {Borough : Type*} [Fintype Borough]
    (arrival admitted risk inspectionProbability noninspectionPenalty : Borough → ℝ)
    (level : ℝ)
    (hadmitted : ∀ b, admitted b = inspectionProbability b * arrival b)
    (hrisk : ∀ b, risk b ≠ 0)
    (hprobability : ∀ b, inspectionProbability b ≠ 0) :
    (∑ b, fixedLoadEfficiencyCellCost
        (arrival b) (admitted b) (risk b)
        (allRequestParityDelay level (risk b) (inspectionProbability b)
          (noninspectionPenalty b))
        (noninspectionPenalty b)) =
      (∑ b, arrival b) * level := by
  classical
  calc
    ∑ b, fixedLoadEfficiencyCellCost
        (arrival b) (admitted b) (risk b)
        (allRequestParityDelay level (risk b) (inspectionProbability b)
          (noninspectionPenalty b))
        (noninspectionPenalty b) =
        ∑ b, arrival b * level := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact fixedLoadEfficiencyCellCost_parityDelay_eq_arrival_mul_level
        (hadmitted b) (hrisk b) (hprobability b)
    _ = (∑ b, arrival b) * level := by rw [Finset.sum_mul]

/-- Arrival-weighted parity reduction simultaneously for all finite categories. -/
theorem finite_fixedLoadEfficiency_at_parity_eq_arrivalWeights
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival admitted risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ)
    (level : Category → ℝ)
    (hadmitted : ∀ k b, admitted k b = inspectionProbability k b * arrival k b)
    (hrisk : ∀ k b, risk k b ≠ 0)
    (hprobability : ∀ k b, inspectionProbability k b ≠ 0) :
    (∑ k, ∑ b, fixedLoadEfficiencyCellCost
        (arrival k b) (admitted k b) (risk k b)
        (allRequestParityDelay (level k) (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b))
        (noninspectionPenalty k b)) =
      ∑ k, (∑ b, arrival k b) * level k := by
  classical
  apply Finset.sum_congr rfl
  intro k _hk
  exact category_fixedLoadEfficiency_at_parity_eq_arrivalWeight
    (arrival k) (admitted k) (risk k) (inspectionProbability k)
    (noninspectionPenalty k) (level k)
    (hadmitted k) (hrisk k) (hprobability k)

/-- Finite parity substitution in the reciprocal-capacity constraint. -/
theorem finite_reciprocalCapacity_at_parity_eq
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (logTail risk inspectionProbability noninspectionPenalty :
      Category → Borough → ℝ)
    (level : Category → ℝ)
    (hrisk : ∀ k b, risk k b ≠ 0)
    (hprobability : ∀ k b, inspectionProbability k b ≠ 0)
    (hlevel : ∀ k b,
      level k - allRequestFixedOffset (risk k b) (inspectionProbability k b)
        (noninspectionPenalty k b) ≠ 0) :
    (∑ k, ∑ b, logTail k b /
        allRequestParityDelay (level k) (risk k b) (inspectionProbability k b)
          (noninspectionPenalty k b)) =
      ∑ k, ∑ b,
        allRequestParityCapacityCoefficient
            (logTail k b) (risk k b) (inspectionProbability k b) /
          (level k - allRequestFixedOffset
            (risk k b) (inspectionProbability k b) (noninspectionPenalty k b)) := by
  classical
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro b _hb
  exact logTail_div_parityDelay_eq
    (hrisk k b) (hprobability k b) (hlevel k b)

/-! ## Finite exact symmetry and zero price -/

/--
For finitely many categories and two Boroughs, equality of all cell primitives
and conditional delays within every category makes the sum of within-category
all-request ranges exactly zero.
-/
theorem finite_exactSymmetry_zero_allRequestRange
    {Category : Type*} [Fintype Category]
    (arrival admitted risk delay noninspectionPenalty : Category → Bool → ℝ)
    (harrival : ∀ k, arrival k false = arrival k true)
    (hadmitted : ∀ k, admitted k false = admitted k true)
    (hrisk : ∀ k, risk k false = risk k true)
    (hdelay : ∀ k, delay k false = delay k true)
    (hpenalty : ∀ k,
      noninspectionPenalty k false = noninspectionPenalty k true) :
    twoBoroughAllRequestRangeObjective
      arrival admitted risk delay noninspectionPenalty = 0 := by
  apply twoBoroughRangeObjective_eq_zero_of_eq
  intro k
  exact fixedLoadAllRequestBurden_eq_of_symmetric_inputs
    (arrival k false) (arrival k true)
    (admitted k false) (admitted k true)
    (risk k false) (risk k true)
    (delay k false) (delay k true)
    (noninspectionPenalty k false) (noninspectionPenalty k true)
    (harrival k) (hadmitted k) (hrisk k) (hdelay k) (hpenalty k)

/--
For arbitrary nonempty finite Borough sets, primitives and delays that are
constant within each category give zero sum of within-category ranges.
-/
theorem finite_exactSymmetry_generalBorough_zero_allRequestRange
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival admitted risk delay noninspectionPenalty : Category → Borough → ℝ)
    (commonArrival commonAdmitted commonRisk commonDelay commonPenalty :
      Category → ℝ)
    (harrival : ∀ k b, arrival k b = commonArrival k)
    (hadmitted : ∀ k b, admitted k b = commonAdmitted k)
    (hrisk : ∀ k b, risk k b = commonRisk k)
    (hdelay : ∀ k b, delay k b = commonDelay k)
    (hpenalty : ∀ k b, noninspectionPenalty k b = commonPenalty k) :
    finiteAllRequestRangeObjective
      (fun k b ↦ fixedLoadAllRequestBurden
        (arrival k b) (admitted k b) (risk k b)
        (delay k b) (noninspectionPenalty k b)) = 0 := by
  apply finiteAllRequestRangeObjective_eq_zero_of_constant
    (level := fun k ↦ fixedLoadAllRequestBurden
      (commonArrival k) (commonAdmitted k) (commonRisk k)
      (commonDelay k) (commonPenalty k))
  intro k b
  exact fixedLoadAllRequestBurden_eq_of_symmetric_inputs
    (arrival k b) (commonArrival k)
    (admitted k b) (commonAdmitted k)
    (risk k b) (commonRisk k)
    (delay k b) (commonDelay k)
    (noninspectionPenalty k b) (commonPenalty k)
    (harrival k b) (hadmitted k b) (hrisk k b)
    (hdelay k b) (hpenalty k b)

/--
If an efficiency minimizer has zero equity, any lexicographic
equity-then-efficiency minimizer has the same efficiency value; hence the
additive price of equity is zero.
-/
theorem zero_lexicographic_price_of_equity
    {X : Type*} {feasible : Set X} {equity efficiency : X → ℝ}
    {efficient equitable : X}
    (hefficient : MinimizesOn feasible efficiency efficient)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      feasible equity efficiency equitable)
    (hequity_nonnegative : ∀ x ∈ feasible, 0 ≤ equity x)
    (hefficient_zero : equity efficient = 0) :
    efficiency equitable - efficiency efficient = 0 := by
  have hequitable_zero : equity equitable = 0 := by
    have hle : equity equitable ≤ 0 := by
      rw [← hefficient_zero]
      exact hequitable.2.1 efficient hefficient.1
    exact le_antisymm hle (hequity_nonnegative equitable hequitable.1)
  have hforward : efficiency efficient ≤ efficiency equitable :=
    hefficient.2 equitable hequitable.1
  have hbackward : efficiency equitable ≤ efficiency efficient :=
    hequitable.2.2 efficient hefficient.1 (by
      rw [hefficient_zero, hequitable_zero])
  linarith

end

end LG24ServiceLevelAgreements
