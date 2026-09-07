import LG24ServiceLevelAgreements.ProposedPooling
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Proposed theory: fixed admitted load and endogenous-load nonconvexity

This file formalizes three elementary claims from the revision memo for
*Redesigning Service Level Agreements*.

* The fixed-load tail condition `(mu - s) * z >= a` is equivalent, for a
  positive conditional delay `z`, to requiring effective capacity
  `s + a / z <= mu`; at equality that effective capacity binds exactly.
* Operationally identical Boroughs within a category have identical
  all-request burdens.  In particular, the memo's closed-form efficiency
  delay assigns identical delays to cells with identical primitives, so their
  two-Borough burden range is zero.
* Once admitted loads are endogenous, the memo's two-class served-delay
  objective violates the midpoint convexity inequality at an explicit pair of
  rational points.

The results are deliberately finite-dimensional algebraic seams.  They do not
formalize the queueing tail bound that motivates the fixed-load constraint.
-/

namespace LG24ServiceLevelAgreements

noncomputable section

/-! ## Reciprocal form of fixed-load SLA feasibility -/

/--
Capacity required by a cell with admitted load `s`, tail exponent `a`, and
conditional SLA delay `z` in the memo's fixed-load benchmark.
-/
def fixedLoadEffectiveCapacity (s a z : ℝ) : ℝ :=
  s + a / z

/-- The sufficient exponential-tail condition for one fixed-load cell. -/
def fixedLoadSLAFeasible (mu s a z : ℝ) : Prop :=
  a ≤ (mu - s) * z

/--
For a positive SLA delay, the multiplicative tail constraint is exactly the
reciprocal effective-capacity constraint used in the revision memo.
-/
theorem fixedLoadSLAFeasible_iff_effectiveCapacity_le
    (mu s a z : ℝ) (hz : 0 < z) :
    fixedLoadSLAFeasible mu s a z ↔ fixedLoadEffectiveCapacity s a z ≤ mu := by
  rw [fixedLoadSLAFeasible, fixedLoadEffectiveCapacity]
  constructor
  · intro h
    have hdiv : a / z ≤ mu - s := (div_le_iff₀ hz).2 h
    linarith
  · intro h
    apply (div_le_iff₀ hz).1
    linarith

/-- At reciprocal effective capacity, the cell's tail constraint binds exactly. -/
theorem fixedLoadEffectiveCapacity_exactly_binds
    (s a z : ℝ) (hz : z ≠ 0) :
    (fixedLoadEffectiveCapacity s a z - s) * z = a := by
  simp [fixedLoadEffectiveCapacity, hz]

/--
Conversely, every binding multiplicative constraint with nonzero delay has
exactly the memo's reciprocal effective-capacity form.
-/
theorem fixedLoad_constraint_binds_iff
    (mu s a z : ℝ) (hz : z ≠ 0) :
    (mu - s) * z = a ↔ mu = fixedLoadEffectiveCapacity s a z := by
  constructor
  · intro h
    have hsub : mu - s = a / z := (eq_div_iff hz).2 h
    simp only [fixedLoadEffectiveCapacity]
    linarith
  · rintro rfl
    exact fixedLoadEffectiveCapacity_exactly_binds s a z hz

/-! ## Exact within-category symmetry of all-request burden -/

/-- The fixed-load inspection fraction is admitted load divided by arrivals. -/
def fixedLoadInspectionProbability (arrival admitted : ℝ) : ℝ :=
  admitted / arrival

/--
The memo's all-request burden written directly in terms of arrival and admitted
loads, using `admitted / arrival` as the inspection probability.
-/
def fixedLoadAllRequestBurden
    (arrival admitted risk conditionalDelay noninspectionPenalty : ℝ) : ℝ :=
  allRequestBurden risk (fixedLoadInspectionProbability arrival admitted)
    conditionalDelay noninspectionPenalty

/--
Identical arrival, admitted load, risk, and noninspection penalty, together
with equal conditional delays, imply equal all-request burdens.
-/
theorem fixedLoadAllRequestBurden_eq_of_symmetric_inputs
    (arrival₁ arrival₂ admitted₁ admitted₂ risk₁ risk₂
      delay₁ delay₂ penalty₁ penalty₂ : ℝ)
    (harrival : arrival₁ = arrival₂)
    (hadmitted : admitted₁ = admitted₂)
    (hrisk : risk₁ = risk₂)
    (hdelay : delay₁ = delay₂)
    (hpenalty : penalty₁ = penalty₂) :
    fixedLoadAllRequestBurden arrival₁ admitted₁ risk₁ delay₁ penalty₁ =
      fixedLoadAllRequestBurden arrival₂ admitted₂ risk₂ delay₂ penalty₂ := by
  subst arrival₂
  subst admitted₂
  subst risk₂
  subst delay₂
  subst penalty₂
  rfl

/--
The memo's closed-form fixed-load efficiency delay
`(A(s) / E(s)) * sqrt (a / (s * r))` for one active cell.
-/
def fixedLoadEfficiencyDelay
    (aggregateRootWeight excessCapacity reliability admitted risk : ℝ) : ℝ :=
  (aggregateRootWeight / excessCapacity) *
    Real.sqrt (reliability / (admitted * risk))

/-- Identical active-cell primitives receive identical closed-form efficiency delays. -/
theorem fixedLoadEfficiencyDelay_eq_of_symmetric_primitives
    (aggregateRootWeight excessCapacity reliability₁ reliability₂
      admitted₁ admitted₂ risk₁ risk₂ : ℝ)
    (hreliability : reliability₁ = reliability₂)
    (hadmitted : admitted₁ = admitted₂)
    (hrisk : risk₁ = risk₂) :
    fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
        reliability₁ admitted₁ risk₁ =
      fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
        reliability₂ admitted₂ risk₂ := by
  subst reliability₂
  subst admitted₂
  subst risk₂
  rfl

/--
Thus symmetric primitive inputs give equal all-request burden at the memo's
closed-form efficiency endpoint, without separately assuming delay symmetry.
-/
theorem efficiencyAllRequestBurden_eq_of_symmetric_primitives
    (aggregateRootWeight excessCapacity
      arrival₁ arrival₂ admitted₁ admitted₂ risk₁ risk₂
      reliability₁ reliability₂ penalty₁ penalty₂ : ℝ)
    (harrival : arrival₁ = arrival₂)
    (hadmitted : admitted₁ = admitted₂)
    (hrisk : risk₁ = risk₂)
    (hreliability : reliability₁ = reliability₂)
    (hpenalty : penalty₁ = penalty₂) :
    fixedLoadAllRequestBurden arrival₁ admitted₁ risk₁
        (fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
          reliability₁ admitted₁ risk₁) penalty₁ =
      fixedLoadAllRequestBurden arrival₂ admitted₂ risk₂
        (fixedLoadEfficiencyDelay aggregateRootWeight excessCapacity
          reliability₂ admitted₂ risk₂) penalty₂ := by
  apply fixedLoadAllRequestBurden_eq_of_symmetric_inputs
  · exact harrival
  · exact hadmitted
  · exact hrisk
  · exact fixedLoadEfficiencyDelay_eq_of_symmetric_primitives
      aggregateRootWeight excessCapacity reliability₁ reliability₂
      admitted₁ admitted₂ risk₁ risk₂ hreliability hadmitted hrisk
  · exact hpenalty

/-- The range of two Borough-level burdens. -/
def twoBoroughRange (burden₁ burden₂ : ℝ) : ℝ :=
  max burden₁ burden₂ - min burden₁ burden₂

/-- Equal Borough burdens have zero two-Borough range. -/
theorem twoBoroughRange_eq_zero_of_eq (burden₁ burden₂ : ℝ)
    (hburden : burden₁ = burden₂) :
    twoBoroughRange burden₁ burden₂ = 0 := by
  subst burden₂
  simp [twoBoroughRange]

/--
Exact within-category primitive symmetry makes the two-Borough all-request
range zero at the closed-form efficiency endpoint.
-/
theorem efficiencyAllRequest_twoBoroughRange_eq_zero
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
  apply twoBoroughRange_eq_zero_of_eq
  exact efficiencyAllRequestBurden_eq_of_symmetric_primitives
    aggregateRootWeight excessCapacity arrival₁ arrival₂ admitted₁ admitted₂
    risk₁ risk₂ reliability₁ reliability₂ penalty₁ penalty₂
    harrival hadmitted hrisk hreliability hpenalty

/-! ## An explicit endogenous-admission nonconvexity witness -/

/--
The two-class served-delay term from the memo's endogenous-admission example,
with `aᵢ * rᵢ = 1`, no drop term, and total capacity `10`.
-/
def endogenousAdmissionServedDelay (s₁ s₂ : ℝ) : ℝ :=
  (Real.sqrt s₁ + Real.sqrt s₂) ^ 2 / (10 - s₁ - s₂)

private theorem sqrt_eight_fifths_eq_two_mul_sqrt_two_fifths :
    Real.sqrt (8 / 5 : ℝ) = 2 * Real.sqrt (2 / 5 : ℝ) := by
  have hsqrtFour : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [show (8 / 5 : ℝ) = 4 * (2 / 5) by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrtFour]

private theorem sqrt_two_fifths_sq :
    Real.sqrt (2 / 5 : ℝ) ^ 2 = 2 / 5 := by
  exact Real.sq_sqrt (by norm_num)

/-- First endpoint of the exact nonconvexity witness. -/
theorem endogenousAdmissionServedDelay_eight_fifths_two_fifths :
    endogenousAdmissionServedDelay (8 / 5) (2 / 5) = 9 / 20 := by
  rw [endogenousAdmissionServedDelay, sqrt_eight_fifths_eq_two_mul_sqrt_two_fifths]
  rw [show (2 * Real.sqrt (2 / 5 : ℝ) + Real.sqrt (2 / 5 : ℝ)) ^ 2 =
      9 * Real.sqrt (2 / 5 : ℝ) ^ 2 by ring]
  rw [sqrt_two_fifths_sq]
  norm_num

/-- The swapped endpoint has the same exact value. -/
theorem endogenousAdmissionServedDelay_two_fifths_eight_fifths :
    endogenousAdmissionServedDelay (2 / 5) (8 / 5) = 9 / 20 := by
  rw [endogenousAdmissionServedDelay, sqrt_eight_fifths_eq_two_mul_sqrt_two_fifths]
  rw [show (Real.sqrt (2 / 5 : ℝ) + 2 * Real.sqrt (2 / 5 : ℝ)) ^ 2 =
      9 * Real.sqrt (2 / 5 : ℝ) ^ 2 by ring]
  rw [sqrt_two_fifths_sq]
  norm_num

/-- The midpoint `(1, 1)` has the strictly larger exact value `1 / 2`. -/
theorem endogenousAdmissionServedDelay_one_one :
    endogenousAdmissionServedDelay 1 1 = 1 / 2 := by
  norm_num [endogenousAdmissionServedDelay]

/--
The midpoint convexity inequality fails at the two rational endpoints: the
midpoint value is strictly greater than the average endpoint value.
-/
theorem endogenousAdmissionServedDelay_midpoint_convexity_fails :
    (endogenousAdmissionServedDelay (8 / 5) (2 / 5) +
        endogenousAdmissionServedDelay (2 / 5) (8 / 5)) / 2 <
      endogenousAdmissionServedDelay 1 1 := by
  rw [endogenousAdmissionServedDelay_eight_fifths_two_fifths,
    endogenousAdmissionServedDelay_two_fifths_eight_fifths,
    endogenousAdmissionServedDelay_one_one]
  norm_num

end

end LG24ServiceLevelAgreements
