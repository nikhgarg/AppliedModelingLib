import AppliedModelingLib.Learning.Prediction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite prediction risk and conditional rates

Reusable finite weighted loss, group-risk, and conditional-rate interfaces.
These primitives are independent of any particular calibration or fairness
definition.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- Squared-error loss at one observation. -/
def squaredError {X : Type*} (f y : Score X) (x : X) : ℝ :=
  (f x - y x) ^ 2

/-- Finite weighted model loss. -/
def modelLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (loss : X → ℝ) : ℝ :=
  ∑ x, w x * loss x

/-- Finite weighted squared-error loss. -/
def squaredLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (f y : Score X) : ℝ :=
  modelLoss w (fun x => squaredError f y x)

/-- Weighted mass of a soft group/event. -/
def groupMass {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : SoftGroup X) : ℝ :=
  ∑ x, w x * g x

/-- Weighted numerator of a group/event-conditional loss. -/
def groupLossNumerator {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : SoftGroup X) (loss : X → ℝ) : ℝ :=
  ∑ x, w x * g x * loss x

/-- Conditional group/event loss, using totalized real division. -/
noncomputable def groupLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : SoftGroup X) (loss : X → ℝ) : ℝ :=
  groupLossNumerator w g loss / groupMass w g

/-- Conditional group squared-error loss. -/
noncomputable def groupSquaredLoss {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : SoftGroup X) (f y : Score X) : ℝ :=
  groupLoss w g (fun x => squaredError f y x)

/-- Conditional group squared disagreement between two predictors. -/
noncomputable def groupSquaredDisagreement {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : SoftGroup X) (f h : Score X) : ℝ :=
  groupLoss w g (fun x => (f x - h x) ^ 2)

/-- Pointwise zero-one loss for classification labels encoded as scores. -/
noncomputable def zeroOneLoss {X : Type*} (c y : Score X) (x : X) : ℝ :=
  if c x = y x then 0 else 1

/-- Expected zero-one classification error. -/
noncomputable def classificationError {X : Type*} [Fintype X]
    (w : FiniteWeight X) (c y : Score X) : ℝ :=
  modelLoss w (fun x => zeroOneLoss c y x)

/-- Expected zero-one classification loss when `yProb` is the conditional
probability of label one. -/
noncomputable def probabilisticClassificationLoss {X : Type*}
    (yProb c : Score X) (x : X) : ℝ :=
  yProb x * zeroOneLoss c (constantScore 1) x +
    (1 - yProb x) * zeroOneLoss c (constantScore 0) x

/-- Numerator for a finite weighted conditional rate. -/
def weightedRateNumerator {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight loss : X → ℝ) : ℝ :=
  ∑ x, w x * weight x * loss x

/-- Mass/denominator for a finite weighted conditional rate. -/
def weightedRateMass {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight : X → ℝ) : ℝ :=
  ∑ x, w x * weight x

/-- Conditional rate for a finite weighted numerator and mass. -/
noncomputable def weightedRate {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight loss : X → ℝ) : ℝ :=
  weightedRateNumerator w weight loss / weightedRateMass w weight

/-- Selected-mass divided by population-mass coefficient. -/
noncomputable def weightedRateBeta {X : Type*} [Fintype X]
    (w : FiniteWeight X) (selected population : X → ℝ) : ℝ :=
  weightedRateMass w selected / weightedRateMass w population

/-- Multiplying a conditional-rate gap by selected mass is equivalent to the
corresponding finite expectation-gap form. -/
theorem weightedRate_gap_eq_expectation_gap {X : Type*} [Fintype X]
    (w : FiniteWeight X) (selected population loss : X → ℝ)
    (hselected_nonneg : 0 ≤ weightedRateMass w selected)
    (hselected_ne : weightedRateMass w selected ≠ 0)
    (hpopulation_ne : weightedRateMass w population ≠ 0) :
    weightedRateMass w selected *
        |weightedRate w selected loss - weightedRate w population loss| =
      |weightedRateNumerator w selected loss -
        weightedRateBeta w selected population *
          weightedRateNumerator w population loss| := by
  unfold weightedRate weightedRateBeta
  set ms := weightedRateMass w selected
  set mp := weightedRateMass w population
  set ns := weightedRateNumerator w selected loss
  set np := weightedRateNumerator w population loss
  have hms : ms ≠ 0 := by simpa [ms] using hselected_ne
  have hmp : mp ≠ 0 := by simpa [mp] using hpopulation_ne
  have hscale :
      ms * |ns / ms - np / mp| =
        |ms * (ns / ms - np / mp)| := by
    rw [abs_mul]
    rw [abs_of_nonneg hselected_nonneg]
  rw [hscale]
  congr 1
  field_simp [hms, hmp]

/-- Conditional posterior mean absolute error contribution at one feature. -/
noncomputable def posteriorConditionalMAE {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) (x : X) : ℝ :=
  ∑ y : Y, q x y * (1 - q x y)

/-- Finite weighted predictive MAE for posterior scores. -/
noncomputable def posteriorMAE {X Y : Type*} [Fintype X] [Fintype Y]
    (w : FiniteWeight X) (q : X → Y → ℝ) : ℝ :=
  modelLoss w (posteriorConditionalMAE q)

end AppliedModelingLib.Learning.Prediction
