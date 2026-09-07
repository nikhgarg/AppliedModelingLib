import AppliedModelingLib.Foundations.Optimization.Argmax
import AppliedModelingLib.Learning.Prediction.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Multiclass prediction primitives

Source-independent interfaces for vector-valued scores, probability-simplex
predictions, and decision rules supported on score maximizers.  These notions
are shared by multiclass calibration, discretization, outcome
indistinguishability, and omniprediction papers.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- A vector-valued real score, with one coordinate for every outcome. -/
abbrev MulticlassScore (X Y : Type*) := Model X (Y → ℝ)

/-- Every prediction is a probability vector over the finite outcome type.

The upper bound is recorded explicitly because source papers often state all
three simplex conditions and use them separately, even though it follows from
unit mass and coordinatewise nonnegativity when the outcome type is inhabited.
-/
def IsSimplexValued {X Y : Type*} [Fintype Y]
    (q : MulticlassScore X Y) : Prop :=
  (∀ x, (∑ y : Y, q x y) = 1) ∧
    (∀ x y, 0 ≤ q x y) ∧
      (∀ x y, q x y ≤ 1)

/-- Formula exposing the three probability-simplex conditions. -/
theorem isSimplexValued_iff {X Y : Type*} [Fintype Y]
    (q : MulticlassScore X Y) :
    IsSimplexValued q ↔
      (∀ x, (∑ y : Y, q x y) = 1) ∧
        (∀ x y, 0 ≤ q x y) ∧
          (∀ x y, q x y ≤ 1) :=
  Iff.rfl

/-- A decision rule chooses a score-maximizing outcome at every feature. -/
abbrev IsArgmaxRule {X Y : Type*}
    (q : MulticlassScore X Y) (rule : Model X Y) : Prop :=
  AppliedModelingLib.Decision.IsPointwiseMax q rule

/-- Formula exposing pointwise score-maximizing support. -/
theorem isArgmaxRule_iff {X Y : Type*}
    (q : MulticlassScore X Y) (rule : Model X Y) :
    IsArgmaxRule q rule ↔ ∀ x y, q x y ≤ q x (rule x) :=
  Iff.rfl

end AppliedModelingLib.Learning.Prediction
