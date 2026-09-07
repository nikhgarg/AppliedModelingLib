import Mathlib.Data.Real.Basic

/-!
# Prediction primitives

Carrier-independent model, score, group, and bounded-loss types used by
calibration, outcome indistinguishability, omniprediction, and multigroup
learning.
-/

namespace AppliedModelingLib.Learning.Prediction

/-- A prediction model from features `X` to reports or actions `Y`. -/
abbrev Model (X Y : Type*) := X → Y

/-- A real-valued prediction score. -/
abbrev Score (X : Type*) := Model X ℝ

/-- A finite weighted distribution over feature observations. -/
abbrev FiniteWeight (X : Type*) := X → ℝ

/-- A real-valued group/event weight. -/
abbrev SoftGroup (X : Type*) := X → ℝ

/-- A Boolean group-membership predicate. -/
abbrev HardGroup (X : Type*) := X → Bool

/-- A loss function normalized to the unit interval. -/
structure BoundedLoss (Y : Type*) where
  value : Y → Y → ℝ
  nonneg : ∀ prediction truth, 0 ≤ value prediction truth
  le_one : ∀ prediction truth, value prediction truth ≤ 1

/-- Constant real-valued prediction score. -/
def constantScore {X : Type*} (a : ℝ) : Score X :=
  fun _ => a

/-- Real indicator of a Boolean group. -/
@[simp] def hardGroupIndicator {X : Type*} (group : HardGroup X) (x : X) : ℝ :=
  if group x then 1 else 0

end AppliedModelingLib.Learning.Prediction
