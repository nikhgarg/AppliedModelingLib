import AppliedModelingLib.Foundations.Probability.PoissonProcess

/-!
# Real-time stationary probability-law interface

This leaf records a probability law preserved by a measurable real-time shift
action.  It does not assert a point-process Palm identity or any queue model.
-/

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory

/-- A probability law invariant under a measurable real-time shift action. -/
structure ShiftInvariantProbabilityLaw
    (Ω : Type*) [MeasurableSpace Ω] where
  Pbase : Measure Ω
  isProbability : IsProbabilityMeasure Pbase
  shift : ℝ → Ω → Ω
  shift_zero : shift 0 = id
  shift_add : ∀ s t : ℝ, shift (s + t) = shift s ∘ shift t
  shift_preserving : ∀ t : ℝ, MeasurePreserving (shift t) Pbase Pbase

end AppliedModelingLib.Probability.Palm
