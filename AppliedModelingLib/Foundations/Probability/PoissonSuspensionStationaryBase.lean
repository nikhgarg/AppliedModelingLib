import AppliedModelingLib.Foundations.Probability.PoissonSuspensionFlow
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core

/-!
# Stationary base law from the Poisson suspension flow

This module packages the normalized exponential special flow as the literal
`ShiftInvariantProbabilityLaw` required by the Palm/PASTA interfaces.  The
result is an untagged stationary base law.  It does not by itself establish
the marked Campbell/Palm identity relating this base to the separately tagged
iid-gap law.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory

noncomputable section

/-- The normalized exponential suspension, restricted to its full-measure
good carrier, is a stationary real-time probability law. -/
def goodSuspensionShiftInvariantLaw
    {rate : ℝ} (hrate : 0 < rate) :
    Palm.ShiftInvariantProbabilityLaw GoodSuspensionState where
  Pbase := goodSuspensionMeasure rate
  isProbability := isProbabilityMeasure_goodSuspensionMeasure hrate
  shift := goodSuspensionFlow
  shift_zero := goodSuspensionFlow_zero
  shift_add := goodSuspensionFlow_add
  shift_preserving := fun t =>
    goodSuspensionFlow_measurePreserving_of_raw hrate t
      (suspensionFlow_measurePreserving_suspensionMeasure hrate t)

end

end AppliedModelingLib.Probability.PoissonProcess
