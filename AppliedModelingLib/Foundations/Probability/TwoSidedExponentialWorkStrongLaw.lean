import AppliedModelingLib.Foundations.Probability.PalmArrivalPathNonexplosion
import Mathlib.Tactic

/-!
# Strong law for two-sided unit-exponential work paths

The SLA source uses a complete integer-indexed iid unit-exponential path for
each class's work marks.  This module records only the forward empirical-mean
law of that path.  It is a source-input fact and makes no queueing, reset,
Palm-response, or stationarity assertion.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

/--
For a two-sided iid unit-exponential path, the empirical mean of its
nonnegative-index work marks converges almost surely to the unit source mean.
The prefix `n + 1` deliberately includes the index-zero mark, matching the
integer-indexed work paths retained by tagged Palm inputs.
-/
theorem ae_tendsto_twoSidedUnitExponentialFutureWorkMean :
    ∀ᵐ omega ∂twoSidedInterarrivalMeasure 1,
      Tendsto
        (fun n : ℕ =>
          (∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.ofNat j) omega) /
            ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1) := by
  simpa only [candidateFutureEpoch, Nat.cast_add, Nat.cast_one, one_div,
    inv_one] using
    (ae_candidateFutureEpoch_succ_div_nat_succ_tendsto
      (rate := (1 : ℝ)) (by norm_num))

end

end AppliedModelingLib.Probability.PoissonProcess
