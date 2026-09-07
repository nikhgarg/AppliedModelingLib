import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalFactors
import Mathlib.Tactic

/-!
# Deterministic arrival-index shifts of marked two-sided renewal input

This file records the literal input-law symmetry needed by a source-native
Lindley construction.  Both the arrival-gap and work-mark paths are shifted
by the same deterministic arrival index.  It is only an iid input symmetry:
it creates no queue state, stationarity certificate, or response-tail claim.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Recenter both coordinates of a literal marked two-sided renewal input at
a deterministic arrival-index displacement. -/
def twoSidedMarkedRenewalIndexShift (k : ℤ) :
    TwoSidedMarkedRenewalSample → TwoSidedMarkedRenewalSample :=
  fun z => (twoSidedGapIndexShift k z.1, twoSidedGapIndexShift k z.2)

/-- The simultaneous marked-input recentering is measurable. -/
theorem measurable_twoSidedMarkedRenewalIndexShift (k : ℤ) :
    Measurable (twoSidedMarkedRenewalIndexShift k) := by
  exact ((measurable_twoSidedGapIndexShift k).comp measurable_fst).prodMk
    ((measurable_twoSidedGapIndexShift k).comp measurable_snd)

/-- The direct marked-renewal source law is invariant under every
deterministic arrival-index shift. -/
theorem twoSidedMarkedRenewalIndexShift_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    MeasurePreserving (twoSidedMarkedRenewalIndexShift k)
      (twoSidedMarkedRenewalMeasure rate) (twoSidedMarkedRenewalMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [twoSidedMarkedRenewalIndexShift, twoSidedMarkedRenewalMeasure] using
    (twoSidedGapIndexShift_measurePreserving hrate k).prod
      (twoSidedGapIndexShift_measurePreserving (by norm_num : 0 < (1 : ℝ)) k)

/-- Every coordinate of a recentered marked input is literally the
corresponding displaced coordinate of the original input. -/
theorem twoSidedMarkedRenewalIndexShift_apply
    (k i : ℤ) (z : TwoSidedMarkedRenewalSample) :
    twoSidedGap i (twoSidedMarkedRenewalIndexShift k z).1 =
      twoSidedGap (i + k) z.1 ∧
    twoSidedGap i (twoSidedMarkedRenewalIndexShift k z).2 =
      twoSidedGap (i + k) z.2 := by
  constructor <;> rfl

end

end AppliedModelingLib.Probability.PoissonProcess
