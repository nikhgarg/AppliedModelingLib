import Mathlib.Probability.CDF
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Tactic

/-!
# Continuity of nonatomic real CDFs

The cumulative distribution function of a nonatomic real probability measure
is continuous.  Mathlib supplies its monotonicity and right continuity; the
only additional point is that the left jump at a threshold is the singleton
mass at that threshold.
-/

open Filter MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Real Topology

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
The CDF of a nonatomic real probability measure is continuous.

Mathlib's CDF is a Stieltjes function and is therefore right-continuous.  The
missing left-continuity at `x` is exactly the assertion that the singleton
`{x}` has zero mass.
-/
theorem continuous_cdf_of_noAtoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (ProbabilityTheory.cdf μ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  rw [(ProbabilityTheory.monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim]
  rw [StieltjesFunction.rightLim_eq (ProbabilityTheory.cdf μ) x]
  have hsingle_cdf : (ProbabilityTheory.cdf μ).measure ({x} : Set ℝ) = 0 := by
    rw [ProbabilityTheory.measure_cdf μ]
    exact measure_singleton x
  rw [(ProbabilityTheory.cdf μ).measure_singleton x] at hsingle_cdf
  have hleft_le :
      Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.cdf μ).mono.leftLim_le le_rfl
  have hsub_nonneg :
      0 ≤ ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x :=
    sub_nonneg.mpr hleft_le
  have hsub_nonpos :
      ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hsingle_cdf
  linarith

end
end Probability
end AppliedModelingLib
