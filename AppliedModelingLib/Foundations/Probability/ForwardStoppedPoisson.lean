import AppliedModelingLib.Foundations.Probability.ForwardPoissonStopping
import Mathlib.Probability.Kernel.Condexp

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-!
# Forward stopped Poisson increments

This module states a stopped-increment interface on the forward `ℝ≥0` time
axis. It deliberately avoids the legacy all-real-time count interface: a
forward report process begins at an incident and is naturally forward in time.
-/

/-- Count arrivals in the `u` units immediately following a forward time `τ`. -/
def forwardPostStopIntervalCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (τ : Ω → ℝ≥0) (u : ℝ≥0) : Ω → ℕ :=
  fun ω => H.intervalCount (τ ω) (τ ω + u) ω

/--
The forward-time strong-Markov seam for a post-stopping-time increment law.

The conditional law field is intentionally an explicit boundary: fixed-time
independent increments do not prove it for random `τ` without a concrete
path-space strong-Markov result.
-/
structure ForwardStoppedPoissonIncrementLawCertificate
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P) where
  stopTime : Ω → ℝ≥0
  isStoppingTime :
    MeasureTheory.IsStoppingTime H.filtration (toNativeForwardStoppingTime stopTime)
  conditional_increment_hasLaw :
    ∀ u : ℝ≥0, ∀ᵐ ω ∂P,
      ProbabilityTheory.HasLaw (forwardPostStopIntervalCount H.process stopTime u)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.process.rate (u : ℝ)
            (mul_nonneg H.process.rate_nonneg (NNReal.coe_nonneg u))))
        (ProbabilityTheory.condExpKernel P isStoppingTime.measurableSpace ω)

namespace ForwardStoppedPoissonIncrementLawCertificate

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P}

/-- Conditional no-arrival survival after a forward stopping time. -/
theorem conditional_postStop_zero_real
    (C : ForwardStoppedPoissonIncrementLawCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.isStoppingTime.measurableSpace ω).real
          {ω' | forwardPostStopIntervalCount H.process C.stopTime u ω' = 0} =
        noArrivalProb H.process.rate (u : ℝ) := by
  filter_upwards [C.conditional_increment_hasLaw u] with ω hω
  simpa using
    (hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.process.rate_nonneg (NNReal.coe_nonneg u)) hω 0)

/-- The Lemma-2 exponential-tail form of the stopped conditional survival law. -/
theorem conditional_postStop_zero_real_eq_exponential_tail
    (C : ForwardStoppedPoissonIncrementLawCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.isStoppingTime.measurableSpace ω).real
          {ω' | forwardPostStopIntervalCount H.process C.stopTime u ω' = 0} =
        ((Exponential.Model.mk H.process.rate H.process.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal := by
  filter_upwards [C.conditional_postStop_zero_real u] with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail H.process.rate H.process.rate_pos
    (NNReal.coe_nonneg u)

end ForwardStoppedPoissonIncrementLawCertificate

end
end PoissonProcess
end Probability
end AppliedModelingLib
