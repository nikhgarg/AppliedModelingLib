import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian Translation Absolute Continuity

Small measure-theoretic support for transferring almost-everywhere statements
between nondegenerate Gaussian score laws with a common variance.
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

open MeasureTheory ProbabilityTheory

/-- An almost-everywhere predicate transfers along absolute continuity. -/
theorem ae_of_absolutelyContinuous
    {Alpha : Type*} [MeasurableSpace Alpha]
    {mu nu : Measure Alpha} {p : Alpha -> Prop}
    (hdom : Measure.AbsolutelyContinuous nu mu)
    (hp : Filter.Eventually p (ae mu)) :
    Filter.Eventually p (ae nu) :=
  hdom.ae_le hp

/--
Two nondegenerate real Gaussian laws with the same variance are absolutely
continuous in the displayed direction.
-/
theorem gaussianReal_absolutelyContinuous_of_common_positive_variance
    (mean1 mean2 : Real) {variance : NNReal} (hvariance : 0 < variance) :
    Measure.AbsolutelyContinuous
      (gaussianReal mean1 variance) (gaussianReal mean2 variance) := by
  have hvariance_ne : Not (variance = 0) := ne_of_gt hvariance
  exact (gaussianReal_absolutelyContinuous mean1 hvariance_ne).trans
    (gaussianReal_absolutelyContinuous' mean2 hvariance_ne)

/--
Two nondegenerate real Gaussian laws with the same variance are mutually
absolutely continuous.
-/
theorem gaussianReal_mutuallyAbsolutelyContinuous_of_common_positive_variance
    (mean1 mean2 : Real) {variance : NNReal} (hvariance : 0 < variance) :
    And
      (Measure.AbsolutelyContinuous
        (gaussianReal mean1 variance) (gaussianReal mean2 variance))
      (Measure.AbsolutelyContinuous
        (gaussianReal mean2 variance) (gaussianReal mean1 variance)) := by
  constructor
  · exact gaussianReal_absolutelyContinuous_of_common_positive_variance
      mean1 mean2 hvariance
  · exact gaussianReal_absolutelyContinuous_of_common_positive_variance
      mean2 mean1 hvariance

/--
Any two nondegenerate real Gaussian laws are absolutely continuous, including
when their variances differ.  This is the support fact needed when a Gaussian
prior is conditioned on a noisy Gaussian signal: a positive latent event
cannot become a zero-probability event at a particular realised score.
-/
theorem gaussianReal_absolutelyContinuous_of_positive_variances
    (mean1 mean2 : Real) {variance1 variance2 : NNReal}
    (hvariance1 : 0 < variance1) (hvariance2 : 0 < variance2) :
    Measure.AbsolutelyContinuous
      (gaussianReal mean1 variance1) (gaussianReal mean2 variance2) := by
  exact (gaussianReal_absolutelyContinuous mean1 (ne_of_gt hvariance1)).trans
    (gaussianReal_absolutelyContinuous' mean2 (ne_of_gt hvariance2))

/-- Two real Gaussian laws with positive, not necessarily equal, variances
have the same null sets. -/
theorem gaussianReal_mutuallyAbsolutelyContinuous_of_positive_variances
    (mean1 mean2 : Real) {variance1 variance2 : NNReal}
    (hvariance1 : 0 < variance1) (hvariance2 : 0 < variance2) :
    Measure.AbsolutelyContinuous
      (gaussianReal mean1 variance1) (gaussianReal mean2 variance2) ∧
    Measure.AbsolutelyContinuous
      (gaussianReal mean2 variance2) (gaussianReal mean1 variance1) := by
  constructor
  · exact gaussianReal_absolutelyContinuous_of_positive_variances
      mean1 mean2 hvariance1 hvariance2
  · exact gaussianReal_absolutelyContinuous_of_positive_variances
      mean2 mean1 hvariance2 hvariance1

end

end Probability
end AppliedModelingLib
