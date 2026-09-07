import LG21TestOptionalPolicies.RawGaussianOptionalPositiveBranch
import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge

/-!
# Literal Gaussian upper-tail posterior formula for LG21

This module connects the selected posterior used by the report-required
candidate to the actual normalized Gaussian tail integral.  It does not
assume a posterior-mean formula: the formula is inherited from the proved
location-scale conditional-mean identity in
`RawGaussianOptionalPositiveBranch` after identifying the explicit Gaussian
posterior kernel with its positive-scale law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open AppliedModelingLib Probability

/-- A positive-variance mathlib Gaussian viewed as a location-scale law. -/
def lg21GaussianScaleLawOfNNRealVariance
    (mean : ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    GaussianScaleLaw where
  mean := mean
  scale := Real.sqrt (variance : ℝ)
  scale_pos := Real.sqrt_pos.2 (by
    exact_mod_cast (pos_iff_ne_zero.mpr hvariance : 0 < variance))

/-- The location-scale representation has exactly the supplied Gaussian law. -/
theorem lg21GaussianScaleLawOfNNRealVariance_toMeasure
    (mean : ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    (lg21GaussianScaleLawOfNNRealVariance mean variance hvariance).toMeasure =
      gaussianReal mean variance := by
  unfold lg21GaussianScaleLawOfNNRealVariance
  dsimp [GaussianScaleLaw.toMeasure, GaussianScaleLaw.varianceNNReal]
  congr 1
  apply NNReal.eq
  exact Real.sq_sqrt NNReal.zero_le_coe

/-- The explicit Gaussian posterior kernel as a positive-scale Gaussian law. -/
def lg21GaussianSignalPosteriorScaleLaw
    (priorMean priorVariance noiseVariance observedScore : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    GaussianScaleLaw :=
  lg21GaussianScaleLawOfNNRealVariance
    (gaussianSignalWeight priorVariance noiseVariance * observedScore +
      gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
    (gaussianSignalPosteriorVariance priorVariance noiseVariance)
    (ne_of_gt (lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance))

/-- The displayed scale law is exactly the posterior kernel fibre. -/
theorem lg21GaussianSignalPosteriorScaleLaw_toMeasure
    (priorMean priorVariance noiseVariance observedScore : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (lg21GaussianSignalPosteriorScaleLaw
      priorMean priorVariance noiseVariance observedScore
      hpriorVariance hnoiseVariance).toMeasure =
      gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance observedScore := by
  rw [gaussianSignalPosteriorKernel_apply]
  exact lg21GaussianScaleLawOfNNRealVariance_toMeasure _ _ _

/--
The literal posterior mean after observing a score and the positive-mass
selection `Q ≥ cutoff` is the Gaussian upper-tail conditional mean.  This is
an equality of the actual normalized conditional integral, not a prescribed
off-path payoff.
-/
theorem lg21_gaussianSignalPosterior_selectedUpperTailMean_eq
    (priorMean priorVariance noiseVariance observedScore cutoff : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          priorMean priorVariance noiseVariance observedScore)
        (Set.Ici cutoff)) =
      (lg21GaussianSignalPosteriorScaleLaw
        priorMean priorVariance noiseVariance observedScore
        hpriorVariance hnoiseVariance).mean +
      (lg21GaussianSignalPosteriorScaleLaw
        priorMean priorVariance noiseVariance observedScore
        hpriorVariance hnoiseVariance).scale *
        standardGaussianHazard
          ((lg21GaussianSignalPosteriorScaleLaw
            priorMean priorVariance noiseVariance observedScore
            hpriorVariance hnoiseVariance).standardize cutoff) := by
  rw [← lg21GaussianSignalPosteriorScaleLaw_toMeasure
    priorMean priorVariance noiseVariance observedScore
    hpriorVariance hnoiseVariance]
  exact lg21_optional_gaussian_upper_closed_tail_conditional_mean_eq _ _

end

end LG21TestOptionalPolicies
