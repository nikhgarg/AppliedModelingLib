import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge
import LG21TestOptionalPolicies.FullProfileGaussianMeanLawBridge
import AppliedModelingLib.Foundations.Probability.FiniteGaussianProfileMeanLaw

/-!
# Literal Section 4 Gaussian mean-law bridge for LG21

The Definition 6 access estimator is tied here to the literal finite Gaussian
source.  Its marginal law is derived by one source update from the full
non-test conditional-mean law; the strict marginal comparison is therefore
separate from the fixed-base observable comparison.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- Given a source-derived Gaussian law for the full non-test posterior mean,
the Definition 6 actual-access estimator has the explicit one-step Gaussian
marginal law. -/
theorem lg21D6ActualAccessEstimateLaw_eq_gaussian_of_baseMeanLaw
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (priorMean baseMeanVariance : ℝ)
    (hbaseMeanVariance : 0 ≤ baseMeanVariance)
    (hbaseMeanLaw : S.baseLaw.map S.posteriorBaseMean =
      gaussianReal priorMean baseMeanVariance.toNNReal) :
    lg21D6ActualAccessEstimateLaw S =
      gaussianReal priorMean
        (baseMeanVariance +
          (lg21D6PosteriorTestWeight S)^2 *
            ((S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ))).toNNReal := by
  let residualVariance : ℝ := S.posteriorBaseVariance
  let noiseVariance : ℝ := S.testNoiseVariance
  let scoreVariance : ℝ := residualVariance + noiseVariance
  have hresidualVariance : 0 < residualVariance := by
    exact S.posteriorBaseVariance_pos
  have hnoiseVariance : 0 < noiseVariance := by
    exact S.testNoiseVariance_pos
  have hscoreVariance : 0 < scoreVariance := by
    exact add_pos hresidualVariance hnoiseVariance
  have hconditionalKernel : lg21D6ConditionalGaussianTestKernel S =
      gaussianLocationKernel S.posteriorBaseMean S.posteriorBaseMean_measurable
        scoreVariance.toNNReal := by
    apply Kernel.ext
    intro base
    rw [lg21D6ConditionalGaussianTestKernel_apply,
      gaussianLocationKernel_apply]
    apply (gaussianReal_ext_iff).2
    constructor
    · rfl
    · apply Subtype.ext
      change ((S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ)) =
        (residualVariance + noiseVariance).toNNReal
      rw [Real.toNNReal_of_nonneg hscoreVariance.le]
      rfl
  have hestimate : lg21D6GaussianPBOEstimate S =
      fun baseScore =>
        gaussianSignalWeight residualVariance noiseVariance * baseScore.2 +
          gaussianSignalPriorWeight residualVariance noiseVariance *
            S.posteriorBaseMean baseScore.1 := by
    funext baseScore
    change S.posteriorBaseMean baseScore.1 +
        (residualVariance / (residualVariance + noiseVariance)) *
          (baseScore.2 - S.posteriorBaseMean baseScore.1) =
      (residualVariance / (residualVariance + noiseVariance)) * baseScore.2 +
        (noiseVariance / (residualVariance + noiseVariance)) *
          S.posteriorBaseMean baseScore.1
    field_simp [ne_of_gt hscoreVariance]
    ring
  letI : IsProbabilityMeasure S.baseLaw := S.baseLaw_isProbability
  have hupdate := gaussianLocationKernel_update_mean_map
    S.baseLaw S.posteriorBaseMean S.posteriorBaseMean_measurable
    priorMean baseMeanVariance residualVariance noiseVariance
    hbaseMeanVariance hresidualVariance hnoiseVariance hbaseMeanLaw
  calc
    lg21D6ActualAccessEstimateLaw S =
        (S.baseLaw ⊗ₘ lg21D6ConditionalGaussianTestKernel S).map
          (lg21D6GaussianPBOEstimate S) := rfl
    _ = (S.baseLaw ⊗ₘ gaussianLocationKernel
          S.posteriorBaseMean S.posteriorBaseMean_measurable
          scoreVariance.toNNReal).map
          (fun baseScore =>
            gaussianSignalWeight residualVariance noiseVariance * baseScore.2 +
              gaussianSignalPriorWeight residualVariance noiseVariance *
                S.posteriorBaseMean baseScore.1) := by
          rw [hconditionalKernel, hestimate]
    _ = gaussianReal priorMean
        (baseMeanVariance +
          (gaussianSignalWeight residualVariance noiseVariance)^2 *
            (residualVariance + noiseVariance)).toNNReal := by
          exact hupdate
    _ = gaussianReal priorMean
        (baseMeanVariance +
          (lg21D6PosteriorTestWeight S)^2 *
            ((S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ))).toNNReal := by
          rfl

/-- The Definition 6 actual-access estimator has strictly more marginal
variation than the no-access posterior mean when the optional test has a
positive source noise variance.  This is a comparison of literal measures,
not an inference from fixed-base kernel inequality. -/
theorem lg21D6ActualAccessEstimateLaw_ne_baseMeanLaw
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (priorMean baseMeanVariance : ℝ)
    (hbaseMeanVariance : 0 ≤ baseMeanVariance)
    (hbaseMeanLaw : S.baseLaw.map S.posteriorBaseMean =
      gaussianReal priorMean baseMeanVariance.toNNReal) :
    lg21D6ActualAccessEstimateLaw S ≠ S.baseLaw.map S.posteriorBaseMean := by
  let increment : ℝ :=
    (lg21D6PosteriorTestWeight S)^2 *
      ((S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ))
  have hweight : 0 < lg21D6PosteriorTestWeight S := by
    exact div_pos S.posteriorBaseVariance_pos (lg21D6PosteriorVarianceSum_pos S)
  have hscoreVariance : 0 <
      (S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ) :=
    lg21D6PosteriorVarianceSum_pos S
  have hincrement : 0 < increment := by
    dsimp [increment]
    exact mul_pos (sq_pos_of_pos hweight) hscoreVariance
  have hlt : baseMeanVariance < baseMeanVariance + increment :=
    lt_add_of_pos_right _ hincrement
  have hnn : baseMeanVariance.toNNReal ≠
      (baseMeanVariance + increment).toNNReal := by
    intro heq
    have hcoe := congrArg (fun value : ℝ≥0 => (value : ℝ)) heq
    change (baseMeanVariance.toNNReal : ℝ) =
      ((baseMeanVariance + increment).toNNReal : ℝ) at hcoe
    rw [Real.coe_toNNReal _ hbaseMeanVariance,
      Real.coe_toNNReal _ (le_trans hbaseMeanVariance hlt.le)] at hcoe
    exact (ne_of_lt hlt) hcoe
  intro heq
  apply hnn
  have hgauss : gaussianReal priorMean
      (baseMeanVariance + increment).toNNReal =
        gaussianReal priorMean baseMeanVariance.toNNReal := by
    calc
      gaussianReal priorMean
          (baseMeanVariance + increment).toNNReal =
          lg21D6ActualAccessEstimateLaw S := by
            symm
            simpa [increment] using
              (lg21D6ActualAccessEstimateLaw_eq_gaussian_of_baseMeanLaw
                S priorMean baseMeanVariance hbaseMeanVariance hbaseMeanLaw)
      _ = S.baseLaw.map S.posteriorBaseMean := heq
      _ = gaussianReal priorMean baseMeanVariance.toNNReal := hbaseMeanLaw
  exact ((gaussianReal_ext_iff).1 hgauss |>.2).symm

end

end LG21TestOptionalPolicies
