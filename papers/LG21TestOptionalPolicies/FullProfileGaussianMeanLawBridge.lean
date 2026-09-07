import LG21TestOptionalPolicies.FullProfileGaussianSequentialBridge
import AppliedModelingLib.Foundations.Probability.FiniteGaussianProfileMeanLaw

/-!
# Literal full-profile posterior-mean law for LG21

This module instantiates the generic finite Gaussian source-law induction for
the literal full non-test LG21 profile.  It supplies the missing marginal law
of the derived base posterior mean without naming that mean in the source
model or assuming a model-law equality.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The literal full non-test LG21 source profile has a source-derived
Gaussian conditional factorization, and the pushforward of its derived
conditional mean is a Gaussian law. -/
theorem lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance baseMeanVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧ 0 ≤ baseMeanVariance ∧
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        baseLaw.map baseMean =
          gaussianReal M.priorMean baseMeanVariance.toNNReal := by
  rcases gaussianFiniteProfileLatentLaw_exists_gaussianLocationFactorization_with_meanLaw
        M.priorMean (M.priorVariance : ℝ) hpriorVariance
        (fun feature : LG21NonTestFeature Feature testFeature =>
          (M.noiseVariance feature.1 : ℝ)) hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hmeanLaw⟩
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
    hbaseLaw, hbaseVariance, hbaseMeanVariance, ?_, hmeanLaw⟩
  simpa [lg21ContinuousGaussianFullBaseLatentPrimitiveLaw,
    gaussianFiniteProfileLatentLaw,
    lg21ContinuousGaussianNonTestNoiseLaw, Real.toNNReal_coe] using
    hfactorization

end

end LG21TestOptionalPolicies
