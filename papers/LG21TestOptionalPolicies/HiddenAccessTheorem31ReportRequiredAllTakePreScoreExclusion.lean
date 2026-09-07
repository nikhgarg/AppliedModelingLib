import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredAllTakeFibreCloseout

/-!
# Pre-score exclusion of the all-taking branch

The report-required policy has one strategic choice: taking before the score
draw.  These lemmas rule out a locally all-taking action only from that
pre-score best response and a positive strict-gain set for declining the test.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- An a.e. all-taking action is incompatible with a positive-mass set on
which the literal pre-score taking payoff is strictly below the outside
no-take payoff. -/
theorem lg21_not_ae_allTake_of_preScore_bestResponse_and_positive_noTakeGain
    {Skill : Type*} [MeasurableSpace Skill]
    (law : Measure Skill) (take : Skill -> Bool)
    (takePayoff : Skill -> ℝ) (outside : ℝ)
    (hbest : NoProfitableBinaryChoiceDeviationAE law
      (fun skill => take skill = true) takePayoff (fun _ => outside))
    (hnoTakeGain : 0 < law {skill | takePayoff skill < outside}) :
    ¬ ∀ᵐ skill ∂law, take skill = true := by
  intro hallTake
  have htakeValue : ∀ᵐ skill ∂law, outside ≤ takePayoff skill := by
    filter_upwards [hbest.1, hallTake] with skill hbestAt htake
    exact hbestAt htake
  have hnoTakeGainZero : law {skill | takePayoff skill < outside} = 0 := by
    simpa only [ae_iff, not_le] using htakeValue
  exact (ne_of_gt hnoTakeGain) hnoTakeGainZero

/-- The canonical unselected Gaussian expected-posterior affine payoff agrees
with the base mean at the conditional latent mean. -/
theorem lg21_gaussianSignal_expectedPosterior_at_baseMean
    (baseMean priorVariance noiseVariance : ℝ)
    (hvariance : priorVariance + noiseVariance ≠ 0) :
    gaussianSignalPriorWeight priorVariance noiseVariance * baseMean +
        gaussianSignalWeight priorVariance noiseVariance * baseMean = baseMean := by
  dsimp [gaussianSignalPriorWeight, gaussianSignalWeight]
  field_simp [hvariance]
  ring

/-- A nondegenerate Gaussian lower tail is a positive strict no-take-gain set
for an affine expected taking payoff that crosses the outside payoff at the
conditional mean. -/
theorem lg21_not_ae_allTake_of_gaussianAffine_preScore_bestResponse
    (mean : ℝ) (variance : NNReal)
    (take : ℝ -> Bool) (intercept slope outside : ℝ)
    (hvariance : variance ≠ 0)
    (hslope : 0 < slope)
    (hcenter : intercept + slope * mean = outside)
    (hbest : NoProfitableBinaryChoiceDeviationAE (gaussianReal mean variance)
      (fun skill => take skill = true)
      (fun skill => intercept + slope * skill) (fun _ => outside)) :
    ¬ ∀ᵐ skill ∂gaussianReal mean variance, take skill = true := by
  apply lg21_not_ae_allTake_of_preScore_bestResponse_and_positive_noTakeGain
    (gaussianReal mean variance) take
    (fun skill => intercept + slope * skill) outside hbest
  have htail : 0 < gaussianReal mean variance (Set.Iio mean) :=
    lg21_gaussianReal_Iio_pos mean mean hvariance
  apply lt_of_lt_of_le htail
  apply measure_mono
  intro skill hskill
  change skill < mean at hskill
  change intercept + slope * skill < outside
  calc
    intercept + slope * skill < intercept + slope * mean := by nlinarith
    _ = outside := hcenter

end

end LG21TestOptionalPolicies
