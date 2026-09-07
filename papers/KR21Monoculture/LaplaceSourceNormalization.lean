import KR21Monoculture.Theorem2OuterConditionalSource
import KR21Monoculture.LaplaceUnitVariance

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Source-normalized Laplace RUM for KR21 Theorem 2

The canonical `laplaceThreeCandidateRankingLaw` uses its first argument as a
Laplace *rate*.  The source instead fixes a unit-variance Laplace base noise
`epsilon` and ranks `x + epsilon / theta`.  A centered Laplace law of rate
`lambda` has variance `2 / lambda^2`; consequently the score noise in the
source convention has rate `sqrt 2 * theta`.

This module makes that change of parameter explicit.  It deliberately leaves
the older canonical-rate family untouched, so no source normalization is
silently smuggled into its existing theorems.  The conclusions below reuse the
already-proved three-candidate Laplace comparisons only after proving that the
converted rate is positive and preserves strict accuracy order.
-/

/-- The literal source base-noise law has unit variance at the chosen
`sqrt 2` rate.  This is the calibration fact behind the source rate conversion,
not merely a naming convention. -/
theorem sourceUnitVarianceLaplaceBaseNoiseLaw_variance_one :
    Var[id; w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity] = 1 := by
  change Var[id; theorem7LaplaceMeasure (Real.sqrt 2) 0] = 1
  exact sourceUnitVarianceLaplaceBaseNoise_variance_one

/-- The Laplace rate induced by the source's unit-variance base noise and its
accuracy parameter `theta`. -/
noncomputable def sourceUnitVarianceLaplaceRate (theta : ℝ) : ℝ :=
  Real.sqrt 2 * theta

@[simp] theorem sourceUnitVarianceLaplaceRate_apply (theta : ℝ) :
    sourceUnitVarianceLaplaceRate theta = Real.sqrt 2 * theta := rfl

theorem sourceUnitVarianceLaplaceRate_pos {theta : ℝ} (htheta : 0 < theta) :
    0 < sourceUnitVarianceLaplaceRate theta := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta

theorem sourceUnitVarianceLaplaceRate_lt {thetaH thetaA : ℝ}
    (hthetaHA : thetaH < thetaA) :
    sourceUnitVarianceLaplaceRate thetaH < sourceUnitVarianceLaplaceRate thetaA := by
  exact mul_lt_mul_of_pos_left hthetaHA (Real.sqrt_pos.2 (by norm_num))

/-- The source-normalized three-candidate Laplace ranking law.  For positive
`theta`, this is the same concrete Laplace score law as the canonical
implementation, at the explicitly converted rate `sqrt 2 * theta`. -/
noncomputable def sourceUnitVarianceLaplaceThreeCandidateRankingLaw
    (theta x1 x2 x3 : ℝ) : PMF (Ranking 1) :=
  laplaceThreeCandidateRankingLaw (sourceUnitVarianceLaplaceRate theta) x1 x2 x3

/-- The source's Laplace RUM family over realized three-candidate profiles.
The `sqrt 2` factor is part of the definition, rather than an unstated
parameter convention in a proof. -/
noncomputable def sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily :
    DistributionalAccuracyFamily 1 where
  dist := fun theta value =>
    sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))

@[simp] theorem sourceUnitVarianceLaplaceThreeCandidateRankingLaw_eq
    (theta x1 x2 x3 : ℝ) :
    sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3 =
      laplaceThreeCandidateRankingLaw (Real.sqrt 2 * theta) x1 x2 x3 := rfl

@[simp] theorem sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_dist
    (theta : ℝ) (value : ValueProfile 1) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value =
      laplaceThreeCandidateRankingLaw (Real.sqrt 2 * theta)
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) := rfl

/-- The fixed-profile Definition-2 comparison at the source-normalized
Laplace parameter. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  exact laplaceThreeCandidate_prefersIndependent
    (sourceUnitVarianceLaplaceRate_pos htheta) hx12 hx23

/-- The fixed-profile Definition-3 comparison at the source-normalized
Laplace parameter. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_prefersWeaker
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaA x1 x2 x3)
      (sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaH x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  exact laplaceThreeCandidate_prefersWeaker
    (sourceUnitVarianceLaplaceRate_pos hthetaH)
    (sourceUnitVarianceLaplaceRate_lt hthetaHA) hx12 hx23

/-- The source-normalized Laplace Appendix-C Definition-2 result, averaged
over an arbitrary outer probability law.  The outer integrability assumptions
are retained verbatim for the source-normalized family. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_outer_prefersIndependentReranking
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hshared : Integrable (fun value => expectedSecondMoverShared
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
      value) D)
    (hindependent : Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
      value) D) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.PrefersIndependentReranking
      D theta := by
  apply DistributionalAccuracyFamily.prefersIndependentReranking_of_ae_pointwise
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta hshared hindependent
  filter_upwards [horder] with value hvalue
  exact sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

/-- The source-normalized Laplace Appendix-C Definition-3 result, averaged
over an arbitrary outer probability law. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_outer_prefersWeakerCompetition
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hbetter : Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaA value)
      value) D)
    (hworse : Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
      value) D) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.PrefersWeakerCompetition
      D thetaA thetaH := by
  apply DistributionalAccuracyFamily.prefersWeakerCompetition_of_ae_pointwise
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaA thetaH hbetter hworse
  filter_upwards [horder] with value hvalue
  exact sourceUnitVarianceLaplaceThreeCandidate_prefersWeaker
    hthetaH hthetaHA hvalue.1 hvalue.2

/-- Definition 2 in the literal source experiment: draw a value profile from
`D`, then draw two conditionally iid rankings from the source-normalized
Laplace law.  The conditioning event has positive mass because strict
pointwise preference implies nonzero top disagreement. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_outer_jointLawDisagreementConditionalGain_pos
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta) :
    0 < (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain D theta
        regularity.base.ranking_atom_measurable) := by
  apply DistributionalAccuracyFamily.jointLawDisagreementConditionalGain_pos_of_ae_pointwise_preference
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta regularity
  filter_upwards [horder] with value hvalue
  exact sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

end KR21Monoculture
