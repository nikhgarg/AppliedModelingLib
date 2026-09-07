import KR21Monoculture.OuterRUMSourceMeasurability
import KR21Monoculture.OuterRUMSourceConcentration
import KR21Monoculture.OuterRUMTheorem1Positive
import KR21Monoculture.OuterRUMSourceMonotonicity

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace KR21Monoculture

/-!
# Concrete outer-D Theorem 1 targets for the KR21 RUM sources

This module closes the outer-lift obligations for the literal Gaussian and
source-normalized Laplace three-candidate families from the source's fixed
rank-labelled support convention, coordinatewise first moments, and a
positive human accuracy.  The proof keeps the finite ranking-kernel,
concentration, Definition-2/3, and Definition-1 transports separate.
-/

/-- Gaussian score variance is invariant under a sign change of the displayed
standard-deviation parameter. -/
theorem gaussianThreeCandidateRankingLaw_neg
    (theta x1 x2 x3 : ℝ) :
    gaussianThreeCandidateRankingLaw (-theta) x1 x2 x3 =
      gaussianThreeCandidateRankingLaw theta x1 x2 x3 := by
  simp [gaussianThreeCandidateRankingLaw,
    theorem8GaussianDefinition2ScoreMeasureStd,
    theorem8GaussianPairMeasureStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.gaussianVarianceFromStd]

/-- At the totalized zero Gaussian accuracy, all scores equal their value
coordinates and the induced PMF is the deterministic score ranking. -/
theorem gaussianThreeCandidateRankingLaw_zero
    (x1 x2 x3 : ℝ) :
    gaussianThreeCandidateRankingLaw 0 x1 x2 x3 =
      PMF.pure (rum3RankByScores x1 x2 x3) := by
  unfold gaussianThreeCandidateRankingLaw rumRankingPMFOfMeasure
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
  simp [theorem8GaussianDefinition2ScoreMeasureStd,
    theorem8GaussianPairMeasureStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    theorem8GaussianVarianceFromStd,
    AppliedModelingLib.Probability.gaussianVarianceFromStd,
    Measure.dirac_prod_dirac]
  congr 1

/-- The deterministic score ranking at zero Gaussian accuracy is Borel in the
outer value profile. -/
noncomputable def gaussianZeroAccuracyRanking
    (value : ValueProfile 1) : Ranking 1 :=
  rum3RankByScores
    (value (0 : Candidate 1)) (value (1 : Candidate 1))
    (value (2 : Candidate 1))

theorem measurable_gaussianZeroAccuracyRanking :
    Measurable gaussianZeroAccuracyRanking := by
  exact rum3RankByScoreFns_measurable
    (measurable_pi_apply (0 : Candidate 1))
    (measurable_pi_apply (1 : Candidate 1))
    (measurable_pi_apply (2 : Candidate 1))

theorem measurable_gaussianZeroAccuracy_rankingAtom (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((PMF.pure (gaussianZeroAccuracyRanking value) : PMF (Ranking 1)) pi).toReal) :=
  (measurable_of_finite fun ranking : Ranking 1 =>
    ((PMF.pure ranking : PMF (Ranking 1)) pi).toReal).comp
      measurable_gaussianZeroAccuracyRanking

/-- Every totalized Gaussian source atom is Borel in the outer profile.  The
positive branch uses the score-density kernel; the negative branch follows
from the variance symmetry, and the zero branch from the explicit Dirac score
law. -/
theorem measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
    (theta : ℝ) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal) := by
  by_cases htheta : 0 < theta
  · exact measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom
      htheta pi
  by_cases hzero : theta = 0
  · subst theta
    convert measurable_gaussianZeroAccuracy_rankingAtom pi using 1
    funext value
    rw [gaussianThreeCandidateDistributionalFamily_dist,
      gaussianThreeCandidateRankingLaw_zero]
    rfl
  · have hneg : 0 < -theta := by
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt htheta) hzero)
    have hmeas :=
      measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom hneg pi
    convert hmeas using 1
    funext value
    exact congrArg (fun law : PMF (Ranking 1) => (law pi).toReal)
      (gaussianThreeCandidateRankingLaw_neg theta
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))).symm

theorem aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
    (D : Measure (ValueProfile 1)) (theta : ℝ) (pi : Ranking 1) :
    AEStronglyMeasurable (fun value : ValueProfile 1 =>
      ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal) D :=
  (measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all theta pi).aestronglyMeasurable

/-- Every totalized source-normalized Laplace atom is Borel in the outer
profile.  Outside its positive-rate source domain the implementation is the
explicit pure-ranking fallback, rather than an unverified density. -/
theorem measurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
    (theta : ℝ) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal) := by
  by_cases htheta : 0 < theta
  · exact
      measurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom
        htheta pi
  · have hrate : ¬ 0 < sourceUnitVarianceLaplaceRate theta := by
      dsimp [sourceUnitVarianceLaplaceRate]
      exact not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_not_gt htheta))
    convert (measurable_const : Measurable fun _ : ValueProfile 1 =>
      ((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal) using 1
    funext value
    simp [sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_dist,
      laplaceThreeCandidateRankingLaw, htheta]

theorem aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
    (D : Measure (ValueProfile 1)) (theta : ℝ) (pi : Ranking 1) :
    AEStronglyMeasurable (fun value : ValueProfile 1 =>
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal) D :=
  (measurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
    theta pi).aestronglyMeasurable

/-- Coordinatewise first moments make the outer first-mover payoff integrable
for every totalized Gaussian source kernel. -/
theorem gaussian_outer_firstMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedFirstMoverUtility
      (gaussianThreeCandidateDistributionalFamily.dist theta value) value) D := by
  simpa [expectedFirstMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D gaussianThreeCandidateDistributionalFamily.dist theta firstChoice hvalue
      (fun pi =>
        aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi))

/-- Coordinatewise first moments make the outer shared-second payoff
integrable for every totalized Gaussian source kernel. -/
theorem gaussian_outer_sharedSecondMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverShared
      (gaussianThreeCandidateDistributionalFamily.dist theta value) value) D := by
  simpa [expectedSecondMoverShared] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D gaussianThreeCandidateDistributionalFamily.dist theta secondChoice hvalue
      (fun pi =>
        aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi))

/-- Coordinatewise first moments make every ordered pair of Gaussian source
ranking laws integrable in the second-mover payoff. -/
theorem gaussian_outer_independentSecondMover_integrable
    (D : Measure (ValueProfile 1)) (thetaSecond thetaFirst : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      (gaussianThreeCandidateDistributionalFamily.dist thetaSecond value)
      (gaussianThreeCandidateDistributionalFamily.dist thetaFirst value) value) D := by
  simpa [expectedSecondMoverIndependent, secondMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
      D
      (fun value => gaussianThreeCandidateDistributionalFamily.dist thetaSecond value)
      (fun value => gaussianThreeCandidateDistributionalFamily.dist thetaFirst value)
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
      (fun pi =>
        aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
          D thetaSecond pi)
      (fun pi =>
        aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
          D thetaFirst pi))

/-- Coordinatewise first moments make the outer first-mover payoff integrable
for every totalized source-normalized Laplace kernel. -/
theorem sourceUnitVarianceLaplace_outer_firstMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedFirstMoverUtility
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) value) D := by
  simpa [expectedFirstMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta firstChoice hvalue
      (fun pi =>
        aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi))

/-- Coordinatewise first moments make the outer shared-second payoff
integrable for every totalized source-normalized Laplace kernel. -/
theorem sourceUnitVarianceLaplace_outer_sharedSecondMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverShared
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) value) D := by
  simpa [expectedSecondMoverShared] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta secondChoice hvalue
      (fun pi =>
        aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi))

/-- Coordinatewise first moments make every ordered pair of source-normalized
Laplace kernels integrable in the second-mover payoff. -/
theorem sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
    (D : Measure (ValueProfile 1)) (thetaSecond thetaFirst : ℝ)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaSecond value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaFirst value) value) D := by
  simpa [expectedSecondMoverIndependent, secondMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
      D
      (fun value =>
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaSecond value)
      (fun value =>
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaFirst value)
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
      (fun pi =>
        aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
          D thetaSecond pi)
      (fun pi =>
        aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
          D thetaFirst pi))

/-- The two pure-ranking terms in the high-accuracy limit are integrable from
coordinatewise first moments alone. -/
theorem outer_pureRanking_firstMover_integrable
    (D : Measure (ValueProfile 1)) (center : Ranking 1)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedFirstMoverUtility
      (PMF.pure center) value) D := by
  simpa [expectedFirstMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D (fun _ _ => PMF.pure center) 0 firstChoice hvalue
      (fun _ => aestronglyMeasurable_const))

theorem outer_pureRanking_sharedSecondMover_integrable
    (D : Measure (ValueProfile 1)) (center : Ranking 1)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverShared
      (PMF.pure center) value) D := by
  simpa [expectedSecondMoverShared] using
    (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
      D (fun _ _ => PMF.pure center) 0 secondChoice hvalue
      (fun _ => aestronglyMeasurable_const))

theorem gaussian_outer_humanAgainstPureSecondMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ) (center : Ranking 1)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      (gaussianThreeCandidateDistributionalFamily.dist theta value)
      (PMF.pure center) value) D := by
  simpa [expectedSecondMoverIndependent, secondMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
      D (fun value => gaussianThreeCandidateDistributionalFamily.dist theta value)
      (fun _ => PMF.pure center)
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
      (fun pi =>
        aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi)
      (fun _ => aestronglyMeasurable_const))

theorem sourceUnitVarianceLaplace_outer_humanAgainstPureSecondMover_integrable
    (D : Measure (ValueProfile 1)) (theta : ℝ) (center : Ranking 1)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
      (PMF.pure center) value) D := by
  simpa [expectedSecondMoverIndependent, secondMoverUtility] using
    (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
      D
      (fun value => sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
      (fun _ => PMF.pure center)
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
      (fun pi =>
        aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
          D theta pi)
      (fun _ => aestronglyMeasurable_const))

/-- The literal Gaussian three-candidate source model satisfies the full
outer-D Theorem 1 target on the source's fixed ordered cone.  No outer payoff
integrability or crossing certificate is accepted as an input: every such
fact is derived above from coordinatewise first moments and semantic ranking
atom measurability. -/
theorem gaussianThreeCandidateDistributionalFamily_outer_theorem1
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    gaussianThreeCandidateDistributionalFamily.DistributionalTheorem1Target D thetaH := by
  apply DistributionalAccuracyFamily.distributional_theorem1_of_outer_atomwise_regular_positive
    gaussianThreeCandidateDistributionalFamily D thetaH rum3Ranking012 hthetaH hvalue
  · intro theta pi
    exact
      aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom_all
        D theta pi
  · intro value pi theta htheta
    exact gaussianThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
      htheta value pi
  · exact gaussianThreeCandidate_ae_atomwise_tendsto_pure012_of_source_order D horder
  · apply DistributionalAccuracyFamily.prefersIndependentReranking_of_ae_pointwise
      gaussianThreeCandidateDistributionalFamily D thetaH
      (gaussian_outer_sharedSecondMover_integrable D thetaH hvalue)
      (gaussian_outer_independentSecondMover_integrable D thetaH thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact gaussianThreeCandidate_prefersIndependent
      hthetaH hvalue_order.1 hvalue_order.2
  · apply DistributionalAccuracyFamily.theorem1_pureCenterLimit_gap_of_ae_pointwise
      gaussianThreeCandidateDistributionalFamily D thetaH rum3Ranking012
      (gaussian_outer_firstMover_integrable D thetaH hvalue)
      (gaussian_outer_humanAgainstPureSecondMover_integrable
        D thetaH rum3Ranking012 hvalue)
      (outer_pureRanking_firstMover_integrable D rum3Ranking012 hvalue)
      (outer_pureRanking_sharedSecondMover_integrable D rum3Ranking012 hvalue)
      (ae_strictlyOrderedBy_rum3Ranking012_of_source_order D horder)
    filter_upwards [horder] with value hvalue_order
    exact gaussianThreeCandidate_prefersIndependent
      hthetaH hvalue_order.1 hvalue_order.2
  · intro thetaA hthetaHA
    apply DistributionalAccuracyFamily.prefersWeakerCompetition_of_ae_pointwise
      gaussianThreeCandidateDistributionalFamily D thetaA thetaH
      (gaussian_outer_independentSecondMover_integrable D thetaH thetaA hvalue)
      (gaussian_outer_independentSecondMover_integrable D thetaH thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact gaussianThreeCandidate_prefersWeaker
      hthetaH hthetaHA hvalue_order.1 hvalue_order.2
  · intro thetaA hthetaHA
    apply DistributionalAccuracyFamily.outer_algorithmAgainstHuman_gt_h_of_ae_removalMonotonicity
      gaussianThreeCandidateDistributionalFamily D thetaA thetaH
      (gaussian_outer_firstMover_integrable D thetaH hvalue)
      (gaussian_outer_independentSecondMover_integrable D thetaH thetaH hvalue)
      (gaussian_outer_firstMover_integrable D thetaA hvalue)
      (gaussian_outer_independentSecondMover_integrable D thetaA thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact gaussianThreeCandidateDistributionalFamily_point_removalMonotonicity
      hthetaH hthetaHA value hvalue_order

/-- The literal source-normalized unit-variance Laplace three-candidate model
satisfies the same full outer-D Theorem 1 target.  Its `sqrt 2 * theta` rate
conversion is retained through the atom, preference, concentration, and
removal-monotonicity components. -/
theorem sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_outer_theorem1
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.DistributionalTheorem1Target
      D thetaH := by
  apply DistributionalAccuracyFamily.distributional_theorem1_of_outer_atomwise_regular_positive
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH
    rum3Ranking012 hthetaH hvalue
  · intro theta pi
    exact
      aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom_all
        D theta pi
  · intro value pi theta htheta
    exact sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
      htheta value pi
  · exact
      sourceUnitVarianceLaplaceThreeCandidate_ae_atomwise_tendsto_pure012_of_source_order
        D horder
  · apply DistributionalAccuracyFamily.prefersIndependentReranking_of_ae_pointwise
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH
      (sourceUnitVarianceLaplace_outer_sharedSecondMover_integrable D thetaH hvalue)
      (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
        D thetaH thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent
      hthetaH hvalue_order.1 hvalue_order.2
  · apply DistributionalAccuracyFamily.theorem1_pureCenterLimit_gap_of_ae_pointwise
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH rum3Ranking012
      (sourceUnitVarianceLaplace_outer_firstMover_integrable D thetaH hvalue)
      (sourceUnitVarianceLaplace_outer_humanAgainstPureSecondMover_integrable
        D thetaH rum3Ranking012 hvalue)
      (outer_pureRanking_firstMover_integrable D rum3Ranking012 hvalue)
      (outer_pureRanking_sharedSecondMover_integrable D rum3Ranking012 hvalue)
      (ae_strictlyOrderedBy_rum3Ranking012_of_source_order D horder)
    filter_upwards [horder] with value hvalue_order
    exact sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent
      hthetaH hvalue_order.1 hvalue_order.2
  · intro thetaA hthetaHA
    apply DistributionalAccuracyFamily.prefersWeakerCompetition_of_ae_pointwise
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaA thetaH
      (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
        D thetaH thetaA hvalue)
      (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
        D thetaH thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact sourceUnitVarianceLaplaceThreeCandidate_prefersWeaker
      hthetaH hthetaHA hvalue_order.1 hvalue_order.2
  · intro thetaA hthetaHA
    apply DistributionalAccuracyFamily.outer_algorithmAgainstHuman_gt_h_of_ae_removalMonotonicity
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaA thetaH
      (sourceUnitVarianceLaplace_outer_firstMover_integrable D thetaH hvalue)
      (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
        D thetaH thetaH hvalue)
      (sourceUnitVarianceLaplace_outer_firstMover_integrable D thetaA hvalue)
      (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
        D thetaA thetaH hvalue)
    filter_upwards [horder] with value hvalue_order
    exact sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_point_removalMonotonicity
      hthetaH hthetaHA value hvalue_order

end KR21Monoculture
