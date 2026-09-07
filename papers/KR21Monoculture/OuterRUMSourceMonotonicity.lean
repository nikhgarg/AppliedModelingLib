import KR21Monoculture.OuterRUMMonotonicity
import KR21Monoculture.LaplaceSourceNormalization

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Pointwise Definition 1 monotonicity for KR21 outer RUM families

The Appendix-C contraction proofs are fixed-profile theorems.  This module
applies those exact theorems to the conditional Gaussian and source-normalized
Laplace kernels used when the source first samples a value profile from `D`.
It proves pointwise removal monotonicity only; integration over `D` remains in
`OuterRUMMonotonicity.lean` with visible payoff integrability assumptions.
-/

/--
For every source-ordered realized profile, the literal Gaussian source kernel
has the strict-first and weak-after-removal monotonicity required by Definition
1 whenever the algorithm accuracy exceeds the human accuracy.
-/
theorem gaussianThreeCandidateDistributionalFamily_point_removalMonotonicity
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : ValueProfile 1)
    (horder : value (1 : Candidate 1) < value (0 : Candidate 1) ∧
      value (2 : Candidate 1) < value (1 : Candidate 1)) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt
      (gaussianThreeCandidateDistributionalFamily.pointFamily value) thetaA thetaH := by
  exact paper_theorem2_gaussianStd_removalMonotonicity_of_rum_source
    (F := gaussianThreeCandidateDistributionalFamily.pointFamily value)
    (x1 := value (0 : Candidate 1))
    (x2 := value (1 : Candidate 1))
    (x3 := value (2 : Candidate 1))
    rfl rfl rfl horder.1 horder.2
    (by
      intro theta htheta
      rfl)
    thetaA thetaH hthetaH hthetaHA

/--
For every source-ordered realized profile, the literal unit-variance Laplace
kernel has Definition 1 removal monotonicity.  The rate change `sqrt 2 *
theta` is part of the proof, so this does not reuse the old rate-as-accuracy
formalization.
-/
theorem sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_point_removalMonotonicity
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : ValueProfile 1)
    (horder : value (1 : Candidate 1) < value (0 : Candidate 1) ∧
      value (2 : Candidate 1) < value (1 : Candidate 1)) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.pointFamily value)
      thetaA thetaH := by
  refine paper_theorem2_laplacianRate_removalMonotonicity_of_rum_source
    (F := sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.pointFamily value)
    sourceUnitVarianceLaplaceRate
    (fun theta htheta => sourceUnitVarianceLaplaceRate_pos htheta)
    (fun thetaA thetaH _ hthetaHA => sourceUnitVarianceLaplaceRate_lt hthetaHA)
    rfl rfl rfl horder.1 horder.2 ?_ thetaA thetaH hthetaH hthetaHA
  intro theta htheta
  change laplaceThreeCandidateRankingLaw (sourceUnitVarianceLaplaceRate theta)
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1)) =
    theorem7LaplacianDefinition2RankingPMF (sourceUnitVarianceLaplaceRate theta)
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1)) (sourceUnitVarianceLaplaceRate_pos htheta)
  exact laplaceThreeCandidateRankingLaw_eq_of_pos
    (sourceUnitVarianceLaplaceRate_pos htheta)

end KR21Monoculture
