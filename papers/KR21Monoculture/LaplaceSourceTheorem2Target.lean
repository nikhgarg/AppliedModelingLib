import KR21Monoculture.LaplaceSourceNormalization

/-!
# Source-normalized Laplace fixed-profile Theorem 2 endpoint

The source fixes a unit-variance Laplace innovation and ranks
`x_i + epsilon_i / theta`.  The repository's canonical Laplace construction
is parameterized by rate, so the literal source parameter has rate
`sqrt 2 * theta`.  `LaplaceSourceNormalization` already proves the fixed-
profile Definition 2 and Definition 3 comparisons at that rate.  This module
closes the remaining fixed-profile Theorem 2 route by proving the elementary
rate regularity required by the existing source-model Theorem 1 bridge.

This is deliberately a fixed value-profile result.  It neither introduces an
outer candidate distribution nor treats the paper's separate outer-law
regularity boundary as discharged.
-/

open AppliedModelingLib Filter Topology

namespace KR21Monoculture

/-- The source-normalized Laplace rate is continuous at every accuracy. -/
theorem sourceUnitVarianceLaplaceRate_continuous :
    Continuous sourceUnitVarianceLaplaceRate := by
  simpa [sourceUnitVarianceLaplaceRate] using
    (continuous_const.mul continuous_id :
      Continuous (fun theta : ℝ => Real.sqrt 2 * theta))

/-- The source-normalized Laplace rate diverges with the source accuracy. -/
theorem sourceUnitVarianceLaplaceRate_tendsto_atTop :
    Tendsto sourceUnitVarianceLaplaceRate atTop atTop := by
  simpa [sourceUnitVarianceLaplaceRate] using
    (Tendsto.const_mul_atTop (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
      tendsto_id : Tendsto (fun theta : ℝ => Real.sqrt 2 * theta) atTop atTop)

/-- The fixed-profile member of the source-normalized Laplace RUM family. -/
noncomputable def sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily
    (x1 x2 x3 : ℝ) : AccuracyFamily 1 where
  dist := fun theta =>
    sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3
  value := threeCandidateValueProfile x1 x2 x3

/--
The source-normalized fixed three-candidate Laplace RUM satisfies the complete
fixed-profile Theorem 1 target at every positive human accuracy.  The value
order is the source's standing `x_1 > x_2 > x_3` convention; the only rate
facts used are derived above from the visible `sqrt 2 * theta` conversion.
-/
theorem sourceUnitVarianceLaplaceThreeCandidate_theorem1Target
    {thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    AccuracyFamily.Theorem1Target
      (sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily x1 x2 x3)
      thetaH := by
  let F : AccuracyFamily 1 :=
    sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily x1 x2 x3
  change AccuracyFamily.Theorem1Target F thetaH
  refine paper_theorem2_laplacianRate_target_from_continuous_rum_source
    (F := F)
    sourceUnitVarianceLaplaceRate
    (fun _ htheta => sourceUnitVarianceLaplaceRate_pos htheta)
    (fun _ _ _ hthetaHA => sourceUnitVarianceLaplaceRate_lt hthetaHA)
    (fun _ _ => sourceUnitVarianceLaplaceRate_continuous.continuousAt)
    sourceUnitVarianceLaplaceRate_tendsto_atTop
    hthetaH
    (by simp [F, sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily,
      threeCandidateValueProfile])
    (by simp [F, sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily,
      threeCandidateValueProfile])
    (by simp [F, sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily,
      threeCandidateValueProfile])
    hx12 hx23 ?_
  intro theta htheta
  simpa [F, sourceUnitVarianceLaplaceThreeCandidateAccuracyFamily,
    sourceUnitVarianceLaplaceThreeCandidateRankingLaw] using
    (laplaceThreeCandidateRankingLaw_eq_of_pos
      (sourceUnitVarianceLaplaceRate_pos htheta))

end KR21Monoculture
