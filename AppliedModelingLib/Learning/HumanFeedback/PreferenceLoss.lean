import Mathlib.Analysis.SpecialFunctions.Log.Basic
import AppliedModelingLib.Learning.HumanFeedback.PairwisePreference

/-!
# Pairwise preference log loss

Finite real log losses are meaningful only when the preference model assigns
strictly positive probability to each observed chosen response.  This module
makes that support condition an explicit argument instead of relying on
`Real.log 0`'s algebraic convention.

## Main declarations

- `PairwisePreference.PositiveAt`
- `PairwisePreference.PositiveOnDataset`
- `pairwiseNegativeLogLikelihood`
- `pairwiseDatasetNegativeLogLikelihood`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- A preference model assigns positive probability to the chosen response in one observation. -/
def PairwisePreference.PositiveAt {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (observation : PairwiseObservation Context Response) : Prop :=
  0 < preference.prob observation.context observation.chosen observation.rejected

/-- A preference model is positive on every observation in a dataset. -/
def PairwisePreference.PositiveOnDataset {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (dataset : PairwiseDataset Context Response) : Prop :=
  ∀ observation ∈ dataset, preference.PositiveAt observation

/-- Negative log likelihood of one recorded pairwise choice. -/
noncomputable def pairwiseNegativeLogLikelihood {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (observation : PairwiseObservation Context Response)
    (_hpositive : preference.PositiveAt observation) : ℝ :=
  -Real.log (preference.prob observation.context observation.chosen observation.rejected)

/-- A valid pairwise-preference model has nonnegative negative log likelihood. -/
theorem pairwiseNegativeLogLikelihood_nonneg {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (observation : PairwiseObservation Context Response)
    (hpositive : preference.PositiveAt observation) :
    0 ≤ pairwiseNegativeLogLikelihood preference observation hpositive := by
  unfold pairwiseNegativeLogLikelihood
  apply neg_nonneg.mpr
  exact Real.log_nonpos hpositive.le
    (preference.le_one observation.context observation.chosen observation.rejected)

/-- Sum of negative log likelihoods for a dataset with an explicit positivity certificate. -/
noncomputable def pairwiseDatasetNegativeLogLikelihood {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (dataset : PairwiseDataset Context Response)
    (hpositive : preference.PositiveOnDataset dataset) : ℝ :=
  (dataset.map fun observation =>
    -Real.log (preference.prob observation.context observation.chosen observation.rejected)).sum

/-- Dataset negative log likelihood is nonnegative under its positivity certificate. -/
theorem pairwiseDatasetNegativeLogLikelihood_nonneg {Context Response : Type*}
    (preference : PairwisePreference Context Response)
    (dataset : PairwiseDataset Context Response)
    (hpositive : preference.PositiveOnDataset dataset) :
    0 ≤ pairwiseDatasetNegativeLogLikelihood preference dataset hpositive := by
  unfold pairwiseDatasetNegativeLogLikelihood
  induction dataset with
  | nil => simp
  | cons observation dataset ih =>
    simp only [List.map_cons, List.sum_cons]
    refine add_nonneg ?_ ?_
    · apply neg_nonneg.mpr
      exact Real.log_nonpos (hpositive observation (by simp)).le
        (preference.le_one observation.context observation.chosen observation.rejected)
    · apply ih
      intro tailObservation hmem
      exact hpositive tailObservation (by simp [hmem])

end HumanFeedback
end Learning
end AppliedModelingLib
