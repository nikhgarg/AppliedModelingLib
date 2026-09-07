import Mathlib.Analysis.SpecialFunctions.Sigmoid
import AppliedModelingLib.Learning.HumanFeedback.PairwisePreference
import AppliedModelingLib.Learning.HumanFeedback.RewardEquivalence

/-!
# Bradley--Terry preferences

This module instantiates a valid pairwise-preference model from a real-valued
reward using Mathlib's sigmoid.  Reusing `Real.sigmoid` keeps its analytic and
order theory in one canonical place.

## Main declarations

- `bradleyTerryPreference`
- `bradleyTerryPreference_invariant`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- The Bradley--Terry preference probability induced by a reward difference. -/
noncomputable def bradleyTerryPreference {Context Response : Type*}
    (reward : Context → Response → ℝ) : PairwisePreference Context Response where
  prob context first second := Real.sigmoid (reward context first - reward context second)
  nonneg context first second := Real.sigmoid_nonneg _
  le_one context first second := Real.sigmoid_le_one _
  complementary := by
    intro context first second
    have hneg : reward context second - reward context first =
        -(reward context first - reward context second) := by
      ring
    rw [hneg, Real.sigmoid_neg]
    ring

/-- Bradley--Terry preferences are unchanged by a context-only reward shift. -/
theorem bradleyTerryPreference_invariant {Context Response : Type*}
    {first second : Context → Response → ℝ}
    (h : RewardEquivalent first second) :
    bradleyTerryPreference first = bradleyTerryPreference second := by
  rcases h with ⟨shift, hshift⟩
  apply PairwisePreference.ext
  funext context left right
  change Real.sigmoid (first context left - first context right) =
    Real.sigmoid (second context left - second context right)
  rw [hshift context left, hshift context right]
  congr 1
  ring

end HumanFeedback
end Learning
end AppliedModelingLib
