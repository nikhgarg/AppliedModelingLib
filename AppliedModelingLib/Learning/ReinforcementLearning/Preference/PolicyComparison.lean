import AppliedModelingLib.Learning.ReinforcementLearning.Preference.UtilityComparison
import Mathlib.Tactic

/-!
# Order properties of policy-score comparisons

The results in this file are link-agnostic: strict monotonicity is the only
property needed to transfer a score maximizer to a comparison maximizer.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A score maximizer weakly improves every comparison against a fixed opponent
when the comparison link is strictly increasing. -/
theorem scoreMaximizer_policyScoreComparison_dominates
    {Policy : Type*} (link : ℝ → ℝ) (score : Policy → ℝ)
    (maximizer competitor opponent : Policy)
    (hlink : StrictMono link) (hmaximizer : ScoreMaximizer score maximizer) :
    policyScoreComparison link score competitor opponent ≤
      policyScoreComparison link score maximizer opponent := by
  exact hlink.monotone (sub_le_sub_right (hmaximizer competitor) (score opponent))

/-- Every nonempty finite policy class has a scalar-score maximizer. -/
theorem exists_scoreMaximizer {Policy : Type*} [Fintype Policy] [Nonempty Policy]
    (score : Policy → ℝ) : ∃ policy, ScoreMaximizer score policy := by
  obtain ⟨policy, _, hmax⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  exact ⟨policy, fun competitor => hmax competitor (Finset.mem_univ competitor)⟩

end PreferenceRL

end AppliedModelingLib
