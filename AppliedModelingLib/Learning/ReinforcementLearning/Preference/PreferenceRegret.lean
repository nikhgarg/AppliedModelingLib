import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PolicyComparison
import Mathlib.Tactic

/-!
# Pairwise preference objectives and score regret

These finite-list definitions are shared by policy-comparison analyses.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A candidate's total centered comparison value against a finite sequence of
played policy pairs. -/
noncomputable def pairwisePreferenceObjective {Policy : Type*} (link : ℝ → ℝ) (score : Policy → ℝ)
    (candidate : Policy) (played : List (Policy × Policy)) : ℝ :=
  (played.map fun pair =>
    (policyScoreComparison link score candidate pair.1 +
      policyScoreComparison link score candidate pair.2 - 1) / 2).sum

/-- The finite cumulative average score gap of played policy pairs from a
benchmark policy. -/
noncomputable def pairwiseScoreRegret {Policy : Type*} (score : Policy → ℝ) (benchmark : Policy)
    (played : List (Policy × Policy)) : ℝ :=
  (played.map fun pair =>
    (2 * score benchmark - score pair.1 - score pair.2) / 2).sum

/-- A score maximizer dominates the sum of two linked comparisons. -/
theorem scoreMaximizer_pairwiseSum_dominates {Policy : Type*}
    (link : ℝ → ℝ) (score : Policy → ℝ)
    (maximizer competitor firstOpponent secondOpponent : Policy)
    (hlink : StrictMono link) (hmaximizer : ScoreMaximizer score maximizer) :
    policyScoreComparison link score competitor firstOpponent +
        policyScoreComparison link score competitor secondOpponent ≤
      policyScoreComparison link score maximizer firstOpponent +
        policyScoreComparison link score maximizer secondOpponent := by
  exact add_le_add
    (scoreMaximizer_policyScoreComparison_dominates link score maximizer competitor
      firstOpponent hlink hmaximizer)
    (scoreMaximizer_policyScoreComparison_dominates link score maximizer competitor
      secondOpponent hlink hmaximizer)

/-- A score maximizer maximizes the finite pairwise preference objective. -/
theorem scoreMaximizer_pairwisePreferenceObjective_dominates {Policy : Type*}
    (link : ℝ → ℝ) (score : Policy → ℝ) (maximizer competitor : Policy)
    (played : List (Policy × Policy)) (hlink : StrictMono link)
    (hmaximizer : ScoreMaximizer score maximizer) :
    pairwisePreferenceObjective link score competitor played ≤
      pairwisePreferenceObjective link score maximizer played := by
  induction played with
  | nil => simp [pairwisePreferenceObjective]
  | cons pair played ih =>
      simp only [pairwisePreferenceObjective, List.map_cons, List.sum_cons]
      apply add_le_add
      · have hsum := scoreMaximizer_pairwiseSum_dominates link score maximizer competitor
          pair.1 pair.2 hlink hmaximizer
        linarith
      · exact ih

/-- A score-maximizing benchmark has nonnegative finite pairwise score regret. -/
theorem pairwiseScoreRegret_nonneg_of_scoreMaximizer {Policy : Type*}
    (score : Policy → ℝ) (benchmark : Policy) (played : List (Policy × Policy))
    (hbenchmark : ScoreMaximizer score benchmark) :
    0 ≤ pairwiseScoreRegret score benchmark played := by
  induction played with
  | nil => simp [pairwiseScoreRegret]
  | cons pair played ih =>
      simp only [pairwiseScoreRegret, List.map_cons, List.sum_cons]
      apply add_nonneg
      · have hfirst := hbenchmark pair.1
        have hsecond := hbenchmark pair.2
        linarith
      · exact ih

end PreferenceRL

end AppliedModelingLib
