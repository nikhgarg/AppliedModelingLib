import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Trajectory
import AppliedModelingLib.Foundations.Optimization.Certificate

/-!
# Utility comparisons on a policy class

These elementary definitions separate a policy's scalar score from the link
function used to turn score differences into comparison probabilities.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A policy whose scalar score is at least that of every competitor. -/
abbrev ScoreMaximizer {Policy : Type*} (score : Policy → ℝ) (policy : Policy) : Prop :=
  Optimization.IsGlobalMaximizer score policy

/-- The comparison value obtained by applying a link to a score difference. -/
def policyScoreComparison {Policy : Type*} (link : ℝ → ℝ) (score : Policy → ℝ)
    (first second : Policy) : ℝ :=
  link (score first - score second)

/-- The trajectory-level comparison probability induced by a utility function. -/
noncomputable def utilityComparisonProbability {Trajectory : Type*}
    (link : ℝ → ℝ) (reward : Trajectory → ℝ) (first second : Trajectory) : ℝ :=
  link (reward first - reward second)

/-- A link normalized at zero assigns probability one half to a self-comparison. -/
theorem utilityComparisonProbability_self {Trajectory : Type*}
    (link : ℝ → ℝ) (reward : Trajectory → ℝ) (hzero : link 0 = 1 / 2)
    (trajectory : Trajectory) :
    utilityComparisonProbability link reward trajectory trajectory = 1 / 2 := by
  simp [utilityComparisonProbability, hzero]

/-- A symmetric link complements the probabilities of reversed comparisons. -/
theorem utilityComparisonProbability_complementary {Trajectory : Type*}
    (link : ℝ → ℝ) (reward : Trajectory → ℝ)
    (hsymmetric : ∀ difference, link difference + link (-difference) = 1)
    (first second : Trajectory) :
    utilityComparisonProbability link reward first second +
        utilityComparisonProbability link reward second first = 1 := by
  unfold utilityComparisonProbability
  rw [show reward second - reward first = -(reward first - reward second) by ring]
  exact hsymmetric (reward first - reward second)

end PreferenceRL

end AppliedModelingLib
