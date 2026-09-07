import AppliedModelingLib.Alignment.Axioms.LinearRanking
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite feature-linear ranking models

This module gives the finite-dimensional linear model behind the ranking axioms
in `LinearRanking.lean`.  A parameter and every candidate feature vector use
the same `Fin dimension → ℝ` carrier.  A parameter weakly induces a ranking
when it respects every strict rank comparison; feasibility asks for a
nondegenerate inducing parameter, matching the source paper's finite
linear-social-choice vocabulary.

## Main declarations

- `FeatureVector`
- `LinearRewardParameter`
- `linearReward`
- `InducesRanking`
- `NondegenerateParameter`
- `LinearFeasibleRanking`
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Alignment
namespace Axioms

open SocialChoice.Ranking

/-- A finite-dimensional real feature vector. -/
abbrev FeatureVector (dimension : ℕ) := Fin dimension → ℝ

/-- A parameter vector for a linear reward model. -/
abbrev LinearRewardParameter (dimension : ℕ) := FeatureVector dimension

/-- The dot-product reward of one candidate under a feature-linear model. -/
noncomputable def linearReward {n dimension : ℕ}
    (parameter : LinearRewardParameter dimension)
    (features : Candidate n → FeatureVector dimension)
    (candidate : Candidate n) : ℝ :=
  ∑ coordinate, parameter coordinate * features candidate coordinate

/-- A parameter weakly respects every strict comparison in `ranking`. -/
def InducesRanking {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (parameter : LinearRewardParameter dimension) (ranking : Ranking n) : Prop :=
  ∀ first second,
    StrictlyPrefers ranking first second →
      linearReward parameter features second ≤ linearReward parameter features first

/-- A parameter gives distinct rewards to every pair of distinct candidates. -/
def NondegenerateParameter {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (parameter : LinearRewardParameter dimension) : Prop :=
  ∀ first second, first ≠ second →
    linearReward parameter features first ≠ linearReward parameter features second

/-- A ranking is feasible when some nondegenerate linear parameter induces it. -/
def LinearFeasibleRanking {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (ranking : Ranking n) : Prop :=
  ∃ parameter : LinearRewardParameter dimension,
    NondegenerateParameter features parameter ∧ InducesRanking features parameter ranking

/--
For a nondegenerate parameter, weak induction becomes a strict reward ordering
on every strict ranking comparison.
-/
theorem inducesRanking_strictReward_of_nondegenerate
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (parameter : LinearRewardParameter dimension) (ranking : Ranking n)
    (hinduced : InducesRanking features parameter ranking)
    (hnondegenerate : NondegenerateParameter features parameter)
    {first second : Candidate n} (hpreference : StrictlyPrefers ranking first second) :
    linearReward parameter features second < linearReward parameter features first := by
  refine lt_of_le_of_ne (hinduced first second hpreference) ?_
  exact Ne.symm (hnondegenerate first second (by
    intro hsame
    subst second
    exact not_strictlyPrefers_self ranking first hpreference))

/-- Candidates with identical feature vectors receive identical linear rewards. -/
theorem linearReward_eq_of_feature_eq
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (parameter : LinearRewardParameter dimension) {first second : Candidate n}
    (hfeatures : features first = features second) :
    linearReward parameter features first = linearReward parameter features second := by
  simp only [linearReward, hfeatures]

/-- Scaling a parameter scales every feature-linear reward by the same scalar. -/
theorem linearReward_smul
    {n dimension : ℕ} (scalar : ℝ)
    (parameter : LinearRewardParameter dimension)
    (features : Candidate n → FeatureVector dimension)
    (candidate : Candidate n) :
    linearReward (scalar • parameter) features candidate =
      scalar * linearReward parameter features candidate := by
  classical
  simp only [linearReward, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact mul_assoc _ _ _

/--
Distinct candidates with identical feature vectors cannot be separated by a
nondegenerate linear parameter.
-/
theorem not_nondegenerate_of_feature_eq
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (parameter : LinearRewardParameter dimension) {first second : Candidate n}
    (hdistinct : first ≠ second) (hfeatures : features first = features second) :
    ¬ NondegenerateParameter features parameter := by
  intro hnondegenerate
  exact hnondegenerate first second hdistinct
    (linearReward_eq_of_feature_eq features parameter hfeatures)

end Axioms
end Alignment
end AppliedModelingLib
