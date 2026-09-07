import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PolicyComparison
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Logistic
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import Mathlib.Tactic

/-!
# Finite mean trajectory embeddings

The expected linear trajectory score equals the dot product of the parameter
with the policy's coordinatewise finite mean embedding.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/-- The coordinatewise expected feature vector of a policy's trajectory law. -/
noncomputable def policyMeanTrajectoryFeature
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (policy : Policy) (coordinate : Feature) : ℝ :=
  pmfExp (trajectoryLaw policy) fun trajectory => feature trajectory coordinate

/-- The score of a policy's finite mean trajectory embedding. -/
noncomputable def policyMeanEmbeddingScore
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    [Fintype Feature] (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (parameter : Feature → ℝ) (policy : Policy) : ℝ :=
  ∑ coordinate, policyMeanTrajectoryFeature trajectoryLaw feature policy coordinate *
    parameter coordinate

/-- Finite expectation commutes with the finite linear feature sum. -/
theorem policyExpectedTrajectoryScore_eq_policyMeanEmbeddingScore
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    [Fintype Feature] (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (parameter : Feature → ℝ) (policy : Policy) :
    policyExpectedTrajectoryScore trajectoryLaw feature parameter policy =
      policyMeanEmbeddingScore trajectoryLaw feature parameter policy := by
  unfold policyExpectedTrajectoryScore policyMeanEmbeddingScore policyMeanTrajectoryFeature
  rw [pmfExp_univ_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [pmfExp_mul_const]

/-- A finite policy mean embedding remains in any Euclidean ball containing
every trajectory feature.  This is the finite-PMF form of Jensen's norm
inequality. -/
theorem normL2_pmfExp_le
    {Outcome Feature : Type*} [Fintype Outcome] [DecidableEq Outcome] [Fintype Feature]
    (distribution : PMF Outcome) (feature : Outcome → Feature → ℝ) (bound : ℝ)
    (hbound : ∀ outcome, FiniteDimensionalNorms.l2 (feature outcome) ≤ bound) :
    FiniteDimensionalNorms.l2
        (fun coordinate => pmfExp distribution (fun outcome => feature outcome coordinate)) ≤ bound := by
  let E := @PiLp (2 : ENNReal) Feature (fun _ => ℝ)
  let lifted : Outcome → E := fun outcome => WithLp.toLp 2 (feature outcome)
  have hmean : pmfVectorExp distribution lifted =
      WithLp.toLp 2 (fun coordinate => pmfExp distribution
        (fun outcome => feature outcome coordinate)) := by
    dsimp [E, lifted]
    unfold pmfVectorExp pmfExp
    simp only [← WithLp.toLp_smul]
    rw [← WithLp.toLp_sum]
    congr 1
    funext coordinate
    simp
  have hnorm := norm_pmfVectorExp_le_pmfExp_norm distribution lifted
  calc
    FiniteDimensionalNorms.l2
        (fun coordinate => pmfExp distribution (fun outcome => feature outcome coordinate)) =
        ‖WithLp.toLp 2 (fun coordinate => pmfExp distribution
          (fun outcome => feature outcome coordinate))‖ :=
      FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 _
    _ = ‖pmfVectorExp distribution lifted‖ := by rw [hmean]
    _ ≤ pmfExp distribution (fun outcome => ‖lifted outcome‖) := hnorm
    _ = pmfExp distribution (fun outcome => FiniteDimensionalNorms.l2 (feature outcome)) := by
      apply pmfExp_congr
      intro outcome
      exact (FiniteDimensionalNorms.normL2_eq_piLp_norm_L2 (feature outcome)).symm
    _ ≤ bound := pmfExp_le_of_forall_le distribution _ bound hbound

/-- The logistic comparison between the mean embeddings of two policies. -/
noncomputable def liftedTrajectoryPolicyComparison
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    [Fintype Feature] (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (parameter : Feature → ℝ)
    (first second : Policy) : ℝ :=
  logisticLink
    (policyMeanEmbeddingScore trajectoryLaw feature parameter first -
      policyMeanEmbeddingScore trajectoryLaw feature parameter second)

/-- Re-expressing the lifted comparison through expected trajectory scores. -/
theorem liftedTrajectoryPolicyComparison_eq_policyScoreComparison
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    [Fintype Feature] (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (parameter : Feature → ℝ)
    (first second : Policy) :
    liftedTrajectoryPolicyComparison trajectoryLaw feature parameter first second =
      policyScoreComparison logisticLink
        (policyExpectedTrajectoryScore trajectoryLaw feature parameter) first second := by
  unfold liftedTrajectoryPolicyComparison policyScoreComparison
  rw [policyExpectedTrajectoryScore_eq_policyMeanEmbeddingScore,
    policyExpectedTrajectoryScore_eq_policyMeanEmbeddingScore]

end PreferenceRL

end AppliedModelingLib
