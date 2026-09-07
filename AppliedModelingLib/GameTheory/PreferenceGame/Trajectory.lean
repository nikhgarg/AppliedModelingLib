import AppliedModelingLib.GameTheory.PreferenceGame.NoRegret
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Trajectory

/-!
# Constant-sum games over finite trajectory laws

This module is the paper-neutral bridge from a trajectory comparison oracle to
the normal-form game induced by two independently sampled trajectory laws.  It
is the mathematical core of the factorized-independent Markov-game reduction:
the sequential construction matters only through each policy's trajectory
law, while the terminal game payoff is the expected preference probability.
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open PreferenceRL

noncomputable section

/-- Swapping two finite trajectory laws complements their expected payoff. -/
theorem trajectoryDistributionPreference_add_swap
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (oracle : TrajectoryPreferenceOracle Trajectory)
    (first second : TrajectoryDistribution Trajectory) :
    trajectoryDistributionPreference oracle first second +
      trajectoryDistributionPreference oracle second first = 1 := by
  change pmfPairExp first second oracle.probability +
    pmfPairExp second first oracle.probability = 1
  rw [pmfPairExp_swap second first (oracle.probability)]
  rw [← pmfPairExp_add]
  calc
    pmfPairExp first second (fun left right ↦
        oracle.probability left right + oracle.probability right left) =
        pmfPairExp first second (fun _ _ ↦ 1) := by
      unfold pmfPairExp
      refine pmfExp_congr first fun firstTrajectory ↦ ?_
      refine pmfExp_congr second fun secondTrajectory ↦ ?_
      exact oracle.complementary firstTrajectory secondTrajectory
    _ = 1 := by simp [pmfPairExp]

/-- Every finite trajectory law ties itself with expected payoff one half. -/
theorem trajectoryDistributionPreference_self
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (oracle : TrajectoryPreferenceOracle Trajectory)
    (policy : TrajectoryDistribution Trajectory) :
    trajectoryDistributionPreference oracle policy policy = 1 / 2 := by
  have hsum := trajectoryDistributionPreference_add_swap oracle policy policy
  linarith

/--
An epsilon von Neumann winner stated directly for a finite law over complete
trajectories.
-/
def IsApproximateTrajectoryVonNeumannWinner
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (oracle : TrajectoryPreferenceOracle Trajectory) (epsilon : ℝ)
    (policy : TrajectoryDistribution Trajectory) : Prop :=
  HasDualityGapAtMost (trajectoryDistributionPreference oracle)
    epsilon policy policy

/--
The factorized-independent Markov-game reduction: if the two induced
trajectory laws form an exact restricted Nash pair for the comparison payoff,
then each law is a von Neumann winner in the original trajectory problem.
-/
theorem restrictedNashTrajectoryLaws_both_vonNeumannWinners
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (oracle : TrajectoryPreferenceOracle Trajectory)
    (first second : TrajectoryDistribution Trajectory)
    (hrestrictedNash : HasDualityGapAtMost
      (trajectoryDistributionPreference oracle) 0 first second) :
    IsApproximateTrajectoryVonNeumannWinner oracle 0 first ∧
      IsApproximateTrajectoryVonNeumannWinner oracle 0 second := by
  simpa [IsApproximateTrajectoryVonNeumannWinner] using
    (constantSum_pair_zeroDualityGap_both_self
      (trajectoryDistributionPreference oracle) 1 first second
      (trajectoryDistributionPreference_add_swap oracle) hrestrictedNash)

end

end PreferenceGame
end GameTheory
end AppliedModelingLib
