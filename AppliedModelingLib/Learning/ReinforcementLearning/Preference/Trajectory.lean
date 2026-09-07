import AppliedModelingLib.Foundations.Probability.MDP
import Mathlib.Tactic

/-!
# Finite trajectories and trajectory-level preference feedback

This module is the trajectory-level layer shared by preference-based
reinforcement-learning papers.  It deliberately does not import the
response-level human-feedback library: a policy over trajectories and a
preference oracle over two trajectories are separate objects.

## Main declarations

- `FiniteTrajectory`: a finite sequence of states and actions.
- `FiniteTrajectory.totalReward`: realized cumulative MDP reward.
- `TrajectoryPreferenceOracle`: a randomized binary comparison oracle.
- `trajectoryPreferenceGap`: the centered probability used in PbRL.
- `TrajectoryRewardEquivalent`: reward functions with the same pairwise gaps.
- `PreferenceValueCalibration`: the value-to-preference lower bound of Xu et al.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/-- A length-`horizon` state-action trajectory, including its terminal state. -/
structure FiniteTrajectory (State Action : Type*) (horizon : ℕ) where
  state : Fin (horizon + 1) → State
  action : Fin horizon → Action

namespace FiniteTrajectory

variable {State Action : Type*} {horizon : ℕ}

/-- The realized cumulative reward of a finite trajectory in an MDP. -/
noncomputable def totalReward
    (M : FiniteMDP State Action) (trajectory : FiniteTrajectory State Action horizon) : ℝ :=
  ∑ time : Fin horizon,
    M.reward (trajectory.state time.castSucc) (trajectory.action time)
      (trajectory.state time.succ)

/-- Adding the same constant to a trajectory reward does not change reward gaps. -/
theorem totalReward_sub_add_constant
    (reward : FiniteTrajectory State Action horizon → ℝ) (constant : ℝ)
    (first second : FiniteTrajectory State Action horizon) :
    (reward first + constant) - (reward second + constant) = reward first - reward second := by
  ring

end FiniteTrajectory

/-- A randomized trajectory preference oracle returning the chance its first input wins. -/
structure TrajectoryPreferenceOracle (Trajectory : Type*) where
  probability : Trajectory → Trajectory → ℝ
  probability_nonneg : ∀ first second, 0 ≤ probability first second
  probability_le_one : ∀ first second, probability first second ≤ 1
  complementary : ∀ first second,
    probability first second + probability second first = 1

namespace TrajectoryPreferenceOracle

variable {Trajectory : Type*}

/-- The centered preference probability `Pr[first ≻ second] - 1/2`. -/
noncomputable def trajectoryPreferenceGap
    (oracle : TrajectoryPreferenceOracle Trajectory) (first second : Trajectory) : ℝ :=
  oracle.probability first second - 1 / 2

/-- Reversing a binary comparison negates its centered preference gap. -/
theorem trajectoryPreferenceGap_swap
    (oracle : TrajectoryPreferenceOracle Trajectory) (first second : Trajectory) :
    trajectoryPreferenceGap oracle second first =
      -trajectoryPreferenceGap oracle first second := by
  unfold trajectoryPreferenceGap
  linarith [oracle.complementary first second]

/-- A trajectory tied with itself has zero centered preference gap. -/
theorem trajectoryPreferenceGap_self
    (oracle : TrajectoryPreferenceOracle Trajectory) (trajectory : Trajectory) :
    trajectoryPreferenceGap oracle trajectory trajectory = 0 := by
  unfold trajectoryPreferenceGap
  linarith [oracle.complementary trajectory trajectory]

/-- The pair of sampled trajectories and its preference label. -/
structure LabeledComparison where
  first : Trajectory
  second : Trajectory
  firstWins : Bool

end TrajectoryPreferenceOracle

/-- Two trajectory-reward functions are equivalent when every pairwise gap agrees. -/
def TrajectoryRewardEquivalent {Trajectory : Type*}
    (first second : Trajectory → ℝ) : Prop :=
  ∀ left right, first left - first right = second left - second right

/-- Equal constant shifts give trajectory-reward equivalence. -/
theorem trajectoryRewardEquivalent_add_constant {Trajectory : Type*}
    (reward : Trajectory → ℝ) (constant : ℝ) :
    TrajectoryRewardEquivalent reward (fun trajectory => reward trajectory + constant) := by
  intro left right
  ring

/-- A finite distribution over complete trajectories. -/
abbrev TrajectoryDistribution (Trajectory : Type*) := PMF Trajectory

/-- The expected probability that a draw from the first law beats a draw from the second. -/
noncomputable def trajectoryDistributionPreference
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (oracle : TrajectoryPreferenceOracle Trajectory)
    (first second : TrajectoryDistribution Trajectory) : ℝ :=
  pmfExp first fun firstTrajectory =>
    pmfExp second fun secondTrajectory =>
      oracle.probability firstTrajectory secondTrajectory

/-- The expected trajectory reward under a finite trajectory distribution. -/
noncomputable def trajectoryDistributionValue
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (distribution : TrajectoryDistribution Trajectory) (reward : Trajectory → ℝ) : ℝ :=
  pmfExp distribution reward

/--
A uniform trajectory-reward perturbation gives the same uniform error in its
finite-distribution expected value.
-/
theorem trajectoryDistributionValue_uniformPerturbation
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (distribution : TrajectoryDistribution Trajectory)
    (truth perturbed : Trajectory → ℝ) (error : ℝ)
    (hperturbation : ∀ trajectory, |truth trajectory - perturbed trajectory| ≤ error) :
    |trajectoryDistributionValue distribution truth -
        trajectoryDistributionValue distribution perturbed| ≤ error := by
  apply abs_le.mpr
  constructor
  · have hbound :
        trajectoryDistributionValue distribution perturbed ≤
          trajectoryDistributionValue distribution truth + error := by
      unfold trajectoryDistributionValue
      calc
        pmfExp distribution perturbed ≤
            pmfExp distribution (fun trajectory => truth trajectory + error) :=
          pmfExp_le_pmfExp_of_forall_le distribution perturbed
            (fun trajectory => truth trajectory + error) (fun trajectory => by
              linarith [(abs_le.mp (hperturbation trajectory)).1])
        _ = pmfExp distribution truth + error := by
          rw [pmfExp_add, pmfExp_const]
    linarith
  · have hbound :
        trajectoryDistributionValue distribution truth ≤
          trajectoryDistributionValue distribution perturbed + error := by
      unfold trajectoryDistributionValue
      calc
        pmfExp distribution truth ≤
            pmfExp distribution (fun trajectory => perturbed trajectory + error) :=
          pmfExp_le_pmfExp_of_forall_le distribution truth
            (fun trajectory => perturbed trajectory + error) (fun trajectory => by
              linarith [(abs_le.mp (hperturbation trajectory)).2])
        _ = pmfExp distribution perturbed + error := by
          rw [pmfExp_add, pmfExp_const]
    linarith

/-- A policy-level numerical value and centered preference gap obey a positive calibration. -/
structure PreferenceValueCalibration (Policy : Type*)
    (value : Policy → ℝ) (preferenceGap : Policy → Policy → ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  lower_bound : ∀ first second,
    0 < value first - value second →
      constant * (value first - value second) ≤ preferenceGap first second

namespace PreferenceValueCalibration

variable {Policy : Type*} {value : Policy → ℝ} {preferenceGap : Policy → Policy → ℝ}

/-- The source-facing consequence of Xu et al.'s Assumption 1. -/
theorem positivePreference_of_valueGap
    (calibration : PreferenceValueCalibration Policy value preferenceGap)
    (first second : Policy) (hvalue : value second < value first) :
    0 < preferenceGap first second := by
  have hgap : 0 < value first - value second := sub_pos.mpr hvalue
  exact lt_of_lt_of_le (mul_pos calibration.constant_pos hgap)
    (calibration.lower_bound first second hgap)

end PreferenceValueCalibration

/-- The centered policy-preference model that is linear in the value gap. -/
noncomputable def linearPreferenceGap {Policy : Type*}
    (constant : ℝ) (value : Policy → ℝ) (first second : Policy) : ℝ :=
  constant * (value first - value second)

/-- A proposition-level form of the value-to-preference calibration. -/
def SatisfiesPreferenceValueCalibration {Policy : Type*}
    (value : Policy → ℝ) (preferenceGap : Policy → Policy → ℝ) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ first second,
    0 < value first - value second →
      constant * (value first - value second) ≤ preferenceGap first second

/-- A positive linear preference model has a calibration witness. -/
noncomputable def linearPreferenceGap_calibration {Policy : Type*}
    (constant : ℝ) (value : Policy → ℝ) (hconstant : 0 < constant) :
    PreferenceValueCalibration Policy value (linearPreferenceGap constant value) := by
  refine
    { constant := constant
      constant_pos := hconstant
      lower_bound := ?_ }
  intro first second _hgap
  rfl

/-- A positive linear preference model satisfies the proposition-level calibration. -/
theorem linearPreferenceGap_satisfies_calibration {Policy : Type*}
    (constant : ℝ) (value : Policy → ℝ) (hconstant : 0 < constant) :
    SatisfiesPreferenceValueCalibration value (linearPreferenceGap constant value) := by
  refine ⟨constant, hconstant, ?_⟩
  intro first second _hgap
  rfl

/--
The linear centered-preference model has strong stochastic transitivity along
strictly decreasing policy values.
-/
theorem linearPreferenceGap_strongStochasticTransitivity {Policy : Type*}
    (constant : ℝ) (value : Policy → ℝ) (hconstant : 0 < constant)
    (first middle last : Policy)
    (hfirstMiddle : value middle < value first)
    (hmiddleLast : value last < value middle) :
    max (linearPreferenceGap constant value first middle)
        (linearPreferenceGap constant value middle last) ≤
      linearPreferenceGap constant value first last := by
  apply max_le
  · unfold linearPreferenceGap
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hconstant)
    linarith
  · unfold linearPreferenceGap
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hconstant)
    linarith

/-- The linear centered-preference model has an exact triangle decomposition. -/
theorem linearPreferenceGap_triangleEquality {Policy : Type*}
    (constant : ℝ) (value : Policy → ℝ) (first middle last : Policy) :
    linearPreferenceGap constant value first last =
      linearPreferenceGap constant value first middle +
        linearPreferenceGap constant value middle last := by
  unfold linearPreferenceGap
  ring

end PreferenceRL

end AppliedModelingLib
