import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Trajectory
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC
import AppliedModelingLib.Foundations.Probability.PMFKernel

/-!
# Expected trajectory scores

The trajectory law is independent of a downstream linear score parameter; this
is the basic reusable reward-agnostic interface for finite policy classes.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/-- A policy-indexed finite probability law over trajectories. -/
abbrev PolicyTrajectoryLaw (Policy Trajectory : Type*) := PMFKernel Policy Trajectory

/-- The expected linear score of a trajectory sampled under a policy. -/
noncomputable def policyExpectedTrajectoryScore
    {Policy Trajectory Feature : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    [Fintype Feature] (trajectoryLaw : PolicyTrajectoryLaw Policy Trajectory)
    (feature : Trajectory → Feature → ℝ) (parameter : Feature → ℝ) (policy : Policy) : ℝ :=
  pmfExp (trajectoryLaw policy) fun trajectory =>
    ∑ coordinate, feature trajectory coordinate * parameter coordinate

/-- A finite dataset of pairwise trajectory labels. -/
abbrev PreferenceDataset (Trajectory : Type*) :=
  List (TrajectoryPreferenceOracle.LabeledComparison (Trajectory := Trajectory))

/-- A data-collection procedure is reward agnostic when every reward yields the same dataset. -/
def RewardAgnosticCollection {Reward Trajectory : Type*}
    (collect : Reward → PreferenceDataset Trajectory) : Prop :=
  ∀ firstReward secondReward, collect firstReward = collect secondReward

/-- A reward-agnostic collection can be reused unchanged for any two reward choices. -/
theorem rewardAgnosticCollection_reusesDataset {Reward Trajectory : Type*}
    (collect : Reward → PreferenceDataset Trajectory)
    (hrewardAgnostic : RewardAgnosticCollection collect)
    (firstReward secondReward : Reward) :
    collect firstReward = collect secondReward :=
  hrewardAgnostic firstReward secondReward

/-- The finite ℓ¹ discrepancy between two probability mass functions. -/
noncomputable def pmfL1Error {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) : ℝ :=
  ∑ outcome : Outcome, |(first outcome).toReal - (second outcome).toReal|

/-- A finite PMF ℓ¹ discrepancy is nonnegative. -/
theorem pmfL1Error_nonneg {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) :
    0 ≤ pmfL1Error first second := by
  unfold pmfL1Error
  exact Finset.sum_nonneg fun outcome _ => abs_nonneg _

/-- Finite PMF ℓ¹ error vanishes for identical laws. -/
@[simp] theorem pmfL1Error_self {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (distribution : PMF Outcome) :
    pmfL1Error distribution distribution = 0 := by
  simp [pmfL1Error]

/-- Finite PMF ℓ¹ error is symmetric. -/
theorem pmfL1Error_comm {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) :
    pmfL1Error first second = pmfL1Error second first := by
  unfold pmfL1Error
  apply Finset.sum_congr rfl
  intro outcome _
  rw [abs_sub_comm]
/-- A finite expectation remains within a uniform absolute-value bound. -/
theorem abs_pmfExp_le_of_forall_abs_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (distribution : PMF Outcome) (value : Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ outcome, |value outcome| ≤ bound) :
    |pmfExp distribution value| ≤ bound := by
  rw [abs_le]
  constructor
  · have hupper : pmfExp distribution (fun outcome => -value outcome) ≤ bound :=
      pmfExp_le_of_forall_le distribution _ bound (fun outcome => by
        calc
          -value outcome ≤ |-value outcome| := le_abs_self _
          _ = |value outcome| := abs_neg _
          _ ≤ bound := hbound outcome)
    rw [pmfExp_neg] at hupper
    linarith
  · exact pmfExp_le_of_forall_le distribution _ bound (fun outcome =>
      (le_abs_self _).trans (hbound outcome))

/-- The real atom mass of a finite PMF bind is the corresponding finite mixture. -/
theorem pmfBind_apply_toReal {Input Output : Type*}
    [Fintype Input] [DecidableEq Input] [Fintype Output] [DecidableEq Output]
    (distribution : PMF Input) (kernel : Input → PMF Output) (output : Output) :
    ((distribution.bind kernel) output).toReal =
      ∑ input : Input, (distribution input).toReal * (kernel input output).toReal := by
  classical
  have h_ne_top :
      ∀ input ∈ (Finset.univ : Finset Input),
        distribution input * kernel input output ≠ ⊤ := by
    intro input _
    exact ENNReal.mul_ne_top (distribution.apply_ne_top input)
      ((kernel input).apply_ne_top output)
  calc
    ((distribution.bind kernel) output).toReal =
        (∑ input : Input, distribution input * kernel input output).toReal := by
          rw [PMF.bind_apply, tsum_fintype]
    _ = ∑ input : Input, (distribution input * kernel input output).toReal := by
          exact ENNReal.toReal_sum (s := (Finset.univ : Finset Input))
            (f := fun input : Input => distribution input * kernel input output) h_ne_top
    _ = ∑ input : Input, (distribution input).toReal * (kernel input output).toReal := by
          simp [ENNReal.toReal_mul]

/--
Changing both the finite input law and its output kernel costs at most the
input-law ℓ¹ error plus the true-input-law average of the kernel errors.
This is the discrete mixture inequality used in rollout-visitation arguments.
-/
theorem pmfL1Error_bind_le
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (trueInput estimatedInput : PMF Input)
    (trueKernel estimatedKernel : Input → PMF Output) :
    pmfL1Error (trueInput.bind trueKernel) (estimatedInput.bind estimatedKernel) ≤
      pmfL1Error trueInput estimatedInput +
        pmfExp trueInput (fun input =>
          pmfL1Error (trueKernel input) (estimatedKernel input)) := by
  classical
  unfold pmfL1Error pmfExp
  calc
    ∑ output : Output,
        |((trueInput.bind trueKernel) output).toReal -
          ((estimatedInput.bind estimatedKernel) output).toReal| =
      ∑ output : Output,
        |(∑ input : Input,
            (trueInput input).toReal * (trueKernel input output).toReal) -
          ∑ input : Input,
            (estimatedInput input).toReal * (estimatedKernel input output).toReal| := by
        apply Finset.sum_congr rfl
        intro output _
        rw [pmfBind_apply_toReal, pmfBind_apply_toReal]
    _ = ∑ output : Output,
        |(∑ input : Input,
          (((trueInput input).toReal - (estimatedInput input).toReal) *
              (estimatedKernel input output).toReal +
            (trueInput input).toReal *
              ((trueKernel input output).toReal -
                (estimatedKernel input output).toReal)))| := by
        apply Finset.sum_congr rfl
        intro output _
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro input _
        ring
    _ ≤ ∑ output : Output,
        ((∑ input : Input,
          |((trueInput input).toReal - (estimatedInput input).toReal) *
              (estimatedKernel input output).toReal|) +
          ∑ input : Input,
            |(trueInput input).toReal *
              ((trueKernel input output).toReal -
                (estimatedKernel input output).toReal)|) := by
        apply Finset.sum_le_sum
        intro output _
        calc
          |(∑ input : Input,
            (((trueInput input).toReal - (estimatedInput input).toReal) *
                (estimatedKernel input output).toReal +
              (trueInput input).toReal *
                ((trueKernel input output).toReal -
                  (estimatedKernel input output).toReal)))| ≤
              |∑ input : Input,
                ((trueInput input).toReal - (estimatedInput input).toReal) *
                    (estimatedKernel input output).toReal| +
                |∑ input : Input,
                  (trueInput input).toReal *
                    ((trueKernel input output).toReal -
                      (estimatedKernel input output).toReal)| := by
                rw [Finset.sum_add_distrib]
                exact abs_add_le _ _
          _ ≤ (∑ input : Input,
                |((trueInput input).toReal - (estimatedInput input).toReal) *
                    (estimatedKernel input output).toReal|) +
              ∑ input : Input,
                |(trueInput input).toReal *
                  ((trueKernel input output).toReal -
                    (estimatedKernel input output).toReal)| := by
                exact add_le_add
                  (Finset.abs_sum_le_sum_abs _ Finset.univ)
                  (Finset.abs_sum_le_sum_abs _ Finset.univ)
    _ = (∑ output : Output, ∑ input : Input,
          |(trueInput input).toReal - (estimatedInput input).toReal| *
            (estimatedKernel input output).toReal) +
        ∑ output : Output, ∑ input : Input, (trueInput input).toReal *
          |(trueKernel input output).toReal -
            (estimatedKernel input output).toReal| := by
        rw [Finset.sum_add_distrib]
        simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = (∑ input : Input, ∑ output : Output,
          |(trueInput input).toReal - (estimatedInput input).toReal| *
            (estimatedKernel input output).toReal) +
        ∑ input : Input, ∑ output : Output, (trueInput input).toReal *
          |(trueKernel input output).toReal -
            (estimatedKernel input output).toReal| := by
        congr 1
        · exact Finset.sum_comm
        · exact Finset.sum_comm
    _ = (∑ input : Input,
          |(trueInput input).toReal - (estimatedInput input).toReal| *
            ∑ output : Output, (estimatedKernel input output).toReal) +
        ∑ input : Input, (trueInput input).toReal *
          ∑ output : Output,
            |(trueKernel input output).toReal -
              (estimatedKernel input output).toReal| := by
        congr 1
        · apply Finset.sum_congr rfl
          intro input _
          rw [← Finset.mul_sum]
        · apply Finset.sum_congr rfl
          intro input _
          rw [← Finset.mul_sum]
    _ = (∑ input : Input,
          |(trueInput input).toReal - (estimatedInput input).toReal|) +
        ∑ input : Input, (trueInput input).toReal *
          ∑ output : Output,
            |(trueKernel input output).toReal -
              (estimatedKernel input output).toReal| := by
        congr 1
        apply Finset.sum_congr rfl
        intro input _
        rw [pmfToRealSum (estimatedKernel input)]
        ring
    _ = pmfL1Error trueInput estimatedInput +
        pmfExp trueInput (fun input =>
          pmfL1Error (trueKernel input) (estimatedKernel input)) := by
        rfl

/-- Applying the same finite kernel cannot increase ℓ¹ error. -/
theorem pmfL1Error_bind_sameKernel_le
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (first second : PMF Input) (kernel : Input → PMF Output) :
    pmfL1Error (first.bind kernel) (second.bind kernel) ≤ pmfL1Error first second := by
  calc
    pmfL1Error (first.bind kernel) (second.bind kernel) ≤
        pmfL1Error first second +
          pmfExp first (fun input => pmfL1Error (kernel input) (kernel input)) :=
      pmfL1Error_bind_le first second kernel kernel
    _ = pmfL1Error first second := by
      simp [pmfExp]

/--
The standard total-variation convention for a finite probability mass
function: one half of its ℓ¹ atom discrepancy.
-/
noncomputable def pmfTotalVariation {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) : ℝ :=
  pmfL1Error first second / 2

/-- The finite total variation distance is one half of the explicit ℓ¹ error. -/
theorem pmfTotalVariation_eq_half_pmfL1Error
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) :
    pmfTotalVariation first second = pmfL1Error first second / 2 :=
  rfl

/--
Changing a finite next-state law changes the expectation of a bounded
continuation value by at most its absolute bound times the PMFs' ℓ¹ error.
The factor is stated for the explicit `pmfL1Error` convention used here.
-/
theorem abs_pmfExp_sub_le_bound_mul_pmfL1Error
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (value : Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ outcome, |value outcome| ≤ bound) :
    |pmfExp first value - pmfExp second value| ≤ bound * pmfL1Error first second := by
  calc
    |pmfExp first value - pmfExp second value| ≤
        ∑ outcome : Outcome,
          |(first outcome).toReal - (second outcome).toReal| * |value outcome| :=
      abs_pmfExp_sub_le_sum_abs_atom_mul first second value
    _ ≤ ∑ outcome : Outcome,
        |(first outcome).toReal - (second outcome).toReal| * bound := by
      apply Finset.sum_le_sum
      intro outcome _
      exact mul_le_mul_of_nonneg_left (hbound outcome) (abs_nonneg _)
    _ = bound * pmfL1Error first second := by
      unfold pmfL1Error
      calc
        ∑ outcome : Outcome,
            |(first outcome).toReal - (second outcome).toReal| * bound =
            ∑ outcome : Outcome,
              bound * |(first outcome).toReal - (second outcome).toReal| := by
          apply Finset.sum_congr rfl
          intro outcome _
          ring
        _ = bound * ∑ outcome : Outcome,
            |(first outcome).toReal - (second outcome).toReal| := by
          rw [Finset.mul_sum]

/-- Replacing a finite law changes a squared bounded continuation expectation
by at most the squared absolute bound times the laws' explicit `ℓ¹` error.
This is the finite empirical-to-population second-moment bridge used when a
confidence correction is expressed through an empirical `L²` width. -/
theorem pmfExp_sq_le_pmfExp_sq_add_sq_bound_mul_pmfL1Error
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (value : Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ outcome, |value outcome| ≤ bound) :
    pmfExp first (fun outcome => (value outcome) ^ 2) ≤
      pmfExp second (fun outcome => (value outcome) ^ 2) +
        bound ^ 2 * pmfL1Error first second := by
  have hsquaredBound : ∀ outcome, |(value outcome) ^ 2| ≤ bound ^ 2 := by
    intro outcome
    rw [abs_of_nonneg (sq_nonneg _)]
    have hvalue := hbound outcome
    have habs : 0 ≤ |value outcome| := abs_nonneg _
    have hrewrite : (value outcome) ^ 2 = |value outcome| ^ 2 := by
      rw [sq_abs]
    rw [hrewrite]
    nlinarith
  have hdifference := abs_pmfExp_sub_le_bound_mul_pmfL1Error
    first second (fun outcome => (value outcome) ^ 2) (bound ^ 2) hsquaredBound
  have honeSided :
      pmfExp first (fun outcome => (value outcome) ^ 2) -
        pmfExp second (fun outcome => (value outcome) ^ 2) ≤
      bound ^ 2 * pmfL1Error first second :=
    (le_abs_self _).trans hdifference
  linarith

/--
Replacing a finite next-state law changes the expectation of a value in
`[lower, upper]` by at most its span times total variation.  Centering the
value at the interval midpoint recovers the standard factor one-half relative
to the explicit ℓ¹ discrepancy.
-/
theorem abs_pmfExp_sub_le_span_mul_pmfTotalVariation
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (value : Outcome → ℝ) (lower upper : ℝ)
    (hspan : lower ≤ upper)
    (hlower : ∀ outcome, lower ≤ value outcome)
    (hupper : ∀ outcome, value outcome ≤ upper) :
    |pmfExp first value - pmfExp second value| ≤
      (upper - lower) * pmfTotalVariation first second := by
  let midpoint : ℝ := (lower + upper) / 2
  have hcentered : ∀ outcome, |value outcome - midpoint| ≤ (upper - lower) / 2 := by
    intro outcome
    rw [abs_le]
    constructor <;> dsimp [midpoint] <;> linarith [hlower outcome, hupper outcome]
  calc
    |pmfExp first value - pmfExp second value| =
      |pmfExp first (fun outcome => value outcome - midpoint) -
        pmfExp second (fun outcome => value outcome - midpoint)| := by
          congr 1
          rw [pmfExp_sub, pmfExp_const, pmfExp_sub, pmfExp_const]
          ring
    _ ≤ ((upper - lower) / 2) * pmfL1Error first second :=
      abs_pmfExp_sub_le_bound_mul_pmfL1Error first second
        (fun outcome => value outcome - midpoint) ((upper - lower) / 2) hcentered
    _ = (upper - lower) * pmfTotalVariation first second := by
      unfold pmfTotalVariation
      ring

/-- State-action visitation law at one time step under a policy and the true dynamics. -/
abbrev StateActionRolloutLaw (Policy Step State Action : Type*) :=
  Policy → PMFKernel Step (State × Action)

/-- The rollout expectation of a learned transition model's ℓ¹ error. -/
noncomputable def expectedTransitionL1Error
    {Policy Step State Action : Type*}
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    (trueTransition estimatedTransition : Step → State → Action → PMF State)
    (rollout : StateActionRolloutLaw Policy Step State Action)
    (policy : Policy) (step : Step) : ℝ :=
  pmfExp (rollout policy step) fun stateAction =>
    pmfL1Error (estimatedTransition step stateAction.1 stateAction.2)
      (trueTransition step stateAction.1 stateAction.2)

/-- Expected finite-PMF transition error is nonnegative. -/
theorem expectedTransitionL1Error_nonneg
    {Policy Step State Action : Type*}
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    (trueTransition estimatedTransition : Step → State → Action → PMF State)
    (rollout : StateActionRolloutLaw Policy Step State Action)
    (policy : Policy) (step : Step) :
    0 ≤ expectedTransitionL1Error trueTransition estimatedTransition rollout policy step := by
  unfold expectedTransitionL1Error
  apply pmfExp_nonneg_of_forall_nonneg
  intro stateAction
  exact pmfL1Error_nonneg _ _

/--
The deterministic guarantee supplied by a reward-free RL oracle on its
high-probability success event.  It is intentionally reward independent.
-/
structure RewardFreeTransitionOracleCertificate
    (Policy Step State Action : Type*)
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : Step → State → Action → PMF State)
    (rollout : StateActionRolloutLaw Policy Step State Action)
    (tolerance : ℝ) where
  estimatedInitial : PMF State
  estimatedTransition : Step → State → Action → PMF State
  initial_error_bound : pmfL1Error estimatedInitial trueInitial ≤ tolerance
  rollout_error_bound : ∀ policy step,
    expectedTransitionL1Error trueTransition estimatedTransition rollout policy step ≤ tolerance

/-- Definition 1's success predicate for one stochastic oracle output. -/
def RewardFreeTransitionOracleSuccess
    {Output Policy Step State Action : Type*}
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : Step → State → Action → PMF State)
    (rollout : StateActionRolloutLaw Policy Step State Action)
    (estimatedInitial : Output → PMF State)
    (estimatedTransition : Output → Step → State → Action → PMF State)
    (tolerance : ℝ) (output : Output) : Prop :=
  pmfL1Error (estimatedInitial output) trueInitial ≤ tolerance ∧
    ∀ policy step,
      expectedTransitionL1Error trueTransition (estimatedTransition output)
        rollout policy step ≤ tolerance

/-- The probabilistic reward-free transition-oracle contract from Definition
1.  The output carrier is finite so its success event and subsequent adaptive
experiment have a literal finite probability law. -/
structure RewardFreeTransitionOracleProcess
    (Output Policy Step State Action : Type*)
    [Fintype Output] [DecidableEq Output]
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : Step → State → Action → PMF State)
    (rollout : StateActionRolloutLaw Policy Step State Action)
    (tolerance failureBudget : ℝ) where
  outputLaw : PMF Output
  estimatedInitial : Output → PMF State
  estimatedTransition : Output → Step → State → Action → PMF State
  failure_probability_le :
    pmfProbClassical outputLaw (fun output ↦
      ¬ RewardFreeTransitionOracleSuccess trueInitial trueTransition rollout
        estimatedInitial estimatedTransition tolerance output) ≤ failureBudget

namespace RewardFreeTransitionOracleProcess

variable {Output Policy Step State Action : Type*}
variable [Fintype Output] [DecidableEq Output]
variable [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
variable {trueInitial : PMF State}
variable {trueTransition : Step → State → Action → PMF State}
variable {rollout : StateActionRolloutLaw Policy Step State Action}
variable {tolerance failureBudget : ℝ}

/-- A successful stochastic output supplies the deterministic certificate used
by Lemmas 5--6. -/
def certificate
    (process : RewardFreeTransitionOracleProcess Output Policy Step State Action
      trueInitial trueTransition rollout tolerance failureBudget)
    (output : Output)
    (hsuccess : RewardFreeTransitionOracleSuccess trueInitial trueTransition rollout
      process.estimatedInitial process.estimatedTransition tolerance output) :
    RewardFreeTransitionOracleCertificate Policy Step State Action
      trueInitial trueTransition rollout tolerance where
  estimatedInitial := process.estimatedInitial output
  estimatedTransition := process.estimatedTransition output
  initial_error_bound := hsuccess.1
  rollout_error_bound := hsuccess.2

end RewardFreeTransitionOracleProcess

/-- A first-stage failure budget plus a uniform conditional second-stage
failure budget controls their literal dependent joint experiment. -/
theorem pmfProbClassical_bind_map_pair_le_failure_add
    {State Outcome : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (stateLaw : PMF State) (outcomeLaw : State → PMF Outcome)
    (stateGood : State → Prop) (outcomeBad : State → Outcome → Prop)
    (stateFailureBudget outcomeFailureBudget : ℝ)
    (houtcomeFailureBudget : 0 ≤ outcomeFailureBudget)
    (hstate : pmfProbClassical stateLaw (fun state ↦ ¬ stateGood state) ≤
      stateFailureBudget)
    (hconditional : ∀ state, stateGood state →
      pmfProbClassical (outcomeLaw state) (outcomeBad state) ≤ outcomeFailureBudget) :
    pmfProbClassical
        (stateLaw.bind fun state ↦
          (outcomeLaw state).map fun outcome ↦ (state, outcome))
        (fun stateOutcome ↦ outcomeBad stateOutcome.1 stateOutcome.2) ≤
      outcomeFailureBudget + stateFailureBudget := by
  classical
  rw [pmfProbClassical_eq_pmfProb, pmfProb_bind]
  have hpoint : ∀ state,
      pmfProb ((outcomeLaw state).map fun outcome ↦ (state, outcome))
          (fun stateOutcome ↦ outcomeBad stateOutcome.1 stateOutcome.2) ≤
        outcomeFailureBudget + if ¬ stateGood state then 1 else 0 := by
    intro state
    rw [pmfProb_map]
    by_cases hgood : stateGood state
    · have hbound := hconditional state hgood
      rw [pmfProbClassical_eq_pmfProb] at hbound
      simpa [hgood] using hbound
    · have hone := pmfProb_le_one (outcomeLaw state) (outcomeBad state)
      simp only [hgood, not_false_eq_true, if_true]
      linarith
  calc
    pmfExp stateLaw (fun state ↦
        pmfProb ((outcomeLaw state).map fun outcome ↦ (state, outcome))
          (fun stateOutcome ↦ outcomeBad stateOutcome.1 stateOutcome.2)) ≤
      pmfExp stateLaw (fun state ↦
        outcomeFailureBudget + if ¬ stateGood state then 1 else 0) :=
      pmfExp_le_pmfExp_of_forall_le stateLaw _ _ hpoint
    _ = outcomeFailureBudget +
        pmfProbClassical stateLaw (fun state ↦ ¬ stateGood state) := by
      rw [pmfExp_add, pmfExp_const]
      rw [pmfProbClassical_eq_pmfProb]
      unfold pmfProb
      congr 1
    _ = pmfProbClassical stateLaw (fun state ↦ ¬ stateGood state) +
        outcomeFailureBudget := add_comm _ _
    _ ≤ stateFailureBudget + outcomeFailureBudget :=
      add_le_add_left hstate outcomeFailureBudget
    _ = outcomeFailureBudget + stateFailureBudget := add_comm _ _

namespace RewardFreeTransitionOracleCertificate

variable {Policy Step State Action : Type*}
variable [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
variable {trueInitial : PMF State} {trueTransition : Step → State → Action → PMF State}
variable {rollout : StateActionRolloutLaw Policy Step State Action} {tolerance : ℝ}

/-- The certificate's initial-law error is at most its stated tolerance. -/
theorem initial_error_le
    (certificate : RewardFreeTransitionOracleCertificate Policy Step State Action
      trueInitial trueTransition rollout tolerance) :
    pmfL1Error certificate.estimatedInitial trueInitial ≤ tolerance :=
  certificate.initial_error_bound

/-- The certificate's transition-error bound holds for every policy and step. -/
theorem rollout_error_le
    (certificate : RewardFreeTransitionOracleCertificate Policy Step State Action
      trueInitial trueTransition rollout tolerance)
    (policy : Policy) (step : Step) :
    expectedTransitionL1Error trueTransition certificate.estimatedTransition rollout policy step ≤
      tolerance :=
  certificate.rollout_error_bound policy step

end RewardFreeTransitionOracleCertificate

end PreferenceRL

end AppliedModelingLib
