import AppliedModelingLib.Foundations.Probability.MDP
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Finite MDPs with independent stochastic rewards

`FiniteMDP` represents a realized reward as a function of the successor state.
This module provides the complementary finite-outcome model in which a
state-action pair has a reward law and a transition law sampled independently.
Its expected-reward projection is an ordinary `FiniteMDP`, so existing Bellman
and policy results can be reused without identifying the two samples.
-/

open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib

/-- The finite-PMF variance agrees with measure-theoretic variance under the
PMF's induced probability measure.  This is the bridge between finite
empirical transition confidence radii and source statements formulated for
the transition kernel as a measure. -/
theorem pmfVariance_eq_variance_toMeasure
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) :
    pmfVariance μ X = ProbabilityTheory.variance X μ.toMeasure := by
  unfold pmfVariance
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite X).aemeasurable]
  rw [← pmfExp_eq_integral_toMeasure μ
    (fun a => (X a - ∫ b, X b ∂μ.toMeasure) ^ 2)]
  rw [← pmfExp_eq_integral_toMeasure μ X]

/-- A finite-state/action MDP whose immediate reward is an arbitrary real
random variable in `[0,1]`, sampled independently of the successor.  The
reward law is a probability measure rather than a finite PMF, matching the
usual bounded-reward MDP model. -/
structure BoundedStochasticRewardMDP (State Action : Type*) where
  transition : State → Action → PMF State
  rewardLaw : State → Action → ProbabilityMeasure ℝ
  reward_ae_mem_Icc : ∀ state action,
    ∀ᵐ reward ∂(rewardLaw state action : Measure ℝ), reward ∈ Set.Icc (0 : ℝ) 1

namespace BoundedStochasticRewardMDP

variable {State Action : Type*}

/-- Expected immediate reward under the source reward law. -/
noncomputable def expectedReward
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) : ℝ :=
  ∫ reward, reward ∂(M.rewardLaw state action : Measure ℝ)

/-- The expected-reward finite MDP used for Bellman planning. -/
noncomputable def expectedMDP
    (M : BoundedStochasticRewardMDP State Action) : FiniteMDP State Action where
  transition := M.transition
  reward := fun state action _ => M.expectedReward state action

/-- The independent joint reward-successor law after one state-action choice.
The state carrier need only have a measurable structure for this probabilistic
view; planning itself uses only the finite transition PMF. -/
noncomputable def oneStepLaw [MeasurableSpace State]
  (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) : Measure (ℝ × State) :=
  (M.rewardLaw state action : Measure ℝ).prod (M.transition state action).toMeasure

/-- The reward marginal of the source joint law is exactly the stated reward
law. -/
theorem oneStepLaw_fst
    [MeasurableSpace State]
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) :
    (M.oneStepLaw state action).fst = (M.rewardLaw state action : Measure ℝ) := by
  unfold oneStepLaw
  rw [Measure.fst_prod]

/-- The successor marginal of the source joint law is exactly the stated
transition PMF viewed as a measure. -/
theorem oneStepLaw_snd
    [MeasurableSpace State]
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) :
    (M.oneStepLaw state action).snd = (M.transition state action).toMeasure := by
  unfold oneStepLaw
  rw [Measure.snd_prod]

/-- The expected reward coordinate of one independent source draw is the
expected reward used by the expected-reward MDP. -/
theorem oneStepLaw_reward_marginal_integral
    [MeasurableSpace State]
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) :
    ∫ outcome, outcome.1 ∂(M.oneStepLaw state action) = M.expectedReward state action := by
  unfold oneStepLaw expectedReward
  simpa using
    (MeasureTheory.integral_fun_fst
      (μ := (M.rewardLaw state action : Measure ℝ))
      (ν := (M.transition state action).toMeasure) id)

/-- The countable-coordinate Markov kernel of independent source reward and
successor observations.  This is the measure-valued interface needed by an
Ionescu--Tulcea execution when rewards need not have finite support. -/
noncomputable def oneStepKernel
    [MeasurableSpace State] [MeasurableSpace Action]
    [Countable State] [Countable Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    (M : BoundedStochasticRewardMDP State Action) : Kernel (State × Action) (ℝ × State) :=
  Kernel.ofFunOfCountable fun coordinate =>
    M.oneStepLaw coordinate.1 coordinate.2

/-- The source one-step kernel is Markov because both the reward law and the
finite transition law are probability measures. -/
instance oneStepKernel_isMarkov
    [MeasurableSpace State] [MeasurableSpace Action]
    [Countable State] [Countable Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    (M : BoundedStochasticRewardMDP State Action) :
    IsMarkovKernel M.oneStepKernel where
  isProbabilityMeasure coordinate := by
    unfold oneStepKernel Kernel.ofFunOfCountable
    change IsProbabilityMeasure
      ((M.rewardLaw coordinate.1 coordinate.2 : Measure ℝ).prod
        (M.transition coordinate.1 coordinate.2).toMeasure)
    infer_instance

/-- The source reward law is nonnegative almost surely, hence so is its
expected reward. -/
theorem expectedReward_nonneg
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) :
    0 ≤ M.expectedReward state action := by
  unfold expectedReward
  apply integral_nonneg_of_ae
  filter_upwards [M.reward_ae_mem_Icc state action] with reward hreward
  exact hreward.1

/-- The source reward law is at most one almost surely, hence its expectation
is at most one. -/
theorem expectedReward_le_one
    (M : BoundedStochasticRewardMDP State Action)
    (state : State) (action : Action) :
    M.expectedReward state action ≤ 1 := by
  have hintegrable : Integrable (fun reward : ℝ => reward)
      (M.rewardLaw state action : Measure ℝ) :=
    Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable
      (M.reward_ae_mem_Icc state action)
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ))
      (M.rewardLaw state action : Measure ℝ) :=
    integrable_const _
  calc
    M.expectedReward state action =
        ∫ reward, reward ∂(M.rewardLaw state action : Measure ℝ) := rfl
    _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂(M.rewardLaw state action : Measure ℝ) := by
      apply integral_mono_ae hintegrable hconst
      filter_upwards [M.reward_ae_mem_Icc state action] with reward hreward
      exact hreward.2
    _ = 1 := by simp

/-- Bellman evaluation in the expected-reward MDP separates immediate reward
and continuation expectation. -/
theorem expectedMDP_actionValue
    [Fintype State] [DecidableEq State]
    (M : BoundedStochasticRewardMDP State Action) (continuation : State → ℝ)
    (state : State) (action : Action) :
    FiniteMDP.actionValue M.expectedMDP continuation state action =
      M.expectedReward state action + pmfExp (M.transition state action) continuation := by
  unfold FiniteMDP.actionValue expectedMDP
  rw [pmfExp_add, pmfExp_const]

/-- The expected payoff of one arbitrary bounded-reward source draw is its
expected immediate reward plus the expected successor continuation value.
This is the measure-level counterpart of the finite-outcome product-law
calculation below. -/
theorem oneStepLaw_payoff_integral
    [MeasurableSpace State] [Fintype State] [DecidableEq State]
    [MeasurableSingletonClass State]
    (M : BoundedStochasticRewardMDP State Action)
    (continuation : State → ℝ) (state : State) (action : Action) :
    ∫ outcome, outcome.1 + continuation outcome.2 ∂M.oneStepLaw state action =
      M.expectedReward state action + pmfExp (M.transition state action) continuation := by
  let rewardMeasure : Measure ℝ := M.rewardLaw state action
  let transitionMeasure : Measure State := (M.transition state action).toMeasure
  letI : IsProbabilityMeasure rewardMeasure := by
    dsimp [rewardMeasure]
    infer_instance
  letI : IsProbabilityMeasure transitionMeasure := by
    dsimp [transitionMeasure]
    infer_instance
  have hreward : Integrable (fun reward : ℝ => reward) rewardMeasure :=
    Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable
      (M.reward_ae_mem_Icc state action)
  have hcontinuation : Integrable continuation transitionMeasure :=
    Integrable.of_finite
  change ∫ outcome, outcome.1 + continuation outcome.2 ∂rewardMeasure.prod transitionMeasure =
      ∫ reward, reward ∂rewardMeasure + pmfExp (M.transition state action) continuation
  rw [integral_add (hreward.comp_fst transitionMeasure)
    (hcontinuation.comp_snd rewardMeasure)]
  rw [MeasureTheory.integral_fun_fst (μ := rewardMeasure) (ν := transitionMeasure)
      (fun reward : ℝ => reward),
    MeasureTheory.integral_fun_snd (μ := rewardMeasure) (ν := transitionMeasure)
      continuation]
  simp only [probReal_univ, one_smul]
  rw [← pmfExp_eq_integral_toMeasure]

set_option maxHeartbeats 800000 in
-- The product-measure `MemLp` instances in this general (non-finite-carrier)
-- variance identity exceed Lean's default elaboration heartbeat budget.
/--
The variance of an arbitrary bounded reward plus an independent successor
continuation is the sum of their variances.  The continuation's `L²` premise
is explicit because this measure-level statement is not restricted to a
finite state carrier.
-/
theorem oneStepLaw_payoff_variance
    [MeasurableSpace State]
    (M : BoundedStochasticRewardMDP State Action)
    (continuation : State → ℝ) (state : State) (action : Action)
    (hcontinuation : MemLp continuation 2 ((M.transition state action).toMeasure)) :
    ProbabilityTheory.variance
        (fun outcome : ℝ × State => outcome.1 + continuation outcome.2)
        (M.oneStepLaw state action) =
      ProbabilityTheory.variance (fun reward : ℝ => reward)
        (M.rewardLaw state action : Measure ℝ) +
        ProbabilityTheory.variance continuation ((M.transition state action).toMeasure) := by
  let rewardMeasure : Measure ℝ := M.rewardLaw state action
  let transitionMeasure : Measure State := (M.transition state action).toMeasure
  letI : IsProbabilityMeasure rewardMeasure := by
    dsimp [rewardMeasure]
    infer_instance
  letI : IsProbabilityMeasure transitionMeasure := by
    dsimp [transitionMeasure]
    infer_instance
  have hreward : MemLp (fun reward : ℝ => reward) 2 rewardMeasure :=
    memLp_of_bounded (M.reward_ae_mem_Icc state action)
      measurable_id.aestronglyMeasurable 2
  change ProbabilityTheory.variance
      (fun outcome : ℝ × State => outcome.1 + continuation outcome.2)
      (rewardMeasure.prod transitionMeasure) =
    ProbabilityTheory.variance (fun reward : ℝ => reward) rewardMeasure +
      ProbabilityTheory.variance continuation transitionMeasure
  exact ProbabilityTheory.variance_add_prod hreward hcontinuation

end BoundedStochasticRewardMDP

/-- A finite controlled transition system with a separate finite reward
outcome law.  `rewardValue` maps the reward carrier to its real payoff. -/
structure FiniteStochasticRewardMDP (State Action Reward : Type*) where
  transition : State → Action → PMF State
  rewardLaw : State → Action → PMF Reward
  rewardValue : Reward → ℝ

namespace FiniteStochasticRewardMDP

variable {State Action Reward : Type*}

/-- Expected immediate reward of a state-action pair. -/
noncomputable def expectedReward [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (state : State) (action : Action) : ℝ :=
  pmfExp (M.rewardLaw state action) M.rewardValue

/-- The ordinary finite MDP governing expected planning values.  Its reward
does not depend on the successor, but the underlying source model still has a
separate stochastic reward draw. -/
noncomputable def expectedMDP [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward) : FiniteMDP State Action where
  transition := M.transition
  reward := fun state action _ => M.expectedReward state action

/-- The independent joint law of the reward outcome and successor state after
one state-action choice. -/
noncomputable def oneStepLaw [Fintype Reward] [Fintype State]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (state : State) (action : Action) : PMF (Reward × State) :=
  pmfProd (M.rewardLaw state action) (M.transition state action)

/-- Bellman evaluation in the expected MDP separates immediate reward and
continuation expectation exactly. -/
theorem expectedMDP_actionValue
    [Fintype State] [DecidableEq State] [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward) (continuation : State → ℝ)
    (state : State) (action : Action) :
    FiniteMDP.actionValue M.expectedMDP continuation state action =
      M.expectedReward state action + pmfExp (M.transition state action) continuation := by
  unfold FiniteMDP.actionValue expectedMDP
  rw [pmfExp_add, pmfExp_const]

/-- The reward coordinate of the independent one-step law has the stated
reward-law expectation. -/
theorem oneStepLaw_reward_marginal_expectation
    [Fintype State] [DecidableEq State] [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (state : State) (action : Action) :
    pmfExp (M.oneStepLaw state action) (fun outcome => M.rewardValue outcome.1) =
      M.expectedReward state action := by
  unfold oneStepLaw expectedReward
  rw [pmfExp_pmfProd_eq_pairExp]
  unfold pmfPairExp
  change pmfExp (M.rewardLaw state action)
      (fun reward => pmfExp (M.transition state action) (fun _ => M.rewardValue reward)) =
    pmfExp (M.rewardLaw state action) M.rewardValue
  apply pmfExp_congr
  intro reward
  exact pmfExp_const _ _

/-- The successor coordinate of the independent one-step law has the stated
transition-law expectation. -/
theorem oneStepLaw_transition_marginal_expectation
    [Fintype State] [DecidableEq State] [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (state : State) (action : Action) (continuation : State → ℝ) :
    pmfExp (M.oneStepLaw state action) (fun outcome => continuation outcome.2) =
      pmfExp (M.transition state action) continuation := by
  unfold oneStepLaw
  rw [pmfExp_pmfProd_eq_pairExp]
  unfold pmfPairExp
  change pmfExp (M.rewardLaw state action)
      (fun _ => pmfExp (M.transition state action) continuation) =
    pmfExp (M.transition state action) continuation
  exact pmfExp_const _ _

/-- The expected payoff of the independent joint draw agrees exactly with the
one-step Bellman value of the expected-reward MDP. -/
theorem oneStepLaw_payoff_expectation
    [Fintype State] [DecidableEq State] [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (continuation : State → ℝ) (state : State) (action : Action) :
    pmfExp (M.oneStepLaw state action)
        (fun outcome => M.rewardValue outcome.1 + continuation outcome.2) =
      FiniteMDP.actionValue M.expectedMDP continuation state action := by
  unfold oneStepLaw
  rw [pmfExp_pmfProd_eq_pairExp, expectedMDP_actionValue]
  unfold pmfPairExp
  change pmfExp (M.rewardLaw state action)
      (fun reward => pmfExp (M.transition state action)
        (fun next => M.rewardValue reward + continuation next)) =
    pmfExp (M.rewardLaw state action) M.rewardValue +
      pmfExp (M.transition state action) continuation
  calc
    pmfExp (M.rewardLaw state action)
        (fun reward => pmfExp (M.transition state action)
          (fun next => M.rewardValue reward + continuation next)) =
        pmfExp (M.rewardLaw state action)
          (fun reward => M.rewardValue reward +
            pmfExp (M.transition state action) continuation) := by
          apply pmfExp_congr
          intro reward
          rw [pmfExp_add, pmfExp_const]
    _ = _ := by rw [pmfExp_add, pmfExp_const]

/--
The variance of one independent reward-successor payoff separates into its
reward-law variance and its successor-continuation variance.  This is the
finite-PMF version of the independent one-step calculation used by
variance-sensitive finite-horizon MDP analyses.
-/
theorem oneStepLaw_payoff_variance
    [Fintype State] [DecidableEq State] [Fintype Reward] [DecidableEq Reward]
    (M : FiniteStochasticRewardMDP State Action Reward)
    (continuation : State → ℝ) (state : State) (action : Action) :
    pmfVariance (M.oneStepLaw state action)
        (fun outcome => M.rewardValue outcome.1 + continuation outcome.2) =
      pmfVariance (M.rewardLaw state action) M.rewardValue +
        pmfVariance (M.transition state action) continuation := by
  have transition_translate (reward : Reward) :
      pmfVariance (M.transition state action)
          (fun next => M.rewardValue reward + continuation next) =
        pmfVariance (M.transition state action) continuation := by
    rw [pmfVariance_eq_exp_sq_sub_sq_exp, pmfVariance_eq_exp_sq_sub_sq_exp]
    simp_rw [add_sq]
    rw [pmfExp_add, pmfExp_add, pmfExp_const_mul, pmfExp_const, pmfExp_add,
      pmfExp_const]
    ring
  have reward_translate (constant : ℝ) :
      pmfVariance (M.rewardLaw state action)
          (fun reward => M.rewardValue reward + constant) =
        pmfVariance (M.rewardLaw state action) M.rewardValue := by
    rw [pmfVariance_eq_exp_sq_sub_sq_exp, pmfVariance_eq_exp_sq_sub_sq_exp]
    simp_rw [add_sq]
    rw [pmfExp_add, pmfExp_add, pmfExp_mul_const, pmfExp_const, pmfExp_add,
      pmfExp_const, pmfExp_const_mul]
    ring
  let payoff : Reward → State → ℝ := fun reward next =>
    M.rewardValue reward + continuation next
  change pmfVariance (pmfProd (M.rewardLaw state action) (M.transition state action))
      (fun outcome => payoff outcome.1 outcome.2) =
    pmfVariance (M.rewardLaw state action) M.rewardValue +
      pmfVariance (M.transition state action) continuation
  rw [pmfVariance_pmfProd_eq_exp_condVariance_add_variance_condExp]
  calc
    pmfExp (M.rewardLaw state action)
        (fun reward =>
          pmfVariance (M.transition state action)
            (fun next => M.rewardValue reward + continuation next)) +
        pmfVariance (M.rewardLaw state action)
          (fun reward =>
            pmfExp (M.transition state action)
              (fun next => M.rewardValue reward + continuation next)) =
      pmfVariance (M.transition state action) continuation +
        pmfVariance (M.rewardLaw state action) M.rewardValue := by
          rw [show (fun reward =>
            pmfVariance (M.transition state action)
              (fun next => M.rewardValue reward + continuation next)) =
            fun _ => pmfVariance (M.transition state action) continuation by
              funext reward
              exact transition_translate reward]
          rw [pmfExp_const]
          congr 1
          have mean_translate :
              (fun reward =>
                pmfExp (M.transition state action)
                  (fun next => M.rewardValue reward + continuation next)) =
                fun reward => M.rewardValue reward +
                  pmfExp (M.transition state action) continuation := by
            funext reward
            rw [pmfExp_add, pmfExp_const]
          rw [mean_translate]
          exact reward_translate _
    _ = _ := by ring

end FiniteStochasticRewardMDP
end AppliedModelingLib
