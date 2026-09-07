import AppliedModelingLib.Learning.ReinforcementLearning.Preference.OptimisticModel
import Mathlib.Tactic

/-!
# Structured finite reinforcement-learning models

Definitions used by generalized-eluder analyses of factored MDPs and POMDPs.
The types are finite so factorization, observation transport, and trajectory
support can be stated directly with PMFs.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/-- A function depends only on the coordinates in `parents`. -/
def DependsOnlyOnCoordinates
    {Factor Value Output : Type*} [DecidableEq Factor]
    (parents : Finset Factor) (function : (Factor → Value) → Output) : Prop :=
  ∀ first second, (∀ factor ∈ parents, first factor = second factor) →
    function first = function second

/-- A finite factored MDP.  Each next-state factor has a local conditional
law depending only on its declared parent coordinates, and the reward is a
sum of factor-local components. -/
structure FiniteFactoredMDP
    (Step Factor Value Action : Type*)
    [Fintype Factor] [DecidableEq Factor]
    [Fintype Value] [DecidableEq Value] where
  parents : Factor → Finset Factor
  localTransition : Step → Factor → (Factor → Value) → Action → PMF Value
  transitionLaw : Step → (Factor → Value) → Action → PMF (Factor → Value)
  transition_local : ∀ step factor action,
    DependsOnlyOnCoordinates (parents factor)
      (fun state ↦ localTransition step factor state action)
  transition_factorizes : ∀ step state action nextState,
    transitionLaw step state action nextState =
      ∏ factor, localTransition step factor state action (nextState factor)
  localReward : Step → Factor → Value → ℝ

namespace FiniteFactoredMDP

/-- The product transition law displayed in the factored-MDP example. -/
noncomputable def transition
    {Step Factor Value Action : Type*}
    [Fintype Factor] [DecidableEq Factor]
    [Fintype Value] [DecidableEq Value]
    (model : FiniteFactoredMDP Step Factor Value Action)
    (step : Step) (state : Factor → Value) (action : Action) :
    PMF (Factor → Value) :=
  model.transitionLaw step state action

@[simp] theorem transition_apply
    {Step Factor Value Action : Type*}
    [Fintype Factor] [DecidableEq Factor]
    [Fintype Value] [DecidableEq Value]
    (model : FiniteFactoredMDP Step Factor Value Action)
    (step : Step) (state : Factor → Value) (action : Action)
    (nextState : Factor → Value) :
    model.transition step state action nextState =
      ∏ factor, model.localTransition step factor state action (nextState factor) :=
  model.transition_factorizes step state action nextState

/-- The additive reward factorization displayed in the source. -/
noncomputable def reward
    {Step Factor Value Action : Type*}
    [Fintype Factor] [DecidableEq Factor]
    [Fintype Value] [DecidableEq Value]
    (model : FiniteFactoredMDP Step Factor Value Action)
    (step : Step) (state : Factor → Value) : ℝ :=
  ∑ factor, model.localReward step factor (state factor)

end FiniteFactoredMDP

/-- A finite-horizon POMDP with hidden states, emitted observations, and
controlled state transitions. -/
structure FinitePOMDP (Horizon : ℕ) (State Observation Action : Type*)
    [Fintype State] [DecidableEq State]
    [Fintype Observation] [DecidableEq Observation] where
  initial : PMF State
  transition : Fin Horizon → State → Action → PMF State
  observation : Fin (Horizon + 1) → State → PMF Observation

namespace FinitePOMDP

/-- Observation law induced by a hidden-state distribution at one stage. -/
noncomputable def observedStateMixture
    {Horizon : ℕ} {State Observation Action : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Observation] [DecidableEq Observation]
    (model : FinitePOMDP Horizon State Observation Action)
    (stage : Fin (Horizon + 1)) (stateLaw : PMF State) : PMF Observation :=
  stateLaw.bind (model.observation stage)

/-- The source's `alpha`-observability condition, with its displayed L1
normalization: every stage's observation channel preserves at least an
`alpha` fraction of hidden-state L1 separation. -/
def IsAlphaObservable
    {Horizon : ℕ} {State Observation Action : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Observation] [DecidableEq Observation]
    (model : FinitePOMDP Horizon State Observation Action) (alpha : ℝ) : Prop :=
  ∀ stage first second,
    alpha * pmfL1Error first second ≤
      pmfL1Error (model.observedStateMixture stage first)
        (model.observedStateMixture stage second)

/-- A complete finite POMDP path. -/
structure Path
    {Horizon : ℕ} (State Observation Action : Type*) where
  state : Fin (Horizon + 1) → State
  observation : Fin (Horizon + 1) → Observation
  action : Fin Horizon → Action

/-- A path has positive probability under the finite POMDP. -/
def Path.IsCompatible
    {Horizon : ℕ} {State Observation Action : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Observation] [DecidableEq Observation]
    (model : FinitePOMDP Horizon State Observation Action)
    (path : Path (Horizon := Horizon) State Observation Action) : Prop :=
  0 < (model.initial (path.state 0)).toReal ∧
  (∀ stage : Fin (Horizon + 1),
    0 < (model.observation stage (path.state stage) (path.observation stage)).toReal) ∧
  ∀ stage : Fin Horizon,
    0 < (model.transition stage (path.state stage.castSucc) (path.action stage)
      (path.state stage.succ)).toReal

/-- Two observation/action arrays agree on the most recent `memory` steps
ending at `stage`.  The zero-based inequalities encode
`(o,a)_{max(0,h-m+1):h-1}, o_h`. -/
def SameRecentHistory
    {Horizon : ℕ} {Observation Action : Type*}
    (memory : ℕ) (stage : Fin (Horizon + 1))
    (firstObservation secondObservation : Fin (Horizon + 1) → Observation)
    (firstAction secondAction : Fin Horizon → Action) : Prop :=
  (∀ index, index.val ≤ stage.val → stage.val < index.val + memory →
    firstObservation index = secondObservation index) ∧
  (∀ index, index.val < stage.val → stage.val < index.val + memory →
    firstAction index = secondAction index)

/-- The paper's `m`-step decodability definition.  A decoder reconstructs the
hidden state on every positive-probability path and is local to the most
recent `memory` observations/actions. -/
def IsMStepDecodable
    {Horizon : ℕ} {State Observation Action : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype Observation] [DecidableEq Observation]
    (model : FinitePOMDP Horizon State Observation Action) (memory : ℕ) : Prop :=
  ∃ decoder : Fin (Horizon + 1) →
      (Fin (Horizon + 1) → Observation) → (Fin Horizon → Action) → State,
    (∀ stage firstObservation secondObservation firstAction secondAction,
      SameRecentHistory memory stage firstObservation secondObservation
        firstAction secondAction →
      decoder stage firstObservation firstAction =
        decoder stage secondObservation secondAction) ∧
    ∀ path : Path State Observation Action, path.IsCompatible model → ∀ stage,
      path.state stage = decoder stage path.observation path.action

end FinitePOMDP

/-- The generalized eluder-type condition used by OMLE.  Historical
exploration-policy squared-TV control implies a cumulative current-policy TV
bound supplied by `xi`. -/
def SatisfiesGeneralizedEluderCondition
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [DecidableEq Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (trueModel : Model) (exploration : Policy → Finset Policy)
    (dimension explorationCard : ℕ)
    (xi : ℕ → ℕ → ℝ → ℕ → ℝ) : Prop :=
  (∀ policy, (exploration policy).card ≤ explorationCard) ∧
  ∀ (rounds : ℕ) (budget : ℝ)
      (model : Fin rounds → Model) (policy : Fin rounds → Policy),
    (∀ time : Fin rounds,
      (∑ prior ∈ (Finset.univ.filter fun prior : Fin rounds ↦ prior.val < time.val),
        ∑ alternative ∈ exploration (policy prior),
          pmfTotalVariation
            (trajectoryLaw (model time) alternative)
            (trajectoryLaw trueModel alternative) ^ 2) ≤ budget) →
    (∑ time : Fin rounds,
      pmfTotalVariation
        (trajectoryLaw (model time) (policy time))
        (trajectoryLaw trueModel (policy time))) ≤
      xi dimension rounds budget explorationCard

end PreferenceRL

end AppliedModelingLib
