import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Linear transition models induce linear expected rewards

This module isolates the finite algebra used when a transition kernel has a
bilinear factorization
`P(next | state, action) = dot (feature state action) (basis next)`.
Integrating any bounded or unbounded real terminal score against that kernel
produces a reward that is linear in the same state-action feature.  No
probabilistic independence claim is hidden here: the terminal score may itself
already be an expectation against an arbitrary second law.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace PreferenceRL

open FiniteDimensionalNorms

noncomputable section

/--
The parameter induced by integrating a scalar terminal score against the
state-side basis of a finite linear transition model.
-/
def linearTransitionRewardParameter
    {NextState Feature : Type*} [Fintype NextState] [Fintype Feature]
    (basis : NextState → Feature → ℝ) (terminalScore : NextState → ℝ) :
    Feature → ℝ :=
  fun coordinate ↦ ∑ nextState, terminalScore nextState * basis nextState coordinate

/--
Finite linear-transition identity: if every real transition mass is the dot
product of a state-action feature and a next-state basis vector, then the
expected terminal score is the dot product with the induced parameter.
-/
theorem pmfExp_eq_dot_linearTransitionRewardParameter
    {State Action NextState Feature : Type*}
    [Fintype NextState] [DecidableEq NextState] [Fintype Feature]
    (nextLaw : State → Action → PMF NextState)
    (feature : State → Action → Feature → ℝ)
    (basis : NextState → Feature → ℝ)
    (terminalScore : NextState → ℝ)
    (hlinear : ∀ state action nextState,
      (nextLaw state action nextState).toReal =
        dot (feature state action) (basis nextState))
    (state : State) (action : Action) :
    pmfExp (nextLaw state action) terminalScore =
      dot (feature state action)
        (linearTransitionRewardParameter basis terminalScore) := by
  classical
  unfold linearTransitionRewardParameter
  rw [dot_weighted_sum_right]
  unfold pmfExp
  apply Finset.sum_congr rfl
  intro nextState _
  rw [hlinear]
  ring

/--
The terminal score faced by one learner when its terminal state is compared
with an independent terminal state drawn from the opponent's law.
-/
def expectedPreferenceAgainst
    {OwnState OpponentState : Type*}
    [Fintype OpponentState] [DecidableEq OpponentState]
    (opponentLaw : PMF OpponentState)
    (preference : OwnState → OpponentState → ℝ) (ownState : OwnState) : ℝ :=
  pmfExp opponentLaw (preference ownState)

/--
The expected comparison feedback constructed from a finite linear transition
kernel is linear in the kernel's state-action feature.  This is the reusable
algebraic bridge needed to feed comparison feedback to a linear adversarial
MDP learner.
-/
theorem expectedPreferenceReward_eq_dot_linearTransitionRewardParameter
    {State Action NextState OpponentState Feature : Type*}
    [Fintype NextState] [DecidableEq NextState]
    [Fintype OpponentState] [DecidableEq OpponentState]
    [Fintype Feature]
    (nextLaw : State → Action → PMF NextState)
    (feature : State → Action → Feature → ℝ)
    (basis : NextState → Feature → ℝ)
    (opponentLaw : PMF OpponentState)
    (preference : NextState → OpponentState → ℝ)
    (hlinear : ∀ state action nextState,
      (nextLaw state action nextState).toReal =
        dot (feature state action) (basis nextState))
    (state : State) (action : Action) :
    pmfExp (nextLaw state action)
        (expectedPreferenceAgainst opponentLaw preference) =
      dot (feature state action)
        (linearTransitionRewardParameter basis
          (expectedPreferenceAgainst opponentLaw preference)) :=
  pmfExp_eq_dot_linearTransitionRewardParameter nextLaw feature basis
    (expectedPreferenceAgainst opponentLaw preference) hlinear state action

end

end PreferenceRL
end AppliedModelingLib
