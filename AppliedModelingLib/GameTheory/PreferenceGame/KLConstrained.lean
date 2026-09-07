import AppliedModelingLib.GameTheory.PreferenceGame.Basic
import AppliedModelingLib.Learning.HumanFeedback.KLConstrained

/-!
# KL-constrained finite preference games

This module supplies the direct regularized-to-constrained bridge used when a
symmetric preference-game equilibrium is compared to policies with no greater
KL divergence from the same reference policy.

## Main declarations

- `IsConstrainedPreferenceGameEquilibrium`
- `regularizedPreferenceGameEquilibrium_isConstrainedAt_attainedKL`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open Learning.HumanFeedback

/--
A preference-game policy is an equilibrium in a finite KL-constrained policy
set when it is feasible and wins each feasible comparison with probability at
least one half.
-/
def IsConstrainedPreferenceGameEquilibrium
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference : FinitePolicy Context Response) (klBudget : ℝ)
    (policy : FinitePolicy Context Response) : Prop :=
  InContextAveragedKLBall contextLaw reference klBudget policy ∧
    ∀ opponent, InContextAveragedKLBall contextLaw reference klBudget opponent →
      1 / 2 ≤ preferenceGamePayoff contextLaw preference policy opponent

/--
A finite regularized preference-game equilibrium is a constrained equilibrium
at the KL radius it attains. This is the regularized-to-constrained direction
of the source constrained/regularized NLHF equivalence.
-/
theorem regularizedPreferenceGameEquilibrium_isConstrainedAt_attainedKL
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference policy : FinitePolicy Context Response) (klRegularization : ℝ)
    (hregularization : 0 ≤ klRegularization)
    (hequilibrium : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference policy klRegularization) :
    IsConstrainedPreferenceGameEquilibrium contextLaw preference reference
      (contextAveragedPolicyKLDivergence contextLaw policy reference) policy := by
  constructor
  · unfold InContextAveragedKLBall
    exact le_rfl
  · intro opponent hopponent
    have hequilibriumAtOpponent := hequilibrium opponent
    have hpenalty :
        klRegularization * contextAveragedPolicyKLDivergence contextLaw opponent reference ≤
          klRegularization * contextAveragedPolicyKLDivergence contextLaw policy reference :=
      mul_le_mul_of_nonneg_left hopponent hregularization
    unfold IsRegularizedPreferenceGameEquilibrium regularizedPreferenceGamePayoff
      preferenceGamePayoff at hequilibriumAtOpponent
    linarith

end PreferenceGame
end GameTheory
end AppliedModelingLib
