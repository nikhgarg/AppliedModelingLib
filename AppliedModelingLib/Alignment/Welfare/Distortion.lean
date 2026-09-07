import AppliedModelingLib.Alignment.Welfare.PolicyLinearization
import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.GameTheory.PreferenceGame.ConstrainedMinimax

/-!
# Finite KL-constrained welfare comparison

This module keeps a reference policy, a KL budget, and the heterogeneous
utility population separate. It gives the finite constrained-game vocabulary
used by alignment-distortion results without defining a welfare ratio at zero
welfare.

## Main declarations

- `InFiniteKLBall`
- `IsConstrainedPopulationBradleyTerryMaximin`
- `IsConstrainedPopulationBradleyTerryEquilibrium`
- `constrainedPopulationBradleyTerryEquilibrium_welfare_lower_bound_source`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

/-- A finite policy belongs to the source KL ball around `reference`. -/
def InFiniteKLBall {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference : PMF Alternative) (klBudget : ℝ) (policy : PMF Alternative) : Prop :=
  finiteKLDivergence policy reference ≤ klBudget

/--
The attained finite-PMF form of the source Theorem-7 constrained
`argmax min` definition. Its preference payoff is the population
Bradley--Terry comparison law at the singleton context.
-/
def IsConstrainedPopulationBradleyTerryMaximin
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative) : Prop :=
  GameTheory.PreferenceGame.IsFiniteKLPreferenceMaximin
    (show Learning.HumanFeedback.PairwisePreference PUnit.{1} Alternative from
      populationBradleyTerryPreference population utility btScale)
    reference klBudget policy

/--
The population-limit constrained NLHF equilibrium condition. It records both
feasibility in the KL ball and the centered zero-sum equilibrium inequality
against every feasible opponent.
-/
def IsConstrainedPopulationBradleyTerryEquilibrium
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative) : Prop :=
  IsPopulationBradleyTerryMaximinOver population utility btScale
    (InFiniteKLBall reference klBudget) policy

/--
The source Theorem-7 welfare factor for a finite KL-constrained population
Bradley--Terry equilibrium. Any feasible benchmark can be used, including a
welfare-maximizing policy in the same KL ball.
-/
theorem constrainedPopulationBradleyTerryEquilibrium_welfare_lower_bound_source
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (reference : PMF Alternative) (klBudget : ℝ)
    (policy benchmark : PMF Alternative)
    (hpolicy : IsConstrainedPopulationBradleyTerryEquilibrium
      population utility btScale reference klBudget policy)
    (hbenchmark : InFiniteKLBall reference klBudget benchmark) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark ≤
      policyAverageUtility population utility policy :=
  populationBradleyTerryMaximin_welfare_lower_bound_source population utility hutility hbtScale
    (InFiniteKLBall reference klBudget) policy benchmark hpolicy hbenchmark

end Welfare
end Alignment
end AppliedModelingLib
