import AppliedModelingLib.Alignment.Welfare.Distortion
import AppliedModelingLib.GameTheory.PreferenceGame.KLConstrained

/-!
# Population preference games as context-free finite games

The heterogeneous-population Bradley--Terry model is a one-context instance of
a finite preference game. This module proves the policy and KL bridges needed
to reuse constrained and regularized preference-game equilibrium theorems.

## Main declarations

- `contextFreeAlternativePolicy`
- `contextFree_constrainedPreferenceEquilibrium_implies_populationEquilibrium`
- `contextFree_regularizedPreferenceEquilibrium_implies_populationEquilibrium`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

open Learning.HumanFeedback
open GameTheory.PreferenceGame

/-- Embed a context-free alternative PMF as a policy on the singleton context. -/
noncomputable def contextFreeAlternativePolicy {Alternative : Type*}
    (policy : PMF Alternative) : FinitePolicy PUnit Alternative :=
  fun _ => policy

/--
The singleton-context average KL divergence of context-free policies is their
ordinary finite KL divergence.
-/
theorem contextFree_contextAveragedPolicyKLDivergence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (first second : PMF Alternative) :
    contextAveragedPolicyKLDivergence (PMF.pure PUnit.unit.{1})
      (contextFreeAlternativePolicy first) (contextFreeAlternativePolicy second) =
      finiteKLDivergence first second := by
  simp [contextAveragedPolicyKLDivergence, pointwisePolicyKLDivergence,
    contextFreeAlternativePolicy]

/--
The singleton-context preference-game payoff is its policy-level
Bradley--Terry margin plus one half.
-/
theorem contextFree_preferenceGamePayoff_eq_margin_add_half
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (first second : PMF Alternative) :
    preferenceGamePayoff (PMF.pure PUnit.unit.{1})
      (populationBradleyTerryPreference population utility btScale)
      (contextFreeAlternativePolicy first) (contextFreeAlternativePolicy second) =
      populationBradleyTerryPolicyMargin population utility btScale first second + (1 : ℝ) / 2 := by
  unfold preferenceGamePayoff Learning.HumanFeedback.policyPreference
  rw [pmfExp_pure]
  change pmfPairExp first second (fun left right =>
      (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} left right) =
    populationBradleyTerryPolicyMargin population utility btScale first second + (1 : ℝ) / 2
  unfold populationBradleyTerryPolicyMargin
  rw [pmfPairExp_sub]
  have hconstant :
      pmfPairExp first second (fun _ _ => (1 : ℝ) / 2) = (1 : ℝ) / 2 := by
    simp [pmfPairExp]
  rw [hconstant]
  ring

/--
A constrained singleton-context preference-game equilibrium induces the
population Bradley--Terry equilibrium condition at the same finite KL budget.
-/
theorem contextFree_constrainedPreferenceEquilibrium_implies_populationEquilibrium
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative)
    (hequilibrium : IsConstrainedPreferenceGameEquilibrium
      (PMF.pure PUnit.unit.{1}) (populationBradleyTerryPreference population utility btScale)
      (contextFreeAlternativePolicy reference) klBudget (contextFreeAlternativePolicy policy)) :
    IsConstrainedPopulationBradleyTerryEquilibrium
      population utility btScale reference klBudget policy := by
  constructor
  · unfold InFiniteKLBall
    have hfeasible := hequilibrium.1
    unfold InContextAveragedKLBall at hfeasible
    simpa only [contextFree_contextAveragedPolicyKLDivergence] using hfeasible
  · intro opponent hopponent
    have hopponentGame : InContextAveragedKLBall (PMF.pure PUnit.unit.{1})
        (contextFreeAlternativePolicy reference) klBudget
        (contextFreeAlternativePolicy opponent) := by
      unfold InContextAveragedKLBall
      simpa only [contextFree_contextAveragedPolicyKLDivergence] using hopponent
    have hwin := hequilibrium.2 (contextFreeAlternativePolicy opponent) hopponentGame
    rw [contextFree_preferenceGamePayoff_eq_margin_add_half] at hwin
    linarith

/--
A policy satisfying the source attained constrained `argmax min` definition
has the population Bradley--Terry equilibrium inequality used by Theorem 7.
-/
theorem contextFree_constrainedPopulationBradleyTerryMaximin_implies_populationEquilibrium
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative)
    (hmaximin : IsConstrainedPopulationBradleyTerryMaximin
      population utility btScale reference klBudget policy) :
    IsConstrainedPopulationBradleyTerryEquilibrium
      population utility btScale reference klBudget policy := by
  apply contextFree_constrainedPreferenceEquilibrium_implies_populationEquilibrium
    population utility btScale reference klBudget policy
  simpa only [contextFreeAlternativePolicy] using
    finiteKLPreferenceMaximin_isConstrainedPreferenceGameEquilibrium
      (populationBradleyTerryPreference population utility btScale)
      reference klBudget policy hmaximin

/-- Every nonnegative finite KL budget admits an attained population NLHF maximin policy. -/
theorem exists_constrainedPopulationBradleyTerryMaximin
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (hbudget : 0 ≤ klBudget) :
    ∃ policy : PMF Alternative,
      IsConstrainedPopulationBradleyTerryMaximin
        population utility btScale reference klBudget policy := by
  exact exists_finiteKLPreferenceMaximin
    (populationBradleyTerryPreference population utility btScale)
    reference klBudget hbudget

/--
A finite regularized population preference-game equilibrium is a constrained
population equilibrium at the ordinary KL divergence it attains from the
context-free reference policy.
-/
theorem contextFree_regularizedPreferenceEquilibrium_implies_populationEquilibrium
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference policy : PMF Alternative) (klRegularization : ℝ)
    (hregularization : 0 ≤ klRegularization)
    (hequilibrium : IsRegularizedPreferenceGameEquilibrium
      (PMF.pure PUnit.unit.{1}) (populationBradleyTerryPreference population utility btScale)
      (contextFreeAlternativePolicy reference) (contextFreeAlternativePolicy policy)
      klRegularization) :
    IsConstrainedPopulationBradleyTerryEquilibrium population utility btScale reference
      (finiteKLDivergence policy reference) policy := by
  apply contextFree_constrainedPreferenceEquilibrium_implies_populationEquilibrium
    population utility btScale reference (finiteKLDivergence policy reference) policy
  have hconstrained := regularizedPreferenceGameEquilibrium_isConstrainedAt_attainedKL
    (PMF.pure PUnit.unit.{1}) (populationBradleyTerryPreference population utility btScale)
    (contextFreeAlternativePolicy reference) (contextFreeAlternativePolicy policy)
    klRegularization hregularization hequilibrium
  simpa only [contextFree_contextAveragedPolicyKLDivergence] using hconstrained

end Welfare
end Alignment
end AppliedModelingLib
