import Mathlib.Data.Real.Basic

namespace AppliedModelingLib

/-!
# Choice Equilibrium Data

Reusable one-agent choice-equilibrium interface: a feasible chosen action,
pointwise weak optimality among feasible actions, and an auxiliary consistency
certificate.

## Main declarations

- `ChoiceEquilibriumData`
- `IsChoiceEquilibrium`
- `isChoiceEquilibrium_feasible`
- `isChoiceEquilibrium_best_response`
- `isChoiceEquilibrium_consistency`
- `isChoiceEquilibrium_of_equiv`
-/

/--
Static choice-equilibrium data.  `Info` packages the agent's type or
information, `Action` is the action space, and `consistency` carries any
domain-specific fixed-point or estimation-consistency condition.
-/
structure ChoiceEquilibriumData (Info Action : Type*) where
  actionFeasible : Info → Action → Prop
  chosenAction : Info → Action
  payoff : Info → Action → ℝ
  consistency : Prop

/--
The chosen action is feasible, weakly maximizes payoff among feasible actions,
and the auxiliary consistency condition holds.
-/
def IsChoiceEquilibrium {Info Action : Type*}
    (E : ChoiceEquilibriumData Info Action) : Prop :=
  (∀ info, E.actionFeasible info (E.chosenAction info)) ∧
    (∀ info action, E.actionFeasible info action →
      E.payoff info action ≤ E.payoff info (E.chosenAction info)) ∧
      E.consistency

theorem isChoiceEquilibrium_feasible
    {Info Action : Type*} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E) (info : Info) :
    E.actionFeasible info (E.chosenAction info) :=
  hEq.1 info

theorem isChoiceEquilibrium_best_response
    {Info Action : Type*} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E) (info : Info) (action : Action)
    (hfeasible : E.actionFeasible info action) :
    E.payoff info action ≤ E.payoff info (E.chosenAction info) :=
  hEq.2.1 info action hfeasible

theorem isChoiceEquilibrium_consistency
    {Info Action : Type*} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E) :
    E.consistency :=
  hEq.2.2

/--
Transfer a choice equilibrium across an extensionally equal choice problem.

The target problem may use different definitions for feasibility, chosen
actions, payoffs, or the consistency certificate, as long as the supplied
bridges translate each component back to the source problem.
-/
theorem isChoiceEquilibrium_of_equiv
    {Info Action : Type*} {E F : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E)
    (hfeasible_to_E :
      ∀ info action, F.actionFeasible info action → E.actionFeasible info action)
    (hfeasible_from_E :
      ∀ info, E.actionFeasible info (E.chosenAction info) →
        F.actionFeasible info (F.chosenAction info))
    (hpayoff_action :
      ∀ info action, F.payoff info action = E.payoff info action)
    (hpayoff_chosen :
      ∀ info, E.payoff info (E.chosenAction info) =
        F.payoff info (F.chosenAction info))
    (hconsistency : E.consistency → F.consistency) :
    IsChoiceEquilibrium F := by
  refine ⟨?_, ?_, ?_⟩
  · intro info
    exact hfeasible_from_E info (hEq.1 info)
  · intro info action hfeasible
    calc
      F.payoff info action = E.payoff info action :=
        hpayoff_action info action
      _ ≤ E.payoff info (E.chosenAction info) :=
        hEq.2.1 info action (hfeasible_to_E info action hfeasible)
      _ = F.payoff info (F.chosenAction info) :=
        hpayoff_chosen info
  · exact hconsistency hEq.2.2

end AppliedModelingLib
