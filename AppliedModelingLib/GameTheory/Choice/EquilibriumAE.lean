import AppliedModelingLib.GameTheory.Choice.Equilibrium
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace AppliedModelingLib

open MeasureTheory

/-!
# Almost-Everywhere Choice Equilibrium

Measure-indexed variant of the reusable choice-equilibrium interface.  This is
for continuous or mixed type spaces where best response is intended to hold
almost everywhere under the realized information law rather than pointwise at
every syntactically possible information state.

## Main declarations

- `IsChoiceEquilibriumAE`
- `isChoiceEquilibriumAE_feasible_ae`
- `isChoiceEquilibriumAE_best_response_ae`
- `isChoiceEquilibriumAE_consistency`
- `isChoiceEquilibriumAE_of_pointwise`
- `isChoiceEquilibriumAE_of_forall_not_mem_null`
-/

/--
The chosen action is feasible and weakly maximizes payoff among feasible
actions for almost every information state under `μ`, and the auxiliary
consistency condition holds.
-/
def IsChoiceEquilibriumAE {Info Action : Type*} [MeasurableSpace Info]
    (μ : Measure Info) (E : ChoiceEquilibriumData Info Action) : Prop :=
  (∀ᵐ info ∂μ, E.actionFeasible info (E.chosenAction info)) ∧
    (∀ᵐ info ∂μ, ∀ action, E.actionFeasible info action →
      E.payoff info action ≤ E.payoff info (E.chosenAction info)) ∧
      E.consistency

theorem isChoiceEquilibriumAE_feasible_ae
    {Info Action : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibriumAE μ E) :
    ∀ᵐ info ∂μ, E.actionFeasible info (E.chosenAction info) :=
  hEq.1

theorem isChoiceEquilibriumAE_best_response_ae
    {Info Action : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibriumAE μ E) :
    ∀ᵐ info ∂μ, ∀ action, E.actionFeasible info action →
      E.payoff info action ≤ E.payoff info (E.chosenAction info) :=
  hEq.2.1

theorem isChoiceEquilibriumAE_consistency
    {Info Action : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibriumAE μ E) :
    E.consistency :=
  hEq.2.2

/--
Every pointwise choice equilibrium is an almost-everywhere equilibrium under
any information law.
-/
theorem isChoiceEquilibriumAE_of_pointwise
    {Info Action : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {E : ChoiceEquilibriumData Info Action}
    (hEq : IsChoiceEquilibrium E) :
    IsChoiceEquilibriumAE μ E := by
  refine ⟨?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun info =>
      isChoiceEquilibrium_feasible hEq info
  · exact Filter.Eventually.of_forall fun info action hfeasible =>
      isChoiceEquilibrium_best_response hEq info action hfeasible
  · exact isChoiceEquilibrium_consistency hEq

/--
Build an a.e. choice equilibrium when feasibility and best response hold
pointwise outside a null exception set.  This is the common continuous-type
bridge for off-support states and cutoff-boundary ties.
-/
theorem isChoiceEquilibriumAE_of_forall_not_mem_null
    {Info Action : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {E : ChoiceEquilibriumData Info Action}
    {exception : Set Info}
    (hexception : μ exception = 0)
    (hfeasible :
      ∀ info, info ∉ exception →
        E.actionFeasible info (E.chosenAction info))
    (hbest :
      ∀ info, info ∉ exception → ∀ action,
        E.actionFeasible info action →
          E.payoff info action ≤ E.payoff info (E.chosenAction info))
    (hconsistency : E.consistency) :
    IsChoiceEquilibriumAE μ E := by
  refine ⟨?_, ?_, hconsistency⟩
  · exact ae_of_forall_not_mem_null (μ := μ) hexception hfeasible
  · exact ae_of_forall_not_mem_null (μ := μ) hexception hbest

end AppliedModelingLib
