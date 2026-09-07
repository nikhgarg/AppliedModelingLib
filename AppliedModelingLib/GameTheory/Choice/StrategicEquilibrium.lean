import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace AppliedModelingLib

open MeasureTheory

/-!
# Strategic Equilibrium Data

Reusable student/action plus planner/policy equilibrium interfaces.

This generalizes the pattern where many individual agents choose feasible best
responses, a planner or school chooses a feasible policy maximizing an
objective, and an auxiliary consistency condition connects the two layers.

## Main declarations

- `StrategicEquilibriumData`
- `IsStrategicEquilibrium`
- `IsStrategicEquilibriumAE`
- `isStrategicEquilibriumAE_of_strategicEquilibrium`
-/

/--
Strategic equilibrium data with a student/action best-response layer and a
school/policy best-response layer.  The field names follow admissions
terminology because this interface was first needed for strategic admissions
papers.
-/
structure StrategicEquilibriumData (Student Action SchoolPolicy : Type*) where
  studentActionFeasible : Student → Action → Prop
  chosenStudentAction : Student → Action
  studentPayoff : Student → Action → ℝ
  schoolPolicyFeasible : SchoolPolicy → Prop
  chosenSchoolPolicy : SchoolPolicy
  schoolObjective : SchoolPolicy → ℝ
  assignmentConsistent : Prop

/--
Pointwise strategic equilibrium: all individual choices are feasible weak best
responses, the chosen policy is a feasible weak maximizer, and the consistency
condition holds.
-/
def IsStrategicEquilibrium {Agent Action Policy : Type*}
    (E : StrategicEquilibriumData Agent Action Policy) : Prop :=
  (∀ student, E.studentActionFeasible student (E.chosenStudentAction student)) ∧
    (∀ student action, E.studentActionFeasible student action →
      E.studentPayoff student action ≤
        E.studentPayoff student (E.chosenStudentAction student)) ∧
      E.schoolPolicyFeasible E.chosenSchoolPolicy ∧
        (∀ policy, E.schoolPolicyFeasible policy →
          E.schoolObjective policy ≤ E.schoolObjective E.chosenSchoolPolicy) ∧
            E.assignmentConsistent

/--
Almost-everywhere strategic equilibrium: individual feasibility and best
responses hold almost everywhere under the agent law, while the policy and
consistency obligations remain pointwise.
-/
def IsStrategicEquilibriumAE
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (E : StrategicEquilibriumData Agent Action Policy) : Prop :=
  (∀ᵐ student ∂μ, E.studentActionFeasible student (E.chosenStudentAction student)) ∧
    (∀ᵐ student ∂μ, ∀ action, E.studentActionFeasible student action →
      E.studentPayoff student action ≤
        E.studentPayoff student (E.chosenStudentAction student)) ∧
      E.schoolPolicyFeasible E.chosenSchoolPolicy ∧
        (∀ policy, E.schoolPolicyFeasible policy →
          E.schoolObjective policy ≤ E.schoolObjective E.chosenSchoolPolicy) ∧
            E.assignmentConsistent

theorem isStrategicEquilibriumAE_agent_feasible_ae
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibriumAE μ E) :
    ∀ᵐ agent ∂μ, E.studentActionFeasible agent (E.chosenStudentAction agent) :=
  hEq.1

theorem isStrategicEquilibriumAE_agent_best_response_ae
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibriumAE μ E) :
    ∀ᵐ agent ∂μ, ∀ action, E.studentActionFeasible agent action →
      E.studentPayoff agent action ≤ E.studentPayoff agent (E.chosenStudentAction agent) :=
  hEq.2.1

theorem isStrategicEquilibriumAE_policy_feasible
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibriumAE μ E) :
    E.schoolPolicyFeasible E.chosenSchoolPolicy :=
  hEq.2.2.1

theorem isStrategicEquilibriumAE_policy_best_response
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibriumAE μ E) :
    ∀ policy, E.schoolPolicyFeasible policy →
      E.schoolObjective policy ≤ E.schoolObjective E.chosenSchoolPolicy :=
  hEq.2.2.2.1

theorem isStrategicEquilibriumAE_consistency
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibriumAE μ E) :
    E.assignmentConsistent :=
  hEq.2.2.2.2

/--
Every pointwise strategic equilibrium is an a.e. strategic equilibrium under
any agent law.
-/
theorem isStrategicEquilibriumAE_of_strategicEquilibrium
    {Agent Action Policy : Type*} [MeasurableSpace Agent]
    {μ : Measure Agent}
    {E : StrategicEquilibriumData Agent Action Policy}
    (hEq : IsStrategicEquilibrium E) :
    IsStrategicEquilibriumAE μ E := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun agent => hEq.1 agent
  · exact Filter.Eventually.of_forall fun agent action hfeasible =>
      hEq.2.1 agent action hfeasible
  · exact hEq.2.2.1
  · exact hEq.2.2.2.1
  · exact hEq.2.2.2.2

end AppliedModelingLib
