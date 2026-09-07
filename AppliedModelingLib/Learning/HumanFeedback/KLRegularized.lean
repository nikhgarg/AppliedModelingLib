import AppliedModelingLib.Foundations.Optimization.EntropyRegularized
import AppliedModelingLib.Learning.HumanFeedback.Policy

/-!
# Contextwise KL-regularized policy optimization

This module lifts the finite Gibbs variational identity from a single response
PMF to a policy indexed by finite contexts.  The lift is deliberately generic:
DPO and Nash-style policy updates can share the same contextwise optimizer
without importing one another's paper-specific modules.

## Main declarations

- `contextExponentialTiltPolicy`
- `contextExponentialTiltObjective`
- `contextExponentialTiltObjective_eq_logPartition_sub_kl`
- `contextExponentialTiltObjective_le_at_exponentialTilt`
- `contextExponentialTiltObjective_globalMax_unique`
- `contextExponentialTiltPolicy_add_context_constant`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- Apply a finite exponential tilt independently at every context. -/
noncomputable def contextExponentialTiltPolicy {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ) :
    FinitePolicy Context Response :=
  fun context => exponentialTilt (reference context) (utility context) inverseTemperature

/-- The context-distribution average of scaled KL-regularized policy objectives. -/
noncomputable def contextExponentialTiltObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ) : ℝ :=
  pmfExp contextLaw fun context =>
    exponentialTiltObjective (reference context) (candidate context)
      (utility context) inverseTemperature

/-- A contextwise exponential tilt preserves full support of a reference policy. -/
theorem contextExponentialTiltPolicy_fullSupport
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hreference : PolicyFullSupport reference) :
    PolicyFullSupport (contextExponentialTiltPolicy reference utility inverseTemperature) := by
  intro context
  exact exponentialTilt_fullSupport (reference context) (utility context)
    inverseTemperature (hreference context)

/-- A context-only utility shift does not change the contextwise tilted policy. -/
theorem contextExponentialTiltPolicy_add_context_constant
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (shift : Context → ℝ)
    (inverseTemperature : ℝ) :
    contextExponentialTiltPolicy reference
        (fun context response => utility context response + shift context)
        inverseTemperature =
      contextExponentialTiltPolicy reference utility inverseTemperature := by
  apply finitePolicy_ext
  intro context
  exact exponentialTilt_add_constant (reference context) (utility context)
    (shift context) inverseTemperature

/-- The contextwise objective is the average log partition minus average KL to the tilt. -/
theorem contextExponentialTiltObjective_eq_logPartition_sub_kl
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hreference : PolicyFullSupport reference) :
    contextExponentialTiltObjective contextLaw reference candidate utility inverseTemperature =
      pmfExp contextLaw fun context =>
        Real.log (Probability.finiteMGF (reference context) (utility context) inverseTemperature) -
          finiteKLDivergence (candidate context)
            (exponentialTilt (reference context) (utility context) inverseTemperature) := by
  unfold contextExponentialTiltObjective
  refine pmfExp_congr contextLaw fun context => ?_
  exact exponentialTiltObjective_eq_logPartition_sub_kl
    (reference context) (candidate context) (utility context)
    inverseTemperature (hreference context)

/-- The contextwise exponential tilt maximizes the averaged scaled objective. -/
theorem contextExponentialTiltObjective_le_at_exponentialTilt
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hreference : PolicyFullSupport reference) :
    contextExponentialTiltObjective contextLaw reference candidate utility inverseTemperature ≤
      contextExponentialTiltObjective contextLaw reference
        (contextExponentialTiltPolicy reference utility inverseTemperature)
        utility inverseTemperature := by
  unfold contextExponentialTiltObjective contextExponentialTiltPolicy
  refine pmfExp_le_pmfExp_of_forall_le contextLaw _ _ fun context => ?_
  exact exponentialTiltObjective_le_at_exponentialTilt
    (reference context) (candidate context) (utility context)
    inverseTemperature (hreference context)

/--
Under a full-support context law, every policy other than the contextwise
exponential tilt has strictly smaller averaged entropy-regularized objective.
The context-law support condition is essential: an objective averaged over a
zero-mass context cannot uniquely identify a policy at that context.
-/
theorem contextExponentialTiltObjective_lt_at_exponentialTilt_of_ne
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference)
    (hne : candidate ≠ contextExponentialTiltPolicy reference utility inverseTemperature) :
    contextExponentialTiltObjective contextLaw reference candidate utility inverseTemperature <
      contextExponentialTiltObjective contextLaw reference
        (contextExponentialTiltPolicy reference utility inverseTemperature)
        utility inverseTemperature := by
  have hcontext : ∃ context,
      candidate context ≠ exponentialTilt (reference context) (utility context) inverseTemperature := by
    by_contra hnot
    push Not at hnot
    apply hne
    apply finitePolicy_ext
    intro context
    exact hnot context
  obtain ⟨witness, hwitness⟩ := hcontext
  have hpointwise_le : ∀ context,
      exponentialTiltObjective (reference context) (candidate context)
        (utility context) inverseTemperature ≤
        exponentialTiltObjective (reference context)
          (exponentialTilt (reference context) (utility context) inverseTemperature)
          (utility context) inverseTemperature := by
    intro context
    exact exponentialTiltObjective_le_at_exponentialTilt
      (reference context) (candidate context) (utility context)
      inverseTemperature (hreference context)
  have hpointwise_lt :
      exponentialTiltObjective (reference witness) (candidate witness)
        (utility witness) inverseTemperature <
        exponentialTiltObjective (reference witness)
          (exponentialTilt (reference witness) (utility witness) inverseTemperature)
          (utility witness) inverseTemperature :=
    exponentialTiltObjective_lt_at_exponentialTilt_of_ne
      (reference witness) (candidate witness) (utility witness)
      inverseTemperature (hreference witness) hwitness
  unfold contextExponentialTiltObjective contextExponentialTiltPolicy pmfExp
  refine Finset.sum_lt_sum ?_ ?_
  · intro context _
    exact mul_le_mul_of_nonneg_left (hpointwise_le context) ENNReal.toReal_nonneg
  · exact ⟨witness, Finset.mem_univ _,
      mul_lt_mul_of_pos_left hpointwise_lt (hcontextLaw witness)⟩

/--
An averaged contextwise entropy-regularized objective reaches the tilted value
exactly at the contextwise tilt when every context has positive mass.
-/
theorem contextExponentialTiltObjective_eq_at_exponentialTilt_iff
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference) :
    contextExponentialTiltObjective contextLaw reference candidate utility inverseTemperature =
      contextExponentialTiltObjective contextLaw reference
        (contextExponentialTiltPolicy reference utility inverseTemperature)
        utility inverseTemperature ↔
      candidate = contextExponentialTiltPolicy reference utility inverseTemperature := by
  constructor
  · intro heq
    by_contra hne
    have hlt := contextExponentialTiltObjective_lt_at_exponentialTilt_of_ne
      contextLaw reference candidate utility inverseTemperature hcontextLaw hreference hne
    linarith
  · intro heq
    subst candidate
    rfl

/--
The full-support contextwise exponential tilt is the unique global maximizer of
the averaged finite entropy-regularized objective.
-/
theorem contextExponentialTiltObjective_globalMax_unique
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (utility : Context → Response → ℝ) (inverseTemperature : ℝ)
    (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference)
    (hmax : ∀ other : FinitePolicy Context Response,
      contextExponentialTiltObjective contextLaw reference other utility inverseTemperature ≤
        contextExponentialTiltObjective contextLaw reference candidate utility inverseTemperature) :
    candidate = contextExponentialTiltPolicy reference utility inverseTemperature := by
  apply (contextExponentialTiltObjective_eq_at_exponentialTilt_iff
    contextLaw reference candidate utility inverseTemperature hcontextLaw hreference).mp
  apply le_antisymm
  · exact contextExponentialTiltObjective_le_at_exponentialTilt
      contextLaw reference candidate utility inverseTemperature hreference
  · exact hmax (contextExponentialTiltPolicy reference utility inverseTemperature)

end HumanFeedback
end Learning
end AppliedModelingLib
