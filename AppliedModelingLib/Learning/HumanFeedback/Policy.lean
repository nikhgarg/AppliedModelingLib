import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.FiniteMixture
import AppliedModelingLib.Foundations.Probability.PMFKernel

/-!
# Finite context-conditioned policies

Reusable finite policy definitions for preference learning and alignment.  A
policy is a function from contexts to probability mass functions over complete
responses; finiteness and support assumptions remain local to the definitions
and theorems that need them.

## Main declarations

- `FinitePolicy`
- `finitePolicy_ext`
- `deterministicPolicy`
- `binaryMixturePolicy`
- `timeAveragedPolicy`
- `PolicyFullSupport`
- `policyExpectedScore`
- `pointwisePolicyKLDivergence`
- `contextAveragedPolicyKLDivergence`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- A policy assigns a probability distribution over responses to each context. -/
abbrev FinitePolicy (Context Response : Type*) := PMFKernel Context Response

/-- Policies are equal when their response PMFs agree at every context. -/
theorem finitePolicy_ext {Context Response : Type*}
    {first second : FinitePolicy Context Response}
    (h : ∀ context, first context = second context) : first = second :=
  PMFKernel.ext h

/-- Embed a deterministic response rule as a context-conditioned policy. -/
noncomputable def deterministicPolicy {Context Response : Type*}
    (response : Context → Response) : FinitePolicy Context Response :=
  PMFKernel.pure response

/-- A contextwise Bernoulli mixture of two finite policies. -/
noncomputable def binaryMixturePolicy {Context Response : Type*}
    (p : NNReal) (hp : p ≤ 1)
    (selected unselected : FinitePolicy Context Response) : FinitePolicy Context Response :=
  fun context => binaryMixturePMF p hp (selected context) (unselected context)

/--
The uniform empirical average of a finite, nonempty policy trajectory.

At every context, this first samples a time index uniformly and then samples
from that round's response policy.  Keeping the time type abstract makes the
definition usable for either `Fin T` trajectories or arbitrary finite logged
collections of rounds.
-/
noncomputable def timeAveragedPolicy {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    (trajectory : Time → FinitePolicy Context Response) : FinitePolicy Context Response :=
  fun context => (uniformPMF Time).bind fun time => trajectory time context

/-- A policy has full support when every context-indexed response law does. -/
def PolicyFullSupport {Context Response : Type*}
    (policy : FinitePolicy Context Response) : Prop :=
  ∀ context, PMFFullSupport (policy context)

/-- The expected score of a policy under a finite context distribution. -/
noncomputable def policyExpectedScore
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (policy : FinitePolicy Context Response)
    (score : Context → Response → ℝ) : ℝ :=
  pmfExp contextLaw fun context => pmfExp (policy context) (score context)

/-- The score of a deterministic policy is the context expectation of its realized score. -/
theorem policyExpectedScore_deterministic
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (response : Context → Response)
    (score : Context → Response → ℝ) :
    policyExpectedScore contextLaw (deterministicPolicy response) score =
      pmfExp contextLaw (fun context => score context (response context)) := by
  unfold policyExpectedScore deterministicPolicy
  refine pmfExp_congr contextLaw fun context => ?_
  exact pmfExp_pure (response context) (score context)

/-- Pointwise finite KL divergence between two policies at a fixed context. -/
noncomputable def pointwisePolicyKLDivergence
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response) (context : Context) : ℝ :=
  finiteKLDivergence (first context) (second context)

/-- Finite KL divergence between policies, averaged over a context distribution. -/
noncomputable def contextAveragedPolicyKLDivergence
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (first second : FinitePolicy Context Response) : ℝ :=
  pmfExp contextLaw (pointwisePolicyKLDivergence first second)

/-- A context-averaged policy KL divergence is nonnegative under full support of the reference. -/
theorem contextAveragedPolicyKLDivergence_nonneg
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (first second : FinitePolicy Context Response)
    (hsecond : PolicyFullSupport second) :
    0 ≤ contextAveragedPolicyKLDivergence contextLaw first second := by
  unfold contextAveragedPolicyKLDivergence
  exact pmfExp_nonneg_of_forall_nonneg contextLaw _ fun context =>
    finiteKLDivergence_nonneg (first context) (second context) (hsecond context)

end HumanFeedback
end Learning
end AppliedModelingLib
