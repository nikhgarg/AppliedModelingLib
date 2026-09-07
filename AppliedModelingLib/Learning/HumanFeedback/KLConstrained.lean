import AppliedModelingLib.Learning.HumanFeedback.Policy

/-!
# Finite KL-constrained policy optimization

The regularized and constrained policy formulations share a direct one-way
bridge: a maximizer of a nonnegative KL-regularized score is optimal among all
policies with no greater KL divergence from the reference policy.

## Main declarations

- `InContextAveragedKLBall`
- `IsConstrainedPolicyScoreMax`
- `policyKLRegularizedScore`
- `policyKLRegularizedScore_globalMax_constrainedScoreMax`
- `policyKLRegularizedScore_globalMax_isConstrainedScoreMax`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- A finite policy lies in the context-averaged KL ball around a reference policy. -/
def InContextAveragedKLBall
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (reference : FinitePolicy Context Response)
    (klBudget : ℝ) (policy : FinitePolicy Context Response) : Prop :=
  contextAveragedPolicyKLDivergence contextLaw policy reference ≤ klBudget

/--
A policy is a constrained finite score maximizer when it is KL-feasible and
beats every policy in the same context-averaged KL ball.
-/
def IsConstrainedPolicyScoreMax
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (reference : FinitePolicy Context Response)
    (score : Context → Response → ℝ) (klBudget : ℝ)
    (policy : FinitePolicy Context Response) : Prop :=
  InContextAveragedKLBall contextLaw reference klBudget policy ∧
    ∀ other, InContextAveragedKLBall contextLaw reference klBudget other →
      policyExpectedScore contextLaw other score ≤ policyExpectedScore contextLaw policy score

/-- The source finite RLHF objective with an explicit nonnegative KL penalty. -/
noncomputable def policyKLRegularizedScore
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (reference policy : FinitePolicy Context Response)
    (score : Context → Response → ℝ) (klWeight : ℝ) : ℝ :=
  policyExpectedScore contextLaw policy score -
    klWeight * contextAveragedPolicyKLDivergence contextLaw policy reference

/--
A globally optimal finite KL-regularized policy is score-optimal in the
constrained problem whose radius is its attained KL divergence. This is the
regularized-to-constrained direction of the source RLHF equivalence argument.
-/
theorem policyKLRegularizedScore_globalMax_constrainedScoreMax
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (reference candidate : FinitePolicy Context Response)
    (score : Context → Response → ℝ) (klWeight : ℝ) (hweight : 0 ≤ klWeight)
    (hmax : ∀ other : FinitePolicy Context Response,
      policyKLRegularizedScore contextLaw reference other score klWeight ≤
        policyKLRegularizedScore contextLaw reference candidate score klWeight) :
    ∀ other,
      InContextAveragedKLBall contextLaw reference
        (contextAveragedPolicyKLDivergence contextLaw candidate reference) other →
      policyExpectedScore contextLaw other score ≤ policyExpectedScore contextLaw candidate score := by
  intro other hfeasible
  have hregularized := hmax other
  have hpenalty :
      klWeight * contextAveragedPolicyKLDivergence contextLaw other reference ≤
        klWeight * contextAveragedPolicyKLDivergence contextLaw candidate reference :=
    mul_le_mul_of_nonneg_left hfeasible hweight
  unfold policyKLRegularizedScore at hregularized
  linarith

/--
A global finite KL-regularized score maximizer is a constrained score maximizer
at its attained KL radius.  This packages the source regularized-to-constrained
RLHF direction without introducing a separate optimizer certificate.
-/
theorem policyKLRegularizedScore_globalMax_isConstrainedScoreMax
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (reference candidate : FinitePolicy Context Response)
    (score : Context → Response → ℝ) (klWeight : ℝ) (hweight : 0 ≤ klWeight)
    (hmax : ∀ other : FinitePolicy Context Response,
      policyKLRegularizedScore contextLaw reference other score klWeight ≤
        policyKLRegularizedScore contextLaw reference candidate score klWeight) :
    IsConstrainedPolicyScoreMax contextLaw reference score
      (contextAveragedPolicyKLDivergence contextLaw candidate reference) candidate := by
  constructor
  · unfold InContextAveragedKLBall
    exact le_rfl
  · exact policyKLRegularizedScore_globalMax_constrainedScoreMax
      contextLaw reference candidate score klWeight hweight hmax

end HumanFeedback
end Learning
end AppliedModelingLib
