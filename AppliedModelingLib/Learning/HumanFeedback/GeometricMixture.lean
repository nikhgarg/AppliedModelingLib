import AppliedModelingLib.Foundations.Probability.GeometricMixture
import AppliedModelingLib.Learning.HumanFeedback.Policy

/-!
# Geometric mixtures of finite policies

This is the context-indexed lift of the finite PMF geometric mixture.  In
particular, `geometricMixturePolicy first reference (η * τ)` is the
regularized opponent in the Nash-MD update of NLHF.

## Main declarations

- `geometricMixturePolicy`
- `geometricMixturePolicy_fullSupport`
- `geometricMixturePolicy_zero`
- `geometricMixturePolicy_one`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- Mix two full-support policies independently at each context. -/
noncomputable def geometricMixturePolicy
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response) (mixWeight : ℝ)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second) :
    FinitePolicy Context Response :=
  fun context => geometricMixture (first context) (second context) mixWeight
    (hfirst context) (hsecond context)

/-- A geometric mixture of full-support policies has full support. -/
theorem geometricMixturePolicy_fullSupport
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response) (mixWeight : ℝ)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second) :
    PolicyFullSupport (geometricMixturePolicy first second mixWeight hfirst hsecond) := by
  intro context
  exact geometricMixture_fullSupport (first context) (second context) mixWeight
    (hfirst context) (hsecond context)

/-- At zero mixture weight, a geometric policy mixture is its first policy. -/
theorem geometricMixturePolicy_zero
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second) :
    geometricMixturePolicy first second 0 hfirst hsecond = first := by
  apply finitePolicy_ext
  intro context
  exact geometricMixture_zero (first context) (second context)
    (hfirst context) (hsecond context)

/-- At unit mixture weight, a geometric policy mixture is its second policy. -/
theorem geometricMixturePolicy_one
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second) :
    geometricMixturePolicy first second 1 hfirst hsecond = second := by
  apply finitePolicy_ext
  intro context
  exact geometricMixture_one (first context) (second context)
    (hfirst context) (hsecond context)

/-- Log response mass of a policy geometric mixture, context by context. -/
theorem geometricMixturePolicy_log_mass
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : FinitePolicy Context Response) (mixWeight : ℝ)
    (hfirst : PolicyFullSupport first) (hsecond : PolicyFullSupport second)
    (context : Context) (response : Response) :
    Real.log (geometricMixturePolicy first second mixWeight hfirst hsecond context response).toReal =
      (1 - mixWeight) * Real.log (first context response).toReal +
        mixWeight * Real.log (second context response).toReal -
          Real.log (geometricMixturePartition (first context) (second context) mixWeight) :=
  geometricMixture_log_mass (first context) (second context) mixWeight
    (hfirst context) (hsecond context) response

end HumanFeedback
end Learning
end AppliedModelingLib
