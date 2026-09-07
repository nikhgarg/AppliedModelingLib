import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.Convex.Function

/-!
# Convex finite-PMF expectations

Reusable closure of convex objectives under finite probability-mass-function
expectation.  This is used whenever a loss is convex pointwise in a decision
parameter and the population objective freezes a finite data law.
-/

namespace AppliedModelingLib

/-- A finite-PMF expectation of convex pointwise objectives is convex. -/
theorem convexOn_pmfExp
    {Data Parameter : Type*} [Fintype Data] [DecidableEq Data]
    [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (law : PMF Data) (domain : Set Parameter) (hdomain : Convex ℝ domain)
    (objective : Data → Parameter → ℝ)
    (hconvex : ∀ datum, ConvexOn ℝ domain (objective datum)) :
    ConvexOn ℝ domain (fun parameter => pmfExp law (fun datum => objective datum parameter)) := by
  refine ⟨hdomain, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  calc
    pmfExp law (fun datum => objective datum (a • first + b • second)) ≤
        pmfExp law (fun datum => a * objective datum first + b * objective datum second) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro datum
          simpa only [smul_eq_mul] using
            (hconvex datum).2 hfirst hsecond ha hb hab
    _ = a * pmfExp law (fun datum => objective datum first) +
          b * pmfExp law (fun datum => objective datum second) := by
          rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]

end AppliedModelingLib
