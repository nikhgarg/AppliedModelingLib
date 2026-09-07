import Mathlib.Data.Real.Basic
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace AppliedModelingLib
namespace Decision

/--
A decision rule follows Thompson Sampling if, given a joint distribution
over quality profiles, it selects an option `v` by first drawing a profile
from the belief and then selecting an argmax of that profile.
-/
def IsThompsonSampling {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (belief : PMF (V → ℝ)) (policy : PMF V) : Prop :=
  ∃ tie_breaker : (V → ℝ) → V,
    (∀ (profile : V → ℝ) (v : V), profile v ≤ profile (tie_breaker profile)) ∧
    policy = belief.bind (fun profile => PMF.pure (tie_breaker profile))

end Decision
end AppliedModelingLib
