import AppliedModelingLib.Foundations.Probability.FiniteKL

/-!
# Appendix entropy identity

Source: Seshadri--Ugander (2020), Appendix, Fact 5 (`max_entropy`).

The printed fact ranges over the closed finite simplex and uses the standard
information-theoretic convention that assigning zero reference mass to a
positive-probability event has infinite cross entropy.  The reusable
`finiteCrossEntropyExtended` definition records that boundary convention
explicitly, avoiding Lean's unrelated finite-real convention `Real.log 0 = 0`.
-/

namespace SeshadriUgander2020IIATesting

/-- Appendix Fact 5 (`max_entropy`): for every finite distribution, entropy
is the infimum of cross entropy over the closed simplex of reference
distributions.  The extended-real codomain makes the paper's zero-mass
boundary convention explicit. -/
theorem appendixFact5_maxEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (q : PMF α) :
    sInf (AppliedModelingLib.finiteCrossEntropyExtendedRange q) = AppliedModelingLib.finiteEntropy q :=
  AppliedModelingLib.sInf_finiteCrossEntropyExtendedRange_eq_entropy q

end SeshadriUgander2020IIATesting
