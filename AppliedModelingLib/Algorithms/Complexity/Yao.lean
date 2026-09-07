import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite Yao-Style Lower-Bound Lemmas

This module contains the finite expectation algebra behind Yao-style lower
bounds. It deliberately avoids modeling computational complexity: the theorem
is about finite sets of deterministic algorithms and finite input
distributions.
-/

namespace AppliedModelingLib
namespace Decision

open AppliedModelingLib

/--
Finite Yao averaging lemma. If a distribution over inputs gives every
deterministic algorithm expected normalized payoff at most `bound`, then every
randomized algorithm has some input on which its expected normalized payoff is
at most `bound`.
-/
theorem exists_input_randomized_payoff_le_of_forall_deterministic_average_le
    {Algorithm Input : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    [Fintype Input] [DecidableEq Input] [Nonempty Input]
    (distribution : PMF Input)
    (randomizedAlgorithm : PMF Algorithm)
    (payoff : Algorithm → Input → ℝ)
    (bound : ℝ)
    (hdet :
      ∀ algorithm,
        pmfExp distribution (fun input => payoff algorithm input) ≤ bound) :
    ∃ input,
      pmfExp randomizedAlgorithm (fun algorithm => payoff algorithm input) ≤
        bound := by
  classical
  by_contra hnone
  push Not at hnone
  let inputPayoff : Input → ℝ :=
    fun input => pmfExp randomizedAlgorithm
      (fun algorithm => payoff algorithm input)
  have hstrict :
      bound < pmfExp distribution inputPayoff :=
    pmfExp_lt_of_forall_lt distribution inputPayoff bound hnone
  have hswap :
      pmfExp distribution inputPayoff =
        pmfExp randomizedAlgorithm
          (fun algorithm =>
            pmfExp distribution (fun input => payoff algorithm input)) := by
    simpa [inputPayoff, pmfPairExp] using
      (pmfPairExp_swap distribution randomizedAlgorithm
        (fun input algorithm => payoff algorithm input))
  have hle :
      pmfExp distribution inputPayoff ≤ bound := by
    rw [hswap]
    exact pmfExp_le_of_forall_le randomizedAlgorithm
      (fun algorithm =>
        pmfExp distribution (fun input => payoff algorithm input))
      bound hdet
  exact not_lt_of_ge hle hstrict

/--
Equivalent no-strict-improvement form of the finite Yao lemma.
-/
theorem not_forall_input_bound_lt_randomized_payoff_of_forall_deterministic_average_le
    {Algorithm Input : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    [Fintype Input] [DecidableEq Input] [Nonempty Input]
    (distribution : PMF Input)
    (randomizedAlgorithm : PMF Algorithm)
    (payoff : Algorithm → Input → ℝ)
    (bound : ℝ)
    (hdet :
      ∀ algorithm,
        pmfExp distribution (fun input => payoff algorithm input) ≤ bound) :
    ¬ ∀ input,
      bound <
        pmfExp randomizedAlgorithm
          (fun algorithm => payoff algorithm input) := by
  intro hbetter
  rcases exists_input_randomized_payoff_le_of_forall_deterministic_average_le
      distribution randomizedAlgorithm payoff bound hdet with ⟨input, hle⟩
  exact not_lt_of_ge hle (hbetter input)

/--
A finite Yao certificate for randomized lower bounds.

The certificate says a hard input distribution gives every deterministic
algorithm average payoff at most `bound`.
-/
structure RandomizedUpperPayoffCertificate
    (Algorithm Input : Type*) [Fintype Input] [DecidableEq Input]
    (bound : ℝ) where
  distribution : PMF Input
  payoff : Algorithm → Input → ℝ
  deterministic_average_le :
    ∀ algorithm,
      pmfExp distribution (fun input => payoff algorithm input) ≤ bound

namespace RandomizedUpperPayoffCertificate

variable {Algorithm Input : Type*} {bound : ℝ}
variable [Fintype Algorithm] [DecidableEq Algorithm]
variable [Fintype Input] [DecidableEq Input] [Nonempty Input]

/--
Every randomized algorithm has an input where its expected payoff is at most
the certificate bound.
-/
theorem exists_input_randomized_payoff_le
    (C : RandomizedUpperPayoffCertificate Algorithm Input bound)
    (randomizedAlgorithm : PMF Algorithm) :
    ∃ input,
      pmfExp randomizedAlgorithm (fun algorithm => C.payoff algorithm input) ≤
        bound := by
  exact
    exists_input_randomized_payoff_le_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.payoff bound
      C.deterministic_average_le

/--
No randomized algorithm can have payoff strictly above the certificate bound on
every input.
-/
theorem not_forall_input_bound_lt_randomized_payoff
    (C : RandomizedUpperPayoffCertificate Algorithm Input bound)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      bound <
        pmfExp randomizedAlgorithm (fun algorithm => C.payoff algorithm input) := by
  exact
    not_forall_input_bound_lt_randomized_payoff_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.payoff bound
      C.deterministic_average_le

end RandomizedUpperPayoffCertificate

end Decision
end AppliedModelingLib
