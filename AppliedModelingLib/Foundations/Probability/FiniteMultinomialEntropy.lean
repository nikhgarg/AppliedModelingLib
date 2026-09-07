import AppliedModelingLib.Foundations.Probability.FiniteTypeLogMass
import Mathlib.Analysis.SpecialFunctions.Stirling

open scoped BigOperators

namespace AppliedModelingLib
namespace Probability

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
# Finite multinomial entropy bounds

This file collects polynomial-loss entropy estimates for multinomial type
probabilities.  The estimates are intended for finite-alphabet Cramer lower
bounds, where only subexponential losses may be discarded.
-/

/--
Upper Stirling bound with a fixed constant.  For `n > 0`,
`log n!` is at most the Stirling main term plus one.
-/
theorem log_factorial_le_stirling_main_add_one {n : ℕ} (hn : n ≠ 0) :
    Real.log (Nat.factorial n : ℝ) ≤
      1 + (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) +
        (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
  have hseq_pos : 0 < Stirling.stirlingSeq n := by
    simpa [hpred] using (Stirling.stirlingSeq'_pos (n - 1))
  have hseq_one_pos : 0 < Stirling.stirlingSeq 1 := by
    simpa using (Stirling.stirlingSeq'_pos 0)
  have hseq_le : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, hpred] using hanti
  have hlog_seq_le :
      Real.log (Stirling.stirlingSeq n) ≤
        Real.log (Stirling.stirlingSeq 1) :=
    Real.log_le_log hseq_pos hseq_le
  have hsqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]
    norm_num
  have hlog_sqrt_two_nonneg : 0 ≤ Real.log (Real.sqrt 2) :=
    Real.log_nonneg hsqrt_two_ge_one
  have hlog_seq_one_le_one :
      Real.log (Stirling.stirlingSeq 1) ≤ 1 := by
    rw [Stirling.stirlingSeq_one,
      Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hsqrt_two_pos),
      Real.log_exp]
    linarith
  have hformula := Stirling.log_stirlingSeq_formula n
  have hmain :
      Real.log (Nat.factorial n : ℝ) -
          (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) -
          (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) ≤ 1 := by
    calc
      Real.log (Nat.factorial n : ℝ) -
          (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) -
          (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1)
          = Real.log (Stirling.stirlingSeq n) := by
              rw [hformula]
      _ ≤ Real.log (Stirling.stirlingSeq 1) := hlog_seq_le
      _ ≤ 1 := hlog_seq_one_le_one
  linarith

/--
If `n <= Q` and `Q > 0`, the logarithm of `n!` is bounded above by the
Stirling main term for `n` plus a common polynomial-loss term depending on `Q`.
-/
theorem log_factorial_le_common_horizon
    {n Q : ℕ} (hQpos : 0 < Q) (hnQ : n ≤ Q) :
    Real.log (Nat.factorial n : ℝ) ≤
      1 + (1 / 2 : ℝ) * Real.log (2 * (Q : ℝ)) +
        (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
  by_cases hn : n = 0
  · subst n
    have hQ_one : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
    have hlog_nonneg : 0 ≤ Real.log (2 * (Q : ℝ)) := by
      apply Real.log_nonneg
      nlinarith
    simp
    linarith
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos_real : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hQpos_real : 0 < (Q : ℝ) := by exact_mod_cast hQpos
    have hnQ_real : (n : ℝ) ≤ Q := by exact_mod_cast hnQ
    have hlog_le :
        Real.log (2 * (n : ℝ)) ≤ Real.log (2 * (Q : ℝ)) := by
      refine Real.log_le_log ?_ ?_
      · nlinarith
      · nlinarith
    have hbase := log_factorial_le_stirling_main_add_one (n := n) hn
    linarith

/-- Logarithm of a multinomial coefficient as numerator factorial minus
denominator factorials. -/
theorem log_multinomial_eq_log_factorial_sub_sum_log_factorial
    (q : α → ℕ) :
    Real.log (Nat.multinomial (Finset.univ : Finset α) q : ℝ) =
      Real.log (Nat.factorial (∑ a : α, q a) : ℝ) -
        ∑ a : α, Real.log (Nat.factorial (q a) : ℝ) := by
  classical
  have hspec :
      (∏ a : α, (Nat.factorial (q a) : ℝ)) *
          (Nat.multinomial (Finset.univ : Finset α) q : ℝ) =
        (Nat.factorial (∑ a : α, q a) : ℝ) := by
    have hnat := Nat.multinomial_spec (Finset.univ : Finset α) q
    exact_mod_cast (by simpa using hnat)
  have hden_pos :
      0 < ∏ a : α, (Nat.factorial (q a) : ℝ) :=
    Finset.prod_pos (fun a _ => by positivity)
  have hmulti_pos :
      0 < (Nat.multinomial (Finset.univ : Finset α) q : ℝ) := by
    exact_mod_cast Nat.multinomial_pos (Finset.univ : Finset α) q
  have hlog_den :
      Real.log (∏ a : α, (Nat.factorial (q a) : ℝ)) =
        ∑ a : α, Real.log (Nat.factorial (q a) : ℝ) := by
    simpa using
      (Real.log_prod (s := (Finset.univ : Finset α))
        (f := fun a : α => (Nat.factorial (q a) : ℝ))
        (by
          intro a _
          positivity))
  have hlog_product :
      Real.log (∏ a : α, (Nat.factorial (q a) : ℝ)) +
          Real.log (Nat.multinomial (Finset.univ : Finset α) q : ℝ) =
        Real.log (Nat.factorial (∑ a : α, q a) : ℝ) := by
    rw [← Real.log_mul (ne_of_gt hden_pos) (ne_of_gt hmulti_pos), hspec]
  linarith

end

end Probability
end AppliedModelingLib
