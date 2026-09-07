import AppliedModelingLib.Foundations.Math.ExponentialBounds
import Mathlib.Tactic

namespace AppliedModelingLib
namespace Probability
namespace Bernoulli

/-!
# Bernoulli Success-Value Helpers

Reusable scalar identities for the value of drawing at least one success from
`q` independent Bernoulli trials with success probability `p`.
-/

/--
Expected satisfaction from `q` independent Bernoulli trials when the consumer
only needs one success: `1 - (1 - p)^q`.
-/
noncomputable def atLeastOneValue (p : ℝ) (q : ℕ) : ℝ :=
  1 - (1 - p) ^ q

@[simp] theorem atLeastOneValue_zero (p : ℝ) :
    atLeastOneValue p 0 = 0 := by
  simp [atLeastOneValue]

@[simp] theorem atLeastOneValue_one (p : ℝ) :
    atLeastOneValue p 1 = p := by
  simp [atLeastOneValue]

/-- Closed form for the one-step Bernoulli satisfaction marginal. -/
theorem atLeastOneValue_succ_sub (p : ℝ) (q : ℕ) :
    atLeastOneValue p (q + 1) - atLeastOneValue p q =
      p * (1 - p) ^ q := by
  calc
    atLeastOneValue p (q + 1) - atLeastOneValue p q
        = (1 - p) ^ q - (1 - p) ^ (q + 1) := by
          simp [atLeastOneValue]
    _ = (1 - p) ^ q - (1 - p) ^ q * (1 - p) := by
          rw [pow_succ]
    _ = p * (1 - p) ^ q := by
          ring

/-- Closed form for the value lost by removing the last Bernoulli trial. -/
theorem atLeastOneValue_sub_pred {p : ℝ} {q : ℕ} (hq : 0 < q) :
    atLeastOneValue p q - atLeastOneValue p (q - 1) =
      p * (1 - p) ^ (q - 1) := by
  have hsucc : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hsucc]
  exact atLeastOneValue_succ_sub p (q - 1)

/-- Bernoulli satisfaction has nonnegative marginal values for `0 ≤ p ≤ 1`. -/
theorem atLeastOneValue_succ_sub_nonneg {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    0 ≤ atLeastOneValue p (q + 1) - atLeastOneValue p q := by
  rw [atLeastOneValue_succ_sub]
  exact mul_nonneg hp0 (pow_nonneg (by linarith) q)

/-- Bernoulli satisfaction has diminishing one-step marginal values for `0 ≤ p ≤ 1`. -/
theorem atLeastOneValue_diminishing_marginal {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    atLeastOneValue p (q + 2) - atLeastOneValue p (q + 1) ≤
      atLeastOneValue p (q + 1) - atLeastOneValue p q := by
  have hr0 : 0 ≤ 1 - p := by linarith
  have hr1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (q + 1) ≤ (1 - p) ^ q := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 q) hr1
  calc
    atLeastOneValue p (q + 2) - atLeastOneValue p (q + 1)
        = p * (1 - p) ^ (q + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            atLeastOneValue_succ_sub p (q + 1)
    _ ≤ p * (1 - p) ^ q := mul_le_mul_of_nonneg_left hpow hp0
    _ = atLeastOneValue p (q + 1) - atLeastOneValue p q := by
          rw [atLeastOneValue_succ_sub]

/--
The probability of no success in `q` Bernoulli trials is at most the
exponential approximation `exp (-q p)`.
-/
theorem one_sub_pow_le_exp_neg_mul {p : ℝ} (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ q ≤ Real.exp (-((q : ℝ) * p)) := by
  by_cases hp_one : p = 1
  · subst p
    by_cases hq : q = 0
    · simp [hq]
    · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
      simpa [hq_pos.ne'] using (Real.exp_pos (-(q : ℝ))).le
  have hp_lt : p < 1 := lt_of_le_of_ne hp1 hp_one
  have hbase_nonneg : 0 ≤ 1 - p := by linarith
  have hbase_pos : 0 < 1 - p := by linarith
  have hlog_le : Real.log (1 - p) ≤ -p := by
    have h := AppliedModelingLib.Math.le_neg_log_one_sub hp0 hp_lt
    linarith
  have hbase_le_exp : 1 - p ≤ Real.exp (-p) :=
    (Real.log_le_iff_le_exp hbase_pos).mp hlog_le
  have hpow :
      (1 - p) ^ q ≤ (Real.exp (-p)) ^ q :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_exp q
  have hexp_pow : (Real.exp (-p)) ^ q = Real.exp (-((q : ℝ) * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa [hexp_pow] using hpow

/--
The at-least-one-success value dominates the exponential lower bound
`1 - exp (-q p)`.
-/
theorem one_sub_exp_neg_mul_le_atLeastOneValue {p : ℝ} (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - Real.exp (-((q : ℝ) * p)) ≤ atLeastOneValue p q := by
  dsimp [atLeastOneValue]
  have hpow := one_sub_pow_le_exp_neg_mul q hp0 hp1
  linarith

/--
Strict corollary of the exponential Bernoulli lower bound.
-/
theorem lt_atLeastOneValue_of_lt_one_sub_exp_neg_mul {p target : ℝ} {q : ℕ}
    (htarget : target < 1 - Real.exp (-((q : ℝ) * p)))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    target < atLeastOneValue p q :=
  lt_of_lt_of_le htarget
    (one_sub_exp_neg_mul_le_atLeastOneValue q hp0 hp1)

end Bernoulli
end Probability
end AppliedModelingLib
