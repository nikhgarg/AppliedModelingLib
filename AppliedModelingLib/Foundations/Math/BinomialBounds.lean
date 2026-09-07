import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteSum

noncomputable section

/--
Complement of a finite binomial lower tail as the corresponding upper tail.

This is a probability-free algebraic identity; distribution-specific files can
instantiate `p` with a threshold survival probability.
-/
theorem binomial_lower_tail_complement_eq_upper_tail
    {n r : ℕ} (hr : r < n) (p : ℝ) :
    1 - ∑ j ∈ Finset.Icc 0 r,
          (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)
      =
      ∑ j ∈ Finset.Icc (r + 1) n,
          (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  let term : ℕ → ℝ :=
    fun j => (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)
  have hfull :
      ∑ j ∈ Finset.range (n + 1), term j = 1 := by
    have h := (add_pow p (1 - p) n).symm
    calc
      ∑ j ∈ Finset.range (n + 1), term j
          = ∑ j ∈ Finset.range (n + 1),
              p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              dsimp [term]
              ring
      _ = (p + (1 - p)) ^ n := by
              simpa using h
      _ = 1 := by
              ring
  have hsplit :
      ∑ j ∈ Finset.range (n + 1), term j =
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j ≤ r), term j +
          ∑ j ∈ (Finset.range (n + 1)).filter (fun j => ¬ j ≤ r), term j := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (n + 1))
      (p := fun j => j ≤ r) (f := term)]
  have hlower :
      (Finset.range (n + 1)).filter (fun j => j ≤ r) =
        Finset.Icc 0 r := by
    ext j
    simp [Finset.mem_Icc]
    omega
  have hupper :
      (Finset.range (n + 1)).filter (fun j => ¬ j ≤ r) =
        Finset.Icc (r + 1) n := by
    ext j
    simp [Finset.mem_Icc]
    omega
  rw [hlower, hupper] at hsplit
  rw [hfull] at hsplit
  linarith

/--
The largest binomial coefficient in row `m` is at least the average row
coefficient.
-/
theorem two_pow_div_succ_le_choose_middle (m : ℕ) :
    ((2 : ℝ) ^ m) / (((m + 1 : ℕ) : ℝ)) ≤
      ((Nat.choose m (m / 2) : ℕ) : ℝ) := by
  have hsum_nat :
      (∑ k ∈ Finset.range (m + 1), Nat.choose m k) = 2 ^ m :=
    Nat.sum_range_choose m
  have hterm :
      ∀ k ∈ Finset.range (m + 1),
        ((Nat.choose m k : ℕ) : ℝ) ≤
          ((Nat.choose m (m / 2) : ℕ) : ℝ) := by
    intro k _hk
    exact_mod_cast Nat.choose_le_middle k m
  have hsum_le :
      (∑ k ∈ Finset.range (m + 1), ((Nat.choose m k : ℕ) : ℝ)) ≤
        ((m + 1 : ℕ) : ℝ) *
          ((Nat.choose m (m / 2) : ℕ) : ℝ) := by
    simpa [Finset.card_range, nsmul_eq_mul, mul_comm] using
      (Finset.sum_le_card_nsmul
        (s := Finset.range (m + 1))
        (f := fun k : ℕ => ((Nat.choose m k : ℕ) : ℝ))
        (((Nat.choose m (m / 2) : ℕ) : ℝ))
        hterm)
  have hsum_real :
      (∑ k ∈ Finset.range (m + 1), ((Nat.choose m k : ℕ) : ℝ)) =
        (2 : ℝ) ^ m := by
    exact_mod_cast hsum_nat
  have hpos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [hsum_real] at hsum_le
  rw [mul_comm] at hsum_le
  exact (div_le_iff₀ hpos).2 hsum_le

/--
The upper middle binomial coefficient has the same average-row lower bound.
-/
theorem two_pow_div_succ_le_choose_upper_middle (m : ℕ) :
    ((2 : ℝ) ^ m) / (((m + 1 : ℕ) : ℝ)) ≤
      ((Nat.choose m (m - m / 2) : ℕ) : ℝ) := by
  have hle : m / 2 ≤ m := Nat.div_le_self m 2
  have hsymm :
      Nat.choose m (m - m / 2) = Nat.choose m (m / 2) :=
    Nat.choose_symm hle
  simpa [hsymm] using two_pow_div_succ_le_choose_middle m

/--
For `0 < pDown ≤ pUp`, the floor/ceiling central split has at least a fixed
`sqrt (pDown / pUp)` fraction of the geometric mean sign weight.
-/
theorem sqrt_div_mul_sqrt_mul_pow_le_floor_ceil_power
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (m : ℕ) :
    Real.sqrt (pDown / pUp) * Real.sqrt (pUp * pDown) ^ m ≤
      pUp ^ (m / 2) * pDown ^ (m - m / 2) := by
  classical
  let c : ℝ := Real.sqrt (pDown / pUp)
  let s : ℝ := Real.sqrt (pUp * pDown)
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = pUp * pDown := by
    dsimp [s]
    rw [Real.sq_sqrt]
    exact mul_nonneg hUp.le hDown.le
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    rw [Real.sqrt_le_one]
    exact div_le_one_of_le₀ hle hUp.le
  have hbase0 : c * s ^ 0 ≤ pUp ^ (0 / 2) * pDown ^ (0 - 0 / 2) := by
    simp [c, hc_le_one]
  have hbase1 : c * s ^ 1 ≤ pUp ^ (1 / 2) * pDown ^ (1 - 1 / 2) := by
    have hprod :
        c * s = pDown := by
      dsimp [c, s]
      rw [← Real.sqrt_mul (show 0 ≤ pDown / pUp by positivity)
        (pUp * pDown)]
      have hinside : (pDown / pUp) * (pUp * pDown) = pDown ^ 2 := by
        field_simp [hUp.ne']
      rw [hinside, Real.sqrt_sq hDown.le]
    simpa [hprod]
  exact
    Nat.twoStepInduction
      (P := fun m : ℕ =>
        c * s ^ m ≤ pUp ^ (m / 2) * pDown ^ (m - m / 2))
      hbase0 hbase1
      (fun k hk _hk1 => by
        have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
        have hceil : k + 2 - (k / 2 + 1) = k - k / 2 + 1 := by omega
        have hmul_nonneg : 0 ≤ pUp * pDown := mul_nonneg hUp.le hDown.le
        have hstep := mul_le_mul_of_nonneg_right hk hmul_nonneg
        calc
          c * s ^ (k + 2)
              = (c * s ^ k) * (pUp * pDown) := by
                rw [show s ^ (k + 2) = s ^ k * s ^ 2 by
                  rw [pow_add, pow_two]]
                rw [hs_sq]
                ring
          _ ≤ (pUp ^ (k / 2) * pDown ^ (k - k / 2)) *
                (pUp * pDown) := hstep
          _ = pUp ^ ((k + 2) / 2) *
                pDown ^ (k + 2 - (k + 2) / 2) := by
                rw [hdiv, hceil]
                rw [pow_succ, pow_succ]
                ring)
      m

/--
Central sign-count lower bound for a biased plus/minus layer.  The central
floor/ceil count captures at least a `1/(m+1)` polynomial fraction of the
geometric sign base, up to the fixed `sqrt (pDown / pUp)` factor.
-/
theorem central_sign_weight_lower
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (m : ℕ) :
    Real.sqrt (pDown / pUp) *
        (2 * Real.sqrt (pUp * pDown)) ^ m /
          (((m + 1 : ℕ) : ℝ)) ≤
      ((Nat.choose m (m / 2) : ℕ) : ℝ) *
        (pUp ^ (m / 2) * pDown ^ (m - m / 2)) := by
  have hchoose := two_pow_div_succ_le_choose_middle m
  have hpower :=
    sqrt_div_mul_sqrt_mul_pow_le_floor_ceil_power hUp hDown hle m
  have hchoose_nonneg :
      0 ≤ ((Nat.choose m (m / 2) : ℕ) : ℝ) := by positivity
  have hleft_nonneg :
      0 ≤ ((2 : ℝ) ^ m) / (((m + 1 : ℕ) : ℝ)) := by positivity
  have hpower_left_nonneg :
      0 ≤ Real.sqrt (pDown / pUp) * Real.sqrt (pUp * pDown) ^ m := by
    positivity
  have hmul :=
    mul_le_mul hchoose hpower hpower_left_nonneg hchoose_nonneg
  calc
    Real.sqrt (pDown / pUp) *
        (2 * Real.sqrt (pUp * pDown)) ^ m /
          (((m + 1 : ℕ) : ℝ))
        =
        (((2 : ℝ) ^ m) / (((m + 1 : ℕ) : ℝ))) *
          (Real.sqrt (pDown / pUp) *
            Real.sqrt (pUp * pDown) ^ m) := by
          rw [mul_pow]
          ring
    _ ≤
        ((Nat.choose m (m / 2) : ℕ) : ℝ) *
          (pUp ^ (m / 2) * pDown ^ (m - m / 2)) := hmul

/--
One layer in the binomial expansion of `(x + y)^n` is at least the average
layer contribution.
-/
theorem exists_binomial_layer_ge_average (x y : ℝ) (n : ℕ) :
    ∃ m ∈ Finset.range (n + 1),
      (x + y) ^ n / (((n + 1 : ℕ) : ℝ)) ≤
        ((Nat.choose n m : ℕ) : ℝ) * x ^ m * y ^ (n - m) := by
  classical
  let layer : ℕ → ℝ :=
    fun m => ((Nat.choose n m : ℕ) : ℝ) * x ^ m * y ^ (n - m)
  have hnonempty : (Finset.range (n + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  have hsum_layer :
      (∑ m ∈ Finset.range (n + 1), layer m) = (x + y) ^ n := by
    rw [add_pow]
    refine Finset.sum_congr rfl ?_
    intro m _hm
    dsimp [layer]
    ring
  have hsum_const :
      (∑ _m ∈ Finset.range (n + 1),
          (x + y) ^ n / (((n + 1 : ℕ) : ℝ))) =
        (x + y) ^ n := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hne]
  have hsum_le :
      (∑ _m ∈ Finset.range (n + 1),
          (x + y) ^ n / (((n + 1 : ℕ) : ℝ))) ≤
        ∑ m ∈ Finset.range (n + 1), layer m := by
    rw [hsum_const, hsum_layer]
  rcases Finset.exists_le_of_sum_le hnonempty hsum_le with ⟨m, hm, hle⟩
  exact ⟨m, hm, by simpa [layer, mul_assoc] using hle⟩

end

end FiniteSum
end AppliedModelingLib
