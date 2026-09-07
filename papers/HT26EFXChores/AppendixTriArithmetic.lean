import AppliedModelingLib.SocialChoice.FairDivision.Chores
import Mathlib.Tactic

/-!
# Arithmetic for the general tri-valued obstruction

The Appendix-A construction of He--Tao uses
`t = ceil(n / 2)`, `s = 2t + 1`, `q = s + 2`, and
`r = s(q + 1) / 2`.  The paper's first counting contradiction says that
no combination of at most `s` unit-cost chores and at most `s` `q`-cost
chores can have cost exactly `r`.  This file isolates that discrete fact;
the allocation proof can then invoke it without treating the modular step as
an informal calculation.

Source: `EFXadditivechores.tex`, Appendix A, lines 2112--2135.
-/

namespace HT26EFXChores

open scoped BigOperators

/-- The size of the larger agent group in the Appendix-A construction. -/
def appendixT (n : ℕ) : ℕ := (n + 1) / 2

/-- The common size of the two non-A chore classes. -/
def appendixS (n : ℕ) : ℕ := 2 * appendixT n + 1

/-- The middle cost in the Appendix-A construction. -/
def appendixQ (n : ℕ) : ℕ := appendixS n + 2

/-- The largest cost, represented as the integral expression used in the
paper's congruence calculation. -/
def appendixRNat (n : ℕ) : ℕ :=
  appendixT n * appendixQ n + appendixS n + 1

/-- The source formula `r = s(q + 1)/2` agrees with the integral expression
`tq + s + 1`; the latter avoids division in all allocation counting proofs. -/
theorem appendix_r_formula (n : ℕ) :
    ((appendixS n : ℝ) * ((appendixQ n : ℝ) + 1)) / 2 = appendixRNat n := by
  simp only [appendixRNat, appendixQ, appendixS]
  norm_num
  ring

/-- The source's modular obstruction, stated over natural chore counts.

Mathematically, reducing the claimed equality modulo `q = s + 2` would give
`y = s + 1` although `y ≤ s`.  Keeping the equality in natural numbers makes
the argument usable after additive-cost sums are converted to cardinals. -/
theorem appendix_no_exact_a_free_cost (n y z : ℕ)
    (hy : y ≤ appendixS n) :
    y + appendixQ n * z ≠ appendixRNat n := by
  intro hcost
  have hslt : appendixS n + 1 < appendixQ n := by
    simp only [appendixQ]
    omega
  have hsmod : appendixS n % appendixQ n = appendixS n :=
    Nat.mod_eq_of_lt (by simp only [appendixQ]; omega)
  have honemod : 1 % appendixQ n = 1 :=
    Nat.mod_eq_of_lt (by simp only [appendixQ, appendixS, appendixT]; omega)
  have hmod : y % appendixQ n = (appendixS n + 1) % appendixQ n := by
    have hmod' := congrArg (fun value : ℕ => value % appendixQ n) hcost
    simpa [appendixRNat, Nat.add_mod, Nat.mul_mod, hsmod, honemod] using hmod'
  have hylt : y < appendixQ n := by
    simp only [appendixQ]
    omega
  rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt hslt] at hmod
  omega

/-- The real-valued form needed after evaluating an additive chore cost. -/
theorem appendix_no_exact_a_free_cost_real (n y z : ℕ)
    (hy : y ≤ appendixS n) :
    (y : ℝ) + (appendixQ n : ℝ) * z ≠ appendixRNat n := by
  intro hcost
  apply appendix_no_exact_a_free_cost n y z hy
  exact_mod_cast hcost

/-- In the final Appendix-A contradiction, a no-A bundle whose first-group
cost is at least `r` must contain at least `t + 1` C-items.  The only input
besides the source parameters is that it contains at most all `s` B-items. -/
theorem appendix_p1_large_forces_C_card
    (n y z : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hy : y ≤ appendixS n)
    (hcost : r ≤ (y : ℝ) + q * z) :
    appendixT n + 1 ≤ z := by
  by_contra hnot
  have hz : z ≤ appendixT n := by omega
  have hrNat : r = appendixRNat n := by
    calc
      r = (appendixS n : ℝ) * (q + 1) / 2 := hr
      _ = (appendixS n : ℝ) * ((appendixQ n : ℝ) + 1) / 2 := by rw [hq]
      _ = appendixRNat n := appendix_r_formula n
  rw [hrNat, hq] at hcost
  have hcostNat : appendixRNat n ≤ y + appendixQ n * z := by
    exact_mod_cast hcost
  have hupper : y + appendixQ n * z ≤ appendixS n + appendixQ n * appendixT n :=
    Nat.add_le_add hy (Nat.mul_le_mul_left _ hz)
  have hstrict : appendixS n + appendixQ n * appendixT n < appendixRNat n := by
    rw [appendixRNat, Nat.mul_comm (appendixT n) (appendixQ n)]
    omega
  omega

/-- The B/C-swapped form of `appendix_p1_large_forces_C_card`, used when the
unique no-A bundle belongs to the second agent group. -/
theorem appendix_p2_large_forces_B_card
    (n y z : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hz : z ≤ appendixS n)
    (hcost : r ≤ q * (y : ℝ) + z) :
    appendixT n + 1 ≤ y := by
  by_contra hnot
  have hy : y ≤ appendixT n := by omega
  have hrNat : r = appendixRNat n := by
    calc
      r = (appendixS n : ℝ) * (q + 1) / 2 := hr
      _ = (appendixS n : ℝ) * ((appendixQ n : ℝ) + 1) / 2 := by rw [hq]
      _ = appendixRNat n := appendix_r_formula n
  rw [hrNat, hq] at hcost
  have hcostNat : appendixRNat n ≤ appendixQ n * y + z := by
    exact_mod_cast hcost
  have hupper : appendixQ n * y + z ≤ appendixQ n * appendixT n + appendixS n :=
    Nat.add_le_add (Nat.mul_le_mul_left _ hy) hz
  have hstrict : appendixQ n * appendixT n + appendixS n < appendixRNat n := by
    rw [appendixRNat, Nat.mul_comm (appendixT n) (appendixQ n)]
    omega
  omega

/-- Removing one B-item from a no-A bundle that has at least `t + 1` items of
both B and C still leaves first-group cost at least `r + t + 1`.  This is the
quantitative EFX step in the final low-group branch of Appendix A. -/
theorem appendix_p1_after_B_removal_lower
    (n y z : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hy : appendixT n + 1 ≤ y) (hz : appendixT n + 1 ≤ z) :
    r + (appendixT n + 1 : ℕ) ≤ ((y - 1 : ℕ) : ℝ) + q * z := by
  have hy' : appendixT n ≤ y - 1 := by omega
  have hmul : appendixQ n * (appendixT n + 1) ≤ appendixQ n * z :=
    Nat.mul_le_mul_left _ hz
  have hnat : appendixRNat n + appendixT n + 1 ≤
      (y - 1) + appendixQ n * z := by
    calc
      appendixRNat n + appendixT n + 1 =
          appendixT n + appendixQ n * (appendixT n + 1) := by
        simp only [appendixRNat, appendixQ, appendixS]
        ring
      _ ≤ (y - 1) + appendixQ n * z := Nat.add_le_add hy' hmul
  have hrNat : r = appendixRNat n := by
    calc
      r = (appendixS n : ℝ) * (q + 1) / 2 := hr
      _ = (appendixS n : ℝ) * ((appendixQ n : ℝ) + 1) / 2 := by rw [hq]
      _ = appendixRNat n := appendix_r_formula n
  rw [hrNat, hq]
  exact_mod_cast hnat

/-- The B/C-swapped version of `appendix_p1_after_B_removal_lower` for the
final high-group branch of Appendix A. -/
theorem appendix_p2_after_C_removal_lower
    (n y z : ℕ) (r q : ℝ)
    (hq : q = appendixQ n)
    (hr : r = (appendixS n : ℝ) * (q + 1) / 2)
    (hy : appendixT n + 1 ≤ y) (hz : appendixT n + 1 ≤ z) :
    r + (appendixT n + 1 : ℕ) ≤ q * (y : ℝ) + ((z - 1 : ℕ) : ℝ) := by
  have hz' : appendixT n ≤ z - 1 := by omega
  have hmul : appendixQ n * (appendixT n + 1) ≤ appendixQ n * y :=
    Nat.mul_le_mul_left _ hy
  have hnat : appendixRNat n + appendixT n + 1 ≤
      appendixQ n * y + (z - 1) := by
    calc
      appendixRNat n + appendixT n + 1 =
          appendixQ n * (appendixT n + 1) + appendixT n := by
        simp only [appendixRNat, appendixQ, appendixS]
        ring
      _ ≤ appendixQ n * y + (z - 1) := Nat.add_le_add hmul hz'
  have hrNat : r = appendixRNat n := by
    calc
      r = (appendixS n : ℝ) * (q + 1) / 2 := hr
      _ = (appendixS n : ℝ) * ((appendixQ n : ℝ) + 1) / 2 := by rw [hq]
      _ = appendixRNat n := appendix_r_formula n
  rw [hrNat, hq]
  exact_mod_cast hnat

end HT26EFXChores
