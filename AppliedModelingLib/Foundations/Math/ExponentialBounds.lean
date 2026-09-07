import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Elementary Exponential Bounds

Reusable real exponential inequalities for finite probability estimates.

## Main declarations

- `exp_neg_two_div_le_one_sub_inv_of_two_le`: for `x >= 2`,
  `exp(-(2/x)) <= 1 - 1/x`.
- `exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le`: the corresponding
  finite-power lower bound.
- `log_add_div_self_le_div`: the shifted logarithm bound
  `log ((x + δ) / x) <= δ / x`.
- `le_neg_log_one_sub`: the standard bound `x <= -log (1 - x)` on
  `[0, 1)`.
- `neg_log_one_sub_le_div_self`: the standard upper bound
  `-log (1 - x) <= x / (1 - x)` on `[0, 1)`.
- `neg_log_one_add_sqrt_div_two_ge_one_fifth_neg_log`: a one-variable
  endpoint-refinement logarithmic bound used in rate-doubling arguments.
- `half_mul_le_one_sub_exp_neg_of_mem_Icc`: a linear lower bound for
  `1 - exp (-x)` on `[0, 1]`.
- `mul_exp_neg_lt_one_of_log_lt`: if a finite union count has logarithm below
  a tail rate, then `count * exp (-rate) < 1`.
- `mul_delta_split_budget_eq_of_delta_eq_div_mul_add`: algebra for choosing
  a grid width from a two-term error budget.
- `tsum_exp_neg_mul_two_pow_le_four_mul_exp_neg`: a dyadic exponential-tail
  sum bound used when unioning small dyadic-shell deviations.
-/

namespace AppliedModelingLib
namespace Math

/-- A nonnegative additive one-step factor is bounded by the exponential of
its accumulated linear scale.  This is the finite-horizon exponential
envelope used after a discrete Grönwall recurrence.

Library provenance: the proof composes Mathlib's
`Real.prod_one_add_le_exp_sum` from the repository-pinned Apache-2.0
`Mathlib/Analysis/Complex/Exponential.lean`; no external proof text is copied
or ported. -/
theorem one_add_div_pow_le_exp_mul
    (steps : ℕ) {ratio scale : ℝ}
    (hratio : 0 ≤ ratio) (hscale : 0 < scale) :
    (1 + ratio / scale) ^ steps ≤
      Real.exp ((steps : ℝ) * (ratio / scale)) := by
  have hproduct := Real.prod_one_add_le_exp_sum (Finset.range steps)
    (f := fun _ : ℕ => ratio / scale) (fun _ => div_nonneg hratio hscale.le)
  calc
    (1 + ratio / scale) ^ steps =
        ∏ _ ∈ Finset.range steps, (1 + ratio / scale) := by
          rw [Finset.prod_const, Finset.card_range]
    _ ≤ Real.exp (∑ _ ∈ Finset.range steps, ratio / scale) := hproduct
    _ = Real.exp ((steps : ℝ) * (ratio / scale)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/--
The reciprocal-polynomial envelope for a negative exponential tail.  This is
the elementary bridge from an exponential moment to any fixed finite moment
or polynomial dyadic-tail estimate.

Library provenance: this directly reuses Mathlib's
`Real.pow_div_factorial_le_exp` and `Real.exp_neg` from
[`Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Exponential.html)),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem exp_neg_le_factorial_div_pow
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
  have hfactorial_pos : 0 < (n.factorial : ℝ) := by positivity
  have hpow_pos : 0 < x ^ n := pow_pos hx _
  have hterm_pos : 0 < x ^ n / (n.factorial : ℝ) :=
    div_pos hpow_pos hfactorial_pos
  have hfactorial_exp : x ^ n / (n.factorial : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hx.le n
  calc
    Real.exp (-x) = 1 / Real.exp x := by rw [one_div, Real.exp_neg]
    _ ≤ 1 / (x ^ n / (n.factorial : ℝ)) :=
      one_div_le_one_div_of_le hterm_pos hfactorial_exp
    _ = (n.factorial : ℝ) / x ^ n := by
      field_simp [hfactorial_pos.ne', hpow_pos.ne']

/--
The dyadic exponential terms are controlled by a geometric sequence whenever
`y ≥ 1`.

Library provenance: this directly reuses Lean core's `Nat.lt_two_pow_self`
from
[`Init/Data/Nat/Lemmas.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Init/Data/Nat/Lemmas.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Lemmas)),
and Mathlib's `Real.exp_neg_one_lt_half`, `summable_geometric_two`, and
`tsum_geometric_two`, from
[`Analysis/Complex/ExponentialBounds.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/ExponentialBounds.lean),
and
[`Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Basic)).
Lean core at the recorded Lean 4 commit and Mathlib at the pinned Mathlib
commit are Apache-2.0; no external Lean source is copied or ported.
-/
theorem exp_neg_mul_two_pow_le_exp_neg_mul_invTwo_pow
    {y : ℝ} (hy : 1 ≤ y) (n : ℕ) :
    Real.exp (-y * (2 : ℝ) ^ n) ≤ Real.exp (-y) * (1 / 2 : ℝ) ^ n := by
  have hpow_nat : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hpow : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hpow_nat
  have hlinear : y + (n : ℝ) ≤ y * ((n : ℝ) + 1) := by nlinarith
  have htarget : y + (n : ℝ) ≤ y * (2 : ℝ) ^ n :=
    hlinear.trans (mul_le_mul_of_nonneg_left hpow (by linarith))
  have harg : -y * (2 : ℝ) ^ n ≤ -y - (n : ℝ) := by linarith
  calc
    Real.exp (-y * (2 : ℝ) ^ n) ≤ Real.exp (-y - (n : ℝ)) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (-y) * Real.exp (-(n : ℝ)) := by
      rw [show -y - (n : ℝ) = (-y) + (-(n : ℝ)) by ring, Real.exp_add]
    _ = Real.exp (-y) * Real.exp (-1) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-y) * (1 / 2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le n)
        (Real.exp_pos _).le

/-- The source's small-shell dyadic exponential envelope is summable. -/
theorem summable_two_mul_exp_neg_mul_two_pow {y : ℝ} (hy : 1 ≤ y) :
    Summable (fun n : ℕ => 2 * Real.exp (-y * (2 : ℝ) ^ n)) := by
  have hright : Summable (fun n : ℕ =>
      (2 * Real.exp (-y)) * (1 / 2 : ℝ) ^ n) :=
    summable_geometric_two.mul_left _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hright
  intro n
  calc
    2 * Real.exp (-y * (2 : ℝ) ^ n) ≤
        2 * (Real.exp (-y) * (1 / 2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left
        (exp_neg_mul_two_pow_le_exp_neg_mul_invTwo_pow hy n) (by norm_num)
    _ = (2 * Real.exp (-y)) * (1 / 2 : ℝ) ^ n := by ring

/--
The dyadic exponential sequence is summable with an explicit first-term tail
bound: for `y ≥ 1`, its total mass is at most four times `exp (-y)`.
-/
theorem tsum_exp_neg_mul_two_pow_le_four_mul_exp_neg
    {y : ℝ} (hy : 1 ≤ y) :
    ∑' n : ℕ, 2 * Real.exp (-y * (2 : ℝ) ^ n) ≤ 4 * Real.exp (-y) := by
  have hright : Summable (fun n : ℕ =>
      (2 * Real.exp (-y)) * (1 / 2 : ℝ) ^ n) :=
    summable_geometric_two.mul_left _
  have hleft := summable_two_mul_exp_neg_mul_two_pow hy
  calc
    ∑' n : ℕ, 2 * Real.exp (-y * (2 : ℝ) ^ n) ≤
        ∑' n : ℕ, (2 * Real.exp (-y)) * (1 / 2 : ℝ) ^ n :=
      Summable.tsum_le_tsum (fun n => by
        calc
          2 * Real.exp (-y * (2 : ℝ) ^ n) ≤
              2 * (Real.exp (-y) * (1 / 2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left
              (exp_neg_mul_two_pow_le_exp_neg_mul_invTwo_pow hy n) (by norm_num)
          _ = (2 * Real.exp (-y)) * (1 / 2 : ℝ) ^ n := by ring) hleft hright
    _ = 4 * Real.exp (-y) := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring

/--
Bernoulli's inequality makes an exponential tail at any geometric base `r>1`
dominated by an ordinary geometric series.  This is the reusable numerical
form needed for the large-shell Fournier--Guillin allocation, whose exponent
base need not be dyadic.

Library provenance: this directly reuses Mathlib's `one_add_mul_sub_le_pow`
from
[`Algebra/Order/Ring/Pow.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Ring/Pow.lean)
and `summable_geometric_of_norm_lt_one` / `tsum_geometric_of_norm_lt_one`
from
[`Analysis/SpecificLimits/Normed.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Normed.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Normed.html)),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem exp_neg_mul_pow_le_exp_neg_mul_geometric
    {y r : ℝ} (hy : 0 ≤ y) (hr : 1 < r) (n : ℕ) :
    Real.exp (-y * r ^ n) ≤
      Real.exp (-y) * Real.exp (-(y * (r - 1))) ^ n := by
  have hbernoulli : 1 + (n : ℝ) * (r - 1) ≤ r ^ n := by
    exact one_add_mul_sub_le_pow (by linarith) n
  have hscaled := mul_le_mul_of_nonneg_left hbernoulli hy
  have harg : -y * r ^ n ≤ -y - y * (n : ℝ) * (r - 1) := by
    nlinarith
  calc
    Real.exp (-y * r ^ n) ≤ Real.exp (-y - y * (n : ℝ) * (r - 1)) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (-y) * Real.exp (-(y * (r - 1))) ^ n := by
      rw [show -y - y * (n : ℝ) * (r - 1) =
        (-y) + (-(y * (r - 1)) * (n : ℝ)) by ring, Real.exp_add,
        ← Real.exp_nat_mul]
      congr 1
      ring

/--
Exponential tails with every strictly growing geometric base are summable.
The proof keeps the base-dependent geometric ratio explicit so downstream
probability unions can establish finiteness before passing to real measures.
-/
theorem summable_exp_neg_mul_pow
    {y r : ℝ} (hy : 0 < y) (hr : 1 < r) :
    Summable (fun n : ℕ => Real.exp (-y * r ^ n)) := by
  let q : ℝ := Real.exp (-(y * (r - 1)))
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (mul_pos hy (sub_pos.mpr hr))
  have hright : Summable (fun n : ℕ => Real.exp (-y) * q ^ n) := by
    have hgeom : Summable (fun n : ℕ => q ^ n) := by
      apply summable_geometric_of_norm_lt_one
      simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt_one
    exact hgeom.mul_left _
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _ hright
  intro n
  calc
    Real.exp (-y * r ^ n) ≤
        Real.exp (-y) * Real.exp (-(y * (r - 1))) ^ n :=
      exp_neg_mul_pow_le_exp_neg_mul_geometric hy.le hr n
    _ = Real.exp (-y) * q ^ n := by rfl

/--
The natural ceiling of a logarithm base `base > 1` is a concrete power
cutoff: its natural power already reaches every positive threshold.  This is
the arithmetic interface used to turn source cutoffs of logarithmic size into
Lean shell indices.

Library provenance: this directly reuses Mathlib's `Real.rpow_logb` from
[`Analysis/SpecialFunctions/Log/Base.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Base.lean),
and `Real.rpow_le_rpow_of_exponent_le` / `Real.rpow_natCast` from
[`Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean),
and `Nat.le_ceil` from
[`Algebra/Order/Floor/Semiring.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean).
These are direct pinned Apache-2.0 Mathlib uses; no external Lean source is
copied or ported.
-/
theorem le_pow_natCeil_logb
    {base threshold : ℝ} (hbase : 1 < base) (hthreshold : 0 < threshold) :
    threshold ≤ base ^ (Nat.ceil (Real.logb base threshold)) := by
  have hceil : Real.logb base threshold ≤
      ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ) := Nat.le_ceil _
  calc
    threshold = base ^ Real.logb base threshold :=
      (Real.rpow_logb (by linarith) hbase.ne' hthreshold).symm
    _ ≤ base ^ ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase.le hceil
    _ = base ^ (Nat.ceil (Real.logb base threshold)) :=
      Real.rpow_natCast _ _

/--
The dyadic depth selected by `ceil(log₂(8 c / x))` makes a terminal radius
`2 c / 2^depth` at most `x / 4`.  This is the finite-depth numerical choice
used by the compact dyadic Wasserstein schedules.
-/
theorem dyadic_terminalRadius_le_quarter
    {coefficient radius : ℝ} (hcoefficient : 0 < coefficient) (hradius : 0 < radius) :
    2 * coefficient /
        ((2 ^ Nat.ceil (Real.logb 2 (8 * coefficient / radius)) : ℕ) : ℝ) ≤
      radius / 4 := by
  have hthreshold : 0 < 8 * coefficient / radius := by positivity
  have hpow := le_pow_natCeil_logb (base := (2 : ℝ))
    (threshold := 8 * coefficient / radius) (by norm_num) hthreshold
  have hpow' : 8 * coefficient / radius ≤
      ((2 ^ Nat.ceil (Real.logb 2 (8 * coefficient / radius)) : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hpow
  have hnum : 0 ≤ 2 * coefficient := by positivity
  calc
    2 * coefficient /
        ((2 ^ Nat.ceil (Real.logb 2 (8 * coefficient / radius)) : ℕ) : ℝ) ≤
        2 * coefficient / (8 * coefficient / radius) :=
      div_le_div_of_nonneg_left hnum hthreshold hpow'
    _ = radius / 4 := by field_simp; ring

/--
An explicit quadratic effective-count condition controls an inverse-square-
root term.  This is the numerical handoff from a sample-size lower bound to
the `x / 4` components of compact empirical-Wasserstein schedules.
-/
theorem div_sqrt_nat_le_div_of_sq_mul_le
    (count : ℕ) (hcount : 0 < count)
    {coefficient radius factor : ℝ}
    (hcoefficient : 0 ≤ coefficient) (hradius : 0 ≤ radius) (hfactor : 0 < factor)
    (hgate : factor ^ 2 * coefficient ^ 2 ≤ (count : ℝ) * radius ^ 2) :
    coefficient / Real.sqrt count ≤ radius / factor := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  apply (sq_le_sq₀ (div_nonneg hcoefficient (Real.sqrt_nonneg _))
    (div_nonneg hradius hfactor.le)).mp
  rw [div_pow, div_pow, Real.sq_sqrt hcount_real.le]
  apply (div_le_div_iff₀ hcount_real (sq_pos_of_pos hfactor)).mpr
  nlinarith

/-- A linear effective-count gate controls an inverse-count term with an
arbitrary positive budget factor. -/
theorem div_nat_le_div_of_mul_le
    (count : ℕ) (hcount : 0 < count)
    {coefficient radius factor : ℝ}
    (hfactor : 0 < factor)
    (hgate : factor * coefficient ≤ (count : ℝ) * radius) :
    coefficient / (count : ℝ) ≤ radius / factor := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  apply (div_le_div_iff₀ hcount_real hfactor).mpr
  nlinarith

/-- The positive natural ceiling of a real threshold.  It is a concrete
positive count that is at least the supplied threshold, without requiring the
threshold itself to be positive. -/
noncomputable def positiveNatCeil (threshold : ℝ) : ℕ :=
  Nat.ceil (max 1 threshold)

/-- The positive natural ceiling dominates its real threshold. -/
theorem le_positiveNatCeil (threshold : ℝ) : threshold ≤ positiveNatCeil threshold := by
  unfold positiveNatCeil
  exact (le_max_right _ _).trans (Nat.le_ceil _)

/-- The positive natural ceiling is nonzero. -/
theorem one_le_positiveNatCeil (threshold : ℝ) : 1 ≤ positiveNatCeil threshold := by
  have hreal : (1 : ℝ) ≤ positiveNatCeil threshold := by
    unfold positiveNatCeil
    exact (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast hreal

/--
The quarter-budget specialization of `div_sqrt_nat_le_div_of_sq_mul_le`.
-/
theorem div_sqrt_nat_le_quarter_of_sixteen_sq_le
    (count : ℕ) (hcount : 0 < count)
    {coefficient radius : ℝ} (hcoefficient : 0 ≤ coefficient) (hradius : 0 ≤ radius)
    (hcountBound : 16 * coefficient ^ 2 ≤ (count : ℝ) * radius ^ 2) :
    coefficient / Real.sqrt count ≤ radius / 4 := by
  have hcount_real : 0 < (count : ℝ) := by exact_mod_cast hcount
  apply (sq_le_sq₀ (div_nonneg hcoefficient (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [div_pow, div_pow, Real.sq_sqrt hcount_real.le]
  norm_num
  apply (div_le_div_iff₀ hcount_real (by norm_num : (0 : ℝ) < 16)).mpr
  nlinarith

/--
An explicit `d`th-power effective-count gate controls an `N^(-1/d)` term.
This is the numerical inversion used by supercritical empirical-Wasserstein
rates: if `coefficient^d ≤ N * radius^d`, then
`coefficient / N^(1/d) ≤ radius`.

Library provenance: this directly reuses Mathlib's
`Real.rpow_inv_le_iff_of_pos`, `Real.rpow_natCast`, and `Real.div_rpow` from
[`Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean),
plus `div_pow` from the imported algebraic power API, at the pinned
Apache-2.0 Mathlib commit. No external Lean source is copied or ported.
-/
theorem div_rpow_nat_inv_le_of_pow_le
    (dimension : ℕ) (hdimension : 0 < dimension)
    {coefficient count radius : ℝ}
    (hcoefficient : 0 ≤ coefficient) (hcount : 0 < count) (hradius : 0 < radius)
    (hgate : coefficient ^ dimension ≤ count * radius ^ dimension) :
    coefficient / count ^ ((dimension : ℝ)⁻¹) ≤ radius := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hroot_pos : 0 < count ^ ((dimension : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hcount _
  apply (div_le_iff₀ hroot_pos).2
  have hratio : coefficient / radius ≤ count ^ ((dimension : ℝ)⁻¹) := by
    apply (Real.rpow_inv_le_iff_of_pos (div_nonneg hcoefficient hradius.le) hcount.le
      (inv_pos.mpr hdimension_real)).mp
    rw [inv_inv, Real.rpow_natCast]
    calc
      (coefficient / radius) ^ dimension = coefficient ^ dimension / radius ^ dimension :=
        div_pow _ _ _
      _ ≤ count := (div_le_iff₀ (pow_pos hradius dimension)).2 hgate
  calc
    coefficient = (coefficient / radius) * radius := by field_simp
    _ ≤ count ^ ((dimension : ℝ)⁻¹) * radius :=
      mul_le_mul_of_nonneg_right hratio hradius.le
    _ = radius * count ^ ((dimension : ℝ)⁻¹) := by ring

/-- A six-way nonnegative error budget.  This is a small reusable bridge from
explicit componentwise real estimates to an `ENNReal` tolerance. -/
theorem ennreal_ofReal_sum_six_le_ofReal_of_each_le_sixth
    {a b c d e f radius : ℝ}
    (hradius : 0 ≤ radius)
    (ha_bound : a ≤ radius / 6) (hb_bound : b ≤ radius / 6)
    (hc_bound : c ≤ radius / 6) (hd_bound : d ≤ radius / 6)
    (he_bound : e ≤ radius / 6) (hf_bound : f ≤ radius / 6) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal d + ENNReal.ofReal e + ENNReal.ofReal f ≤
      ENNReal.ofReal radius := by
  calc
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal d + ENNReal.ofReal e + ENNReal.ofReal f ≤
        ENNReal.ofReal (radius / 6) + ENNReal.ofReal (radius / 6) +
          ENNReal.ofReal (radius / 6) + ENNReal.ofReal (radius / 6) +
          ENNReal.ofReal (radius / 6) + ENNReal.ofReal (radius / 6) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add (ENNReal.ofReal_le_ofReal ha_bound)
                (ENNReal.ofReal_le_ofReal hb_bound))
              (ENNReal.ofReal_le_ofReal hc_bound))
            (ENNReal.ofReal_le_ofReal hd_bound))
          (ENNReal.ofReal_le_ofReal he_bound))
        (ENNReal.ofReal_le_ofReal hf_bound)
    _ = ENNReal.ofReal radius := by
      rw [← ENNReal.ofReal_add (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6))
        (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6)),
        ← ENNReal.ofReal_add (by positivity) (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6)),
        ← ENNReal.ofReal_add (by positivity) (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6)),
        ← ENNReal.ofReal_add (by positivity) (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6)),
        ← ENNReal.ofReal_add (by positivity) (div_nonneg hradius (by norm_num : (0 : ℝ) ≤ 6))]
      congr 1
      ring

/-- A three-pair form of the six-way error budget.  It is convenient when a
concentration schedule retains two natural real-valued pairs before mapping
the sum into `ENNReal`. -/
theorem ennreal_ofReal_paired_sum_three_le_ofReal_of_each_le_sixth
    {a b c d e f radius : ℝ}
    (hradius : 0 ≤ radius)
    (ha_bound : a ≤ radius / 6) (hb_bound : b ≤ radius / 6)
    (hc_bound : c ≤ radius / 6) (hd_bound : d ≤ radius / 6)
    (he_bound : e ≤ radius / 6) (hf_bound : f ≤ radius / 6) :
    ENNReal.ofReal (a + b) + ENNReal.ofReal c +
        (ENNReal.ofReal (d + e) + ENNReal.ofReal f) ≤ ENNReal.ofReal radius := by
  calc
    ENNReal.ofReal (a + b) + ENNReal.ofReal c +
        (ENNReal.ofReal (d + e) + ENNReal.ofReal f) ≤
        ((ENNReal.ofReal a + ENNReal.ofReal b) + ENNReal.ofReal c) +
          ((ENNReal.ofReal d + ENNReal.ofReal e) + ENNReal.ofReal f) := by
      exact add_le_add
        (add_le_add ENNReal.ofReal_add_le le_rfl)
        (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ = ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal d + ENNReal.ofReal e + ENNReal.ofReal f := by ac_rfl
    _ ≤ ENNReal.ofReal radius :=
      ennreal_ofReal_sum_six_le_ofReal_of_each_le_sixth hradius ha_bound hb_bound
        hc_bound hd_bound he_bound hf_bound

/--
The natural floor of a positive-base logarithm is a concrete power below its
threshold.  Together with the ceiling counterpart, this turns logarithmic
cutoffs into finite Lean indices with both required numerical brackets.

Library provenance: this directly reuses `Nat.floor_le` from
[`Algebra/Order/Floor/Semiring.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Floor/Semiring.lean),
as well as the pinned Apache-2.0 real-logarithm and real-power declarations
cited by `le_pow_natCeil_logb`. No external Lean source is copied or ported.
-/
theorem pow_natFloor_logb_le
    {base threshold : ℝ} (hbase : 1 < base) (hthreshold : 1 ≤ threshold) :
    base ^ Nat.floor (Real.logb base threshold) ≤ threshold := by
  have hthreshold_pos : 0 < threshold := lt_of_lt_of_le zero_lt_one hthreshold
  have hlog_nonneg : 0 ≤ Real.logb base threshold := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg hthreshold) (Real.log_pos hbase).le
  have hfloor : ((Nat.floor (Real.logb base threshold) : ℕ) : ℝ) ≤
      Real.logb base threshold := Nat.floor_le hlog_nonneg
  calc
    base ^ Nat.floor (Real.logb base threshold) =
        base ^ ((Nat.floor (Real.logb base threshold) : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ base ^ Real.logb base threshold :=
      Real.rpow_le_rpow_of_exponent_le hbase.le hfloor
    _ = threshold := Real.rpow_logb (by linarith) hbase.ne' hthreshold_pos

/--
The floor logarithmic cutoff loses strictly less than one multiplicative
factor of its base.  This is the complementary bracket to
`pow_natFloor_logb_le`; together they turn a finite dyadic depth into both the
cell-count gate and an explicit terminal-radius estimate.

Library provenance: this uses the same pinned Apache-2.0 Mathlib floor,
real-logarithm, and real-power APIs credited by `pow_natFloor_logb_le`.
-/
theorem threshold_lt_base_mul_pow_natFloor_logb
    {base threshold : ℝ} (hbase : 1 < base) (hthreshold : 1 ≤ threshold) :
    threshold < base * base ^ Nat.floor (Real.logb base threshold) := by
  have hthreshold_pos : 0 < threshold := lt_of_lt_of_le zero_lt_one hthreshold
  have hfloor : Real.logb base threshold <
      ((Nat.floor (Real.logb base threshold) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (Real.logb base threshold)
  calc
    threshold = base ^ Real.logb base threshold :=
      (Real.rpow_logb (by linarith) hbase.ne' hthreshold_pos).symm
    _ < base ^ ((Nat.floor (Real.logb base threshold) + 1 : ℕ) : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hbase hfloor
    _ = base * base ^ Nat.floor (Real.logb base threshold) := by
      rw [show ((Nat.floor (Real.logb base threshold) + 1 : ℕ) : ℝ) =
          (Nat.floor (Real.logb base threshold) : ℝ) + 1 by norm_num]
      rw [Real.rpow_add (by linarith : 0 < base), Real.rpow_one,
        ← Real.rpow_natCast]
      ring

/--
The number of complete dyadic partition levels supported by a real effective
sample count.  The argument reserves one additional `d`-dimensional cell
level, which is exactly the small-error gate used in conditional shell
concentration.
-/
noncomputable def dyadicEffectiveCountDepth (dimension : ℕ) (effectiveCount : ℝ) : ℕ :=
  Nat.floor (Real.logb ((2 ^ dimension : ℕ) : ℝ)
    (effectiveCount / ((2 ^ dimension : ℕ) : ℝ)))

/--
The real-effective-count dyadic depth is monotone in its count argument.
This is the reusable numerical fact that turns a shellwise logarithmic depth
into one global sample-size logarithm on a finite retained head.
-/
theorem dyadicEffectiveCountDepth_mono
    (dimension : ℕ) (hdimension : 0 < dimension)
    {smaller larger : ℝ} (hsmaller : 0 < smaller) (hle : smaller ≤ larger) :
    dyadicEffectiveCountDepth dimension smaller ≤
      dyadicEffectiveCountDepth dimension larger := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  have hbase_nat : 2 ≤ 2 ^ dimension := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ dimension := Nat.pow_le_pow_right (by norm_num) hdimension
  have hbase : 1 < base := by
    dsimp [base]
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hbase_nat
  have hsmaller_div : 0 < smaller / base := div_pos hsmaller (by linarith)
  have hdiv_le : smaller / base ≤ larger / base :=
    div_le_div_of_nonneg_right hle (by linarith [hbase])
  unfold dyadicEffectiveCountDepth
  apply Nat.floor_le_floor
  exact Real.logb_le_logb_of_le hbase hsmaller_div hdiv_le

/--
At `dyadicEffectiveCountDepth`, the next full `d`-dimensional dyadic cell
level fits inside the real effective count.  This is the numerical form used
to discharge levelwise selected-shell gates without rounding `N μ(B)`.
-/
theorem dyadic_cellCount_next_le_effectiveCount
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount : ℝ}
    (heffectiveCount : ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount) :
    ((2 ^ (dimension * (dyadicEffectiveCountDepth dimension effectiveCount + 1)) : ℕ) : ℝ) ≤
      effectiveCount := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  have hbase_nat : 2 ≤ 2 ^ dimension := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ dimension := Nat.pow_le_pow_right (by norm_num) hdimension
  have hbase : 1 < base := by
    dsimp [base]
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hbase_nat
  have hthreshold : 1 ≤ effectiveCount / base := by
    apply (one_le_div (by linarith : 0 < base)).mpr
    simpa [base] using heffectiveCount
  have hpow := pow_natFloor_logb_le hbase hthreshold
  have hnext : base ^ (dyadicEffectiveCountDepth dimension effectiveCount + 1) ≤
      effectiveCount := by
    calc
      base ^ (dyadicEffectiveCountDepth dimension effectiveCount + 1) =
          base ^ dyadicEffectiveCountDepth dimension effectiveCount * base := by
            rw [pow_succ]
      _ ≤ (effectiveCount / base) * base :=
          mul_le_mul_of_nonneg_right (by
            simpa [dyadicEffectiveCountDepth, base] using hpow) (by linarith [hbase])
      _ = effectiveCount := by field_simp
  calc
    ((2 ^ (dimension * (dyadicEffectiveCountDepth dimension effectiveCount + 1)) : ℕ) : ℝ) =
        base ^ (dyadicEffectiveCountDepth dimension effectiveCount + 1) := by
          dsimp [base]
          norm_num [Nat.cast_pow, pow_mul]
    _ ≤ effectiveCount := hnext

/--
A finite depth that spends half the effective count on dyadic cells and half
on a nonnegative confidence term.  It is zero when the effective count is too
small to support even the first retained level.
-/
noncomputable def dyadicGeometricEffectiveDepth
    (dimension : ℕ) (effectiveCount confidence : ℝ) : ℕ :=
  if 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount then
    dyadicEffectiveCountDepth dimension (effectiveCount / 16)
  else 0

/--
Every retained dyadic level of `dyadicGeometricEffectiveDepth` satisfies the
quadratic small-error gate for the real effective count.  The constants split
the available count equally between its cell and confidence contributions.
-/
theorem dyadicGeometricEffectiveDepth_gate
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount confidence : ℝ} (hconfidence : 0 ≤ confidence)
    {level : ℕ} (hlevel : level ∈
      Finset.range (dyadicGeometricEffectiveDepth dimension effectiveCount confidence)) :
    4 * (2 * ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ) + confidence) ≤
      effectiveCount := by
  unfold dyadicGeometricEffectiveDepth at hlevel
  by_cases hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount
  · simp only [if_pos hlarge] at hlevel
    rcases hlarge with ⟨hcellBudget, hconfidenceBudget⟩
    have heffective : ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount / 16 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
      nlinarith
    have hcellDepth := dyadic_cellCount_next_le_effectiveCount
      dimension hdimension heffective
    have hlevelDepth : level + 1 ≤
        dyadicEffectiveCountDepth dimension (effectiveCount / 16) := by
      exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hlevel)
    have hcellNat : 2 ^ (dimension * (level + 1)) ≤
        2 ^ (dimension *
          (dyadicEffectiveCountDepth dimension (effectiveCount / 16) + 1)) := by
      apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
      exact Nat.mul_le_mul_left dimension (hlevelDepth.trans (Nat.le_succ _))
    have hcell : ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ) ≤
        effectiveCount / 16 := by
      calc
        ((2 ^ (dimension * (level + 1)) : ℕ) : ℝ) ≤
            ((2 ^ (dimension *
              (dyadicEffectiveCountDepth dimension (effectiveCount / 16) + 1)) : ℕ) : ℝ) := by
              exact_mod_cast hcellNat
        _ ≤ effectiveCount / 16 := hcellDepth
    nlinarith
  · simp only [if_neg hlarge] at hlevel
    simp at hlevel

/--
When the geometric effective-depth schedule is active, its terminal dyadic
cell scale is within two base factors of the real effective count.  This is
the lower numerical bracket needed to convert its terminal radius into the
dimension-dependent empirical-Wasserstein rate.
-/
theorem effectiveCount_lt_sixteen_mul_dyadicBase_sq_mul_pow_geometricEffectiveDepth
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    effectiveCount < 16 * ((2 ^ dimension : ℕ) : ℝ) ^ 2 *
      ((2 ^ dimension : ℕ) : ℝ) ^
        dyadicGeometricEffectiveDepth dimension effectiveCount confidence := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  have hbase_nat : 2 ≤ 2 ^ dimension := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ dimension := Nat.pow_le_pow_right (by norm_num) hdimension
  have hbase : 1 < base := by
    dsimp [base]
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hbase_nat
  have hthreshold : 1 ≤ (effectiveCount / 16) / base := by
    apply (one_le_div (by linarith : 0 < base)).mpr
    nlinarith [hlarge.1]
  have hbelow := threshold_lt_base_mul_pow_natFloor_logb hbase hthreshold
  unfold dyadicGeometricEffectiveDepth
  rw [if_pos hlarge]
  change effectiveCount < 16 * base ^ 2 * base ^
    dyadicEffectiveCountDepth dimension (effectiveCount / 16)
  calc
    effectiveCount = (16 * base) * ((effectiveCount / 16) / base) := by
      field_simp
    _ < (16 * base) *
        (base * base ^ dyadicEffectiveCountDepth dimension (effectiveCount / 16)) :=
      mul_lt_mul_of_pos_left
        (by simpa [dyadicEffectiveCountDepth, base] using hbelow)
        (by positivity)
    _ = 16 * base ^ 2 * base ^
        dyadicEffectiveCountDepth dimension (effectiveCount / 16) := by ring

/--
When the geometric effective-depth schedule is active, its next dyadic cell
level fits inside one sixteenth of the real effective count.  Together with
`effectiveCount_lt_sixteen_mul_dyadicBase_sq_mul_pow_geometricEffectiveDepth`,
this gives the two-sided finite-depth bracket used in each dimension regime.
-/
theorem dyadicBase_pow_succ_geometricEffectiveDepth_le_effectiveCount_div_sixteen
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    ((2 ^ dimension : ℕ) : ℝ) ^
        (dyadicGeometricEffectiveDepth dimension effectiveCount confidence + 1) ≤
      effectiveCount / 16 := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  have heffective : base ≤ effectiveCount / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    dsimp [base]
    nlinarith [hlarge.1]
  have hcell := dyadic_cellCount_next_le_effectiveCount
    dimension hdimension heffective
  unfold dyadicGeometricEffectiveDepth
  rw [if_pos hlarge]
  change base ^ (dyadicEffectiveCountDepth dimension (effectiveCount / 16) + 1) ≤ _
  calc
    base ^ (dyadicEffectiveCountDepth dimension (effectiveCount / 16) + 1) =
        ((2 ^ (dimension *
          (dyadicEffectiveCountDepth dimension (effectiveCount / 16) + 1)) : ℕ) : ℝ) := by
      dsimp [base]
      norm_num [Nat.cast_pow, pow_mul]
    _ ≤ effectiveCount / 16 := hcell

/--
In dimension one, an active real-effective-count depth gives the terminal
compact radius the explicit inverse-count scale.  The strict version is
convenient when this radius is assigned a positive share of a target error.
-/
theorem dyadicDimensionOne_terminalRadius_geometricEffectiveDepth_lt
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ 1 : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 effectiveCount confidence) : ℕ) : ℝ) <
      128 / effectiveCount := by
  have hlarge' := hlarge
  norm_num at hlarge'
  have heffectiveCount : 0 < effectiveCount := by
    nlinarith [hlarge'.1]
  have hcell := effectiveCount_lt_sixteen_mul_dyadicBase_sq_mul_pow_geometricEffectiveDepth
    1 (by omega) hlarge
  norm_num [Nat.cast_pow] at hcell
  have hcell' : effectiveCount < 64 *
      ((2 ^ (dyadicGeometricEffectiveDepth 1 effectiveCount confidence) : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hcell
  apply (div_lt_div_iff₀ (by positivity) heffectiveCount).mpr
  nlinarith

/--
In dimension two, an active real-effective-count depth gives the critical
terminal compact radius the inverse-square-root scale.  The logarithmic
multiscale contribution is treated separately by the critical-rate proof.
-/
theorem dyadicDimensionTwo_terminalRadius_geometricEffectiveDepth_lt
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ 2 : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    2 * Real.sqrt 2 /
        ((2 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) <
      32 * Real.sqrt 2 / Real.sqrt effectiveCount := by
  have hlarge' := hlarge
  norm_num at hlarge'
  have heffectiveCount : 0 < effectiveCount := by
    nlinarith [hlarge'.1]
  have hcell := effectiveCount_lt_sixteen_mul_dyadicBase_sq_mul_pow_geometricEffectiveDepth
    2 (by omega) hlarge
  norm_num [Nat.cast_pow] at hcell
  have hcell' : effectiveCount < 256 *
      ((4 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hcell
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  rw [div_pow, div_pow, Real.sq_sqrt heffectiveCount.le]
  have hpowsq :
      (((2 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) ^ 2) =
        ((4 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) := by
    calc
      (((2 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) ^ 2) =
          (((2 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) ^ 2 : ℕ) : ℝ) := by
            norm_num [Nat.cast_pow]
      _ = ((2 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence * 2) : ℕ) : ℝ) := by
            rw [← pow_mul]
      _ = ((2 ^ (2 * dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) := by
            rw [Nat.mul_comm]
      _ = (((2 ^ 2 : ℕ) ^ dyadicGeometricEffectiveDepth 2 effectiveCount confidence : ℕ) : ℝ) := by
            rw [pow_mul]
      _ = ((4 ^ (dyadicGeometricEffectiveDepth 2 effectiveCount confidence) : ℕ) : ℝ) := by
            norm_num
  rw [hpowsq]
  apply (div_lt_div_iff₀ (by positivity) heffectiveCount).mpr
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/--
For every positive dimension, the reciprocal terminal dyadic scale of an
active real-effective-count schedule is bounded by the corresponding
negative `1 / d` real power.  This is the common dimensional inversion used
by the supercritical empirical-Wasserstein calculation.
-/
theorem inv_dyadicGeometricEffectiveDepth_lt_effectiveCount_scale
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    1 / ((2 ^ (dyadicGeometricEffectiveDepth dimension effectiveCount confidence) : ℕ) : ℝ) <
      (effectiveCount /
        (16 * ((2 ^ dimension : ℕ) : ℝ) ^ 2)) ^ (-(dimension : ℝ)⁻¹) := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  let depth := dyadicGeometricEffectiveDepth dimension effectiveCount confidence
  let cells : ℝ := ((2 ^ depth : ℕ) : ℝ)
  let constant : ℝ := 16 * base ^ 2
  have hbase_pos : 0 < base := by
    dsimp [base]
    positivity
  have hconstant_pos : 0 < constant := by
    dsimp [constant]
    positivity
  have heffectiveCount_pos : 0 < effectiveCount := by
    have hcell : 0 < ((2 ^ dimension : ℕ) : ℝ) := by positivity
    nlinarith [hlarge.1]
  have hcells_pos : 0 < cells := by
    dsimp [cells]
    positivity
  have hcellScale := effectiveCount_lt_sixteen_mul_dyadicBase_sq_mul_pow_geometricEffectiveDepth
    dimension hdimension hlarge
  have hpowers : cells ^ dimension = base ^ depth := by
    dsimp [cells, base]
    calc
      (((2 ^ depth : ℕ) : ℝ) ^ dimension) =
          (((2 ^ depth : ℕ) ^ dimension : ℕ) : ℝ) := by
            norm_num [Nat.cast_pow]
      _ = ((2 ^ (depth * dimension) : ℕ) : ℝ) := by
            rw [← pow_mul]
      _ = ((2 ^ (dimension * depth) : ℕ) : ℝ) := by
            rw [Nat.mul_comm]
      _ = (((2 ^ dimension : ℕ) ^ depth : ℕ) : ℝ) := by
            rw [pow_mul]
      _ = (((2 ^ dimension : ℕ) : ℝ) ^ depth) := by
            norm_num [Nat.cast_pow]
  have hratio : effectiveCount / constant < cells ^ dimension := by
    apply (div_lt_iff₀ hconstant_pos).mpr
    calc
      effectiveCount < 16 * base ^ 2 * base ^ depth := by
        simpa [base, depth] using hcellScale
      _ = cells ^ dimension * constant := by
        rw [hpowers]
        dsimp [constant]
        ring
  have hratio_nonneg : 0 ≤ effectiveCount / constant :=
    (div_nonneg heffectiveCount_pos.le hconstant_pos.le)
  have hroot : (effectiveCount / constant) ^ ((dimension : ℝ)⁻¹) < cells := by
    apply (Real.rpow_inv_lt_iff_of_pos hratio_nonneg hcells_pos.le
      (by exact_mod_cast hdimension)).mpr
    rw [Real.rpow_natCast]
    exact hratio
  have hroot_pos : 0 < (effectiveCount / constant) ^ ((dimension : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (div_pos heffectiveCount_pos hconstant_pos) _
  have hinv : cells⁻¹ < ((effectiveCount / constant) ^ ((dimension : ℝ)⁻¹))⁻¹ :=
    (inv_lt_inv₀ hcells_pos hroot_pos).mpr hroot
  change 1 / cells < (effectiveCount / constant) ^ (-(dimension : ℝ)⁻¹)
  simpa only [one_div, Real.rpow_neg (div_nonneg heffectiveCount_pos.le hconstant_pos.le)]
    using hinv

/--
The shell-mass-scaled negative `1/d` effective-count factor separates into
the usual global `count^(-1/d)` rate and the source-mass power
`mass^(1-1/d)`.  This is algebra, but retaining it as a named lemma prevents
the supercritical shell calculation from hiding a change of exponent.
-/
theorem mass_mul_div_rpow_neg_inv_nat_eq
    (dimension : ℕ) (hdimension : 0 < dimension)
    {count mass constant : ℝ}
    (hcount : 0 < count) (hmass : 0 < mass) (hconstant : 0 < constant) :
    mass * ((count * mass / constant) ^ (-(dimension : ℝ)⁻¹)) =
      constant ^ ((dimension : ℝ)⁻¹) *
        mass ^ (1 - (dimension : ℝ)⁻¹) / count ^ ((dimension : ℝ)⁻¹) := by
  let exponent : ℝ := (dimension : ℝ)⁻¹
  have hexponent : 0 < exponent := by
    dsimp [exponent]
    exact inv_pos.mpr (by exact_mod_cast hdimension)
  have hmass_combine : mass * mass ^ (-exponent) = mass ^ (1 - exponent) := by
    calc
      mass * mass ^ (-exponent) = mass ^ 1 * mass ^ (-exponent) := by
        rw [Real.rpow_one]
      _ = mass ^ (1 + -exponent) := (Real.rpow_add hmass _ _).symm
      _ = mass ^ (1 - exponent) := by congr 1
  have hcount_pow_ne : count ^ exponent ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hcount exponent)
  have hconstant_pow_ne : constant ^ exponent ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hconstant exponent)
  change mass * ((count * mass / constant) ^ (-exponent)) =
    constant ^ exponent * mass ^ (1 - exponent) / count ^ exponent
  calc
    mass * ((count * mass / constant) ^ (-exponent)) =
        mass * ((count * mass) ^ (-exponent) / constant ^ (-exponent)) := by
          rw [Real.div_rpow (mul_nonneg hcount.le hmass.le) hconstant.le]
    _ = mass * ((count ^ (-exponent) * mass ^ (-exponent)) /
        constant ^ (-exponent)) := by
          rw [Real.mul_rpow hcount.le hmass.le]
    _ = (mass * mass ^ (-exponent)) * constant ^ exponent / count ^ exponent := by
          rw [Real.rpow_neg hcount.le, Real.rpow_neg hconstant.le]
          field_simp
    _ = constant ^ exponent * mass ^ (1 - exponent) / count ^ exponent := by
          rw [hmass_combine]
          ring

/--
For an active geometric effective depth, the increasing supercritical ratio
is still dominated by one inverse terminal dyadic scale after normalizing by
the square root of the effective count.  This is the finite-depth numerical
step that keeps the supercritical multiscale contribution at the
`count^(-1/d)` scale.
-/
theorem dyadicSupercritical_ratio_pow_succ_div_sqrt_le_inv_terminalCell
    (dimension : ℕ) (hdimension : 0 < dimension)
    {effectiveCount confidence : ℝ}
    (hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount) :
    (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
        (dyadicGeometricEffectiveDepth dimension effectiveCount confidence + 1) /
        Real.sqrt effectiveCount ≤
      1 / (8 * ((2 ^ (dyadicGeometricEffectiveDepth dimension effectiveCount confidence) : ℕ) : ℝ)) := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  let depth : ℕ := dyadicGeometricEffectiveDepth dimension effectiveCount confidence
  let cells : ℝ := ((2 ^ depth : ℕ) : ℝ)
  have hbase_nonneg : 0 ≤ base := by
    dsimp [base]
    positivity
  have heffectiveCount_pos : 0 < effectiveCount := by
    have hbase_pos : 0 < 16 * ((2 ^ dimension : ℕ) : ℝ) := by positivity
    exact lt_of_lt_of_le hbase_pos hlarge.1
  have hcell := dyadicBase_pow_succ_geometricEffectiveDepth_le_effectiveCount_div_sixteen
    dimension hdimension hlarge
  have hratio_nonneg : 0 ≤ (Real.sqrt base / 2) ^ (depth + 1) / Real.sqrt effectiveCount := by
    positivity
  have hright_nonneg : 0 ≤ 1 / (8 * cells) := by
    positivity
  apply (sq_le_sq₀ hratio_nonneg hright_nonneg).mp
  have hratio_sq : (Real.sqrt base / 2) ^ 2 = base / 4 := by
    rw [div_pow, Real.sq_sqrt hbase_nonneg]
    norm_num
  have hratio_pow :
      (Real.sqrt base / 2) ^ (2 * (depth + 1)) = (base / 4) ^ (depth + 1) := by
    rw [pow_mul, hratio_sq]
  have hleft_sq :
      ((Real.sqrt base / 2) ^ (depth + 1) / Real.sqrt effectiveCount) ^ 2 =
        base ^ (depth + 1) / (4 ^ (depth + 1) * effectiveCount) := by
    calc
      ((Real.sqrt base / 2) ^ (depth + 1) / Real.sqrt effectiveCount) ^ 2 =
          ((Real.sqrt base / 2) ^ (depth + 1)) ^ 2 / effectiveCount := by
            rw [div_pow, Real.sq_sqrt heffectiveCount_pos.le]
      _ = (Real.sqrt base / 2) ^ ((depth + 1) * 2) / effectiveCount := by
            rw [pow_mul]
      _ = (Real.sqrt base / 2) ^ (2 * (depth + 1)) / effectiveCount := by
            congr 2
            omega
      _ = (base / 4) ^ (depth + 1) / effectiveCount := by rw [hratio_pow]
      _ = base ^ (depth + 1) / (4 ^ (depth + 1) * effectiveCount) := by
            rw [div_pow]
            ring
  have hright_sq : (1 / (8 * cells)) ^ 2 =
      1 / (16 * 4 ^ (depth + 1)) := by
    dsimp [cells]
    have hfour : (4 : ℝ) ^ depth = ((2 : ℝ) ^ depth) ^ 2 := by
      calc
        (4 : ℝ) ^ depth = ((2 : ℝ) ^ 2) ^ depth := by norm_num
        _ = (2 : ℝ) ^ (2 * depth) := by rw [← pow_mul]
        _ = (2 : ℝ) ^ (depth * 2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ depth) ^ 2 := pow_mul _ depth 2
    rw [div_pow]
    norm_num [Nat.cast_pow, pow_succ]
    rw [hfour]
    field_simp
    ring
  change ((Real.sqrt base / 2) ^ (depth + 1) / Real.sqrt effectiveCount) ^ 2 ≤
    (1 / (8 * cells)) ^ 2
  rw [hleft_sq, hright_sq]
  have hdenleft : 0 < (4 : ℝ) ^ (depth + 1) * effectiveCount := by positivity
  have hdenright : 0 < (16 : ℝ) * 4 ^ (depth + 1) := by positivity
  apply (div_le_div_iff₀ hdenleft hdenright).mpr
  field_simp
  have hcell_scaled :
      ((2 ^ dimension : ℕ) : ℝ) ^
          (dyadicGeometricEffectiveDepth dimension effectiveCount confidence + 1) * 16 ≤
        effectiveCount :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mp hcell
  simpa [base, depth] using hcell_scaled

/--
On a probability mass, every power `1 - 1 / d` with `d ≥ 2` is bounded by
the square-root power.  This lets the supercritical empirical-Wasserstein
source-shell sum reuse the same radial square-root envelope as the critical
and subcritical terms.
-/
theorem rpow_one_sub_inv_nat_le_sqrt
    (dimension : ℕ) (hdimension : 2 ≤ dimension)
    {mass : ℝ} (hmass_nonneg : 0 ≤ mass) (hmass_le_one : mass ≤ 1) :
    mass ^ (1 - (dimension : ℝ)⁻¹) ≤ Real.sqrt mass := by
  rw [Real.sqrt_eq_rpow]
  have hdimension_real : (2 : ℝ) ≤ dimension := by
    exact_mod_cast hdimension
  have hinv : (dimension : ℝ)⁻¹ ≤ 1 / (2 : ℝ) := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hdimension_real)
  have hexponent_pos : 0 < 1 - (dimension : ℝ)⁻¹ := by
    linarith
  by_cases hmass_zero : mass = 0
  · subst mass
    rw [Real.zero_rpow hexponent_pos.ne']
    norm_num
  apply Real.rpow_le_rpow_of_exponent_ge
    (lt_of_le_of_ne hmass_nonneg (Ne.symm hmass_zero)) hmass_le_one
  linarith

/--
A nonnegative quantity below a threshold is bounded by the product of their
square roots.  This is the elementary small-mass split used when an empirical
shell receives no positive dyadic depth.
-/
theorem le_sqrt_mul_sqrt_of_nonneg_of_le
    {mass threshold : ℝ} (hmass_nonneg : 0 ≤ mass) (hmass_le : mass ≤ threshold) :
    mass ≤ Real.sqrt mass * Real.sqrt threshold := by
  calc
    mass = Real.sqrt mass * Real.sqrt mass := (Real.mul_self_sqrt hmass_nonneg).symm
    _ ≤ Real.sqrt mass * Real.sqrt threshold :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass_le) (Real.sqrt_nonneg _)

/--
The source-mass factor cancels one square root of a positive real effective
count.  This is the algebraic normalization behind the finite shell-head
`N⁻¹ᐟ²` terms.
-/
theorem mass_div_sqrt_mul_eq_sqrt_mass_div_sqrt_count
    {count mass : ℝ} (hcount : 0 < count) (hmass : 0 < mass) :
    mass / Real.sqrt (count * mass) = Real.sqrt mass / Real.sqrt count := by
  rw [Real.sqrt_mul hcount.le]
  have hsqrtCount : Real.sqrt count ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcount)
  have hsqrtMass : Real.sqrt mass ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmass)
  have hmass_eq : mass = Real.sqrt mass * Real.sqrt mass :=
    (Real.mul_self_sqrt hmass.le).symm
  nth_rewrite 1 [hmass_eq]
  field_simp

/-- A positive source mass cancels from an inverse real effective count. -/
theorem mass_mul_div_mul_eq_div_count
    {constant count mass : ℝ} (hcount : 0 < count) (hmass : 0 < mass) :
    mass * (constant / (count * mass)) = constant / count := by
  field_simp [hcount.ne', hmass.ne']

/-- A source-mass-scaled square-root effective-count term has its canonical
`sqrt(mass) / sqrt(count)` form. -/
theorem mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count
    {constant count mass : ℝ} (hcount : 0 < count) (hmass : 0 < mass) :
    mass * (constant / Real.sqrt (count * mass)) =
      constant * Real.sqrt mass / Real.sqrt count := by
  calc
    mass * (constant / Real.sqrt (count * mass)) =
        constant * (mass / Real.sqrt (count * mass)) := by ring
    _ = constant * (Real.sqrt mass / Real.sqrt count) := by
        rw [mass_div_sqrt_mul_eq_sqrt_mass_div_sqrt_count hcount hmass]
    _ = constant * Real.sqrt mass / Real.sqrt count := by ring

/--
After multiplying by a positive source-shell mass, the active one-dimensional
terminal term is an inverse-total-count contribution.  This is the local
subcritical part of the finite shell-head calculation.
-/
theorem mass_mul_dyadicDimensionOne_terminalRadius_geometricEffectiveDepth_lt
    {count mass confidence : ℝ} (hcount : 0 < count) (hmass : 0 < mass)
    (hlarge : 16 * ((2 ^ 1 : ℕ) : ℝ) ≤ count * mass ∧
      8 * confidence ≤ count * mass) :
    mass * (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ)) <
      128 / count := by
  have hterminal := dyadicDimensionOne_terminalRadius_geometricEffectiveDepth_lt hlarge
  have hscaled := mul_lt_mul_of_pos_left hterminal hmass
  calc
    mass * (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ)) <
        mass * (128 / (count * mass)) := hscaled
    _ = 128 / count := mass_mul_div_mul_eq_div_count hcount hmass

/--
After multiplying by a positive source-shell mass, the active critical
terminal term has the canonical `sqrt(mass) / sqrt(count)` scale.
-/
theorem mass_mul_dyadicDimensionTwo_terminalRadius_geometricEffectiveDepth_lt
    {count mass confidence : ℝ} (hcount : 0 < count) (hmass : 0 < mass)
    (hlarge : 16 * ((2 ^ 2 : ℕ) : ℝ) ≤ count * mass ∧
      8 * confidence ≤ count * mass) :
    mass * (2 * Real.sqrt 2 /
        ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ)) <
      32 * Real.sqrt 2 * Real.sqrt mass / Real.sqrt count := by
  have hterminal := dyadicDimensionTwo_terminalRadius_geometricEffectiveDepth_lt hlarge
  have hscaled := mul_lt_mul_of_pos_left hterminal hmass
  calc
    mass * (2 * Real.sqrt 2 /
        ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ)) <
        mass * (32 * Real.sqrt 2 / Real.sqrt (count * mass)) := hscaled
    _ = 32 * Real.sqrt 2 * Real.sqrt mass / Real.sqrt count :=
      mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass

/--
The full active one-dimensional finite-depth envelope, after source-mass
scaling.  The terminal term is inverse-count while the two stochastic terms
have the common square-root shell-mass form needed for radial summation.
-/
theorem mass_mul_dyadicDimensionOne_activeEnvelope_lt
    {count mass confidence : ℝ} (hcount : 0 < count) (hmass : 0 < mass)
    (hlarge : 16 * ((2 ^ 1 : ℕ) : ℝ) ≤ count * mass ∧
      8 * confidence ≤ count * mass) :
    mass *
        (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ) +
          (2 / Real.sqrt (count * mass)) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt (count * mass)) <
      128 / count +
        (2 * (1 / (1 - 1 / Real.sqrt 2)) + 2 * Real.sqrt confidence) *
          Real.sqrt mass / Real.sqrt count := by
  have hterminal := mass_mul_dyadicDimensionOne_terminalRadius_geometricEffectiveDepth_lt
    hcount hmass hlarge
  have hfluctuation :
      mass * ((2 / Real.sqrt (count * mass)) * (1 / (1 - 1 / Real.sqrt 2))) =
        (2 * (1 / (1 - 1 / Real.sqrt 2))) * Real.sqrt mass / Real.sqrt count := by
    calc
      mass * ((2 / Real.sqrt (count * mass)) * (1 / (1 - 1 / Real.sqrt 2))) =
          (mass * (2 / Real.sqrt (count * mass))) * (1 / (1 - 1 / Real.sqrt 2)) := by ring
      _ = (2 * Real.sqrt mass / Real.sqrt count) * (1 / (1 - 1 / Real.sqrt 2)) := by
          rw [mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass]
      _ = (2 * (1 / (1 - 1 / Real.sqrt 2))) * Real.sqrt mass / Real.sqrt count := by ring
  have hconfidenceTerm :
      mass * (2 * Real.sqrt confidence / Real.sqrt (count * mass)) =
        (2 * Real.sqrt confidence) * Real.sqrt mass / Real.sqrt count := by
    rw [show mass * (2 * Real.sqrt confidence / Real.sqrt (count * mass)) =
        (2 * Real.sqrt confidence) * Real.sqrt mass / Real.sqrt count by
      exact mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass]
  calc
    mass *
        (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ) +
          (2 / Real.sqrt (count * mass)) * (1 / (1 - 1 / Real.sqrt 2)) +
          2 * Real.sqrt confidence / Real.sqrt (count * mass)) =
        mass * (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ)) +
          mass * ((2 / Real.sqrt (count * mass)) * (1 / (1 - 1 / Real.sqrt 2))) +
          mass * (2 * Real.sqrt confidence / Real.sqrt (count * mass)) := by ring
    _ < 128 / count +
        (2 * (1 / (1 - 1 / Real.sqrt 2)) + 2 * Real.sqrt confidence) *
          Real.sqrt mass / Real.sqrt count := by
      rw [hfluctuation, hconfidenceTerm]
      calc
        mass * (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ)) +
            2 * (1 / (1 - 1 / Real.sqrt 2)) * Real.sqrt mass / Real.sqrt count +
            2 * Real.sqrt confidence * Real.sqrt mass / Real.sqrt count =
            mass * (2 / ((2 ^ (dyadicGeometricEffectiveDepth 1 (count * mass) confidence) : ℕ) : ℝ)) +
              (2 * (1 / (1 - 1 / Real.sqrt 2)) + 2 * Real.sqrt confidence) *
                Real.sqrt mass / Real.sqrt count := by ring
        _ < 128 / count +
            (2 * (1 / (1 - 1 / Real.sqrt 2)) + 2 * Real.sqrt confidence) *
              Real.sqrt mass / Real.sqrt count :=
          by linarith

/--
The active critical-dimensional finite-depth envelope after source-mass
scaling.  Its retained depth remains explicit: this is exactly the logarithmic
factor that must be bounded uniformly when a finite shell head is selected.
-/
theorem mass_mul_dyadicDimensionTwo_activeEnvelope_lt
    {count mass confidence : ℝ} (hcount : 0 < count) (hmass : 0 < mass)
    (hlarge : 16 * ((2 ^ 2 : ℕ) : ℝ) ≤ count * mass ∧
      8 * confidence ≤ count * mass) :
    mass *
        (2 * Real.sqrt 2 /
            ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ) +
          4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) /
            Real.sqrt (count * mass) +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt (count * mass)) <
      (32 * Real.sqrt 2 +
          4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) +
          2 * Real.sqrt 2 * Real.sqrt confidence) *
        Real.sqrt mass / Real.sqrt count := by
  have hterminal := mass_mul_dyadicDimensionTwo_terminalRadius_geometricEffectiveDepth_lt
    hcount hmass hlarge
  have hdepthTerm :
      mass *
          (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) /
            Real.sqrt (count * mass)) =
        (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence)) *
          Real.sqrt mass / Real.sqrt count := by
    exact mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass
  have hconfidenceTerm :
      mass * (2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt (count * mass)) =
        (2 * Real.sqrt 2 * Real.sqrt confidence) *
          Real.sqrt mass / Real.sqrt count := by
    exact mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass
  calc
    mass *
        (2 * Real.sqrt 2 /
            ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ) +
          4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) /
            Real.sqrt (count * mass) +
          2 * Real.sqrt 2 * Real.sqrt confidence / Real.sqrt (count * mass)) =
        mass * (2 * Real.sqrt 2 /
            ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ)) +
          mass * (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) /
            Real.sqrt (count * mass)) +
          mass * (2 * Real.sqrt 2 * Real.sqrt confidence /
            Real.sqrt (count * mass)) := by ring
    _ < (32 * Real.sqrt 2 +
          4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) +
          2 * Real.sqrt 2 * Real.sqrt confidence) *
        Real.sqrt mass / Real.sqrt count := by
      rw [hdepthTerm, hconfidenceTerm]
      calc
        mass * (2 * Real.sqrt 2 /
            ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ)) +
            (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence)) *
              Real.sqrt mass / Real.sqrt count +
            (2 * Real.sqrt 2 * Real.sqrt confidence) *
              Real.sqrt mass / Real.sqrt count =
            mass * (2 * Real.sqrt 2 /
              ((2 ^ (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) : ℕ) : ℝ)) +
              (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) +
                2 * Real.sqrt 2 * Real.sqrt confidence) *
                  Real.sqrt mass / Real.sqrt count := by ring
        _ < 32 * Real.sqrt 2 * Real.sqrt mass / Real.sqrt count +
            (4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) +
              2 * Real.sqrt 2 * Real.sqrt confidence) *
                Real.sqrt mass / Real.sqrt count := by
          nlinarith
        _ = (32 * Real.sqrt 2 +
          4 * (dyadicGeometricEffectiveDepth 2 (count * mass) confidence) +
          2 * Real.sqrt 2 * Real.sqrt confidence) *
            Real.sqrt mass / Real.sqrt count := by ring

/--
The active supercritical finite-depth envelope has the canonical fractional
source-mass scale.  The terminal and increasing geometric contributions are
both charged to the same inverse-effective-count factor; the confidence term
retains its smaller square-root scale.
-/
theorem mass_mul_dyadicDimensionGreaterTwo_activeEnvelope_lt
    (dimension : ℕ) (hdimension : 2 < dimension)
    {count mass confidence : ℝ} (hcount : 0 < count) (hmass : 0 < mass)
    (hlarge : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ count * mass ∧
      8 * confidence ≤ count * mass) :
    mass *
        (2 * Real.sqrt dimension /
            ((2 ^ (dyadicGeometricEffectiveDepth dimension (count * mass) confidence) : ℕ) : ℝ) +
          (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
            (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2) ^
              (dyadicGeometricEffectiveDepth dimension (count * mass) confidence + 1) /
              (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1) +
          2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt (count * mass)) <
      (2 * Real.sqrt dimension +
          Real.sqrt dimension * Real.sqrt 2 /
            (4 * (Real.sqrt ((2 ^ dimension : ℕ) : ℝ) / 2 - 1))) *
        (mass * ((count * mass /
          (16 * ((2 ^ dimension : ℕ) : ℝ) ^ 2)) ^ (-(dimension : ℝ)⁻¹))) +
      (2 * Real.sqrt dimension * Real.sqrt confidence) *
        Real.sqrt mass / Real.sqrt count := by
  let base : ℝ := ((2 ^ dimension : ℕ) : ℝ)
  let depth : ℕ := dyadicGeometricEffectiveDepth dimension (count * mass) confidence
  let cells : ℝ := ((2 ^ depth : ℕ) : ℝ)
  let ratio : ℝ := Real.sqrt base / 2
  let scale : ℝ := (count * mass / (16 * base ^ 2)) ^ (-(dimension : ℝ)⁻¹)
  have hdimension_pos : 0 < dimension := by omega
  have heffective_pos : 0 < count * mass := mul_pos hcount hmass
  have hratio_gt_one : 1 < ratio := by
    dsimp [ratio, base]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simp only [one_mul]
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr
    have hpow : 2 ^ 2 < 2 ^ dimension :=
      Nat.pow_lt_pow_right (by norm_num) hdimension
    norm_num at hpow ⊢
    exact_mod_cast hpow
  have hratio_sub_pos : 0 < ratio - 1 := by linarith
  have hcells_pos : 0 < cells := by
    dsimp [cells]
    positivity
  have hscale_inv := inv_dyadicGeometricEffectiveDepth_lt_effectiveCount_scale
    dimension hdimension_pos hlarge
  have hratio_bound := dyadicSupercritical_ratio_pow_succ_div_sqrt_le_inv_terminalCell
    dimension hdimension_pos hlarge
  have hinv_cells : 1 / cells < scale := by
    simpa [base, depth, cells, scale] using hscale_inv
  have hratio_bound' : ratio ^ (depth + 1) / Real.sqrt (count * mass) ≤
      1 / (8 * cells) := by
    simpa [base, depth, cells, ratio] using hratio_bound
  have hscale_pos : 0 < scale := by
    dsimp [scale, base]
    exact Real.rpow_pos_of_pos
      (div_pos heffective_pos (by positivity)) _
  have hterminal :
      mass * (2 * Real.sqrt dimension / cells) <
        (2 * Real.sqrt dimension) * (mass * scale) := by
    have hterminalCoefficient_pos : 0 < 2 * Real.sqrt dimension * mass := by
      positivity
    have hmult := mul_lt_mul_of_pos_left hinv_cells hterminalCoefficient_pos
    change mass * (2 * Real.sqrt dimension / cells) <
      (2 * Real.sqrt dimension) * (mass * scale)
    calc
      mass * (2 * Real.sqrt dimension / cells) =
          (2 * Real.sqrt dimension * mass) * (1 / cells) := by field_simp [hcells_pos.ne']
      _ < (2 * Real.sqrt dimension * mass) * scale := hmult
      _ = (2 * Real.sqrt dimension) * (mass * scale) := by ring
  have hgeometric :
      mass *
          ((2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
            ratio ^ (depth + 1) / (ratio - 1)) <
        (Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1))) *
          (mass * scale) := by
    have hcoefficient_pos : 0 <
        (2 * Real.sqrt dimension * Real.sqrt 2 / (ratio - 1)) * mass := by
      positivity
    have hratio_mult := mul_le_mul_of_nonneg_left hratio_bound' hcoefficient_pos.le
    have hgeoCoefficient_pos : 0 <
        Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1)) := by
      positivity
    have hscaled_lt := mul_lt_mul_of_pos_left hinv_cells
      (mul_pos hgeoCoefficient_pos hmass)
    have hsqrteffective_ne : Real.sqrt (count * mass) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr heffective_pos)
    calc
      mass *
          ((2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
            ratio ^ (depth + 1) / (ratio - 1)) =
          (2 * Real.sqrt dimension * Real.sqrt 2 / (ratio - 1)) * mass *
            (ratio ^ (depth + 1) / Real.sqrt (count * mass)) := by
              field_simp [hsqrteffective_ne, hratio_sub_pos.ne']
      _ ≤ (2 * Real.sqrt dimension * Real.sqrt 2 / (ratio - 1)) * mass *
            (1 / (8 * cells)) := hratio_mult
      _ = (Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1))) *
            (mass * (1 / cells)) := by
              field_simp [hcells_pos.ne', hratio_sub_pos.ne']
              ring
      _ < (Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1))) *
            (mass * scale) := by
              simpa only [mul_assoc] using hscaled_lt
  have hconfidence :
      mass * (2 * Real.sqrt dimension * Real.sqrt confidence /
        Real.sqrt (count * mass)) =
      (2 * Real.sqrt dimension * Real.sqrt confidence) *
        Real.sqrt mass / Real.sqrt count :=
    mass_mul_div_sqrt_mul_eq_mul_sqrt_mass_div_sqrt_count hcount hmass
  change mass *
      (2 * Real.sqrt dimension / cells +
        (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
          ratio ^ (depth + 1) / (ratio - 1) +
        2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt (count * mass)) < _
  calc
    mass *
        (2 * Real.sqrt dimension / cells +
          (2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
            ratio ^ (depth + 1) / (ratio - 1) +
          2 * Real.sqrt dimension * Real.sqrt confidence / Real.sqrt (count * mass)) =
        (mass * (2 * Real.sqrt dimension / cells) +
          mass * ((2 * Real.sqrt dimension * Real.sqrt 2 / Real.sqrt (count * mass)) *
            ratio ^ (depth + 1) / (ratio - 1))) +
          mass * (2 * Real.sqrt dimension * Real.sqrt confidence /
            Real.sqrt (count * mass)) := by ring
    _ < ((2 * Real.sqrt dimension) * (mass * scale) +
          (Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1))) *
            (mass * scale)) +
          mass * (2 * Real.sqrt dimension * Real.sqrt confidence /
            Real.sqrt (count * mass)) :=
      by linarith [add_lt_add hterminal hgeometric]
    _ = (2 * Real.sqrt dimension +
          Real.sqrt dimension * Real.sqrt 2 / (4 * (ratio - 1))) *
          (mass * scale) +
        (2 * Real.sqrt dimension * Real.sqrt confidence) *
          Real.sqrt mass / Real.sqrt count := by
      rw [hconfidence]
      ring

/--
If the real-effective-count dyadic gate is inactive, the effective count is
strictly below the sum of its cell and confidence budgets.  This turns the
zero-depth branch into a uniform small-mass estimate on a finite shell head.
-/
theorem effectiveCount_lt_cellBudget_add_confidenceBudget_of_not_geometricEffectiveDepth_gate
    (dimension : ℕ) {effectiveCount confidence : ℝ} (hconfidence : 0 ≤ confidence)
    (hinactive : ¬ (16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount ∧
      8 * confidence ≤ effectiveCount)) :
    effectiveCount < 16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * confidence := by
  by_cases hcell : 16 * ((2 ^ dimension : ℕ) : ℝ) ≤ effectiveCount
  · have hconfidence' : ¬ 8 * confidence ≤ effectiveCount := by
      intro hconfidenceBudget
      exact hinactive ⟨hcell, hconfidenceBudget⟩
    have hconfidence_lt : effectiveCount < 8 * confidence := lt_of_not_ge hconfidence'
    nlinarith
  · have hcell_lt : effectiveCount < 16 * ((2 ^ dimension : ℕ) : ℝ) :=
      lt_of_not_ge hcell
    nlinarith

/--
The same concrete logarithmic cutoff overshoots its threshold by less than
one multiplicative factor of the base.  This upper bracket is the half of the
source `n_1` calculation needed to keep its finite Bennett head large enough.

Library provenance: in addition to the declarations cited by
`le_pow_natCeil_logb`, this directly reuses `Nat.ceil_lt_add_one` from the
same pinned Apache-2.0 Mathlib floor module.
-/
theorem pow_natCeil_logb_lt_mul
    {base threshold : ℝ} (hbase : 1 < base) (hthreshold : 1 ≤ threshold) :
    base ^ (Nat.ceil (Real.logb base threshold)) < base * threshold := by
  have hlogb_nonneg : 0 ≤ Real.logb base threshold := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg hthreshold) (Real.log_pos hbase).le
  have hceil_lt : ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ) <
      Real.logb base threshold + 1 :=
    Nat.ceil_lt_add_one hlogb_nonneg
  calc
    base ^ (Nat.ceil (Real.logb base threshold)) =
        base ^ ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ < base ^ (Real.logb base threshold + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt hbase hceil_lt
    _ = base * threshold := by
      rw [Real.rpow_add (by linarith), Real.rpow_one,
        Real.rpow_logb (by linarith) hbase.ne' (lt_of_lt_of_le zero_lt_one hthreshold)]
      ring

/--
Taking a negative power reverses the upper logarithmic-cutoff bracket.  This
is the reusable form needed when a shell weight decays with its cutoff index.

Library provenance: this directly reuses `Real.mul_rpow`, `Real.rpow_mul`,
and `Real.rpow_neg` from the pinned Apache-2.0
[`Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean),
in addition to the logarithmic-cutoff declarations cited above. No external
Lean source is copied or ported.
-/
theorem mul_rpow_neg_le_rpow_neg_mul_natCeil_logb
    {base threshold exponent : ℝ}
    (hbase : 1 < base) (hthreshold : 1 ≤ threshold) (hexponent : 0 ≤ exponent) :
    base ^ (-exponent) * threshold ^ (-exponent) ≤
      base ^ (-exponent * ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ)) := by
  let cutoff : ℕ := Nat.ceil (Real.logb base threshold)
  have hbase_pos : 0 < base := by linarith
  have hthreshold_pos : 0 < threshold := lt_of_lt_of_le zero_lt_one hthreshold
  have hpower : base ^ (cutoff : ℝ) ≤ base * threshold := by
    calc
      base ^ (cutoff : ℝ) = base ^ cutoff := Real.rpow_natCast _ _
      _ ≤ base * threshold := (pow_natCeil_logb_lt_mul hbase hthreshold).le
  have hpower_pos : 0 < base ^ (cutoff : ℝ) :=
    Real.rpow_pos_of_pos hbase_pos _
  have hproduct_pos : 0 < base * threshold := mul_pos hbase_pos hthreshold_pos
  have hraised : (base ^ (cutoff : ℝ)) ^ exponent ≤
      (base * threshold) ^ exponent :=
    Real.rpow_le_rpow hpower_pos.le hpower hexponent
  have hinv : ((base * threshold) ^ exponent)⁻¹ ≤
      ((base ^ (cutoff : ℝ)) ^ exponent)⁻¹ :=
    (inv_le_inv₀
      (Real.rpow_pos_of_pos hproduct_pos exponent)
      (Real.rpow_pos_of_pos hpower_pos exponent)).2 hraised
  have hnegative : (base * threshold) ^ (-exponent) ≤
      (base ^ (cutoff : ℝ)) ^ (-exponent) := by
    rw [Real.rpow_neg hproduct_pos.le, Real.rpow_neg hpower_pos.le]
    exact hinv
  calc
    base ^ (-exponent) * threshold ^ (-exponent) =
        (base * threshold) ^ (-exponent) := by
      rw [Real.mul_rpow hbase_pos.le hthreshold_pos.le]
    _ ≤ (base ^ (cutoff : ℝ)) ^ (-exponent) := hnegative
    _ = base ^ ((cutoff : ℝ) * (-exponent)) := by
      rw [Real.rpow_mul hbase_pos.le]
    _ = base ^ (-exponent * ((Nat.ceil (Real.logb base threshold) : ℕ) : ℝ)) := by
      dsimp [cutoff]
      congr 1
      ring

/--
Every affine sequence is eventually dominated by a geometric sequence of base
strictly greater than one.  The returned cutoff is uniform
over all offsets, which is the form needed to discharge a post-cutoff shell
allocation rather than merely prove an asymptotic statement.

Library provenance: this directly reuses Mathlib's
`tendsto_pow_atTop_atTop_of_one_lt` from
[`Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean)
and `one_add_mul_sub_le_pow` from the already linked pinned Apache-2.0
`Algebra/Order/Ring/Pow.lean` module. No external Lean source is copied or
ported.
-/
theorem exists_cutoff_affine_le_pow
    {a b r : ℝ} (hr : 1 < r) :
    ∃ cutoff : ℕ, ∀ offset : ℕ,
      a + b * (offset : ℝ) ≤ r ^ (cutoff + offset) := by
  let threshold : ℝ := max a (b / (r - 1))
  have hr_nonneg : 0 ≤ r := by linarith
  have hr_minus_one_pos : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_ge_atTop threshold)
  refine ⟨cutoff, fun offset => ?_⟩
  have hthreshold : threshold ≤ r ^ cutoff := hcutoff cutoff le_rfl
  have ha_cutoff : a ≤ r ^ cutoff :=
    (le_max_left _ _).trans hthreshold
  have hb_div_cutoff : b / (r - 1) ≤ r ^ cutoff :=
    (le_max_right _ _).trans hthreshold
  have hb_cutoff : b ≤ r ^ cutoff * (r - 1) :=
    (div_le_iff₀ hr_minus_one_pos).mp hb_div_cutoff
  have hscaled := mul_le_mul_of_nonneg_right hb_cutoff (Nat.cast_nonneg offset)
  have hpre : a + b * (offset : ℝ) ≤
      r ^ cutoff * (1 + (offset : ℝ) * (r - 1)) := by
    nlinarith
  have hbernoulli : 1 + (offset : ℝ) * (r - 1) ≤ r ^ offset := by
    exact one_add_mul_sub_le_pow (by linarith) offset
  calc
    a + b * (offset : ℝ) ≤
        r ^ cutoff * (1 + (offset : ℝ) * (r - 1)) := hpre
    _ ≤ r ^ cutoff * r ^ offset :=
      mul_le_mul_of_nonneg_left hbernoulli (pow_nonneg hr_nonneg _)
    _ = r ^ (cutoff + offset) := (pow_add _ _ _).symm

/--
An affine term evaluated at the post-cutoff index is dominated by the square
of any geometric base greater than one.  This converts the preceding generic
eventual bound into the shifted form used by shell cutoff arguments.
-/
theorem exists_cutoff_affine_cutoff_add_le_sq_pow
    {a b s : ℝ} (hs : 1 < s) :
    ∃ cutoff : ℕ, ∀ offset : ℕ,
      a + b * ((cutoff + offset : ℕ) : ℝ) ≤
        (s ^ 2) ^ (cutoff + offset) := by
  obtain ⟨halfCutoff, hhalfCutoff⟩ := exists_cutoff_affine_le_pow (a := a)
    (b := b) hs
  refine ⟨2 * halfCutoff, fun offset => ?_⟩
  have hsource := hhalfCutoff (2 * halfCutoff + offset)
  have hindex : halfCutoff + (2 * halfCutoff + offset) ≤
      2 * (2 * halfCutoff + offset) := by omega
  have hpow : s ^ (halfCutoff + (2 * halfCutoff + offset)) ≤
      s ^ (2 * (2 * halfCutoff + offset)) :=
    pow_le_pow_right₀ (by linarith) hindex
  calc
    a + b * (((2 * halfCutoff + offset : ℕ) : ℝ)) ≤
        s ^ (halfCutoff + (2 * halfCutoff + offset)) := hsource
    _ ≤ s ^ (2 * (2 * halfCutoff + offset)) := hpow
    _ = (s ^ 2) ^ (2 * halfCutoff + offset) := by rw [pow_mul]

/--
An explicit summable envelope for exponential tails at every geometric base
strictly larger than one.  The positive lower rate `y₀` yields a constant
geometric ratio independent of `y ≥ y₀`.
-/
theorem tsum_exp_neg_mul_pow_le_exp_neg_div_one_sub_exp_neg
    {y y₀ r : ℝ} (hy₀ : 0 < y₀) (hy : y₀ ≤ y) (hr : 1 < r) :
    ∑' n : ℕ, Real.exp (-y * r ^ n) ≤
      Real.exp (-y) / (1 - Real.exp (-(y₀ * (r - 1)))) := by
  let q : ℝ := Real.exp (-(y₀ * (r - 1)))
  have hy_nonneg : 0 ≤ y := hy₀.le.trans hy
  have hr_minus_one_pos : 0 < r - 1 := sub_pos.mpr hr
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (mul_pos hy₀ hr_minus_one_pos)
  have hratio : Real.exp (-(y * (r - 1))) ≤ q := by
    apply Real.exp_le_exp.mpr
    dsimp [q]
    have hscaled := mul_le_mul_of_nonneg_right hy hr_minus_one_pos.le
    linarith
  have hright : Summable (fun n : ℕ => Real.exp (-y) * q ^ n) := by
    have hgeom : Summable (fun n : ℕ => q ^ n) := by
      apply summable_geometric_of_norm_lt_one
      simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt_one
    exact hgeom.mul_left _
  have hleft : Summable (fun n : ℕ => Real.exp (-y * r ^ n)) := by
    apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _ hright
    intro n
    calc
      Real.exp (-y * r ^ n) ≤
          Real.exp (-y) * Real.exp (-(y * (r - 1))) ^ n :=
        exp_neg_mul_pow_le_exp_neg_mul_geometric hy_nonneg hr n
      _ ≤ Real.exp (-y) * q ^ n := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.exp_pos _).le hratio n) (Real.exp_pos _).le
  calc
    ∑' n : ℕ, Real.exp (-y * r ^ n) ≤
        ∑' n : ℕ, Real.exp (-y) * q ^ n :=
      Summable.tsum_le_tsum (fun n => by
        calc
          Real.exp (-y * r ^ n) ≤
              Real.exp (-y) * Real.exp (-(y * (r - 1))) ^ n :=
            exp_neg_mul_pow_le_exp_neg_mul_geometric hy_nonneg hr n
          _ ≤ Real.exp (-y) * q ^ n := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Real.exp_pos _).le hratio n) (Real.exp_pos _).le) hleft hright
    _ = Real.exp (-y) / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
      · ring
      · simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt_one
    _ = Real.exp (-y) / (1 - Real.exp (-(y₀ * (r - 1)))) := by rfl

/--
Taking logs of an exponential upper tail gives a stable lower bound for a
positive reciprocal mass.  This is the reusable algebraic form needed to turn
a shell-mass envelope into the logarithmic factor of a Bennett rate.

Library provenance: this directly reuses Mathlib's `Real.log_div`,
`Real.log_mul`, `Real.log_le_log`, and `Real.log_exp` from
[`Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic)),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem log_div_mul_lower_of_le_mul_exp_neg
    {numerator scale mass moment rate : ℝ}
    (hnumerator : 0 < numerator) (hscale : 0 < scale)
    (hmass : 0 < mass) (hmoment : 0 < moment)
    (hmass_le : mass ≤ moment * Real.exp (-rate)) :
    Real.log (numerator / (scale * mass)) ≥
      Real.log (numerator / scale) + rate - Real.log moment := by
  have hlog_mass : Real.log mass ≤ Real.log moment - rate := by
    calc
      Real.log mass ≤ Real.log (moment * Real.exp (-rate)) :=
        Real.log_le_log hmass hmass_le
      _ = Real.log moment - rate := by
        rw [Real.log_mul hmoment.ne' (Real.exp_ne_zero _), Real.log_exp]
        ring
  calc
    Real.log (numerator / (scale * mass)) =
        Real.log numerator - Real.log (scale * mass) :=
      Real.log_div hnumerator.ne' (mul_ne_zero hscale.ne' hmass.ne')
    _ = Real.log numerator - (Real.log scale + Real.log mass) := by
      rw [Real.log_mul hscale.ne' hmass.ne']
    _ = (Real.log numerator - Real.log scale) - Real.log mass := by ring
    _ = Real.log (numerator / scale) - Real.log mass := by
      rw [Real.log_div hnumerator.ne' hscale.ne']
    _ ≥ Real.log (numerator / scale) + rate - Real.log moment := by
      linarith


/-- Exponentiating half a logarithm gives the positive square root. -/
theorem exp_log_div_two_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le]
  exact Real.exp_log (Real.sqrt_pos.mpr hx)

/--
Union-bound exponential-tail arithmetic: if `log count < rate`, then a
uniform failure probability bounded by `exp (-rate)` has total mass below one
over `count` events.
-/
theorem mul_exp_neg_lt_one_of_log_lt
    {count rate : ℝ} (hcount : 0 < count)
    (hlog : Real.log count < rate) :
    count * Real.exp (-rate) < 1 := by
  have hsub : Real.log count - rate < 0 := by linarith
  have hexp : Real.exp (Real.log count - rate) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact hsub
  have hrewrite :
      count * Real.exp (-rate) = Real.exp (Real.log count - rate) := by
    rw [Real.exp_sub, Real.exp_log hcount, Real.exp_neg, div_eq_mul_inv]
  simpa [hrewrite] using hexp

/-- A logarithmic upper bound on a positive prefactor can be absorbed into an
exponential tail. -/
theorem mul_exp_neg_le_exp_neg_of_log_le
    {count rate penalty : ℝ} (hcount : 0 < count)
    (hlog : Real.log count ≤ penalty) :
    count * Real.exp (-rate) ≤ Real.exp (-(rate - penalty)) := by
  have hrewrite :
      count * Real.exp (-rate) = Real.exp (Real.log count - rate) := by
    rw [Real.exp_sub, Real.exp_log hcount, Real.exp_neg, div_eq_mul_inv]
  rw [hrewrite]
  apply Real.exp_le_exp.mpr
  linarith

/--
A finite-union exponential tail is at most `exp (-confidence)` whenever the
tail rate absorbs the logarithm of its positive prefactor.  This is the exact
tail-inversion step used by finite covering arguments.
-/
theorem finiteUnionExponentialTail_le_exp_neg_of_log_threshold
    {failure count rate confidence : ℝ}
    (htail : failure ≤ count * Real.exp (-rate))
    (hcount : 0 < count)
    (hthreshold : confidence + Real.log count ≤ rate) :
    failure ≤ Real.exp (-confidence) := by
  calc
    failure ≤ count * Real.exp (-rate) := htail
    _ ≤ Real.exp (-(rate - (rate - confidence))) :=
      mul_exp_neg_le_exp_neg_of_log_le hcount (by linarith)
    _ = Real.exp (-confidence) := by
      congr 1
      ring

/-- A positive exponential prefactor can be allocated a concrete logarithmic
threshold: `log (coefficient / tolerance) ≤ exponent` implies
`coefficient * exp (-exponent) ≤ tolerance`.

Library provenance: this directly reuses Mathlib's `Real.log_div`,
`Real.exp_sub`, `Real.exp_log`, and monotonicity of `Real.exp` from
[`Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html)),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
theorem mul_exp_neg_le_of_log_div_le
    {coefficient tolerance exponent : ℝ}
    (hcoefficient : 0 < coefficient) (htolerance : 0 < tolerance)
    (hlog : Real.log (coefficient / tolerance) ≤ exponent) :
    coefficient * Real.exp (-exponent) ≤ tolerance := by
  calc
    coefficient * Real.exp (-exponent) =
        Real.exp (Real.log coefficient - exponent) := by
      rw [Real.exp_sub, Real.exp_log hcoefficient, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (Real.log tolerance) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_div hcoefficient.ne' htolerance.ne'] at hlog
      linarith
    _ = tolerance := Real.exp_log htolerance

/-- An explicit nonnegative confidence level that spends at most half of a
positive failure budget on `exp (-confidence)`.  The maximum handles budgets
larger than two without imposing an unnecessary normalization.

Library provenance: this directly reuses Mathlib's `Real.log_lt_iff_lt_exp`,
`Real.exp_log`, and `Real.exp_neg` from
[`Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html)),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
noncomputable def expConfidenceForHalfBudget (budget : ℝ) : ℝ :=
  max 0 (Real.log (2 / budget))

/-- The explicit confidence selector is nonnegative. -/
theorem expConfidenceForHalfBudget_nonneg (budget : ℝ) :
    0 ≤ expConfidenceForHalfBudget budget := by
  unfold expConfidenceForHalfBudget
  exact le_max_left _ _

/-- The explicit confidence selector leaves at most one half of its positive
budget for the exponential confidence term. -/
theorem exp_neg_expConfidenceForHalfBudget_le_half
    {budget : ℝ} (hbudget : 0 < budget) :
    Real.exp (-expConfidenceForHalfBudget budget) ≤ budget / 2 := by
  unfold expConfidenceForHalfBudget
  have hratio : 0 < 2 / budget := div_pos (by norm_num) hbudget
  by_cases hlog : 0 ≤ Real.log (2 / budget)
  · rw [max_eq_right hlog, Real.exp_neg, Real.exp_log hratio]
    field_simp [hbudget.ne']
    norm_num
  · have hlogneg : Real.log (2 / budget) < 0 := lt_of_not_ge hlog
    have hratio_lt_one : 2 / budget < 1 := by
      have hbound := (Real.log_lt_iff_lt_exp hratio).mp hlogneg
      simpa using hbound
    have hbudget_two : 2 < budget := (div_lt_one₀ hbudget).mp (by simpa using hratio_lt_one)
    rw [max_eq_left hlogneg.le]
    simp
    linarith

/--
For `0 ≤ x < 1`, the logarithmic penalty from `1 - x^2` is no larger than
the penalty from `1 - x`.
-/
theorem neg_log_one_sub_sq_le_neg_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x ^ 2) ≤ -Real.log (1 - x) := by
  have hx_sq_le : x ^ 2 ≤ x := by
    nlinarith [mul_self_le_mul_self hx0 hx1.le]
  have harg_left_pos : 0 < 1 - x := by linarith
  have harg_right_pos : 0 < 1 - x ^ 2 := by
    have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0).mpr hx1
    linarith
  have harg_le : 1 - x ≤ 1 - x ^ 2 := by linarith
  have hlog_le :
      Real.log (1 - x) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log harg_left_pos harg_le
  linarith

/-- For `0 ≤ x < 1`, `x ≤ -log (1 - x)`. -/
theorem le_neg_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/-- For `0 ≤ x < 1`, `-log (1 - x) ≤ x / (1 - x)`. -/
theorem neg_log_one_sub_le_div_self
    {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hsub : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [ne_of_gt hpos]
    ring
  simpa [hsub] using hlog

/-- The map `x ↦ -log (1 - x)` is monotone on `(-∞, 1)`. -/
theorem neg_log_one_sub_mono
    {x y : ℝ} (hxy : x ≤ y) (hy1 : y < 1) :
    -Real.log (1 - x) ≤ -Real.log (1 - y) := by
  have hy_pos : 0 < 1 - y := by linarith
  have harg_le : 1 - y ≤ 1 - x := by linarith
  have hlog_le :
      Real.log (1 - y) ≤ Real.log (1 - x) :=
    Real.log_le_log hy_pos harg_le
  linarith

/--
The map `x ↦ -log (1 - x^2)` is monotone on `[0, 1)`.
-/
theorem neg_log_one_sub_sq_mono
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    -Real.log (1 - x ^ 2) ≤ -Real.log (1 - y ^ 2) := by
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0).mpr hx1
  have hy_sq_lt : y ^ 2 < 1 := (sq_lt_one_iff₀ hy0).mpr hy1
  have hsq_le : x ^ 2 ≤ y ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self hx0 hxy
  have harg_pos : 0 < 1 - y ^ 2 := by linarith
  have harg_le : 1 - y ^ 2 ≤ 1 - x ^ 2 := by linarith
  have hlog_le :
      Real.log (1 - y ^ 2) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log harg_pos harg_le
  linarith

/-- For `0 < x < 1`, the squared endpoint logarithmic penalty is positive. -/
theorem neg_log_one_sub_sq_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < -Real.log (1 - x ^ 2) := by
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_ne_zero (ne_of_gt hx0)
  have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0.le).mpr hx1
  have harg_pos : 0 < 1 - x ^ 2 := by linarith
  have harg_lt_one : 1 - x ^ 2 < 1 := by linarith
  have hlog_neg : Real.log (1 - x ^ 2) < 0 :=
    Real.log_neg harg_pos harg_lt_one
  linarith

/--
For any real denominator at least two, the elementary logarithmic estimate
`log(1 - 1/x) >= -2/x` gives `exp(-2/x) <= 1 - 1/x`.
-/
theorem exp_neg_two_div_le_one_sub_inv_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 / x)) ≤ 1 - 1 / x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxm1_pos : 0 < x - 1 := by linarith
  have hy_pos : 0 < 1 - 1 / x := by
    rw [sub_pos]
    rw [div_lt_one hx_pos]
    linarith
  have hrepr :
      1 - 1 / x = (1 + 1 / (x - 1))⁻¹ := by
    field_simp [ne_of_gt hx_pos, ne_of_gt hxm1_pos]
    ring
  have hlog_upper :
      Real.log (1 + 1 / (x - 1)) ≤ 2 / x := by
    have harg_pos : 0 < 1 + 1 / (x - 1) := by positivity
    have hlog_le :
        Real.log (1 + 1 / (x - 1)) ≤
          (1 + 1 / (x - 1)) - 1 :=
      Real.log_le_sub_one_of_pos harg_pos
    have hfrac : 1 / (x - 1) ≤ 2 / x := by
      rw [div_le_div_iff₀ hxm1_pos hx_pos]
      nlinarith
    linarith
  have hlog_lower :
      -(2 / x) ≤ Real.log (1 - 1 / x) := by
    rw [hrepr, Real.log_inv]
    exact neg_le_neg hlog_upper
  exact (Real.le_log_iff_exp_le hy_pos).mp hlog_lower

/--
Finite-power form of `exp_neg_two_div_le_one_sub_inv_of_two_le`: if `x >= 2`,
then `exp(-(2N/x)) <= (1 - 1/x)^N`.
-/
theorem exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le
    (N : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 * (N : ℝ) / x)) ≤ (1 - 1 / x) ^ N := by
  have hbase := exp_neg_two_div_le_one_sub_inv_of_two_le (x := x) hx
  have hpow :
      (Real.exp (-(2 / x))) ^ N ≤ (1 - 1 / x) ^ N :=
    pow_le_pow_left₀ (Real.exp_pos _).le hbase N
  have hleft :
      Real.exp (-(2 * (N : ℝ) / x)) =
        (Real.exp (-(2 / x))) ^ N := by
    calc
      Real.exp (-(2 * (N : ℝ) / x)) =
          Real.exp ((N : ℝ) * (-(2 / x))) := by
            congr 1
            ring
      _ = (Real.exp (-(2 / x))) ^ N :=
          Real.exp_nat_mul (-(2 / x)) N
  simpa [hleft] using hpow

/--
If a finite set has cardinality at most `C`, then the product of the constant
factor `exp (-A/C)` over that set is at least `exp (-A)` for `A ≥ 0`.

This is the deterministic exponential floor behind product-ratio bounds such
as `∏ exp (-2 ε σ / C) ≥ exp (-2 ε σ)`.
-/
theorem exp_neg_le_finset_prod_const_exp_neg_div_of_card_le
    {α : Type*} (s : Finset α) {A C : ℝ}
    (hA_nonneg : 0 ≤ A) (hC_pos : 0 < C)
    (hcard : (s.card : ℝ) ≤ C) :
    Real.exp (-A) ≤ ∏ _i ∈ s, Real.exp (-(A / C)) := by
  rw [Finset.prod_const]
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hcard_div_le_one : (s.card : ℝ) / C ≤ 1 := by
    rw [div_le_one hC_pos]
    exact hcard
  have harg :
      -A ≤ (s.card : ℝ) * (-(A / C)) := by
    have hmul : A * ((s.card : ℝ) / C) ≤ A * 1 :=
      mul_le_mul_of_nonneg_left hcard_div_le_one hA_nonneg
    have hrewrite :
        (s.card : ℝ) * (A / C) = A * ((s.card : ℝ) / C) := by
      ring
    have hle : (s.card : ℝ) * (A / C) ≤ A := by
      simpa [hrewrite] using hmul
    linarith
  simpa [neg_div, mul_neg] using harg

/--
Small-probability exponential floor for ratios of failure probabilities.

If `q` is at most `sigma / C` and at most one half, then the paper-style
failure ratio `(1 - q) / (1 - (1 - epsilon) q)` is bounded below by
`exp (-2 epsilon sigma / C)`.
-/
theorem exp_neg_two_mul_mul_div_le_one_sub_div_one_sub_one_sub_mul
    {epsilon sigma C q : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma) (hC_pos : 0 < C)
    (hq_nonneg : 0 ≤ q) (hq_le_half : q ≤ 1 / 2)
    (hq_le : q ≤ sigma / C) :
    Real.exp (-(2 * epsilon * sigma / C)) ≤
      (1 - q) / (1 - (1 - epsilon) * q) := by
  let den : ℝ := 1 - (1 - epsilon) * q
  let x : ℝ := epsilon * q / den
  have hq_lt_one : q < 1 := by linarith
  have hone_sub_q_pos : 0 < 1 - q := by linarith
  have hden_pos : 0 < den := by
    dsimp [den]
    have hmul_le : (1 - epsilon) * q ≤ q := by
      have hone_sub_nonneg : 0 ≤ 1 - epsilon := by linarith
      have hone_sub_le_one : 1 - epsilon ≤ 1 := by linarith
      nlinarith
    linarith
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg hepsilon_nonneg hq_nonneg) hden_pos.le
  have hx_lt_one : x < 1 := by
    dsimp [x]
    rw [div_lt_one hden_pos]
    dsimp [den]
    linarith
  have hone_sub_x_eq :
      1 - x = (1 - q) / den := by
    dsimp [x]
    calc
      1 - epsilon * q / den = (den - epsilon * q) / den := by
        field_simp [ne_of_gt hden_pos]
      _ = (1 - q) / den := by
        have hnum : den - epsilon * q = 1 - q := by
          dsimp [den]
          ring
        rw [hnum]
  have hx_div_eq :
      x / (1 - x) = epsilon * q / (1 - q) := by
    dsimp [x]
    rw [hone_sub_x_eq]
    field_simp [ne_of_gt hden_pos, ne_of_gt hone_sub_q_pos]
  have hq_div_le : q / (1 - q) ≤ 2 * q := by
    have hden_half : 1 / 2 ≤ 1 - q := by linarith
    have hden_pos' : 0 < 1 - q := hone_sub_q_pos
    have hle_inv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
      rw [inv_le_comm₀ hden_pos' (by norm_num : (0 : ℝ) < 2)]
      norm_num
      linarith
    have hmul := mul_le_mul_of_nonneg_left hle_inv hq_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hx_div_le : x / (1 - x) ≤ 2 * epsilon * sigma / C := by
    rw [hx_div_eq]
    have h1 : epsilon * (q / (1 - q)) ≤ epsilon * (2 * q) :=
      mul_le_mul_of_nonneg_left hq_div_le hepsilon_nonneg
    have h2 : epsilon * (2 * q) ≤ epsilon * (2 * (sigma / C)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hq_le (by norm_num : (0 : ℝ) ≤ 2))
        hepsilon_nonneg
    have halg1 : epsilon * q / (1 - q) =
        epsilon * (q / (1 - q)) := by ring
    have halg2 : epsilon * (2 * (sigma / C)) =
        2 * epsilon * sigma / C := by ring
    simpa [halg1, halg2] using le_trans h1 h2
  have hneglog :
      -Real.log (1 - x) ≤ 2 * epsilon * sigma / C :=
    (neg_log_one_sub_le_div_self hx_nonneg hx_lt_one).trans hx_div_le
  have hlog_lower : -(2 * epsilon * sigma / C) ≤ Real.log (1 - x) := by
    linarith
  have hone_sub_x_pos : 0 < 1 - x := by linarith
  have hexp : Real.exp (-(2 * epsilon * sigma / C)) ≤ 1 - x :=
    (Real.le_log_iff_exp_le hone_sub_x_pos).mp hlog_lower
  simpa [hone_sub_x_eq, den] using hexp

/--
Elementary shifted-log bound used in bisection approximation arguments:
`log ((x + δ) / x) ≤ δ / x` for a positive base point and nonnegative shift.
-/
theorem log_add_div_self_le_div {x δ : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) :
    Real.log ((x + δ) / x) ≤ δ / x := by
  have hnum_pos : 0 < x + δ := by linarith
  have harg_pos : 0 < (x + δ) / x := div_pos hnum_pos hx
  have hlog :
      Real.log ((x + δ) / x) ≤ (x + δ) / x - 1 :=
    Real.log_le_sub_one_of_pos harg_pos
  have hsub : (x + δ) / x - 1 = δ / x := by
    field_simp [ne_of_gt hx]
    ring
  simpa [hsub] using hlog

/--
Scaled shifted-log bound for nonnegative coefficients.
-/
theorem mul_log_add_div_self_le_mul_div {g x δ : ℝ}
    (hg : 0 ≤ g) (hx : 0 < x) (hδ : 0 ≤ δ) :
    g * Real.log ((x + δ) / x) ≤ g * (δ / x) :=
  mul_le_mul_of_nonneg_left (log_add_div_self_le_div hx hδ) hg

/--
For a nonnegative shift, the multiplicative shifted-log loss
`log ((x + δ) / x)` is antitone in the positive base point.
-/
theorem log_add_div_self_le_log_add_div_self_of_le
    {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) :
    Real.log ((y + δ) / y) ≤ Real.log ((x + δ) / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have harg_y_pos : 0 < (y + δ) / y := by
    exact div_pos (by linarith) hy
  have hratio :
      (y + δ) / y ≤ (x + δ) / x := by
    have hdiv : δ / y ≤ δ / x :=
      div_le_div_of_nonneg_left hδ hx hxy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have hx_ne : x ≠ 0 := ne_of_gt hx
    rw [add_div, add_div, div_self hy_ne, div_self hx_ne]
    linarith
  exact Real.log_le_log harg_y_pos hratio

/--
For `t ∈ [1/2, 1]`, the endpoint refinement midpoint
`(1 + sqrt t) / 2` is at most the fifth root of `t`.

The proof is algebraic after setting `s = sqrt t`:
`32 s^2 - (1+s)^5 = (1-s)(s^4 + 6s^3 + 16s^2 - 6s - 1)`, and the last
factor is nonnegative for `s >= 1/2`.
-/
theorem one_add_sqrt_div_two_pow_five_le_self_of_half_le_of_le_one
    {t : ℝ} (hhalf : (1 / 2 : ℝ) ≤ t) (ht1 : t ≤ 1) :
    ((1 + Real.sqrt t) / 2) ^ 5 ≤ t := by
  have ht_nonneg : 0 ≤ t := by nlinarith
  let s : ℝ := Real.sqrt t
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg t
  have hs_sq : s ^ 2 = t := by
    dsimp [s]
    exact Real.sq_sqrt ht_nonneg
  have hs_le_one : s ≤ 1 := by
    have hs_sq_le : s ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa [hs_sq] using ht1
    exact le_of_sq_le_sq hs_sq_le (by norm_num)
  have hs_ge_half : (1 / 2 : ℝ) ≤ s := by
    have hsq : ((1 / 2 : ℝ) ^ 2) ≤ s ^ 2 := by
      rw [hs_sq]
      norm_num
      nlinarith
    have habs : |(1 / 2 : ℝ)| ≤ |s| := by
      exact (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg hs_nonneg] using habs
  have hmain_nonneg : 0 ≤ 16 * s ^ 2 - 6 * s - 1 := by
    have hleft : 0 ≤ 2 * s - 1 := by nlinarith
    have hright : 0 ≤ 8 * s + 1 := by nlinarith
    have hprod : 0 ≤ (2 * s - 1) * (8 * s + 1) :=
      mul_nonneg hleft hright
    have hprod_eq :
        (2 * s - 1) * (8 * s + 1) = 16 * s ^ 2 - 6 * s - 1 := by
      ring
    simpa [hprod_eq] using hprod
  have hs3_nonneg : 0 ≤ s ^ 3 := by positivity
  have hs4_nonneg : 0 ≤ s ^ 4 := by positivity
  have hfactor_nonneg :
      0 ≤ s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1 := by
    nlinarith
  have hgap_nonneg :
      0 ≤ 32 * s ^ 2 - (1 + s) ^ 5 := by
    have hone_minus_nonneg : 0 ≤ 1 - s := by linarith
    have hprod_nonneg :
        0 ≤ (1 - s) *
          (s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1) :=
      mul_nonneg hone_minus_nonneg hfactor_nonneg
    have hfactor :
        (1 - s) * (s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1) =
          32 * s ^ 2 - (1 + s) ^ 5 := by
      ring
    simpa [hfactor] using hprod_nonneg
  have hpow :
      ((1 + s) / 2) ^ 5 ≤ s ^ 2 := by
    rw [div_pow]
    norm_num
    nlinarith
  simpa [s, hs_sq] using hpow

/--
For `t ∈ [1/2, 1]`, replacing the endpoint `t` by `(1 + sqrt t) / 2`
loses at most a factor `5` in the negative logarithmic rate.
-/
theorem neg_log_one_add_sqrt_div_two_ge_one_fifth_neg_log
    {t : ℝ} (hhalf : (1 / 2 : ℝ) ≤ t) (ht1 : t ≤ 1) :
    (1 / 5 : ℝ) * (-Real.log t) ≤
      -Real.log ((1 + Real.sqrt t) / 2) := by
  have ht_pos : 0 < t := by nlinarith
  have hbase_pos : 0 < (1 + Real.sqrt t) / 2 := by
    positivity
  have hpow :=
    one_add_sqrt_div_two_pow_five_le_self_of_half_le_of_le_one
      (t := t) hhalf ht1
  have hlog :
      Real.log (((1 + Real.sqrt t) / 2) ^ 5) ≤ Real.log t :=
    Real.log_le_log (pow_pos hbase_pos 5) hpow
  rw [Real.log_pow] at hlog
  norm_num at hlog
  nlinarith

/--
For `x ∈ [0, 1]`, the survival increment `1 - exp (-x)` is bounded below by
`x / 2`.
-/
theorem half_mul_le_one_sub_exp_neg_of_mem_Icc
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  by_cases hx_zero : x = 0
  · subst x
    simp
  have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_zero)
  have hy : 2 ≤ 2 / x := by
    rw [le_div_iff₀ hx_pos]
    nlinarith
  have hbound :=
    exp_neg_two_div_le_one_sub_inv_of_two_le (x := 2 / x) hy
  have hrepr :
      Real.exp (-(2 / (2 / x))) = Real.exp (-x) := by
    congr 1
    field_simp [ne_of_gt hx_pos]
  have hrhs :
      1 - 1 / (2 / x) = 1 - x / 2 := by
    field_simp [ne_of_gt hx_pos]
  have hexp : Real.exp (-x) ≤ 1 - x / 2 := by
    simpa [hrepr, hrhs] using hbound
  linarith

/--
If `lower ≤ r` and `lower ∈ [0, 1]`, then a first-level endpoint of the form
`1 - exp (-r)` is at least `lower / 2`.
-/
theorem half_lower_le_one_sub_exp_neg_of_lower_le_rate
    {lower r : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_rate : lower ≤ r) :
    lower / 2 ≤ 1 - Real.exp (-r) := by
  have hlinear :=
    half_mul_le_one_sub_exp_neg_of_mem_Icc hlower0 hlower1
  have hexp_mono : Real.exp (-r) ≤ Real.exp (-lower) :=
    Real.exp_le_exp.mpr (by linarith)
  have htail : 1 - Real.exp (-lower) ≤ 1 - Real.exp (-r) := by
    linarith
  exact hlinear.trans htail

/--
Elementary algebra for approximation proofs: if
`delta = eps / (g * (A + B))`, then the two weighted error-budget terms add
exactly to `eps`.
-/
theorem mul_delta_split_budget_eq_of_delta_eq_div_mul_add
    {g A B eps delta : ℝ}
    (hg : g ≠ 0)
    (hsum : A + B ≠ 0)
    (hdelta : delta = eps / (g * (A + B))) :
    g * (delta * A) + g * (delta * B) = eps := by
  subst delta
  field_simp [hg, hsum]

/--
An exponential upper bound on a finite prefactor can be absorbed directly
into a negative exponential rate.  This is the numerical form used to turn a
finite shell head into a pure concentration exponential once its cutoff has
been bounded.
-/
theorem mul_exp_neg_le_exp_neg_sub_of_le_exp
    {prefactor allowance rate : ℝ}
    (hprefactor : prefactor ≤ Real.exp allowance) :
    prefactor * Real.exp (-rate) ≤ Real.exp (-(rate - allowance)) := by
  calc
    prefactor * Real.exp (-rate) ≤ Real.exp allowance * Real.exp (-rate) :=
      mul_le_mul_of_nonneg_right hprefactor (Real.exp_pos _).le
    _ = Real.exp (allowance + (-rate)) := (Real.exp_add _ _).symm
    _ = Real.exp (-(rate - allowance)) := by congr 1 <;> ring

/--
The explicit denominator in a growing-base exponential series is uniformly
bounded away from zero once the first rate times `base - 1` is at least one.
This turns a geometric-series tail into a constant multiple of its leading
exponential term.
-/
theorem exp_neg_div_one_sub_exp_neg_mul_le_exp_neg_div_one_sub_exp_neg_one
    {rate floor base : ℝ}
    (hfloor_le_rate : floor ≤ rate) (hbase : 1 < base)
    (hfloor_large : 1 ≤ floor * (base - 1)) :
    Real.exp (-rate) / (1 - Real.exp (-(rate * (base - 1)))) ≤
      Real.exp (-floor) / (1 - Real.exp (-1)) := by
  have hbase_nonneg : 0 ≤ base - 1 := sub_nonneg.mpr hbase.le
  have hrate_large : 1 ≤ rate * (base - 1) := by
    calc
      1 ≤ floor * (base - 1) := hfloor_large
      _ ≤ rate * (base - 1) :=
        mul_le_mul_of_nonneg_right hfloor_le_rate hbase_nonneg
  have hnumerator : Real.exp (-rate) ≤ Real.exp (-floor) :=
    Real.exp_le_exp.mpr (neg_le_neg hfloor_le_rate)
  have hdenominator : 1 - Real.exp (-1) ≤
      1 - Real.exp (-(rate * (base - 1))) := by
    have hexp : Real.exp (-(rate * (base - 1))) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have htarget_den_pos : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos]
    exact (Real.exp_lt_one_iff).mpr (by norm_num)
  exact div_le_div₀ (Real.exp_pos _).le hnumerator htarget_den_pos hdenominator

end Math
end AppliedModelingLib
