import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

/-!
# Coordinatewise powers over convex hulls

This module contains a finite-dimensional-free convex-hull transport lemma for
coordinatewise real powers.  It is useful when changing a power exponent in a
convexified image set: a companion point in the target hull dominates the
coordinatewise powered source-hull point.
-/

namespace AppliedModelingLib.Optimization

/-- A finite product commutes with a fixed real power on nonnegative factors. -/
theorem finset_prod_coordinatewise_rpow
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r := by
  exact Real.finset_prod_rpow s f hf r

/--
For nonnegative scalars, a bound on the sum of squares transports to a bound
on the sum of real powers with exponent in `[0, 2]`.  This is the two-term
power-mean comparison obtained by concavity of `t ↦ t^(r / 2)`.
-/
theorem two_rpow_sum_le_two_rpow_of_square_sum_le
    {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr_nonnegative : 0 ≤ r) (hr_le_two : r ≤ 2)
    (hsquares : a ^ 2 + b ^ 2 ≤ 2 * c ^ 2) :
    a ^ r + b ^ r ≤ 2 * c ^ r := by
  let q : ℝ := r / 2
  have hq_nonnegative : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    linarith
  have hconcave := Real.concaveOn_rpow hq_nonnegative hq_le_one
  have hmean := hconcave.2 (show a ^ 2 ∈ Set.Ici 0 by exact sq_nonneg a)
    (show b ^ 2 ∈ Set.Ici 0 by exact sq_nonneg b)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  change (1 / 2 : ℝ) * (a ^ 2) ^ q + (1 / 2 : ℝ) * (b ^ 2) ^ q ≤
    ((1 / 2 : ℝ) * a ^ 2 + (1 / 2 : ℝ) * b ^ 2) ^ q at hmean
  have hmean' : (a ^ 2) ^ q + (b ^ 2) ^ q ≤
      2 * ((a ^ 2 + b ^ 2) / 2) ^ q := by
    calc
      (a ^ 2) ^ q + (b ^ 2) ^ q =
          2 * ((1 / 2 : ℝ) * (a ^ 2) ^ q +
            (1 / 2 : ℝ) * (b ^ 2) ^ q) := by ring
      _ ≤ 2 * ((1 / 2 : ℝ) * a ^ 2 + (1 / 2 : ℝ) * b ^ 2) ^ q :=
        mul_le_mul_of_nonneg_left hmean (by norm_num)
      _ = 2 * ((a ^ 2 + b ^ 2) / 2) ^ q := by congr 2 <;> ring
  have hbase : (a ^ 2 + b ^ 2) / 2 ≤ c ^ 2 := by
    nlinarith
  have hpow : ((a ^ 2 + b ^ 2) / 2) ^ q ≤ (c ^ 2) ^ q := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hbase
    · exact hq_nonnegative
  calc
    a ^ r + b ^ r = (a ^ 2) ^ q + (b ^ 2) ^ q := by
      congr 1
      · calc
          a ^ r = a ^ ((2 : ℝ) * q) := by dsimp [q]; congr 1 <;> ring
          _ = (a ^ (2 : ℝ)) ^ q := Real.rpow_mul ha 2 q
          _ = (a ^ 2) ^ q := by rw [Real.rpow_two]
      · calc
          b ^ r = b ^ ((2 : ℝ) * q) := by dsimp [q]; congr 1 <;> ring
          _ = (b ^ (2 : ℝ)) ^ q := Real.rpow_mul hb 2 q
          _ = (b ^ 2) ^ q := by rw [Real.rpow_two]
    _ ≤ 2 * ((a ^ 2 + b ^ 2) / 2) ^ q := hmean'
    _ ≤ 2 * (c ^ 2) ^ q := by gcongr
    _ = 2 * c ^ r := by
      congr 1
      calc
        (c ^ 2) ^ q = (c ^ (2 : ℝ)) ^ q := by rw [Real.rpow_two]
        _ = c ^ ((2 : ℝ) * q) := (Real.rpow_mul hc 2 q).symm
        _ = c ^ r := by dsimp [q]; congr 1 <;> ring

/--
If every nonnegative point of `S` has a target-hull companion that dominates
its coordinatewise `r`-th power, the same is true for every point of the
convex hull of `S`, provided `r >= 1`.  Convexity of `x ↦ x^r` supplies the
only analytic ingredient.
-/
theorem exists_mem_convexHull_coordinatewise_rpow_le
    {ι : Type*} {S T : Set (ι → ℝ)} {r : ℝ}
    (hr : 1 ≤ r)
    (hS_nonnegative : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hbase : ∀ x ∈ S, ∃ y ∈ T, ∀ i, x i ^ r ≤ y i) :
    ∀ x ∈ convexHull ℝ S, ∃ y ∈ convexHull ℝ T, ∀ i, x i ^ r ≤ y i := by
  let Q : Set (ι → ℝ) := {x | (∀ i, 0 ≤ x i) ∧
    ∃ y ∈ convexHull ℝ T, ∀ i, x i ^ r ≤ y i}
  have hS_subset : S ⊆ Q := by
    intro x hx
    refine ⟨hS_nonnegative x hx, ?_⟩
    obtain ⟨y, hyT, hxy⟩ := hbase x hx
    exact ⟨y, subset_convexHull ℝ T hyT, hxy⟩
  have hQ_convex : Convex ℝ Q := by
    intro x hx z hz a b ha hb hab
    rcases hx with ⟨hx_nonnegative, y, hy, hxy⟩
    rcases hz with ⟨hz_nonnegative, w, hw, hzw⟩
    refine ⟨?_, ?_⟩
    · intro i
      change 0 ≤ a * x i + b * z i
      exact add_nonneg (mul_nonneg ha (hx_nonnegative i))
        (mul_nonneg hb (hz_nonnegative i))
    · refine ⟨a • y + b • w, (convex_convexHull ℝ T) hy hw ha hb hab, ?_⟩
      intro i
      change (a * x i + b * z i) ^ r ≤ a * y i + b * w i
      calc
        (a * x i + b * z i) ^ r ≤ a * (x i) ^ r + b * (z i) ^ r := by
          simpa [smul_eq_mul] using
            (convexOn_rpow hr).2 (hx_nonnegative i) (hz_nonnegative i) ha hb hab
        _ ≤ a * y i + b * w i :=
          add_le_add (mul_le_mul_of_nonneg_left (hxy i) ha)
            (mul_le_mul_of_nonneg_left (hzw i) hb)
  intro x hx
  exact ((convexHull_min hS_subset hQ_convex) hx).2

end AppliedModelingLib.Optimization
