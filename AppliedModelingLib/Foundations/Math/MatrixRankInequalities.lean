import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Matrix Rank Inequality Primitives

Small reusable matrix-rank and trace/Frobenius facts intended as infrastructure
for finite-dimensional rank lower-bound arguments, including future uses of
Alon's near-identity rank theorem.
-/

open Matrix
open scoped BigOperators

namespace AppliedModelingLib
namespace Math
namespace MatrixRankInequalities

universe u v w

section RankWrappers

variable {R : Type*} [CommRing R]
variable {m : Type u} {m₀ : Type v} {n : Type w} {n₀ : Type*}
variable [Fintype n] [Fintype n₀]

/-- A named wrapper around `Matrix.rank_submatrix_le` for later rank-bound arguments. -/
theorem rank_submatrix_le
    (A : Matrix m n R) (rows : m₀ → m) (cols : n₀ → n) :
    (A.submatrix rows cols).rank ≤ A.rank :=
  Matrix.rank_submatrix_le A rows cols

/-- Reindexing both rows and columns by equivalences preserves matrix rank. -/
theorem rank_submatrix_eq_of_equiv
    (A : Matrix m n R) (rows : m₀ ≃ m) (cols : n₀ ≃ n) :
    (A.submatrix rows cols).rank = A.rank :=
  Matrix.rank_submatrix A rows cols

end RankWrappers

section DiagonalScaling

variable {m : Type u} {n : Type v}

section RowScale

variable [Fintype m] [DecidableEq m]

/-- Left multiplication by a diagonal matrix, viewed as row scaling. -/
def rowScale {R : Type*} [NonUnitalNonAssocSemiring R]
    (d : m → R) (A : Matrix m n R) : Matrix m n R :=
  Matrix.diagonal d * A

@[simp]
theorem rowScale_apply {R : Type*} [NonUnitalNonAssocSemiring R]
    (d : m → R) (A : Matrix m n R) (i : m) (j : n) :
    rowScale d A i j = d i * A i j := by
  simp [rowScale, Matrix.diagonal_mul]

end RowScale

section ColScale

variable [Fintype n] [DecidableEq n]

/-- Right multiplication by a diagonal matrix, viewed as column scaling. -/
def colScale {R : Type*} [NonUnitalNonAssocSemiring R]
    (A : Matrix m n R) (d : n → R) : Matrix m n R :=
  A * Matrix.diagonal d

@[simp]
theorem colScale_apply {R : Type*} [NonUnitalNonAssocSemiring R]
    (A : Matrix m n R) (d : n → R) (i : m) (j : n) :
    colScale A d i j = A i j * d j := by
  simp [colScale, Matrix.mul_diagonal]

end ColScale

variable [Fintype m] [Fintype n] [DecidableEq m]

/-- Scaling rows by nonzero real factors preserves rank. -/
theorem rank_rowScale_eq_real
    (d : m → ℝ) (A : Matrix m n ℝ) (hd : ∀ i, d i ≠ 0) :
    (rowScale d A).rank = A.rank := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (by
      exact Finset.prod_ne_zero_iff.mpr fun i _hi => hd i)
  simpa [rowScale] using
    Matrix.rank_mul_eq_right_of_isUnit_det
      (A := Matrix.diagonal d) (B := A) hdet

variable [DecidableEq n]

omit [Fintype m] [DecidableEq m] in
/-- Scaling columns by nonzero real factors preserves rank. -/
theorem rank_colScale_eq_real
    (A : Matrix m n ℝ) (d : n → ℝ) (hd : ∀ j, d j ≠ 0) :
    (colScale A d).rank = A.rank := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (by
      exact Finset.prod_ne_zero_iff.mpr fun j _hj => hd j)
  simpa [colScale] using
    Matrix.rank_mul_eq_left_of_isUnit_det
      (A := Matrix.diagonal d) (B := A) hdet

end DiagonalScaling

section DiagonalNormalization

variable {ι : Type u}

/-- A positive lower bound on diagonal entries gives the nonzero hypothesis. -/
theorem diagonal_ne_zero_of_pos_le
    {A : Matrix ι ι ℝ} {gamma : ℝ}
    (hgamma : 0 < gamma) (hdiag : ∀ i, gamma ≤ A i i) :
    ∀ i, A i i ≠ 0 := by
  intro i
  exact (lt_of_lt_of_le hgamma (hdiag i)).ne'

variable [Fintype ι] [DecidableEq ι]

/-- Row-normalize a square real matrix by multiplying row `i` by `(A i i)⁻¹`. -/
noncomputable def normalizeRowsByDiagonal (A : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  rowScale (fun i => (A i i)⁻¹) A

@[simp]
theorem normalizeRowsByDiagonal_apply
    (A : Matrix ι ι ℝ) (i j : ι) :
    normalizeRowsByDiagonal A i j = (A i i)⁻¹ * A i j := by
  simp [normalizeRowsByDiagonal]

/-- Row normalization makes each nonzero diagonal entry equal to one. -/
theorem normalizeRowsByDiagonal_diag
    {A : Matrix ι ι ℝ} (hdiag : ∀ i, A i i ≠ 0) (i : ι) :
    normalizeRowsByDiagonal A i i = 1 := by
  simp [normalizeRowsByDiagonal, hdiag i]

/-- Row normalization by nonzero diagonal entries preserves rank. -/
theorem rank_normalizeRowsByDiagonal_eq
    {A : Matrix ι ι ℝ} (hdiag : ∀ i, A i i ≠ 0) :
    (normalizeRowsByDiagonal A).rank = A.rank :=
  rank_rowScale_eq_real (fun i => (A i i)⁻¹) A fun i => inv_ne_zero (hdiag i)

/--
If diagonal entries are at least `gamma > 0`, row normalization scales an
off-diagonal absolute bound `eta` to `eta / gamma`.
-/
theorem normalizeRowsByDiagonal_offdiag_abs_le
    {A : Matrix ι ι ℝ} {gamma eta : ℝ}
    (hgamma : 0 < gamma)
    (hdiag : ∀ i, gamma ≤ A i i)
    (hoff : ∀ ⦃i j : ι⦄, i ≠ j → |A i j| ≤ eta)
    {i j : ι} (hij : i ≠ j) :
    |normalizeRowsByDiagonal A i j| ≤ eta / gamma := by
  have hdiag_pos : 0 < A i i := lt_of_lt_of_le hgamma (hdiag i)
  have hdiag_abs : gamma ≤ |A i i| := by
    simpa [abs_of_pos hdiag_pos] using hdiag i
  have hinv_le : |(A i i)⁻¹| ≤ 1 / gamma := by
    have h := one_div_le_one_div_of_le hgamma hdiag_abs
    simpa [one_div, abs_inv] using h
  have hmul :
      |(A i i)⁻¹| * |A i j| ≤ (1 / gamma) * eta :=
    mul_le_mul hinv_le (hoff hij) (abs_nonneg _) (by positivity)
  calc
    |normalizeRowsByDiagonal A i j| = |(A i i)⁻¹ * A i j| := by
      simp [normalizeRowsByDiagonal]
    _ = |(A i i)⁻¹| * |A i j| := abs_mul _ _
    _ ≤ (1 / gamma) * eta := hmul
    _ = eta / gamma := by ring

end DiagonalNormalization

section RankCasts

variable {m : Type u} {n : Type v} [Fintype n]

/-- Matrix ranks are nonnegative when coerced to the reals. -/
theorem rank_cast_nonneg {R : Type*} [CommRing R] (A : Matrix m n R) :
    0 ≤ (A.rank : ℝ) := by
  exact_mod_cast Nat.zero_le A.rank

end RankCasts

section FactorizationRank

variable {row : Type u} {col : Type v} {coord : Type w}
variable [Fintype col] [Fintype coord]

/--
If a matrix factors through a finite middle coordinate type, its rank is at
most the size of that middle type.
-/
theorem rank_mul_le_middle_card
    (X : Matrix row coord ℝ) (Y : Matrix coord col ℝ) :
    (X * Y).rank ≤ Fintype.card coord :=
  (Matrix.rank_mul_le_left X Y).trans (Matrix.rank_le_card_width X)

/--
Rank bound for a matrix represented by finite feature dot products.
-/
theorem rank_le_middle_card_of_dot_factorization
    [Fintype row]
    (M : Matrix row col ℝ) (X : row → coord → ℝ) (Y : col → coord → ℝ)
    (hM : ∀ i j, M i j = ∑ r : coord, X i r * Y j r) :
    M.rank ≤ Fintype.card coord := by
  let Xmat : Matrix row coord ℝ := X
  let Ymat : Matrix coord col ℝ := fun r j => Y j r
  have hfactor : M = Xmat * Ymat := by
    ext i j
    simp [Xmat, Ymat, Matrix.mul_apply, hM i j]
  rw [hfactor]
  exact rank_mul_le_middle_card Xmat Ymat

end FactorizationRank

section SymmetricMonomials

variable {coord : Type w} [Fintype coord] [DecidableEq coord]

/--
Stars-and-bars count for the symmetric-power coordinate space that appears
after symmetrizing a `d`-dimensional dot-product factorization.
-/
theorem card_sym_sum_fin_eq_choose (d t : ℕ) :
    Fintype.card (Sym (Sum (Fin d) (Fin d)) t) =
      (2 * d + t - 1).choose t := by
  rw [Sym.card_sym_eq_choose]
  simp [Fintype.card_sum, two_mul, Nat.add_assoc]

/--
The stars-and-bars count for degree-`t` monomials in `2d` coordinates is
bounded by the factorial-normalized power envelope.  This is the sharp finite
count needed for polynomial-method rank arguments that retain logarithmic
factors.
-/
theorem choose_sum_fin_le_pow_div_factorial (d t : ℕ) :
    ((2 * d + t - 1).choose t : ℝ) ≤
      (((2 * d + t - 1) ^ t : ℕ) : ℝ) / (t.factorial : ℝ) := by
  simpa using
    (Nat.choose_le_pow_div (α := ℝ) t (2 * d + t - 1))

/--
Coarse Stirling lower bound in the form usually needed for finite
polynomial-method estimates: `p! >= (p/e)^p`.
-/
theorem factorial_ge_pow_div_exp_self {p : ℕ} (hp : 0 < p) :
    ((p : ℝ) / Real.exp 1) ^ p ≤ (p.factorial : ℝ) := by
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hrad_ge_one : 1 ≤ 2 * Real.pi * (p : ℝ) := by
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.two_le_pi]
    have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [hpi, hp_one]
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (p : ℝ)) :=
    Real.one_le_sqrt.mpr hrad_ge_one
  have hpow_nonneg : 0 ≤ ((p : ℝ) / Real.exp 1) ^ p := by positivity
  have hmul_le :
      ((p : ℝ) / Real.exp 1) ^ p ≤
        Real.sqrt (2 * Real.pi * (p : ℝ)) *
          ((p : ℝ) / Real.exp 1) ^ p :=
    le_mul_of_one_le_left hpow_nonneg hsqrt
  exact hmul_le.trans (Stirling.le_factorial_stirling p)

/--
The factorial-normalized power envelope is bounded by the simpler
source-scale expression `(e * N / p)^p`.
-/
theorem pow_div_factorial_le_exp_mul_div_pow
    {N p : ℕ} (hp : 0 < p) :
    ((((N ^ p : ℕ) : ℝ) / (p.factorial : ℝ))) ≤
      (Real.exp 1 * (N : ℝ) / (p : ℝ)) ^ p := by
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hfac_pos : 0 < (p.factorial : ℝ) := by positivity
  have hden_pos : 0 < ((p : ℝ) / Real.exp 1) ^ p := by
    exact pow_pos (div_pos hp_real_pos (Real.exp_pos 1)) _
  have hfac_ge := factorial_ge_pow_div_exp_self (p := p) hp
  have hleft :
      (((N ^ p : ℕ) : ℝ) / (p.factorial : ℝ)) ≤
        (((N ^ p : ℕ) : ℝ) / (((p : ℝ) / Real.exp 1) ^ p)) := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden_pos hfac_ge
  calc
    (((N ^ p : ℕ) : ℝ) / (p.factorial : ℝ))
        ≤ (((N ^ p : ℕ) : ℝ) / (((p : ℝ) / Real.exp 1) ^ p)) := hleft
    _ = (Real.exp 1 * (N : ℝ) / (p : ℝ)) ^ p := by
      have hp_pow_ne : (p : ℝ) ^ p ≠ 0 := pow_ne_zero _ hp_real_pos.ne'
      rw [Nat.cast_pow, div_pow]
      field_simp [hp_real_pos.ne', hp_pow_ne, (Real.exp_pos 1).ne']
      have hcancel : (p : ℝ) ^ p * (p : ℝ)⁻¹ ^ p = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hp_real_pos.ne', one_pow]
      rw [div_eq_mul_inv, mul_pow, mul_pow]
      calc
        (N : ℝ) ^ p * Real.exp 1 ^ p
            = ((p : ℝ) ^ p * (p : ℝ)⁻¹ ^ p) *
                (Real.exp 1 ^ p * (N : ℝ) ^ p) := by
              rw [hcancel]
              ring
        _ = (p : ℝ) ^ p *
              ((Real.exp 1 ^ p * (N : ℝ) ^ p) * (p : ℝ)⁻¹ ^ p) := by
              ring

/--
Standard binomial envelope from the factorial bound:
`choose N p <= (e N / p)^p`.
-/
theorem choose_le_exp_mul_div_pow
    {N p : ℕ} (hp : 0 < p) :
    ((Nat.choose N p : ℕ) : ℝ) ≤
      (Real.exp 1 * (N : ℝ) / (p : ℝ)) ^ p := by
  have hchoose :
      ((Nat.choose N p : ℕ) : ℝ) ≤
        (((N ^ p : ℕ) : ℝ) / (p.factorial : ℝ)) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) p N)
  exact hchoose.trans (pow_div_factorial_le_exp_mul_div_pow (N := N) hp)

/--
Logarithmic form of the standard binomial envelope, for the nonzero range
`0 < p <= N`.
-/
theorem log_choose_le_mul_log_exp_mul_div
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    Real.log ((Nat.choose N p : ℕ) : ℝ) ≤
      (p : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / (p : ℝ)) := by
  have hchoose_pos :
      0 < ((Nat.choose N p : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hpN
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hp hpN)
  have hp_real_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp
  have hbase_pos : 0 < Real.exp 1 * (N : ℝ) / (p : ℝ) := by
    positivity
  have hle := choose_le_exp_mul_div_pow (N := N) hp
  have hlog :=
    Real.log_le_log hchoose_pos hle
  rw [Real.log_pow] at hlog
  simpa [Nat.cast_mul] using hlog

/--
Logarithmic envelope for the small-support union-count bound
`(p+1) * choose N p`.
-/
theorem log_succ_mul_choose_le_log_succ_add_mul_log_exp_mul_div
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    Real.log ((((p + 1) * Nat.choose N p : ℕ) : ℝ)) ≤
      Real.log (((p + 1 : ℕ) : ℝ)) +
        (p : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / (p : ℝ)) := by
  have hfactor_ne : (((p + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hchoose_ne : ((Nat.choose N p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hpN).ne'
  have hchoose_log :=
    log_choose_le_mul_log_exp_mul_div (N := N) (p := p) hp hpN
  rw [Nat.cast_mul, Real.log_mul hfactor_ne hchoose_ne]
  linarith

/--
Strict two-sided version of `pow_div_factorial_le_exp_mul_div_pow`, convenient
when the target argument already carries the leading factor `2`.
-/
theorem two_mul_pow_div_factorial_lt_of_two_mul_exp_mul_div_pow_lt
    {N p : ℕ} {s : ℝ} (hp : 0 < p)
    (hpow : 2 * (Real.exp 1 * (N : ℝ) / (p : ℝ)) ^ p < s) :
    2 * ((((N ^ p : ℕ) : ℝ) / (p.factorial : ℝ))) < s := by
  have hle := pow_div_factorial_le_exp_mul_div_pow (N := N) hp
  nlinarith

/--
Sufficient factorial-normalized power envelope for the symmetric-power
coordinate count.
-/
theorem two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt
    {d t : ℕ} {s : ℝ}
    (hpow :
      2 * ((((2 * d + t - 1) ^ t : ℕ) : ℝ) / (t.factorial : ℝ)) < s) :
    2 * ((2 * d + t - 1).choose t : ℝ) < s := by
  have hchoose := choose_sum_fin_le_pow_div_factorial d t
  nlinarith

/--
Source-scale sufficient envelope for the symmetric-power stars-and-bars count:
Stirling turns `(2d+t-1)^t/t!` into `(e(2d+t-1)/t)^t`.
-/
theorem two_mul_choose_sum_fin_lt_of_two_mul_exp_mul_div_pow_lt
    {d t : ℕ} {s : ℝ} (ht : 0 < t)
    (hpow : 2 * (Real.exp 1 * ((2 * d + t - 1 : ℕ) : ℝ) / (t : ℝ)) ^ t < s) :
    2 * ((2 * d + t - 1).choose t : ℝ) < s := by
  exact
    two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt
      (d := d) (t := t)
      (two_mul_pow_div_factorial_lt_of_two_mul_exp_mul_div_pow_lt
        (N := 2 * d + t - 1) ht hpow)

/--
Version of
`two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt` stated directly
for the symmetric-power coordinate type.
-/
theorem two_mul_card_sym_sum_fin_lt_of_two_mul_pow_div_factorial_lt
    {d t : ℕ} {s : ℝ}
    (hpow :
      2 * ((((2 * d + t - 1) ^ t : ℕ) : ℝ) / (t.factorial : ℝ)) < s) :
    2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) t) : ℝ) < s := by
  simpa [card_sym_sum_fin_eq_choose] using
    two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt (d := d) (t := t) hpow

/--
Version of `two_mul_choose_sum_fin_lt_of_two_mul_exp_mul_div_pow_lt` stated
directly for the symmetric-power coordinate type.
-/
theorem two_mul_card_sym_sum_fin_lt_of_two_mul_exp_mul_div_pow_lt
    {d t : ℕ} {s : ℝ} (ht : 0 < t)
    (hpow : 2 * (Real.exp 1 * ((2 * d + t - 1 : ℕ) : ℝ) / (t : ℝ)) ^ t < s) :
    2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) t) : ℝ) < s := by
  simpa [card_sym_sum_fin_eq_choose] using
    two_mul_choose_sum_fin_lt_of_two_mul_exp_mul_div_pow_lt
      (d := d) (t := t) ht hpow

/--
The stars-and-bars count for degree-`t` monomials in `2d` coordinates is
bounded by the simpler power envelope `(2d+t)^t`, in the form used by
polynomial-method rank arguments.
-/
theorem two_mul_choose_sum_fin_lt_of_two_mul_pow_lt
    {d t : ℕ} {s : ℝ}
    (hpow : 2 * (((2 * d + t) ^ t : ℕ) : ℝ) < s) :
    2 * ((2 * d + t - 1).choose t : ℝ) < s := by
  have hchoose_nat :
      (2 * d + t - 1).choose t ≤ (2 * d + t) ^ t := by
    calc
      (2 * d + t - 1).choose t ≤ (2 * d + t - 1) ^ t :=
        Nat.choose_le_pow _ _
      _ ≤ (2 * d + t) ^ t :=
        Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hchoose_real :
      ((2 * d + t - 1).choose t : ℝ) ≤
        (((2 * d + t) ^ t : ℕ) : ℝ) := by
    exact_mod_cast hchoose_nat
  nlinarith

/--
Version of `two_mul_choose_sum_fin_lt_of_two_mul_pow_lt` stated directly for
the symmetric-power coordinate type.
-/
theorem two_mul_card_sym_sum_fin_lt_of_two_mul_pow_lt
    {d t : ℕ} {s : ℝ}
    (hpow : 2 * (((2 * d + t) ^ t : ℕ) : ℝ) < s) :
    2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) t) : ℝ) < s := by
  simpa [card_sym_sum_fin_eq_choose] using
    two_mul_choose_sum_fin_lt_of_two_mul_pow_lt (d := d) (t := t) hpow

/-- The unordered tuple underlying an ordered `t`-tuple. -/
noncomputable def tupleSym (t : ℕ) (p : Fin t → coord) : Sym coord t :=
  Sym.ofVector ⟨List.ofFn p, by simp⟩

/-- The monomial associated to an unordered tuple. -/
noncomputable def symMonomial {t : ℕ} (x : coord → ℝ) (s : Sym coord t) : ℝ :=
  ((s : Multiset coord).map x).prod

/--
The multinomial coefficient of an unordered tuple, defined as the number of
ordered tuples that realize it.
-/
noncomputable def symPowerCoeff {t : ℕ} (s : Sym coord t) : ℝ :=
  (((Finset.univ : Finset (Fin t → coord)).filter
      (fun p => tupleSym t p = s)).card : ℝ)

omit [Fintype coord] [DecidableEq coord] in
theorem tuple_prod_eq_symMonomial_mul
    (x y : coord → ℝ) {t : ℕ} (p : Fin t → coord) :
    (∏ i, x (p i) * y (p i)) =
      symMonomial x (tupleSym t p) * symMonomial y (tupleSym t p) := by
  rw [← (List.prod_ofFn (f := fun i : Fin t => x (p i) * y (p i)))]
  dsimp [symMonomial, tupleSym, Sym.ofVector]
  rw [List.ofFn_comp' p (fun a => x a * y a)]
  exact List.prod_map_mul

/--
Regroup the ordered tuple expansion of a dot-product power by unordered
tuples.  The fiber cardinal is the multinomial coefficient.
-/
theorem dot_pow_eq_sum_symPowerCoeff_monomial
    (x y : coord → ℝ) (t : ℕ) :
    (∑ r, x r * y r) ^ t =
      ∑ s : Sym coord t,
        symPowerCoeff s * symMonomial x s * symMonomial y s := by
  classical
  rw [Fintype.sum_pow (fun r : coord => x r * y r) t]
  have hprod :
      (∑ p : Fin t → coord, ∏ i, x (p i) * y (p i)) =
        ∑ p : Fin t → coord,
          symMonomial x (tupleSym t p) * symMonomial y (tupleSym t p) := by
    exact Finset.sum_congr rfl fun p _ =>
      tuple_prod_eq_symMonomial_mul x y p
  rw [hprod]
  let f : (Fin t → coord) → ℝ :=
    fun p => symMonomial x (tupleSym t p) * symMonomial y (tupleSym t p)
  have hfiberwise :
      (∑ s : Sym coord t,
          ∑ p ∈ (Finset.univ : Finset (Fin t → coord)) with tupleSym t p = s,
            f p) =
        ∑ p : Fin t → coord, f p := by
    simpa [f] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin t → coord)))
        (t := (Finset.univ : Finset (Sym coord t)))
        (g := fun p => tupleSym t p)
        (by intro p hp; simp)
        (f := f))
  rw [← hfiberwise]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  unfold f symPowerCoeff
  have hconst :
      (∑ p ∈ (Finset.univ : Finset (Fin t → coord)) with tupleSym t p = s,
          symMonomial x (tupleSym t p) * symMonomial y (tupleSym t p)) =
        ∑ p ∈ (Finset.univ : Finset (Fin t → coord)) with tupleSym t p = s,
          symMonomial x s * symMonomial y s := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : tupleSym t p = s := (Finset.mem_filter.mp hp).2
    simp [hp']
  rw [hconst]
  simp [mul_assoc]

/-- Entrywise natural powers of a dot-product matrix have symmetric-monomial rank. -/
theorem rank_entrywisePow_le_card_sym_of_dot_factorization
    {row : Type u} {col : Type v}
    [Fintype row] [Fintype col]
    (M : Matrix row col ℝ) (X : row → coord → ℝ) (Y : col → coord → ℝ)
    (hM : ∀ i j, M i j = ∑ r : coord, X i r * Y j r)
    (t : ℕ) :
    (Matrix.of fun i j => (M i j) ^ t).rank ≤ Fintype.card (Sym coord t) := by
  classical
  refine
    rank_le_middle_card_of_dot_factorization
      (coord := Sym coord t)
      (M := Matrix.of fun i j => (M i j) ^ t)
      (X := fun i s => symPowerCoeff s * symMonomial (X i) s)
      (Y := fun j s => symMonomial (Y j) s) ?_
  intro i j
  change (M i j) ^ t =
    ∑ s : Sym coord t,
      (symPowerCoeff s * symMonomial (X i) s) * symMonomial (Y j) s
  rw [hM i j]
  simpa [mul_assoc] using
    dot_pow_eq_sum_symPowerCoeff_monomial (X i) (Y j) t

end SymmetricMonomials

section FrobeniusTrace

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]

/-- Squared Frobenius norm of a finite real matrix, as an elementary finite sum. -/
noncomputable def frobeniusSq (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

theorem frobeniusSq_nonneg (A : Matrix m n ℝ) :
    0 ≤ frobeniusSq A := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj => sq_nonneg (A i j)

/-- `trace (Aᵀ * A)` is the squared Frobenius sum of entries. -/
theorem trace_transpose_mul_self_eq_frobeniusSq
    (A : Matrix m n ℝ) :
    Matrix.trace (Aᵀ * A) = frobeniusSq A := by
  unfold frobeniusSq Matrix.trace Matrix.diag
  simp [Matrix.mul_apply, pow_two]
  rw [Finset.sum_comm]

/-- Elementary nonnegativity of `trace (Aᵀ * A)` over real matrices. -/
theorem trace_transpose_mul_self_nonneg (A : Matrix m n ℝ) :
    0 ≤ Matrix.trace (Aᵀ * A) := by
  rw [trace_transpose_mul_self_eq_frobeniusSq]
  exact frobeniusSq_nonneg A

end FrobeniusTrace

section FiniteSupportSums

variable {ι : Type u} [Fintype ι]

/--
Finite Cauchy-Schwarz with the support size: the square of a finite real sum is
bounded by the number of nonzero summands times the sum of squares.
-/
theorem sq_sum_le_support_card_mul_sum_sq (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤
      (Fintype.card {i : ι // f i ≠ 0} : ℝ) * ∑ i, f i ^ 2 := by
  classical
  let s : Finset ι := (Finset.univ : Finset ι).filter fun i => f i ≠ 0
  have hsum :
      (∑ i ∈ s, f i) = ∑ i : ι, f i := by
    rw [show s = (Finset.univ : Finset ι).filter (fun i => f i ≠ 0) by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    by_cases hi : f i ≠ 0
    · simp [hi]
    · simp [not_not.mp hi]
  have hsq_le :
      (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := s) (f := f))
  have hcard :
      (s.card : ℝ) = (Fintype.card {i : ι // f i ≠ 0} : ℝ) := by
    have hcard_nat : s.card = Fintype.card {i : ι // f i ≠ 0} := by
      rw [Fintype.card_subtype]
    exact_mod_cast hcard_nat
  have hsum_sq_le :
      ∑ i ∈ s, f i ^ 2 ≤ ∑ i : ι, f i ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; exact Finset.mem_univ i)
      (by intro i _huniv his; exact sq_nonneg (f i))
  calc
    (∑ i : ι, f i) ^ 2 = (∑ i ∈ s, f i) ^ 2 := by rw [← hsum]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := hsq_le
    _ ≤ (s.card : ℝ) * ∑ i : ι, f i ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsum_sq_le (Nat.cast_nonneg s.card)
    _ = (Fintype.card {i : ι // f i ≠ 0} : ℝ) * ∑ i : ι, f i ^ 2 := by
      rw [hcard]

end FiniteSupportSums

section HermitianTraceRank

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
Spectral trace/rank Cauchy-Schwarz for real Hermitian matrices, stated against
the Hermitian eigenvalue square sum.  This is the first reusable step in the
standard trace/rank estimate used in near-identity rank lower bounds.
-/
theorem trace_sq_le_rank_mul_sum_eigenvalues_sq_of_isHermitian
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * ∑ i, hA.eigenvalues i ^ 2 := by
  have htrace : A.trace = ∑ i, hA.eigenvalues i := by
    simpa using hA.trace_eq_sum_eigenvalues
  have hrank :
      (Fintype.card {i : ι // hA.eigenvalues i ≠ 0} : ℝ) =
        (A.rank : ℝ) := by
    exact_mod_cast hA.rank_eq_card_non_zero_eigs.symm
  have hcauchy :=
    sq_sum_le_support_card_mul_sum_sq (fun i : ι => hA.eigenvalues i)
  rw [htrace, ← hrank]
  exact hcauchy

/--
For a real Hermitian matrix, the trace of `A * A` is the sum of the squares of
the Hermitian eigenvalues.
-/
theorem trace_mul_self_eq_sum_eigenvalues_sq_of_isHermitian
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle']
  simp only [← Matrix.mul_assoc]
  rw [Unitary.coe_star_mul_self]
  simp only [one_mul]
  rw [Matrix.mul_assoc (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))
    (star (↑hA.eigenvectorUnitary : Matrix ι ι ℝ))
    (↑hA.eigenvectorUnitary : Matrix ι ι ℝ)]
  rw [Unitary.coe_star_mul_self]
  simp [Matrix.trace_diagonal, pow_two]

/--
Trace/rank estimate for real Hermitian matrices in Frobenius form:
`trace(A)^2 <= rank(A) * trace(Aᵀ A)`.
-/
theorem trace_sq_le_rank_mul_trace_transpose_mul_self_of_isHermitian
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * Matrix.trace (Aᵀ * A) := by
  have htranspose : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
    exact hA
  have htrace :
      Matrix.trace (Aᵀ * A) = ∑ i, hA.eigenvalues i ^ 2 := by
    rw [htranspose]
    exact trace_mul_self_eq_sum_eigenvalues_sq_of_isHermitian hA
  rw [htrace]
  exact trace_sq_le_rank_mul_sum_eigenvalues_sq_of_isHermitian hA

/--
Divided form of the trace/rank estimate for real Hermitian matrices.
-/
theorem trace_sq_div_trace_transpose_mul_self_le_rank_of_isHermitian
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (htrace_pos : 0 < Matrix.trace (Aᵀ * A)) :
    A.trace ^ 2 / Matrix.trace (Aᵀ * A) ≤ (A.rank : ℝ) := by
  exact (div_le_iff₀ htrace_pos).2
    (trace_sq_le_rank_mul_trace_transpose_mul_self_of_isHermitian hA)

end HermitianTraceRank

section NearIdentityRankObstruction

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {coord : Type v} [Fintype coord] [DecidableEq coord]

/--
If a Hermitian matrix has trace at least the ambient cardinality and squared
Frobenius trace at most twice that cardinality, then its rank is at least half
the ambient cardinality.  This is the trace/Frobenius core of the polynomial
method near-identity rank obstruction.
-/
theorem card_le_two_mul_rank_of_isHermitian_trace_frobenius
    {P : Matrix ι ι ℝ} (hP : P.IsHermitian)
    (htrace : (Fintype.card ι : ℝ) ≤ P.trace)
    (hfrob : Matrix.trace (Pᵀ * P) ≤ 2 * (Fintype.card ι : ℝ)) :
    (Fintype.card ι : ℝ) ≤ 2 * (P.rank : ℝ) := by
  have htrace_nonneg : 0 ≤ P.trace :=
    le_trans (Nat.cast_nonneg _) htrace
  have hcard_sq_le : (Fintype.card ι : ℝ) ^ 2 ≤ P.trace ^ 2 := by
    exact sq_le_sq' (by nlinarith) htrace
  have htrace_rank :=
    trace_sq_le_rank_mul_trace_transpose_mul_self_of_isHermitian hP
  have hrank_nonneg : 0 ≤ (P.rank : ℝ) :=
    rank_cast_nonneg P
  have hmain :
      (Fintype.card ι : ℝ) ^ 2 ≤
        (P.rank : ℝ) * (2 * (Fintype.card ι : ℝ)) := by
    exact hcard_sq_le.trans
      (htrace_rank.trans
        (mul_le_mul_of_nonneg_left hfrob hrank_nonneg))
  by_cases hcard_zero : (Fintype.card ι : ℝ) = 0
  · simp [hcard_zero]
  · have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
      exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hcard_zero)
    nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Entrywise natural powers preserve Hermitian symmetry over real matrices. -/
theorem isHermitian_entrywisePow_of_symmetric
    {M : Matrix ι ι ℝ} (hsym : ∀ i j, M i j = M j i) (t : ℕ) :
    (Matrix.of fun i j => (M i j) ^ t).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp [hsym i j]

omit [DecidableEq ι] in
/-- The trace of an entrywise power is the ambient cardinality when the diagonal is one. -/
theorem trace_entrywisePow_eq_card_of_diag_one
    {M : Matrix ι ι ℝ} (hdiag : ∀ i, M i i = 1) (t : ℕ) :
    (Matrix.of fun i j => (M i j) ^ t).trace = (Fintype.card ι : ℝ) := by
  simp [Matrix.trace, Matrix.diag, hdiag]

/--
If an entrywise power of a diagonal-one matrix has all off-diagonal entries
bounded by `eta`, and `card * eta^(2t) <= 1`, its squared Frobenius trace is at
most `2 * card`.
-/
theorem trace_transpose_mul_self_entrywisePow_le_two_card_of_diag_one_offdiag
    {M : Matrix ι ι ℝ} {eta : ℝ} (heta_nonneg : 0 ≤ eta)
    (hdiag : ∀ i, M i i = 1)
    (hoff : ∀ ⦃i j : ι⦄, i ≠ j → |M i j| ≤ eta)
    (t : ℕ)
    (hsmall : (Fintype.card ι : ℝ) * eta ^ (2 * t) ≤ 1) :
    Matrix.trace
        ((Matrix.of fun i j => (M i j) ^ t)ᵀ *
          (Matrix.of fun i j => (M i j) ^ t)) ≤
      2 * (Fintype.card ι : ℝ) := by
  classical
  let P : Matrix ι ι ℝ := Matrix.of fun i j => (M i j) ^ t
  have hentry :
      ∀ i j : ι, P i j ^ 2 ≤ if i = j then (1 : ℝ) else eta ^ (2 * t) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [P, hdiag]
    · have habs_pow : |M i j ^ t| ≤ eta ^ t := by
        simpa [abs_pow] using
          pow_le_pow_left₀ (abs_nonneg (M i j)) (hoff hij) t
      have hsquare : (M i j ^ t) ^ 2 ≤ (eta ^ t) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (pow_nonneg heta_nonneg t)] using habs_pow
      have hpow : (eta ^ t) ^ 2 = eta ^ (2 * t) := by
        rw [← pow_mul]
        ring_nf
      simpa [P, hij, hpow] using hsquare
  have hfrob_bound :
      frobeniusSq P ≤
        ∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else eta ^ (2 * t) := by
    unfold frobeniusSq
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hentry i j
  have hrow :
      ∀ i : ι,
        (∑ j : ι, if i = j then (1 : ℝ) else eta ^ (2 * t)) ≤
          1 + (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
    intro i
    calc
      (∑ j : ι, if i = j then (1 : ℝ) else eta ^ (2 * t))
          ≤ ∑ j : ι, ((if i = j then (1 : ℝ) else 0) + eta ^ (2 * t)) := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            by_cases hij : i = j
            · simp [hij, pow_nonneg heta_nonneg (2 * t)]
            · simp [hij]
      _ = 1 + (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
            simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  have hsum_bound :
      (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else eta ^ (2 * t)) ≤
        (Fintype.card ι : ℝ) *
          (1 + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
    calc
      (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else eta ^ (2 * t))
          ≤ ∑ _i : ι, (1 + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
            exact Finset.sum_le_sum fun i _ => hrow i
      _ = (Fintype.card ι : ℝ) *
            (1 + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
            simp [Finset.sum_const, mul_comm]
            ring
  have htotal :
      frobeniusSq P ≤ 2 * (Fintype.card ι : ℝ) := by
    have hmiddle :
        (Fintype.card ι : ℝ) *
            (1 + (Fintype.card ι : ℝ) * eta ^ (2 * t)) ≤
          2 * (Fintype.card ι : ℝ) := by
      nlinarith
    exact hfrob_bound.trans (hsum_bound.trans hmiddle)
  simpa [P, trace_transpose_mul_self_eq_frobeniusSq] using htotal

/--
Finite polynomial-method obstruction for symmetric dot-factorized
near-identity matrices.  If the symmetric-power feature count is less than half
the number of rows, some off-diagonal entry must exceed `eta`.
-/
theorem exists_offdiag_gt_of_symmetric_dot_factorization_diag_one
    (M : Matrix ι ι ℝ) (X : ι → coord → ℝ) (Y : ι → coord → ℝ)
    (hM : ∀ i j, M i j = ∑ r : coord, X i r * Y j r)
    (hsym : ∀ i j, M i j = M j i)
    (hdiag : ∀ i, M i i = 1)
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (t : ℕ)
    (hsmall : (Fintype.card ι : ℝ) * eta ^ (2 * t) ≤ 1)
    (hdim : 2 * (Fintype.card (Sym coord t) : ℝ) < (Fintype.card ι : ℝ)) :
    ∃ i j : ι, i ≠ j ∧ eta < |M i j| := by
  classical
  by_contra hnone
  have hoff : ∀ ⦃i j : ι⦄, i ≠ j → |M i j| ≤ eta := by
    intro i j hij
    by_contra hle
    exact hnone ⟨i, j, hij, lt_of_not_ge hle⟩
  let P : Matrix ι ι ℝ := Matrix.of fun i j => (M i j) ^ t
  have hP_herm : P.IsHermitian := by
    simpa [P] using isHermitian_entrywisePow_of_symmetric (M := M) hsym t
  have htrace : (Fintype.card ι : ℝ) ≤ P.trace := by
    rw [show P.trace = (Fintype.card ι : ℝ) by
      simpa [P] using trace_entrywisePow_eq_card_of_diag_one (M := M) hdiag t]
  have hfrob :
      Matrix.trace (Pᵀ * P) ≤ 2 * (Fintype.card ι : ℝ) := by
    simpa [P] using
      trace_transpose_mul_self_entrywisePow_le_two_card_of_diag_one_offdiag
        (M := M) (eta := eta) heta_nonneg hdiag hoff t hsmall
  have hlower :
      (Fintype.card ι : ℝ) ≤ 2 * (P.rank : ℝ) :=
    card_le_two_mul_rank_of_isHermitian_trace_frobenius hP_herm htrace hfrob
  have hupper_nat :
      P.rank ≤ Fintype.card (Sym coord t) := by
    simpa [P] using
      rank_entrywisePow_le_card_sym_of_dot_factorization
        (coord := coord) (M := M) (X := X) (Y := Y) hM t
  have hupper : 2 * (P.rank : ℝ) ≤
      2 * (Fintype.card (Sym coord t) : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hupper_nat) (by norm_num)
  exact not_lt_of_ge (hlower.trans hupper) hdim

/--
Finite polynomial-method obstruction for symmetric dot-factorized matrices with
diagonal lower and upper bounds.  The displayed inequality is the exact
trace/Frobenius contradiction after taking entrywise degree-`t` powers.
-/
theorem exists_offdiag_gt_of_symmetric_dot_factorization_diag_bounds
    (M : Matrix ι ι ℝ) (X : ι → coord → ℝ) (Y : ι → coord → ℝ)
    (hM : ∀ i j, M i j = ∑ r : coord, X i r * Y j r)
    (hsym : ∀ i j, M i j = M j i)
    {gamma beta eta : ℝ}
    (hgamma_nonneg : 0 ≤ gamma) (hbeta_nonneg : 0 ≤ beta)
    (hdiag_lower : ∀ i, gamma ≤ M i i)
    (hdiag_abs_upper : ∀ i, |M i i| ≤ beta)
    (heta_nonneg : 0 ≤ eta) (t : ℕ)
    (hdim :
      (Fintype.card (Sym coord t) : ℝ) *
          ((Fintype.card ι : ℝ) * beta ^ (2 * t) +
            (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * eta ^ (2 * t)) <
        (Fintype.card ι : ℝ) ^ 2 * gamma ^ (2 * t)) :
    ∃ i j : ι, i ≠ j ∧ eta < |M i j| := by
  classical
  by_contra hnone
  have hoff : ∀ ⦃i j : ι⦄, i ≠ j → |M i j| ≤ eta := by
    intro i j hij
    by_contra hle
    exact hnone ⟨i, j, hij, lt_of_not_ge hle⟩
  let P : Matrix ι ι ℝ := Matrix.of fun i j => (M i j) ^ t
  have hP_herm : P.IsHermitian := by
    simpa [P] using isHermitian_entrywisePow_of_symmetric (M := M) hsym t
  have htrace_lower :
      (Fintype.card ι : ℝ) * gamma ^ t ≤ P.trace := by
    unfold Matrix.trace Matrix.diag
    have hsum :
        (∑ _i : ι, gamma ^ t) ≤ ∑ i : ι, (M i i) ^ t := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact pow_le_pow_left₀ hgamma_nonneg (hdiag_lower i) t
    simpa [P, Finset.sum_const, Nat.cast_mul, mul_comm] using hsum
  have hentry :
      ∀ i j : ι, P i j ^ 2 ≤
        if i = j then beta ^ (2 * t) else eta ^ (2 * t) := by
    intro i j
    by_cases hij : i = j
    · subst j
      have habs_pow : |M i i ^ t| ≤ beta ^ t := by
        simpa [abs_pow] using
          pow_le_pow_left₀ (abs_nonneg (M i i)) (hdiag_abs_upper i) t
      have hsquare : (M i i ^ t) ^ 2 ≤ (beta ^ t) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (pow_nonneg hbeta_nonneg t)] using habs_pow
      have hpow : (beta ^ t) ^ 2 = beta ^ (2 * t) := by
        rw [← pow_mul]
        ring_nf
      simpa [P, hpow] using hsquare
    · have habs_pow : |M i j ^ t| ≤ eta ^ t := by
        simpa [abs_pow] using
          pow_le_pow_left₀ (abs_nonneg (M i j)) (hoff hij) t
      have hsquare : (M i j ^ t) ^ 2 ≤ (eta ^ t) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (pow_nonneg heta_nonneg t)] using habs_pow
      have hpow : (eta ^ t) ^ 2 = eta ^ (2 * t) := by
        rw [← pow_mul]
        ring_nf
      simpa [P, hij, hpow] using hsquare
  have hfrob_bound :
      frobeniusSq P ≤
        ∑ i : ι, ∑ j : ι,
          if i = j then beta ^ (2 * t) else eta ^ (2 * t) := by
    unfold frobeniusSq
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hentry i j
  have hrow :
      ∀ i : ι,
        (∑ j : ι, if i = j then beta ^ (2 * t) else eta ^ (2 * t)) ≤
          beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
    intro i
    calc
      (∑ j : ι, if i = j then beta ^ (2 * t) else eta ^ (2 * t))
          ≤ ∑ j : ι,
              ((if i = j then beta ^ (2 * t) else 0) + eta ^ (2 * t)) := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            by_cases hij : i = j
            · simp [hij, pow_nonneg heta_nonneg (2 * t)]
            · simp [hij]
      _ = beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
            simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  have hsum_bound :
      (∑ i : ι, ∑ j : ι,
          if i = j then beta ^ (2 * t) else eta ^ (2 * t)) ≤
        (Fintype.card ι : ℝ) *
          (beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
    calc
      (∑ i : ι, ∑ j : ι,
          if i = j then beta ^ (2 * t) else eta ^ (2 * t))
          ≤ ∑ _i : ι,
              (beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
            exact Finset.sum_le_sum fun i _ => hrow i
      _ = (Fintype.card ι : ℝ) *
            (beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
            simp [Finset.sum_const, mul_comm]
            ring
  have hfrob :
      Matrix.trace (Pᵀ * P) ≤
        (Fintype.card ι : ℝ) * beta ^ (2 * t) +
          (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
    have htotal := hfrob_bound.trans hsum_bound
    have hrearrange :
        (Fintype.card ι : ℝ) *
            (beta ^ (2 * t) + (Fintype.card ι : ℝ) * eta ^ (2 * t)) =
          (Fintype.card ι : ℝ) * beta ^ (2 * t) +
            (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * eta ^ (2 * t) := by
      ring
    simpa [P, trace_transpose_mul_self_eq_frobeniusSq, hrearrange] using htotal
  have htrace_nonneg : 0 ≤ P.trace := by
    exact le_trans
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hgamma_nonneg t))
      htrace_lower
  have htrace_sq_lower :
      ((Fintype.card ι : ℝ) * gamma ^ t) ^ 2 ≤ P.trace ^ 2 := by
    have hlhs_nonneg :
        0 ≤ (Fintype.card ι : ℝ) * gamma ^ t :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hgamma_nonneg t)
    exact sq_le_sq'
      (by nlinarith [hlhs_nonneg, htrace_nonneg])
      htrace_lower
  have htrace_rank :=
    trace_sq_le_rank_mul_trace_transpose_mul_self_of_isHermitian hP_herm
  have hupper_nat :
      P.rank ≤ Fintype.card (Sym coord t) := by
    simpa [P] using
      rank_entrywisePow_le_card_sym_of_dot_factorization
        (coord := coord) (M := M) (X := X) (Y := Y) hM t
  have hupper :
      (P.rank : ℝ) ≤ (Fintype.card (Sym coord t) : ℝ) := by
    exact_mod_cast hupper_nat
  have hfrob_nonneg :
      0 ≤ Matrix.trace (Pᵀ * P) :=
    trace_transpose_mul_self_nonneg P
  have hbound :
      P.trace ^ 2 ≤
        (Fintype.card (Sym coord t) : ℝ) *
          ((Fintype.card ι : ℝ) * beta ^ (2 * t) +
            (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * eta ^ (2 * t)) := by
    exact htrace_rank.trans
      ((mul_le_mul hupper hfrob hfrob_nonneg (Nat.cast_nonneg _)))
  have hleft_rewrite :
      ((Fintype.card ι : ℝ) * gamma ^ t) ^ 2 =
        (Fintype.card ι : ℝ) ^ 2 * gamma ^ (2 * t) := by
    rw [mul_pow]
    congr 1
    rw [← pow_mul]
    ring_nf
  exact not_lt_of_ge
    (by simpa [hleft_rewrite] using htrace_sq_lower.trans hbound)
    hdim

end NearIdentityRankObstruction

end MatrixRankInequalities
end Math
end AppliedModelingLib
