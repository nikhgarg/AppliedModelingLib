import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Reusable Matrix Rank Bounds

Interfaces and consequences for rank lower bounds used by linear
compressed-sensing arguments.  The Alon near-identity theorem is isolated as a
paper-neutral theorem predicate so paper files can depend on exact rank-bound
semantics rather than broad endpoint certificates.
-/

namespace AppliedModelingLib
namespace Math
namespace RankBounds

/--
The diagonal-one form of Alon's near-identity rank lower bound.
-/
noncomputable def alonNormalizedRankBound
    (n : ℕ) (epsilon c : ℝ) : ℝ :=
  c * Real.log (n : ℝ) / (epsilon ^ 2 * Real.log (1 / epsilon))

/--
The scaled form of Alon's near-identity rank lower bound.  In LRH notation,
`gamma` lower-bounds the diagonal entries and `eta` upper-bounds off-diagonal
absolute values.
-/
noncomputable def alonScaledRankBound
    (n : ℕ) (gamma eta c : ℝ) : ℝ :=
  c * gamma ^ 2 * Real.log (n : ℝ) /
    (eta ^ 2 * Real.log (gamma / eta))

/--
Reusable theorem predicate for the normalized Alon rank bound.  This is the
actual deep theorem: a square matrix with diagonal exactly one and all
off-diagonal entries at most `epsilon` has rank at least logarithmic in its
size with Alon's denominator.
-/
def AlonNormalizedRankBoundHolds (c : ℝ) : Prop :=
  0 < c ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (D : Matrix ι ι ℝ) {epsilon : ℝ},
      1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
      epsilon < 1 / 2 →
      (∀ i, D i i = 1) →
      (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
      alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ)

/--
The strict off-diagonal form quoted by the LRH paper.  It is kept separate
from `AlonNormalizedRankBoundHolds`: strict and non-strict hypotheses are not
interchangeable at an externally cited theorem boundary.
-/
def AlonNormalizedStrictRankBoundHolds (c : ℝ) : Prop :=
  0 < c ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (D : Matrix ι ι ℝ) {epsilon : ℝ},
      1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
      epsilon < 1 / 2 →
      (∀ i, D i i = 1) →
      (∀ ⦃i j⦄, i ≠ j → |D i j| < epsilon) →
      alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ)

/--
Reusable theorem predicate for the scaled Alon rank bound.  This is the form
used by lower-bound reductions after the diagonal entries are only known to be
bounded below by `gamma`.
-/
def AlonScaledRankBoundHolds (c : ℝ) : Prop :=
  0 < c ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (C : Matrix ι ι ℝ) {gamma eta : ℝ},
      0 < gamma →
      gamma ≤ 1 →
      gamma / Real.sqrt (Fintype.card ι : ℝ) < eta →
      eta < gamma / 2 →
      (∀ i, gamma ≤ C i i) →
      (∀ ⦃i j⦄, i ≠ j → |C i j| ≤ eta) →
      alonScaledRankBound (Fintype.card ι) gamma eta c ≤ (C.rank : ℝ)

/-- Algebraic identity connecting the normalized and scaled Alon formulas. -/
theorem alonNormalizedRankBound_eta_div_gamma_eq_scaled
    {n : ℕ} {gamma eta c : ℝ} (hgamma : gamma ≠ 0) (heta : eta ≠ 0) :
    alonNormalizedRankBound n (eta / gamma) c =
      alonScaledRankBound n gamma eta c := by
  unfold alonNormalizedRankBound alonScaledRankBound
  field_simp [hgamma, heta]

noncomputable def rowNormalizeByDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Matrix.diagonal (fun i : ι => (C i i)⁻¹) * C

theorem rowNormalizeByDiagonal_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℝ}
    (hdiag_ne : ∀ i : ι, C i i ≠ 0) (i : ι) :
    rowNormalizeByDiagonal C i i = 1 := by
  simp [rowNormalizeByDiagonal, Matrix.diagonal_mul, hdiag_ne i]

theorem rowNormalizeByDiagonal_offdiag_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℝ}
    {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (hdiag : ∀ i : ι, gamma ≤ C i i)
    (hoff : ∀ ⦃i j : ι⦄, i ≠ j → |C i j| ≤ eta)
    {i j : ι} (hij : i ≠ j) :
    |rowNormalizeByDiagonal C i j| ≤ eta / gamma := by
  have hdiag_pos : 0 < C i i := lt_of_lt_of_le hgamma_pos (hdiag i)
  have hdiag_ne : C i i ≠ 0 := hdiag_pos.ne'
  have hdiag_abs : gamma ≤ |C i i| := by
    simpa [abs_of_pos hdiag_pos] using hdiag i
  have hinv_le : |(C i i)⁻¹| ≤ 1 / gamma := by
    have hinv := one_div_le_one_div_of_le hgamma_pos hdiag_abs
    simpa [one_div, abs_inv] using hinv
  have hmul :
      |(C i i)⁻¹| * |C i j| ≤ (1 / gamma) * eta :=
    mul_le_mul hinv_le (hoff hij) (abs_nonneg _) (by positivity)
  calc
    |rowNormalizeByDiagonal C i j| = |(C i i)⁻¹ * C i j| := by
      simp [rowNormalizeByDiagonal, Matrix.diagonal_mul]
    _ = |(C i i)⁻¹| * |C i j| := abs_mul _ _
    _ ≤ (1 / gamma) * eta := hmul
    _ = eta / gamma := by ring

theorem rowNormalizeByDiagonal_offdiag_abs_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℝ}
    {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (hdiag : ∀ i : ι, gamma ≤ C i i)
    (hoff : ∀ ⦃i j : ι⦄, i ≠ j → |C i j| < eta)
    {i j : ι} (hij : i ≠ j) :
    |rowNormalizeByDiagonal C i j| < eta / gamma := by
  have hdiag_pos : 0 < C i i := lt_of_lt_of_le hgamma_pos (hdiag i)
  have hdiag_abs : gamma ≤ |C i i| := by
    simpa [abs_of_pos hdiag_pos] using hdiag i
  have hinv_le : |(C i i)⁻¹| ≤ 1 / gamma := by
    have hinv := one_div_le_one_div_of_le hgamma_pos hdiag_abs
    simpa [one_div, abs_inv] using hinv
  calc
    |rowNormalizeByDiagonal C i j| = |(C i i)⁻¹| * |C i j| := by
      simp [rowNormalizeByDiagonal, Matrix.diagonal_mul, abs_mul]
    _ ≤ (1 / gamma) * |C i j| :=
      mul_le_mul_of_nonneg_right hinv_le (abs_nonneg _)
    _ < (1 / gamma) * eta :=
      mul_lt_mul_of_pos_left (hoff hij) (one_div_pos.mpr hgamma_pos)
    _ = eta / gamma := by ring

theorem rowNormalizeByDiagonal_rank_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℝ}
    (hdiag_ne : ∀ i : ι, C i i ≠ 0) :
    (rowNormalizeByDiagonal C).rank = C.rank := by
  have hdet_unit :
      IsUnit (Matrix.diagonal (fun i : ι => (C i i)⁻¹)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i _hi
      exact inv_ne_zero (hdiag_ne i))
  simpa [rowNormalizeByDiagonal] using
    Matrix.rank_mul_eq_right_of_isUnit_det
      (A := Matrix.diagonal (fun i : ι => (C i i)⁻¹))
      (B := C) hdet_unit

theorem one_div_sqrt_card_lt_eta_div_gamma_of_scaled
    {ι : Type*} [Fintype ι] {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (heta_low : gamma / Real.sqrt (Fintype.card ι : ℝ) < eta) :
    1 / Real.sqrt (Fintype.card ι : ℝ) < eta / gamma := by
  have h := div_lt_div_of_pos_right heta_low hgamma_pos
  have hrewrite : gamma / Real.sqrt (Fintype.card ι : ℝ) / gamma =
      1 / Real.sqrt (Fintype.card ι : ℝ) := by
    field_simp [hgamma_pos.ne']
  simpa [hrewrite] using h

theorem eta_div_gamma_lt_one_half_of_scaled
    {gamma eta : ℝ} (hgamma_pos : 0 < gamma)
    (heta_high : eta < gamma / 2) :
    eta / gamma < 1 / 2 := by
  have h := div_lt_div_of_pos_right heta_high hgamma_pos
  have hrewrite : gamma / 2 / gamma = (1 : ℝ) / 2 := by
    field_simp [hgamma_pos.ne']
  simpa [hrewrite] using h

/--
The source proof of the diagonal corollary to Alon's theorem: scale each row
by the inverse of its diagonal entry.  This theorem is fully reusable; it
turns the normalized diagonal-one theorem into the scaled lower bound for one
fixed finite index type.  Keeping the index type fixed avoids elaborating the
entire theorem predicate when paper proofs only need one concrete submatrix
type at a time.
-/
theorem scaledRankBound_of_normalizedRankBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ}
    (hnormalized :
      ∀ (D : Matrix ι ι ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ))
    (C : Matrix ι ι ℝ) {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (heta_low : gamma / Real.sqrt (Fintype.card ι : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i, gamma ≤ C i i)
    (hoff : ∀ ⦃i j⦄, i ≠ j → |C i j| ≤ eta) :
    alonScaledRankBound (Fintype.card ι) gamma eta c ≤ (C.rank : ℝ) := by
  classical
  let D : Matrix ι ι ℝ := rowNormalizeByDiagonal C
  have hdiag_pos : ∀ i : ι, 0 < C i i := by
    intro i
    exact lt_of_lt_of_le hgamma_pos (hdiag i)
  have hdiag_ne : ∀ i : ι, C i i ≠ 0 := fun i => (hdiag_pos i).ne'
  have hD_diag : ∀ i : ι, D i i = 1 := by
    intro i
    simpa [D] using rowNormalizeByDiagonal_diag (C := C) hdiag_ne i
  have heta_pos : 0 < eta := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_nonneg _
    have hnonneg : 0 ≤ gamma / Real.sqrt (Fintype.card ι : ℝ) := by
      exact div_nonneg hgamma_pos.le hsqrt_nonneg
    exact lt_of_le_of_lt hnonneg heta_low
  have heta_ne : eta ≠ 0 := heta_pos.ne'
  have heps_low :
      1 / Real.sqrt (Fintype.card ι : ℝ) < eta / gamma := by
    exact one_div_sqrt_card_lt_eta_div_gamma_of_scaled
      (ι := ι) hgamma_pos heta_low
  have heps_high : eta / gamma < 1 / 2 := by
    exact eta_div_gamma_lt_one_half_of_scaled hgamma_pos heta_high
  have hD_off : ∀ ⦃i j : ι⦄, i ≠ j → |D i j| ≤ eta / gamma := by
    intro i j hij
    simpa [D] using
      rowNormalizeByDiagonal_offdiag_abs_le
        (C := C) hgamma_pos hdiag hoff hij
  have hD_rank_eq : D.rank = C.rank := by
    simpa [D] using rowNormalizeByDiagonal_rank_eq (C := C) hdiag_ne
  have hnormalized_bound :
      alonNormalizedRankBound (Fintype.card ι) (eta / gamma) c ≤
        (D.rank : ℝ) :=
    hnormalized D heps_low heps_high hD_diag hD_off
  have hformula :
      alonNormalizedRankBound (Fintype.card ι) (eta / gamma) c =
        alonScaledRankBound (Fintype.card ι) gamma eta c :=
    alonNormalizedRankBound_eta_div_gamma_eq_scaled
      (n := Fintype.card ι) (c := c) hgamma_pos.ne' heta_ne
  rw [← hformula]
  rw [← hD_rank_eq]
  exact hnormalized_bound

/--
The exact row-normalization reduction for a normalized theorem with strict
off-diagonal hypotheses.  This is the form needed to formalize the LRH
paper's stated Alon lemma and its stated scaled corollary without silently
strengthening the imported theorem boundary.
-/
theorem scaledRankBound_of_strict_normalizedRankBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ}
    (hnormalized :
      ∀ (D : Matrix ι ι ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| < epsilon) →
        alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ))
    (C : Matrix ι ι ℝ) {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (heta_low : gamma / Real.sqrt (Fintype.card ι : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i, gamma ≤ C i i)
    (hoff : ∀ ⦃i j⦄, i ≠ j → |C i j| < eta) :
    alonScaledRankBound (Fintype.card ι) gamma eta c ≤ (C.rank : ℝ) := by
  classical
  let D : Matrix ι ι ℝ := rowNormalizeByDiagonal C
  have hdiag_pos : ∀ i : ι, 0 < C i i := by
    intro i
    exact lt_of_lt_of_le hgamma_pos (hdiag i)
  have hdiag_ne : ∀ i : ι, C i i ≠ 0 := fun i => (hdiag_pos i).ne'
  have hD_diag : ∀ i : ι, D i i = 1 := by
    intro i
    simpa [D] using rowNormalizeByDiagonal_diag (C := C) hdiag_ne i
  have heta_pos : 0 < eta := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_nonneg _
    have hnonneg : 0 ≤ gamma / Real.sqrt (Fintype.card ι : ℝ) :=
      div_nonneg hgamma_pos.le hsqrt_nonneg
    exact lt_of_le_of_lt hnonneg heta_low
  have heps_low :
      1 / Real.sqrt (Fintype.card ι : ℝ) < eta / gamma :=
    one_div_sqrt_card_lt_eta_div_gamma_of_scaled hgamma_pos heta_low
  have heps_high : eta / gamma < 1 / 2 :=
    eta_div_gamma_lt_one_half_of_scaled hgamma_pos heta_high
  have hD_off : ∀ ⦃i j : ι⦄, i ≠ j → |D i j| < eta / gamma := by
    intro i j hij
    simpa [D] using
      rowNormalizeByDiagonal_offdiag_abs_lt
        (C := C) hgamma_pos hdiag hoff hij
  have hD_rank_eq : D.rank = C.rank := by
    simpa [D] using rowNormalizeByDiagonal_rank_eq (C := C) hdiag_ne
  have hnormalized_bound :
      alonNormalizedRankBound (Fintype.card ι) (eta / gamma) c ≤
        (D.rank : ℝ) :=
    hnormalized D heps_low heps_high hD_diag hD_off
  have hformula :
      alonNormalizedRankBound (Fintype.card ι) (eta / gamma) c =
        alonScaledRankBound (Fintype.card ι) gamma eta c :=
    alonNormalizedRankBound_eta_div_gamma_eq_scaled
      (n := Fintype.card ι) (c := c) hgamma_pos.ne' heta_pos.ne'
  rw [← hformula]
  rw [← hD_rank_eq]
  exact hnormalized_bound

/--
Contrapositive scaled form derived from the normalized Alon theorem for one
fixed finite index type.
-/
theorem exists_offdiag_gt_of_rank_lt_scaledRankBound_of_normalized
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ}
    (hnormalized :
      ∀ (D : Matrix ι ι ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card ι : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card ι) epsilon c ≤ (D.rank : ℝ))
    (C : Matrix ι ι ℝ) {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (heta_low : gamma / Real.sqrt (Fintype.card ι : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i, gamma ≤ C i i)
    (hrank :
      (C.rank : ℝ) <
        alonScaledRankBound (Fintype.card ι) gamma eta c) :
    ∃ i j : ι, i ≠ j ∧ eta < |C i j| := by
  classical
  by_contra hnone
  have hoff : ∀ ⦃i j : ι⦄, i ≠ j → |C i j| ≤ eta := by
    intro i j hij
    by_contra hle
    exact hnone ⟨i, j, hij, lt_of_not_ge hle⟩
  have hbound :=
    scaledRankBound_of_normalizedRankBound
      (ι := ι) (c := c) hnormalized C
      hgamma_pos heta_low heta_high hdiag hoff
  exact not_lt_of_ge hbound hrank

/--
Contrapositive form used by graph reductions: if a matrix satisfies the
diagonal hypotheses and has rank below the Alon lower bound, then some
off-diagonal entry must exceed `eta` in absolute value.
-/
theorem exists_offdiag_gt_of_rank_lt_alonScaledRankBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ}
    (hAlon :
      ∀ (C : Matrix ι ι ℝ) {gamma eta : ℝ},
        0 < gamma →
        gamma ≤ 1 →
        gamma / Real.sqrt (Fintype.card ι : ℝ) < eta →
        eta < gamma / 2 →
        (∀ i, gamma ≤ C i i) →
        (∀ ⦃i j⦄, i ≠ j → |C i j| ≤ eta) →
        alonScaledRankBound (Fintype.card ι) gamma eta c ≤ (C.rank : ℝ))
    (C : Matrix ι ι ℝ) {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (heta_low : gamma / Real.sqrt (Fintype.card ι : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i, gamma ≤ C i i)
    (hrank :
      (C.rank : ℝ) <
        alonScaledRankBound (Fintype.card ι) gamma eta c) :
    ∃ i j : ι, i ≠ j ∧ eta < |C i j| := by
  classical
  by_contra hnone
  have hoff : ∀ ⦃i j : ι⦄, i ≠ j → |C i j| ≤ eta := by
    intro i j hij
    by_contra hle
    exact hnone ⟨i, j, hij, lt_of_not_ge hle⟩
  have hbound :=
    hAlon C hgamma_pos hgamma_le_one heta_low heta_high hdiag hoff
  exact not_lt_of_ge hbound hrank

end RankBounds
end Math
end AppliedModelingLib
