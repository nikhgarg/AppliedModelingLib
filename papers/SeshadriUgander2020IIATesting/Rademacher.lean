import SeshadriUgander2020IIATesting.ChiSquare

/-!
# Rademacher averaging for cycle orientations

Source: Lemma 4.  Each independent orientation of a decomposed cycle is a
Rademacher sign.  The analytic factor in the proof is a hyperbolic cosine,
bounded by `exp(x² / 2)`.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace Rademacher

/-- The real-valued Rademacher encoding of a Boolean orientation. -/
def sign (a : Bool) : ℝ := if a then 1 else -1

theorem sign_eq_one_or_neg_one (a : Bool) : sign a = 1 ∨ sign a = -1 := by
  cases a <;> simp [sign]

theorem sign_sq (a : Bool) : sign a ^ 2 = 1 := by
  rcases sign_eq_one_or_neg_one a with h | h <;> rw [h] <;> norm_num

/-- Averaging two independent orientation signs for one cycle produces
`cosh(t)`, exactly as in the fifth line of the source Lemma 4 proof. -/
theorem average_pair_exp_eq_cosh (t : ℝ) :
    (1 / 4 : ℝ) * ∑ a : Bool, ∑ a' : Bool,
      Real.exp (t * sign a * sign a') = Real.cosh t := by
  norm_num [sign, Real.cosh_eq, Real.exp_neg]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Pairing two orientation assignments pointwise.  This equivalence is what
turns the double average over orientations in source Lemma 4 into a product
of independent one-cycle averages. -/
noncomputable def orientationPairEquiv :
    (ι → Bool) × (ι → Bool) ≃ (ι → Bool × Bool) where
  toFun ab := fun i => (ab.1 i, ab.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv := by
    rintro ⟨a, a'⟩
    rfl
  right_inv := by
    intro f
    funext i
    exact Prod.eta _

/-- Before normalization, the independent orientation sum factors into its
one-cycle contributions. -/
theorem orientation_sum_exp_factors (t : ι → ℝ) :
    (∑ a : ι → Bool, ∑ a' : ι → Bool,
      Real.exp (∑ i, t i * sign (a i) * sign (a' i))) =
      ∏ i, (∑ a : Bool, ∑ a' : Bool,
        Real.exp (t i * sign a * sign a')) := by
  classical
  rw [← Fintype.sum_prod_type']
  calc
    (∑ ab : (ι → Bool) × (ι → Bool),
        Real.exp (∑ i, t i * sign (ab.1 i) * sign (ab.2 i))) =
        ∑ f : ι → Bool × Bool,
          Real.exp (∑ i, t i * sign (f i).1 * sign (f i).2) := by
      exact Fintype.sum_equiv orientationPairEquiv _ _ (by rintro ⟨a, a'⟩; rfl)
    _ = ∑ f : ι → Bool × Bool,
          ∏ i, Real.exp (t i * sign (f i).1 * sign (f i).2) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Real.exp_sum]
    _ = ∏ i, ∑ p : Bool × Bool,
          Real.exp (t i * sign p.1 * sign p.2) := by
      rw [Fintype.prod_sum]
    _ = ∏ i, (∑ a : Bool, ∑ a' : Bool,
          Real.exp (t i * sign a * sign a')) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]

/-- The normalized orientation average in source Lemma 4 is exactly a
product of hyperbolic cosines. -/
theorem orientation_average_exp_eq_prod_cosh (t : ι → ℝ) :
    (1 / (4 : ℝ) ^ Fintype.card ι) *
        (∑ a : ι → Bool, ∑ a' : ι → Bool,
          Real.exp (∑ i, t i * sign (a i) * sign (a' i))) =
      ∏ i, Real.cosh (t i) := by
  classical
  rw [orientation_sum_exp_factors]
  have hlocal : ∀ i : ι,
      (∑ a : Bool, ∑ a' : Bool,
        Real.exp (t i * sign a * sign a')) = 4 * Real.cosh (t i) := by
    intro i
    have h := average_pair_exp_eq_cosh (t i)
    linarith
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  field_simp

/-- The product of the one-cycle cosh bounds, in the exact form used when
closing source Lemma 4. -/
theorem prod_cosh_le_exp_half_sum_sq (t : ι → ℝ) :
    (∏ i, Real.cosh (t i)) ≤ Real.exp (∑ i, (t i) ^ 2 / 2) := by
  calc
    (∏ i, Real.cosh (t i)) ≤ ∏ i, Real.exp ((t i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact (Real.cosh_pos _).le
      · intro i hi
        exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (∑ i, (t i) ^ 2 / 2) := by
      rw [Real.exp_sum]

/-- The full analytic orientation bound used in source Lemma 4. -/
theorem orientation_average_exp_le_exp_half_sum_sq (t : ι → ℝ) :
    (1 / (4 : ℝ) ^ Fintype.card ι) *
        (∑ a : ι → Bool, ∑ a' : ι → Bool,
          Real.exp (∑ i, t i * sign (a i) * sign (a' i))) ≤
      Real.exp (∑ i, (t i) ^ 2 / 2) := by
  rw [orientation_average_exp_eq_prod_cosh]
  exact prod_cosh_le_exp_half_sum_sq t

end Rademacher

end SeshadriUgander2020IIATesting
