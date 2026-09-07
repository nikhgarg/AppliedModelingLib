import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Tactic

/-!
# Finite-PMF `L²` and standard-deviation inequalities

This module supplies the finite weighted `L²` geometry used by empirical
Bernstein arguments.  The results are paper-neutral: a standard deviation is
Lipschitz under the finite-PMF `L²` seminorm.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The root second moment of a real function under a finite PMF. -/
noncomputable def pmfL2
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) : ℝ :=
  Real.sqrt (pmfExp μ (fun a => f a ^ 2))

/-- The finite-PMF root second moment is an ordinary Euclidean norm after
weighting every coordinate by the square root of its PMF mass. -/
theorem pmfL2_eq_normL2_weighted
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfL2 μ f = FiniteDimensionalNorms.l2
      (fun a => Real.sqrt ((μ a).toReal) * f a) := by
  unfold pmfL2 pmfExp FiniteDimensionalNorms.l2 FiniteDimensionalNorms.l2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hmass : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
  rw [mul_pow, Real.sq_sqrt hmass]

/-- The finite-PMF root second moment satisfies the triangle inequality. -/
theorem pmfL2_add_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfL2 μ (fun a => f a + g a) ≤ pmfL2 μ f + pmfL2 μ g := by
  rw [pmfL2_eq_normL2_weighted, pmfL2_eq_normL2_weighted,
    pmfL2_eq_normL2_weighted]
  calc
    FiniteDimensionalNorms.l2
        (fun a => Real.sqrt ((μ a).toReal) * (f a + g a)) =
        FiniteDimensionalNorms.l2
          (fun a => Real.sqrt ((μ a).toReal) * f a +
            Real.sqrt ((μ a).toReal) * g a) := by
          congr 1
          funext a
          ring
    _ ≤ FiniteDimensionalNorms.l2 (fun a => Real.sqrt ((μ a).toReal) * f a) +
          FiniteDimensionalNorms.l2 (fun a => Real.sqrt ((μ a).toReal) * g a) :=
      FiniteDimensionalNorms.normL2_add_le _ _

/-- The standard deviation of a finite-PMF random variable. -/
noncomputable def pmfStdDev
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) : ℝ :=
  Real.sqrt (pmfVariance μ f)

/-- A standard deviation is the root second moment of the centered function. -/
theorem pmfStdDev_eq_pmfL2_centered
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfStdDev μ f = pmfL2 μ (fun a => f a - pmfExp μ f) := rfl

/-- Finite-PMF standard deviation satisfies the triangle inequality. -/
theorem pmfStdDev_add_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfStdDev μ (fun a => f a + g a) ≤ pmfStdDev μ f + pmfStdDev μ g := by
  rw [pmfStdDev_eq_pmfL2_centered, pmfStdDev_eq_pmfL2_centered,
    pmfStdDev_eq_pmfL2_centered]
  calc
    pmfL2 μ (fun a => f a + g a - pmfExp μ (fun a => f a + g a)) =
        pmfL2 μ (fun a =>
          (f a - pmfExp μ f) + (g a - pmfExp μ g)) := by
          congr 1
          funext a
          rw [pmfExp_add]
          ring
    _ ≤ pmfL2 μ (fun a => f a - pmfExp μ f) +
          pmfL2 μ (fun a => g a - pmfExp μ g) := pmfL2_add_le μ _ _

/-- Reversing a difference does not change its finite-PMF standard deviation. -/
theorem pmfStdDev_sub_rev
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfStdDev μ (fun a => f a - g a) = pmfStdDev μ (fun a => g a - f a) := by
  unfold pmfStdDev pmfVariance
  congr 1
  apply pmfExp_congr
  intro a
  simp only [pmfExp_sub]
  ring

/-- Subtracting standard deviations is controlled by the standard deviation
of the pointwise difference. -/
theorem pmfStdDev_sub_le_pmfStdDev_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfStdDev μ f - pmfStdDev μ g ≤ pmfStdDev μ (fun a => f a - g a) := by
  have htriangle := pmfStdDev_add_le μ (fun a => f a - g a) g
  have hsplit : (fun a => (f a - g a) + g a) = f := by
    funext a
    ring
  rw [hsplit] at htriangle
  linarith

/-- Standard deviation is bounded by the root second moment. -/
theorem pmfStdDev_le_pmfL2
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfStdDev μ f ≤ pmfL2 μ f := by
  unfold pmfStdDev pmfL2
  apply Real.sqrt_le_sqrt
  rw [pmfVariance_eq_exp_sq_sub_sq_exp]
  exact sub_le_self _ (sq_nonneg _)

/-- Finite-PMF standard deviation is Lipschitz under the finite-PMF `L²`
seminorm. -/
theorem abs_pmfStdDev_sub_le_pmfL2_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    |pmfStdDev μ f - pmfStdDev μ g| ≤ pmfL2 μ (fun a => f a - g a) := by
  have hforward := pmfStdDev_sub_le_pmfStdDev_sub μ f g
  have hbackwardRaw := pmfStdDev_sub_le_pmfStdDev_sub μ g f
  have hbackward : pmfStdDev μ g - pmfStdDev μ f ≤ pmfStdDev μ (fun a => f a - g a) := by
    calc
      pmfStdDev μ g - pmfStdDev μ f ≤ pmfStdDev μ (fun a => g a - f a) := hbackwardRaw
      _ = pmfStdDev μ (fun a => f a - g a) := (pmfStdDev_sub_rev μ f g).symm
  apply le_trans (abs_le.mpr ⟨by linarith, hforward⟩)
  exact pmfStdDev_le_pmfL2 μ _

end AppliedModelingLib
