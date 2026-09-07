import KR21Monoculture.LaplaceW11Regularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Probability.Moments.Variance

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace KR21Monoculture

/-!
# Literal unit-variance centered Laplace law

The source's Laplace example fixes a unit-standard-deviation innovation.  The
paper-local ranking construction uses the rate parametrization
`lambda / 2 * exp (-lambda * |x|)`, so this module verifies the semantic
normalization rather than treating the `sqrt 2` rate as a naming convention.
-/

private theorem laplaceRawMean_centered (lam : ℝ) :
    ∫ x : ℝ, x * theorem7LaplacePDF lam 0 x = 0 := by
  let f : ℝ → ℝ := fun x => x * theorem7LaplacePDF lam 0 x
  have hneg : (fun x : ℝ => f (-x)) = fun x => -f x := by
    funext x
    dsimp [f]
    simp only [theorem7LaplacePDF, sub_zero, abs_neg, neg_mul]
  have hsymm : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
    integral_neg_eq_self f volume
  rw [hneg, integral_neg] at hsymm
  dsimp [f] at hsymm ⊢
  linarith

private theorem real_gamma_three : Real.Gamma (3 : ℝ) = 2 := by
  norm_num [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]

private theorem laplaceRawSecondMoment_centered
    {lam : ℝ} (hlam : 0 < lam) :
    ∫ x : ℝ, x ^ 2 * theorem7LaplacePDF lam 0 x = 2 / lam ^ 2 := by
  have hgamma :
      (∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-lam * x)) =
        (1 / lam) ^ 3 * Real.Gamma 3 := by
    calc
      ∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-lam * x) =
          ∫ x : ℝ in Set.Ioi 0,
            x ^ ((3 : ℝ) - 1) * Real.exp (-(lam * x)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
        ring_nf
      _ = (1 / lam) ^ (3 : ℝ) * Real.Gamma 3 :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi
          (a := (3 : ℝ)) (r := lam) (by norm_num) hlam
      _ = (1 / lam) ^ 3 * Real.Gamma 3 := by
        congr 1
        exact Real.rpow_natCast (1 / lam) 3
  calc
    ∫ x : ℝ, x ^ 2 * theorem7LaplacePDF lam 0 x =
        ∫ x : ℝ, lam / 2 * (|x| ^ 2 * Real.exp (-lam * |x|)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [theorem7LaplacePDF]
      rw [← sq_abs x]
      ring_nf
    _ = lam / 2 * ∫ x : ℝ, |x| ^ 2 * Real.exp (-lam * |x|) := by
      rw [integral_const_mul]
    _ = lam / 2 *
        (2 * ∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-lam * x)) := by
      change lam / 2 *
        ∫ x : ℝ, (fun y : ℝ => y ^ 2 * Real.exp (-lam * y)) |x| = _
      rw [integral_comp_abs (f := fun y : ℝ => y ^ 2 * Real.exp (-lam * y))]
    _ = 2 / lam ^ 2 := by
      rw [hgamma, real_gamma_three]
      field_simp [hlam.ne']

private theorem centeredLaplace_mean_zero
    {lam : ℝ} (hlam : 0 < lam) :
    ∫ x : ℝ, x ∂theorem7LaplaceMeasure lam 0 = 0 := by
  change ∫ x : ℝ, x ∂(volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (theorem7LaplacePDF lam 0 x)) = 0
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simpa only [smul_eq_mul, ENNReal.toReal_ofReal
      (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := _) hlam.le), mul_comm] using
      laplaceRawMean_centered lam
  · exact (theorem7LaplacePDF_measurable lam 0).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

private theorem centeredLaplace_secondMoment
    {lam : ℝ} (hlam : 0 < lam) :
    ∫ x : ℝ, x ^ 2 ∂theorem7LaplaceMeasure lam 0 = 2 / lam ^ 2 := by
  change ∫ x : ℝ, x ^ 2 ∂(volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (theorem7LaplacePDF lam 0 x)) = 2 / lam ^ 2
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simpa only [smul_eq_mul, ENNReal.toReal_ofReal
      (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := _) hlam.le), mul_comm] using
      laplaceRawSecondMoment_centered hlam
  · exact (theorem7LaplacePDF_measurable lam 0).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

private theorem centeredLaplace_sq_integrable
    {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun x : ℝ => x ^ 2) (theorem7LaplaceMeasure lam 0) := by
  change Integrable (fun x : ℝ => x ^ 2) ((volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (theorem7LaplacePDF lam 0 x)))
  rw [integrable_withDensity_iff]
  · have hraw : Integrable (fun x : ℝ =>
        x ^ 2 * theorem7LaplacePDF lam 0 x) volume := by
      apply Integrable.of_integral_ne_zero
      rw [laplaceRawSecondMoment_centered hlam]
      positivity
    simpa only [ENNReal.toReal_ofReal
      (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := _) hlam.le)] using hraw
  · exact (theorem7LaplacePDF_measurable lam 0).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- The literal centered Laplace base law used for KR21 has zero mean. -/
theorem sourceUnitVarianceLaplaceBaseNoise_mean_zero :
    ∫ x : ℝ, x ∂theorem7LaplaceMeasure (Real.sqrt 2) 0 = 0 := by
  exact centeredLaplace_mean_zero (Real.sqrt_pos.2 (by norm_num))

/-- The literal centered Laplace base law used for KR21 has second moment one. -/
theorem sourceUnitVarianceLaplaceBaseNoise_secondMoment_one :
    ∫ x : ℝ, x ^ 2 ∂theorem7LaplaceMeasure (Real.sqrt 2) 0 = 1 := by
  rw [centeredLaplace_secondMoment (Real.sqrt_pos.2 (by norm_num))]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The literal centered Laplace base law has a finite second moment. -/
theorem sourceUnitVarianceLaplaceBaseNoise_memLp_two :
    MemLp id 2 (theorem7LaplaceMeasure (Real.sqrt 2) 0) := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq (by fun_prop)]
  simpa only [id_eq] using
    centeredLaplace_sq_integrable (Real.sqrt_pos.2 (by norm_num))

/-- Semantic source normalization: the specified centered Laplace base law has variance one. -/
theorem sourceUnitVarianceLaplaceBaseNoise_variance_one :
    Var[id; theorem7LaplaceMeasure (Real.sqrt 2) 0] = 1 := by
  letI : IsProbabilityMeasure (theorem7LaplaceMeasure (Real.sqrt 2) 0) :=
    ⟨theorem7LaplaceMeasure_univ (lam := Real.sqrt 2) (μ := 0)
      (Real.sqrt_pos.2 (by norm_num))⟩
  calc
    Var[id; theorem7LaplaceMeasure (Real.sqrt 2) 0] =
        (∫ x : ℝ, x ^ 2 ∂theorem7LaplaceMeasure (Real.sqrt 2) 0) -
          (∫ x : ℝ, x ∂theorem7LaplaceMeasure (Real.sqrt 2) 0) ^ 2 := by
      simpa only [id_eq] using
        (ProbabilityTheory.variance_eq_sub sourceUnitVarianceLaplaceBaseNoise_memLp_two)
    _ = 1 := by
      rw [sourceUnitVarianceLaplaceBaseNoise_secondMoment_one,
        sourceUnitVarianceLaplaceBaseNoise_mean_zero]
      norm_num

end KR21Monoculture
