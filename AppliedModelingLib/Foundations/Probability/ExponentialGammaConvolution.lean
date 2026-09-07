import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalErlang

/-!
# Exact density reduction for the two-exponential convolution

This isolates the sole analytic statement needed to identify the two-gap
arrival law with the shape-two gamma law.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The ENNReal gamma density is Borel measurable. -/
theorem measurable_gammaPDF (a rate : ℝ) :
    Measurable (ProbabilityTheory.gammaPDF a rate) := by
  simpa [ProbabilityTheory.gammaPDF] using
    (ProbabilityTheory.measurable_gammaPDFReal a rate).ennreal_ofReal

/-- The exponential density is definitionally the shape-one gamma density. -/
theorem exponentialPDF_eq_gammaPDF_one (rate : ℝ) :
    ProbabilityTheory.exponentialPDF rate = ProbabilityTheory.gammaPDF 1 rate := by
  rfl

/--
The convolution of two exponential measures is the shape-two gamma measure
exactly when their additive-convolution densities agree almost everywhere.

The right-hand side is a concrete finite-interval integral identity after
unfolding `lconvolution_def`; no stochastic independence remains in it.
-/
theorem expMeasure_conv_expMeasure_eq_gammaMeasure_two_iff (rate : ℝ) :
    ProbabilityTheory.expMeasure rate ∗ ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure 2 rate ↔
    (ProbabilityTheory.gammaPDF 1 rate ⋆ₗ[volume]
      ProbabilityTheory.gammaPDF 1 rate) =ᵐ[volume]
        ProbabilityTheory.gammaPDF 2 rate := by
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [MeasureTheory.conv_withDensity_eq_lconvolution
      (measurable_gammaPDF 1 rate) (measurable_gammaPDF 1 rate),
    MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (MeasureTheory.measurable_lconvolution volume
        (measurable_gammaPDF 1 rate) (measurable_gammaPDF 1 rate)).aemeasurable
      (measurable_gammaPDF 2 rate).aemeasurable]

/-- The same exact reduction stated using the exponential-density name. -/
theorem expMeasure_conv_expMeasure_eq_gammaMeasure_two_iff_exponentialPDF
    (rate : ℝ) :
    ProbabilityTheory.expMeasure rate ∗ ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure 2 rate ↔
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) =ᵐ[volume]
        ProbabilityTheory.gammaPDF 2 rate := by
  simpa only [exponentialPDF_eq_gammaPDF_one] using
    (expMeasure_conv_expMeasure_eq_gammaMeasure_two_iff rate)

/-- Pointwise expansion of the remaining convolution-density integrand. -/
theorem exponentialPDF_lconvolution_apply (rate x : ℝ) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ∫⁻ y : ℝ, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) := by
  rw [MeasureTheory.lconvolution_def]

/--
The convolution integral is supported on the geometric simplex `0 ≤ y ≤ x`.
This leaves only a finite-interval calculation on the positive branch.
-/
theorem exponentialPDF_lconvolution_eq_setLIntegral_Icc (rate x : ℝ) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
        ∫⁻ y : ℝ, (Set.Icc (0 : ℝ) x).indicator
          (fun z => ProbabilityTheory.exponentialPDF rate z *
            ProbabilityTheory.exponentialPDF rate (-z + x)) y := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) x
      · simp [hy]
      · rw [Set.indicator_of_notMem hy]
        have houtside : y < 0 ∨ x < y := by
          by_cases hyneg : y < 0
          · exact Or.inl hyneg
          · right
            have hynonneg : 0 ≤ y := le_of_not_gt hyneg
            have hnotle : ¬ y ≤ x := by
              intro hle
              exact hy ⟨hynonneg, hle⟩
            exact lt_of_not_ge hnotle
        rcases houtside with hyneg | hgt
        · rw [ProbabilityTheory.exponentialPDF_of_neg hyneg]
          simp
        · have hshift_neg : -y + x < 0 := by linarith
          rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
          simp
    _ = ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) :=
      MeasureTheory.lintegral_indicator measurableSet_Icc _

/--
The convolution density vanishes on the negative half-line.  This discharges
the negative branch of the shape-two gamma density calculation without any
integration theorem.
-/
theorem exponentialPDF_lconvolution_eq_zero_of_neg
    {rate x : ℝ} (hx : x < 0) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x = 0 := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) = ∫⁻ _ : ℝ, 0 := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y < 0
      · rw [ProbabilityTheory.exponentialPDF_of_neg hy]
        simp
      · have hy_nonneg : 0 ≤ y := le_of_not_gt hy
        have hshift_neg : -y + x < 0 := by linarith
        rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
        simp
    _ = 0 := MeasureTheory.lintegral_zero

/-- The target gamma density has the same zero branch on negative inputs. -/
theorem exponentialPDF_lconvolution_eq_gammaPDF_two_of_neg
    {rate x : ℝ} (hx : x < 0) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 2 rate x := by
  rw [exponentialPDF_lconvolution_eq_zero_of_neg hx,
    ProbabilityTheory.gammaPDF_of_neg hx]

/--
On the positive convolution simplex, the product of the two exponential
densities is constant.  This is the algebraic core of the remaining
shape-two gamma calculation; integrating the constant over `Icc 0 x` is the
only analytic step still needed on the nonnegative branch.
-/
theorem exponentialPDF_convolution_integrand_eq_const_on_Icc
    {rate x y : ℝ} (hrate : 0 < rate) (hyx : y ∈ Set.Icc 0 x) :
    ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
      ENNReal.ofReal (rate ^ 2 * Real.exp (-(rate * x))) := by
  have hy_nonneg : 0 ≤ y := hyx.1
  have hshift_nonneg : 0 ≤ -y + x := by linarith [hyx.2]
  rw [ProbabilityTheory.exponentialPDF_of_nonneg hy_nonneg,
    ProbabilityTheory.exponentialPDF_of_nonneg hshift_nonneg]
  have hfirst_nonneg : 0 ≤ rate * Real.exp (-(rate * y)) := by positivity
  rw [← ENNReal.ofReal_mul hfirst_nonneg]
  congr 1
  calc
    rate * Real.exp (-(rate * y)) *
        (rate * Real.exp (-(rate * (-y + x)))) =
        rate ^ 2 * (Real.exp (-(rate * y)) *
          Real.exp (-(rate * (-y + x)))) := by ring
    _ = rate ^ 2 * Real.exp (-(rate * y) + -(rate * (-y + x))) := by
      rw [← Real.exp_add]
    _ = rate ^ 2 * Real.exp (-(rate * x)) := by
      have harg : -(rate * y) + -(rate * (-y + x)) = -(rate * x) := by ring
      rw [harg]

/-- The shape-two gamma normalization is one. -/
theorem gamma_two : Real.Gamma 2 = 1 := by
  have h := Real.Gamma_nat_eq_factorial 1
  norm_num at h ⊢

/--
The nonnegative branch of the two-exponential convolution density is exactly
the shape-two gamma density.
-/
theorem exponentialPDF_lconvolution_eq_gammaPDF_two_of_nonneg
    {rate x : ℝ} (hrate : 0 < rate) (hx : 0 ≤ x) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 2 rate x := by
  rw [exponentialPDF_lconvolution_eq_setLIntegral_Icc]
  have hconst :
      (∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.exponentialPDF rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x)) =
        ∫⁻ _y : ℝ in Set.Icc 0 x,
          ENNReal.ofReal (rate ^ 2 * Real.exp (-(rate * x))) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact exponentialPDF_convolution_integrand_eq_const_on_Icc hrate hy
  rw [hconst, MeasureTheory.setLIntegral_const, Real.volume_Icc,
    ProbabilityTheory.gammaPDF_of_nonneg hx, gamma_two]
  norm_num
  have hconst_nonneg : 0 ≤ rate ^ 2 * Real.exp (-(rate * x)) := by positivity
  rw [← ENNReal.ofReal_mul hconst_nonneg]
  congr 1
  ring

/-- The two convolution densities agree pointwise at every real input. -/
theorem exponentialPDF_lconvolution_eq_gammaPDF_two
    {rate : ℝ} (hrate : 0 < rate) (x : ℝ) :
    (ProbabilityTheory.exponentialPDF rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 2 rate x := by
  by_cases hx : 0 ≤ x
  · exact exponentialPDF_lconvolution_eq_gammaPDF_two_of_nonneg hrate hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [exponentialPDF_lconvolution_eq_zero_of_neg hxneg,
      ProbabilityTheory.gammaPDF_of_neg hxneg]

/-- Two independent rate-`rate` exponential gaps have the shape-two gamma law. -/
theorem expMeasure_conv_expMeasure_eq_gammaMeasure_two
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.expMeasure rate ∗ ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure 2 rate := by
  apply (expMeasure_conv_expMeasure_eq_gammaMeasure_two_iff_exponentialPDF rate).2
  exact Filter.Eventually.of_forall
    (fun x => exponentialPDF_lconvolution_eq_gammaPDF_two hrate x)

/-- The two-gap canonical arrival time has the shape-two gamma law. -/
theorem arrivalTime_one_hasLaw_gammaMeasure_two
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (arrivalTime 1)
      (ProbabilityTheory.gammaMeasure 2 rate)
      (exponentialInterarrivalMeasure rate) := by
  have h := arrivalTime_one_hasLaw_exponential_conv hrate
  rw [expMeasure_conv_expMeasure_eq_gammaMeasure_two hrate] at h
  exact h

/-- The second post-tag epoch is the same two-gap gamma arrival time. -/
theorem postTagArrival_two_hasLaw_gammaMeasure_two
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (postTagArrival 2)
      (ProbabilityTheory.gammaMeasure 2 rate)
      (exponentialInterarrivalMeasure rate) := by
  simpa [postTagArrival] using
    (arrivalTime_one_hasLaw_gammaMeasure_two hrate)

/-- A compact-interval `lintegral` calculation for the first Gamma induction step. -/
theorem lintegral_ofReal_mul_id_Icc
    {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    (∫⁻ y : ℝ in Set.Icc 0 x, ENNReal.ofReal (c * y)) =
      ENNReal.ofReal (c * (x ^ 2 / 2)) := by
  have h_int : Integrable (fun y : ℝ => c * y)
      (volume.restrict (Set.Icc (0 : ℝ) x)) := by
    simpa [IntegrableOn] using
      ((continuous_const.mul continuous_id).integrableOn_Icc
        (a := (0 : ℝ)) (b := x) (μ := volume))
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) x)]
      (fun y : ℝ => c * y) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_nonneg hc hy.1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  congr 1
  have h_set_integral :
      (∫ y : ℝ in Set.Icc 0 x, c * y) =
        ∫ y : ℝ in (0 : ℝ)..x, c * y := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx]
  rw [h_set_integral, intervalIntegral.integral_const_mul]
  have hpow : (∫ y : ℝ in (0 : ℝ)..x, y) = x ^ 2 / 2 := by
    simp
  rw [hpow]

/-- The shape-three Gamma normalization. -/
theorem gamma_three : Real.Gamma 3 = 2 := by
  have h := Real.Gamma_nat_eq_factorial 2
  norm_num at h ⊢

/-- Algebra in the positive convolution simplex for the shape-two-to-three step. -/
theorem gammaPDF_two_exp_integrand_eq_const_mul_id
    {rate x y : ℝ} (hrate : 0 < rate) (hyx : y ∈ Set.Icc 0 x) :
    ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
      ENNReal.ofReal ((rate ^ 3 * Real.exp (-(rate * x))) * y) := by
  have hy_nonneg : 0 ≤ y := hyx.1
  have hshift_nonneg : 0 ≤ -y + x := by linarith [hyx.2]
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy_nonneg,
    ProbabilityTheory.exponentialPDF_of_nonneg hshift_nonneg, gamma_two]
  norm_num [Real.rpow_one]
  have hfirst_nonneg : 0 ≤ rate ^ 2 * y * Real.exp (-(rate * y)) := by positivity
  rw [← ENNReal.ofReal_mul hfirst_nonneg]
  congr 1
  calc
    rate ^ 2 * y * Real.exp (-(rate * y)) *
        (rate * Real.exp (-(rate * (-y + x)))) =
      rate ^ 3 * y *
        (Real.exp (-(rate * y)) * Real.exp (-(rate * (-y + x)))) := by
        ring
    _ = (rate ^ 3 * Real.exp (-(rate * x))) * y := by
        rw [← Real.exp_add]
        have harg : -(rate * y) + -(rate * (-y + x)) = -(rate * x) := by ring
        rw [harg]
        ring

/-- The shape-two Gamma--exponential convolution is supported on `Icc 0 x`. -/
theorem gammaPDF_two_lconvolution_exp_eq_setLIntegral_Icc
    (rate x : ℝ) :
    (ProbabilityTheory.gammaPDF 2 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
        ∫⁻ y : ℝ, (Set.Icc (0 : ℝ) x).indicator
          (fun z => ProbabilityTheory.gammaPDF 2 rate z *
            ProbabilityTheory.exponentialPDF rate (-z + x)) y := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) x
      · simp [hy]
      · rw [Set.indicator_of_notMem hy]
        have houtside : y < 0 ∨ x < y := by
          by_cases hyneg : y < 0
          · exact Or.inl hyneg
          · right
            have hynonneg : 0 ≤ y := le_of_not_gt hyneg
            have hnotle : ¬ y ≤ x := by
              intro hle
              exact hy ⟨hynonneg, hle⟩
            exact lt_of_not_ge hnotle
        rcases houtside with hyneg | hgt
        · rw [ProbabilityTheory.gammaPDF_of_neg hyneg]
          simp
        · have hshift_neg : -y + x < 0 := by linarith
          rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
          simp
    _ = ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) :=
      MeasureTheory.lintegral_indicator measurableSet_Icc _

/-- The shape-two Gamma--exponential convolution vanishes below zero. -/
theorem gammaPDF_two_lconvolution_exp_eq_zero_of_neg
    {rate x : ℝ} (hx : x < 0) :
    (ProbabilityTheory.gammaPDF 2 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x = 0 := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) = ∫⁻ _ : ℝ, 0 := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y < 0
      · rw [ProbabilityTheory.gammaPDF_of_neg hy]
        simp
      · have hy_nonneg : 0 ≤ y := le_of_not_gt hy
        have hshift_neg : -y + x < 0 := by linarith
        rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
        simp
    _ = 0 := MeasureTheory.lintegral_zero

/-- The positive branch of the finite shape-two-to-three Gamma convolution. -/
theorem gammaPDF_two_lconvolution_exp_eq_gammaPDF_three_of_nonneg
    {rate x : ℝ} (hrate : 0 < rate) (hx : 0 ≤ x) :
    (ProbabilityTheory.gammaPDF 2 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 3 rate x := by
  rw [gammaPDF_two_lconvolution_exp_eq_setLIntegral_Icc]
  have hconst :
      (∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF 2 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x)) =
        ∫⁻ y : ℝ in Set.Icc 0 x,
          ENNReal.ofReal ((rate ^ 3 * Real.exp (-(rate * x))) * y) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact gammaPDF_two_exp_integrand_eq_const_mul_id hrate hy
  rw [hconst,
    lintegral_ofReal_mul_id_Icc (by positivity) hx,
    ProbabilityTheory.gammaPDF_of_nonneg hx, gamma_three]
  norm_num [Real.rpow_two]
  congr 1
  ring

/-- Pointwise density identity for the finite shape-two-to-three Gamma step. -/
theorem gammaPDF_two_lconvolution_exp_eq_gammaPDF_three
    {rate : ℝ} (hrate : 0 < rate) (x : ℝ) :
    (ProbabilityTheory.gammaPDF 2 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 3 rate x := by
  by_cases hx : 0 ≤ x
  · exact gammaPDF_two_lconvolution_exp_eq_gammaPDF_three_of_nonneg hrate hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [gammaPDF_two_lconvolution_exp_eq_zero_of_neg hxneg,
      ProbabilityTheory.gammaPDF_of_neg hxneg]

/-- A shape-two Gamma law plus one exponential gap is a shape-three Gamma law. -/
theorem gammaMeasure_two_conv_expMeasure_eq_gammaMeasure_three
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.gammaMeasure 2 rate ∗ ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure 3 rate := by
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [MeasureTheory.conv_withDensity_eq_lconvolution
      (measurable_gammaPDF 2 rate) (measurable_gammaPDF 1 rate),
    MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (MeasureTheory.measurable_lconvolution volume
        (measurable_gammaPDF 2 rate) (measurable_gammaPDF 1 rate)).aemeasurable
      (measurable_gammaPDF 3 rate).aemeasurable]
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [← exponentialPDF_eq_gammaPDF_one] using
      (gammaPDF_two_lconvolution_exp_eq_gammaPDF_three hrate x))

/-- The three-gap canonical arrival time has the shape-three Gamma law. -/
theorem arrivalTime_two_hasLaw_gammaMeasure_three
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (arrivalTime 2)
      (ProbabilityTheory.gammaMeasure 3 rate)
      (exponentialInterarrivalMeasure rate) := by
  have h := arrivalTime_hasLaw_erlangConvolution hrate 2
  simpa [erlangConvolutionMeasure, expMeasure_conv_expMeasure_eq_gammaMeasure_two hrate,
    gammaMeasure_two_conv_expMeasure_eq_gammaMeasure_three hrate] using h

/-- The third post-tag epoch is the same three-gap Gamma arrival time. -/
theorem postTagArrival_three_hasLaw_gammaMeasure_three
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (postTagArrival 3)
      (ProbabilityTheory.gammaMeasure 3 rate)
      (exponentialInterarrivalMeasure rate) := by
  simpa [postTagArrival] using
    (arrivalTime_two_hasLaw_gammaMeasure_three hrate)

/-- The quadratic compact-interval `lintegral` used by the shape-three-to-four step. -/
theorem lintegral_ofReal_mul_sq_Icc
    {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    (∫⁻ y : ℝ in Set.Icc 0 x, ENNReal.ofReal (c * y ^ 2)) =
      ENNReal.ofReal (c * (x ^ 3 / 3)) := by
  have h_int : Integrable (fun y : ℝ => c * y ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) x)) := by
    simpa [IntegrableOn] using
      ((continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc
        (a := (0 : ℝ)) (b := x) (μ := volume))
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) x)]
      (fun y : ℝ => c * y ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_nonneg hc (sq_nonneg y)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  congr 1
  have h_set_integral :
      (∫ y : ℝ in Set.Icc 0 x, c * y ^ 2) =
        ∫ y : ℝ in (0 : ℝ)..x, c * y ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx]
  rw [h_set_integral, intervalIntegral.integral_const_mul]
  have hpow : (∫ y : ℝ in (0 : ℝ)..x, y ^ 2) = x ^ 3 / 3 := by
    rw [integral_pow]
    norm_num
  rw [hpow]

/-- The support reduction shared by each finite Gamma--exponential step. -/
theorem gammaPDF_lconvolution_exp_eq_setLIntegral_Icc
    (shape rate x : ℝ) :
    (ProbabilityTheory.gammaPDF shape rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF shape rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.gammaPDF shape rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
        ∫⁻ y : ℝ, (Set.Icc (0 : ℝ) x).indicator
          (fun z => ProbabilityTheory.gammaPDF shape rate z *
            ProbabilityTheory.exponentialPDF rate (-z + x)) y := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) x
      · simp [hy]
      · rw [Set.indicator_of_notMem hy]
        have houtside : y < 0 ∨ x < y := by
          by_cases hyneg : y < 0
          · exact Or.inl hyneg
          · right
            have hynonneg : 0 ≤ y := le_of_not_gt hyneg
            have hnotle : ¬ y ≤ x := by
              intro hle
              exact hy ⟨hynonneg, hle⟩
            exact lt_of_not_ge hnotle
        rcases houtside with hyneg | hgt
        · rw [ProbabilityTheory.gammaPDF_of_neg hyneg]
          simp
        · have hshift_neg : -y + x < 0 := by linarith
          rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
          simp
    _ = ∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF shape rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) :=
      MeasureTheory.lintegral_indicator measurableSet_Icc _

/-- The corresponding negative branch of any finite Gamma--exponential step. -/
theorem gammaPDF_lconvolution_exp_eq_zero_of_neg
    {shape rate x : ℝ} (hx : x < 0) :
    (ProbabilityTheory.gammaPDF shape rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x = 0 := by
  rw [MeasureTheory.lconvolution_def]
  calc
    ∫⁻ y : ℝ, ProbabilityTheory.gammaPDF shape rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) = ∫⁻ _ : ℝ, 0 := by
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y < 0
      · rw [ProbabilityTheory.gammaPDF_of_neg hy]
        simp
      · have hy_nonneg : 0 ≤ y := le_of_not_gt hy
        have hshift_neg : -y + x < 0 := by linarith
        rw [ProbabilityTheory.exponentialPDF_of_neg hshift_neg]
        simp
    _ = 0 := MeasureTheory.lintegral_zero

/-- The shape-four Gamma normalization. -/
theorem gamma_four : Real.Gamma 4 = 6 := by
  have h := Real.Gamma_nat_eq_factorial 3
  norm_num at h ⊢

/-- Algebra in the positive simplex for the shape-three-to-four Gamma step. -/
theorem gammaPDF_three_exp_integrand_eq_const_mul_sq
    {rate x y : ℝ} (hrate : 0 < rate) (hyx : y ∈ Set.Icc 0 x) :
    ProbabilityTheory.gammaPDF 3 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
      ENNReal.ofReal ((rate ^ 4 / 2 * Real.exp (-(rate * x))) * y ^ 2) := by
  have hy_nonneg : 0 ≤ y := hyx.1
  have hshift_nonneg : 0 ≤ -y + x := by linarith [hyx.2]
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy_nonneg,
    ProbabilityTheory.exponentialPDF_of_nonneg hshift_nonneg, gamma_three]
  norm_num [Real.rpow_two]
  have hfirst_nonneg : 0 ≤ rate ^ 3 / 2 * y ^ 2 * Real.exp (-(rate * y)) := by positivity
  rw [← ENNReal.ofReal_mul hfirst_nonneg]
  congr 1
  calc
    rate ^ 3 / 2 * y ^ 2 * Real.exp (-(rate * y)) *
        (rate * Real.exp (-(rate * (-y + x)))) =
      (rate ^ 4 / 2) * y ^ 2 *
        (Real.exp (-(rate * y)) * Real.exp (-(rate * (-y + x)))) := by
        ring
    _ = (rate ^ 4 / 2 * Real.exp (-(rate * x))) * y ^ 2 := by
        rw [← Real.exp_add]
        have harg : -(rate * y) + -(rate * (-y + x)) = -(rate * x) := by ring
        rw [harg]
        ring

/-- The positive branch of the finite shape-three-to-four Gamma convolution. -/
theorem gammaPDF_three_lconvolution_exp_eq_gammaPDF_four_of_nonneg
    {rate x : ℝ} (hrate : 0 < rate) (hx : 0 ≤ x) :
    (ProbabilityTheory.gammaPDF 3 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 4 rate x := by
  rw [gammaPDF_lconvolution_exp_eq_setLIntegral_Icc]
  have hconst :
      (∫⁻ y : ℝ in Set.Icc 0 x, ProbabilityTheory.gammaPDF 3 rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x)) =
        ∫⁻ y : ℝ in Set.Icc 0 x,
          ENNReal.ofReal ((rate ^ 4 / 2 * Real.exp (-(rate * x))) * y ^ 2) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact gammaPDF_three_exp_integrand_eq_const_mul_sq hrate hy
  rw [hconst,
    lintegral_ofReal_mul_sq_Icc (by positivity) hx,
    ProbabilityTheory.gammaPDF_of_nonneg hx, gamma_four]
  norm_num [Real.rpow_natCast]
  congr 1
  ring

/-- Pointwise density identity for the finite shape-three-to-four Gamma step. -/
theorem gammaPDF_three_lconvolution_exp_eq_gammaPDF_four
    {rate : ℝ} (hrate : 0 < rate) (x : ℝ) :
    (ProbabilityTheory.gammaPDF 3 rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF 4 rate x := by
  by_cases hx : 0 ≤ x
  · exact gammaPDF_three_lconvolution_exp_eq_gammaPDF_four_of_nonneg hrate hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [gammaPDF_lconvolution_exp_eq_zero_of_neg hxneg,
      ProbabilityTheory.gammaPDF_of_neg hxneg]

/-- A shape-three Gamma law plus one exponential gap is a shape-four Gamma law. -/
theorem gammaMeasure_three_conv_expMeasure_eq_gammaMeasure_four
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.gammaMeasure 3 rate ∗ ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure 4 rate := by
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [MeasureTheory.conv_withDensity_eq_lconvolution
      (measurable_gammaPDF 3 rate) (measurable_gammaPDF 1 rate),
    MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (MeasureTheory.measurable_lconvolution volume
        (measurable_gammaPDF 3 rate) (measurable_gammaPDF 1 rate)).aemeasurable
      (measurable_gammaPDF 4 rate).aemeasurable]
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [← exponentialPDF_eq_gammaPDF_one] using
      (gammaPDF_three_lconvolution_exp_eq_gammaPDF_four hrate x))

/-- The four-gap canonical arrival time has the shape-four Gamma law. -/
theorem arrivalTime_three_hasLaw_gammaMeasure_four
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (arrivalTime 3)
      (ProbabilityTheory.gammaMeasure 4 rate)
      (exponentialInterarrivalMeasure rate) := by
  have h := arrivalTime_hasLaw_erlangConvolution hrate 3
  simpa [erlangConvolutionMeasure, expMeasure_conv_expMeasure_eq_gammaMeasure_two hrate,
    gammaMeasure_two_conv_expMeasure_eq_gammaMeasure_three hrate,
    gammaMeasure_three_conv_expMeasure_eq_gammaMeasure_four hrate] using h

/-- The fourth post-tag epoch is the same four-gap Gamma arrival time. -/
theorem postTagArrival_four_hasLaw_gammaMeasure_four
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (postTagArrival 4)
      (ProbabilityTheory.gammaMeasure 4 rate)
      (exponentialInterarrivalMeasure rate) := by
  simpa [postTagArrival] using
    (arrivalTime_three_hasLaw_gammaMeasure_four hrate)

/-- The finite polynomial integral needed for every integer-shape Gamma step. -/
theorem lintegral_ofReal_mul_pow_Icc
    {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (n : ℕ) :
    (∫⁻ y : ℝ in Set.Icc 0 x, ENNReal.ofReal (c * y ^ n)) =
      ENNReal.ofReal (c * (x ^ (n + 1) / ((n : ℝ) + 1))) := by
  have h_int : Integrable (fun y : ℝ => c * y ^ n)
      (volume.restrict (Set.Icc (0 : ℝ) x)) := by
    simpa [IntegrableOn] using
      ((continuous_const.mul (continuous_id.pow n)).integrableOn_Icc
        (a := (0 : ℝ)) (b := x) (μ := volume))
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) x)]
      (fun y : ℝ => c * y ^ n) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_nonneg hc (pow_nonneg hy.1 n)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  congr 1
  have h_set_integral :
      (∫ y : ℝ in Set.Icc 0 x, c * y ^ n) =
        ∫ y : ℝ in (0 : ℝ)..x, c * y ^ n := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx]
  rw [h_set_integral, intervalIntegral.integral_const_mul, integral_pow]
  simp

/-- Algebra in the positive convolution simplex for an arbitrary positive
integer Gamma shape. -/
theorem gammaPDF_nat_succ_exp_integrand_eq_const_mul_pow
    {rate x y : ℝ} (n : ℕ) (hrate : 0 < rate) (hyx : y ∈ Set.Icc 0 x) :
    ProbabilityTheory.gammaPDF ((n : ℝ) + 1) rate y *
        ProbabilityTheory.exponentialPDF rate (-y + x) =
      ENNReal.ofReal
        ((rate ^ (n + 2) / (n.factorial : ℝ) * Real.exp (-(rate * x))) * y ^ n) := by
  have hy_nonneg : 0 ≤ y := hyx.1
  have hshift_nonneg : 0 ≤ -y + x := by linarith [hyx.2]
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy_nonneg,
    ProbabilityTheory.exponentialPDF_of_nonneg hshift_nonneg,
    Real.Gamma_nat_eq_factorial n]
  have hshape : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  have hpower : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
  rw [hpower, Real.rpow_natCast, hshape, Real.rpow_natCast]
  have hfirst_nonneg :
      0 ≤ rate ^ (n + 1) / (n.factorial : ℝ) * y ^ n *
        Real.exp (-(rate * y)) := by positivity
  rw [← ENNReal.ofReal_mul hfirst_nonneg]
  congr 1
  calc
    rate ^ (n + 1) / (n.factorial : ℝ) * y ^ n * Real.exp (-(rate * y)) *
        (rate * Real.exp (-(rate * (-y + x)))) =
      (rate ^ (n + 2) / (n.factorial : ℝ)) * y ^ n *
        (Real.exp (-(rate * y)) * Real.exp (-(rate * (-y + x)))) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
    _ = (rate ^ (n + 2) / (n.factorial : ℝ) *
        Real.exp (-(rate * x))) * y ^ n := by
        rw [← Real.exp_add]
        have harg : -(rate * y) + -(rate * (-y + x)) = -(rate * x) := by ring
        rw [harg]
        ring

/-- The positive branch of the generic integer-shape Gamma induction step. -/
theorem gammaPDF_nat_succ_lconvolution_exp_eq_gammaPDF_nat_succ_succ_of_nonneg
    {rate x : ℝ} (n : ℕ) (hrate : 0 < rate) (hx : 0 ≤ x) :
    (ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF ((n + 2 : ℕ) : ℝ) rate x := by
  rw [gammaPDF_lconvolution_exp_eq_setLIntegral_Icc]
  have hconst :
      (∫⁻ y : ℝ in Set.Icc 0 x,
        ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate y *
          ProbabilityTheory.exponentialPDF rate (-y + x)) =
        ∫⁻ y : ℝ in Set.Icc 0 x,
          ENNReal.ofReal
            ((rate ^ (n + 2) / (n.factorial : ℝ) *
              Real.exp (-(rate * x))) * y ^ n) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    simpa only [Nat.cast_add, Nat.cast_one] using
      (gammaPDF_nat_succ_exp_integrand_eq_const_mul_pow n hrate hy)
  rw [hconst, lintegral_ofReal_mul_pow_Icc (by positivity) hx n,
    ProbabilityTheory.gammaPDF_of_nonneg hx]
  have hshape_gamma : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hpower : ((n + 1 : ℕ) : ℝ) + 1 - 1 = ((n + 1 : ℕ) : ℝ) := by ring
  have hshape_rate : ((n + 1 : ℕ) : ℝ) + 1 = ((n + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hshape_gamma, Real.Gamma_nat_eq_factorial (n + 1), hpower,
    Real.rpow_natCast, hshape_rate, Real.rpow_natCast]
  have hfac_succ : ((n + 1).factorial : ℝ) =
      ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ n
  rw [hfac_succ]
  congr 1
  have hfac_ne : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsucc_ne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hfac_ne, hsucc_ne]

/-- Pointwise density form of the general positive-integer Gamma induction step. -/
theorem gammaPDF_nat_succ_lconvolution_exp_eq_gammaPDF_nat_succ_succ
    {rate : ℝ} (n : ℕ) (hrate : 0 < rate) (x : ℝ) :
    (ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate ⋆ₗ[volume]
      ProbabilityTheory.exponentialPDF rate) x =
      ProbabilityTheory.gammaPDF ((n + 2 : ℕ) : ℝ) rate x := by
  by_cases hx : 0 ≤ x
  · exact gammaPDF_nat_succ_lconvolution_exp_eq_gammaPDF_nat_succ_succ_of_nonneg
      n hrate hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [gammaPDF_lconvolution_exp_eq_zero_of_neg hxneg,
      ProbabilityTheory.gammaPDF_of_neg hxneg]

/-- Convolution of an integer-shape Gamma law with one exponential gap. -/
theorem gammaMeasure_nat_succ_conv_expMeasure_eq_gammaMeasure_nat_succ_succ
    {rate : ℝ} (n : ℕ) (hrate : 0 < rate) :
    ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate ∗
        ProbabilityTheory.expMeasure rate =
      ProbabilityTheory.gammaMeasure ((n + 2 : ℕ) : ℝ) rate := by
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [MeasureTheory.conv_withDensity_eq_lconvolution
      (measurable_gammaPDF ((n + 1 : ℕ) : ℝ) rate)
      (measurable_gammaPDF 1 rate),
    MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (MeasureTheory.measurable_lconvolution volume
        (measurable_gammaPDF ((n + 1 : ℕ) : ℝ) rate)
        (measurable_gammaPDF 1 rate)).aemeasurable
      (measurable_gammaPDF ((n + 2 : ℕ) : ℝ) rate).aemeasurable]
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [← exponentialPDF_eq_gammaPDF_one] using
      (gammaPDF_nat_succ_lconvolution_exp_eq_gammaPDF_nat_succ_succ n hrate x))

/-- The finite Erlang convolution is the corresponding positive integer-shape Gamma law. -/
theorem erlangConvolutionMeasure_eq_gammaMeasure_nat_succ
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    erlangConvolutionMeasure rate n =
      ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate := by
  induction n with
  | zero =>
      simp only [erlangConvolutionMeasure]
      norm_num [ProbabilityTheory.expMeasure]
  | succ n ih =>
      rw [erlangConvolutionMeasure, ih,
        gammaMeasure_nat_succ_conv_expMeasure_eq_gammaMeasure_nat_succ_succ n hrate]

/-- Every finite canonical arrival epoch has the integer-shape Gamma law. -/
theorem arrivalTime_hasLaw_gammaMeasure_nat_succ
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (arrivalTime n)
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate)
      (exponentialInterarrivalMeasure rate) := by
  have h := arrivalTime_hasLaw_erlangConvolution hrate n
  rw [erlangConvolutionMeasure_eq_gammaMeasure_nat_succ hrate n] at h
  exact h

/-- The positive post-tag epochs have the corresponding integer-shape Gamma laws. -/
theorem postTagArrival_succ_hasLaw_gammaMeasure_nat_succ
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (postTagArrival (n + 1))
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate)
      (exponentialInterarrivalMeasure rate) := by
  simpa [postTagArrival] using
    (arrivalTime_hasLaw_gammaMeasure_nat_succ hrate n)

end
end PoissonProcess
end Probability
end AppliedModelingLib
