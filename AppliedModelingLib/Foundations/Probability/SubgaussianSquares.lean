import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Math.ExponentialBounds

/-!
# Squared Sub-Gaussian Variables

Reusable moment bounds that turn a variance-one sub-Gaussian random variable
on a finite probability space into a centered square with a local quadratic
moment-generating-function estimate.
-/

open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib
namespace Probability

/--
On a finite probability space, the exponential square moment of a real random
variable with variance-one sub-Gaussian MGF is dominated by the corresponding
standard-Gaussian moment.  The proof uses the Gaussian auxiliary-variable
identity and Fubini's theorem.
-/
theorem integral_exp_mul_sq_le_inv_sqrt_one_sub_two_mul_of_hasSubgaussianMGF_one
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasSubgaussianMGF X 1 μ) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_lt : lambda < 1 / 2) :
    (∫ omega, Real.exp (lambda * X omega ^ 2) ∂μ) ≤
      (Real.sqrt (1 - 2 * lambda))⁻¹ := by
  let f : ℝ → Ω → ℝ := fun g omega =>
    Real.exp (Real.sqrt (2 * lambda) * g * X omega)
  have hfmeas : Measurable (Function.uncurry f) := by
    dsimp [f]
    exact Measurable.exp ((measurable_const.mul measurable_fst).mul
      ((measurable_of_finite X).comp measurable_snd))
  have hfint : Integrable (Function.uncurry f) ((gaussianReal 0 1).prod μ) := by
    rw [integrable_prod_iff' hfmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [] with omega
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using
        (integrable_exp_mul_gaussianReal (μ := 0) (v := 1)
          (Real.sqrt (2 * lambda) * X omega))
    · exact Integrable.of_finite
  have hgaussint : Integrable (fun g : ℝ => Real.exp (lambda * g ^ 2))
      (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
    rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top (μ := 0) (v := 1))]
    simp_rw [toReal_gaussianPDF]
    simp only [gaussianPDFReal]
    norm_num
    rw [show (fun g : ℝ =>
        Real.exp (lambda * g ^ 2) * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
          Real.exp (-g ^ 2 / 2))) =
        fun g : ℝ => ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          Real.exp (-(1 / 2 - lambda) * g ^ 2) by
        ext g
        rw [show Real.exp (lambda * g ^ 2) * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
            Real.exp (-g ^ 2 / 2)) =
            ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
              (Real.exp (lambda * g ^ 2) * Real.exp (-g ^ 2 / 2)) by ring]
        rw [← Real.exp_add]
        congr 1
        ring_nf]
    exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _
  have hHS (omega : Ω) :
      (∫ g : ℝ, f g omega ∂gaussianReal 0 1) =
        Real.exp (lambda * X omega ^ 2) := by
    dsimp [f]
    rw [show (fun g : ℝ =>
        Real.exp (Real.sqrt (2 * lambda) * g * X omega)) =
        fun g : ℝ => Real.exp ((Real.sqrt (2 * lambda) * X omega) * g) by
        ext g
        congr 1
        ring]
    change mgf id (gaussianReal 0 1)
      (Real.sqrt (2 * lambda) * X omega) = _
    rw [mgf_id_gaussianReal]
    simp only [zero_mul]
    congr 1
    rw [mul_pow]
    rw [show Real.sqrt (2 * lambda) ^ 2 = 2 * lambda by
      exact Real.sq_sqrt (by positivity)]
    norm_num
    ring
  have hinner (g : ℝ) :
      (∫ omega, f g omega ∂μ) ≤ Real.exp (lambda * g ^ 2) := by
    change mgf X μ (Real.sqrt (2 * lambda) * g) ≤ _
    calc
      mgf X μ (Real.sqrt (2 * lambda) * g) ≤
          Real.exp (((1 : NNReal) : ℝ) * (Real.sqrt (2 * lambda) * g) ^ 2 / 2) :=
        hX.mgf_le _
      _ = Real.exp (lambda * g ^ 2) := by
        congr 1
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        norm_num
        ring
  calc
    (∫ omega, Real.exp (lambda * X omega ^ 2) ∂μ) =
        ∫ omega, ∫ g : ℝ, f g omega ∂gaussianReal 0 1 ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with omega
          exact (hHS omega).symm
    _ = ∫ g : ℝ, ∫ omega, f g omega ∂μ ∂gaussianReal 0 1 := by
          calc
            (∫ omega, ∫ g : ℝ, f g omega ∂gaussianReal 0 1 ∂μ) =
                ∫ z : Ω × ℝ, f z.2 z.1 ∂(μ.prod (gaussianReal 0 1)) := by
                  have hswap :
                      Integrable (Function.uncurry (fun omega (g : ℝ) => f g omega))
                        (μ.prod (gaussianReal 0 1)) := by
                    simpa [Function.uncurry, Function.comp_def] using hfint.swap
                  exact integral_integral hswap
            _ = ∫ g : ℝ, ∫ omega, f g omega ∂μ ∂gaussianReal 0 1 := by
                  simpa using (integral_integral_symm hfint).symm
    _ ≤ ∫ g : ℝ, Real.exp (lambda * g ^ 2) ∂gaussianReal 0 1 := by
          apply integral_mono
          · exact hfint.integral_prod_left
          · exact hgaussint
          · exact hinner
    _ = (Real.sqrt (1 - 2 * lambda))⁻¹ := by
          rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
          simp only [smul_eq_mul, gaussianPDFReal]
          norm_num
          rw [show (fun g : ℝ =>
              (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
                Real.exp (-g ^ 2 / 2) * Real.exp (lambda * g ^ 2)) =
              fun g : ℝ => ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
                (Real.exp (-g ^ 2 / 2) * Real.exp (lambda * g ^ 2)) by
              ext g
              ring]
          rw [integral_const_mul]
          have hrewrite :
              (fun g : ℝ =>
                Real.exp (-g ^ 2 / 2) * Real.exp (lambda * g ^ 2)) =
                fun g : ℝ => Real.exp (-(1 / 2 - lambda) * g ^ 2) := by
            ext g
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hrewrite, integral_gaussian]
          have hb : 0 < 1 / 2 - lambda := by linarith
          have hpos : 0 < 1 - 2 * lambda := by linarith
          have hsqrt_two : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
          have hsqrt_pi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
            Real.sq_sqrt Real.pi_pos.le
          have hsqrt_pi_div : (Real.sqrt (Real.pi / (1 / 2 - lambda))) ^ 2 =
              Real.pi / (1 / 2 - lambda) :=
            Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)
          have hsqrt_one : (Real.sqrt (1 - 2 * lambda)) ^ 2 = 1 - 2 * lambda :=
            Real.sq_sqrt hpos.le
          field_simp
          apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
          rw [mul_pow]
          rw [Real.sq_sqrt]
          · rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt]
            · field_simp
              nlinarith
            · positivity
            · positivity
          · positivity

/-- A scalar MGF estimate valid on the quarter-radius interval. -/
theorem exp_neg_mul_inv_sqrt_one_sub_two_mul_le_exp_four_mul_sq
    (t : ℝ) (ht0 : 0 ≤ t) (htquarter : t ≤ 1 / 4) :
    Real.exp (-t) * (Real.sqrt (1 - 2 * t))⁻¹ ≤ Real.exp (4 * t ^ 2) := by
  have hq_pos : 0 < 1 - 2 * t := by linarith
  have hlog : -Real.log (1 - 2 * t) ≤ (2 * t) / (1 - 2 * t) := by
    exact AppliedModelingLib.Math.neg_log_one_sub_le_div_self (by linarith) (by linarith)
  have hsqrt : Real.sqrt (1 - 2 * t) = Real.exp (Real.log (1 - 2 * t) / 2) :=
    (AppliedModelingLib.Math.exp_log_div_two_eq_sqrt hq_pos).symm
  rw [hsqrt, ← Real.exp_neg]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hrepr : -t + t / (1 - 2 * t) = (2 * t ^ 2) / (1 - 2 * t) := by
    apply (eq_div_iff (ne_of_gt hq_pos)).mpr
    rw [show (-t + t / (1 - 2 * t)) * (1 - 2 * t) =
        t * (-(1 - 2 * t) + (1 - 2 * t) * (1 / (1 - 2 * t))) by ring]
    rw [one_div, mul_inv_cancel₀ (ne_of_gt hq_pos)]
    ring
  have hterm : (2 * t ^ 2) / (1 - 2 * t) ≤ 4 * t ^ 2 := by
    rw [div_le_iff₀ hq_pos]
    nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ 1 - 4 * t)]
  calc
    -t + -(Real.log (1 - 2 * t) / 2) ≤
        -t + ((2 * t) / (1 - 2 * t)) / 2 := by linarith
    _ = -t + t / (1 - 2 * t) := by ring
    _ = (2 * t ^ 2) / (1 - 2 * t) := hrepr
    _ ≤ 4 * t ^ 2 := hterm

/--
The centered square of a variance-one sub-Gaussian random variable on a finite
probability space has a quadratic MGF bound on the interval `[0, 1/4]`.
-/
theorem integral_exp_mul_centered_sq_le_exp_four_mul_sq_of_hasSubgaussianMGF_one
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasSubgaussianMGF X 1 μ) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_quarter : lambda ≤ 1 / 4) :
    (∫ omega, Real.exp (lambda * (X omega ^ 2 - 1)) ∂μ) ≤
      Real.exp (4 * lambda ^ 2) := by
  calc
    (∫ omega, Real.exp (lambda * (X omega ^ 2 - 1)) ∂μ) =
        Real.exp (-lambda) *
          ∫ omega, Real.exp (lambda * X omega ^ 2) ∂μ := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with omega
            rw [← Real.exp_add]
            congr 1
            ring
    _ ≤ Real.exp (-lambda) * (Real.sqrt (1 - 2 * lambda))⁻¹ := by
          gcongr
          exact integral_exp_mul_sq_le_inv_sqrt_one_sub_two_mul_of_hasSubgaussianMGF_one
            μ X hX lambda hlambda (by linarith)
    _ ≤ Real.exp (4 * lambda ^ 2) := by
          exact exp_neg_mul_inv_sqrt_one_sub_two_mul_le_exp_four_mul_sq
            lambda hlambda hlambda_quarter

/-- A truncation remainder estimate used to obtain a lower-tail bound from a square MGF. -/
theorem sub_min_le_eight_mul_exp_neg_eight_mul_exp_quarter (u : ℝ) (hu : 0 ≤ u) :
    u - min u 64 ≤ 8 * Real.exp (-8) * Real.exp (u / 4) := by
  by_cases h : u ≤ 64
  · rw [min_eq_left h]
    have hpos : 0 < 8 * Real.exp (-8) * Real.exp (u / 4) := by positivity
    simpa using hpos.le
  · have h64 : 64 ≤ u := le_of_not_ge h
    have hlinear : u ≤ 8 * Real.exp (u / 8) := by
      have h := Real.le_inv_mul_exp u (by norm_num : (0 : ℝ) < 1 / 8)
      convert h using 1
      all_goals ring_nf
    have hexp : Real.exp (u / 8) ≤ Real.exp (-8) * Real.exp (u / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      u - min u 64 ≤ u := sub_le_self u (le_min hu (by norm_num))
      _ ≤ 8 * Real.exp (u / 8) := hlinear
      _ ≤ 8 * (Real.exp (-8) * Real.exp (u / 4)) := by gcongr
      _ = _ := by ring

/-- A numerical bound for the truncation remainder at level `64`. -/
theorem eight_mul_exp_neg_eight_mul_two_le_one_sixteenth :
    8 * Real.exp (-8) * 2 ≤ 1 / 16 := by
  have hpow : (2 : ℝ) ^ 8 < (Real.exp 1) ^ 8 := by
    exact pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
  have hexp : (256 : ℝ) < Real.exp 8 := by
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    norm_num at hpow ⊢
    exact hpow
  have hinv : Real.exp (-8) < (1 / 256 : ℝ) := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (by positivity) (by positivity)]
    simpa using hexp
  nlinarith [Real.exp_pos (-8)]

/--
If a variance-one sub-Gaussian real variable has exact second moment one, its
square retains at least `15/16` of its expectation after truncation at `64`.
This bounded surrogate supports lower-tail concentration without a fourth
moment assumption.
-/
theorem integral_min_sq_sixty_four_ge_fifteen_sixteenths_of_hasSubgaussianMGF_one
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasSubgaussianMGF X 1 μ)
    (hsecond : (∫ omega, X omega ^ 2 ∂μ) = 1) :
    15 / 16 ≤ (∫ omega, min (X omega ^ 2) 64 ∂μ) := by
  have hmgf :=
    integral_exp_mul_sq_le_inv_sqrt_one_sub_two_mul_of_hasSubgaussianMGF_one
      μ X hX (1 / 4) (by norm_num) (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt (1 - 2 * (1 / 4 : ℝ)) := by positivity
  have hsqrt_sq : (Real.sqrt (1 - 2 * (1 / 4 : ℝ))) ^ 2 = 1 - 2 * (1 / 4 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hmgf_two :
      (∫ omega, Real.exp (X omega ^ 2 / 4) ∂μ) ≤ 2 := by
    calc
      (∫ omega, Real.exp (X omega ^ 2 / 4) ∂μ) =
          (∫ omega, Real.exp ((1 / 4 : ℝ) * X omega ^ 2) ∂μ) := by
            apply integral_congr_ae
            filter_upwards [] with omega
            congr 1
            ring
      _ ≤ (Real.sqrt (1 - 2 * (1 / 4 : ℝ)))⁻¹ := hmgf
      _ ≤ 2 := by
            rw [inv_le_iff_one_le_mul₀ hsqrt_pos]
            nlinarith
  have htail :
      (∫ omega, X omega ^ 2 - min (X omega ^ 2) 64 ∂μ) ≤ 1 / 16 := by
    calc
      (∫ omega, X omega ^ 2 - min (X omega ^ 2) 64 ∂μ) ≤
          ∫ omega, 8 * Real.exp (-8) * Real.exp (X omega ^ 2 / 4) ∂μ := by
            apply integral_mono
            · exact Integrable.of_finite
            · exact Integrable.of_finite
            · intro omega
              exact sub_min_le_eight_mul_exp_neg_eight_mul_exp_quarter
                (X omega ^ 2) (sq_nonneg _)
      _ = (8 * Real.exp (-8)) *
          ∫ omega, Real.exp (X omega ^ 2 / 4) ∂μ := by
            rw [integral_const_mul]
      _ ≤ (8 * Real.exp (-8)) * 2 := by
            gcongr
      _ ≤ 1 / 16 := by
            exact eight_mul_exp_neg_eight_mul_two_le_one_sixteenth
  have hsplit :
      (∫ omega, X omega ^ 2 - min (X omega ^ 2) 64 ∂μ) =
        (∫ omega, X omega ^ 2 ∂μ) - (∫ omega, min (X omega ^ 2) 64 ∂μ) := by
    rw [integral_sub] <;> exact Integrable.of_finite
  linarith

/--
Chernoff's bound for a finite independent family when each summand has a
specified MGF bound at the selected nonnegative tilt.
-/
theorem measure_sum_ge_le_exp_of_iIndepFun_mgf_le
    {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : I → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset I) (t epsilon kappa : ℝ) (ht : 0 ≤ t)
    (h_int : ∀ i ∈ s, Integrable (fun omega => Real.exp (t * X i omega)) μ)
    (h_mgf : ∀ i ∈ s, mgf (X i) μ t ≤ Real.exp kappa) :
    μ.real {omega | epsilon ≤ ∑ i ∈ s, X i omega} ≤
      Real.exp (-t * epsilon + (s.card : ℝ) * kappa) := by
  have hsumint : Integrable (fun omega => Real.exp (t * (∑ i ∈ s, X i) omega)) μ :=
    h_indep.integrable_exp_mul_sum h_meas h_int
  calc
    μ.real {omega | epsilon ≤ ∑ i ∈ s, X i omega} ≤
        Real.exp (-t * epsilon) * mgf (∑ i ∈ s, X i) μ t :=
      by simpa only [Finset.sum_apply] using
        (measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) epsilon ht hsumint)
    _ = Real.exp (-t * epsilon) * ∏ i ∈ s, mgf (X i) μ t := by
      rw [h_indep.mgf_sum h_meas]
    _ ≤ Real.exp (-t * epsilon) * ∏ _i ∈ s, Real.exp kappa := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i hi => h_mgf i hi)
    _ = Real.exp (-t * epsilon + (s.card : ℝ) * kappa) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]

end Probability
end AppliedModelingLib
