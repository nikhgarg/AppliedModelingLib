import AppliedModelingLib.Queueing.ManyServerPoisson
import AppliedModelingLib.Foundations.Probability.PoissonChernoff
import AppliedModelingLib.Foundations.Probability.GaussianMathlib
import AppliedModelingLib.Foundations.Probability.WeakConvergenceCDF
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Analytic tools for Poisson queue asymptotics

This module begins the reusable analytic layer needed for many-server QED
limits.  Its first result is the exact characteristic function of a Poisson
law; diffusion and local-limit consequences are developed separately.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Real Topology

/-- The characteristic function of a Poisson law. -/
theorem poissonMeasure_charFun (mean : ℝ≥0) (t : ℝ) :
    charFun (Measure.map (fun n : ℕ => (n : ℝ)) (poissonMeasure mean)) t =
      Complex.exp ((mean : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  rw [charFun_apply,
    integral_map ((Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).aemeasurable)
      (by fun_prop),
    integral_poissonMeasure]
  change (∑' n : ℕ,
    (↑(Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ n / (n.factorial : ℝ)) : ℂ) *
      Complex.exp ((↑(t * (n : ℝ)) : ℂ) * Complex.I)) = _
  have hterm (n : ℕ) :
      (↑(Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ n / (n.factorial : ℝ)) : ℂ) *
          Complex.exp ((↑(t * (n : ℝ)) : ℂ) * Complex.I) =
        Complex.exp (-(mean : ℂ)) *
          (((mean : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ n / (n.factorial : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_neg, Complex.ofReal_pow]
    have hfactorial : (↑(n.factorial : ℝ) : ℂ) = (n.factorial : ℂ) := by
      norm_cast
    have hangle : (↑(t * (n : ℝ)) : ℂ) = (n : ℂ) * (t : ℂ) := by
      norm_cast
      ring
    rw [hfactorial, hangle, mul_assoc, Complex.exp_nat_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hexpSeries (z : ℂ) :
      (∑' n : ℕ, z ^ n / (n.factorial : ℂ)) = Complex.exp z := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [hexpSeries]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The real-valued version of a Poisson law. -/
noncomputable def poissonRealMeasure (mean : ℝ≥0) : Measure ℝ :=
  Measure.map (fun n : ℕ => (n : ℝ)) (poissonMeasure mean)

/-- A Poisson variable centered by its mean and normalized by its standard
deviation. -/
noncomputable def poissonCenteredScaledMeasure (mean : ℝ≥0) : Measure ℝ :=
  Measure.map (fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / Real.sqrt mean)
    (poissonMeasure mean)

/-- The centered and scaled Poisson law is an affine image of its
real-valued version. -/
theorem poissonCenteredScaledMeasure_eq_affine
    {mean : ℝ≥0} (hmean : 0 < mean) :
    poissonCenteredScaledMeasure mean =
      Measure.map (fun x : ℝ => x + -Real.sqrt mean)
        (Measure.map (fun x : ℝ => (Real.sqrt mean)⁻¹ * x)
          (poissonRealMeasure mean)) := by
  let f : ℕ → ℝ := fun n => (n : ℝ)
  let g : ℝ → ℝ := fun x => (Real.sqrt mean)⁻¹ * x
  let h : ℝ → ℝ := fun x => x + -Real.sqrt mean
  have hf : Measurable f := Measurable.of_discrete
  have hg : Measurable g := by fun_prop
  have hh : Measurable h := by fun_prop
  rw [show poissonRealMeasure mean = Measure.map f (poissonMeasure mean) by rfl,
    Measure.map_map hh hg, Measure.map_map (hh.comp hg) hf]
  apply Measure.map_congr
  filter_upwards with n
  simp only [Function.comp_apply, f, g, h]
  have hsqrt_ne : Real.sqrt (mean : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmean))
  have hsquare : Real.sqrt (mean : ℝ) ^ 2 = (mean : ℝ) :=
    Real.sq_sqrt (by positivity)
  field_simp [hsqrt_ne]
  nlinarith

/-- Exact characteristic function of a centered, variance-one Poisson law. -/
theorem poissonCenteredScaledMeasure_charFun
    {mean : ℝ≥0} (hmean : 0 < mean) (t : ℝ) :
    charFun (poissonCenteredScaledMeasure mean) t =
      Complex.exp
        ((mean : ℂ) *
            (Complex.exp (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) - 1) -
          ((Real.sqrt mean : ℂ) * (t : ℂ) * Complex.I)) := by
  rw [poissonCenteredScaledMeasure_eq_affine hmean,
    charFun_map_add_const, charFun_map_mul,
    show poissonRealMeasure mean =
      Measure.map (fun n : ℕ => (n : ℝ)) (poissonMeasure mean) by rfl,
    poissonMeasure_charFun]
  rw [← Complex.exp_add]
  congr 1
  have hinter : inner ℝ (-Real.sqrt (mean : ℝ)) t = -(Real.sqrt mean * t) := by
    change t * (-Real.sqrt (mean : ℝ)) = _
    ring
  rw [hinter]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul]
  ring

/-- The exponent in the centered Poisson characteristic function separates
into its quadratic Gaussian term and a third-order exponential remainder. -/
theorem poissonCenteredScaled_charFunExponent_eq_remainder
    {mean : ℝ≥0} (hmean : 0 < mean) (t : ℝ) :
    let u : ℂ := ((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I
    (mean : ℂ) * (Complex.exp u - 1) -
        ((Real.sqrt mean : ℂ) * (t : ℂ) * Complex.I) =
      (mean : ℂ) *
        (Complex.exp u - (1 + u + u ^ 2 / 2)) - (t : ℂ) ^ 2 / 2 := by
  dsimp
  have hsqrt_ne : (Real.sqrt (mean : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmean))
  have hsqrt_sq : (Real.sqrt (mean : ℝ) : ℂ) ^ 2 = (mean : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have hlinear : (mean : ℂ) *
      (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) =
        (Real.sqrt mean : ℂ) * (t : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [hsqrt_ne]
    ring_nf
    rw [hsqrt_sq]
    ring
  have hquadratic : (mean : ℂ) *
      ((((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) ^ 2) = -(t : ℂ) ^ 2 := by
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [hsqrt_ne]
    ring_nf
    rw [hsqrt_sq]
    simp
    ring
  calc
    (mean : ℂ) * (Complex.exp (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) - 1) -
        ((Real.sqrt mean : ℂ) * (t : ℂ) * Complex.I) =
      (mean : ℂ) *
          (Complex.exp (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) -
            (1 + (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) +
              (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) ^ 2 / 2)) +
        (mean : ℂ) * (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) +
        (mean : ℂ) * ((((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) ^ 2) / 2 -
        ((Real.sqrt mean : ℂ) * (t : ℂ) * Complex.I) := by ring
    _ = (mean : ℂ) *
        (Complex.exp (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) -
          (1 + (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) +
            (((Real.sqrt mean)⁻¹ * t : ℝ) * Complex.I) ^ 2 / 2)) -
        (t : ℂ) ^ 2 / 2 := by rw [hlinear, hquadratic]; ring

/-- The third-order remainder in a centered Poisson characteristic exponent
vanishes as the Poisson mean diverges. -/
theorem tendsto_poissonCenteredScaled_charFun_remainder
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) (t : ℝ) :
    Tendsto (fun n : ℕ => (mean n : ℂ) *
      (Complex.exp (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) -
        (1 + (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) +
          (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) ^ 2 / 2)))
      atTop (𝓝 0) := by
  let u : ℕ → ℂ := fun n => ((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (mean n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmean
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (mean n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hscalar : Tendsto (fun n : ℕ => (Real.sqrt (mean n : ℝ))⁻¹ * t)
      atTop (𝓝 0) := by
    simpa using hinv.mul_const t
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u] using
      ((Complex.continuous_ofReal.tendsto 0).comp hscalar).mul_const Complex.I
  have hsum (z : ℂ) :
      (∑ i ∈ Finset.range 3, z ^ i / (i.factorial : ℂ)) =
        1 + z + z ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  have hTaylor :
      (fun n : ℕ => Complex.exp (u n) -
        (1 + u n + u n ^ 2 / 2)) =o[atTop] fun n : ℕ => u n ^ 2 := by
    simpa only [Function.comp_apply, Nat.reduceAdd, hsum] using
      (Complex.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto hu
  by_cases ht : t = 0
  · subst t
    simp
  have hu_ne (n : ℕ) : u n ≠ 0 := by
    apply mul_ne_zero
    · apply Complex.ofReal_ne_zero.mpr
      exact mul_ne_zero
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmean_pos n)))) ht
    · exact Complex.I_ne_zero
  have hu_sq_ne (n : ℕ) : u n ^ 2 ≠ 0 := pow_ne_zero _ (hu_ne n)
  have hquot : Tendsto (fun n : ℕ =>
      (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) / u n ^ 2)
      atTop (𝓝 0) :=
    (Asymptotics.isLittleO_iff_tendsto
      (fun n hzero => (hu_sq_ne n hzero).elim)).mp hTaylor
  have hmean_u_sq (n : ℕ) : (mean n : ℂ) * u n ^ 2 = -(t : ℂ) ^ 2 := by
    dsimp [u]
    have hsqrt_ne : (Real.sqrt (mean n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmean_pos n))
    have hsqrt_sq : (Real.sqrt (mean n : ℝ) : ℂ) ^ 2 = (mean n : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (by positivity)
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [hsqrt_ne]
    ring_nf
    rw [hsqrt_sq]
    simp
    ring
  have hmul : Tendsto (fun n : ℕ => (mean n : ℂ) *
      (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2))) atTop (𝓝 0) := by
    have hproduct := hquot.mul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => -(t : ℂ) ^ 2) atTop (𝓝 (-(t : ℂ) ^ 2)))
    have hproduct_zero : Tendsto (fun n : ℕ =>
        (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) / u n ^ 2 *
          (-(t : ℂ) ^ 2)) atTop (𝓝 0) := by
      simpa using hproduct
    have hpointwise (n : ℕ) :
        (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) / u n ^ 2 * (-(t : ℂ) ^ 2) =
          (mean n : ℂ) * (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) := by
      rw [← hmean_u_sq n]
      calc
        (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) / u n ^ 2 *
            ((mean n : ℂ) * u n ^ 2) =
          (mean n : ℂ) *
            ((Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) / u n ^ 2 * u n ^ 2) := by
              ring
        _ = (mean n : ℂ) *
            (Complex.exp (u n) - (1 + u n + u n ^ 2 / 2)) := by
              rw [div_mul_cancel₀ _ (hu_sq_ne n)]
    exact Tendsto.congr hpointwise hproduct_zero
  simpa [u] using hmul

/-- The exponents of centered Poisson characteristic functions converge to
the standard Gaussian exponent when their means diverge. -/
theorem tendsto_poissonCenteredScaled_charFunExponent
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (mean n : ℂ) *
          (Complex.exp (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) - 1) -
        ((Real.sqrt (mean n) : ℂ) * (t : ℂ) * Complex.I))
      atTop (𝓝 (-((t : ℂ) ^ 2 / 2))) := by
  have hrem := tendsto_poissonCenteredScaled_charFun_remainder hmean_pos hmean t
  have hrem_sub : Tendsto (fun n : ℕ => (mean n : ℂ) *
      (Complex.exp (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) -
        (1 + (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) +
          (((Real.sqrt (mean n))⁻¹ * t : ℝ) * Complex.I) ^ 2 / 2)) -
        (t : ℂ) ^ 2 / 2) atTop (𝓝 (-((t : ℂ) ^ 2 / 2))) := by
    simpa using hrem.sub_const ((t : ℂ) ^ 2 / 2)
  exact Tendsto.congr
    (fun n => (poissonCenteredScaled_charFunExponent_eq_remainder (hmean_pos n) t).symm)
    hrem_sub

/-- Centered Poisson laws with diverging means have pointwise convergent
characteristic functions, with the standard Gaussian limit. -/
theorem tendsto_poissonCenteredScaledMeasure_charFun
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun (poissonCenteredScaledMeasure (mean n)) t)
      atTop (𝓝 (Complex.exp (-((t : ℂ) ^ 2 / 2)))) := by
  exact Tendsto.congr
    (fun n => (poissonCenteredScaledMeasure_charFun (hmean_pos n) t).symm)
    (tendsto_poissonCenteredScaled_charFunExponent hmean_pos hmean t).cexp

/-- The probability-measure packaging of a centered and scaled Poisson law. -/
noncomputable def poissonCenteredScaledProbabilityMeasure (mean : ℝ≥0) :
    ProbabilityMeasure ℝ :=
  ⟨poissonCenteredScaledMeasure mean,
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable⟩

/-- The centered unit-variance Gaussian probability measure. -/
noncomputable def standardGaussianProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- **Poisson central limit theorem with varying means:** centered Poisson
laws converge weakly to the standard Gaussian whenever their means diverge. -/
theorem tendsto_poissonCenteredScaledProbabilityMeasure
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) :
    Tendsto (fun n : ℕ => poissonCenteredScaledProbabilityMeasure (mean n)) atTop
      (𝓝 standardGaussianProbabilityMeasure) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
  intro t
  change Tendsto (fun n : ℕ => charFun (poissonCenteredScaledMeasure (mean n)) t)
    atTop (𝓝 (charFun (gaussianReal 0 1) t))
  simpa [charFun_gaussianReal, Complex.ofReal_pow] using
    tendsto_poissonCenteredScaledMeasure_charFun hmean_pos hmean t

/-- The law of `scale * X` when `X` has law `ν`. -/
noncomputable def probabilityMeasureMapScale
    (ν : ProbabilityMeasure ℝ) (scale : ℝ) : ProbabilityMeasure ℝ :=
  ν.map
    (((continuous_const : Continuous fun _ : ℝ => scale).mul continuous_id).measurable.aemeasurable)

/-- Scaling a probability law can be represented by adjoining a deterministic
factor and applying multiplication on the product space. -/
theorem probabilityMeasureMapScale_eq_product
    (ν : ProbabilityMeasure ℝ) (scale : ℝ) :
    probabilityMeasureMapScale ν scale =
      (ν.prod (diracProba scale)).map
        ((continuous_snd.mul continuous_fst).measurable.aemeasurable) := by
  apply Subtype.ext
  change Measure.map (fun x : ℝ => scale * x) ν.toMeasure =
    Measure.map (fun value : ℝ × ℝ => value.2 * value.1)
      (ν.toMeasure.prod (Measure.dirac scale))
  have hpair : Measurable (fun value : ℝ × ℝ => value.2 * value.1) := by
    fun_prop
  have hlift : Measurable (fun x : ℝ => (x, scale)) := by
    fun_prop
  rw [Measure.prod_dirac, Measure.map_map hpair hlift]
  apply Measure.map_congr
  filter_upwards with x
  rfl

/-- Weak convergence is preserved under deterministic multipliers that also
converge. -/
theorem tendsto_probabilityMeasure_map_variable_mul
    {ν : ℕ → ProbabilityMeasure ℝ} {νLimit : ProbabilityMeasure ℝ}
    {scale : ℕ → ℝ} {scaleLimit : ℝ}
    (hν : Tendsto ν atTop (𝓝 νLimit))
    (hscale : Tendsto scale atTop (𝓝 scaleLimit)) :
    Tendsto (fun n => probabilityMeasureMapScale (ν n) (scale n)) atTop
      (𝓝 (probabilityMeasureMapScale νLimit scaleLimit)) := by
  have hdirac : Tendsto (fun n => diracProba (scale n)) atTop
      (𝓝 (diracProba scaleLimit)) := by
    have hdiracAt : Tendsto diracProba (𝓝 scaleLimit)
        (𝓝 (diracProba scaleLimit)) :=
      (tendsto_diracProba_iff_tendsto (𝓝 scaleLimit)).2 tendsto_id
    exact hdiracAt.comp hscale
  have hproduct : Tendsto (fun n => (ν n).prod (diracProba (scale n))) atTop
      (𝓝 (νLimit.prod (diracProba scaleLimit)) ) := by
    have hcontinuous := ProbabilityMeasure.continuous_prod.tendsto
      (νLimit, diracProba scaleLimit)
    rw [nhds_prod_eq] at hcontinuous
    exact hcontinuous.comp (hν.prodMk hdirac)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (ν n).prod (diracProba (scale n)))
    (νLimit.prod (diracProba scaleLimit)) hproduct
    (continuous_snd.mul continuous_fst)
  simpa only [← probabilityMeasureMapScale_eq_product] using hmap

/-- A centered Poisson law normalized by an arbitrary nonzero real scale. -/
noncomputable def poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) : Measure ℝ :=
  Measure.map (fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / normalizer)
    (poissonMeasure mean)

/-- Every centered and nontrivially normalized Poisson law has mean zero. -/
theorem integral_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ x : ℝ, x ∂poissonCenteredNormalizedMeasure mean normalizer = 0 := by
  rw [poissonCenteredNormalizedMeasure,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hpoint : (fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / normalizer) =
      (fun n : ℕ => normalizer⁻¹ * ((n : ℝ) - (mean : ℝ))) := by
    funext n
    field_simp [hnormalizer]
  rw [hpoint, integral_const_mul,
    AppliedModelingLib.Probability.PoissonProcess.integral_natCast_sub_parameter_poissonMeasure]
  ring

/-- A centered Poisson law remains integrable after any deterministic
normalization. -/
theorem integrable_id_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) :
    Integrable id (poissonCenteredNormalizedMeasure mean normalizer) := by
  unfold poissonCenteredNormalizedMeasure
  apply (integrable_map_measure
    (f := fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / normalizer)
    (g := id) aestronglyMeasurable_id Measurable.of_discrete.aemeasurable).mpr
  refine (AppliedModelingLib.Probability.PoissonProcess.integrable_natCast_sub_parameter_poissonMeasure
    mean).mul_const normalizer⁻¹ |>.congr ?_
  filter_upwards [] with n
  simp only [Function.comp_apply, id_eq]
  simp [div_eq_mul_inv]

/-- The square of a centered Poisson law remains integrable after any
deterministic normalization. -/
theorem integrable_sq_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) :
    Integrable (fun x : ℝ => x ^ 2)
      (poissonCenteredNormalizedMeasure mean normalizer) := by
  unfold poissonCenteredNormalizedMeasure
  apply (integrable_map_measure
    (f := fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / normalizer)
    (g := fun x : ℝ => x ^ 2)
    (by fun_prop) Measurable.of_discrete.aemeasurable).mpr
  refine ((AppliedModelingLib.Probability.PoissonProcess.integrable_natCast_sub_parameter_sq_poissonMeasure
    mean).mul_const ((normalizer⁻¹) ^ 2)).congr ?_
  filter_upwards [] with n
  simp only [Function.comp_apply]
  simp [div_eq_mul_inv]
  ring

/-- The difference of two independently normalized centered Poisson variables
has an integrable square. -/
theorem integrable_sq_sub_poissonCenteredNormalizedMeasure_prod
    (firstMean secondMean : ℝ≥0) (normalizer : ℝ) :
    Integrable (fun pair : ℝ × ℝ => (pair.1 - pair.2) ^ 2)
      ((poissonCenteredNormalizedMeasure firstMean normalizer).prod
        (poissonCenteredNormalizedMeasure secondMean normalizer)) := by
  let firstLaw : Measure ℝ := poissonCenteredNormalizedMeasure firstMean normalizer
  let secondLaw : Measure ℝ := poissonCenteredNormalizedMeasure secondMean normalizer
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hfirst_sq : Integrable (fun x : ℝ => x ^ 2) firstLaw := by
    simpa [firstLaw] using integrable_sq_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_sq : Integrable (fun x : ℝ => x ^ 2) secondLaw := by
    simpa [secondLaw] using integrable_sq_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfirst_id : Integrable id firstLaw := by
    simpa [firstLaw] using integrable_id_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_id : Integrable id secondLaw := by
    simpa [secondLaw] using integrable_id_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfst_sq : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 2)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_sq.comp_fst secondLaw
  have hsnd_sq : Integrable (fun pair : ℝ × ℝ => pair.2 ^ 2)
      (firstLaw.prod secondLaw) := by
    simpa using hsecond_sq.comp_snd firstLaw
  have hproduct : Integrable (fun pair : ℝ × ℝ => pair.1 * pair.2)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_id.mul_prod hsecond_id
  refine ((hfst_sq.add hsnd_sq).sub (hproduct.const_mul 2)).congr ?_
  filter_upwards with pair
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The difference of two independent centered normalized Poisson variables
has mean zero. -/
theorem integral_sub_poissonCenteredNormalizedMeasure_prod
    (firstMean secondMean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ pair : ℝ × ℝ, pair.1 - pair.2 ∂
      (poissonCenteredNormalizedMeasure firstMean normalizer).prod
        (poissonCenteredNormalizedMeasure secondMean normalizer) = 0 := by
  let firstLaw : Measure ℝ := poissonCenteredNormalizedMeasure firstMean normalizer
  let secondLaw : Measure ℝ := poissonCenteredNormalizedMeasure secondMean normalizer
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hfirst_id : Integrable id firstLaw := by
    simpa [firstLaw] using integrable_id_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_id : Integrable id secondLaw := by
    simpa [secondLaw] using integrable_id_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfst : Integrable (fun pair : ℝ × ℝ => pair.1) (firstLaw.prod secondLaw) := by
    simpa using hfirst_id.comp_fst secondLaw
  have hsnd : Integrable (fun pair : ℝ × ℝ => pair.2) (firstLaw.prod secondLaw) := by
    simpa using hsecond_id.comp_snd firstLaw
  have hfst_integral :
      (∫ pair : ℝ × ℝ, pair.1 ∂firstLaw.prod secondLaw) = ∫ x : ℝ, x ∂firstLaw := by
    simpa using (MeasureTheory.integral_fun_fst (μ := firstLaw) (ν := secondLaw) id)
  have hsnd_integral :
      (∫ pair : ℝ × ℝ, pair.2 ∂firstLaw.prod secondLaw) = ∫ x : ℝ, x ∂secondLaw := by
    simpa using (MeasureTheory.integral_fun_snd (μ := firstLaw) (ν := secondLaw) id)
  calc
    ∫ pair : ℝ × ℝ, pair.1 - pair.2 ∂firstLaw.prod secondLaw =
        (∫ pair : ℝ × ℝ, pair.1 ∂firstLaw.prod secondLaw) -
          ∫ pair : ℝ × ℝ, pair.2 ∂firstLaw.prod secondLaw :=
      integral_sub hfst hsnd
    _ = (∫ x : ℝ, x ∂firstLaw) - ∫ x : ℝ, x ∂secondLaw := by
      rw [hfst_integral, hsnd_integral]
    _ = 0 := by
      rw [show (∫ x : ℝ, x ∂firstLaw) = 0 by
        simpa [firstLaw] using
          integral_poissonCenteredNormalizedMeasure firstMean normalizer hnormalizer,
        show (∫ x : ℝ, x ∂secondLaw) = 0 by
          simpa [secondLaw] using
            integral_poissonCenteredNormalizedMeasure secondMean normalizer hnormalizer]
      ring

/-- The normalized centered Poisson law has the expected exact second moment.
This gives the deterministic increment-variance calculation used by
functional Poisson and queueing tightness arguments. -/
theorem integral_sq_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ x : ℝ, x ^ 2 ∂poissonCenteredNormalizedMeasure mean normalizer =
      (mean : ℝ) / normalizer ^ 2 := by
  rw [poissonCenteredNormalizedMeasure,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hpoint : (fun n : ℕ => (((n : ℝ) - (mean : ℝ)) / normalizer) ^ 2) =
      (fun n : ℕ => (normalizer⁻¹) ^ 2 * ((n : ℝ) - (mean : ℝ)) ^ 2) := by
    funext n
    field_simp [hnormalizer]
  rw [hpoint, integral_const_mul,
    AppliedModelingLib.Probability.PoissonProcess.integral_natCast_sub_parameter_sq_poissonMeasure]
  field_simp [hnormalizer]

/-- The fourth power of a centered Poisson law remains integrable after any
deterministic normalization. -/
theorem integrable_fourth_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) :
    Integrable (fun x : ℝ => x ^ 4)
      (poissonCenteredNormalizedMeasure mean normalizer) := by
  unfold poissonCenteredNormalizedMeasure
  apply (integrable_map_measure
    (f := fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / normalizer)
    (g := fun x : ℝ => x ^ 4)
    (by fun_prop) Measurable.of_discrete.aemeasurable).mpr
  have hfourth : Integrable (fun n : ℕ => ((n : ℝ) - (mean : ℝ)) ^ 4)
      (poissonMeasure mean) :=
    AppliedModelingLib.Probability.PoissonProcess.integrable_natCast_sub_parameter_fourth_poissonMeasure mean
  refine (hfourth.mul_const ((normalizer⁻¹) ^ 4)).congr ?_
  filter_upwards [] with n
  simp only [Function.comp_apply]
  simp [div_eq_mul_inv]
  ring

/-- The normalized centered Poisson law has its exact fourth central moment. -/
theorem integral_fourth_poissonCenteredNormalizedMeasure
    (mean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ x : ℝ, x ^ 4 ∂poissonCenteredNormalizedMeasure mean normalizer =
      ((mean : ℝ) + 3 * (mean : ℝ) ^ 2) / normalizer ^ 4 := by
  rw [poissonCenteredNormalizedMeasure,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hpoint : (fun n : ℕ => (((n : ℝ) - (mean : ℝ)) / normalizer) ^ 4) =
      (fun n : ℕ => (normalizer⁻¹) ^ 4 * ((n : ℝ) - (mean : ℝ)) ^ 4) := by
    funext n
    field_simp [hnormalizer]
  rw [hpoint, integral_const_mul,
    AppliedModelingLib.Probability.PoissonProcess.integral_natCast_sub_parameter_fourth_poissonMeasure]
  field_simp [hnormalizer]

/-- A deterministic fourth-power inequality for differences. -/
theorem fourth_sub_le_eight_mul_fourth_sum (first second : ℝ) :
    (first - second) ^ 4 ≤ 8 * (first ^ 4 + second ^ 4) := by
  have hsq : (first - second) ^ 2 ≤ 2 * (first ^ 2 + second ^ 2) := by
    nlinarith [sq_nonneg (first + second)]
  have hfourth : (first - second) ^ 2 * (first - second) ^ 2 ≤
      (2 * (first ^ 2 + second ^ 2)) * (2 * (first ^ 2 + second ^ 2)) :=
    mul_self_le_mul_self (sq_nonneg (first - second)) hsq
  have hsumfourth : (first ^ 2 + second ^ 2) ^ 2 ≤
      2 * (first ^ 4 + second ^ 4) := by
    nlinarith [sq_nonneg (first ^ 2 - second ^ 2)]
  calc
    (first - second) ^ 4 = (first - second) ^ 2 * (first - second) ^ 2 := by ring
    _ ≤ (2 * (first ^ 2 + second ^ 2)) * (2 * (first ^ 2 + second ^ 2)) := hfourth
    _ = 4 * (first ^ 2 + second ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * (first ^ 4 + second ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hsumfourth (by norm_num)
    _ = 8 * (first ^ 4 + second ^ 4) := by ring

/-- The difference of two independently normalized centered Poisson
variables has an integrable fourth power. -/
theorem integrable_fourth_sub_poissonCenteredNormalizedMeasure_prod
    (firstMean secondMean : ℝ≥0) (normalizer : ℝ) :
    Integrable (fun pair : ℝ × ℝ => (pair.1 - pair.2) ^ 4)
      ((poissonCenteredNormalizedMeasure firstMean normalizer).prod
        (poissonCenteredNormalizedMeasure secondMean normalizer)) := by
  let firstLaw : Measure ℝ := poissonCenteredNormalizedMeasure firstMean normalizer
  let secondLaw : Measure ℝ := poissonCenteredNormalizedMeasure secondMean normalizer
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hfirst_fourth : Integrable (fun x : ℝ => x ^ 4) firstLaw := by
    simpa [firstLaw] using
      integrable_fourth_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_fourth : Integrable (fun x : ℝ => x ^ 4) secondLaw := by
    simpa [secondLaw] using
      integrable_fourth_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfst_fourth : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 4)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_fourth.comp_fst secondLaw
  have hsnd_fourth : Integrable (fun pair : ℝ × ℝ => pair.2 ^ 4)
      (firstLaw.prod secondLaw) := by
    simpa using hsecond_fourth.comp_snd firstLaw
  have hbound : Integrable (fun pair : ℝ × ℝ => 8 * (pair.1 ^ 4 + pair.2 ^ 4))
      (firstLaw.prod secondLaw) :=
    (hfst_fourth.add hsnd_fourth).const_mul 8
  have hdiff_meas : AEStronglyMeasurable (fun pair : ℝ × ℝ =>
      (pair.1 - pair.2) ^ 4) (firstLaw.prod secondLaw) := by fun_prop
  refine hbound.mono' hdiff_meas ?_
  filter_upwards with pair
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (pair.1 - pair.2) ^ 4)]
  exact fourth_sub_le_eight_mul_fourth_sum pair.1 pair.2

/-- For two independent centered Poisson variables, the fourth moment of
their difference is bounded by eight times the sum of their marginal fourth
moments.  The deliberately simple constant avoids imposing unnecessary
third-moment bookkeeping on later path-tightness arguments. -/
theorem integral_fourth_sub_poissonCenteredNormalizedMeasure_prod_le
    (firstMean secondMean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 4 ∂
      (poissonCenteredNormalizedMeasure firstMean normalizer).prod
        (poissonCenteredNormalizedMeasure secondMean normalizer) ≤
      8 * (((firstMean : ℝ) + 3 * (firstMean : ℝ) ^ 2 +
        (secondMean : ℝ) + 3 * (secondMean : ℝ) ^ 2) / normalizer ^ 4) := by
  let firstLaw : Measure ℝ := poissonCenteredNormalizedMeasure firstMean normalizer
  let secondLaw : Measure ℝ := poissonCenteredNormalizedMeasure secondMean normalizer
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hfirst_fourth : Integrable (fun x : ℝ => x ^ 4) firstLaw := by
    simpa [firstLaw] using
      integrable_fourth_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_fourth : Integrable (fun x : ℝ => x ^ 4) secondLaw := by
    simpa [secondLaw] using
      integrable_fourth_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfst_fourth : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 4)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_fourth.comp_fst secondLaw
  have hsnd_fourth : Integrable (fun pair : ℝ × ℝ => pair.2 ^ 4)
      (firstLaw.prod secondLaw) := by
    simpa using hsecond_fourth.comp_snd firstLaw
  have hsum_fourth : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 4 + pair.2 ^ 4)
      (firstLaw.prod secondLaw) := hfst_fourth.add hsnd_fourth
  have hbound : Integrable (fun pair : ℝ × ℝ =>
      8 * (pair.1 ^ 4 + pair.2 ^ 4)) (firstLaw.prod secondLaw) :=
    hsum_fourth.const_mul 8
  have hdiff_meas : AEStronglyMeasurable (fun pair : ℝ × ℝ =>
      (pair.1 - pair.2) ^ 4) (firstLaw.prod secondLaw) := by fun_prop
  have hdiff : Integrable (fun pair : ℝ × ℝ => (pair.1 - pair.2) ^ 4)
      (firstLaw.prod secondLaw) := by
    refine hbound.mono' hdiff_meas ?_
    filter_upwards with pair
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (pair.1 - pair.2) ^ 4)]
    exact fourth_sub_le_eight_mul_fourth_sum pair.1 pair.2
  have hpointwise : (fun pair : ℝ × ℝ => (pair.1 - pair.2) ^ 4) ≤ᵐ[
      firstLaw.prod secondLaw] fun pair => 8 * (pair.1 ^ 4 + pair.2 ^ 4) :=
    Filter.Eventually.of_forall fun pair =>
      fourth_sub_le_eight_mul_fourth_sum pair.1 pair.2
  have hfirst_integral : (∫ x : ℝ, x ^ 4 ∂firstLaw) =
      ((firstMean : ℝ) + 3 * (firstMean : ℝ) ^ 2) / normalizer ^ 4 := by
    simpa [firstLaw] using
      integral_fourth_poissonCenteredNormalizedMeasure firstMean normalizer hnormalizer
  have hsecond_integral : (∫ x : ℝ, x ^ 4 ∂secondLaw) =
      ((secondMean : ℝ) + 3 * (secondMean : ℝ) ^ 2) / normalizer ^ 4 := by
    simpa [secondLaw] using
      integral_fourth_poissonCenteredNormalizedMeasure secondMean normalizer hnormalizer
  have hfst_integral :
      (∫ pair : ℝ × ℝ, pair.1 ^ 4 ∂firstLaw.prod secondLaw) =
        ∫ x : ℝ, x ^ 4 ∂firstLaw := by
    change ∫ pair : ℝ × ℝ, (fun x : ℝ => x ^ 4) pair.1
      ∂firstLaw.prod secondLaw = _
    simpa using (MeasureTheory.integral_fun_fst
      (μ := firstLaw) (ν := secondLaw) (fun x : ℝ => x ^ 4))
  have hsnd_integral :
      (∫ pair : ℝ × ℝ, pair.2 ^ 4 ∂firstLaw.prod secondLaw) =
        ∫ x : ℝ, x ^ 4 ∂secondLaw := by
    change ∫ pair : ℝ × ℝ, (fun x : ℝ => x ^ 4) pair.2
      ∂firstLaw.prod secondLaw = _
    simpa using (MeasureTheory.integral_fun_snd
      (μ := firstLaw) (ν := secondLaw) (fun x : ℝ => x ^ 4))
  have hmono := integral_mono_ae hdiff hbound hpointwise
  change ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 4 ∂firstLaw.prod secondLaw ≤ _
  calc
    ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 4 ∂firstLaw.prod secondLaw ≤
        ∫ pair : ℝ × ℝ, 8 * (pair.1 ^ 4 + pair.2 ^ 4) ∂firstLaw.prod secondLaw := hmono
    _ = 8 * ((∫ pair : ℝ × ℝ, pair.1 ^ 4 ∂firstLaw.prod secondLaw) +
        ∫ pair : ℝ × ℝ, pair.2 ^ 4 ∂firstLaw.prod secondLaw) := by
      rw [integral_const_mul, integral_add hfst_fourth hsnd_fourth]
    _ = 8 * (((firstMean : ℝ) + 3 * (firstMean : ℝ) ^ 2 +
        (secondMean : ℝ) + 3 * (secondMean : ℝ) ^ 2) / normalizer ^ 4) := by
      rw [hfst_integral, hsnd_integral, hfirst_integral, hsecond_integral]
      field_simp [hnormalizer]
      ring

/-- Independent centered Poisson variables have additive second moments under
subtraction.  This is the exact scalar variance identity for a difference of
two independently normalized Poisson counts. -/
theorem integral_sq_sub_poissonCenteredNormalizedMeasure_prod
    (firstMean secondMean : ℝ≥0) (normalizer : ℝ) (hnormalizer : normalizer ≠ 0) :
    ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 2 ∂
      (poissonCenteredNormalizedMeasure firstMean normalizer).prod
        (poissonCenteredNormalizedMeasure secondMean normalizer) =
      ((firstMean : ℝ) + (secondMean : ℝ)) / normalizer ^ 2 := by
  let firstLaw : Measure ℝ := poissonCenteredNormalizedMeasure firstMean normalizer
  let secondLaw : Measure ℝ := poissonCenteredNormalizedMeasure secondMean normalizer
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw, poissonCenteredNormalizedMeasure]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hfirst_sq : Integrable (fun x : ℝ => x ^ 2) firstLaw := by
    simpa [firstLaw] using
      integrable_sq_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_sq : Integrable (fun x : ℝ => x ^ 2) secondLaw := by
    simpa [secondLaw] using
      integrable_sq_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfirst_id : Integrable id firstLaw := by
    simpa [firstLaw] using
      integrable_id_poissonCenteredNormalizedMeasure firstMean normalizer
  have hsecond_id : Integrable id secondLaw := by
    simpa [secondLaw] using
      integrable_id_poissonCenteredNormalizedMeasure secondMean normalizer
  have hfst_sq : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 2)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_sq.comp_fst secondLaw
  have hsnd_sq : Integrable (fun pair : ℝ × ℝ => pair.2 ^ 2)
      (firstLaw.prod secondLaw) := by
    simpa using hsecond_sq.comp_snd firstLaw
  have hproduct : Integrable (fun pair : ℝ × ℝ => pair.1 * pair.2)
      (firstLaw.prod secondLaw) := by
    simpa using hfirst_id.mul_prod hsecond_id
  have hsum : Integrable (fun pair : ℝ × ℝ => pair.1 ^ 2 + pair.2 ^ 2)
      (firstLaw.prod secondLaw) := hfst_sq.add hsnd_sq
  have hfirst_second : (∫ x : ℝ, x ^ 2 ∂firstLaw) =
      (firstMean : ℝ) / normalizer ^ 2 := by
    simpa [firstLaw] using
      integral_sq_poissonCenteredNormalizedMeasure firstMean normalizer hnormalizer
  have hsecond_second : (∫ x : ℝ, x ^ 2 ∂secondLaw) =
      (secondMean : ℝ) / normalizer ^ 2 := by
    simpa [secondLaw] using
      integral_sq_poissonCenteredNormalizedMeasure secondMean normalizer hnormalizer
  have hfirst_mean : (∫ x : ℝ, x ∂firstLaw) = 0 := by
    simpa [firstLaw] using
      integral_poissonCenteredNormalizedMeasure firstMean normalizer hnormalizer
  have hsecond_mean : (∫ x : ℝ, x ∂secondLaw) = 0 := by
    simpa [secondLaw] using
      integral_poissonCenteredNormalizedMeasure secondMean normalizer hnormalizer
  have hfst_integral :
      (∫ pair : ℝ × ℝ, pair.1 ^ 2 ∂firstLaw.prod secondLaw) =
        ∫ x : ℝ, x ^ 2 ∂firstLaw := by
    change ∫ pair : ℝ × ℝ, (fun x : ℝ => x ^ 2) pair.1
      ∂firstLaw.prod secondLaw = _
    simpa using (MeasureTheory.integral_fun_fst
      (μ := firstLaw) (ν := secondLaw) (fun x : ℝ => x ^ 2))
  have hsnd_integral :
      (∫ pair : ℝ × ℝ, pair.2 ^ 2 ∂firstLaw.prod secondLaw) =
        ∫ x : ℝ, x ^ 2 ∂secondLaw := by
    change ∫ pair : ℝ × ℝ, (fun x : ℝ => x ^ 2) pair.2
      ∂firstLaw.prod secondLaw = _
    simpa using (MeasureTheory.integral_fun_snd
      (μ := firstLaw) (ν := secondLaw) (fun x : ℝ => x ^ 2))
  have hproduct_integral :
      (∫ pair : ℝ × ℝ, pair.1 * pair.2 ∂firstLaw.prod secondLaw) =
        (∫ x : ℝ, x ∂firstLaw) * ∫ x : ℝ, x ∂secondLaw := by
    exact MeasureTheory.integral_prod_mul id id
  change ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 2
    ∂firstLaw.prod secondLaw = _
  calc
    ∫ pair : ℝ × ℝ, (pair.1 - pair.2) ^ 2
      ∂firstLaw.prod secondLaw =
        ∫ pair : ℝ × ℝ, pair.1 ^ 2 + pair.2 ^ 2 - 2 * (pair.1 * pair.2)
          ∂firstLaw.prod secondLaw := by
      apply integral_congr_ae
      filter_upwards with pair
      ring
    _ =
        (∫ pair : ℝ × ℝ, pair.1 ^ 2 + pair.2 ^ 2 ∂firstLaw.prod secondLaw) -
          ∫ pair : ℝ × ℝ, 2 * (pair.1 * pair.2) ∂firstLaw.prod secondLaw :=
      integral_sub hsum (hproduct.const_mul 2)
    _ = (∫ pair : ℝ × ℝ, pair.1 ^ 2 ∂firstLaw.prod secondLaw) +
          (∫ pair : ℝ × ℝ, pair.2 ^ 2 ∂firstLaw.prod secondLaw) -
            2 * ∫ pair : ℝ × ℝ, pair.1 * pair.2 ∂firstLaw.prod secondLaw := by
      rw [integral_add hfst_sq hsnd_sq, integral_const_mul]
    _ = (∫ x : ℝ, x ^ 2 ∂firstLaw) + (∫ x : ℝ, x ^ 2 ∂secondLaw) -
          2 * ((∫ x : ℝ, x ∂firstLaw) * ∫ x : ℝ, x ∂secondLaw) := by
      rw [hfst_integral, hsnd_integral, hproduct_integral]
    _ = ((firstMean : ℝ) + (secondMean : ℝ)) / normalizer ^ 2 := by
      rw [hfirst_second, hsecond_second, hfirst_mean, hsecond_mean]
      field_simp [hnormalizer]
      ring

/-- Probability-measure packaging of a centered Poisson law normalized by an
arbitrary nonzero real scale. -/
noncomputable def poissonCenteredNormalizedProbabilityMeasure
    (mean : ℝ≥0) (normalizer : ℝ) : ProbabilityMeasure ℝ :=
  ⟨poissonCenteredNormalizedMeasure mean normalizer,
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable⟩

/-- The arbitrary normalization is a deterministic multiplier of the
variance-one normalization. -/
theorem poissonCenteredNormalizedMeasure_eq_map_scaled
    {mean : ℝ≥0} {normalizer : ℝ}
    (hmean : 0 < mean) (hnormalizer : normalizer ≠ 0) :
    poissonCenteredNormalizedMeasure mean normalizer =
      Measure.map (fun x : ℝ => (Real.sqrt mean / normalizer) * x)
        (poissonCenteredScaledMeasure mean) := by
  have hmult : Measurable (fun x : ℝ => (Real.sqrt mean / normalizer) * x) := by
    fun_prop
  rw [show poissonCenteredScaledMeasure mean =
      Measure.map (fun n : ℕ => ((n : ℝ) - (mean : ℝ)) / Real.sqrt mean)
        (poissonMeasure mean) by rfl,
    Measure.map_map hmult Measurable.of_discrete]
  apply Measure.map_congr
  filter_upwards with n
  simp only [Function.comp_apply]
  have hsqrt_ne : Real.sqrt (mean : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hmean))
  field_simp [hsqrt_ne, hnormalizer]

/-- Probability-measure form of the arbitrary-normalization identity. -/
theorem poissonCenteredNormalizedProbabilityMeasure_eq_map_scaled
    {mean : ℝ≥0} {normalizer : ℝ}
    (hmean : 0 < mean) (hnormalizer : normalizer ≠ 0) :
    poissonCenteredNormalizedProbabilityMeasure mean normalizer =
      probabilityMeasureMapScale (poissonCenteredScaledProbabilityMeasure mean)
        (Real.sqrt mean / normalizer) := by
  apply Subtype.ext
  exact poissonCenteredNormalizedMeasure_eq_map_scaled hmean hnormalizer

/-- Centered Poisson laws converge under any deterministic normalization whose
ratio to the Poisson standard deviation has a finite limit. -/
theorem tendsto_poissonCenteredNormalizedProbabilityMeasure
    {mean : ℕ → ℝ≥0} {normalizer : ℕ → ℝ} {scaleLimit : ℝ}
    (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop)
    (hnormalizer_ne : ∀ n, normalizer n ≠ 0)
    (hscale : Tendsto (fun n : ℕ => Real.sqrt (mean n) / normalizer n) atTop
      (𝓝 scaleLimit)) :
    Tendsto (fun n => poissonCenteredNormalizedProbabilityMeasure (mean n) (normalizer n))
      atTop
      (𝓝 (probabilityMeasureMapScale standardGaussianProbabilityMeasure scaleLimit)) := by
  have hstandard := tendsto_poissonCenteredScaledProbabilityMeasure hmean_pos hmean
  have hmapped := tendsto_probabilityMeasure_map_variable_mul hstandard hscale
  apply Tendsto.congr' _ hmapped
  filter_upwards with n
  exact (poissonCenteredNormalizedProbabilityMeasure_eq_map_scaled
    (hmean_pos n) (hnormalizer_ne n)).symm

/-- A finite family of independently packaged centered Poisson laws converges
jointly whenever each coordinate has a diverging mean and a convergent
normalization.  This is the finite-dimensional input for Poisson functional
limits; it does not assert tightness of a path-valued process. -/
theorem tendsto_poissonCenteredNormalizedProbabilityMeasure_pi
    {ι : Type*} [Fintype ι]
    {mean : ℕ → ι → NNReal} {normalizer : ℕ → ι → ℝ}
    {scaleLimit : ι → ℝ}
    (hmean_pos : ∀ (n : ℕ) (index : ι), 0 < mean n index)
    (hmean : ∀ (index : ι),
      Tendsto (fun n : ℕ => (mean n index : ℝ)) atTop atTop)
    (hnormalizer_ne : ∀ (n : ℕ) (index : ι), normalizer n index ≠ 0)
    (hscale : ∀ (index : ι),
      Tendsto (fun n : ℕ => Real.sqrt (mean n index) / normalizer n index) atTop
        (𝓝 (scaleLimit index))) :
    Tendsto (fun n => ProbabilityMeasure.pi (fun index =>
      poissonCenteredNormalizedProbabilityMeasure (mean n index) (normalizer n index))) atTop
      (𝓝 (ProbabilityMeasure.pi (fun index =>
        probabilityMeasureMapScale standardGaussianProbabilityMeasure
          (scaleLimit index)))) := by
  apply AppliedModelingLib.Probability.tendsto_probabilityMeasure_pi_of_tendsto
  intro index
  exact tendsto_poissonCenteredNormalizedProbabilityMeasure
    (fun n => hmean_pos n index) (hmean index)
    (fun n => hnormalizer_ne n index) (hscale index)

/-- Scaling the standard Gaussian by `scale` gives the centered Gaussian with
variance `scale ^ 2`. -/
theorem probabilityMeasureMapScale_standardGaussian_eq_gaussian
    (scale : ℝ) :
    probabilityMeasureMapScale standardGaussianProbabilityMeasure scale =
      ⟨gaussianReal 0 (NNReal.mk (scale ^ 2) (sq_nonneg scale)), inferInstance⟩ := by
  apply Subtype.ext
  change Measure.map (fun x : ℝ => scale * x) (gaussianReal 0 1) = _
  rw [gaussianReal_map_const_mul]
  simp

/-- At every fixed real cutoff, the distribution functions of centered
Poisson laws converge to the corresponding standard-Gaussian mass. -/
theorem tendsto_poissonCenteredScaledProbabilityMeasure_Iic
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) (cutoff : ℝ) :
    Tendsto (fun n : ℕ =>
      poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic cutoff)) atTop
      (𝓝 (standardGaussianProbabilityMeasure (Set.Iic cutoff))) := by
  apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (tendsto_poissonCenteredScaledProbabilityMeasure hmean_pos hmean)
  letI : NoAtoms (gaussianReal 0 1) :=
    ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  have hnull : gaussianReal 0 1 (frontier (Set.Iic cutoff)) = 0 := by
    rw [frontier_Iic]
    exact NoAtoms.measure_singleton cutoff
  simpa [standardGaussianProbabilityMeasure] using hnull

/-- Fixed standardized lower-tail probabilities converge to the standard
Gaussian CDF, expressed as real probabilities. -/
theorem tendsto_poissonCenteredScaledProbabilityMeasureReal_Iic
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop) (cutoff : ℝ) :
    Tendsto (fun n : ℕ =>
      ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic cutoff) : ℝ≥0) : ℝ))
      atTop (𝓝 (standardGaussianCDF cutoff)) := by
  have h := (NNReal.continuous_coe.tendsto _).comp
    (tendsto_poissonCenteredScaledProbabilityMeasure_Iic hmean_pos hmean cutoff)
  simpa [standardGaussianProbabilityMeasure, standardGaussianCDF,
    ProbabilityTheory.cdf_eq_real] using h

/-- Standardized lower-tail probabilities remain convergent when the cutoff
varies and has a real limit. -/
theorem tendsto_poissonCenteredScaledProbabilityMeasureReal_Iic_of_tendsto_cutoff
    {mean : ℕ → ℝ≥0} (hmean_pos : ∀ n, 0 < mean n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop)
    {cutoff : ℕ → ℝ} {cutoffLimit : ℝ}
    (hcutoff : Tendsto cutoff atTop (𝓝 cutoffLimit)) :
    Tendsto (fun n : ℕ =>
      ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic (cutoff n)) : ℝ≥0) : ℝ))
      atTop (𝓝 (standardGaussianCDF cutoffLimit)) := by
  let F : ℕ → ℝ := fun n =>
    ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic (cutoff n)) : ℝ≥0) : ℝ)
  have hfixed (x : ℝ) : Tendsto (fun n : ℕ =>
      ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic x) : ℝ≥0) : ℝ))
      atTop (𝓝 (standardGaussianCDF x)) :=
    tendsto_poissonCenteredScaledProbabilityMeasureReal_Iic hmean_pos hmean x
  have hmono (n : ℕ) {x y : ℝ} (hxy : x ≤ y) :
      ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic x) : ℝ≥0) : ℝ) ≤
        ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic y) : ℝ≥0) : ℝ) := by
    apply NNReal.coe_le_coe.mpr
    change ((poissonCenteredScaledProbabilityMeasure (mean n) : Measure ℝ)
      (Set.Iic x)).toNNReal ≤
        ((poissonCenteredScaledProbabilityMeasure (mean n) : Measure ℝ)
          (Set.Iic y)).toNNReal
    apply ENNReal.toNNReal_mono (measure_ne_top _ _)
    exact measure_mono (Set.Iic_subset_Iic.2 hxy)
  change Tendsto F atTop (𝓝 (standardGaussianCDF cutoffLimit))
  rw [tendsto_order]
  constructor
  · intro lower hlower
    by_cases hlower_neg : lower < 0
    · filter_upwards with n
      exact lt_of_lt_of_le hlower_neg (NNReal.coe_nonneg _)
    have hlower_nonneg : 0 ≤ lower := le_of_not_gt hlower_neg
    let q : Set.Ioo (0 : ℝ) 1 := ⟨(lower + standardGaussianCDF cutoffLimit) / 2,
      by constructor <;> nlinarith [standardGaussianCDF_pos cutoffLimit,
        standardGaussianCDF_lt_one cutoffLimit]⟩
    let bridge : ℝ := standardGaussianQuantileIoo q
    have hq_lower : lower < (q : ℝ) := by
      dsimp [q]
      linarith
    have hq_limit : (q : ℝ) < standardGaussianCDF cutoffLimit := by
      dsimp [q]
      linarith
    have hbridge_lt : bridge < cutoffLimit := by
      apply standardGaussianCDF_strictMono.lt_iff_lt.mp
      rw [standardGaussianCDF_quantileIoo]
      exact hq_limit
    have hcut : ∀ᶠ n : ℕ in atTop, bridge ≤ cutoff n :=
      (hcutoff.eventually_const_lt hbridge_lt).mono fun _ h => h.le
    have hbridge : ∀ᶠ n : ℕ in atTop, lower <
        ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic bridge) : ℝ≥0) : ℝ) := by
      have hq : lower < standardGaussianCDF bridge := by
        rw [standardGaussianCDF_quantileIoo]
        exact hq_lower
      exact (hfixed bridge).eventually_const_lt hq
    filter_upwards [hcut, hbridge] with n hn hprob
    exact hprob.trans_le (hmono n hn)
  · intro upper hupper
    by_cases hone_lt : 1 < upper
    · filter_upwards with n
      exact lt_of_le_of_lt ((NNReal.coe_le_one).mpr
        (ProbabilityMeasure.apply_le_one _ _)) hone_lt
    have hone_le : upper ≤ 1 := le_of_not_gt hone_lt
    let q : Set.Ioo (0 : ℝ) 1 := ⟨(standardGaussianCDF cutoffLimit + upper) / 2,
      by constructor <;> nlinarith [standardGaussianCDF_pos cutoffLimit,
        standardGaussianCDF_lt_one cutoffLimit]⟩
    let bridge : ℝ := standardGaussianQuantileIoo q
    have hlimit_q : standardGaussianCDF cutoffLimit < (q : ℝ) := by
      dsimp [q]
      linarith
    have hq_upper : (q : ℝ) < upper := by
      dsimp [q]
      linarith
    have hlimit_lt_bridge : cutoffLimit < bridge := by
      apply standardGaussianCDF_strictMono.lt_iff_lt.mp
      rw [standardGaussianCDF_quantileIoo]
      exact hlimit_q
    have hcut : ∀ᶠ n : ℕ in atTop, cutoff n ≤ bridge :=
      (hcutoff.eventually_lt_const hlimit_lt_bridge).mono fun _ h => h.le
    have hbridge : ∀ᶠ n : ℕ in atTop,
        ((poissonCenteredScaledProbabilityMeasure (mean n) (Set.Iic bridge) : ℝ≥0) : ℝ) < upper := by
      have hq : standardGaussianCDF bridge < upper := by
        rw [standardGaussianCDF_quantileIoo]
        exact hq_upper
      exact (hfixed bridge).eventually_lt_const hq
    filter_upwards [hcut, hbridge] with n hn hprob
    exact (hmono n hn).trans_lt hprob

/-- The discrete strict lower tail below a server threshold is exactly an
interval event for the centered, scaled Poisson law. -/
theorem poissonCenteredScaledMeasure_Iic_serverThreshold_eq_Iio
    (mean : ℝ≥0) {servers : ℕ} (hservers : 0 < servers) (hmean : 0 < mean) :
    poissonCenteredScaledMeasure mean
        (Set.Iic (((servers : ℝ) - 1 - (mean : ℝ)) / Real.sqrt mean)) =
      poissonMeasure mean (Set.Iio servers) := by
  let f : ℕ → ℝ := fun n => ((n : ℝ) - (mean : ℝ)) / Real.sqrt mean
  have hf : Measurable f := Measurable.of_discrete
  have hsqrt_pos : 0 < Real.sqrt (mean : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hmean)
  have hpreimage : f ⁻¹' Set.Iic (((servers : ℝ) - 1 - (mean : ℝ)) /
      Real.sqrt mean) = Set.Iio servers := by
    ext n
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Iio]
    rw [show f n = ((n : ℝ) - (mean : ℝ)) / Real.sqrt mean by rfl,
      div_le_div_iff_of_pos_right hsqrt_pos]
    constructor
    · intro h
      have hreal : (n : ℝ) < servers := by linarith
      exact_mod_cast hreal
    · intro h
      have hleNat : n ≤ servers - 1 := Nat.le_sub_one_of_lt h
      have hcast_sub : ((servers - 1 : ℕ) : ℝ) = (servers : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hreal : (n : ℝ) ≤ (servers : ℝ) - 1 := by
        rw [← hcast_sub]
        exact_mod_cast hleNat
      linarith
  change Measure.map f (poissonMeasure mean)
    (Set.Iic (((servers : ℝ) - 1 - (mean : ℝ)) / Real.sqrt mean)) = _
  rw [Measure.map_apply hf measurableSet_Iic, hpreimage]

/-- The finite Poisson lower-tail probability is the real mass of the
corresponding standardized interval event. -/
theorem poissonLowerTailProbability_eq_centeredScaledMeasureReal_Iic_serverThreshold
    (mean : ℝ≥0) {servers : ℕ} (hservers : 0 < servers) (hmean : 0 < mean) :
    poissonLowerTailProbability mean servers =
      (poissonCenteredScaledMeasure mean).real
        (Set.Iic (((servers : ℝ) - 1 - (mean : ℝ)) / Real.sqrt mean)) := by
  rw [poissonLowerTailProbability_eq_measureReal_Iio]
  change ((poissonMeasure mean) (Set.Iio servers)).toReal =
    ((poissonCenteredScaledMeasure mean)
      (Set.Iic (((servers : ℝ) - 1 - (mean : ℝ)) / Real.sqrt mean))).toReal
  rw [poissonCenteredScaledMeasure_Iic_serverThreshold_eq_Iio mean hservers hmean]

/-- A moving standardized server threshold turns the finite Poisson lower
tail into the corresponding Gaussian-CDF limit. -/
theorem tendsto_poissonLowerTailProbability_of_tendsto_serverThreshold
    {mean : ℕ → ℝ≥0} {servers : ℕ → ℕ}
    (hmean_pos : ∀ n, 0 < mean n) (hservers_pos : ∀ n, 0 < servers n)
    (hmean : Tendsto (fun n : ℕ => (mean n : ℝ)) atTop atTop)
    {thresholdLimit : ℝ}
    (hthreshold : Tendsto
      (fun n : ℕ =>
        (((servers n : ℝ) - 1 - (mean n : ℝ)) / Real.sqrt (mean n)))
      atTop (𝓝 thresholdLimit)) :
    Tendsto (fun n : ℕ => poissonLowerTailProbability (mean n) (servers n))
      atTop (𝓝 (standardGaussianCDF thresholdLimit)) := by
  refine Tendsto.congr (fun n => ?_)
    (tendsto_poissonCenteredScaledProbabilityMeasureReal_Iic_of_tendsto_cutoff
      hmean_pos hmean hthreshold)
  exact (poissonLowerTailProbability_eq_centeredScaledMeasureReal_Iic_serverThreshold
    (mean n) (hservers_pos n) (hmean_pos n)).symm

/-- A finite square-root-scale spare-capacity limit forces the traffic
intensity itself to converge to critical load. -/
theorem tendsto_trafficIntensity_of_tendsto_qed_spareCapacity
    {trafficIntensity : ℕ → ℝ} {beta : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) * (1 - trafficIntensity n))
      atTop (𝓝 beta)) :
    Tendsto trafficIntensity atTop (𝓝 1) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hgap_div : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (n : ℝ) * (1 - trafficIntensity n)) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaled hsqrt
  have hgap : Tendsto (fun n : ℕ => 1 - trafficIntensity n) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgap_div
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnat_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 hnat_pos).ne'
    field_simp [hsqrt_ne]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)

/-- The logarithmic correction in a square-root QED perturbation has the
quadratic Gaussian exponent. -/
theorem tendsto_qed_logCorrection
    {trafficIntensity : ℕ → ℝ} {beta : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) * (1 - trafficIntensity n))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => (n : ℝ) *
        (Real.log (trafficIntensity n) - trafficIntensity n + 1))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
  let deviation : ℕ → ℝ := fun n => 1 - trafficIntensity n
  have hscaledDeviation : Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) * deviation n)
      atTop (𝓝 beta) := by
    simpa [deviation] using hscaled
  have htraffic := tendsto_trafficIntensity_of_tendsto_qed_spareCapacity hscaled
  have hdeviation : Tendsto deviation atTop (𝓝 0) := by
    simpa [deviation] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub htraffic)
  have habsDeviation : Tendsto (fun n : ℕ => |deviation n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using hdeviation.norm
  have hsmall : ∀ᶠ n : ℕ in atTop, |deviation n| < 1 :=
    habsDeviation.eventually_lt_const (by norm_num)
  have hratio : Tendsto
      (fun n : ℕ => |deviation n| / (1 - |deviation n|))
      atTop (𝓝 0) := by
    have hdenominator : Tendsto (fun n : ℕ => 1 - |deviation n|)
        atTop (𝓝 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          habsDeviation)
    simpa using habsDeviation.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  have hboundLimit : Tendsto
      (fun n : ℕ => (Real.sqrt (n : ℝ) * deviation n) ^ 2 *
        (|deviation n| / (1 - |deviation n|)))
      atTop (𝓝 0) := by
    simpa using (hscaledDeviation.pow 2).mul hratio
  have hremainder : Tendsto
      (fun n : ℕ => (n : ℝ) *
        (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    change Tendsto
      (fun n : ℕ => |(n : ℝ) *
        (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n))|)
      atTop (𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hboundLimit
    filter_upwards [hsmall] with n hn
    have hseries :
        |deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)| ≤
          |deviation n| ^ 3 / (1 - |deviation n|) := by
      convert Real.abs_log_sub_add_sum_range_le hn 2 using 1
      norm_num [Finset.sum_range_succ]
    have hnat_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      |(n : ℝ) *
          (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n))| =
          (n : ℝ) *
            |deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)| := by
              rw [abs_mul, abs_of_nonneg hnat_nonneg]
      _ ≤ (n : ℝ) * (|deviation n| ^ 3 / (1 - |deviation n|)) :=
        mul_le_mul_of_nonneg_left hseries hnat_nonneg
      _ = (Real.sqrt (n : ℝ) * deviation n) ^ 2 *
          (|deviation n| / (1 - |deviation n|)) := by
        rw [mul_pow, Real.sq_sqrt hnat_nonneg, ← sq_abs]
        ring
  have hquadratic : Tendsto
      (fun n : ℕ => -((Real.sqrt (n : ℝ) * deviation n) ^ 2 / 2))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
    simpa using ((hscaledDeviation.pow 2).div_const (2 : ℝ)).neg
  have hsum : Tendsto
      (fun n : ℕ => -((Real.sqrt (n : ℝ) * deviation n) ^ 2 / 2) +
        (n : ℝ) *
          (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
    simpa using hquadratic.add hremainder
  refine Tendsto.congr' ?_ hsum
  filter_upwards [hsmall] with n hn
  have htraffic_eq : trafficIntensity n = 1 - deviation n := by
    simp [deviation]
  rw [htraffic_eq]
  have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  ring_nf
  rw [hsquare]
  ring

/-- The logarithmic QED correction is stable under any server-count sequence
that tends to infinity. -/
theorem tendsto_logCorrection_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ} {beta : ℝ}
    (hservers : Tendsto (fun n : ℕ => (servers n : ℝ)) atTop atTop)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - trafficIntensity n))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => (servers n : ℝ) *
        (Real.log (trafficIntensity n) - trafficIntensity n + 1))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
  let deviation : ℕ → ℝ := fun n => 1 - trafficIntensity n
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hservers
  have hscaledDeviation : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * deviation n)
      atTop (𝓝 beta) := by
    simpa [deviation] using hscaled
  have hgapDiv : Tendsto
      (fun n : ℕ => (Real.sqrt (servers n : ℝ) * deviation n) /
        Real.sqrt (servers n : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaledDeviation hsqrtServers
  have hdeviation : Tendsto deviation atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgapDiv
    filter_upwards [hservers.eventually_gt_atTop (0 : ℝ)] with n hn
    have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 hn).ne'
    field_simp [hsqrt_ne]
  have habsDeviation : Tendsto (fun n : ℕ => |deviation n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using hdeviation.norm
  have hsmall : ∀ᶠ n : ℕ in atTop, |deviation n| < 1 :=
    habsDeviation.eventually_lt_const (by norm_num)
  have hratio : Tendsto
      (fun n : ℕ => |deviation n| / (1 - |deviation n|))
      atTop (𝓝 0) := by
    have hdenominator : Tendsto (fun n : ℕ => 1 - |deviation n|)
        atTop (𝓝 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          habsDeviation)
    simpa using habsDeviation.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  have hboundLimit : Tendsto
      (fun n : ℕ => (Real.sqrt (servers n : ℝ) * deviation n) ^ 2 *
        (|deviation n| / (1 - |deviation n|)))
      atTop (𝓝 0) := by
    simpa using (hscaledDeviation.pow 2).mul hratio
  have hremainder : Tendsto
      (fun n : ℕ => (servers n : ℝ) *
        (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    change Tendsto
      (fun n : ℕ => |(servers n : ℝ) *
        (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n))|)
      atTop (𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hboundLimit
    filter_upwards [hsmall] with n hn
    have hseries :
        |deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)| ≤
          |deviation n| ^ 3 / (1 - |deviation n|) := by
      convert Real.abs_log_sub_add_sum_range_le hn 2 using 1
      norm_num [Finset.sum_range_succ]
    have hservers_nonneg : 0 ≤ (servers n : ℝ) := Nat.cast_nonneg _
    calc
      |(servers n : ℝ) *
          (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n))| =
          (servers n : ℝ) *
            |deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)| := by
              rw [abs_mul, abs_of_nonneg hservers_nonneg]
      _ ≤ (servers n : ℝ) * (|deviation n| ^ 3 / (1 - |deviation n|)) :=
        mul_le_mul_of_nonneg_left hseries hservers_nonneg
      _ = (Real.sqrt (servers n : ℝ) * deviation n) ^ 2 *
          (|deviation n| / (1 - |deviation n|)) := by
        rw [mul_pow, Real.sq_sqrt hservers_nonneg, ← sq_abs]
        ring
  have hquadratic : Tendsto
      (fun n : ℕ => -((Real.sqrt (servers n : ℝ) * deviation n) ^ 2 / 2))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
    simpa using ((hscaledDeviation.pow 2).div_const (2 : ℝ)).neg
  have hsum : Tendsto
      (fun n : ℕ => -((Real.sqrt (servers n : ℝ) * deviation n) ^ 2 / 2) +
        (servers n : ℝ) *
          (deviation n + deviation n ^ 2 / 2 + Real.log (1 - deviation n)))
      atTop (𝓝 (-(beta ^ 2 / 2))) := by
    simpa using hquadratic.add hremainder
  refine Tendsto.congr' ?_ hsum
  filter_upwards [hsmall] with n hn
  have htraffic_eq : trafficIntensity n = 1 - deviation n := by
    simp [deviation]
  rw [htraffic_eq]
  have hsquare : Real.sqrt (servers n : ℝ) ^ 2 = (servers n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  ring_nf
  rw [hsquare]
  ring

/-- Under square-root spare-capacity scaling, the logarithm of the traffic
intensity has first-order limit `-beta` on the matching square-root scale. -/
theorem tendsto_sqrtServer_mul_log_trafficIntensity_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0} {beta : ℝ}
    (hservers : Tendsto servers atTop atTop)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * Real.log (trafficIntensity n : ℝ))
      atTop (𝓝 (-beta)) := by
  let deviation : ℕ → ℝ := fun n => 1 - (trafficIntensity n : ℝ)
  have hserversReal : Tendsto (fun n : ℕ => (servers n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hserversReal
  have hscaledDeviation : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * deviation n)
      atTop (𝓝 beta) := by
    simpa [deviation] using hscaled
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity n : ℝ))
      atTop (𝓝 1) := by
    have hgapDiv : Tendsto
        (fun n : ℕ =>
          (Real.sqrt (servers n : ℝ) * deviation n) /
            Real.sqrt (servers n : ℝ))
        atTop (𝓝 0) :=
      Tendsto.div_atTop hscaledDeviation hsqrtServers
    have hgap : Tendsto deviation atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ hgapDiv
      filter_upwards [hservers.eventually_gt_atTop 0] with n hn
      have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
      field_simp [hsqrt_ne]
    simpa [deviation] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)
  have hdeviation : Tendsto deviation atTop (𝓝 0) := by
    simpa [deviation] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub htraffic)
  have habsDeviation : Tendsto (fun n : ℕ => |deviation n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using hdeviation.norm
  have hsmall : ∀ᶠ n : ℕ in atTop, |deviation n| < 1 :=
    habsDeviation.eventually_lt_const (by norm_num)
  have hratio : Tendsto
      (fun n : ℕ => |deviation n| / (1 - |deviation n|)) atTop (𝓝 0) := by
    have hdenominator : Tendsto (fun n : ℕ => 1 - |deviation n|)
        atTop (𝓝 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          habsDeviation)
    simpa using habsDeviation.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  have hsqrtAbsDeviation : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * |deviation n|)
      atTop (𝓝 |beta|) := by
    have habsScaled := hscaledDeviation.norm
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
      habsScaled
  have hboundLimit : Tendsto
    (fun n : ℕ => Real.sqrt (servers n : ℝ) *
        (|deviation n| ^ 2 / (1 - |deviation n|)))
      atTop (𝓝 0) := by
    have hproduct := hsqrtAbsDeviation.mul hratio
    convert hproduct using 1
    all_goals ring_nf
  have hremainder : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) *
        (deviation n + Real.log (1 - deviation n)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    change Tendsto
      (fun n : ℕ => |Real.sqrt (servers n : ℝ) *
        (deviation n + Real.log (1 - deviation n))|)
      atTop (𝓝 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hboundLimit
    filter_upwards [hsmall] with n hn
    have hseries :
        |deviation n + Real.log (1 - deviation n)| ≤
          |deviation n| ^ 2 / (1 - |deviation n|) := by
      convert Real.abs_log_sub_add_sum_range_le hn 1 using 1
      norm_num [Finset.sum_range_succ]
    calc
      |Real.sqrt (servers n : ℝ) *
          (deviation n + Real.log (1 - deviation n))| =
        Real.sqrt (servers n : ℝ) *
          |deviation n + Real.log (1 - deviation n)| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (servers n : ℝ) *
          (|deviation n| ^ 2 / (1 - |deviation n|)) :=
        mul_le_mul_of_nonneg_left hseries (Real.sqrt_nonneg _)
  have hmain : Tendsto
      (fun n : ℕ => -(Real.sqrt (servers n : ℝ) * deviation n) +
        Real.sqrt (servers n : ℝ) *
          (deviation n + Real.log (1 - deviation n)))
      atTop (𝓝 (-beta)) := by
    simpa using hscaledDeviation.neg.add hremainder
  refine Tendsto.congr' ?_ hmain
  filter_upwards with n
  symm
  change Real.sqrt (servers n : ℝ) * Real.log (trafficIntensity n : ℝ) =
    -(Real.sqrt (servers n : ℝ) * deviation n) +
      Real.sqrt (servers n : ℝ) *
        (deviation n + Real.log (1 - deviation n))
  have htraffic_eq : (trafficIntensity n : ℝ) = 1 - deviation n := by
    simp [deviation]
  rw [htraffic_eq]
  ring

/-- A geometric factor with an offset on the square-root server scale has
the exponential QED limit determined by the spare-capacity and offset
parameters. -/
theorem tendsto_trafficIntensity_pow_of_tendsto_scaled_tailOffset
    {servers tailOffset : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0}
    {beta delta : ℝ}
    (hservers : Tendsto servers atTop atTop)
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 beta))
    (htailOffset : Tendsto
      (fun n : ℕ => (tailOffset n : ℝ) / Real.sqrt (servers n : ℝ))
      atTop (𝓝 delta)) :
    Tendsto (fun n : ℕ => (trafficIntensity n : ℝ) ^ tailOffset n)
      atTop (𝓝 (Real.exp (-(beta * delta)))) := by
  have hlog :=
    tendsto_sqrtServer_mul_log_trafficIntensity_of_tendsto_scaled_spareCapacity
      hservers htraffic_pos hscaled
  have hproduct := htailOffset.mul hlog
  have hproduct' : Tendsto
      (fun n : ℕ =>
        ((tailOffset n : ℝ) / Real.sqrt (servers n : ℝ)) *
          (Real.sqrt (servers n : ℝ) * Real.log (trafficIntensity n : ℝ)))
      atTop (𝓝 (-(beta * delta))) := by
    convert hproduct using 1
    all_goals ring_nf
  have hexponential := (Real.continuous_exp.tendsto _).comp hproduct'
  refine Tendsto.congr' ?_ hexponential
  filter_upwards [hservers.eventually_gt_atTop 0] with n hn
  have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have htraffic_real_pos : 0 < (trafficIntensity n : ℝ) := by
    exact_mod_cast htraffic_pos n
  calc
    Real.exp
        (((tailOffset n : ℝ) / Real.sqrt (servers n : ℝ)) *
          (Real.sqrt (servers n : ℝ) * Real.log (trafficIntensity n : ℝ))) =
        Real.exp ((tailOffset n : ℝ) * Real.log (trafficIntensity n : ℝ)) := by
          congr 1
          field_simp [hsqrt_ne]
    _ = (trafficIntensity n : ℝ) ^ tailOffset n := by
      rw [Real.exp_nat_mul, Real.exp_log htraffic_real_pos]

/-- An exact Stirling decomposition of a Poisson point mass at a
square-root-scale server threshold. -/
theorem sqrt_mul_poissonPointProbability_eq_stirling_correction
    (trafficIntensity : ℝ≥0) {servers : ℕ} (hservers : 0 < servers)
    (htraffic : 0 < (trafficIntensity : ℝ)) :
    Real.sqrt (servers : ℝ) *
        poissonPointProbability (servers * trafficIntensity) servers =
      (Real.sqrt 2 * Stirling.stirlingSeq servers)⁻¹ *
        Real.exp ((servers : ℝ) *
          (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1)) := by
  rw [poissonPointProbability_eq]
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  have hservers_real : 0 < (servers : ℝ) := by exact_mod_cast hservers
  have hservers_ne : (servers : ℝ) ≠ 0 := ne_of_gt hservers_real
  have hsqrt_servers_ne : Real.sqrt (servers : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hservers_real).ne'
  have hfactorial_ne : (servers.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero servers
  have hexp_one_ne : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos _).ne'
  have hpower_ne : ((servers : ℝ) / Real.exp 1) ^ servers ≠ 0 := by
    apply pow_ne_zero
    exact div_ne_zero hservers_ne hexp_one_ne
  have hroot_two_ne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hroot_two_servers_ne : Real.sqrt (2 * (servers : ℝ)) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hservers_real)
  have htraffic_pow : (trafficIntensity : ℝ) ^ servers =
      Real.exp ((servers : ℝ) * Real.log (trafficIntensity : ℝ)) := by
    symm
    rw [Real.exp_nat_mul, Real.exp_log htraffic]
  have hexp_one_pow : (Real.exp (1 : ℝ)) ^ servers = Real.exp (servers : ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hratio_pow : ((servers : ℝ) / Real.exp 1) ^ servers =
      (servers : ℝ) ^ servers / Real.exp (servers : ℝ) := by
    rw [div_pow, hexp_one_pow]
  have hcorrection_exp :
      Real.exp ((servers : ℝ) *
        (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1)) =
        Real.exp ((servers : ℝ) * Real.log (trafficIntensity : ℝ)) *
          Real.exp (-((servers : ℝ) * (trafficIntensity : ℝ))) *
            Real.exp (servers : ℝ) := by
    rw [show (servers : ℝ) *
        (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1) =
          (servers : ℝ) * Real.log (trafficIntensity : ℝ) +
            (-((servers : ℝ) * (trafficIntensity : ℝ)) + (servers : ℝ)) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hpoisson_factor :
      Real.exp (-((servers : ℝ) * (trafficIntensity : ℝ))) *
        (((servers : ℝ) * (trafficIntensity : ℝ)) ^ servers) =
        Real.exp ((servers : ℝ) *
          (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1)) *
          ((servers : ℝ) / Real.exp 1) ^ servers := by
    rw [mul_pow, htraffic_pow, hratio_pow, hcorrection_exp]
    field_simp [Real.exp_ne_zero]
  rw [hpoisson_factor, Stirling.stirlingSeq]
  field_simp [hfactorial_ne, hpower_ne, hroot_two_ne, hroot_two_servers_ne]
  rw [show (servers : ℝ) * 2 = 2 * (servers : ℝ) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The reciprocal Stirling normalization has the standard Gaussian density
constant as its limit. -/
theorem tendsto_stirling_reciprocal_normalization :
    Tendsto (fun n : ℕ => (Real.sqrt 2 * Stirling.stirlingSeq n)⁻¹)
      atTop (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹)) := by
  have hdenominator : Tendsto
      (fun n : ℕ => Real.sqrt 2 * Stirling.stirlingSeq n)
      atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi)) := by
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.sqrt 2) atTop (𝓝 (Real.sqrt 2))).mul
        Stirling.tendsto_stirlingSeq_sqrt_pi
  have hdenominator' : Tendsto
      (fun n : ℕ => Real.sqrt 2 * Stirling.stirlingSeq n)
      atTop (𝓝 (Real.sqrt (2 * Real.pi))) := by
    convert hdenominator using 1
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact hdenominator'.inv₀ (by positivity)

/-- The Poisson large-deviation exponent at a subcritical server threshold is
at most minus one half the squared spare capacity. -/
theorem poissonLogRate_le_neg_half_scaledSpareCapacity_sq
    (trafficIntensity : ℝ≥0) {servers : ℕ}
    (htraffic_pos : 0 < (trafficIntensity : ℝ))
    (htraffic_le_one : (trafficIntensity : ℝ) ≤ 1) :
    (servers : ℝ) *
        (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1) ≤
      -(Real.sqrt (servers : ℝ) * (1 - (trafficIntensity : ℝ))) ^ 2 / 2 := by
  let gap : ℝ := 1 - (trafficIntensity : ℝ)
  have hgap_nonneg : 0 ≤ gap := by
    dsimp [gap]
    linarith
  have hgap_lt_one : gap < 1 := by
    dsimp [gap]
    linarith
  have hquadratic : gap + gap ^ 2 / 2 ≤ -Real.log (1 - gap) :=
    AppliedModelingLib.Math.add_half_sq_le_neg_log_one_sub hgap_nonneg hgap_lt_one
  have hbracket :
      Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1 ≤
        -(gap ^ 2) / 2 := by
    have htraffic_eq : (trafficIntensity : ℝ) = 1 - gap := by
      dsimp [gap]
      ring
    rw [htraffic_eq]
    linarith
  have hscaled :
      (servers : ℝ) *
          (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1) ≤
        (servers : ℝ) * (-(gap ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hbracket (Nat.cast_nonneg servers)
  have hsquare : Real.sqrt (servers : ℝ) ^ 2 = (servers : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg servers)
  dsimp [gap] at hscaled ⊢
  nlinarith

/-- Exponential quadratic tails vanish along every real sequence diverging
to positive infinity. -/
theorem tendsto_exp_neg_half_sq_of_tendsto_atTop
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun n : ℕ => Real.exp (-(u n ^ 2 / 2))) atTop (𝓝 0) := by
  have hquadraticAtTop : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const
      (by norm_num)
  simpa only [Function.comp_apply] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hquadraticAtTop.comp hu)

/-- If the square-root spare capacity diverges, the Poisson upper tail above
the server threshold vanishes. -/
theorem tendsto_poissonUpperTailProbability_of_tendsto_scaledSpareCapacity_atTop
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0}
    (htraffic_pos : ∀ n, 0 < (trafficIntensity n : ℝ))
    (htraffic_le_one : ∀ n, (trafficIntensity n : ℝ) ≤ 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)))
      atTop (𝓝 0) := by
  let scaledGap : ℕ → ℝ := fun n =>
    Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))
  have hexpZero : Tendsto (fun n : ℕ => Real.exp (-(scaledGap n ^ 2 / 2)))
      atTop (𝓝 0) := by
    exact tendsto_exp_neg_half_sq_of_tendsto_atTop hscaled
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)) ∧
        (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)) ≤
          Real.exp (-(scaledGap n ^ 2 / 2)) := by
    filter_upwards with n
    constructor
    · exact measureReal_nonneg
    · calc
        (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)) ≤
            Real.exp ((servers n : ℝ) *
              (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) :=
          PoissonProcess.measureReal_poissonMeasure_Ici_servers_le_exp_rate
            (servers n) (trafficIntensity n) (htraffic_pos n) (htraffic_le_one n)
        _ ≤ Real.exp (-(scaledGap n ^ 2 / 2)) := by
          apply Real.exp_le_exp.mpr
          have hrate := poissonLogRate_le_neg_half_scaledSpareCapacity_sq
            (servers := servers n) (trafficIntensity n) (htraffic_pos n) (htraffic_le_one n)
          dsimp [scaledGap]
          convert hrate using 1
          ring_nf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexpZero
    (hbound.mono fun _ hn => hn.1)
    (hbound.mono fun _ hn => hn.2)

/-- If the square-root spare capacity diverges, the finite Poisson lower tail
below the server threshold tends to one. -/
theorem tendsto_poissonLowerTailProbability_of_tendsto_scaledSpareCapacity_atTop
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0}
    (htraffic_pos : ∀ n, 0 < (trafficIntensity n : ℝ))
    (htraffic_le_one : ∀ n, (trafficIntensity n : ℝ) ≤ 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        poissonLowerTailProbability (servers n * trafficIntensity n) (servers n))
      atTop (𝓝 1) := by
  have hupper :=
    tendsto_poissonUpperTailProbability_of_tendsto_scaledSpareCapacity_atTop
      htraffic_pos htraffic_le_one hscaled
  have hone : Tendsto
      (fun n : ℕ => 1 -
        (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hupper)
  refine Tendsto.congr' ?_ hone
  filter_upwards with n
  calc
    1 - (poissonMeasure (servers n * trafficIntensity n)).real (Set.Ici (servers n)) =
        (poissonMeasure (servers n * trafficIntensity n)).real
          ((Set.Ici (servers n))ᶜ) := by
      rw [MeasureTheory.measureReal_compl measurableSet_Ici, probReal_univ]
    _ = (poissonMeasure (servers n * trafficIntensity n)).real (Set.Iio (servers n)) := by
      congr 1
      ext state
      simp
    _ = poissonLowerTailProbability (servers n * trafficIntensity n) (servers n) :=
      (poissonLowerTailProbability_eq_measureReal_Iio _ _).symm

/-- The Poisson large-deviation exponential is negligible compared with a
diverging square-root spare-capacity scale. -/
theorem tendsto_exp_poissonLogRate_div_scaledSpareCapacity_of_tendsto_atTop
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0}
    (htraffic_pos : ∀ n, 0 < (trafficIntensity n : ℝ))
    (htraffic_le_one : ∀ n, (trafficIntensity n : ℝ) ≤ 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        Real.exp ((servers n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) /
          (Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))))
      atTop (𝓝 0) := by
  let scaledGap : ℕ → ℝ := fun n =>
    Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))
  have hexpZero : Tendsto (fun n : ℕ => Real.exp (-(scaledGap n ^ 2 / 2)))
      atTop (𝓝 0) :=
    tendsto_exp_neg_half_sq_of_tendsto_atTop hscaled
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.exp ((servers n : ℝ) *
        (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) /
          scaledGap n ∧
        Real.exp ((servers n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) /
            scaledGap n ≤ Real.exp (-(scaledGap n ^ 2 / 2)) := by
    filter_upwards [hscaled.eventually_ge_atTop 1] with n hn
    have hnpos : 0 < scaledGap n := by linarith
    have hrate := poissonLogRate_le_neg_half_scaledSpareCapacity_sq
      (servers := servers n) (trafficIntensity n) (htraffic_pos n) (htraffic_le_one n)
    have hexpRate :
        Real.exp ((servers n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) ≤
          Real.exp (-(scaledGap n ^ 2 / 2)) := by
      dsimp [scaledGap]
      convert Real.exp_le_exp.mpr hrate using 1
      ring_nf
    constructor
    · exact div_nonneg (Real.exp_pos _).le hnpos.le
    · calc
        Real.exp ((servers n : ℝ) *
            (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) /
              scaledGap n ≤
            Real.exp (-(scaledGap n ^ 2 / 2)) / scaledGap n :=
          div_le_div_of_nonneg_right hexpRate hnpos.le
        _ ≤ Real.exp (-(scaledGap n ^ 2 / 2)) := by
          rw [div_le_iff₀ hnpos]
          have htail_nonneg : 0 ≤ Real.exp (-(scaledGap n ^ 2 / 2)) :=
            (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left hn htail_nonneg]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexpZero
    (hbound.mono fun _ hn => hn.1)
    (hbound.mono fun _ hn => hn.2)

/-- The scaled Poisson point mass is negligible relative to a diverging
square-root spare-capacity scale. -/
theorem tendsto_scaledPoissonPoint_div_scaledSpareCapacity_of_tendsto_atTop
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0}
    (hservers : Tendsto servers atTop atTop)
    (hservers_pos : ∀ n, 0 < servers n)
    (htraffic_pos : ∀ n, 0 < (trafficIntensity n : ℝ))
    (htraffic_le_one : ∀ n, (trafficIntensity n : ℝ) ≤ 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (servers n : ℝ) *
          poissonPointProbability (servers n * trafficIntensity n) (servers n)) /
          (Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))))
      atTop (𝓝 0) := by
  have hfactor := tendsto_stirling_reciprocal_normalization.comp hservers
  have hdecay :=
    tendsto_exp_poissonLogRate_div_scaledSpareCapacity_of_tendsto_atTop
      htraffic_pos htraffic_le_one hscaled
  have hproduct := hfactor.mul hdecay
  have hproductZero : Tendsto
      (fun n : ℕ => (Real.sqrt 2 * Stirling.stirlingSeq (servers n))⁻¹ *
        (Real.exp ((servers n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)) /
          (Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))))
      atTop (𝓝 0) := by
    simpa using hproduct
  refine Tendsto.congr' ?_ hproductZero
  filter_upwards with n
  rw [sqrt_mul_poissonPointProbability_eq_stirling_correction
    (trafficIntensity n) (hservers_pos n) (htraffic_pos n)]
  ring

/-- The local Poisson limit in the QED regime follows from the exact Stirling
decomposition and the quadratic logarithmic correction. -/
theorem tendsto_sqrt_mul_poissonPointProbability_of_tendsto_qed_spareCapacity
    {trafficIntensity : ℕ → ℝ≥0} {beta : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) *
        poissonPointProbability (n * trafficIntensity n) n)
      atTop (𝓝 (standardGaussianDensity beta)) := by
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity n : ℝ))
      atTop (𝓝 1) :=
    tendsto_trafficIntensity_of_tendsto_qed_spareCapacity hscaled
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < (trafficIntensity n : ℝ) :=
    htraffic.eventually_const_lt (by norm_num)
  have hlogCorrection := tendsto_qed_logCorrection hscaled
  have hexponential : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) *
        (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)))
      atTop (𝓝 (Real.exp (-(beta ^ 2 / 2)))) := by
    exact (Real.continuous_exp.tendsto _).comp hlogCorrection
  have hproduct := tendsto_stirling_reciprocal_normalization.mul hexponential
  have hproduct' : Tendsto
      (fun n : ℕ => (Real.sqrt 2 * Stirling.stirlingSeq n)⁻¹ *
        Real.exp ((n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)))
      atTop (𝓝 (standardGaussianDensity beta)) := by
    rw [standardGaussianDensity_eq_mills_integrand]
    convert hproduct using 1
    ring_nf
  refine Tendsto.congr' ?_ hproduct'
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hpositive] with n hn hρ
    exact (sqrt_mul_poissonPointProbability_eq_stirling_correction
      (trafficIntensity n) hn hρ).symm

/-- The local Poisson limit holds along any positive server-count sequence
that tends to infinity. -/
theorem tendsto_sqrtServer_mul_poissonPointProbability_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ≥0} {beta : ℝ}
    (hservers : Tendsto servers atTop atTop)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) *
        poissonPointProbability (servers n * trafficIntensity n) (servers n))
      atTop (𝓝 (standardGaussianDensity beta)) := by
  have hserversReal : Tendsto (fun n : ℕ => (servers n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hservers
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hserversReal
  have hgapDiv : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (servers n : ℝ) * (1 - (trafficIntensity n : ℝ))) /
          Real.sqrt (servers n : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaled hsqrtServers
  have hgap : Tendsto (fun n : ℕ => 1 - (trafficIntensity n : ℝ))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgapDiv
    filter_upwards [hservers.eventually_gt_atTop 0] with n hn
    have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact_mod_cast hn
    field_simp [hsqrt_ne]
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity n : ℝ))
      atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < (trafficIntensity n : ℝ) :=
    htraffic.eventually_const_lt (by norm_num)
  have hlogCorrection :=
    tendsto_logCorrection_of_tendsto_scaled_spareCapacity hserversReal hscaled
  have hexponential : Tendsto
      (fun n : ℕ => Real.exp ((servers n : ℝ) *
        (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)))
      atTop (𝓝 (Real.exp (-(beta ^ 2 / 2)))) := by
    exact (Real.continuous_exp.tendsto _).comp hlogCorrection
  have hproduct :=
    (tendsto_stirling_reciprocal_normalization.comp hservers).mul hexponential
  have hproduct' : Tendsto
      (fun n : ℕ => (Real.sqrt 2 * Stirling.stirlingSeq (servers n))⁻¹ *
        Real.exp ((servers n : ℝ) *
          (Real.log (trafficIntensity n : ℝ) - (trafficIntensity n : ℝ) + 1)))
      atTop (𝓝 (standardGaussianDensity beta)) := by
    rw [standardGaussianDensity_eq_mills_integrand]
    convert hproduct using 1
    ring_nf
  refine Tendsto.congr' ?_ hproduct'
  filter_upwards [hservers.eventually_gt_atTop 0, hpositive] with n hn hρ
  exact (sqrt_mul_poissonPointProbability_eq_stirling_correction
    (trafficIntensity n) hn hρ).symm

/-- A finite square-root spare-capacity limit along any server-count sequence
that tends to infinity forces the traffic intensity to approach critical
load. -/
theorem tendsto_trafficIntensity_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ} {beta : ℝ}
    (hservers : Tendsto servers atTop atTop)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - trafficIntensity n))
      atTop (𝓝 beta)) :
    Tendsto trafficIntensity atTop (𝓝 1) := by
  have hsqrtServers : Tendsto (fun n : ℕ => Real.sqrt (servers n : ℝ))
      atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp hservers
  have hgapDiv : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (servers n : ℝ) * (1 - trafficIntensity n)) /
          Real.sqrt (servers n : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaled hsqrtServers
  have hgap : Tendsto (fun n : ℕ => 1 - trafficIntensity n) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgapDiv
    filter_upwards [hservers.eventually_gt_atTop 0] with n hn
    have hsqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact_mod_cast hn
    field_simp [hsqrt_ne]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)

/-- The strict Poisson lower-tail threshold along a diverging server-count
sequence has the same finite limit as the scaled spare capacity. -/
theorem tendsto_serverThreshold_of_tendsto_scaled_spareCapacity
    {servers : ℕ → ℕ} {trafficIntensity : ℕ → ℝ} {beta : ℝ}
    (hservers : Tendsto servers atTop atTop)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt (servers n : ℝ) * (1 - trafficIntensity n))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ =>
        (((servers n : ℝ) - 1 - (servers n : ℝ) * trafficIntensity n) /
          Real.sqrt ((servers n : ℝ) * trafficIntensity n)))
      atTop (𝓝 beta) := by
  have hsqrtServers : Tendsto (fun n : ℕ => Real.sqrt (servers n : ℝ))
      atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp hservers
  have htraffic := tendsto_trafficIntensity_of_tendsto_scaled_spareCapacity
    hservers hscaled
  have hservers_pos : ∀ᶠ n : ℕ in atTop, 0 < servers n :=
    hservers.eventually_gt_atTop 0
  have hsqrtTraffic : Tendsto (fun n : ℕ => Real.sqrt (trafficIntensity n))
      atTop (𝓝 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htraffic
  have hinvSqrtTraffic : Tendsto
      (fun n : ℕ => (Real.sqrt (trafficIntensity n))⁻¹)
      atTop (𝓝 1) := by
    simpa using hsqrtTraffic.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvSqrtServers : Tendsto
      (fun n : ℕ => (Real.sqrt (servers n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_div_atTop hsqrtServers (1 : ℝ)
  have hmain : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (servers n : ℝ) * (1 - trafficIntensity n)) *
          (Real.sqrt (trafficIntensity n))⁻¹ -
        (Real.sqrt (servers n : ℝ))⁻¹ *
          (Real.sqrt (trafficIntensity n))⁻¹)
      atTop (𝓝 beta) := by
    simpa using (hscaled.mul hinvSqrtTraffic).sub
      (hinvSqrtServers.mul hinvSqrtTraffic)
  refine Tendsto.congr' ?_ hmain
  filter_upwards [hservers_pos,
    htraffic.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hn hρ
  have hservers_nonneg : 0 ≤ (servers n : ℝ) := by positivity
  have hservers_sqrt_ne : Real.sqrt (servers n : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact_mod_cast hn
  have htraffic_sqrt_ne : Real.sqrt (trafficIntensity n) ≠ 0 :=
    (Real.sqrt_pos.2 hρ).ne'
  rw [Real.sqrt_mul hservers_nonneg]
  have hservers_square : Real.sqrt (servers n : ℝ) ^ 2 = (servers n : ℝ) :=
    Real.sq_sqrt hservers_nonneg
  field_simp [hservers_sqrt_ne, htraffic_sqrt_ne]
  rw [hservers_square]
  ring

/-- A QED spare-capacity limit along the positive server sequence `n + 1`
forces the corresponding traffic intensities to approach critical load. -/
theorem tendsto_qed_succ_trafficIntensity
    {trafficIntensity : ℕ → ℝ≥0} {beta : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ)) atTop (𝓝 1) := by
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hgapDiv : Tendsto
      (fun n : ℕ =>
        (Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (1 - (trafficIntensity (n + 1) : ℝ))) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaled hsqrtServers
  have hgap : Tendsto (fun n : ℕ => 1 - (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgapDiv
    filter_upwards with n
    have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact_mod_cast Nat.succ_pos n
    field_simp [hsqrt_ne]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)

/-- The strict Poisson lower-tail threshold for a positive server sequence
converges to the QED spare-capacity parameter.  Indexing servers by `n + 1`
avoids an artificial zero-server initial term. -/
theorem tendsto_qed_succ_serverThreshold
    {trafficIntensity : ℕ → ℝ≥0} {beta : ℝ}
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta)) :
    Tendsto
      (fun n : ℕ =>
        ((((n + 1 : ℕ) : ℝ) - 1 -
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ))) /
          Real.sqrt (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ))))
      atTop (𝓝 beta) := by
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hgapDiv : Tendsto
      (fun n : ℕ =>
        (Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (1 - (trafficIntensity (n + 1) : ℝ))) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    Tendsto.div_atTop hscaled hsqrtServers
  have hgap : Tendsto (fun n : ℕ => 1 - (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hgapDiv
    filter_upwards with n
    have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      exact_mod_cast Nat.succ_pos n
    field_simp [hsqrt_ne]
  have htraffic : Tendsto (fun n : ℕ => (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap)
  have hsqrtTraffic : Tendsto
      (fun n : ℕ => Real.sqrt (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htraffic
  have hinvSqrtTraffic : Tendsto
      (fun n : ℕ => (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using hsqrtTraffic.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvSqrtServers : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_div_atTop hsqrtServers (1 : ℝ)
  have hmain : Tendsto
      (fun n : ℕ =>
        (Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (1 - (trafficIntensity (n + 1) : ℝ))) *
          (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹ -
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
          (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹)
      atTop (𝓝 beta) := by
    simpa using (hscaled.mul hinvSqrtTraffic).sub
      (hinvSqrtServers.mul hinvSqrtTraffic)
  refine Tendsto.congr' ?_ hmain
  filter_upwards [htraffic.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hρ
  have hservers_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hservers_sqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.succ_pos n
  have htraffic_sqrt_ne : Real.sqrt (trafficIntensity (n + 1) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hρ).ne'
  rw [Real.sqrt_mul hservers_nonneg]
  have hservers_square : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hservers_nonneg
  field_simp [hservers_sqrt_ne, htraffic_sqrt_ne]
  rw [hservers_square]
  ring

/-- A cutoff below a positive server sequence has the expected standardized
Poisson limit when both its gap from the server threshold and the QED spare
capacity are on the square-root scale. -/
theorem tendsto_qed_succ_cutoffThreshold
    {trafficIntensity : ℕ → ℝ≥0} {beta delta : ℝ} {cutoff : ℕ → ℕ}
    (hcutoff : ∀ n, cutoff n ≤ n + 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcutoffGap : Tendsto
      (fun n : ℕ => ((n + 1 - cutoff n : ℕ) : ℝ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ =>
        (((cutoff n : ℝ) - 1 -
          (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ))) /
          Real.sqrt (((n + 1 : ℕ) : ℝ) * (trafficIntensity (n + 1) : ℝ))))
      atTop (𝓝 (beta - delta)) := by
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htraffic := tendsto_qed_succ_trafficIntensity hscaled
  have hsqrtTraffic : Tendsto
      (fun n : ℕ => Real.sqrt (trafficIntensity (n + 1) : ℝ))
      atTop (𝓝 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htraffic
  have hinvSqrtTraffic : Tendsto
      (fun n : ℕ => (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using hsqrtTraffic.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvSqrtServers : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_div_atTop hsqrtServers (1 : ℝ)
  have hmain : Tendsto
      (fun n : ℕ =>
        (Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (1 - (trafficIntensity (n + 1) : ℝ))) *
          (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹ -
        (((n + 1 - cutoff n : ℕ) : ℝ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) *
          (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹ -
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
          (Real.sqrt (trafficIntensity (n + 1) : ℝ))⁻¹)
      atTop (𝓝 (beta - delta)) := by
    simpa using ((hscaled.mul hinvSqrtTraffic).sub
      (hcutoffGap.mul hinvSqrtTraffic)).sub
        (hinvSqrtServers.mul hinvSqrtTraffic)
  refine Tendsto.congr' ?_ hmain
  filter_upwards [htraffic.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hρ
  have hservers_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hservers_sqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.succ_pos n
  have htraffic_sqrt_ne : Real.sqrt (trafficIntensity (n + 1) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hρ).ne'
  have hcutoff_cast : ((n + 1 - cutoff n : ℕ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) - (cutoff n : ℝ) := by
    rw [Nat.cast_sub (hcutoff n)]
  rw [Real.sqrt_mul hservers_nonneg, hcutoff_cast]
  have hservers_square : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hservers_nonneg
  field_simp [hservers_sqrt_ne, htraffic_sqrt_ne]
  rw [hservers_square]
  ring

/-- The local Poisson mass at a lower square-root-scale cutoff has the normal
density limit dictated by its standardized displacement. -/
theorem tendsto_sqrtServer_mul_poissonPointProbability_of_qed_succ_cutoff
    {trafficIntensity : ℕ → ℝ≥0} {beta delta : ℝ} {cutoff : ℕ → ℕ}
    (htraffic_pos : ∀ n, 0 < trafficIntensity n)
    (hcutoff_pos : ∀ n, 0 < cutoff n)
    (hcutoff : ∀ n, cutoff n ≤ n + 1)
    (hscaled : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (1 - (trafficIntensity (n + 1) : ℝ)))
      atTop (𝓝 beta))
    (hcutoffGap : Tendsto
      (fun n : ℕ => ((n + 1 - cutoff n : ℕ) : ℝ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 delta)) :
    Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        poissonPointProbability
          (((n + 1 : ℕ) : ℝ≥0) * trafficIntensity (n + 1)) (cutoff n))
      atTop (𝓝 (standardGaussianDensity (beta - delta))) := by
  let adjustedTrafficIntensity : ℕ → ℝ≥0 := fun n =>
    (((n + 1 : ℕ) : ℝ≥0) * trafficIntensity (n + 1) / (cutoff n : ℝ≥0))
  have hserversReal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsqrtServers : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hserversReal
  have hinvSqrtServers : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_div_atTop hsqrtServers (1 : ℝ)
  have hcutoffRatio : Tendsto
      (fun n : ℕ => (cutoff n : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hgapRatio := hcutoffGap.mul hinvSqrtServers
    have hmain : Tendsto
        (fun n : ℕ => 1 -
          (((n + 1 - cutoff n : ℕ) : ℝ) /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) *
              (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          hgapRatio)
    refine Tendsto.congr' ?_ hmain
    filter_upwards with n
    have hserver_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)).ne'
    have hcutoff_cast : ((n + 1 - cutoff n : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) - (cutoff n : ℝ) := by
      rw [Nat.cast_sub (hcutoff n)]
    rw [hcutoff_cast]
    have hsquare : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    field_simp [hserver_ne, hsqrt_ne]
    rw [hsquare]
    ring
  have hcutoffReal : Tendsto (fun n : ℕ => (cutoff n : ℝ)) atTop atTop := by
    have hproduct := hcutoffRatio.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
      hserversReal
    refine Tendsto.congr' ?_ hproduct
    filter_upwards with n
    have hserver_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp [hserver_ne]
  have hcutoffAtTop : Tendsto cutoff atTop atTop :=
    tendsto_natCast_atTop_iff.mp hcutoffReal
  have hsqrtCutoffRatio : Tendsto
      (fun n : ℕ => Real.sqrt (cutoff n : ℝ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hcutoffRatio
    have hroot' : Tendsto
        (fun n : ℕ => Real.sqrt ((cutoff n : ℝ) / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 1) := by
      simpa [Function.comp_def] using hroot
    refine Tendsto.congr' ?_ hroot'
    filter_upwards with n
    rw [Real.sqrt_div (by positivity : 0 ≤ (cutoff n : ℝ))]
  have hsqrtServerOverCutoff : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) /
        Real.sqrt (cutoff n : ℝ))
      atTop (𝓝 1) := by
    have hinv := hsqrtCutoffRatio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hinv' : Tendsto
        (fun n : ℕ => (Real.sqrt (cutoff n : ℝ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 1) := by
      simpa using hinv
    refine Tendsto.congr' ?_ hinv'
    filter_upwards with n
    have hserver_sqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)).ne'
    have hcutoff_sqrt_ne : Real.sqrt (cutoff n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast hcutoff_pos n)).ne'
    field_simp [hserver_sqrt_ne, hcutoff_sqrt_ne]
  have hadjusted_pos (n : ℕ) : 0 < adjustedTrafficIntensity n := by
    dsimp [adjustedTrafficIntensity]
    exact div_pos
      (mul_pos (by exact_mod_cast Nat.succ_pos n) (htraffic_pos (n + 1)))
      (by exact_mod_cast hcutoff_pos n)
  have hadjustedScaled : Tendsto
      (fun n : ℕ => Real.sqrt (cutoff n : ℝ) *
        (1 - (adjustedTrafficIntensity n : ℝ)))
      atTop (𝓝 (beta - delta)) := by
    have hcore := hscaled.sub hcutoffGap
    have hmain := hcore.mul hsqrtServerOverCutoff
    have hmain' : Tendsto
        (fun n : ℕ =>
          (Real.sqrt ((n + 1 : ℕ) : ℝ) *
            (1 - (trafficIntensity (n + 1) : ℝ)) -
            ((n + 1 - cutoff n : ℕ) : ℝ) /
              Real.sqrt ((n + 1 : ℕ) : ℝ)) *
            (Real.sqrt ((n + 1 : ℕ) : ℝ) /
              Real.sqrt (cutoff n : ℝ)))
        atTop (𝓝 (beta - delta)) := by
      simpa using hmain
    refine Tendsto.congr' ?_ hmain'
    filter_upwards with n
    have hcutoff_real_pos : 0 < (cutoff n : ℝ) := by
      exact_mod_cast hcutoff_pos n
    have hserver_sqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)).ne'
    have hcutoff_sqrt_ne : Real.sqrt (cutoff n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 hcutoff_real_pos).ne'
    have hcutoff_ne : (cutoff n : ℝ) ≠ 0 := ne_of_gt hcutoff_real_pos
    have hcutoff_cast : ((n + 1 - cutoff n : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) - (cutoff n : ℝ) := by
      rw [Nat.cast_sub (hcutoff n)]
    symm
    dsimp [adjustedTrafficIntensity]
    simp only [NNReal.coe_natCast]
    rw [hcutoff_cast]
    have hsquare : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hcutoff_square : Real.sqrt (cutoff n : ℝ) ^ 2 = (cutoff n : ℝ) :=
      Real.sq_sqrt hcutoff_real_pos.le
    field_simp [hserver_sqrt_ne, hcutoff_sqrt_ne, hcutoff_ne]
    rw [hsquare, hcutoff_square]
    ring
  have hlocal :=
    tendsto_sqrtServer_mul_poissonPointProbability_of_tendsto_scaled_spareCapacity
      hcutoffAtTop hadjustedScaled
  have hmean_eq (n : ℕ) :
      (cutoff n : ℝ≥0) * adjustedTrafficIntensity n =
        ((n + 1 : ℕ) : ℝ≥0) * trafficIntensity (n + 1) := by
    dsimp [adjustedTrafficIntensity]
    have hcutoff_ne : (cutoff n : ℝ≥0) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hcutoff_pos n))
    field_simp [hcutoff_ne]
  have hproduct := hsqrtServerOverCutoff.mul hlocal
  have hproduct' : Tendsto
      (fun n : ℕ =>
        (Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt (cutoff n : ℝ)) *
          (Real.sqrt (cutoff n : ℝ) *
            poissonPointProbability
              ((cutoff n : ℝ≥0) * adjustedTrafficIntensity n) (cutoff n)))
      atTop (𝓝 (standardGaussianDensity (beta - delta))) := by
    simpa using hproduct
  refine Tendsto.congr' ?_ hproduct'
  filter_upwards with n
  rw [hmean_eq]
  have hcutoff_sqrt_ne : Real.sqrt (cutoff n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hcutoff_pos n)).ne'
  field_simp [hcutoff_sqrt_ne]

end AppliedModelingLib.Probability.Queueing
