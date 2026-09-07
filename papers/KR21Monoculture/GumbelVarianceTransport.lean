import KR21Monoculture.GumbelRUMPlackettLuce
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

/-!
# Variance Transport for the Explicit KR21 Gumbel Construction

The existing Gumbel ranking construction uses the literal scale-one innovation
`-log T` for `T ~ Exp(1)` and the displayed scale `sqrt 6 / pi`.  This module
proves the normalization algebra only: an explicit proof of the base identity
`Var[-log T] = pi^2 / 6` yields unit variance after scaling and translation.

It does not assert that base identity, identify the resulting law with an
underspecified source Gumbel convention, or use a unit-variance certificate.
-/

namespace KR21Monoculture

/-!
## Concrete Transform Bridge

The base law is not an abstract ``Gumbel'' placeholder.  The following
lemmas derive its moment-generating transform directly from the density of
`expMeasure 1` and Euler's Gamma integral.  The remaining unproved analytic
step is only the second-order special-value calculation
`iteratedDeriv 2 (fun t => Gamma (1 - t)) 0 = gamma^2 + pi^2 / 6`
(equivalently the trigamma value at one).
-/

private lemma ae_ne_zero_volume : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
  rw [ae_iff]
  simpa using Real.volume_singleton

private lemma exp_neglog_eq_rpow_neg (x t : ℝ) (hx : 0 < x) :
    Real.exp (t * (-Real.log x)) = x ^ (-t) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- The literal `-log Exp(1)` transform has Gamma moment-generating function. -/
theorem integral_expMeasure_neglog_exp_eq_Gamma (t : ℝ) (ht : t < 1) :
    ∫ x : ℝ, Real.exp (t * (-Real.log x)) ∂(expMeasure 1) =
      Real.Gamma (1 - t) := by
  change ∫ x : ℝ, Real.exp (t * (-Real.log x)) ∂
      volume.withDensity (exponentialPDF 1) = Real.Gamma (1 - t)
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul]
    have h_ae :
        (fun x : ℝ => (exponentialPDF 1 x).toReal * Real.exp (t * (-Real.log x))) =ᶠ[ae volume]
          (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x) * x ^ (-t)) := by
      filter_upwards [ae_ne_zero_volume] with x hx
      simp only [Set.indicator, Set.mem_Ioi]
      by_cases hpos : 0 < x
      · have hnonneg : 0 ≤ x := hpos.le
        rw [if_pos hpos]
        rw [exponentialPDF_eq, if_pos hnonneg]
        rw [ENNReal.toReal_ofReal]
        · rw [exp_neglog_eq_rpow_neg x t hpos]
          ring_nf
        · positivity
      · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
        rw [if_neg hpos]
        rw [exponentialPDF_eq, if_neg (not_le.mpr hneg)]
        norm_num
    rw [integral_congr_ae h_ae, integral_indicator measurableSet_Ioi]
    rw [Real.Gamma_eq_integral (by linarith : 0 < 1 - t)]
    congr 1
    funext x
    congr 2
    ring
  · exact (measurable_exponentialPDFReal 1).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- Finiteness of the literal transform, derived from its nonzero Gamma value. -/
theorem integrable_expMeasure_neglog_exp (t : ℝ) (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * (-Real.log x))) (expMeasure 1) := by
  by_contra h
  have hzero := integral_undef h
  rw [integral_expMeasure_neglog_exp_eq_Gamma t ht] at hzero
  exact (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - t)).ne' hzero

/-- The scale-one innovation's MGF is the concrete Gamma transform. -/
theorem scaleOneGumbelInnovation_mgf_eq_Gamma (t : ℝ) (ht : t < 1) :
    mgf scaleOneGumbelInnovation (expMeasure 1) t = Real.Gamma (1 - t) := by
  simpa only [mgf, scaleOneGumbelInnovation] using
    integral_expMeasure_neglog_exp_eq_Gamma t ht

/-- The literal innovation has an open interval of finite exponential moments around zero. -/
theorem scaleOneGumbelInnovation_zero_mem_interior_integrableExpSet :
    0 ∈ interior (integrableExpSet scaleOneGumbelInnovation (expMeasure 1)) := by
  have hneg : (-1 / 2 : ℝ) ∈ integrableExpSet scaleOneGumbelInnovation (expMeasure 1) := by
    change Integrable (fun x : ℝ => Real.exp ((-1 / 2) * scaleOneGumbelInnovation x))
      (expMeasure 1)
    simpa only [scaleOneGumbelInnovation] using
      integrable_expMeasure_neglog_exp (-1 / 2) (by norm_num)
  have hpos : (1 / 2 : ℝ) ∈ integrableExpSet scaleOneGumbelInnovation (expMeasure 1) := by
    change Integrable (fun x : ℝ => Real.exp ((1 / 2) * scaleOneGumbelInnovation x))
      (expMeasure 1)
    simpa only [scaleOneGumbelInnovation] using
      integrable_expMeasure_neglog_exp (1 / 2) (by norm_num)
  have hsegment := convex_integrableExpSet.openSegment_subset hneg hpos
  rw [openSegment_eq_Ioo (by norm_num : (-1 / 2 : ℝ) < 1 / 2)] at hsegment
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro x hx
  have habs : |x| < 1 / 2 := by
    simpa [Real.dist_eq] using hx
  apply hsegment
  constructor <;> linarith [abs_lt.mp habs]

private lemma scaleOneGumbelInnovation_mgf_eventuallyEq_Gamma :
    mgf scaleOneGumbelInnovation (expMeasure 1) =ᶠ[𝓝 0]
      fun t => Real.Gamma (1 - t) := by
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
  exact scaleOneGumbelInnovation_mgf_eq_Gamma t ht

private lemma scaleOneGumbelInnovation_firstGammaDerivative :
    iteratedDeriv 1 (fun t : ℝ => Real.Gamma (1 - t)) 0 =
      Real.eulerMascheroniConstant := by
  have hderiv : HasDerivAt (fun t : ℝ => Real.Gamma (1 - t))
      Real.eulerMascheroniConstant 0 := by
    have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub (hasDerivAt_id 0) using 1
      all_goals simp [sub_eq_add_neg]
    have hgamma : HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) (1 - (0 : ℝ)) := by
      norm_num
      exact Real.hasDerivAt_Gamma_one
    convert hgamma.comp 0 hinner using 1
    all_goals ring
  simpa [iteratedDeriv_one] using hderiv.deriv

/--
All probability and transform obligations for the literal innovation reduce
its variance to the second Gamma derivative.  The displayed right side is the
single remaining special-function target; it is not assumed here.
-/
theorem scaleOneGumbelInnovation_variance_eq_Gamma_secondDerivative :
    Var[scaleOneGumbelInnovation; expMeasure 1] =
      iteratedDeriv 2 (fun t : ℝ => Real.Gamma (1 - t)) 0 -
        Real.eulerMascheroniConstant ^ 2 := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hinterior := scaleOneGumbelInnovation_zero_mem_interior_integrableExpSet
  rw [variance_eq_sub
    (memLp_of_mem_interior_integrableExpSet hinterior (2 : NNReal))]
  rw [← iteratedDeriv_mgf_zero hinterior 2]
  have hmom1 : ∫ x : ℝ, scaleOneGumbelInnovation x ∂(expMeasure 1) =
      iteratedDeriv 1 (mgf scaleOneGumbelInnovation (expMeasure 1)) 0 := by
    rw [iteratedDeriv_mgf_zero hinterior 1]
    simp
  rw [hmom1]
  rw [scaleOneGumbelInnovation_mgf_eventuallyEq_Gamma.iteratedDeriv_eq 2,
    scaleOneGumbelInnovation_mgf_eventuallyEq_Gamma.iteratedDeriv_eq 1,
    scaleOneGumbelInnovation_firstGammaDerivative]

/--
The scalar law obtained by translating and scaling the actual scale-one
`-log Exp(1)` measure.  The name describes the displayed construction only;
unit variance is established below only from the explicit base variance
identity.
-/
noncomputable def explicitScaledGumbelMeasure (location : ℝ) : Measure ℝ :=
  scaleOneGumbelMeasure.map
    (fun g => unitVarianceGumbelScale * (location + g))

/-- The scalar translation-and-scale map is measurable. -/
theorem measurable_explicitScaledGumbelMap (location : ℝ) :
    Measurable (fun g : ℝ => unitVarianceGumbelScale * (location + g)) := by
  fun_prop

/-- The explicit scalar construction is a probability law. -/
theorem explicitScaledGumbelMeasure_isProbabilityMeasure (location : ℝ) :
    IsProbabilityMeasure (explicitScaledGumbelMeasure location) := by
  letI : IsProbabilityMeasure scaleOneGumbelMeasure :=
    scaleOneGumbelMeasure_isProbabilityMeasure
  unfold explicitScaledGumbelMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_explicitScaledGumbelMap location).aemeasurable

/--
The variance of the scale-one Gumbel law is exactly the variance of its
displayed `-log Exp(1)` innovation.  Thus the remaining analytic identity is
about this literal transformed exponential measure, not a named distribution.
-/
theorem scaleOneGumbelMeasure_variance_eq_innovationVariance :
    Var[id; scaleOneGumbelMeasure] =
      Var[scaleOneGumbelInnovation; expMeasure 1] := by
  unfold scaleOneGumbelMeasure
  exact ProbabilityTheory.variance_id_map
    measurable_scaleOneGumbelInnovation.aemeasurable

/--
The exact normalization algebra for the displayed Gumbel scale.  Its premise
is deliberately the literal base-law variance equality that remains to be
proved analytically; no source-facing unit-variance assertion is available
without that premise.
-/
theorem explicitScaledGumbelMeasure_variance_eq_one_of_scaleOneVariance
    (location : ℝ)
    (hbaseVariance : Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6) :
    Var[id; explicitScaledGumbelMeasure location] = 1 := by
  letI : IsProbabilityMeasure scaleOneGumbelMeasure :=
    scaleOneGumbelMeasure_isProbabilityMeasure
  rw [explicitScaledGumbelMeasure]
  rw [ProbabilityTheory.variance_id_map
    (measurable_explicitScaledGumbelMap location).aemeasurable]
  rw [ProbabilityTheory.variance_const_mul]
  change unitVarianceGumbelScale ^ 2 *
    Var[(fun g : ℝ => location + g); scaleOneGumbelMeasure] = 1
  have htranslate :
      Var[(fun g : ℝ => location + g); scaleOneGumbelMeasure] =
        Var[id; scaleOneGumbelMeasure] := by
    simpa only [id_eq] using
      (ProbabilityTheory.variance_const_add
        (X := id) (μ := scaleOneGumbelMeasure)
        measurable_id.aestronglyMeasurable location)
  rw [htranslate, hbaseVariance]
  unfold unitVarianceGumbelScale
  have hsqrt : Real.sqrt (6 : ℝ) ^ 2 = 6 := by
    norm_num
  calc
    (Real.sqrt 6 / Real.pi) ^ 2 * (Real.pi ^ 2 / 6) =
        Real.sqrt 6 ^ 2 / 6 := by
      field_simp [Real.pi_ne_zero]
    _ = 1 := by
      rw [hsqrt]
      norm_num

end KR21Monoculture
