import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Tilted

/-!
# Exponential tilts of real Gaussian laws

This module records the elementary Esscher-transform identity for a real
Gaussian law.  It is source-neutral probability infrastructure: a linear
exponential tilt preserves the variance and shifts the mean by `variance *
tilt`.
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/--
Exponentially tilting a real Gaussian law by `x ↦ tilt * x` preserves its
variance and shifts its mean by `variance * tilt`.

The statement also covers the degenerate variance-zero Gaussian: then both
sides are the same point mass.  The proof identifies the two probability
laws through their moment-generating functions.
-/
theorem gaussianReal_tilted_linear_eq_shift
    (mean : ℝ) (variance : NNReal) (tilt : ℝ) :
    (gaussianReal mean variance).tilted (fun x ↦ tilt * x) =
      gaussianReal (mean + (variance : ℝ) * tilt) variance := by
  let baseLaw : Measure ℝ := gaussianReal mean variance
  let tiltedLaw : Measure ℝ := baseLaw.tilted (fun x ↦ tilt * x)
  let shiftedLaw : Measure ℝ :=
    gaussianReal (mean + (variance : ℝ) * tilt) variance
  letI : IsProbabilityMeasure baseLaw := by
    simpa [baseLaw] using
      (inferInstance : IsProbabilityMeasure (gaussianReal mean variance))
  letI : NeZero baseLaw := ⟨IsProbabilityMeasure.ne_zero baseLaw⟩
  have htiltIntegrable :
      Integrable (fun x : ℝ ↦ rexp (tilt * x)) baseLaw := by
    simpa [baseLaw] using
      (integrable_exp_mul_gaussianReal (μ := mean) (v := variance) tilt)
  letI : IsProbabilityMeasure tiltedLaw := by
    simpa [tiltedLaw] using
      (isProbabilityMeasure_tilted (μ := baseLaw) htiltIntegrable)
  letI : IsProbabilityMeasure shiftedLaw := by
    simpa [shiftedLaw] using
      (inferInstance : IsProbabilityMeasure
        (gaussianReal (mean + (variance : ℝ) * tilt) variance))
  have htiltedExp : ∀ s : ℝ,
      Integrable (fun x : ℝ ↦ rexp (s * x)) tiltedLaw := by
    intro s
    rw [show tiltedLaw = baseLaw.tilted (fun x ↦ tilt * x) by rfl,
      integrable_tilted_iff htiltIntegrable]
    convert integrable_exp_mul_gaussianReal (μ := mean) (v := variance)
      (tilt + s) using 1
    ext x
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hmgf : mgf id tiltedLaw = mgf id shiftedLaw := by
    ext s
    calc
      mgf id tiltedLaw s =
          mgf id baseLaw (tilt + s) / mgf id baseLaw tilt := by
        unfold mgf
        rw [show tiltedLaw = baseLaw.tilted (fun x ↦ tilt * x) by rfl,
          integral_exp_tilted]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        simp only [Pi.add_apply, id_eq]
        congr 1
        ring
      _ = rexp ((mean + (variance : ℝ) * tilt) * s +
          (variance : ℝ) * s ^ 2 / 2) := by
        rw [show baseLaw = gaussianReal mean variance by rfl,
          mgf_id_gaussianReal]
        rw [← Real.exp_sub]
        congr 1
        ring
      _ = mgf id shiftedLaw s := by
        rw [show shiftedLaw =
          gaussianReal (mean + (variance : ℝ) * tilt) variance by rfl,
          mgf_id_gaussianReal]
  change tiltedLaw = shiftedLaw
  apply Measure.ext_of_complexMGF_id_eq
  have hdomain : integrableExpSet id tiltedLaw = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    simpa [integrableExpSet] using htiltedExp s
  have heq := eqOn_complexMGF_of_mgf (X := id) (Y := id)
    (μ := tiltedLaw) (μ' := shiftedLaw) hmgf
  rw [hdomain] at heq
  exact funext fun z ↦ heq (by simp)

/--
A prescribed mean shift of a nondegenerate real Gaussian is a linear
exponential tilt of the original law.  This is the rearranged form convenient
when a Bayesian calculation first produces the shifted posterior law.
-/
theorem gaussianReal_shift_eq_tilted_linear
    (mean shift : ℝ) (variance : NNReal) (hvariance : 0 < variance) :
    gaussianReal (mean + shift) variance =
      (gaussianReal mean variance).tilted
        (fun x ↦ (shift / (variance : ℝ)) * x) := by
  rw [gaussianReal_tilted_linear_eq_shift]
  congr 1
  have hvariance_ne : (variance : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hvariance
  field_simp

private theorem gaussianReal_quadratic_tilt_density
    (mean variance noiseVariance : ℝ)
    (hvariance : 0 < variance) (hnoiseVariance : 0 < noiseVariance) :
    ∃ normalizer : ℝ, 0 < normalizer ∧ ∀ x : ℝ,
      Real.exp (-x ^ 2 / (2 * noiseVariance)) *
          gaussianPDFReal mean variance.toNNReal x =
        normalizer *
          gaussianPDFReal (mean * noiseVariance / (variance + noiseVariance))
            (variance * noiseVariance / (variance + noiseVariance)).toNNReal x := by
  let posteriorVariance : ℝ := variance * noiseVariance / (variance + noiseVariance)
  let posteriorMean : ℝ := mean * noiseVariance / (variance + noiseVariance)
  let priorCoefficient : ℝ :=
    (Real.sqrt (2 * Real.pi * (variance.toNNReal : ℝ)))⁻¹
  let posteriorCoefficient : ℝ :=
    (Real.sqrt (2 * Real.pi * (posteriorVariance.toNNReal : ℝ)))⁻¹
  let normalizer : ℝ := (priorCoefficient / posteriorCoefficient) *
    Real.exp (-mean ^ 2 / (2 * (variance + noiseVariance)))
  have hvarianceCoe : (variance.toNNReal : ℝ) = variance :=
    Real.coe_toNNReal _ hvariance.le
  have hsum : 0 < variance + noiseVariance := add_pos hvariance hnoiseVariance
  have hposteriorVariance : 0 < posteriorVariance := by
    dsimp [posteriorVariance]
    exact div_pos (mul_pos hvariance hnoiseVariance) hsum
  have hposteriorVarianceCoe :
      (posteriorVariance.toNNReal : ℝ) = posteriorVariance :=
    Real.coe_toNNReal _ hposteriorVariance.le
  have hposteriorCoefficient_ne : posteriorCoefficient ≠ 0 := by
    dsimp [posteriorCoefficient]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  refine ⟨normalizer, ?_, ?_⟩
  · dsimp [normalizer]
    exact mul_pos (div_pos (by
      dsimp [priorCoefficient]
      exact inv_pos.2 (Real.sqrt_pos.2 (by positivity)))
      (by
        dsimp [posteriorCoefficient]
        exact inv_pos.2 (Real.sqrt_pos.2 (by positivity))))
      (Real.exp_pos _)
  · intro x
    simp only [gaussianPDFReal, normalizer, priorCoefficient,
      posteriorCoefficient]
    rw [hvarianceCoe, hposteriorVarianceCoe]
    change Real.exp (-x ^ 2 / (2 * noiseVariance)) *
        ((Real.sqrt (2 * Real.pi * variance))⁻¹ *
          Real.exp (-((x - mean) ^ 2) / (2 * variance))) =
      (((Real.sqrt (2 * Real.pi * variance))⁻¹ /
          (Real.sqrt (2 * Real.pi * posteriorVariance))⁻¹) *
        Real.exp (-mean ^ 2 / (2 * (variance + noiseVariance)))) *
          ((Real.sqrt (2 * Real.pi * posteriorVariance))⁻¹ *
            Real.exp (-((x - posteriorMean) ^ 2) / (2 * posteriorVariance)))
    have hexp :
        Real.exp (-x ^ 2 / (2 * noiseVariance)) *
            Real.exp (-((x - mean) ^ 2) / (2 * variance)) =
          Real.exp (-mean ^ 2 / (2 * (variance + noiseVariance))) *
            Real.exp (-((x - posteriorMean) ^ 2) /
              (2 * posteriorVariance)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [posteriorVariance, posteriorMean]
      field_simp [ne_of_gt hvariance, ne_of_gt hnoiseVariance, ne_of_gt hsum]
      ring
    calc
      Real.exp (-x ^ 2 / (2 * noiseVariance)) *
          ((Real.sqrt (2 * Real.pi * variance))⁻¹ *
            Real.exp (-((x - mean) ^ 2) / (2 * variance))) =
          (Real.sqrt (2 * Real.pi * variance))⁻¹ *
            (Real.exp (-x ^ 2 / (2 * noiseVariance)) *
              Real.exp (-((x - mean) ^ 2) / (2 * variance))) := by ring
      _ = (Real.sqrt (2 * Real.pi * variance))⁻¹ *
            (Real.exp (-mean ^ 2 / (2 * (variance + noiseVariance))) *
              Real.exp (-((x - posteriorMean) ^ 2) /
                (2 * posteriorVariance))) := by rw [hexp]
      _ =
          (((Real.sqrt (2 * Real.pi * variance))⁻¹ /
              (Real.sqrt (2 * Real.pi * posteriorVariance))⁻¹) *
            Real.exp (-mean ^ 2 / (2 * (variance + noiseVariance)))) *
              ((Real.sqrt (2 * Real.pi * posteriorVariance))⁻¹ *
                Real.exp (-((x - posteriorMean) ^ 2) /
                  (2 * posteriorVariance))) := by
          field_simp [hposteriorCoefficient_ne]

/--
Tilting a nondegenerate real Gaussian by the quadratic likelihood factor
`x ↦ -x² / (2 * noiseVariance)` gives the usual Gaussian posterior obtained
from a zero-centered Gaussian signal with variance `noiseVariance`.

This is deliberately stated as an equality of normalized laws, so downstream
Bayesian arguments may use it before imposing any selected-action restriction.
-/
theorem gaussianReal_tilted_quadratic_eq_posterior
    (mean variance noiseVariance : ℝ)
    (hvariance : 0 < variance) (hnoiseVariance : 0 < noiseVariance) :
    (gaussianReal mean variance.toNNReal).tilted
      (fun x ↦ -x ^ 2 / (2 * noiseVariance)) =
      gaussianReal (mean * noiseVariance / (variance + noiseVariance))
        (variance * noiseVariance / (variance + noiseVariance)).toNNReal := by
  let baseLaw : Measure ℝ := gaussianReal mean variance.toNNReal
  let posteriorVariance : ℝ := variance * noiseVariance / (variance + noiseVariance)
  let posteriorMean : ℝ := mean * noiseVariance / (variance + noiseVariance)
  let posteriorLaw : Measure ℝ := gaussianReal posteriorMean posteriorVariance.toNNReal
  let likelihood : ℝ → ℝ := fun x ↦ -x ^ 2 / (2 * noiseVariance)
  let normalizingIntegral : ℝ := ∫ x, Real.exp (likelihood x) ∂baseLaw
  letI : IsProbabilityMeasure baseLaw := by
    dsimp [baseLaw]
    infer_instance
  have hintegrable : Integrable (fun x : ℝ ↦ Real.exp (likelihood x)) baseLaw := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (by
      dsimp [likelihood]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x))
        (by positivity))
  have hnormalizingIntegral : 0 < normalizingIntegral := by
    letI : NeZero baseLaw := ⟨IsProbabilityMeasure.ne_zero baseLaw⟩
    exact integral_exp_pos hintegrable
  obtain ⟨densityNormalizer, hdensityNormalizer,
    hdensity⟩ := gaussianReal_quadratic_tilt_density mean variance noiseVariance
      hvariance hnoiseVariance
  let proportionality : ℝ≥0∞ :=
    ENNReal.ofReal (densityNormalizer / normalizingIntegral)
  have hpointwise : ∀ x : ℝ,
      gaussianPDF mean variance.toNNReal x *
        (↑(NNReal.mk (Real.exp (likelihood x) / normalizingIntegral)
          (by positivity)) : ℝ≥0∞) =
        proportionality * gaussianPDF posteriorMean posteriorVariance.toNNReal x := by
    intro x
    change ENNReal.ofReal (gaussianPDFReal mean variance.toNNReal x) *
        (↑(NNReal.mk (Real.exp (likelihood x) / normalizingIntegral)
          (by positivity)) : ℝ≥0∞) =
      ENNReal.ofReal (densityNormalizer / normalizingIntegral) *
        ENNReal.ofReal (gaussianPDFReal posteriorMean posteriorVariance.toNNReal x)
    rw [← ENNReal.ofReal_eq_coe_nnreal]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rw [← ENNReal.ofReal_mul
      (div_nonneg hdensityNormalizer.le hnormalizingIntegral.le)]
    congr 1
    change gaussianPDFReal mean variance.toNNReal x *
        (Real.exp (likelihood x) / normalizingIntegral) =
      (densityNormalizer / normalizingIntegral) *
        gaussianPDFReal posteriorMean posteriorVariance.toNNReal x
    calc
      gaussianPDFReal mean variance.toNNReal x *
          (Real.exp (likelihood x) / normalizingIntegral) =
          (Real.exp (likelihood x) *
            gaussianPDFReal mean variance.toNNReal x) / normalizingIntegral := by ring
      _ = (densityNormalizer *
          gaussianPDFReal posteriorMean posteriorVariance.toNNReal x) /
            normalizingIntegral := by
          rw [show Real.exp (likelihood x) *
              gaussianPDFReal mean variance.toNNReal x =
              densityNormalizer *
                gaussianPDFReal posteriorMean posteriorVariance.toNNReal x by
            simpa only [likelihood, posteriorMean, posteriorVariance] using hdensity x]
      _ = (densityNormalizer / normalizingIntegral) *
          gaussianPDFReal posteriorMean posteriorVariance.toNNReal x := by ring
  have hbaseDensity : baseLaw =
      volume.withDensity (gaussianPDF mean variance.toNNReal) := by
    dsimp [baseLaw]
    rw [gaussianReal_of_var_ne_zero]
    exact (Real.toNNReal_pos.mpr hvariance).ne'
  have hposteriorDensity : posteriorLaw =
      volume.withDensity (gaussianPDF posteriorMean posteriorVariance.toNNReal) := by
    dsimp [posteriorLaw]
    rw [gaussianReal_of_var_ne_zero]
    have hposteriorVariance : 0 < posteriorVariance := by
      dsimp [posteriorVariance]
      exact div_pos (mul_pos hvariance hnoiseVariance)
        (add_pos hvariance hnoiseVariance)
    exact (Real.toNNReal_pos.mpr hposteriorVariance).ne'
  have htilted : baseLaw.tilted likelihood = proportionality • posteriorLaw := by
    rw [MeasureTheory.tilted_eq_withDensity_nnreal, hbaseDensity,
      ← withDensity_mul]
    · rw [hposteriorDensity, ← withDensity_smul]
      · congr 1
        funext x
        rw [← hbaseDensity] at *
        simpa only [Pi.smul_apply, smul_eq_mul] using hpointwise x
      · exact measurable_gaussianPDF _ _
    · exact measurable_gaussianPDF _ _
    · exact (by fun_prop)
  have hprobability : IsProbabilityMeasure (baseLaw.tilted likelihood) := by
    letI : NeZero baseLaw := ⟨IsProbabilityMeasure.ne_zero baseLaw⟩
    exact isProbabilityMeasure_tilted hintegrable
  have hproportionality : proportionality = 1 := by
    have huniv : (proportionality • posteriorLaw) Set.univ = 1 := by
      rw [← htilted]
      exact hprobability.measure_univ
    simpa [posteriorLaw] using huniv
  change baseLaw.tilted likelihood = posteriorLaw
  rw [htilted, hproportionality, one_smul]

end

end Probability
end AppliedModelingLib
