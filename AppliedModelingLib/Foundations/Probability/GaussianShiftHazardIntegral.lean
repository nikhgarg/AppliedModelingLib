import AppliedModelingLib.Foundations.Probability.GaussianMathlib

/-!
# Gaussian-shift hazard integrals

Reusable continuity control for expectations of a standard-Gaussian hazard
under an affine parameter shift. The result is measure-neutral: callers must
establish the displayed integrability of their literal random shift.
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Expectation of the standard Gaussian hazard after an affine parameter
shift. -/
def gaussianShiftHazardIntegral
    {Alpha : Type*} [MeasurableSpace Alpha]
    (mu : Measure Alpha) (coefficient : ℝ) (shift : Alpha -> ℝ)
    (parameter : ℝ) : ℝ :=
  ∫ sample, standardGaussianHazard
    (coefficient * parameter + shift sample) ∂mu

/-- A Gaussian-hazard shift expectation is Lipschitz in its scalar parameter.
The only analytic premise is integrability of the literal integrand at each
parameter; the Lipschitz bound itself follows from the checked global hazard
derivative bound. -/
theorem gaussianShiftHazardIntegral_lipschitzWith
    {Alpha : Type*} [MeasurableSpace Alpha]
    (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (coefficient : ℝ) (shift : Alpha -> ℝ)
    (hintegrable : ∀ parameter,
      Integrable (fun sample => standardGaussianHazard
        (coefficient * parameter + shift sample)) mu) :
    LipschitzWith ‖coefficient‖₊
      (gaussianShiftHazardIntegral mu coefficient shift) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro left right
  let leftIntegrand : Alpha -> ℝ := fun sample =>
    standardGaussianHazard (coefficient * left + shift sample)
  let rightIntegrand : Alpha -> ℝ := fun sample =>
    standardGaussianHazard (coefficient * right + shift sample)
  have hleft : Integrable leftIntegrand mu := by
    simpa [leftIntegrand] using hintegrable left
  have hright : Integrable rightIntegrand mu := by
    simpa [rightIntegrand] using hintegrable right
  have hpoint : ∀ sample,
      ‖leftIntegrand sample - rightIntegrand sample‖ ≤
        ‖coefficient‖ * ‖left - right‖ := by
    intro sample
    have hlip := standardGaussianHazard_lipschitzWith_one.dist_le_mul
      (coefficient * left + shift sample)
      (coefficient * right + shift sample)
    have harg : coefficient * left + shift sample -
        (coefficient * right + shift sample) =
          coefficient * (left - right) := by
      ring
    rw [Real.dist_eq, Real.dist_eq, harg] at hlip
    simpa [leftIntegrand, rightIntegrand, Real.norm_eq_abs, abs_mul] using hlip
  have hbound :
      ‖∫ sample, leftIntegrand sample - rightIntegrand sample ∂mu‖ ≤
        (‖coefficient‖ * ‖left - right‖) * mu.real Set.univ := by
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall hpoint)
  have hsub :
      (∫ sample, leftIntegrand sample - rightIntegrand sample ∂mu) =
        (∫ sample, leftIntegrand sample ∂mu) -
          ∫ sample, rightIntegrand sample ∂mu :=
    integral_sub hleft hright
  rw [gaussianShiftHazardIntegral, Real.dist_eq]
  change |(∫ sample, leftIntegrand sample ∂mu) -
      ∫ sample, rightIntegrand sample ∂mu| ≤
    (‖coefficient‖₊ : ℝ) * |left - right|
  rw [← hsub]
  simpa [Real.norm_eq_abs] using hbound

/-- The preceding literal hazard expectation is continuous in its parameter. -/
theorem gaussianShiftHazardIntegral_continuous
    {Alpha : Type*} [MeasurableSpace Alpha]
    (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (coefficient : ℝ) (shift : Alpha -> ℝ)
    (hintegrable : ∀ parameter,
      Integrable (fun sample => standardGaussianHazard
        (coefficient * parameter + shift sample)) mu) :
    Continuous (gaussianShiftHazardIntegral mu coefficient shift) :=
  (gaussianShiftHazardIntegral_lipschitzWith
    mu coefficient shift hintegrable).continuous

/--
For a positive affine coefficient, a Gaussian-hazard shift expectation
vanishes as its scalar parameter tends to `-∞`.

The proof is deliberately measure-generic.  Pointwise, the hazard argument
tends to `-∞`; on the eventual half-line `parameter ≤ 0`, monotonicity bounds
it by the integrable unshifted hazard.  This supplies the endpoint control
needed by literal selected-Gaussian cutoff constructions without inserting an
asymptotic assumption into a paper theorem.
-/
theorem gaussianShiftHazardIntegral_tendsto_atBot_zero
    {Alpha : Type*} [MeasurableSpace Alpha]
    (mu : Measure Alpha) (coefficient : ℝ) (shift : Alpha -> ℝ)
    (hcoefficient : 0 < coefficient)
    (hshiftMeasurable : AEStronglyMeasurable shift mu)
    (hshiftHazardIntegrable : Integrable
      (fun sample => standardGaussianHazard (shift sample)) mu) :
    Tendsto (gaussianShiftHazardIntegral mu coefficient shift)
      atBot (𝓝 0) := by
  let F : ℝ -> Alpha -> ℝ := fun parameter sample =>
    standardGaussianHazard (coefficient * parameter + shift sample)
  have hFmeas : ∀ᶠ parameter in atBot, AEStronglyMeasurable (F parameter) mu := by
    filter_upwards with parameter
    exact
      (standardGaussianHazard_continuous.comp_aestronglyMeasurable
        (hshiftMeasurable.const_add (coefficient * parameter)))
  have hbound : ∀ᶠ parameter in atBot,
      ∀ᵐ sample ∂mu, ‖F parameter sample‖ ≤
        standardGaussianHazard (shift sample) := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with parameter hparameter
    filter_upwards with sample
    have hargument : coefficient * parameter + shift sample ≤ shift sample := by
      have hnonpos : coefficient * parameter ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoefficient.le hparameter
      linarith
    have hmono := standardGaussianHazard_mono hargument
    rw [Real.norm_eq_abs, abs_of_nonneg (standardGaussianHazard_pos _).le]
    exact hmono
  have hlim : ∀ᵐ sample ∂mu,
      Tendsto (fun parameter : ℝ => F parameter sample) atBot (𝓝 0) := by
    filter_upwards with sample
    have hargument : Tendsto
        (fun parameter : ℝ => coefficient * parameter + shift sample)
        atBot atBot := by
      exact
        ((Filter.tendsto_const_mul_atBot_of_pos hcoefficient).2 tendsto_id).atBot_add
          tendsto_const_nhds
    exact standardGaussianHazard_tendsto_atBot_zero.comp hargument
  have hintegral := tendsto_integral_filter_of_dominated_convergence
    (μ := mu) (F := F) (f := fun _sample : Alpha => (0 : ℝ))
    (fun sample => standardGaussianHazard (shift sample))
    hFmeas hbound hshiftHazardIntegrable hlim
  simpa [gaussianShiftHazardIntegral, F] using hintegral

end

end Probability
end AppliedModelingLib
