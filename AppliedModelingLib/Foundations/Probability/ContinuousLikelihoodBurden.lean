import AppliedModelingLib.Foundations.Probability.StieltjesAbsolutelyContinuous
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Probability.CDF

/-!
# CDF representation of continuous likelihood burden

This module proves the finite-threshold Stieltjes integration-by-parts identity
used in the continuous version of MMDH18 Theorem 4.1.  Its explicit
regularity assumptions make precise the analytic conditions implicit in the
paper's displayed calculation: an everywhere `C¹` likelihood cost with a
continuous, nonpositive derivative, zero cost at the threshold, and a law
whose positive-likelihood CDF vanishes at zero.
-/

namespace AppliedModelingLib

open MeasureTheory Set Filter Function
open scoped Topology

/--
For a continuous likelihood cost, the source's Stieltjes burden integral is
the negative CDF-weighted integral of its likelihood derivative.  This is the
fully proved analytic identity preceding the sign argument in MMDH18 Theorem
4.1; the explicit `C¹` assumptions are the currently formalized regularity
conditions needed for the printed integration-by-parts step.
-/
theorem continuousLikelihoodBurden_eq_cdfDerivative
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (cost costDerivative : ℝ → ℝ → ℝ) (threshold : ℝ)
    (hthreshold : 0 < threshold)
    (hcdfZero : ProbabilityTheory.cdf law 0 = 0)
    (hcostThreshold : cost threshold threshold = 0)
    (hderiv : ∀ likelihood,
      HasDerivAt (fun l => cost l threshold) (costDerivative likelihood threshold) likelihood)
    (hderivNonpos : ∀ likelihood, costDerivative likelihood threshold ≤ 0)
    (hderivContinuous : Continuous (fun likelihood => costDerivative likelihood threshold)) :
    ∫ likelihood in Ioc (0 : ℝ) threshold, cost likelihood threshold ∂law =
      -∫ likelihood in (0 : ℝ)..threshold,
        costDerivative likelihood threshold * ProbabilityTheory.cdf law likelihood := by
  let F : ℝ → ℝ := ProbabilityTheory.cdf law
  let u : ℝ → ℝ := fun likelihood => -cost likelihood threshold
  let u' : ℝ → ℝ := fun likelihood => -costDerivative likelihood threshold
  have hF_mono : Monotone F := ProbabilityTheory.monotone_cdf law
  have hF_rightContinuous : ∀ likelihood, ContinuousWithinAt F (Ici likelihood) likelihood :=
    fun likelihood => (ProbabilityTheory.cdf law).right_continuous likelihood
  have hu_deriv : ∀ likelihood, HasDerivAt u (u' likelihood) likelihood := by
    intro likelihood
    exact (hderiv likelihood).neg
  have hu_nonneg : ∀ likelihood, 0 ≤ u' likelihood := by
    intro likelihood
    exact neg_nonneg.mpr (hderivNonpos likelihood)
  have hu_continuous : Continuous u' := hderivContinuous.neg
  have hu_mono : Monotone u := monotone_of_hasDerivAt_nonneg hu_deriv hu_nonneg
  have hF_stieltjes : ∀ likelihood, (hF_mono.stieltjes) likelihood = F likelihood := by
    intro likelihood
    change hF_mono.stieltjesFunction likelihood = F likelihood
    rw [Monotone.stieltjesFunction_eq]
    exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
      ((hF_rightContinuous likelihood).mono_left
        (nhdsWithin_mono likelihood Ioi_subset_Ici_self))
  have hu_stieltjes : ∀ likelihood, (hu_mono.stieltjes) likelihood = u likelihood := by
    intro likelihood
    change hu_mono.stieltjesFunction likelihood = u likelihood
    rw [Monotone.stieltjesFunction_eq]
    exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
      ((hu_deriv likelihood).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hu_continuous' : Continuous u :=
    continuous_iff_continuousAt.mpr (fun likelihood => (hu_deriv likelihood).continuousAt)
  have hu_leftLim : ∀ likelihood, leftLim (⇑(hu_mono.stieltjes)) likelihood = u likelihood := by
    intro likelihood
    rw [leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne]
    rw [show ⇑(hu_mono.stieltjes) = u from funext hu_stieltjes]
    exact (hu_continuous'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hF_measure : hF_mono.stieltjesMeasure = law := by
    change hF_mono.stieltjesFunction.measure = law
    rw [show hF_mono.stieltjesFunction = ProbabilityTheory.cdf law from
      StieltjesFunction.ext hF_stieltjes]
    exact ProbabilityTheory.measure_cdf law
  have h_first :
      ∫ likelihood in Ioc (0 : ℝ) threshold, F likelihood ∂hu_mono.stieltjesMeasure =
        ∫ likelihood in Ioc (0 : ℝ) threshold, F likelihood * u' likelihood := by
    exact Monotone.stieltjes_setIntegral_eq_lebesgue hu_mono hu_deriv hu_nonneg
      hu_continuous F (s := Ioc (0 : ℝ) threshold) measurableSet_Ioc
  have h_second :
      ∫ likelihood in Ioc (0 : ℝ) threshold,
        leftLim (⇑(hu_mono.stieltjes)) likelihood ∂hF_mono.stieltjesMeasure =
      -∫ likelihood in Ioc (0 : ℝ) threshold, cost likelihood threshold ∂law := by
    rw [hF_measure]
    simp_rw [hu_leftLim]
    rw [← MeasureTheory.integral_neg]
  have h_boundary :
      (hF_mono.stieltjes) threshold * (hu_mono.stieltjes) threshold -
        (hF_mono.stieltjes) 0 * (hu_mono.stieltjes) 0 = 0 := by
    simp_rw [hF_stieltjes, hu_stieltjes]
    dsimp [F, u]
    rw [hcdfZero, hcostThreshold]
    ring
  have h_ibp := MeasureTheory.stieltjes_ibp_local hF_mono hu_mono (0 : ℝ) threshold hthreshold
  dsimp only at h_ibp
  rw [h_boundary] at h_ibp
  rw [h_second] at h_ibp
  simp_rw [hF_stieltjes] at h_ibp
  rw [h_first] at h_ibp
  rw [← intervalIntegral.integral_of_le (μ := volume) hthreshold.le] at h_ibp
  have h_normalize :
      ∫ likelihood in (0 : ℝ)..threshold, F likelihood * u' likelihood =
        -∫ likelihood in (0 : ℝ)..threshold,
          costDerivative likelihood threshold * ProbabilityTheory.cdf law likelihood := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro likelihood _
    dsimp [F, u']
    ring
  rw [h_normalize] at h_ibp
  linarith

end AppliedModelingLib
