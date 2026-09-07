/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
Authors: Daniel Lyng

This file narrowly ports the absolute-continuity Stieltjes results from
https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/MeasureTheory/StieltjesAbsCont.lean
(Apache-2.0).  It was adapted to this repository's Lean 4.30.0-rc2 / pinned
Mathlib environment; the upstream project pins Lean 4.29.  The original
copyright and Apache-2.0 notice are retained.  No other Econlib declarations
or dependencies are imported.
-/

import AppliedModelingLib.Foundations.Probability.StieltjesIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Absolutely continuous Stieltjes measures

For a monotone `C¹` real function with continuous nonnegative derivative, its
Stieltjes measure equals Lebesgue measure weighted by that derivative.  This
is the analytic bridge from a continuous likelihood cost to the ordinary
derivative/CDF integral in continuous stochastic-dominance arguments.

The two results are a narrow, credited port of Daniel Lyng's Apache-2.0
Econlib development.  They are compiled and logically checked locally rather
than accepted by source inspection.
-/

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Real

namespace Monotone

/-- The Stieltjes measure of a monotone `C¹` function equals Lebesgue measure
weighted by its nonnegative derivative. -/
theorem stieltjes_measure_eq_withDensity {u u' : ℝ → ℝ} (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u') :
    hu.stieltjesMeasure = volume.withDensity (fun x => ENNReal.ofReal (u' x)) := by
  apply Real.measure_ext_Ioo_rat
  intro a b
  by_cases hab : (a : ℝ) < b
  · have h_sf_eq : ∀ x, (hu.stieltjes) x = u x := by
      intro x
      change hu.stieltjesFunction x = u x
      rw [Monotone.stieltjesFunction_eq]
      exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
        ((h_deriv x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hu_continuous : Continuous u :=
      continuous_iff_continuousAt.mpr (fun x => (h_deriv x).continuousAt)
    have h_leftLim : leftLim (⇑(hu.stieltjes)) (b : ℝ) = u b := by
      rw [leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne
        (by rw [show ⇑(hu.stieltjes) = u from funext h_sf_eq]
            exact hu_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)]
    have h_lhs : (hu.stieltjesMeasure) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (u b - u a) := by
      change (hu.stieltjes).measure (Ioo (a : ℝ) b) = _
      rw [StieltjesFunction.measure_Ioo, h_sf_eq, h_leftLim]
    have h_rhs : (volume.withDensity (fun x => ENNReal.ofReal (u' x))) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (u b - u a) := by
      rw [withDensity_apply _ measurableSet_Ioo]
      have h_ftc : ∫ x in (a : ℝ)..b, u' x = u b - u a :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => h_deriv x) (hu_cont.intervalIntegrable _ _)
      have h_intOn : IntegrableOn u' (Ioo (a : ℝ) b) :=
        (hu_cont.intervalIntegrable (a : ℝ) b |>.1).mono_set Ioo_subset_Ioc_self
      rw [← ofReal_integral_eq_lintegral_ofReal h_intOn (ae_of_all _ hu_nn)]
      congr 1
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab.le]
      exact h_ftc
    rw [h_lhs, h_rhs]
  · push Not at hab
    rw [Ioo_eq_empty (not_lt.mpr (by exact_mod_cast hab)), measure_empty, measure_empty]

/-- Integrating against a monotone `C¹` function's Stieltjes measure is the
ordinary Lebesgue integral weighted by its derivative. -/
theorem stieltjes_integral_eq_lebesgue {u u' : ℝ → ℝ} (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u')
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(hu.stieltjesMeasure) = ∫ y, f y * u' y := by
  rw [stieltjes_measure_eq_withDensity hu h_deriv hu_nn hu_cont]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hu_cont.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  ext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hu_nn x), mul_comm]

/-- The set-integral form of `stieltjes_integral_eq_lebesgue`.  It is the
usable local identity for a finite threshold interval. -/
theorem stieltjes_setIntegral_eq_lebesgue {u u' : ℝ → ℝ} (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u') (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ y in s, f y ∂(hu.stieltjesMeasure) = ∫ y in s, f y * u' y := by
  rw [stieltjes_measure_eq_withDensity hu h_deriv hu_nn hu_cont]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hu_cont.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ hs]
  congr 1
  ext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hu_nn x), mul_comm]

end Monotone
