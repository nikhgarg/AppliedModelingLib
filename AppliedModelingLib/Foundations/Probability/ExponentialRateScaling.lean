import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic

/-!
# Positive scaling of exponential measures

This module records the rate convention for a deterministic positive scaling
of an exponential random variable.  It is stated directly as an equality of
pushforward measures, so queueing constructions can use it without silently
switching between rate and mean parameterizations.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Dividing a rate-`rate` exponential variable by a positive constant
`scale` gives a rate-`rate * scale` exponential variable. -/
theorem map_div_expMeasure_eq_expMeasure
    {rate scale : ℝ} (hrate : 0 < rate) (hscale : 0 < scale) :
    Measure.map (fun x : ℝ => x / scale) (expMeasure rate) =
      expMeasure (rate * scale) := by
  have hdiv : Measurable (fun x : ℝ => x / scale) :=
    measurable_id.div measurable_const
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (Measure.map (fun x : ℝ => x / scale)
      (expMeasure rate)) :=
    Measure.isProbabilityMeasure_map
      hdiv.aemeasurable
  letI : IsProbabilityMeasure (expMeasure (rate * scale)) :=
    isProbabilityMeasure_expMeasure (mul_pos hrate hscale)
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real,
    map_measureReal_apply hdiv measurableSet_Iic]
  have hpreimage : (fun y : ℝ => y / scale) ⁻¹' Iic x = Iic (scale * x) := by
    ext y
    change y / scale ≤ x ↔ y ≤ scale * x
    simpa [mul_comm] using (div_le_iff₀ hscale)
  rw [hpreimage, ← cdf_eq_real (expMeasure rate) (scale * x),
    cdf_expMeasure_eq hrate (scale * x),
    ← cdf_eq_real (expMeasure (rate * scale)) x,
    cdf_expMeasure_eq (mul_pos hrate hscale) x]
  by_cases hx : 0 ≤ x
  · have hscaled : 0 ≤ scale * x := mul_nonneg hscale.le hx
    rw [if_pos hscaled, if_pos hx]
    congr 2
    ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hscaledneg : scale * x < 0 := mul_neg_of_pos_of_neg hscale hxneg
    rw [if_neg (not_le_of_gt hscaledneg), if_neg hx]

/-- In particular, a unit-rate exponential work requirement divided by the
positive service rate has the usual rate-`serviceRate` service-time law. -/
theorem map_div_unitExpMeasure_eq_expMeasure
    {serviceRate : ℝ} (hservice : 0 < serviceRate) :
    Measure.map (fun x : ℝ => x / serviceRate) (expMeasure (1 : ℝ)) =
      expMeasure serviceRate := by
  simpa using
    (map_div_expMeasure_eq_expMeasure (rate := (1 : ℝ)) (scale := serviceRate)
      (by norm_num) hservice)

end

end AppliedModelingLib.Probability
