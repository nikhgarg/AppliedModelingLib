import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.CDF

/-!
# Continuous CDF stochastic dominance

This module records the continuous first-order stochastic-dominance order on
real probability laws and the interval-integral sign calculation used by
comparative-statics arguments.  It deliberately separates the elementary
calculus conclusion from a later Stieltjes integration-by-parts bridge that
identifies a model-specific burden gap with `cdfDerivativeGap`.

The CDF uses Mathlib's `ProbabilityTheory.cdf`; it is meaningful as a
probability-law CDF when the measures carry `IsProbabilityMeasure` instances.

Upstream credit: this module directly uses Mathlib's CDF API in
[`Mathlib/Probability/CDF.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/CDF.lean)
and interval-integral positivity API in
[`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean),
at the repository's pinned Apache-2.0 Mathlib revision. No external proof or
code is copied or ported.
-/

namespace AppliedModelingLib

open MeasureTheory Set

/-- `dominant` first-order stochastically dominates `dominated` by lower-tail CDF order. -/
def WeakCDFDominates (dominant dominated : Measure ℝ) : Prop :=
  ∀ cutoff, ProbabilityTheory.cdf dominant cutoff ≤ ProbabilityTheory.cdf dominated cutoff

/-- Group `disadvantaged` has strictly more positive-likelihood mass below every interior cutoff. -/
def StrictCDFDisadvantage (advantaged disadvantaged : Measure ℝ) : Prop :=
  ∀ cutoff ∈ Ioo (0 : ℝ) 1,
    ProbabilityTheory.cdf advantaged cutoff < ProbabilityTheory.cdf disadvantaged cutoff

/-- Lower-tail CDF dominance is reflexive. -/
theorem weakCDFDominates_refl (law : Measure ℝ) : WeakCDFDominates law law :=
  fun _ => le_rfl

/-- Lower-tail CDF dominance is transitive. -/
theorem WeakCDFDominates.trans {first second third : Measure ℝ}
    (hfirst : WeakCDFDominates first second) (hsecond : WeakCDFDominates second third) :
    WeakCDFDominates first third :=
  fun cutoff => (hfirst cutoff).trans (hsecond cutoff)

/--
The CDF--derivative expression in the proof of MMDH18 Theorem 4.1.  For a
cost derivative negative in its likelihood coordinate and strict CDF
disadvantage, its positivity is an ordinary interval-integral fact.
-/
noncomputable def cdfDerivativeGap
    (costDerivative : ℝ → ℝ → ℝ) (cdfA cdfB : ℝ → ℝ) (threshold : ℝ) : ℝ :=
  ∫ likelihood in (0 : ℝ)..threshold,
    costDerivative likelihood threshold * (cdfA likelihood - cdfB likelihood)

/--
The sign calculation needs only interval integrability, not continuity of the
CDFs.  This is the appropriate analytic form for laws that may have atoms;
continuity remains a convenient sufficient condition in
`cdfDerivativeGap_pos` below.
-/
theorem cdfDerivativeGap_pos_of_intervalIntegrable
    (costDerivative : ℝ → ℝ → ℝ) (cdfA cdfB : ℝ → ℝ) (threshold : ℝ)
    (hthreshold : 0 < threshold)
    (hdisadvantaged : ∀ likelihood ∈ Ioo (0 : ℝ) threshold,
      cdfA likelihood < cdfB likelihood)
    (hderivativeNegative : ∀ likelihood ∈ Ioo (0 : ℝ) threshold,
      costDerivative likelihood threshold < 0)
    (hintegrable : IntervalIntegrable
      (fun likelihood => costDerivative likelihood threshold *
        (cdfA likelihood - cdfB likelihood)) volume (0 : ℝ) threshold) :
    0 < cdfDerivativeGap costDerivative cdfA cdfB threshold := by
  unfold cdfDerivativeGap
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hintegrable
  · intro likelihood hlikelihood
    exact mul_pos_of_neg_of_neg
      (hderivativeNegative likelihood hlikelihood)
      (sub_neg.mpr (hdisadvantaged likelihood hlikelihood))
  · exact hthreshold

/--
The analytic sign step in MMDH18 Theorem 4.1: strict CDF disadvantage and a
negative initial-likelihood derivative make the CDF--derivative gap positive.

The continuity assumption is an explicit sufficient condition for interval
integrability; the paper's displayed integration-by-parts calculation needs
such regularity to have its usual real-valued meaning.
-/
theorem cdfDerivativeGap_pos
    (costDerivative : ℝ → ℝ → ℝ) (cdfA cdfB : ℝ → ℝ) (threshold : ℝ)
    (hthreshold : 0 < threshold)
    (hdisadvantaged : ∀ likelihood ∈ Ioo (0 : ℝ) threshold,
      cdfA likelihood < cdfB likelihood)
    (hderivativeNegative : ∀ likelihood ∈ Ioo (0 : ℝ) threshold,
      costDerivative likelihood threshold < 0)
    (hcontinuous : ContinuousOn
      (fun likelihood => costDerivative likelihood threshold *
        (cdfA likelihood - cdfB likelihood)) (Icc (0 : ℝ) threshold)) :
    0 < cdfDerivativeGap costDerivative cdfA cdfB threshold := by
  unfold cdfDerivativeGap
  exact cdfDerivativeGap_pos_of_intervalIntegrable
    costDerivative cdfA cdfB threshold hthreshold hdisadvantaged hderivativeNegative
    (hcontinuous.intervalIntegrable_of_Icc hthreshold.le)

/--
The threshold-comparison step in the proof of MMDH18 Theorem 4.1.  If the
likelihood derivative becomes weakly more negative as the threshold rises,
then strict CDF disadvantage makes the CDF--derivative gap strictly increase.

The interval-integrability hypotheses are deliberately local to the two
thresholds.  They expose the analytic condition needed to split the displayed
integral, without imposing an unnecessary continuity or atomlessness condition
on the two CDFs themselves.
-/
theorem cdfDerivativeGap_strictMono_of_derivativeAntitone
    (costDerivative : ℝ → ℝ → ℝ) (cdfA cdfB : ℝ → ℝ)
    {lowerThreshold upperThreshold : ℝ}
    (hlower : 0 < lowerThreshold) (hlowerUpper : lowerThreshold < upperThreshold)
    (hdisadvantaged : ∀ likelihood ∈ Ioo (0 : ℝ) upperThreshold,
      cdfA likelihood < cdfB likelihood)
    (hderivativeNegative : ∀ likelihood threshold,
      likelihood ∈ Ioo (0 : ℝ) threshold → costDerivative likelihood threshold < 0)
    (hderivativeAntitone : ∀ likelihood lower upper,
      lower ≤ upper → costDerivative likelihood upper ≤ costDerivative likelihood lower)
    (hintegrableLower : IntervalIntegrable
      (fun likelihood => costDerivative likelihood lowerThreshold *
        (cdfA likelihood - cdfB likelihood)) volume (0 : ℝ) lowerThreshold)
    (hintegrableUpperPrefix : IntervalIntegrable
      (fun likelihood => costDerivative likelihood upperThreshold *
        (cdfA likelihood - cdfB likelihood)) volume (0 : ℝ) lowerThreshold)
    (hintegrableUpperTail : IntervalIntegrable
      (fun likelihood => costDerivative likelihood upperThreshold *
        (cdfA likelihood - cdfB likelihood)) volume lowerThreshold upperThreshold) :
    cdfDerivativeGap costDerivative cdfA cdfB lowerThreshold <
      cdfDerivativeGap costDerivative cdfA cdfB upperThreshold := by
  unfold cdfDerivativeGap
  have hprefix :
      (∫ likelihood in (0 : ℝ)..lowerThreshold,
        costDerivative likelihood lowerThreshold * (cdfA likelihood - cdfB likelihood) ≤
      ∫ likelihood in (0 : ℝ)..lowerThreshold,
        costDerivative likelihood upperThreshold * (cdfA likelihood - cdfB likelihood)) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hlower.le
      hintegrableLower hintegrableUpperPrefix
    intro likelihood hlikelihood
    have hCDFNonpos : cdfA likelihood - cdfB likelihood ≤ 0 :=
      (sub_neg.mpr (hdisadvantaged likelihood
        ⟨hlikelihood.1, lt_trans hlikelihood.2 hlowerUpper⟩)).le
    exact mul_le_mul_of_nonpos_right
      (hderivativeAntitone likelihood lowerThreshold upperThreshold hlowerUpper.le) hCDFNonpos
  have htail :
      0 < ∫ likelihood in lowerThreshold..upperThreshold,
        costDerivative likelihood upperThreshold * (cdfA likelihood - cdfB likelihood) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hintegrableUpperTail
    · intro likelihood hlikelihood
      exact mul_pos_of_neg_of_neg
        (hderivativeNegative likelihood upperThreshold
          ⟨lt_trans hlower hlikelihood.1, hlikelihood.2⟩)
        (sub_neg.mpr (hdisadvantaged likelihood ⟨lt_trans hlower hlikelihood.1, hlikelihood.2⟩))
    · exact hlowerUpper
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hintegrableUpperPrefix hintegrableUpperTail
  linarith

end AppliedModelingLib
