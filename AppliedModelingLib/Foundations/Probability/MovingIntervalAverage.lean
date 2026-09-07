import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Moving-Interval Integrals and Averages

This module proves continuity of an integral, interval mass, and conditional
average when both endpoints of a closed real interval move continuously.  The
measure is finite and atomless, the integrand is integrable, and the interval
has positive mass wherever an average is taken.

The results are useful for threshold and pooling models: atomlessness prevents
an endpoint from acquiring or losing positive probability mass discontinuously,
while the positive-mass premise exposes the ordinary conditional-mean domain.

## Library provenance

The proof composes Mathlib's `Integrable.continuous_primitive` from
[`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean),
`intervalIntegral.integral_interval_sub_left` from
[`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean),
and `setAverage_eq`, `average_union_mem_segment`,
`exists_le_setAverage`, and `exists_setAverage_le` from
[`Mathlib/MeasureTheory/Integral/Average.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Average.lean).
These files belong to the Apache-2.0-licensed
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
repository at pinned commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external proof or code is copied or ported.
-/

namespace AppliedModelingLib
namespace Probability

open Set MeasureTheory
open scoped Interval

noncomputable section

/--
Under a finite law with full topological support, every nondegenerate closed
real interval has positive real mass.  This is a direct interface from the
standard open-support condition to conditional averages on closed pools.

Mathlib's `Measure.IsOpenPosMeasure` and `measure_Ioo_pos` are from
[`Mathlib/MeasureTheory/Measure/OpenPos.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/OpenPos.lean)
at the pinned Apache-2.0 revision; no external proof or code is copied or
ported.
-/
theorem measureReal_Icc_pos_of_isOpenPosMeasure
    (μ : Measure ℝ) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasure μ]
  {lower upper : ℝ} (hordered : lower < upper) :
    0 < μ.real (Icc lower upper) := by
  have hopen : 0 < μ (Ioo lower upper) :=
    (Measure.measure_Ioo_pos μ).mpr hordered
  have hclosed : 0 < μ (Icc lower upper) :=
    hopen.trans_le (measure_mono Ioo_subset_Icc_self)
  exact ENNReal.toReal_pos (ne_of_gt hclosed) (measure_ne_top _ _)

/--
An integrable function has a continuous integral over a closed interval whose
ordered endpoints vary continuously on the parameter set.
-/
theorem continuousOn_setIntegral_Icc_moving
    {Parameter Value : Type*} [TopologicalSpace Parameter]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure ℝ) [NoAtoms μ]
    (integrand : ℝ → Value) (hintegrable : Integrable integrand μ)
    {domain : Set Parameter} (lower upper : Parameter → ℝ)
    (hlower : ContinuousOn lower domain) (hupper : ContinuousOn upper domain)
    (hordered : ∀ parameter ∈ domain, lower parameter ≤ upper parameter) :
    ContinuousOn
      (fun parameter => ∫ x in Icc (lower parameter) (upper parameter), integrand x ∂μ)
      domain := by
  let primitive : ℝ → Value := fun endpoint => ∫ x in (0 : ℝ)..endpoint, integrand x ∂μ
  have hprimitive : Continuous primitive := by
    exact hintegrable.continuous_primitive 0
  have hcontinuous : ContinuousOn
      (fun parameter => primitive (upper parameter) - primitive (lower parameter)) domain :=
    (hprimitive.comp_continuousOn hupper).sub
      (hprimitive.comp_continuousOn hlower)
  refine hcontinuous.congr ?_
  intro parameter hparameter
  change (∫ x in Icc (lower parameter) (upper parameter), integrand x ∂μ) =
    (∫ x in (0 : ℝ)..upper parameter, integrand x ∂μ) -
      ∫ x in (0 : ℝ)..lower parameter, integrand x ∂μ
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (hordered parameter hparameter)]
  exact (intervalIntegral.integral_interval_sub_left
    hintegrable.intervalIntegrable hintegrable.intervalIntegrable).symm

/--
Under a finite atomless measure, the real mass of a closed interval is
continuous when its ordered endpoints vary continuously.
-/
theorem continuousOn_measureReal_Icc_moving
    {Parameter : Type*} [TopologicalSpace Parameter]
    (μ : Measure ℝ) [NoAtoms μ] [IsFiniteMeasure μ]
    {domain : Set Parameter} (lower upper : Parameter → ℝ)
    (hlower : ContinuousOn lower domain) (hupper : ContinuousOn upper domain)
    (hordered : ∀ parameter ∈ domain, lower parameter ≤ upper parameter) :
    ContinuousOn (fun parameter => μ.real (Icc (lower parameter) (upper parameter))) domain := by
  simpa only [setIntegral_one_eq_measureReal] using
    (continuousOn_setIntegral_Icc_moving μ (fun _ => (1 : ℝ))
      (integrable_const (1 : ℝ)) lower upper hlower hupper hordered)

/--
An integrable function has a continuous conditional average over a moving
closed interval wherever that interval has positive mass.
-/
theorem continuousOn_setAverage_Icc_moving
    {Parameter Value : Type*} [TopologicalSpace Parameter]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (μ : Measure ℝ) [NoAtoms μ] [IsFiniteMeasure μ]
    (integrand : ℝ → Value) (hintegrable : Integrable integrand μ)
    {domain : Set Parameter} (lower upper : Parameter → ℝ)
    (hlower : ContinuousOn lower domain) (hupper : ContinuousOn upper domain)
    (hordered : ∀ parameter ∈ domain, lower parameter ≤ upper parameter)
    (hmass : ∀ parameter ∈ domain,
      0 < μ.real (Icc (lower parameter) (upper parameter))) :
    ContinuousOn
      (fun parameter => ⨍ x in Icc (lower parameter) (upper parameter), integrand x ∂μ)
      domain := by
  have hmassContinuous :=
    continuousOn_measureReal_Icc_moving μ lower upper hlower hupper hordered
  have hinverse : ContinuousOn
      (fun parameter => (μ.real (Icc (lower parameter) (upper parameter)))⁻¹) domain :=
    hmassContinuous.inv₀ fun parameter hparameter => ne_of_gt (hmass parameter hparameter)
  have hintegral :=
    continuousOn_setIntegral_Icc_moving μ integrand hintegrable
      lower upper hlower hupper hordered
  simpa only [setAverage_eq] using hinverse.smul hintegral

/--
A constant-threshold superlevel set of a moving conditional average is closed
when the parameter domain is closed.
-/
theorem isClosed_setOf_mem_and_le_setAverage_Icc_moving
    {Parameter : Type*} [TopologicalSpace Parameter]
    (μ : Measure ℝ) [NoAtoms μ] [IsFiniteMeasure μ]
    (integrand : ℝ → ℝ) (hintegrable : Integrable integrand μ)
    {domain : Set Parameter} (hdomain : IsClosed domain)
    (lower upper : Parameter → ℝ)
    (hlower : ContinuousOn lower domain) (hupper : ContinuousOn upper domain)
    (hordered : ∀ parameter ∈ domain, lower parameter ≤ upper parameter)
    (hmass : ∀ parameter ∈ domain,
      0 < μ.real (Icc (lower parameter) (upper parameter)))
    (target : ℝ) :
    IsClosed {parameter | parameter ∈ domain ∧
      target ≤ ⨍ x in Icc (lower parameter) (upper parameter), integrand x ∂μ} := by
  exact hdomain.isClosed_le continuousOn_const
    (continuousOn_setAverage_Icc_moving μ integrand hintegrable
      lower upper hlower hupper hordered hmass)

/--
For a positive-mass interval, the conditional mean of the identity is at most
the interval's right endpoint.
-/
theorem setAverage_id_Icc_le_right
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hintegrable : Integrable id μ) {lower upper : ℝ}
    (hmass : 0 < μ.real (Icc lower upper)) :
    (⨍ likelihood in Icc lower upper, likelihood ∂μ) ≤ upper := by
  have hmeasure : μ (Icc lower upper) ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp (ne_of_gt hmass)).1
  obtain ⟨likelihood, hlikelihood, hmean⟩ :=
    exists_setAverage_le hmeasure (measure_ne_top _ _) hintegrable.integrableOn
  exact hmean.trans hlikelihood.2

/--
For a positive-mass interval, the conditional mean of the identity is at
least the interval's left endpoint.
-/
theorem left_le_setAverage_id_Icc
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hintegrable : Integrable id μ) {lower upper : ℝ}
    (hmass : 0 < μ.real (Icc lower upper)) :
    lower ≤ (⨍ likelihood in Icc lower upper, likelihood ∂μ) := by
  have hmeasure : μ (Icc lower upper) ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp (ne_of_gt hmass)).1
  obtain ⟨likelihood, hlikelihood, hmean⟩ :=
    exists_le_setAverage hmeasure (measure_ne_top _ _) hintegrable.integrableOn
  exact hlikelihood.1.trans hmean

/--
Under an atomless finite likelihood law, conditioning on a positive-mass
closed interval shifts the mean likelihood weakly right when both endpoints
shift weakly right.  The proof partitions the two intervals at their overlap;
atomlessness makes the shared endpoints negligible, and the zero-overlap-mass
cases are handled by almost-everywhere equality rather than by a density
assumption.
-/
theorem setAverage_id_Icc_mono_of_endpoints
    (μ : Measure ℝ) [NoAtoms μ] [IsFiniteMeasure μ]
    (hintegrable : Integrable id μ) {leftLower leftUpper rightLower rightUpper : ℝ}
    (hlower : leftLower ≤ rightLower) (hupper : leftUpper ≤ rightUpper)
    (hleftMass : 0 < μ.real (Icc leftLower leftUpper))
    (hrightMass : 0 < μ.real (Icc rightLower rightUpper)) :
    (⨍ likelihood in Icc leftLower leftUpper, likelihood ∂μ) ≤
      (⨍ likelihood in Icc rightLower rightUpper, likelihood ∂μ) := by
  by_cases hseparated : leftUpper ≤ rightLower
  · exact (setAverage_id_Icc_le_right μ hintegrable hleftMass).trans
      (hseparated.trans (left_le_setAverage_id_Icc μ hintegrable hrightMass))
  have hoverlap : rightLower ≤ leftUpper := le_of_not_ge hseparated
  have hleftUnion : Icc leftLower leftUpper = Icc leftLower rightLower ∪
      Icc rightLower leftUpper :=
    (Icc_union_Icc_eq_Icc hlower hoverlap).symm
  have hrightUnion : Icc rightLower rightUpper = Icc rightLower leftUpper ∪
      Icc leftUpper rightUpper :=
    (Icc_union_Icc_eq_Icc hoverlap hupper).symm
  have hdisjointLeftMiddle : AEDisjoint μ (Icc leftLower rightLower)
      (Icc rightLower leftUpper) := by
    rw [AEDisjoint, Icc_inter_Icc_eq_singleton hlower hoverlap]
    simp
  have hdisjointMiddleRight : AEDisjoint μ (Icc rightLower leftUpper)
      (Icc leftUpper rightUpper) := by
    rw [AEDisjoint, Icc_inter_Icc_eq_singleton hoverlap hupper]
    simp
  by_cases hmiddleZero : μ (Icc rightLower leftUpper) = 0
  · have hleftEq :
        (⨍ likelihood in Icc leftLower leftUpper, likelihood ∂μ) =
          (⨍ likelihood in Icc leftLower rightLower, likelihood ∂μ) := by
      rw [hleftUnion]
      simpa [union_comm] using
        (setAverage_congr
          (union_ae_eq_right.mpr
            (measure_mono_null diff_subset hmiddleZero) :
            (Icc rightLower leftUpper ∪ Icc leftLower rightLower : Set ℝ) =ᵐ[μ]
              Icc leftLower rightLower))
    have hrightEq :
        (⨍ likelihood in Icc rightLower rightUpper, likelihood ∂μ) =
          (⨍ likelihood in Icc leftUpper rightUpper, likelihood ∂μ) := by
      rw [hrightUnion]
      apply setAverage_congr
      apply union_ae_eq_right.mpr
      exact measure_mono_null diff_subset hmiddleZero
    have hleftPieceMass : 0 < μ.real (Icc leftLower rightLower) := by
      by_contra hnot
      have hnot : μ.real (Icc leftLower rightLower) ≤ 0 := le_of_not_gt hnot
      have hrealZero : μ.real (Icc leftLower rightLower) = 0 :=
        le_antisymm hnot measureReal_nonneg
      have hzero : μ (Icc leftLower rightLower) = 0 :=
        ((ENNReal.toReal_eq_zero_iff _).mp hrealZero).resolve_right (measure_ne_top _ _)
      have hleftZero : μ (Icc leftLower leftUpper) = 0 := by
        rw [hleftUnion]
        exact measure_union_null hzero hmiddleZero
      have hzeroReal : μ.real (Icc leftLower leftUpper) = 0 := by
        change (μ (Icc leftLower leftUpper)).toReal = 0
        rw [hleftZero]
        rfl
      exact (ne_of_gt hleftMass) hzeroReal
    have hrightPieceMass : 0 < μ.real (Icc leftUpper rightUpper) := by
      by_contra hnot
      have hnot : μ.real (Icc leftUpper rightUpper) ≤ 0 := le_of_not_gt hnot
      have hrealZero : μ.real (Icc leftUpper rightUpper) = 0 :=
        le_antisymm hnot measureReal_nonneg
      have hzero : μ (Icc leftUpper rightUpper) = 0 :=
        ((ENNReal.toReal_eq_zero_iff _).mp hrealZero).resolve_right (measure_ne_top _ _)
      have hrightZero : μ (Icc rightLower rightUpper) = 0 := by
        rw [hrightUnion]
        exact measure_union_null hmiddleZero hzero
      have hzeroReal : μ.real (Icc rightLower rightUpper) = 0 := by
        change (μ (Icc rightLower rightUpper)).toReal = 0
        rw [hrightZero]
        rfl
      exact (ne_of_gt hrightMass) hzeroReal
    rw [hleftEq, hrightEq]
    exact (setAverage_id_Icc_le_right μ hintegrable hleftPieceMass).trans
      (hoverlap.trans (left_le_setAverage_id_Icc μ hintegrable hrightPieceMass))
  have hmiddleMass : 0 < μ.real (Icc rightLower leftUpper) :=
    ENNReal.toReal_pos hmiddleZero (measure_ne_top _ _)
  have hleft_le_middle :
      (⨍ likelihood in Icc leftLower leftUpper, likelihood ∂μ) ≤
        (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) := by
    by_cases hleftPieceZero : μ (Icc leftLower rightLower) = 0
    · rw [hleftUnion]
      have hEq :
          (⨍ likelihood in (Icc leftLower rightLower ∪ Icc rightLower leftUpper),
            likelihood ∂μ) =
            (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) :=
        setAverage_congr (union_ae_eq_right.mpr
          (measure_mono_null diff_subset hleftPieceZero))
      exact hEq.le
    have hleftPieceMass : 0 < μ.real (Icc leftLower rightLower) :=
      ENNReal.toReal_pos hleftPieceZero (measure_ne_top _ _)
    have hpiecesOrdered :
        (⨍ likelihood in Icc leftLower rightLower, likelihood ∂μ) ≤
          (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) :=
      (setAverage_id_Icc_le_right μ hintegrable hleftPieceMass).trans
        (left_le_setAverage_id_Icc μ hintegrable hmiddleMass)
    have hsegment :
        (⨍ likelihood in Icc leftLower leftUpper, likelihood ∂μ) ∈
          segment ℝ
            (⨍ likelihood in Icc leftLower rightLower, likelihood ∂μ)
            (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) := by
      rw [hleftUnion]
      exact average_union_mem_segment hdisjointLeftMiddle measurableSet_Icc.nullMeasurableSet
        (measure_ne_top _ _) (measure_ne_top _ _) hintegrable.integrableOn hintegrable.integrableOn
    rw [segment_eq_Icc hpiecesOrdered] at hsegment
    exact hsegment.2
  have hmiddle_le_right :
      (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) ≤
        (⨍ likelihood in Icc rightLower rightUpper, likelihood ∂μ) := by
    by_cases hrightPieceZero : μ (Icc leftUpper rightUpper) = 0
    · rw [hrightUnion]
      have hEq :
          (⨍ likelihood in (Icc rightLower leftUpper ∪ Icc leftUpper rightUpper),
            likelihood ∂μ) =
            (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) := by
        simpa [union_comm] using
          (setAverage_congr
            (union_ae_eq_right.mpr
              (measure_mono_null diff_subset hrightPieceZero) :
              (Icc leftUpper rightUpper ∪ Icc rightLower leftUpper : Set ℝ) =ᵐ[μ]
                Icc rightLower leftUpper))
      exact hEq.ge
    have hrightPieceMass : 0 < μ.real (Icc leftUpper rightUpper) :=
      ENNReal.toReal_pos hrightPieceZero (measure_ne_top _ _)
    have hpiecesOrdered :
        (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ) ≤
          (⨍ likelihood in Icc leftUpper rightUpper, likelihood ∂μ) :=
      (setAverage_id_Icc_le_right μ hintegrable hmiddleMass).trans
        (left_le_setAverage_id_Icc μ hintegrable hrightPieceMass)
    have hsegment :
        (⨍ likelihood in Icc rightLower rightUpper, likelihood ∂μ) ∈
          segment ℝ
            (⨍ likelihood in Icc rightLower leftUpper, likelihood ∂μ)
            (⨍ likelihood in Icc leftUpper rightUpper, likelihood ∂μ) := by
      rw [hrightUnion]
      exact average_union_mem_segment hdisjointMiddleRight measurableSet_Icc.nullMeasurableSet
        (measure_ne_top _ _) (measure_ne_top _ _) hintegrable.integrableOn hintegrable.integrableOn
    rw [segment_eq_Icc hpiecesOrdered] at hsegment
    exact hsegment.1
  exact hleft_le_middle.trans hmiddle_le_right

end

end Probability
end AppliedModelingLib
