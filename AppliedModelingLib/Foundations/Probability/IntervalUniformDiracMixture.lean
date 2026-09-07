import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Conditional Means for a Uniform--Dirac Mixture

This module packages an elementary probability law that is useful for testing
whether conditional-mean and threshold-equilibrium claims inadvertently assume
atomlessness.  The law gives equal weight to Lebesgue measure on `[0,1]` and
to a Dirac mass at a caller-selected point.  We compute its mass, first
moment, and conditional mean on closed subintervals, separately according to
whether the atom lies in the conditioning interval.

## Library provenance

The implementation directly uses Mathlib's `setAverage_eq`,
`integral_smul_measure`, and `integral_add_measure` from
[`Mathlib/MeasureTheory/Integral/Average.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Average.lean)
and its imported Bochner-integral API; `integral_id` from
[`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean);
`Real.volume_Icc` and Lebesgue restriction from
[`Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean);
and `restrict_dirac` and `setIntegral_dirac` from
[`Mathlib/MeasureTheory/Measure/Dirac.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Dirac.lean).
These files are part of the Apache-2.0-licensed
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
repository at pinned commit
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external code or proof is copied or ported.
-/

namespace AppliedModelingLib
namespace Probability

open Set MeasureTheory
open scoped Interval ENNReal

noncomputable section

/-- Lebesgue measure on `[0,1]` plus one unit Dirac mass at `atom`. -/
def unitIntervalLebesguePlusDirac (atom : ℝ) : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1) + Measure.dirac atom

/--
The equal mixture of the uniform probability law on `[0,1]` and a Dirac law.
The atom may lie anywhere on the real line; both components still have mass
one.
-/
def equalUnitIntervalUniformDiracMixture (atom : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • unitIntervalLebesguePlusDirac atom

instance (atom : ℝ) : IsProbabilityMeasure
    (equalUnitIntervalUniformDiracMixture atom) where
  measure_univ := by
    rw [equalUnitIntervalUniformDiracMixture, Measure.smul_apply,
      unitIntervalLebesguePlusDirac, Measure.add_apply]
    simp [Measure.restrict_apply, Real.volume_Icc]
    simpa only [one_add_one_eq_two] using
      (ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num))

/-- The first moment of Lebesgue measure on a closed real interval. -/
theorem integral_id_Icc (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b, x) = (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  exact integral_id

/-- Restricting unit-interval Lebesgue measure to a contained closed interval. -/
theorem unitIntervalLebesgue_measure_Icc (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    (volume.restrict (Icc (0 : ℝ) 1)) (Icc a b) =
      ENNReal.ofReal (b - a) := by
  rw [Measure.restrict_apply measurableSet_Icc]
  have hsubset : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  rw [inter_eq_left.mpr hsubset]
  exact Real.volume_Icc

/--
Every nonempty open subinterval of `[0,1]` has positive probability under the
equal uniform--Dirac mixture, independently of the atom's location.  Thus the
uniform component supplies full topological support on the unit interval even
when the law also has atoms.
-/
theorem equalUnitIntervalUniformDiracMixture_measure_Ioo_pos
    (atom a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < equalUnitIntervalUniformDiracMixture atom (Ioo a b) := by
  rw [equalUnitIntervalUniformDiracMixture, Measure.smul_apply,
    unitIntervalLebesguePlusDirac, Measure.add_apply]
  rw [Measure.restrict_apply measurableSet_Ioo]
  have hsubset : Ioo a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩
  rw [inter_eq_left.mpr hsubset, Real.volume_Ioo]
  simp only [smul_eq_mul]
  rw [ENNReal.mul_pos_iff]
  constructor
  · exact ENNReal.inv_pos.mpr (by norm_num)
  · exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
      (le_add_right (le_refl _))

/-- Interval mass when the Dirac atom belongs to the interval. -/
theorem unitIntervalLebesguePlusDirac_measure_Icc_of_mem (atom a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hatom : atom ∈ Icc a b) :
    unitIntervalLebesguePlusDirac atom (Icc a b) =
      ENNReal.ofReal (b - a) + 1 := by
  rw [unitIntervalLebesguePlusDirac, Measure.add_apply,
    unitIntervalLebesgue_measure_Icc a b ha hb]
  rw [(dirac_eq_one_iff_mem measurableSet_Icc).mpr hatom]

/-- Interval mass when the Dirac atom does not belong to the interval. -/
theorem unitIntervalLebesguePlusDirac_measure_Icc_of_not_mem (atom a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hatom : atom ∉ Icc a b) :
    unitIntervalLebesguePlusDirac atom (Icc a b) =
      ENNReal.ofReal (b - a) := by
  rw [unitIntervalLebesguePlusDirac, Measure.add_apply,
    unitIntervalLebesgue_measure_Icc a b ha hb]
  rw [(dirac_eq_zero_iff_not_mem measurableSet_Icc).mpr hatom, add_zero]

/-- First moment on a contained interval that includes the Dirac atom. -/
theorem unitIntervalLebesguePlusDirac_integral_id_Icc_of_mem
    (atom a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hatom : atom ∈ Icc a b) :
    (∫ x in Icc a b, x ∂unitIntervalLebesguePlusDirac atom) =
      (b ^ 2 - a ^ 2) / 2 + atom := by
  rw [unitIntervalLebesguePlusDirac, Measure.restrict_add]
  rw [integral_add_measure]
  · rw [Measure.restrict_restrict_of_subset]
    · rw [integral_id_Icc a b hab]
      rw [setIntegral_dirac, if_pos hatom]
    · intro x hx
      exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  · exact continuous_id.integrableOn_Icc
  · rw [restrict_dirac, if_pos hatom]
    exact integrable_dirac (by simp)

/-- First moment on a contained interval that excludes the Dirac atom. -/
theorem unitIntervalLebesguePlusDirac_integral_id_Icc_of_not_mem
    (atom a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hatom : atom ∉ Icc a b) :
    (∫ x in Icc a b, x ∂unitIntervalLebesguePlusDirac atom) =
      (b ^ 2 - a ^ 2) / 2 := by
  rw [unitIntervalLebesguePlusDirac, Measure.restrict_add]
  rw [integral_add_measure]
  · rw [Measure.restrict_restrict_of_subset]
    · rw [integral_id_Icc a b hab]
      rw [setIntegral_dirac, if_neg hatom, add_zero]
    · intro x hx
      exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  · exact continuous_id.integrableOn_Icc
  · rw [restrict_dirac, if_neg hatom]
    exact integrable_zero_measure

/--
Conditional mean on a contained closed interval that includes the atom.  The
factor one half in the probability law cancels from numerator and denominator.
-/
theorem equalUnitIntervalUniformDiracMixture_setAverage_id_Icc_of_mem
    (atom a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hatom : atom ∈ Icc a b) :
    (⨍ x in Icc a b, x ∂equalUnitIntervalUniformDiracMixture atom) =
      ((b ^ 2 - a ^ 2) / 2 + atom) / ((b - a) + 1) := by
  rw [setAverage_eq]
  rw [equalUnitIntervalUniformDiracMixture, Measure.restrict_smul,
    integral_smul_measure]
  rw [unitIntervalLebesguePlusDirac_integral_id_Icc_of_mem
    atom a b hab ha hb hatom]
  simp only [Measure.real, Measure.smul_apply,
    unitIntervalLebesguePlusDirac_measure_Icc_of_mem atom a b ha hb hatom]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_add (by finiteness) (by simp)]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ENNReal.toReal_one]
  norm_num [smul_eq_mul]
  field_simp

/--
Conditional mean on a nondegenerate contained closed interval that excludes
the atom.  It is the ordinary uniform midpoint.
-/
theorem equalUnitIntervalUniformDiracMixture_setAverage_id_Icc_of_not_mem
    (atom a b : ℝ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hatom : atom ∉ Icc a b) :
    (⨍ x in Icc a b, x ∂equalUnitIntervalUniformDiracMixture atom) =
      (a + b) / 2 := by
  rw [setAverage_eq]
  rw [equalUnitIntervalUniformDiracMixture, Measure.restrict_smul,
    integral_smul_measure]
  rw [unitIntervalLebesguePlusDirac_integral_id_Icc_of_not_mem
    atom a b hab.le ha hb hatom]
  simp only [Measure.real, Measure.smul_apply,
    unitIntervalLebesguePlusDirac_measure_Icc_of_not_mem atom a b ha hb hatom]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  norm_num [smul_eq_mul]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

end

end Probability
end AppliedModelingLib
