import GN21DriverSurgePricing.Theorem2ExplicitInstance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous Theorem 2 Instance

The source model for GN21 uses a continuous trip-length distribution.  This
module supplies the explicit Theorem 2 witness with a bounded-density law:
half of the mass is uniform on `[0.99, 1.01]` and half is uniform on
`[5.99, 6.01]`.  The components have means `1` and `6`, respectively, so the
existing reward algebra applies without changing its numerical margins.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-- The short bounded-density component of the continuous Theorem 2 witness. -/
def theorem2BothStatesContinuousShortUniform : Measure TripLength :=
  (50 : ℝ≥0∞) • volume.restrict (Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100))

/-- The long bounded-density component of the continuous Theorem 2 witness. -/
def theorem2BothStatesContinuousLongUniform : Measure TripLength :=
  (50 : ℝ≥0∞) • volume.restrict (Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100))

theorem theorem2BothStatesContinuousShortUniform_mass_univ :
    theorem2BothStatesContinuousShortUniform Set.univ = 1 := by
  simp [theorem2BothStatesContinuousShortUniform, Real.volume_Icc]
  have h : ((101 : ℝ) / 100 - (99 : ℝ) / 100) = (1 : ℝ) / 50 := by norm_num
  rw [h, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 50)]
  simpa using ENNReal.mul_inv_cancel (a := (50 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem theorem2BothStatesContinuousLongUniform_mass_univ :
    theorem2BothStatesContinuousLongUniform Set.univ = 1 := by
  simp [theorem2BothStatesContinuousLongUniform, Real.volume_Icc]
  have h : ((601 : ℝ) / 100 - (599 : ℝ) / 100) = (1 : ℝ) / 50 := by norm_num
  rw [h, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 50)]
  simpa using ENNReal.mul_inv_cancel (a := (50 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem theorem2BothStatesContinuousShortUniform_integral_id :
    ∫ τ : TripLength, τ ∂theorem2BothStatesContinuousShortUniform = 1 := by
  rw [theorem2BothStatesContinuousShortUniform, integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le
    (by norm_num : (99 : ℝ) / 100 ≤ (101 : ℝ) / 100)]
  rw [integral_id]
  norm_num

theorem theorem2BothStatesContinuousLongUniform_integral_id :
    ∫ τ : TripLength, τ ∂theorem2BothStatesContinuousLongUniform = 6 := by
  rw [theorem2BothStatesContinuousLongUniform, integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le
    (by norm_num : (599 : ℝ) / 100 ≤ (601 : ℝ) / 100)]
  rw [integral_id]
  norm_num

theorem theorem2BothStatesContinuous_shortInterval_subset_acceptAll :
    Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100) ⊆ acceptAllPolicy := by
  intro τ hτ
  simpa [acceptAllPolicy, positiveTripLengths] using (show 0 < τ by linarith [hτ.1])

theorem theorem2BothStatesContinuous_longInterval_subset_acceptAll :
    Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100) ⊆ acceptAllPolicy := by
  intro τ hτ
  simpa [acceptAllPolicy, positiveTripLengths] using (show 0 < τ by linarith [hτ.1])

theorem theorem2BothStatesContinuous_shortInterval_subset_rejectLong :
    Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100) ⊆ rejectLongTripsPolicy 2 := by
  intro τ hτ
  constructor <;> simp
  · linarith [hτ.1]
  · linarith [hτ.2]

theorem theorem2BothStatesContinuous_longInterval_subset_rejectShort :
    Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100) ⊆ rejectShortTripsPolicy 2 := by
  intro τ hτ
  constructor <;> simp
  · linarith [hτ.1]
  · linarith [hτ.1]

theorem theorem2BothStatesContinuousShortUniform_restrict_acceptAll :
    theorem2BothStatesContinuousShortUniform.restrict acceptAllPolicy =
      theorem2BothStatesContinuousShortUniform := by
  rw [theorem2BothStatesContinuousShortUniform, Measure.restrict_smul,
    Measure.restrict_restrict measurableSet_acceptAllPolicy,
    Set.inter_eq_right.mpr theorem2BothStatesContinuous_shortInterval_subset_acceptAll]

theorem theorem2BothStatesContinuousLongUniform_restrict_acceptAll :
    theorem2BothStatesContinuousLongUniform.restrict acceptAllPolicy =
      theorem2BothStatesContinuousLongUniform := by
  rw [theorem2BothStatesContinuousLongUniform, Measure.restrict_smul,
    Measure.restrict_restrict measurableSet_acceptAllPolicy,
    Set.inter_eq_right.mpr theorem2BothStatesContinuous_longInterval_subset_acceptAll]

theorem theorem2BothStatesContinuousShortUniform_restrict_rejectLong :
    theorem2BothStatesContinuousShortUniform.restrict (rejectLongTripsPolicy 2) =
      theorem2BothStatesContinuousShortUniform := by
  rw [theorem2BothStatesContinuousShortUniform, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_rejectLongTripsPolicy 2),
    Set.inter_eq_right.mpr theorem2BothStatesContinuous_shortInterval_subset_rejectLong]

theorem theorem2BothStatesContinuousLongUniform_restrict_rejectShort :
    theorem2BothStatesContinuousLongUniform.restrict (rejectShortTripsPolicy 2) =
      theorem2BothStatesContinuousLongUniform := by
  rw [theorem2BothStatesContinuousLongUniform, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_rejectShortTripsPolicy 2),
    Set.inter_eq_right.mpr theorem2BothStatesContinuous_longInterval_subset_rejectShort]

theorem theorem2BothStatesContinuous_rejectLong_inter_longInterval :
    rejectLongTripsPolicy 2 ∩ Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro τ hτ
  rcases hτ with ⟨hpolicy, hinterval⟩
  change 0 < τ ∧ τ < 2 at hpolicy
  linarith [hpolicy.2, hinterval.1]

theorem theorem2BothStatesContinuous_rejectShort_inter_shortInterval :
    rejectShortTripsPolicy 2 ∩ Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro τ hτ
  rcases hτ with ⟨hpolicy, hinterval⟩
  change 0 < τ ∧ 2 < τ at hpolicy
  linarith [hpolicy.2, hinterval.2]

theorem theorem2BothStatesContinuousLongUniform_restrict_rejectLong :
    theorem2BothStatesContinuousLongUniform.restrict (rejectLongTripsPolicy 2) = 0 := by
  rw [theorem2BothStatesContinuousLongUniform, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_rejectLongTripsPolicy 2),
    theorem2BothStatesContinuous_rejectLong_inter_longInterval,
    Measure.restrict_empty, smul_zero]

theorem theorem2BothStatesContinuousShortUniform_restrict_rejectShort :
    theorem2BothStatesContinuousShortUniform.restrict (rejectShortTripsPolicy 2) = 0 := by
  rw [theorem2BothStatesContinuousShortUniform, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_rejectShortTripsPolicy 2),
    theorem2BothStatesContinuous_rejectShort_inter_shortInterval,
    Measure.restrict_empty, smul_zero]

/-- Continuous bounded-density trip-length distribution used by the Theorem 2 witness. -/
def theorem2BothStatesContinuousMix : Measure TripLength :=
  ((1 : ℝ≥0∞) / 2) • theorem2BothStatesContinuousShortUniform +
    ((1 : ℝ≥0∞) / 2) • theorem2BothStatesContinuousLongUniform

theorem theorem2BothStatesContinuousMix_restrict_acceptAll :
    theorem2BothStatesContinuousMix.restrict acceptAllPolicy = theorem2BothStatesContinuousMix := by
  rw [theorem2BothStatesContinuousMix, Measure.restrict_add,
    Measure.restrict_smul, theorem2BothStatesContinuousShortUniform_restrict_acceptAll,
    Measure.restrict_smul, theorem2BothStatesContinuousLongUniform_restrict_acceptAll]

theorem theorem2BothStatesContinuousMix_restrict_rejectLong :
    theorem2BothStatesContinuousMix.restrict (rejectLongTripsPolicy 2) =
      ((1 : ℝ≥0∞) / 2) • theorem2BothStatesContinuousShortUniform := by
  rw [theorem2BothStatesContinuousMix, Measure.restrict_add,
    Measure.restrict_smul, theorem2BothStatesContinuousShortUniform_restrict_rejectLong,
    Measure.restrict_smul, theorem2BothStatesContinuousLongUniform_restrict_rejectLong,
    smul_zero, add_zero]

theorem theorem2BothStatesContinuousMix_restrict_rejectShort :
    theorem2BothStatesContinuousMix.restrict (rejectShortTripsPolicy 2) =
      ((1 : ℝ≥0∞) / 2) • theorem2BothStatesContinuousLongUniform := by
  rw [theorem2BothStatesContinuousMix, Measure.restrict_add,
    Measure.restrict_smul, theorem2BothStatesContinuousShortUniform_restrict_rejectShort,
    smul_zero, Measure.restrict_smul,
    theorem2BothStatesContinuousLongUniform_restrict_rejectShort, zero_add]

theorem integrable_id_theorem2BothStatesContinuousShortUniform :
    Integrable (fun τ : TripLength => τ) theorem2BothStatesContinuousShortUniform := by
  have hbase :
      Integrable (fun τ : TripLength => τ)
        (volume.restrict (Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100))) :=
    continuous_id.continuousOn.integrableOn_compact isCompact_Icc
  simpa [theorem2BothStatesContinuousShortUniform] using hbase.smul_measure (by norm_num)

theorem integrable_id_theorem2BothStatesContinuousLongUniform :
    Integrable (fun τ : TripLength => τ) theorem2BothStatesContinuousLongUniform := by
  have hbase :
      Integrable (fun τ : TripLength => τ)
        (volume.restrict (Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100))) :=
    continuous_id.continuousOn.integrableOn_compact isCompact_Icc
  simpa [theorem2BothStatesContinuousLongUniform] using hbase.smul_measure (by norm_num)

theorem theorem2BothStatesContinuousMix_acceptAll_integral
    (f : TripLength → ℝ)
    (hshort : Integrable f theorem2BothStatesContinuousShortUniform)
    (hlong : Integrable f theorem2BothStatesContinuousLongUniform) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2BothStatesContinuousMix =
      ((1 : ℝ) / 2) * (∫ τ, f τ ∂theorem2BothStatesContinuousShortUniform) +
        ((1 : ℝ) / 2) * (∫ τ, f τ ∂theorem2BothStatesContinuousLongUniform) := by
  rw [theorem2BothStatesContinuousMix_restrict_acceptAll,
    theorem2BothStatesContinuousMix, integral_add_measure]
  · simp [integral_smul_measure]
  · exact hshort.smul_measure (by norm_num)
  · exact hlong.smul_measure (by norm_num)

theorem theorem2BothStatesContinuousMix_rejectLong_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectLongTripsPolicy 2, f τ ∂theorem2BothStatesContinuousMix =
      ((1 : ℝ) / 2) * (∫ τ, f τ ∂theorem2BothStatesContinuousShortUniform) := by
  rw [theorem2BothStatesContinuousMix_restrict_rejectLong]
  simp [integral_smul_measure]

theorem theorem2BothStatesContinuousMix_rejectShort_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectShortTripsPolicy 2, f τ ∂theorem2BothStatesContinuousMix =
      ((1 : ℝ) / 2) * (∫ τ, f τ ∂theorem2BothStatesContinuousLongUniform) := by
  rw [theorem2BothStatesContinuousMix_restrict_rejectShort]
  simp [integral_smul_measure]

theorem theorem2BothStatesContinuousMix_time_acceptAll :
    singleStateTripTime theorem2BothStatesContinuousMix acceptAllPolicy = (7 : ℝ) / 2 := by
  rw [singleStateTripTime, theorem2BothStatesContinuousMix_acceptAll_integral]
  · rw [theorem2BothStatesContinuousShortUniform_integral_id,
      theorem2BothStatesContinuousLongUniform_integral_id]
    norm_num
  · exact integrable_id_theorem2BothStatesContinuousShortUniform
  · exact integrable_id_theorem2BothStatesContinuousLongUniform

theorem theorem2BothStatesContinuousMix_time_rejectLong :
    singleStateTripTime theorem2BothStatesContinuousMix (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  rw [singleStateTripTime, theorem2BothStatesContinuousMix_rejectLong_integral]
  rw [theorem2BothStatesContinuousShortUniform_integral_id]
  norm_num

theorem theorem2BothStatesContinuousMix_time_rejectShort :
    singleStateTripTime theorem2BothStatesContinuousMix (rejectShortTripsPolicy 2) = 3 := by
  rw [singleStateTripTime, theorem2BothStatesContinuousMix_rejectShort_integral]
  rw [theorem2BothStatesContinuousLongUniform_integral_id]
  norm_num

theorem theorem2BothStatesContinuousMix_mass_univ :
    theorem2BothStatesContinuousMix Set.univ = 1 := by
  simp [theorem2BothStatesContinuousMix,
    theorem2BothStatesContinuousShortUniform_mass_univ,
    theorem2BothStatesContinuousLongUniform_mass_univ]
  rw [← one_div (2 : ℝ≥0∞), ENNReal.div_add_div_same]
  convert ENNReal.div_self (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) using 1
  all_goals norm_num

theorem theorem2BothStatesContinuousMix_acceptAll_mass :
    singleStateTripMass theorem2BothStatesContinuousMix acceptAllPolicy = 1 := by
  unfold singleStateTripMass
  rw [← Measure.restrict_apply_univ acceptAllPolicy,
    theorem2BothStatesContinuousMix_restrict_acceptAll,
    theorem2BothStatesContinuousMix_mass_univ]
  norm_num

theorem theorem2BothStatesContinuousMix_rejectLong_mass :
    singleStateTripMass theorem2BothStatesContinuousMix (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  unfold singleStateTripMass
  rw [← Measure.restrict_apply_univ (rejectLongTripsPolicy 2),
    theorem2BothStatesContinuousMix_restrict_rejectLong]
  simp [theorem2BothStatesContinuousShortUniform_mass_univ]

theorem theorem2BothStatesContinuousMix_rejectShort_mass :
    singleStateTripMass theorem2BothStatesContinuousMix (rejectShortTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  unfold singleStateTripMass
  rw [← Measure.restrict_apply_univ (rejectShortTripsPolicy 2),
    theorem2BothStatesContinuousMix_restrict_rejectShort]
  simp [theorem2BothStatesContinuousLongUniform_mass_univ]

def theorem2BothStatesContinuousSwitch : TripLength → ℝ :=
  fun τ => gn21SwitchProb ((1 : ℝ) / 4) ((1 : ℝ) / 4) τ

theorem theorem2BothStatesContinuousSwitch_short_left_gt_one_six :
    (1 : ℝ) / 6 < theorem2BothStatesContinuousSwitch ((99 : ℝ) / 100) := by
  have hbase : (499 : ℝ) / 400 < Real.exp ((99 : ℝ) / 400) := by
    have h := Real.add_one_lt_exp
      (show ((99 : ℝ) / 400) ≠ 0 by norm_num)
    norm_num at h ⊢
    exact h
  have hsquare : ((499 : ℝ) / 400) ^ 2 <
      (Real.exp ((99 : ℝ) / 400)) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (Real.exp_nonneg _)).mpr hbase
  have hthree_halves : (3 : ℝ) / 2 < Real.exp ((99 : ℝ) / 200) := by
    rw [show ((99 : ℝ) / 200) = (99 : ℝ) / 400 + (99 : ℝ) / 400 by ring,
      Real.exp_add]
    nlinarith
  have hexp_lt : Real.exp (-((99 : ℝ) / 200)) < (2 : ℝ) / 3 := by
    have hinv : (Real.exp ((99 : ℝ) / 200))⁻¹ < ((3 : ℝ) / 2)⁻¹ :=
      inv_strictAnti₀ (by norm_num : 0 < (3 : ℝ) / 2) hthree_halves
    have hexp_rewrite : Real.exp (-((99 : ℝ) / 200)) =
        (Real.exp ((99 : ℝ) / 200))⁻¹ := by
      rw [Real.exp_neg]
    rw [hexp_rewrite]
    norm_num at hinv ⊢
    exact hinv
  rw [theorem2BothStatesContinuousSwitch, paper_lemma2_switch_probability_formula]
  ring_nf
  nlinarith

theorem theorem2BothStatesContinuousSwitch_mono {s t : TripLength} (hst : s ≤ t) :
    theorem2BothStatesContinuousSwitch s ≤ theorem2BothStatesContinuousSwitch t := by
  unfold theorem2BothStatesContinuousSwitch
  rw [paper_lemma2_switch_probability_formula,
    paper_lemma2_switch_probability_formula]
  have hexp :
      Real.exp (-(((1 : ℝ) / 4 + (1 : ℝ) / 4) * t)) ≤
        Real.exp (-(((1 : ℝ) / 4 + (1 : ℝ) / 4) * s)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  ring_nf at hexp ⊢
  nlinarith

theorem integrable_theorem2BothStatesContinuousSwitch_shortUniform :
    Integrable theorem2BothStatesContinuousSwitch theorem2BothStatesContinuousShortUniform := by
  have hbase :
      Integrable theorem2BothStatesContinuousSwitch
        (volume.restrict (Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100))) :=
    (continuous_gn21SwitchProb ((1 : ℝ) / 4) ((1 : ℝ) / 4)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  simpa [theorem2BothStatesContinuousShortUniform, theorem2BothStatesContinuousSwitch] using
    hbase.smul_measure (by norm_num)

theorem theorem2BothStatesContinuousSwitch_short_average_gt_one_six :
    (1 : ℝ) / 6 <
      ∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousShortUniform := by
  letI : IsFiniteMeasure theorem2BothStatesContinuousShortUniform := ⟨by
    rw [theorem2BothStatesContinuousShortUniform_mass_univ]
    norm_num⟩
  have hmem_base :
      ∀ᵐ τ ∂(volume.restrict (Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100))),
        τ ∈ Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100) :=
    ae_restrict_mem measurableSet_Icc
  have hmem :
      ∀ᵐ τ ∂theorem2BothStatesContinuousShortUniform,
        τ ∈ Set.Icc ((99 : ℝ) / 100) ((101 : ℝ) / 100) := by
    rw [theorem2BothStatesContinuousShortUniform]
    exact (Measure.ae_ennreal_smul_measure_iff
      (by norm_num : (50 : ℝ≥0∞) ≠ 0)).2 hmem_base
  have hbound : theorem2BothStatesContinuousSwitch ((99 : ℝ) / 100) ≤
      ∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousShortUniform := by
    have h := integral_mono_ae
      (integrable_const (theorem2BothStatesContinuousSwitch ((99 : ℝ) / 100)))
      integrable_theorem2BothStatesContinuousSwitch_shortUniform
      (hmem.mono fun τ hτ => theorem2BothStatesContinuousSwitch_mono hτ.1)
    simpa [Measure.real, theorem2BothStatesContinuousShortUniform_mass_univ] using h
  linarith [theorem2BothStatesContinuousSwitch_short_left_gt_one_six]

theorem integrable_theorem2BothStatesContinuousSwitch_longUniform :
    Integrable theorem2BothStatesContinuousSwitch theorem2BothStatesContinuousLongUniform := by
  have hbase :
      Integrable theorem2BothStatesContinuousSwitch
        (volume.restrict (Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100))) :=
    (continuous_gn21SwitchProb ((1 : ℝ) / 4) ((1 : ℝ) / 4)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  simpa [theorem2BothStatesContinuousLongUniform, theorem2BothStatesContinuousSwitch] using
    hbase.smul_measure (by norm_num)

theorem theorem2BothStatesContinuousSwitch_nonneg_of_nonneg {τ : TripLength} (hτ : 0 ≤ τ) :
    0 ≤ theorem2BothStatesContinuousSwitch τ :=
  paper_lemma2_switch_probability_nonneg
    ((1 : ℝ) / 4) ((1 : ℝ) / 4) τ
    (by norm_num) (by norm_num) hτ

theorem theorem2BothStatesContinuousSwitch_le_half (τ : TripLength) :
    theorem2BothStatesContinuousSwitch τ ≤ (1 : ℝ) / 2 := by
  rw [theorem2BothStatesContinuousSwitch, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (τ * (-(1 : ℝ) / 2)) := Real.exp_nonneg _
  nlinarith

theorem theorem2BothStatesContinuousSwitch_long_average_nonneg :
    0 ≤ ∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousLongUniform := by
  have hmem_base :
      ∀ᵐ τ ∂(volume.restrict (Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100))),
        τ ∈ Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100) :=
    ae_restrict_mem measurableSet_Icc
  have hmem :
      ∀ᵐ τ ∂theorem2BothStatesContinuousLongUniform,
        τ ∈ Set.Icc ((599 : ℝ) / 100) ((601 : ℝ) / 100) := by
    rw [theorem2BothStatesContinuousLongUniform]
    exact (Measure.ae_ennreal_smul_measure_iff
      (by norm_num : (50 : ℝ≥0∞) ≠ 0)).2 hmem_base
  apply integral_nonneg_of_ae
  exact hmem.mono fun τ hτ =>
    theorem2BothStatesContinuousSwitch_nonneg_of_nonneg (by linarith [hτ.1])

theorem theorem2BothStatesContinuousSwitch_long_average_le_half :
    (∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousLongUniform) ≤
      (1 : ℝ) / 2 := by
  letI : IsFiniteMeasure theorem2BothStatesContinuousLongUniform := ⟨by
    rw [theorem2BothStatesContinuousLongUniform_mass_univ]
    norm_num⟩
  have h := integral_mono_ae integrable_theorem2BothStatesContinuousSwitch_longUniform
    (integrable_const ((1 : ℝ) / 2))
    (ae_of_all theorem2BothStatesContinuousLongUniform
      theorem2BothStatesContinuousSwitch_le_half)
  simpa [Measure.real, theorem2BothStatesContinuousLongUniform_mass_univ] using h

def theorem2BothStatesContinuousMu : Fin 2 → Measure TripLength
  | _ => theorem2BothStatesContinuousMix

def theorem2BothStatesContinuousArrival : Fin 2 → ℝ
  | 0 => 1
  | 1 => 2

def theorem2BothStatesContinuousM : Fin 2 → ℝ
  | 0 => 1
  | 1 => 10

def theorem2BothStatesContinuousNonsurgeDeviation : Fin 2 → TripPolicy
  | 0 => rejectLongTripsPolicy 2
  | 1 => acceptAllPolicy

def theorem2BothStatesContinuousSurgeDeviation : Fin 2 → TripPolicy
  | 0 => acceptAllPolicy
  | 1 => rejectShortTripsPolicy 2

def theorem2BothStatesContinuousQShort : ℝ :=
  ∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousShortUniform

def theorem2BothStatesContinuousQLong : ℝ :=
  ∫ τ, theorem2BothStatesContinuousSwitch τ ∂theorem2BothStatesContinuousLongUniform

theorem theorem2BothStatesContinuousQShort_gt_one_six :
    (1 : ℝ) / 6 < theorem2BothStatesContinuousQShort := by
  exact theorem2BothStatesContinuousSwitch_short_average_gt_one_six

theorem theorem2BothStatesContinuousQLong_nonneg :
    0 ≤ theorem2BothStatesContinuousQLong := by
  exact theorem2BothStatesContinuousSwitch_long_average_nonneg

theorem theorem2BothStatesContinuousQLong_le_half :
    theorem2BothStatesContinuousQLong ≤ (1 : ℝ) / 2 := by
  exact theorem2BothStatesContinuousSwitch_long_average_le_half

theorem theorem2BothStatesContinuousExitWeight_acceptAll_arrival_one :
    gn21ExitWeightIntegral theorem2BothStatesContinuousMix 1
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) acceptAllPolicy =
      (1 : ℝ) / 4 +
        (1 : ℝ) / 2 * theorem2BothStatesContinuousQShort +
          (1 : ℝ) / 2 * theorem2BothStatesContinuousQLong := by
  unfold gn21ExitWeightIntegral theorem2BothStatesContinuousQShort
    theorem2BothStatesContinuousQLong
  rw [theorem2BothStatesContinuousMix_acceptAll_integral]
  · simp only [theorem2BothStatesContinuousSwitch]
    ring
  · exact integrable_theorem2BothStatesContinuousSwitch_shortUniform
  · exact integrable_theorem2BothStatesContinuousSwitch_longUniform

theorem theorem2BothStatesContinuousExitWeight_rejectLong_arrival_one :
    gn21ExitWeightIntegral theorem2BothStatesContinuousMix 1
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 4 + (1 : ℝ) / 2 * theorem2BothStatesContinuousQShort := by
  unfold gn21ExitWeightIntegral theorem2BothStatesContinuousQShort
  rw [theorem2BothStatesContinuousMix_rejectLong_integral]
  simp only [theorem2BothStatesContinuousSwitch]
  ring

theorem theorem2BothStatesContinuousExitWeight_acceptAll_arrival_two :
    gn21ExitWeightIntegral theorem2BothStatesContinuousMix 2
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) acceptAllPolicy =
      (1 : ℝ) / 4 + theorem2BothStatesContinuousQShort +
        theorem2BothStatesContinuousQLong := by
  unfold gn21ExitWeightIntegral theorem2BothStatesContinuousQShort
    theorem2BothStatesContinuousQLong
  rw [theorem2BothStatesContinuousMix_acceptAll_integral]
  · simp only [theorem2BothStatesContinuousSwitch]
    ring
  · exact integrable_theorem2BothStatesContinuousSwitch_shortUniform
  · exact integrable_theorem2BothStatesContinuousSwitch_longUniform

theorem theorem2BothStatesContinuousExitWeight_rejectShort_arrival_two :
    gn21ExitWeightIntegral theorem2BothStatesContinuousMix 2
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) (rejectShortTripsPolicy 2) =
      (1 : ℝ) / 4 + theorem2BothStatesContinuousQLong := by
  unfold gn21ExitWeightIntegral theorem2BothStatesContinuousQLong
  rw [theorem2BothStatesContinuousMix_rejectShort_integral]
  simp only [theorem2BothStatesContinuousSwitch]
  ring

theorem theorem2BothStatesContinuousPayment_acceptAll_m_one :
    singleStateTripPayment theorem2BothStatesContinuousMix (multiplicativePricing 1)
        acceptAllPolicy = (7 : ℝ) / 2 := by
  rw [singleStateTripPayment_multiplicativePricing,
    theorem2BothStatesContinuousMix_time_acceptAll]
  norm_num

theorem theorem2BothStatesContinuousPayment_rejectLong_m_one :
    singleStateTripPayment theorem2BothStatesContinuousMix (multiplicativePricing 1)
        (rejectLongTripsPolicy 2) = (1 : ℝ) / 2 := by
  rw [singleStateTripPayment_multiplicativePricing,
    theorem2BothStatesContinuousMix_time_rejectLong]
  norm_num

theorem theorem2BothStatesContinuousPayment_acceptAll_m_ten :
    singleStateTripPayment theorem2BothStatesContinuousMix (multiplicativePricing 10)
        acceptAllPolicy = 35 := by
  rw [singleStateTripPayment_multiplicativePricing,
    theorem2BothStatesContinuousMix_time_acceptAll]
  norm_num

theorem theorem2BothStatesContinuousPayment_rejectShort_m_ten :
    singleStateTripPayment theorem2BothStatesContinuousMix (multiplicativePricing 10)
        (rejectShortTripsPolicy 2) = 30 := by
  rw [singleStateTripPayment_multiplicativePricing,
    theorem2BothStatesContinuousMix_time_rejectShort]
  norm_num

theorem theorem2BothStatesContinuousScaledTime_zero_acceptAll :
    gn21ScaledStateTime (theorem2BothStatesContinuousMu 0)
        (theorem2BothStatesContinuousArrival 0) acceptAllPolicy = (9 : ℝ) / 2 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousMix_time_acceptAll]

theorem theorem2BothStatesContinuousScaledTime_zero_rejectLong :
    gn21ScaledStateTime (theorem2BothStatesContinuousMu 0)
        (theorem2BothStatesContinuousArrival 0) (rejectLongTripsPolicy 2) =
      (3 : ℝ) / 2 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousMix_time_rejectLong]

theorem theorem2BothStatesContinuousScaledTime_one_acceptAll :
    gn21ScaledStateTime (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 1) acceptAllPolicy = 8 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousMix_time_acceptAll]

theorem theorem2BothStatesContinuousScaledTime_one_rejectShort :
    gn21ScaledStateTime (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 1) (rejectShortTripsPolicy 2) = 7 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousMix_time_rejectShort]

theorem theorem2BothStatesContinuousScaledEarning_zero_acceptAll :
    gn21ScaledStateEarning (theorem2BothStatesContinuousMu 0)
        (theorem2BothStatesContinuousArrival 0)
        (multiplicativePricing (theorem2BothStatesContinuousM 0)) acceptAllPolicy =
      (7 : ℝ) / 2 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousM,
    theorem2BothStatesContinuousPayment_acceptAll_m_one]

theorem theorem2BothStatesContinuousScaledEarning_zero_rejectLong :
    gn21ScaledStateEarning (theorem2BothStatesContinuousMu 0)
        (theorem2BothStatesContinuousArrival 0)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (rejectLongTripsPolicy 2) = (1 : ℝ) / 2 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousM,
    theorem2BothStatesContinuousPayment_rejectLong_m_one]

theorem theorem2BothStatesContinuousScaledEarning_one_acceptAll :
    gn21ScaledStateEarning (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 1)
        (multiplicativePricing (theorem2BothStatesContinuousM 1)) acceptAllPolicy = 70 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousM,
    theorem2BothStatesContinuousPayment_acceptAll_m_ten]

theorem theorem2BothStatesContinuousScaledEarning_one_rejectShort :
    gn21ScaledStateEarning (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 1)
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        (rejectShortTripsPolicy 2) = 60 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesContinuousMu,
    theorem2BothStatesContinuousArrival, theorem2BothStatesContinuousM,
    theorem2BothStatesContinuousPayment_rejectShort_m_ten]

theorem theorem2BothStatesContinuousAggregateReward_acceptAll :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 +
          (1 : ℝ) / 2 * theorem2BothStatesContinuousQShort +
            (1 : ℝ) / 2 * theorem2BothStatesContinuousQLong)
        ((1 : ℝ) / 4 + theorem2BothStatesContinuousQShort +
          theorem2BothStatesContinuousQLong)
        ((9 : ℝ) / 2) 8 ((7 : ℝ) / 2) 70 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesContinuousMu, theorem2BothStatesContinuousArrival,
    theorem2BothStatesContinuousM]
  rw [theorem2BothStatesContinuousExitWeight_acceptAll_arrival_one,
    theorem2BothStatesContinuousExitWeight_acceptAll_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesContinuousMix_time_acceptAll,
    theorem2BothStatesContinuousPayment_acceptAll_m_one,
    theorem2BothStatesContinuousPayment_acceptAll_m_ten]

theorem theorem2BothStatesContinuousAggregateReward_nonsurgeDeviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        (rejectLongTripsPolicy 2) acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * theorem2BothStatesContinuousQShort)
        ((1 : ℝ) / 4 + theorem2BothStatesContinuousQShort +
          theorem2BothStatesContinuousQLong)
        ((3 : ℝ) / 2) 8 ((1 : ℝ) / 2) 70 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesContinuousMu, theorem2BothStatesContinuousArrival,
    theorem2BothStatesContinuousM]
  rw [theorem2BothStatesContinuousExitWeight_rejectLong_arrival_one,
    theorem2BothStatesContinuousExitWeight_acceptAll_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesContinuousMix_time_rejectLong,
    theorem2BothStatesContinuousMix_time_acceptAll,
    theorem2BothStatesContinuousPayment_rejectLong_m_one,
    theorem2BothStatesContinuousPayment_acceptAll_m_ten]

theorem theorem2BothStatesContinuousAggregateReward_surgeDeviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy (rejectShortTripsPolicy 2) =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 +
          (1 : ℝ) / 2 * theorem2BothStatesContinuousQShort +
            (1 : ℝ) / 2 * theorem2BothStatesContinuousQLong)
        ((1 : ℝ) / 4 + theorem2BothStatesContinuousQLong)
        ((9 : ℝ) / 2) 7 ((7 : ℝ) / 2) 60 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesContinuousMu, theorem2BothStatesContinuousArrival,
    theorem2BothStatesContinuousM]
  rw [theorem2BothStatesContinuousExitWeight_acceptAll_arrival_one,
    theorem2BothStatesContinuousExitWeight_rejectShort_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesContinuousMix_time_acceptAll,
    theorem2BothStatesContinuousMix_time_rejectShort,
    theorem2BothStatesContinuousPayment_acceptAll_m_one,
    theorem2BothStatesContinuousPayment_rejectShort_m_ten]

theorem theorem2BothStatesContinuousAggregate_profitable_nonsurge :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        (rejectLongTripsPolicy 2) acceptAllPolicy := by
  rw [theorem2BothStatesContinuousAggregateReward_acceptAll,
    theorem2BothStatesContinuousAggregateReward_nonsurgeDeviation]
  exact theorem2BothStatesAggregate_nonsurge_algebra
    (le_of_lt (lt_trans (by norm_num : 0 < (1 : ℝ) / 6)
      theorem2BothStatesContinuousQShort_gt_one_six))
    theorem2BothStatesContinuousQLong_nonneg
    theorem2BothStatesContinuousQLong_le_half

theorem theorem2BothStatesContinuousAggregate_profitable_surge :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy (rejectShortTripsPolicy 2) := by
  rw [theorem2BothStatesContinuousAggregateReward_acceptAll,
    theorem2BothStatesContinuousAggregateReward_surgeDeviation]
  exact theorem2BothStatesAggregate_surge_algebra
    theorem2BothStatesContinuousQShort_gt_one_six
    theorem2BothStatesContinuousQLong_nonneg
    theorem2BothStatesContinuousQLong_le_half

theorem theorem2BothStatesContinuousAcceptAll_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
      (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      acceptAllPolicy acceptAllPolicy := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_acceptAll_mass]
    norm_num
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_acceptAll_mass]
    norm_num
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num
  · norm_num
  · exact measurableSet_acceptAllPolicy
  · exact measurableSet_acceptAllPolicy
  · intro τ hτ
    exact hτ
  · intro τ hτ
    exact hτ

theorem theorem2BothStatesContinuousNonsurgeDeviation_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
      (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      (rejectLongTripsPolicy 2) acceptAllPolicy := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_rejectLong_mass]
    norm_num
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_acceptAll_mass]
    norm_num
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num
  · norm_num
  · exact measurableSet_rejectLongTripsPolicy 2
  · exact measurableSet_acceptAllPolicy
  · intro τ hτ
    exact hτ.1
  · intro τ hτ
    exact hτ

theorem theorem2BothStatesContinuousSurgeDeviation_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
      (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      acceptAllPolicy (rejectShortTripsPolicy 2) := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_acceptAll_mass]
    norm_num
  · rw [theorem2BothStatesContinuousMu,
      theorem2BothStatesContinuousMix_rejectShort_mass]
    norm_num
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num [theorem2BothStatesContinuousArrival]
  · norm_num
  · norm_num
  · exact measurableSet_acceptAllPolicy
  · exact measurableSet_rejectShortTripsPolicy 2
  · intro τ hτ
    exact hτ
  · intro τ hτ
    exact hτ.1

theorem paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_continuous :
    dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
        theorem2BothStatesContinuousNonsurgeDeviation ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
        theorem2BothStatesContinuousSurgeDeviation := by
  constructor
  · unfold dynamicProfitableDeviation gn21MeasuredDynamicRewardFunctional
    exact
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy acceptAllPolicy
        (theorem2BothStatesContinuousNonsurgeDeviation 0)
        (theorem2BothStatesContinuousNonsurgeDeviation 1)
        theorem2BothStatesContinuousAcceptAll_nondegenerate
        theorem2BothStatesContinuousNonsurgeDeviation_nondegenerate
        (by
          simpa [theorem2BothStatesContinuousNonsurgeDeviation]
            using theorem2BothStatesContinuousAggregate_profitable_nonsurge)
  · unfold dynamicProfitableDeviation gn21MeasuredDynamicRewardFunctional
    exact
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (theorem2BothStatesContinuousMu 0) (theorem2BothStatesContinuousMu 1)
        (theorem2BothStatesContinuousArrival 0) (theorem2BothStatesContinuousArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesContinuousM 0))
        (multiplicativePricing (theorem2BothStatesContinuousM 1))
        acceptAllPolicy acceptAllPolicy
        (theorem2BothStatesContinuousSurgeDeviation 0)
        (theorem2BothStatesContinuousSurgeDeviation 1)
        theorem2BothStatesContinuousAcceptAll_nondegenerate
        theorem2BothStatesContinuousSurgeDeviation_nondegenerate
        (by
          simpa [theorem2BothStatesContinuousSurgeDeviation]
            using theorem2BothStatesContinuousAggregate_profitable_surge)

theorem paper_theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_in_both_states_explicit_continuous :
    ((0 < (2 : ℝ) ∧
        rejectsLongTrips 2 (theorem2BothStatesContinuousNonsurgeDeviation 0)) ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
        theorem2BothStatesContinuousNonsurgeDeviation) ∧
      ((0 < (2 : ℝ) ∧
          rejectsShortTrips 2 (theorem2BothStatesContinuousSurgeDeviation 1)) ∧
        dynamicProfitableDeviation
          (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
            theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
            (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
          theorem2BothStatesContinuousSurgeDeviation) := by
  refine ⟨⟨⟨by norm_num, ?_⟩,
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_continuous.1⟩,
    ⟨⟨by norm_num, ?_⟩,
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_continuous.2⟩⟩
  · intro τ hτ
    simp [theorem2BothStatesContinuousNonsurgeDeviation, rejectLongTripsPolicy, hτ]
  · intro τ hτ
    simp [theorem2BothStatesContinuousSurgeDeviation, rejectShortTripsPolicy]

theorem paper_theorem2_multiplicative_measured_not_ic_both_states_explicit_continuous :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
        theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesContinuousM i))) :=
    not_dynamicIncentiveCompatible_of_profitableDeviation
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
        theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
      theorem2BothStatesContinuousNonsurgeDeviation
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_continuous.1

end

end GN21DriverSurgePricing
