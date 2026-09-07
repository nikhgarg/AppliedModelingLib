import AppliedModelingLib.Foundations.Probability.StationaryPoissonDisplacement

/-!
# Calendar-time first-report displacement

For Lemma 1, a retained incident is observed at its birth time plus its
first-report delay. This module records the intensity calculation for that
calendar-time displacement. The remaining point-process theorem must derive
independent Poisson interval counts from the marked birth process; an intensity
equality alone is not that theorem.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal MeasureTheory NNReal

noncomputable section

/-- The source primitives for calendar-time first reports. A point of the
marked birth process is a pair `(birth time, first-report delay)`, present only
when the incident reports before its duration ends. The finite retained-delay
measure has total mass equal to that reporting probability. -/
structure CalendarFirstReportSourceModel
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  incidentRate : ℝ
  /-- Poisson incidence may be degenerate at zero; the source's Lemma 1
  calculation includes that boundary. -/
  incidentRate_nonnegative : 0 ≤ incidentRate
  retentionProbability : ℝ
  /-- An incident may have zero probability of reporting before its duration
  ends; this is likewise a source-valid boundary. -/
  retentionProbability_nonnegative : 0 ≤ retentionProbability
  retentionProbability_le_one : retentionProbability ≤ 1
  retainedDelay : Measure ℝ
  retainedDelay_finite : IsFiniteMeasure retainedDelay
  retainedDelay_nonnegative_support : retainedDelay (Set.Iio (0 : ℝ)) = 0
  retainedDelay_mass :
    retainedDelay Set.univ = ENNReal.ofReal retentionProbability
  markedBirths : AppliedModelingLib.Probability.PoissonCountingMeasureByLaw
    Ω (ℝ × ℝ) P
      (ENNReal.ofReal incidentRate • ((volume : Measure ℝ).prod retainedDelay))

namespace CalendarFirstReportSourceModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Marked birth points whose calendar-time first reports fall in `(a,b]`. -/
def firstReportSet (a b : ℝ) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Set.Ioc a b

/-- The observed first-report count from calendar time zero through `t`. -/
def calendarCount (M : CalendarFirstReportSourceModel Ω P)
    (t : ℝ≥0) : Ω → ℕ :=
  M.markedBirths.finiteCount (firstReportSet 0 t)

/-- The marked first-report set is measurable. -/
theorem measurableSet_firstReportSet (a b : ℝ) :
    MeasurableSet (firstReportSet a b) :=
  measurableSet_Ioc.preimage (measurable_fst.add measurable_snd)

/-- A bounded calendar interval has finite marked-birth intensity. -/
theorem firstReportSet_intensity_ne_top
    (M : CalendarFirstReportSourceModel Ω P) (a b : ℝ) :
    (ENNReal.ofReal M.incidentRate •
      ((volume : Measure ℝ).prod M.retainedDelay))
        (firstReportSet a b) ≠ ∞ := by
  letI : IsFiniteMeasure M.retainedDelay := M.retainedDelay_finite
  change (ENNReal.ofReal M.incidentRate •
    ((volume : Measure ℝ).prod M.retainedDelay))
      ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Set.Ioc a b) ≠ ∞
  rw [AppliedModelingLib.Probability.smul_volume_prod_preimage_add_Ioc]
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ne_of_lt measure_Ioc_lt_top)

/-- Adjacent calendar first-report intervals concatenate. -/
theorem firstReportSet_union {s t : ℝ≥0} (hst : s ≤ t) :
    firstReportSet 0 s ∪ firstReportSet s t = firstReportSet 0 t := by
  unfold firstReportSet
  rw [← Set.preimage_union]
  exact congrArg (fun u => (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' u)
    (Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (NNReal.coe_le_coe.mpr hst))

/-- Adjacent calendar first-report intervals are disjoint. -/
theorem disjoint_firstReportSet_adjacent {s t : ℝ≥0} :
    Disjoint (firstReportSet 0 s) (firstReportSet s t) := by
  refine Set.disjoint_left.2 ?_
  intro z hz0 hzt
  change z.1 + z.2 ∈ Set.Ioc 0 (s : ℝ) at hz0
  change z.1 + z.2 ∈ Set.Ioc (s : ℝ) (t : ℝ) at hzt
  exact
    (Set.disjoint_left.1
      (Set.Ioc_disjoint_Ioc_of_le (a := (0 : ℝ)) (b := (s : ℝ))
        (c := (s : ℝ)) (d := (t : ℝ)) le_rfl) hz0 hzt)

/-- The count starts at zero at calendar time zero. -/
theorem calendarCount_zero_ae
    (M : CalendarFirstReportSourceModel Ω P) :
    ∀ᵐ ω ∂P, M.calendarCount 0 ω = 0 := by
  simpa [calendarCount, firstReportSet] using M.markedBirths.finiteCount_empty_ae

/-- Calendar first-report counts are pathwise nondecreasing. -/
theorem calendarCount_mono
    (M : CalendarFirstReportSourceModel Ω P) (ω : Ω) :
    Monotone fun t => M.calendarCount t ω := by
  intro s t hst
  apply M.markedBirths.finiteCount_mono
  · exact measurableSet_firstReportSet 0 s
  · exact measurableSet_firstReportSet 0 t
  · exact M.firstReportSet_intensity_ne_top 0 s
  · exact M.firstReportSet_intensity_ne_top 0 t
  · intro z hz
    change z.1 + z.2 ∈ Set.Ioc 0 (s : ℝ) at hz
    change z.1 + z.2 ∈ Set.Ioc 0 (t : ℝ)
    exact ⟨hz.1, le_trans hz.2 (NNReal.coe_le_coe.mpr hst)⟩

/-- The marked-birth intensity of an observed calendar interval has exactly
the source rate `incidentRate * retentionProbability`. -/
theorem firstReportSet_intensity_toNNReal_eq_rateExposure
    (M : CalendarFirstReportSourceModel Ω P) {s t : ℝ≥0} (hst : s ≤ t) :
    ((ENNReal.ofReal M.incidentRate •
      ((volume : Measure ℝ).prod M.retainedDelay))
      (firstReportSet s t)).toNNReal =
      AppliedModelingLib.Probability.PoissonProcess.rateExposureParam
        (M.incidentRate * M.retentionProbability) ((t : ℝ) - (s : ℝ))
        (mul_nonneg (mul_nonneg M.incidentRate_nonnegative M.retentionProbability_nonnegative)
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))) := by
  letI : IsFiniteMeasure M.retainedDelay := M.retainedDelay_finite
  apply ENNReal.coe_injective
  rw [ENNReal.coe_toNNReal (M.firstReportSet_intensity_ne_top s t)]
  change (ENNReal.ofReal M.incidentRate •
    ((volume : Measure ℝ).prod M.retainedDelay))
      ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Set.Ioc (s : ℝ) (t : ℝ)) = _
  rw [AppliedModelingLib.Probability.smul_volume_prod_preimage_add_Ioc]
  rw [M.retainedDelay_mass, Real.volume_Ioc]
  simp only [AppliedModelingLib.Probability.PoissonProcess.rateExposureParam]
  rw [ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal M.incidentRate * ENNReal.ofReal M.retentionProbability *
      ENNReal.ofReal ((t : ℝ) - (s : ℝ)) =
    ENNReal.ofReal (M.incidentRate * M.retentionProbability * ((t : ℝ) - (s : ℝ)))
  rw [← ENNReal.ofReal_mul M.incidentRate_nonnegative]
  exact (ENNReal.ofReal_mul
    (mul_nonneg M.incidentRate_nonnegative M.retentionProbability_nonnegative)).symm

/-- A forward increment of the calendar count is the count of exactly the
corresponding displaced marked-birth interval. -/
theorem calendarCount_increment_ae_eq_markedIntervalCount
    (M : CalendarFirstReportSourceModel Ω P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, M.calendarCount t ω - M.calendarCount s ω =
      M.markedBirths.finiteCount (firstReportSet s t) ω := by
  have hadd := M.markedBirths.finiteCount_union_ae
    (firstReportSet 0 s) (firstReportSet s t)
    (measurableSet_firstReportSet 0 s) (measurableSet_firstReportSet s t)
    (M.firstReportSet_intensity_ne_top 0 s)
    (M.firstReportSet_intensity_ne_top s t)
    (disjoint_firstReportSet_adjacent (s := s) (t := t))
  filter_upwards [hadd] with ω hω
  have hsum : M.calendarCount t ω = M.calendarCount s ω +
      M.markedBirths.finiteCount (firstReportSet s t) ω := by
    simpa only [calendarCount, firstReportSet_union hst] using hω
  exact (Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsum.symm)).symm

/-- Each calendar first-report increment has its derived Poisson law. -/
theorem calendarCount_increment_hasLaw
    (M : CalendarFirstReportSourceModel Ω P) {s t : ℝ≥0} (hst : s ≤ t) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => M.calendarCount t ω - M.calendarCount s ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam
          (M.incidentRate * M.retentionProbability) ((t : ℝ) - (s : ℝ))
          (mul_nonneg (mul_nonneg M.incidentRate_nonnegative M.retentionProbability_nonnegative)
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P := by
  have h := M.markedBirths.finiteCount_hasLaw (firstReportSet s t)
    (measurableSet_firstReportSet s t)
    (M.firstReportSet_intensity_ne_top s t)
  rw [M.firstReportSet_intensity_toNNReal_eq_rateExposure hst] at h
  exact h.congr (M.calendarCount_increment_ae_eq_markedIntervalCount hst)

/-- The calendar count has independent increments because its disjoint
calendar intervals are disjoint preimages in the marked stationary process. -/
theorem calendarCount_hasIndepIncrements
    (M : CalendarFirstReportSourceModel Ω P) :
    ProbabilityTheory.HasIndepIncrements M.calendarCount P := by
  intro n t ht
  have hmarked := M.markedBirths.finiteCount_independent n
    (fun i => firstReportSet (t i.castSucc) (t i.succ))
    (fun i => measurableSet_firstReportSet (t i.castSucc) (t i.succ))
    (fun i => M.firstReportSet_intensity_ne_top (t i.castSucc) (t i.succ))
    (by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hindex : i.succ ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.succ_le_iff.mpr (Fin.mk_lt_mk.mp hij)
        have htime : t i.succ ≤ t j.castSucc := ht hindex
        refine Set.disjoint_left.2 ?_
        intro z hzi hzj
        change z.1 + z.2 ∈ Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) at hzi
        change z.1 + z.2 ∈ Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) at hzj
        exact (Set.disjoint_left.1
          (Set.Ioc_disjoint_Ioc_of_le (NNReal.coe_le_coe.mpr htime)) hzi hzj)
      · have hindex : j.succ ≤ i.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.succ_le_iff.mpr (Fin.mk_lt_mk.mp hji)
        have htime : t j.succ ≤ t i.castSucc := ht hindex
        refine Disjoint.symm (Set.disjoint_left.2 ?_)
        intro z hzj hzi
        change z.1 + z.2 ∈ Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) at hzj
        change z.1 + z.2 ∈ Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) at hzi
        exact (Set.disjoint_left.1
          (Set.Ioc_disjoint_Ioc_of_le (NNReal.coe_le_coe.mpr htime)) hzj hzi))
  apply (ProbabilityTheory.iIndepFun_congr ?_).mpr hmarked
  intro i
  exact M.calendarCount_increment_ae_eq_markedIntervalCount
    (ht (Fin.castSucc_le_succ i))

/-- The literal source model produces a forward homogeneous Poisson process
of calendar-time first reports, at the incident rate times the probability of
reporting before the duration ends. -/
def toForwardHomogeneousPoissonProcess
    (M : CalendarFirstReportSourceModel Ω P)
    (incidentRate_pos : 0 < M.incidentRate)
    (retentionProbability_pos : 0 < M.retentionProbability) :
    ForwardHomogeneousPoissonCountingProcessByLaw Ω P where
  isProbability := M.markedBirths.isProbability
  rate := M.incidentRate * M.retentionProbability
  rate_pos := mul_pos incidentRate_pos retentionProbability_pos
  count := M.calendarCount
  count_measurable := fun t =>
    M.markedBirths.measurable_finiteCount (firstReportSet 0 t)
  count_zero_ae := M.calendarCount_zero_ae
  count_mono_ae := Filter.Eventually.of_forall M.calendarCount_mono
  hasIndepIncrements := M.calendarCount_hasIndepIncrements
  increment_hasLaw := by
    intro s t hst
    exact M.calendarCount_increment_hasLaw hst

end CalendarFirstReportSourceModel

/-- Translating stationary birth intensity by a finite retained-delay measure
preserves its Lebesgue form. The retained-delay mass is the probability that an
incident is first reported before its duration ends. -/
theorem calendar_first_report_intensity_eq_mass_smul
    (retainedDelay : Measure ℝ) [IsFiniteMeasure retainedDelay] :
    (volume : Measure ℝ) ∗ retainedDelay = retainedDelay Set.univ • volume :=
  AppliedModelingLib.Probability.volume_conv_eq_mass_smul retainedDelay

/-- For a calendar interval, the marked-birth intensity of first reports is
the incident intensity times the retained-delay mass times interval length. -/
theorem calendar_first_report_intensity_Ioc
    (incidentIntensity : ℝ≥0∞) (retainedDelay : Measure ℝ)
    [IsFiniteMeasure retainedDelay] (a b : ℝ) :
    (incidentIntensity • ((volume : Measure ℝ).prod retainedDelay))
        ((fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Set.Ioc a b) =
      incidentIntensity * retainedDelay Set.univ * volume (Set.Ioc a b) :=
  AppliedModelingLib.Probability.smul_volume_prod_preimage_add_Ioc
    incidentIntensity retainedDelay a b

end

end LBG24SpatialUnderreporting
