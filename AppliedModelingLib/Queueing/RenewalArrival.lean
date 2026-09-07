import AppliedModelingLib.Foundations.Probability.IidSequence

/-!
# Deterministic renewal-arrival clocks

This module provides the pathwise calendar for a renewal arrival stream.  The
arrival at index zero occurs at time zero; `renewalArrivalCount` counts the
strictly positive arrival epochs completed by a given time.  No distributional
or stationarity assertion is built into this deterministic interface.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The epoch of the arrival with a given index, when arrival zero is placed
at time zero and `gaps i` is the interval from arrival `i` to arrival
`i + 1`. -/
def renewalArrivalEpoch (gaps : ℕ → ℝ) (index : ℕ) : ℝ :=
  ∑ i ∈ Finset.range index, gaps i

@[simp]
theorem renewalArrivalEpoch_zero (gaps : ℕ → ℝ) :
    renewalArrivalEpoch gaps 0 = 0 := by
  simp [renewalArrivalEpoch]

/-- One renewal epoch is obtained from its predecessor by adding the preceding
interarrival gap. -/
theorem renewalArrivalEpoch_succ (gaps : ℕ → ℝ) (index : ℕ) :
    renewalArrivalEpoch gaps (index + 1) =
      renewalArrivalEpoch gaps index + gaps index := by
  simp [renewalArrivalEpoch, Finset.sum_range_succ]

/-- Nonnegative interarrival gaps make the renewal epochs monotone. -/
theorem monotone_renewalArrivalEpoch {gaps : ℕ → ℝ}
    (hnonnegative : ∀ index : ℕ, 0 ≤ gaps index) :
    Monotone (renewalArrivalEpoch gaps) := by
  intro first second hfirstsecond
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr hfirstsecond)
  intro index _ _
  exact hnonnegative index

/-- Every fixed renewal epoch is a measurable function of the full gap path. -/
theorem measurable_renewalArrivalEpoch (index : ℕ) :
    Measurable (fun gaps : ℕ → ℝ => renewalArrivalEpoch gaps index) := by
  exact (Finset.range index).measurable_sum fun i _ =>
    (measurable_pi_apply i : Measurable (fun gaps : ℕ → ℝ => gaps i))

/-- A renewal path is nonexplosive when its successive epochs eventually
exceed every finite real time. -/
def IsNonexplosiveRenewalArrivalPath (gaps : ℕ → ℝ) : Prop :=
  Tendsto (renewalArrivalEpoch gaps) atTop atTop

/-- If nonnegative gaps exceed a fixed positive threshold infinitely often,
their renewal epochs diverge to infinity. -/
theorem isNonexplosiveRenewalArrivalPath_of_frequently_le
    {gaps : ℕ → ℝ} {threshold : ℝ}
    (hnonnegative : ∀ index : ℕ, 0 ≤ gaps index)
    (hthreshold : 0 < threshold)
    (hfrequently : ∃ᶠ index : ℕ in atTop, threshold ≤ gaps index) :
    IsNonexplosiveRenewalArrivalPath gaps := by
  apply tendsto_atTop.2
  intro time
  obtain ⟨count, hcount⟩ := exists_nat_ge (time / threshold)
  have htime : time ≤ (count : ℝ) * threshold :=
    (div_le_iff₀ hthreshold).mp hcount
  have hreach : ∀ count : ℕ, ∃ index : ℕ,
      (count : ℝ) * threshold ≤ renewalArrivalEpoch gaps index := by
    intro count
    induction count with
    | zero => exact ⟨0, by simp⟩
    | succ count ih =>
      obtain ⟨index, hindex⟩ := ih
      obtain ⟨next, hindexnext, hnext⟩ := frequently_atTop.1 hfrequently index
      refine ⟨next + 1, ?_⟩
      calc
        ((count + 1 : ℕ) : ℝ) * threshold = (count : ℝ) * threshold + threshold := by
          push_cast
          ring
        _ ≤ renewalArrivalEpoch gaps next + gaps next := by
          exact add_le_add
            (hindex.trans (monotone_renewalArrivalEpoch hnonnegative hindexnext)) hnext
        _ = renewalArrivalEpoch gaps (next + 1) :=
          (renewalArrivalEpoch_succ gaps next).symm
  obtain ⟨index, hindex⟩ := hreach count
  filter_upwards [eventually_atTop.2 ⟨index, fun larger hlarger =>
    monotone_renewalArrivalEpoch hnonnegative hlarger⟩] with larger hlarger
  exact htime.trans (hindex.trans hlarger)

/-- A canonical iid renewal stream is almost surely nonexplosive when its
gaps are nonnegative almost surely and every gap has positive probability of
exceeding one fixed positive threshold. -/
theorem ae_isNonexplosiveRenewalArrivalPath_iidSequenceSample
    (law : Measure ℝ) [IsProbabilityMeasure law] {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hnonnegative : ∀ᵐ value ∂law, 0 ≤ value)
    (hevent_pos : 0 < law (Set.Ioi threshold)) :
    ∀ᵐ gaps ∂iidSequenceMeasure law,
      IsNonexplosiveRenewalArrivalPath
        (fun index => iidSequenceSample index gaps) := by
  let μ : Measure (ℕ → ℝ) := iidSequenceMeasure law
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using iidSequenceMeasure_isProbabilityMeasure law
  let event : ℕ → Set (ℕ → ℝ) := fun index =>
    (iidSequenceSample index) ⁻¹' Set.Ioi threshold
  have hnonnegative_sample : ∀ᵐ gaps ∂μ, ∀ index : ℕ,
      0 ≤ iidSequenceSample index gaps := by
    rw [ae_all_iff]
    intro index
    have hmeas : Measurable (fun value : ℝ => 0 ≤ value) := by fun_prop
    have hlaw := (iidSequenceSample_measurePreserving law index).hasLaw
    exact (hlaw.ae_iff hmeas).2 hnonnegative
  have hevent_measurable : ∀ index : ℕ, MeasurableSet (event index) := by
    intro index
    exact measurableSet_Ioi.preimage (measurable_iidSequenceSample index)
  have hevent_independent : iIndepSet event μ := by
    rw [iIndepSet_iff_meas_biInter hevent_measurable]
    intro indexes
    simpa only [event] using
      (iidSequenceSample_iIndepFun law).measure_inter_preimage_eq_mul indexes
        (sets := fun _ => Set.Ioi threshold) (fun _ _ => measurableSet_Ioi)
  have hevent_measure : ∀ index : ℕ, μ (event index) = law (Set.Ioi threshold) := by
    intro index
    calc
      μ (event index) = μ ((iidSequenceSample index) ⁻¹' Set.Ioi threshold) := rfl
      _ = Measure.map (iidSequenceSample index) μ (Set.Ioi threshold) := by
        rw [Measure.map_apply_of_aemeasurable
          (measurable_iidSequenceSample index).aemeasurable measurableSet_Ioi]
      _ = law (Set.Ioi threshold) := by
        simpa [μ] using congrArg (fun measure => measure (Set.Ioi threshold))
          (iidSequenceSample_law law index)
  have htsum : (∑' index : ℕ, μ (event index)) = ∞ := by
    simp_rw [hevent_measure]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt hevent_pos)
  have hlimsup : μ (limsup event atTop) = 1 :=
    measure_limsup_eq_one hevent_measurable hevent_independent htsum
  have hmem_limsup : ∀ᵐ gaps ∂μ, gaps ∈ limsup event atTop := by
    rw [ae_iff]
    change μ ((limsup event atTop)ᶜ) = 0
    rw [measure_compl (MeasurableSet.measurableSet_limsup hevent_measurable)
      (by rw [hlimsup]; simp), hlimsup]
    rw [IsProbabilityMeasure.measure_univ]
    exact tsub_self 1
  filter_upwards [hnonnegative_sample, hmem_limsup] with gaps hnonnegative_gaps hlimsup_gaps
  apply isNonexplosiveRenewalArrivalPath_of_frequently_le hnonnegative_gaps hthreshold
  exact (mem_limsup_iff_frequently_mem.mp hlimsup_gaps).mono fun _ hgap => le_of_lt hgap

/-- A nonexplosive renewal path has a future positive-index arrival after any
specified finite time. -/
theorem exists_renewalArrivalEpoch_succ_gt
    {gaps : ℕ → ℝ} (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps)
    (time : ℝ) :
    ∃ index : ℕ, time < renewalArrivalEpoch gaps (index + 1) := by
  obtain ⟨index, hindex⟩ :=
    Filter.eventually_atTop.mp (hnonexplosive.eventually_gt_atTop time)
  exact ⟨index, hindex (index + 1) (Nat.le_succ _)⟩

/-- Number of strictly positive renewal arrivals completed by `time`.  On a
nonexplosive path it is the first positive-index epoch after `time`; the
fallback on an explosive path is deliberately harmless. -/
noncomputable def renewalArrivalCount (time : ℝ) (gaps : ℕ → ℝ) : ℕ := by
  classical
  exact if h : ∃ index : ℕ, time < renewalArrivalEpoch gaps (index + 1) then
    Nat.find h else 0

/-- A total least-index predicate used to expose the measurability of the
completed renewal count, including its zero fallback on explosive paths. -/
private def renewalArrivalCountSearchPredicate (time : ℝ)
    (gaps : ℕ → ℝ) (index : ℕ) : Prop :=
  time < renewalArrivalEpoch gaps (index + 1) ∨
    (index = 0 ∧ ∀ candidate : ℕ,
      ¬ time < renewalArrivalEpoch gaps (candidate + 1))

private theorem measurableSet_renewalArrivalCountSearchPredicate
    (time : ℝ) (index : ℕ) :
    MeasurableSet {gaps : ℕ → ℝ |
      renewalArrivalCountSearchPredicate time gaps index} := by
  have hfirst : MeasurableSet {gaps : ℕ → ℝ |
      time < renewalArrivalEpoch gaps (index + 1)} :=
    measurableSet_lt measurable_const (measurable_renewalArrivalEpoch (index + 1))
  have hnone : MeasurableSet {gaps : ℕ → ℝ |
      ∀ candidate : ℕ, ¬ time < renewalArrivalEpoch gaps (candidate + 1)} := by
    rw [show {gaps : ℕ → ℝ | ∀ candidate : ℕ,
        ¬ time < renewalArrivalEpoch gaps (candidate + 1)} =
        ⋂ candidate : ℕ, {gaps : ℕ → ℝ |
          ¬ time < renewalArrivalEpoch gaps (candidate + 1)} by
      ext gaps
      simp]
    apply MeasurableSet.iInter
    intro candidate
    exact (measurableSet_lt measurable_const
      (measurable_renewalArrivalEpoch (candidate + 1))).compl
  by_cases hindex : index = 0
  · subst index
    rw [show {gaps : ℕ → ℝ | renewalArrivalCountSearchPredicate time gaps 0} =
        {gaps : ℕ → ℝ | time < renewalArrivalEpoch gaps 1} ∪
          {gaps : ℕ → ℝ | ∀ candidate : ℕ,
            ¬ time < renewalArrivalEpoch gaps (candidate + 1)} by
      ext gaps
      simp [renewalArrivalCountSearchPredicate]]
    exact hfirst.union hnone
  · rw [show {gaps : ℕ → ℝ | renewalArrivalCountSearchPredicate time gaps index} =
        {gaps : ℕ → ℝ | time < renewalArrivalEpoch gaps (index + 1)} by
      ext gaps
      simp [renewalArrivalCountSearchPredicate, hindex]]
    exact hfirst

private theorem renewalArrivalCountSearchPredicate_exists
    (time : ℝ) (gaps : ℕ → ℝ) :
    ∃ index : ℕ, renewalArrivalCountSearchPredicate time gaps index := by
  by_cases hfuture : ∃ index : ℕ, time < renewalArrivalEpoch gaps (index + 1)
  · obtain ⟨index, hindex⟩ := hfuture
    exact ⟨index, Or.inl hindex⟩
  · exact ⟨0, Or.inr ⟨rfl, by simpa using hfuture⟩⟩

private noncomputable def measurableRenewalArrivalCount (time : ℝ) : (ℕ → ℝ) → ℕ := by
  classical
  exact fun gaps => Nat.find (renewalArrivalCountSearchPredicate_exists time gaps)

private theorem measurable_measurableRenewalArrivalCount (time : ℝ) :
    Measurable (measurableRenewalArrivalCount time) := by
  classical
  unfold measurableRenewalArrivalCount
  apply measurable_find
  intro index
  exact measurableSet_renewalArrivalCountSearchPredicate time index

private theorem renewalArrivalCount_eq_measurableRenewalArrivalCount
    (time : ℝ) (gaps : ℕ → ℝ) :
    renewalArrivalCount time gaps = measurableRenewalArrivalCount time gaps := by
  classical
  unfold renewalArrivalCount measurableRenewalArrivalCount
  split_ifs with hfuture
  · apply le_antisymm
    · apply Nat.find_min' hfuture
      rcases Nat.find_spec (renewalArrivalCountSearchPredicate_exists time gaps) with hpred | hpred
      · exact hpred
      · obtain ⟨index, hindex⟩ := hfuture
        exact (hpred.2 index hindex).elim
    · apply Nat.find_min' (renewalArrivalCountSearchPredicate_exists time gaps)
      exact Or.inl (Nat.find_spec hfuture)
  · simp only [not_exists] at hfuture
    symm
    apply (Nat.find_eq_zero (renewalArrivalCountSearchPredicate_exists time gaps)).mpr
    exact Or.inr ⟨rfl, hfuture⟩

/-- The completed renewal count is measurable in the full gap sequence. -/
theorem measurable_renewalArrivalCount (time : ℝ) :
    Measurable (renewalArrivalCount time) := by
  rw [show renewalArrivalCount time = measurableRenewalArrivalCount time by
    funext gaps
    exact renewalArrivalCount_eq_measurableRenewalArrivalCount time gaps]
  exact measurable_measurableRenewalArrivalCount time

theorem renewalArrivalCount_eq_find
    (time : ℝ) (gaps : ℕ → ℝ)
    (hfuture : ∃ index : ℕ, time < renewalArrivalEpoch gaps (index + 1)) :
    renewalArrivalCount time gaps = Nat.find hfuture := by
  classical
  simp [renewalArrivalCount, hfuture]

/-- The next positive renewal epoch is strictly after the present time on a
nonexplosive renewal path. -/
theorem lt_renewalArrivalEpoch_succ_renewalArrivalCount
    {gaps : ℕ → ℝ} (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps)
    (time : ℝ) :
    time < renewalArrivalEpoch gaps (renewalArrivalCount time gaps + 1) := by
  obtain hfuture := exists_renewalArrivalEpoch_succ_gt hnonexplosive time
  rw [renewalArrivalCount_eq_find time gaps hfuture]
  exact Nat.find_spec hfuture

/-- An index below the renewal count has already arrived by the specified
time. -/
theorem renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount
    {gaps : ℕ → ℝ} (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps)
    {time : ℝ} {index : ℕ}
    (hindex : index < renewalArrivalCount time gaps) :
    renewalArrivalEpoch gaps (index + 1) ≤ time := by
  obtain hfuture := exists_renewalArrivalEpoch_succ_gt hnonexplosive time
  rw [renewalArrivalCount_eq_find time gaps hfuture] at hindex
  exact le_of_not_gt (Nat.find_min hfuture hindex)

/-- The completed-arrival count has the exact threshold characterization on a
nonexplosive renewal path. -/
theorem lt_renewalArrivalCount_iff_renewalArrivalEpoch_succ_le
    {gaps : ℕ → ℝ} (hnonnegative : ∀ index : ℕ, 0 ≤ gaps index)
    (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps)
    (time : ℝ) (index : ℕ) :
    index < renewalArrivalCount time gaps ↔
      renewalArrivalEpoch gaps (index + 1) ≤ time := by
  constructor
  · exact renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount hnonexplosive
  · intro hle
    by_contra hnot
    have hcount_le : renewalArrivalCount time gaps ≤ index := Nat.le_of_not_gt hnot
    have hnext := lt_renewalArrivalEpoch_succ_renewalArrivalCount hnonexplosive time
    have hepoch_le : renewalArrivalEpoch gaps (renewalArrivalCount time gaps + 1) ≤
        renewalArrivalEpoch gaps (index + 1) := by
      exact monotone_renewalArrivalEpoch hnonnegative (Nat.succ_le_succ hcount_le)
    exact (not_lt_of_ge (hepoch_le.trans hle)) hnext

/-- Strictly positive gaps make successive renewal epochs strictly increasing. -/
theorem renewalArrivalEpoch_lt_succ {gaps : ℕ → ℝ}
    (hpositive : ∀ index : ℕ, 0 < gaps index) (index : ℕ) :
    renewalArrivalEpoch gaps index < renewalArrivalEpoch gaps (index + 1) := by
  rw [renewalArrivalEpoch_succ]
  exact lt_add_of_pos_right _ (hpositive index)

/-- At a renewal epoch, the completed-arrival count is exactly that epoch's
index. -/
theorem renewalArrivalCount_epoch {gaps : ℕ → ℝ}
    (hpositive : ∀ index : ℕ, 0 < gaps index)
    (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps) (index : ℕ) :
    renewalArrivalCount (renewalArrivalEpoch gaps index) gaps = index := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hgreater
    have hafter := renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount
      hnonexplosive hgreater
    exact (not_le_of_gt (renewalArrivalEpoch_lt_succ hpositive index)) hafter
  · cases index with
    | zero => exact Nat.zero_le _
    | succ index =>
      exact Nat.succ_le_iff.mpr
        ((lt_renewalArrivalCount_iff_renewalArrivalEpoch_succ_le
          (fun j => (hpositive j).le) hnonexplosive
          (renewalArrivalEpoch gaps (index + 1)) index).mpr le_rfl)

/-- Between consecutive renewal epochs, the completed-arrival count is the
index of the preceding epoch. -/
theorem renewalArrivalCount_eq_of_epoch_le_lt_next
    {gaps : ℕ → ℝ} (hpositive : ∀ index : ℕ, 0 < gaps index)
    (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps) {index : ℕ} {time : ℝ}
    (hstart : renewalArrivalEpoch gaps index ≤ time)
    (hend : time < renewalArrivalEpoch gaps (index + 1)) :
    renewalArrivalCount time gaps = index := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hgreater
    have hnext_le := renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount
      hnonexplosive hgreater
    exact (not_le_of_gt hend) hnext_le
  · cases index with
    | zero => exact Nat.zero_le _
    | succ index =>
      exact Nat.succ_le_iff.mpr
        ((lt_renewalArrivalCount_iff_renewalArrivalEpoch_succ_le
          (fun j => (hpositive j).le) hnonexplosive time index).mpr (by
            simpa [Nat.add_comm] using hstart))

/-- The renewal epoch indexed by the current completed-arrival count has
already occurred at any nonnegative time on a nonexplosive path. -/
theorem renewalArrivalEpoch_renewalArrivalCount_le {gaps : ℕ → ℝ}
    (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps) {time : ℝ}
    (htime : 0 ≤ time) :
    renewalArrivalEpoch gaps (renewalArrivalCount time gaps) ≤ time := by
  by_cases hcount_zero : renewalArrivalCount time gaps = 0
  · rw [hcount_zero]
    simpa [renewalArrivalEpoch] using htime
  · have hcount_pos : 0 < renewalArrivalCount time gaps := Nat.pos_of_ne_zero hcount_zero
    have hpred_lt : renewalArrivalCount time gaps - 1 < renewalArrivalCount time gaps :=
      Nat.sub_lt hcount_pos (by omega)
    have harrival := renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount
      hnonexplosive hpred_lt
    have hindex : renewalArrivalCount time gaps - 1 + 1 = renewalArrivalCount time gaps := by
      omega
    simpa [hindex] using harrival

/-- Completed-renewal counts are monotone in physical time on a nonexplosive
path. -/
theorem monotone_renewalArrivalCount
    {gaps : ℕ → ℝ} (hnonexplosive : IsNonexplosiveRenewalArrivalPath gaps) :
    Monotone (fun time => renewalArrivalCount time gaps) := by
  intro earlier later hearlier_later
  by_contra hnot
  have hcount : renewalArrivalCount later gaps < renewalArrivalCount earlier gaps :=
    Nat.lt_of_not_ge hnot
  have hbefore : renewalArrivalEpoch gaps (renewalArrivalCount later gaps + 1) ≤ earlier :=
    renewalArrivalEpoch_succ_le_of_lt_renewalArrivalCount hnonexplosive hcount
  have hafter := lt_renewalArrivalEpoch_succ_renewalArrivalCount hnonexplosive later
  exact (not_lt_of_ge (hbefore.trans hearlier_later)) hafter

end

end Queueing
end Probability
end AppliedModelingLib
