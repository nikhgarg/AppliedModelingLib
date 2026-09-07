import AppliedModelingLib.Queueing.ManyServerMarkedCanonicalTrajectory
import AppliedModelingLib.Queueing.ManyServerMarkedStateTrajectory
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalOccupation
import AppliedModelingLib.Foundations.Probability.IidExternalWeightedMartingale
import AppliedModelingLib.Foundations.Probability.ExponentialMoments

/-!
# Physical-time idle-occupation decomposition for many-server queues

This module gives the exact pathwise conversion from an embedded idle-fraction
prefix to physical-time idle occupation under an independent renewal clock.
The centered clock reward and its final incomplete interarrival interval remain
explicit, so later probabilistic bounds do not hide a time-change error.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter MeasureTheory ProbabilityTheory Preorder Filtration
open scoped ENNReal NNReal

noncomputable section

/-- The completed-gap centered renewal reward of the embedded idle fraction. -/
noncomputable def manyServerMarkedCanonicalIdleFractionClockCenteredReward
    (servers : ℕ) (rate time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ :=
  ∑ index ∈ Finset.range (PoissonProcess.canonicalRenewalCount time value.2),
    manyServerMarkedStateIdleFractionAt servers index value.1 *
      (1 - rate * PoissonProcess.interarrival index value.2)

/-- The centered renewal-clock reward and terminal partial-gap correction for
the idle fraction of a marked many-server trajectory. -/
noncomputable def manyServerMarkedCanonicalIdleFractionClockResidual
    (servers : ℕ) (rate time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ :=
  manyServerMarkedCanonicalIdleFractionClockCenteredReward servers rate time value -
    rate * manyServerMarkedStateIdleFractionAt servers
      (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
      (time - PoissonProcess.arrivalPrefix
      (PoissonProcess.canonicalRenewalCount time value.2) value.2)

/-- The idle fraction retained strictly before a lower-barrier exit and capped
by the deterministic idle fraction at that barrier.  The cap makes the
coefficient globally bounded while agreeing with the literal coefficient on
valid paths before exit. -/
noncomputable def manyServerMarkedStateCappedLowerIdleFraction
    (servers lowerThreshold index : ℕ) (path : ℕ → ℕ × Bool) : ℝ :=
  (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
    (fun path => min (manyServerMarkedStateIdleFractionAt servers index path)
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) path

/-- The capped lower-barrier idle coefficient is Borel measurable. -/
theorem measurable_manyServerMarkedStateCappedLowerIdleFraction
    (servers lowerThreshold index : ℕ) :
    Measurable (manyServerMarkedStateCappedLowerIdleFraction
      servers lowerThreshold index) := by
  have hactive : MeasurableSet
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index) := by
    exact (piLE.le index) _
      (manyServerMarkedStateLowerExitActiveSet_measurableSet lowerThreshold index)
  have hidle : Measurable (manyServerMarkedStateIdleFractionAt servers index) := by
    unfold manyServerMarkedStateIdleFractionAt
    exact measurable_const.sub
      ((measurable_of_countable fun state : ℕ × Bool =>
        (manyServerBusyFraction servers state.1 : ℝ)).comp
        (measurable_pi_apply index))
  unfold manyServerMarkedStateCappedLowerIdleFraction
  exact (hidle.min measurable_const).indicator hactive

/-- On a valid marked trajectory, the capped coefficient is the literal idle
fraction before the lower exit and zero afterwards. -/
theorem manyServerMarkedStateCappedLowerIdleFraction_eq_indicator_idleFraction
    (servers lowerThreshold index : ℕ) (path : ℕ → ℕ × Bool)
    (hstep : ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (path step) (path (step + 1))) :
    manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold index path =
      (manyServerMarkedStateLowerExitActiveSet lowerThreshold index).indicator
        (manyServerMarkedStateIdleFractionAt servers index) path := by
  by_cases hactive : path ∈ manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · have hbefore : (index : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path := by
      simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hactive
    have hidle_le : manyServerMarkedStateIdleFractionAt servers index path ≤
        1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
      simpa [manyServerMarkedStateIdleFractionAt] using
        one_sub_manyServerBusyFraction_le_of_lt_lowerExitTime
          servers lowerThreshold index path hstep hbefore
    unfold manyServerMarkedStateCappedLowerIdleFraction
    rw [Set.indicator_of_mem hactive, Set.indicator_of_mem hactive, min_eq_left hidle_le]
  · unfold manyServerMarkedStateCappedLowerIdleFraction
    rw [Set.indicator_of_notMem hactive, Set.indicator_of_notMem hactive]

/-- The capped lower-barrier idle coefficient has the deterministic bound
required by externally weighted IID martingale estimates. -/
theorem abs_manyServerMarkedStateCappedLowerIdleFraction_le
    (servers lowerThreshold index : ℕ) (path : ℕ → ℕ × Bool)
    (hservers : 0 < servers) :
    |manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold index path| ≤
      1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
  have hthreshold_nonneg : 0 ≤ 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  by_cases hactive : path ∈ manyServerMarkedStateLowerExitActiveSet lowerThreshold index
  · have hidle_nonneg :=
      (manyServerMarkedStateIdleFractionAt_nonneg_le_one servers index path hservers).1
    unfold manyServerMarkedStateCappedLowerIdleFraction
    rw [Set.indicator_of_mem hactive, abs_of_nonneg
      (le_min hidle_nonneg hthreshold_nonneg)]
    exact min_le_right _ _
  · unfold manyServerMarkedStateCappedLowerIdleFraction
    rw [Set.indicator_of_notMem hactive]
    simpa using hthreshold_nonneg

/-- Doob's estimate for the shifted part of the renewal-clock reward, stopped
at a lower barrier and expressed with globally capped idle coefficients. -/
theorem ennreal_mul_measure_manyServerMarkedCappedLowerIdleClockRewardMaximum_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers lowerThreshold : ℕ) {rate : ℝ} (hservers : 0 < servers) (hrate : 0 < rate)
    (cap : ℕ) (threshold : ℝ≥0) :
    threshold * trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate) {value |
      (threshold : ℝ) ≤ (Finset.range (cap + 1)).sup'
        Finset.nonempty_range_add_one
        (fun steps => (∑ index ∈ Finset.range steps,
          manyServerMarkedStateCappedLowerIdleFraction
            servers lowerThreshold (index + 1) value.1 *
            (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)} ≤
      ENNReal.ofReal ((cap : ℝ) *
        (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) := by
  let weight : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold (index + 1) path
  let reward : ℝ → ℝ := fun gap => 1 - rate * gap
  let bound : ℝ := 1 - (manyServerBusyFraction servers lowerThreshold : ℝ)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  have hweight : ∀ index, Measurable (weight index) := by
    intro index
    exact measurable_manyServerMarkedStateCappedLowerIdleFraction
      servers lowerThreshold (index + 1)
  have hreward : Measurable reward := measurable_const.sub (measurable_const.mul measurable_id)
  have hweight_bound : ∀ index path, ‖weight index path‖ ≤ bound := by
    intro index path
    simpa [weight, bound, Real.norm_eq_abs] using
      abs_manyServerMarkedStateCappedLowerIdleFraction_le
        servers lowerThreshold (index + 1) path hservers
  have hreward_sq_int : Integrable (fun gap => reward gap ^ 2)
      (ProbabilityTheory.expMeasure rate) := by
    simpa [reward] using integrable_sq_one_sub_mul_id_expMeasure hrate
  have hmean : ∫ gap, reward gap ∂ProbabilityTheory.expMeasure rate = 0 := by
    simpa [reward] using integral_one_sub_mul_id_expMeasure hrate
  have hvariance : (∫ gap, reward gap ^ 2 ∂ProbabilityTheory.expMeasure rate) ≤ 1 := by
    rw [show (∫ gap, reward gap ^ 2 ∂ProbabilityTheory.expMeasure rate) = 1 by
      simpa [reward] using integral_sq_one_sub_mul_id_expMeasure hrate]
  have hmax := IIDStream.ennreal_mul_measure_externalWeightedShiftedMaximumSq_le
    trajectory (ProbabilityTheory.expMeasure rate) weight reward hweight hreward bound 1
      hbound_nonneg hweight_bound hreward_sq_int hmean hvariance cap threshold
  simpa [weight, reward, bound, IIDStream.measure,
    IIDStream.externalWeightedShiftedPartialSum, IIDStream.coordinate,
    PoissonProcess.exponentialInterarrivalMeasure, PoissonProcess.interarrival] using hmax

/-- Real-valued form of the capped lower-idle clock-reward maximal estimate. -/
theorem real_mul_measure_manyServerMarkedCappedLowerIdleClockRewardMaximum_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers lowerThreshold : ℕ) {rate : ℝ} (hservers : 0 < servers) (hrate : 0 < rate)
    (cap : ℕ) (threshold : ℝ≥0) :
    (threshold : ℝ) *
      (trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate)).real {value |
        (threshold : ℝ) ≤ (Finset.range (cap + 1)).sup'
          Finset.nonempty_range_add_one
          (fun steps => (∑ index ∈ Finset.range steps,
            manyServerMarkedStateCappedLowerIdleFraction
              servers lowerThreshold (index + 1) value.1 *
              (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)} ≤
        (cap : ℝ) *
          (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate)
  let event : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (threshold : ℝ) ≤ (Finset.range (cap + 1)).sup'
      Finset.nonempty_range_add_one
      (fun steps => (∑ index ∈ Finset.range steps,
        manyServerMarkedStateCappedLowerIdleFraction
          servers lowerThreshold (index + 1) value.1 *
          (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)}
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hbase := ennreal_mul_measure_manyServerMarkedCappedLowerIdleClockRewardMaximum_le
    trajectory servers lowerThreshold hservers hrate cap threshold
  have hdelta_nonneg : 0 ≤
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
    positivity
  have hbase_toReal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
    ENNReal.ofReal_ne_top).mpr hbase
  change (threshold : ℝ) * source.real event ≤ _
  simpa [source, event, Measure.real, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal hdelta_nonneg] using hbase_toReal

/-- A square-event estimate for the initial capped lower-idle renewal reward. -/
theorem ennreal_mul_measure_manyServerMarkedCappedLowerIdleClockInitialSq_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers lowerThreshold : ℕ) {rate : ℝ} (hservers : 0 < servers) (hrate : 0 < rate)
    (threshold : ℝ≥0) :
    threshold * trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate) {value |
      (threshold : ℝ) ≤
        (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
          (1 - rate * PoissonProcess.interarrival 0 value.2)) ^ 2} ≤
      ENNReal.ofReal ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) := by
  let weight : (ℕ → ℕ × Bool) → ℝ :=
    manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0
  let reward : ℝ → ℝ := fun gap => 1 - rate * gap
  let bound : ℝ := 1 - (manyServerBusyFraction servers lowerThreshold : ℝ)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  have hweight : Measurable weight := by
    simpa [weight] using
      measurable_manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0
  have hreward : Measurable reward := by
    simpa [reward] using (measurable_const.sub (measurable_id.const_mul rate))
  have hweight_bound : ∀ path, ‖weight path‖ ≤ bound := by
    intro path
    simpa [weight, bound, Real.norm_eq_abs] using
      abs_manyServerMarkedStateCappedLowerIdleFraction_le
        servers lowerThreshold 0 path hservers
  have hreward_sq_int : Integrable (fun gap => reward gap ^ 2)
      (ProbabilityTheory.expMeasure rate) := by
    simpa [reward] using integrable_sq_one_sub_mul_id_expMeasure hrate
  have hvariance : (∫ gap, reward gap ^ 2 ∂ProbabilityTheory.expMeasure rate) ≤ 1 := by
    rw [show (∫ gap, reward gap ^ 2 ∂ProbabilityTheory.expMeasure rate) = 1 by
      simpa [reward] using integral_sq_one_sub_mul_id_expMeasure hrate]
  have hinitial := IIDStream.ennreal_mul_measure_externalWeightedCoordinateSqEvent_le
    trajectory (ProbabilityTheory.expMeasure rate) weight reward 0 hweight hreward bound 1
      hbound_nonneg hweight_bound hreward_sq_int hvariance threshold
  simpa [weight, reward, bound, IIDStream.measure,
    IIDStream.externalWeightedCoordinateReward, IIDStream.coordinate,
    PoissonProcess.exponentialInterarrivalMeasure, PoissonProcess.interarrival] using hinitial

/-- Real-valued form of the initial capped lower-idle renewal-reward estimate. -/
theorem real_mul_measure_manyServerMarkedCappedLowerIdleClockInitialSq_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers lowerThreshold : ℕ) {rate : ℝ} (hservers : 0 < servers) (hrate : 0 < rate)
    (threshold : ℝ≥0) :
    (threshold : ℝ) *
      (trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate)).real {value |
        (threshold : ℝ) ≤
          (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
            (1 - rate * PoissonProcess.interarrival 0 value.2)) ^ 2} ≤
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate)
  let event : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (threshold : ℝ) ≤
      (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
        (1 - rate * PoissonProcess.interarrival 0 value.2)) ^ 2}
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hbase := ennreal_mul_measure_manyServerMarkedCappedLowerIdleClockInitialSq_le
    trajectory servers lowerThreshold hservers hrate threshold
  have hdelta_nonneg : 0 ≤
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
    positivity
  have hbase_toReal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
    ENNReal.ofReal_ne_top).mpr hbase
  change (threshold : ℝ) * source.real event ≤ _
  simpa [source, event, Measure.real, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal hdelta_nonneg] using hbase_toReal

/-- Before a specified lower-barrier exit, the completed clock reward splits
into its initial interarrival contribution and the corresponding capped,
shifted IID partial sum. -/
theorem manyServerMarkedCanonicalIdleFractionClockCenteredReward_eq_cappedInitial_add_shifted
    (servers lowerThreshold : ℕ) (rate time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hstep : ∀ step : ℕ,
      ManyServerMarkedStateStepAllowed (value.1 step) (value.1 (step + 1)))
    (hcount_pos : 0 < PoissonProcess.canonicalRenewalCount time value.2)
    (hactive : ∀ index < PoissonProcess.canonicalRenewalCount time value.2,
      value.1 ∈ manyServerMarkedStateLowerExitActiveSet lowerThreshold index) :
    manyServerMarkedCanonicalIdleFractionClockCenteredReward servers rate time value =
      manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
          (1 - rate * PoissonProcess.interarrival 0 value.2) +
        ∑ index ∈ Finset.range
          (PoissonProcess.canonicalRenewalCount time value.2 - 1),
          manyServerMarkedStateCappedLowerIdleFraction
              servers lowerThreshold (index + 1) value.1 *
            (1 - rate * PoissonProcess.interarrival (index + 1) value.2) := by
  obtain ⟨steps, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount_pos)
  rw [hsteps]
  have hcapped : ∀ index < steps + 1,
      manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold index value.1 =
        manyServerMarkedStateIdleFractionAt servers index value.1 := by
    intro index hindex
    rw [manyServerMarkedStateCappedLowerIdleFraction_eq_indicator_idleFraction
      servers lowerThreshold index value.1 hstep]
    simp [Set.indicator_of_mem (hactive index (by simpa [hsteps] using hindex))]
  unfold manyServerMarkedCanonicalIdleFractionClockCenteredReward
  rw [hsteps, Finset.sum_range_succ']
  simp only [Nat.succ_sub_one]
  calc
    (∑ index ∈ Finset.range steps,
        manyServerMarkedStateIdleFractionAt servers (index + 1) value.1 *
          (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) +
        manyServerMarkedStateIdleFractionAt servers 0 value.1 *
          (1 - rate * PoissonProcess.interarrival 0 value.2) =
      manyServerMarkedStateIdleFractionAt servers 0 value.1 *
          (1 - rate * PoissonProcess.interarrival 0 value.2) +
        ∑ index ∈ Finset.range steps,
          manyServerMarkedStateIdleFractionAt servers (index + 1) value.1 *
            (1 - rate * PoissonProcess.interarrival (index + 1) value.2) := by ring
    _ = _ := by
      congr 1
      · rw [← hcapped 0 (by omega)]
      · apply Finset.sum_congr rfl
        intro index hindex
        rw [← hcapped (index + 1) (by
          exact Nat.succ_lt_succ (Finset.mem_range.mp hindex))]

/-- The renewal-clock residual is the completed-gap centered reward minus
the explicit incomplete-gap terminal correction. -/
theorem manyServerMarkedCanonicalIdleFractionClockResidual_eq_centeredReward_sub_terminal
    (servers : ℕ) (rate time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    manyServerMarkedCanonicalIdleFractionClockResidual servers rate time value =
      manyServerMarkedCanonicalIdleFractionClockCenteredReward servers rate time value -
        rate * manyServerMarkedStateIdleFractionAt servers
          (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
            (time - PoissonProcess.arrivalPrefix
            (PoissonProcess.canonicalRenewalCount time value.2) value.2) := rfl

/-- The terminal incomplete-gap part of the idle-occupation residual is
bounded by the complete interarrival gap that straddles the clock time. -/
theorem abs_manyServerMarkedCanonicalIdleFractionClock_terminal_le_rate_mul_interarrival
    (servers : ℕ) {rate time : ℝ}
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hservers : 0 < servers) (hrate : 0 < rate) (htime : 0 ≤ time)
    (hfuture : ∃ index : ℕ, time < PoissonProcess.arrivalTime index value.2) :
    |rate * manyServerMarkedStateIdleFractionAt servers
      (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
      (time - PoissonProcess.arrivalPrefix
        (PoissonProcess.canonicalRenewalCount time value.2) value.2)| ≤
      rate * PoissonProcess.interarrival
        (PoissonProcess.canonicalRenewalCount time value.2) value.2 := by
  let index := PoissonProcess.canonicalRenewalCount time value.2
  have hidle := manyServerMarkedStateIdleFractionAt_nonneg_le_one
    servers index value.1 hservers
  have helapsed_nonneg : 0 ≤
      time - PoissonProcess.arrivalPrefix index value.2 := by
    simpa [index] using
      PoissonProcess.zero_le_time_sub_arrivalPrefix_canonicalRenewalCount
        time value.2 htime hfuture
  have helapsed_lt :
      time - PoissonProcess.arrivalPrefix index value.2 <
        PoissonProcess.interarrival index value.2 := by
    simpa [index] using
      PoissonProcess.time_sub_arrivalPrefix_canonicalRenewalCount_lt_interarrival
        time value.2 hfuture
  have hproduct_nonneg : 0 ≤ rate *
      manyServerMarkedStateIdleFractionAt servers index value.1 *
      (time - PoissonProcess.arrivalPrefix index value.2) :=
    mul_nonneg (mul_nonneg hrate.le hidle.1) helapsed_nonneg
  rw [abs_of_nonneg hproduct_nonneg]
  calc
    rate * manyServerMarkedStateIdleFractionAt servers index value.1 *
        (time - PoissonProcess.arrivalPrefix index value.2) =
        rate * (manyServerMarkedStateIdleFractionAt servers index value.1 *
          (time - PoissonProcess.arrivalPrefix index value.2)) := by ring
    _ ≤ rate * (1 * (time - PoissonProcess.arrivalPrefix index value.2)) := by
      apply mul_le_mul_of_nonneg_left _ hrate.le
      exact mul_le_mul_of_nonneg_right hidle.2 helapsed_nonneg
    _ ≤ rate * (1 * PoissonProcess.interarrival index value.2) := by
      apply mul_le_mul_of_nonneg_left _ hrate.le
      simpa only [one_mul] using helapsed_lt.le
    _ = rate * PoissonProcess.interarrival index value.2 := by ring

/-- On a canonical exponential-clock full-measure event, a finite clock-count
cutoff and a uniform bound on its interarrivals control every terminal
incomplete-gap correction on the physical horizon. -/
theorem ae_forall_manyServerMarkedCanonicalIdleFractionClock_terminal_le_of_clockCount_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers : ℕ) {rate horizon z : ℝ} (cap : ℕ)
    (hservers : 0 < servers) (hrate : 0 < rate) :
    ∀ᵐ value ∂trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate),
      PoissonProcess.canonicalRenewalCount horizon value.2 ≤ cap →
        (∀ index ≤ cap, rate * PoissonProcess.interarrival index value.2 ≤ z) →
          ∀ time ∈ Set.Icc (0 : ℝ) horizon,
            |rate * manyServerMarkedStateIdleFractionAt servers
              (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
              (time - PoissonProcess.arrivalPrefix
                (PoissonProcess.canonicalRenewalCount time value.2) value.2)| ≤ z := by
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hdivergence : ∀ᵐ gap ∂gaps,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gap) atTop atTop := by
    simpa [gaps] using PoissonProcess.ae_arrivalTime_tendsto_atTop hrate
  have hlift : ∀ᵐ value ∂trajectory.prod gaps,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop := by
    refine ae_of_ae_map (μ := trajectory.prod gaps) (f := Prod.snd)
      (p := fun gap => Tendsto
        (fun index : ℕ => PoissonProcess.arrivalTime index gap) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hdivergence
  change ∀ᵐ value ∂trajectory.prod gaps, _
  filter_upwards [hlift] with value hdivergence
  intro hcount hgap time htime
  have hfuture : ∃ index : ℕ,
      time < PoissonProcess.arrivalTime index value.2 :=
    (hdivergence.eventually_gt_atTop time).exists
  have htime_count : PoissonProcess.canonicalRenewalCount time value.2 ≤
      PoissonProcess.canonicalRenewalCount horizon value.2 :=
    PoissonProcess.canonicalRenewalCount_monotone_of_tendsto value.2 hdivergence htime.2
  have hterminal :=
    abs_manyServerMarkedCanonicalIdleFractionClock_terminal_le_rate_mul_interarrival
      servers value hservers hrate htime.1 hfuture
  exact hterminal.trans (hgap _ (htime_count.trans hcount))

/-- A finite-horizon probability bound for the incomplete-gap terminal part
of the renewal-clock residual.  The two terms are respectively a clock-count
overflow and a finite union of rate-scaled exponential interarrival tails. -/
theorem real_measure_manyServerMarkedCanonicalIdleFractionClock_terminal_excursion_le
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers : ℕ) {rate horizon z : ℝ} (cap : ℕ)
    (hservers : 0 < servers) (hrate : 0 < rate)
    (hhorizon : 0 ≤ horizon) (hz : 0 ≤ z) :
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value | ∃ time ∈ Set.Icc (0 : ℝ) horizon,
      z < |rate * manyServerMarkedStateIdleFractionAt servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
        (time - PoissonProcess.arrivalPrefix
          (PoissonProcess.canonicalRenewalCount time value.2) value.2)|} ≤
      (rate * horizon) / (cap + 1 : ℝ) +
        (cap + 1 : ℝ) * Real.exp (-z) := by
  dsimp only
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let terminalEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ∃ time ∈ Set.Icc (0 : ℝ) horizon,
      z < |rate * manyServerMarkedStateIdleFractionAt servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
        (time - PoissonProcess.arrivalPrefix
          (PoissonProcess.canonicalRenewalCount time value.2) value.2)|}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (cap + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let gapEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ∃ index ≤ cap, z < rate * PoissonProcess.interarrival index value.2}
  let exceptionalEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ¬ (PoissonProcess.canonicalRenewalCount horizon value.2 ≤ cap →
      (∀ index ≤ cap, rate * PoissonProcess.interarrival index value.2 ≤ z) →
        ∀ time ∈ Set.Icc (0 : ℝ) horizon,
          |rate * manyServerMarkedStateIdleFractionAt servers
            (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
            (time - PoissonProcess.arrivalPrefix
              (PoissonProcess.canonicalRenewalCount time value.2) value.2)| ≤ z)}
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hgood :=
    ae_forall_manyServerMarkedCanonicalIdleFractionClock_terminal_le_of_clockCount_le
      trajectory servers (horizon := horizon) (z := z) cap hservers hrate
  have hnull : source exceptionalEvent = 0 := by
    exact ae_iff.mp (by simpa [source, exceptionalEvent] using hgood)
  have hnull_real : source.real exceptionalEvent = 0 := by
    simp only [Measure.real, hnull, ENNReal.toReal_zero]
  have hsubset : terminalEvent ⊆ (clockEvent ∪ gapEvent) ∪ exceptionalEvent := by
    intro value hvalue
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl (Or.inl hclock)
    by_cases hgap : value ∈ gapEvent
    · exact Or.inl (Or.inr hgap)
    right
    change ¬ (PoissonProcess.canonicalRenewalCount horizon value.2 ≤ cap →
      (∀ index ≤ cap, rate * PoissonProcess.interarrival index value.2 ≤ z) →
        ∀ time ∈ Set.Icc (0 : ℝ) horizon,
          |rate * manyServerMarkedStateIdleFractionAt servers
            (PoissonProcess.canonicalRenewalCount time value.2) value.1 *
            (time - PoissonProcess.arrivalPrefix
              (PoissonProcess.canonicalRenewalCount time value.2) value.2)| ≤ z)
    intro hgood_value
    obtain ⟨time, htime, hlarge⟩ := hvalue
    have hclock_lt : (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) <
        (cap + 1 : ℝ) := lt_of_not_ge hclock
    have hclock_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < cap + 1 := by
      exact_mod_cast hclock_lt
    have hclock_le : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ cap :=
      Nat.lt_succ_iff.mp hclock_lt_nat
    have hgap_le : ∀ index ≤ cap,
        rate * PoissonProcess.interarrival index value.2 ≤ z := by
      intro index hindex
      exact le_of_not_gt (by
        intro hgt
        apply hgap
        exact ⟨index, hindex, hgt⟩)
    exact (not_le_of_gt hlarge) (hgood_value hclock_le hgap_le time htime)
  have hsplit : source.real terminalEvent ≤
      source.real clockEvent + source.real gapEvent := by
    calc
      source.real terminalEvent ≤ source.real ((clockEvent ∪ gapEvent) ∪ exceptionalEvent) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ source.real (clockEvent ∪ gapEvent) + source.real exceptionalEvent :=
        measureReal_union_le _ _
      _ = source.real (clockEvent ∪ gapEvent) := by rw [hnull_real, add_zero]
      _ ≤ source.real clockEvent + source.real gapEvent := measureReal_union_le _ _
  have hclock_meas : MeasurableSet {gap : ℕ → ℝ |
      (cap + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon gap : ℝ)} := by
    exact ((measurable_of_countable fun count : ℕ => (count : ℝ)).comp
      (PoissonProcess.measurable_canonicalRenewalCount horizon)) measurableSet_Ici
  have hclock_measure : source.real clockEvent = gaps.real {gap : ℕ → ℝ |
      (cap + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon gap : ℝ)} := by
    change (trajectory.prod gaps).real (Prod.snd ⁻¹' {gap : ℕ → ℝ |
      (cap + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon gap : ℝ)}) =
        gaps.real {gap : ℕ → ℝ |
          (cap + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon gap : ℝ)}
    simp only [Measure.real]
    rw [← Measure.map_apply measurable_snd hclock_meas,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hclock := PoissonProcess.real_mul_measure_canonicalRenewalCount_ge_le
    hrate hhorizon (show 0 ≤ (cap + 1 : ℝ) by positivity)
  have hclock' : (cap + 1 : ℝ) * source.real clockEvent ≤ rate * horizon := by
    simpa [gaps] using hclock_measure.symm ▸ hclock
  have hclock_div : source.real clockEvent ≤ (rate * horizon) / (cap + 1 : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < (cap + 1 : ℝ))).mpr
    simpa [mul_comm] using hclock'
  have hgap_meas : MeasurableSet {gap : ℕ → ℝ |
      ∃ index ≤ cap, z < rate * PoissonProcess.interarrival index gap} := by
    rw [show {gap : ℕ → ℝ | ∃ index ≤ cap,
        z < rate * PoissonProcess.interarrival index gap} =
        ⋃ index ∈ Finset.range (cap + 1),
          {gap | z < rate * PoissonProcess.interarrival index gap} by
      ext gap
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨index, hindex, hvalue⟩
        exact ⟨index, Nat.lt_succ_iff.mpr hindex, hvalue⟩
      · rintro ⟨index, hindex, hvalue⟩
        exact ⟨index, Nat.lt_succ_iff.mp hindex, hvalue⟩]
    exact Finset.measurableSet_biUnion (Finset.range (cap + 1)) fun index _ =>
      measurableSet_lt measurable_const
        (measurable_const.mul (PoissonProcess.measurable_interarrival index))
  have hgap_measure : source.real gapEvent = gaps.real {gap : ℕ → ℝ |
      ∃ index ≤ cap, z < rate * PoissonProcess.interarrival index gap} := by
    change (trajectory.prod gaps).real (Prod.snd ⁻¹' {gap : ℕ → ℝ |
      ∃ index ≤ cap, z < rate * PoissonProcess.interarrival index gap}) =
        gaps.real {gap : ℕ → ℝ |
          ∃ index ≤ cap, z < rate * PoissonProcess.interarrival index gap}
    simp only [Measure.real]
    rw [← Measure.map_apply measurable_snd hgap_meas,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hgap_bound := PoissonProcess.real_measure_exists_interarrival_rate_mul_gt_le
    hrate hz cap
  have hgap' : source.real gapEvent ≤ (cap + 1 : ℝ) * Real.exp (-z) := by
    simpa [gaps, gapEvent] using hgap_measure.symm ▸ hgap_bound
  change source.real terminalEvent ≤ _
  exact hsplit.trans (add_le_add hclock_div hgap')

/-- The embedded idle-fraction prefix minus its rate-scaled physical-time
occupation is exactly the explicit centered-clock residual. -/
theorem manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
    (servers : ℕ) (rate time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (harrival_nonneg : ∀ index : ℕ,
      0 ≤ PoissonProcess.arrivalTime index value.2)
    (htime : 0 ≤ time) :
    manyServerMarkedStateIdleFractionPrefix servers value.1
        (PoissonProcess.canonicalRenewalCount time value.2) -
      rate * manyServerMarkedCanonicalIdleFractionOccupation servers time value =
        manyServerMarkedCanonicalIdleFractionClockResidual servers rate time value := by
  simpa only [manyServerMarkedStateIdleFractionPrefix,
    manyServerMarkedCanonicalIdleFractionOccupation,
    manyServerMarkedCanonicalIdleFractionOnReal,
    manyServerMarkedCanonicalQueueLength,
    manyServerMarkedStateIdleFractionAt,
    manyServerMarkedCanonicalIdleFractionClockResidual] using
    PoissonProcess.renewalRewardPrefix_sub_rate_mul_occupation_eq_centeredClock_sub_terminal
      (fun index => 1 - (manyServerBusyFraction servers (value.1 index).1 : ℝ))
      value.2 hdiverges hmono harrival_nonneg rate time htime

/-- Under any independent external marked-trajectory law, the idle-prefix
and physical-occupation identity holds simultaneously at all nonnegative
times on one exponential-clock full-measure event. -/
theorem ae_forall_manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (servers : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ value ∂trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate),
      ∀ time : ℝ, 0 ≤ time →
        manyServerMarkedStateIdleFractionPrefix servers value.1
            (PoissonProcess.canonicalRenewalCount time value.2) -
          rate * manyServerMarkedCanonicalIdleFractionOccupation servers time value =
            manyServerMarkedCanonicalIdleFractionClockResidual servers rate time value := by
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ gap ∂gaps,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index gap) atTop atTop ∧
        Monotone (fun index : ℕ => PoissonProcess.arrivalTime index gap) ∧
          ∀ index : ℕ, 0 ≤ PoissonProcess.arrivalTime index gap := by
    filter_upwards [PoissonProcess.ae_arrivalTime_tendsto_atTop hrate,
      PoissonProcess.ae_arrivalTime_monotone hrate,
      PoissonProcess.ae_all_arrivalTime_nonnegative hrate] with gap hdiv hmono hnonneg
    exact ⟨hdiv, hmono, hnonneg⟩
  have hlift : ∀ᵐ value ∂trajectory.prod gaps,
      Tendsto (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop ∧
        Monotone (fun index : ℕ => PoissonProcess.arrivalTime index value.2) ∧
          ∀ index : ℕ, 0 ≤ PoissonProcess.arrivalTime index value.2 := by
    refine ae_of_ae_map (μ := trajectory.prod gaps) (f := Prod.snd)
      (p := fun gap => Tendsto
        (fun index : ℕ => PoissonProcess.arrivalTime index gap) atTop atTop ∧
        Monotone (fun index : ℕ => PoissonProcess.arrivalTime index gap) ∧
        ∀ index : ℕ, 0 ≤ PoissonProcess.arrivalTime index gap)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with value hvalue
  intro time htime
  exact manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
    servers rate time value hvalue.1 hvalue.2.1 hvalue.2.2 htime

/-- Replacing the retained potential-event mark by the next fresh mark changes
an idle compensator prefix by at most two endpoint terms and one server share
per embedded transition; the statement also covers the empty prefix. -/
theorem abs_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_nextPotentialServiceIdlePrefix_le_two_add_steps_div
    (servers : ℕ) (path : ℕ → ℕ × Bool) (steps : ℕ) (hservers : 0 < servers)
    (hstep : ∀ index : ℕ,
      ManyServerMarkedStateStepAllowed (path index) (path (index + 1))) :
    |manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers path steps -
      manyServerMarkedStateNextPotentialServiceIdlePrefix servers path steps| ≤
      2 + (steps : ℝ) * (1 / (servers : ℝ)) := by
  cases steps with
  | zero =>
      simp [manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix,
        manyServerMarkedStateNextPotentialServiceIdlePrefix]
  | succ steps =>
      have hbase :=
        abs_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_nextPotentialServiceIdlePrefix_le
          servers path steps hservers hstep
      calc
        |manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
            servers path (steps + 1) -
          manyServerMarkedStateNextPotentialServiceIdlePrefix servers path (steps + 1)| ≤
            2 + (steps : ℝ) * (1 / (servers : ℝ)) := hbase
        _ ≤ 2 + ((steps + 1 : ℕ) : ℝ) * (1 / (servers : ℝ)) := by
            have hinv_nonneg : 0 ≤ 1 / (servers : ℝ) := by positivity
            rw [one_div] at hinv_nonneg
            norm_num [Nat.cast_add, Nat.cast_one]
            nlinarith

/-- Multiplying the idle-prefix/physical-occupation decomposition by a fixed
selection share preserves the exact clock-residual form. -/
theorem scalar_mul_manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
    (servers : ℕ) (rate share time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (harrival_nonneg : ∀ index : ℕ,
      0 ≤ PoissonProcess.arrivalTime index value.2)
    (htime : 0 ≤ time) :
    share * manyServerMarkedStateIdleFractionPrefix servers value.1
        (PoissonProcess.canonicalRenewalCount time value.2) -
      (rate * share) * manyServerMarkedCanonicalIdleFractionOccupation
        servers time value =
        share * manyServerMarkedCanonicalIdleFractionClockResidual
          servers rate time value := by
  have hbase :=
    manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
      servers rate time value hdiverges hmono harrival_nonneg htime
  calc
    share * manyServerMarkedStateIdleFractionPrefix servers value.1
        (PoissonProcess.canonicalRenewalCount time value.2) -
        (rate * share) * manyServerMarkedCanonicalIdleFractionOccupation
          servers time value =
        share * (manyServerMarkedStateIdleFractionPrefix servers value.1
          (PoissonProcess.canonicalRenewalCount time value.2) -
          rate * manyServerMarkedCanonicalIdleFractionOccupation servers time value) := by
            ring
    _ = share * manyServerMarkedCanonicalIdleFractionClockResidual
          servers rate time value := by rw [hbase]

/-- After inserting the uniformization potential-service share, the physical
idle occupation carries exactly the aggregate many-server service rate. -/
theorem manyServerPotentialIdleFractionPrefix_sub_physicalIdleOccupation_eq_clockResidual
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ) (time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (harrival_nonneg : ∀ index : ℕ,
      0 ≤ PoissonProcess.arrivalTime index value.2)
    (htime : 0 ≤ time) :
    ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        manyServerMarkedStateIdleFractionPrefix servers value.1
          (PoissonProcess.canonicalRenewalCount time value.2) -
      ((servers : ℝ) * serviceRate) *
        manyServerMarkedCanonicalIdleFractionOccupation servers time value =
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        manyServerMarkedCanonicalIdleFractionClockResidual servers
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers) time value := by
  have hbase :=
    scalar_mul_manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
      servers (manyServerUniformizationRate
        (trafficIntensity : ℝ) serviceRate servers)
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) time value
      hdiverges hmono harrival_nonneg htime
  rw [manyServerUniformizationRate_potentialService] at hbase
  exact hbase

/-- The next-fresh-mark potential-service reward has the same physical idle
occupation plus two explicit centered errors: the fresh-mark reward and the
renewal-clock residual. -/
theorem manyServerMarkedStateNextPotentialServiceIdlePrefix_sub_physicalIdleOccupation_eq
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ) (time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (harrival_nonneg : ∀ index : ℕ,
      0 ≤ PoissonProcess.arrivalTime index value.2)
    (htime : 0 ≤ time) :
    manyServerMarkedStateNextPotentialServiceIdlePrefix servers value.1
        (PoissonProcess.canonicalRenewalCount time value.2) -
      ((servers : ℝ) * serviceRate) *
        manyServerMarkedCanonicalIdleFractionOccupation servers time value =
      manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1 +
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        manyServerMarkedCanonicalIdleFractionClockResidual servers
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers) time value := by
  have hphysical :=
    manyServerPotentialIdleFractionPrefix_sub_physicalIdleOccupation_eq_clockResidual
      trafficIntensity serviceRate servers time value
      hdiverges hmono harrival_nonneg htime
  have hfresh :=
    manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_eq
      trafficIntensity servers
      (PoissonProcess.canonicalRenewalCount time value.2) value.1
  have hshare :
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
        1 - (uniformizedBirthProbability trafficIntensity : ℝ) := by
    rw [NNReal.coe_sub (uniformizedBirthProbability_le_one trafficIntensity)]
    norm_num
  rw [hshare] at hphysical ⊢
  calc
    manyServerMarkedStateNextPotentialServiceIdlePrefix servers value.1
          (PoissonProcess.canonicalRenewalCount time value.2) -
        ((servers : ℝ) * serviceRate) *
          manyServerMarkedCanonicalIdleFractionOccupation servers time value =
        (manyServerMarkedStateNextPotentialServiceIdlePrefix servers value.1
          (PoissonProcess.canonicalRenewalCount time value.2) -
          (1 - (uniformizedBirthProbability trafficIntensity : ℝ)) *
            manyServerMarkedStateIdleFractionPrefix servers value.1
              (PoissonProcess.canonicalRenewalCount time value.2)) +
          ((1 - (uniformizedBirthProbability trafficIntensity : ℝ)) *
            manyServerMarkedStateIdleFractionPrefix servers value.1
              (PoissonProcess.canonicalRenewalCount time value.2) -
            ((servers : ℝ) * serviceRate) *
              manyServerMarkedCanonicalIdleFractionOccupation servers time value) := by
              ring
    _ = manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
          trafficIntensity servers
          (PoissonProcess.canonicalRenewalCount time value.2) value.1 +
        (1 - (uniformizedBirthProbability trafficIntensity : ℝ)) *
          manyServerMarkedCanonicalIdleFractionClockResidual servers
            (manyServerUniformizationRate
              (trafficIntensity : ℝ) serviceRate servers) time value := by
              rw [← hfresh, hphysical]

/-- The literal embedded unused-service compensator equals physical idle
occupation plus the retained-mark replacement error, fresh-mark martingale,
and explicit renewal-clock residual. -/
theorem manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_physicalIdleOccupation_eq
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ) (time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) atTop atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (harrival_nonneg : ∀ index : ℕ,
      0 ≤ PoissonProcess.arrivalTime index value.2)
    (htime : 0 ≤ time) :
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers value.1 (PoissonProcess.canonicalRenewalCount time value.2) -
      ((servers : ℝ) * serviceRate) *
        manyServerMarkedCanonicalIdleFractionOccupation servers time value =
      (manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers value.1 (PoissonProcess.canonicalRenewalCount time value.2) -
        manyServerMarkedStateNextPotentialServiceIdlePrefix
          servers value.1 (PoissonProcess.canonicalRenewalCount time value.2)) +
      manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1 +
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        manyServerMarkedCanonicalIdleFractionClockResidual servers
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers) time value := by
  have hnext :=
    manyServerMarkedStateNextPotentialServiceIdlePrefix_sub_physicalIdleOccupation_eq
      trafficIntensity serviceRate servers time value
      hdiverges hmono harrival_nonneg htime
  linarith

/-- The complete embedded unused-service compensator/physical-occupation
decomposition holds simultaneously at every nonnegative time under any
independent external marked-trajectory probability law. -/
theorem ae_forall_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_sub_physicalIdleOccupation_eq
    (trajectory : Measure (ℕ → ℕ × Bool)) [IsProbabilityMeasure trajectory]
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers) :
    ∀ᵐ value ∂trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)),
      ∀ time : ℝ, 0 ≤ time →
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
            servers value.1 (PoissonProcess.canonicalRenewalCount time value.2) -
          ((servers : ℝ) * serviceRate) *
            manyServerMarkedCanonicalIdleFractionOccupation servers time value =
          (manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
              servers value.1 (PoissonProcess.canonicalRenewalCount time value.2) -
            manyServerMarkedStateNextPotentialServiceIdlePrefix
              servers value.1 (PoissonProcess.canonicalRenewalCount time value.2)) +
          manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
            trafficIntensity servers
            (PoissonProcess.canonicalRenewalCount time value.2) value.1 +
          ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            manyServerMarkedCanonicalIdleFractionClockResidual servers
              (manyServerUniformizationRate
                (trafficIntensity : ℝ) serviceRate servers) time value := by
  have hidle :=
    ae_forall_manyServerMarkedStateIdleFractionPrefix_sub_rate_mul_canonicalIdleOccupation_eq_clockResidual
      trajectory servers hrate
  filter_upwards [hidle] with value hidle
  intro time htime
  have hshare :
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
        1 - (uniformizedBirthProbability trafficIntensity : ℝ) := by
    rw [NNReal.coe_sub (uniformizedBirthProbability_le_one trafficIntensity)]
    norm_num
  have hphysical :
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          manyServerMarkedStateIdleFractionPrefix servers value.1
            (PoissonProcess.canonicalRenewalCount time value.2) -
        ((servers : ℝ) * serviceRate) *
          manyServerMarkedCanonicalIdleFractionOccupation servers time value =
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          manyServerMarkedCanonicalIdleFractionClockResidual servers
            (manyServerUniformizationRate
              (trafficIntensity : ℝ) serviceRate servers) time value := by
    have hpotential := manyServerUniformizationRate_potentialService
      trafficIntensity serviceRate servers
    calc
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            manyServerMarkedStateIdleFractionPrefix servers value.1
              (PoissonProcess.canonicalRenewalCount time value.2) -
          ((servers : ℝ) * serviceRate) *
            manyServerMarkedCanonicalIdleFractionOccupation servers time value =
          ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            manyServerMarkedStateIdleFractionPrefix servers value.1
              (PoissonProcess.canonicalRenewalCount time value.2) -
            (manyServerUniformizationRate
              (trafficIntensity : ℝ) serviceRate servers *
              ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ)) *
              manyServerMarkedCanonicalIdleFractionOccupation servers time value := by
              rw [hpotential]
      _ =
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (manyServerMarkedStateIdleFractionPrefix servers value.1
            (PoissonProcess.canonicalRenewalCount time value.2) -
            manyServerUniformizationRate
              (trafficIntensity : ℝ) serviceRate servers *
              manyServerMarkedCanonicalIdleFractionOccupation servers time value) := by ring
      _ = ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          manyServerMarkedCanonicalIdleFractionClockResidual servers
            (manyServerUniformizationRate
              (trafficIntensity : ℝ) serviceRate servers) time value := by
            exact congrArg (fun x : ℝ =>
              ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) * x)
              (hidle time htime)
  have hfresh :=
    manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum_eq
      trafficIntensity servers
      (PoissonProcess.canonicalRenewalCount time value.2) value.1
  rw [hshare] at hphysical ⊢
  linarith

/-- Outside the renewal clock's null monotonicity exception, a deterministic
clock cutoff and an unhit predictable lower barrier control every fresh-mark
idle-martingale coordinate by its stopped finite-prefix maximum. -/
theorem ae_forall_manyServerMarkedCanonicalCenteredNextPotentialServiceIdle_sq_le_stoppedMaximum_of_clock_count_le_no_lowerExit
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℝ) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n →
        (n : ENat) ≤
          manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 →
        ∀ time : ℝ, time ≤ horizon →
          (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
            trafficIntensity servers
            (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2 ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun index =>
                (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
                  trafficIntensity servers lowerThreshold index value.1) ^ 2) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hmono_gaps : ∀ᵐ gap ∂gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ value ∂trajectory.prod gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := trajectory.prod gaps) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  filter_upwards [hmono] with value hmono_value hcount hbefore time htime
  have htime_count : PoissonProcess.canonicalRenewalCount time value.2 ≤ n :=
    (hmono_value htime).trans hcount
  have htime_before : (PoissonProcess.canonicalRenewalCount time value.2 : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 :=
    le_trans (ENat.coe_le_coe.mpr htime_count) hbefore
  rw [← manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_centered_of_le_lowerExit
    trafficIntensity servers lowerThreshold
    (PoissonProcess.canonicalRenewalCount time value.2) value.1 htime_before]
  exact Finset.le_sup'
    (s := Finset.range (n + 1))
    (f := fun index =>
      (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
        trafficIntensity servers lowerThreshold index value.1) ^ 2)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le htime_count))

/-- The lower-barrier-stopped fresh-mark idle maximum has its finite-prefix
Doob bound after coupling the embedded trajectory to an independent canonical
renewal clock. -/
theorem real_mul_measure_manyServerMarkedCanonicalStoppedNextPotentialServiceIdleMaximum_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (threshold : ℝ≥0) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (threshold : ℝ) * (trajectory.prod gaps).real {value | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index value.1) ^ 2)} ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℕ × Bool) := {path | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index path) ^ 2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    apply measurableSet_le measurable_const
    exact Finset.measurable_range_sup'' fun index _ =>
      (((manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_stronglyAdapted
        trafficIntensity servers lowerThreshold index).mono (piLE.le index)).measurable.pow
          measurable_const)
  have hpreserve : MeasurePreserving Prod.fst source trajectory := by
    dsimp [source]
    exact measurePreserving_fst
  have hmeasure : source.real (Prod.fst ⁻¹' event) = trajectory.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst hevent_meas]
  have hbase :=
    ennreal_mul_measure_maximalStoppedNextPotentialServiceIdlePartialSum_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity servers lowerThreshold hservers threshold n
  have hidle_nonneg : 0 ≤ 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  have hright_nonneg : 0 ≤ (n : ℝ) *
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg n) hidle_nonneg
  have hbase_real : (threshold : ℝ) * trajectory.real event ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    have hbase_toReal := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top).mpr hbase
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal hright_nonneg] using hbase_toReal
  change (threshold : ℝ) * source.real (Prod.fst ⁻¹' event) ≤ _
  rw [hmeasure]
  exact hbase_real

/-- An arbitrary-initial physical-time fresh-mark idle-martingale excursion
is controlled by canonical-clock overflow, predictable lower-barrier exit,
and the stopped fresh-mark maximum. -/
theorem real_measure_manyServerMarkedCanonicalFreshIdleMartingaleExcursion_le_from_initial_lowerBarrier
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold martingaleThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hmartingaleThreshold_pos : 0 < martingaleThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value |
      initialLower ≤ (value.1 0).1 ∧
        ∃ time : ℝ, time ≤ horizon ∧ (martingaleThreshold : ℝ) ≤
          (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
            trafficIntensity servers
            (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2} ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
          martingaleThreshold := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let bad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (martingaleThreshold : ℝ) ≤
        (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
          trafficIntensity servers
          (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let exitEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤
        (n : ℕ∞)}
  let stoppedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (martingaleThreshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index value.1) ^ 2)}
  let good : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hmono_gaps : ∀ᵐ gap ∂gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  have hbad_eq : (fun value => value ∈ bad) =ᵐ[source]
      (fun value => value ∈ bad ∩ good) := by
    filter_upwards [hmono] with value hvalue
    simp [good, hvalue]
  have hbad_measure : source.real bad = source.real (bad ∩ good) := by
    exact MeasureTheory.measureReal_congr hbad_eq
  have hsubset : bad ∩ good ⊆
      (clockEvent ∪ exitEvent) ∪ stoppedEvent := by
    intro value hvalue
    rcases hvalue.1 with ⟨hinitial, time, htime, hlarge⟩
    have hclock_mono := hvalue.2
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl (Or.inl hclock)
    by_cases hexit : value ∈ exitEvent
    · exact Or.inl (Or.inr hexit)
    right
    have hcount_lt_real :
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) < (n + 1 : ℝ) :=
      lt_of_not_ge hclock
    have hcount_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < n + 1 := by
      exact_mod_cast hcount_lt_real
    have hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n :=
      Nat.lt_succ_iff.mp hcount_lt_nat
    have hbefore : (PoissonProcess.canonicalRenewalCount horizon value.2 : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 := by
      apply lt_of_not_ge
      intro hle
      apply hexit
      exact ⟨hinitial, hle.trans (ENat.coe_le_coe.mpr hcount)⟩
    have htime_count : PoissonProcess.canonicalRenewalCount time value.2 ≤ n :=
      (hclock_mono htime).trans hcount
    have htime_before : (PoissonProcess.canonicalRenewalCount time value.2 : ENat) ≤
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 :=
      le_of_lt (lt_of_le_of_lt
        (ENat.coe_le_coe.mpr (hclock_mono htime)) hbefore)
    change (martingaleThreshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
            trafficIntensity servers lowerThreshold index value.1) ^ 2)
    apply hlarge.trans
    rw [← manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum_eq_centered_of_le_lowerExit
      trafficIntensity servers lowerThreshold
      (PoissonProcess.canonicalRenewalCount time value.2) value.1 htime_before]
    exact Finset.le_sup'
      (s := Finset.range (n + 1))
      (f := fun index =>
        (manyServerMarkedStateStoppedNextPotentialServiceIdlePartialSum
          trafficIntensity servers lowerThreshold index value.1) ^ 2)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le htime_count))
  have hsplit : source.real bad ≤
      source.real clockEvent + source.real exitEvent + source.real stoppedEvent := by
    calc
      source.real bad = source.real (bad ∩ good) := hbad_measure
      _ ≤ source.real ((clockEvent ∪ exitEvent) ∪ stoppedEvent) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ source.real (clockEvent ∪ exitEvent) + source.real stoppedEvent :=
        measureReal_union_le _ _
      _ ≤ source.real clockEvent + source.real exitEvent + source.real stoppedEvent := by
        gcongr
        exact measureReal_union_le _ _
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤ rate * horizon := by
    simpa [rate, trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤ (rate * horizon) / (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hexit_bound :=
    real_mul_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
      initial trafficIntensity serviceRate servers initialLower lowerThreshold n hservers hserviceRate
        margin exitThreshold hmargin_nonneg hexitThreshold_le hmargin
  have hexit_div : source.real exitEvent ≤ (n : ℝ) / exitThreshold := by
    have hexit' : (exitThreshold : ℝ) * source.real exitEvent ≤ n := by
      simpa [rate, trajectory, gaps, source, exitEvent] using hexit_bound
    apply (le_div_iff₀ (by exact_mod_cast hexitThreshold_pos)).mpr
    simpa [mul_comm] using hexit'
  have hstopped :=
    real_mul_measure_manyServerMarkedCanonicalStoppedNextPotentialServiceIdleMaximum_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity serviceRate servers lowerThreshold hservers hserviceRate
        martingaleThreshold n
  have hstopped' : (martingaleThreshold : ℝ) * source.real stoppedEvent ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    simpa [rate, trajectory, gaps, source, stoppedEvent] using hstopped
  have hstopped_div : source.real stoppedEvent ≤
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
        martingaleThreshold := by
    apply (le_div_iff₀ (by exact_mod_cast hmartingaleThreshold_pos)).mpr
    simpa [mul_comm] using hstopped'
  change source.real bad ≤
    (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
        martingaleThreshold
  exact hsplit.trans (add_le_add (add_le_add hclock_div hexit_div) hstopped_div)

/-- The physical-time fresh-mark idle-martingale estimate with its initial
condition event separated as an exact initial queue lower tail. -/
theorem real_measure_manyServerMarkedCanonicalFreshIdleMartingaleExcursion_le_from_initial_lowerBarrier_withInitialTail
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold martingaleThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hmartingaleThreshold_pos : 0 < martingaleThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (martingaleThreshold : ℝ) ≤
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2} ≤
      initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            martingaleThreshold := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let initialBad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (value.1 0).1 < initialLower}
  let localizedBad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (martingaleThreshold : ℝ) ≤
        (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
          trafficIntensity servers
          (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2}
  let martingaleEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ∃ time : ℝ, time ≤ horizon ∧ (martingaleThreshold : ℝ) ≤
      (manyServerMarkedStateCenteredNextPotentialServiceIdlePartialSum
        trafficIntensity servers
        (PoissonProcess.canonicalRenewalCount time value.2) value.1) ^ 2}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hsubset : martingaleEvent ⊆ initialBad ∪ localizedBad := by
    intro value hvalue
    by_cases hinitial : initialLower ≤ (value.1 0).1
    · exact Or.inr ⟨hinitial, hvalue⟩
    · exact Or.inl (Nat.lt_of_not_ge hinitial)
  have htail_measure : source initialBad = initial.toMeasure (Set.Iio initialLower) := by
    simpa [source, initialBad, manyServerMarkedCanonicalInitialQueue] using
      (measure_manyServerMarkedCanonicalInitialQueue_preimage
        initial trafficIntensity serviceRate servers hservers hserviceRate (Set.Iio initialLower))
  have htail : source.real initialBad = initial.toMeasure.real (Set.Iio initialLower) := by
    simp only [Measure.real]
    rw [htail_measure]
  have hlocalized :=
    real_measure_manyServerMarkedCanonicalFreshIdleMartingaleExcursion_le_from_initial_lowerBarrier
      initial trafficIntensity serviceRate servers initialLower lowerThreshold
        hservers hserviceRate hhorizon n margin exitThreshold martingaleThreshold
        hmargin_nonneg hexitThreshold_le hexitThreshold_pos hmargin
        hmartingaleThreshold_pos
  have hlocalized' : source.real localizedBad ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
          martingaleThreshold := by
    simpa [source, localizedBad] using hlocalized
  calc
    source.real martingaleEvent ≤ source.real (initialBad ∪ localizedBad) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ source.real initialBad + source.real localizedBad :=
      measureReal_union_le _ _
    _ ≤ initial.toMeasure.real (Set.Iio initialLower) +
        ((rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            martingaleThreshold) := by
        rw [htail]
        gcongr
    _ = initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            martingaleThreshold := by ring

/-- The completed state-weighted clock reward is controlled by canonical-clock
overflow, lower-barrier exit, its initial IID coordinate, and the shifted
externally weighted IID maximum. -/
theorem real_measure_manyServerMarkedCanonicalIdleClockCenteredRewardExcursion_le_from_initial_lowerBarrier
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold rewardThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hrewardThreshold_pos : 0 < rewardThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value |
      initialLower ≤ (value.1 0).1 ∧
        ∃ time : ℝ, time ≤ horizon ∧ (rewardThreshold : ℝ) ≤
          (manyServerMarkedCanonicalIdleFractionClockCenteredReward
            servers rate time value) ^ 2} ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
          ((rewardThreshold : ℝ) / 4) +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
          ((rewardThreshold : ℝ) / 4) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let bad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (rewardThreshold : ℝ) ≤
        (manyServerMarkedCanonicalIdleFractionClockCenteredReward
          servers rate time value) ^ 2}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let exitEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤
        (n : ℕ∞)}
  let initialEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ((rewardThreshold : ℝ) / 4) ≤
      (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
        (1 - rate * PoissonProcess.interarrival 0 value.2)) ^ 2}
  let shiftedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ((rewardThreshold : ℝ) / 4) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun steps => (∑ index ∈ Finset.range steps,
          manyServerMarkedStateCappedLowerIdleFraction
            servers lowerThreshold (index + 1) value.1 *
            (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)}
  let good : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) ∧
      ∀ step : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 step) (value.1 (step + 1))}
  let quarterThreshold : ℝ≥0 := ⟨(rewardThreshold : ℝ) / 4, by positivity⟩
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hquarter_pos : 0 < (quarterThreshold : ℝ) := by
    dsimp [quarterThreshold]
    exact div_pos (by exact_mod_cast hrewardThreshold_pos) (by norm_num)
  have hrewardThreshold_real_pos : 0 < (rewardThreshold : ℝ) := by
    exact_mod_cast hrewardThreshold_pos
  have hquarter_real_pos : 0 < (rewardThreshold : ℝ) / 4 :=
    div_pos hrewardThreshold_real_pos (by norm_num)
  have hmono_gaps : ∀ᵐ gap ∂gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  have hsteps : ∀ᵐ value ∂source,
      ∀ step : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 step) (value.1 (step + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ step : ℕ, ManyServerMarkedStateStepAllowed (path step) (path (step + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  have hbad_eq : (fun value => value ∈ bad) =ᵐ[source]
      (fun value => value ∈ bad ∩ good) := by
    filter_upwards [hmono, hsteps] with value hmono_value hsteps_value
    simp [good, hmono_value, hsteps_value]
  have hbad_measure : source.real bad = source.real (bad ∩ good) := by
    exact MeasureTheory.measureReal_congr hbad_eq
  have hsubset : bad ∩ good ⊆
      ((clockEvent ∪ exitEvent) ∪ initialEvent) ∪ shiftedEvent := by
    intro value hvalue
    rcases hvalue.1 with ⟨hinitial, time, htime, hlarge⟩
    have hclock_mono := hvalue.2.1
    have hstep := hvalue.2.2
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl (Or.inl (Or.inl hclock))
    by_cases hexit : value ∈ exitEvent
    · exact Or.inl (Or.inl (Or.inr hexit))
    by_cases hincoming : value ∈ initialEvent
    · exact Or.inl (Or.inr hincoming)
    right
    have hcount_lt_real :
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) < (n + 1 : ℝ) :=
      lt_of_not_ge hclock
    have hcount_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < n + 1 := by
      exact_mod_cast hcount_lt_real
    have hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n :=
      Nat.lt_succ_iff.mp hcount_lt_nat
    have hbefore : (n : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 := by
      apply lt_of_not_ge
      intro hle
      apply hexit
      exact ⟨hinitial, hle⟩
    have htime_count : PoissonProcess.canonicalRenewalCount time value.2 ≤ n :=
      (hclock_mono htime).trans hcount
    have htime_before : (PoissonProcess.canonicalRenewalCount time value.2 : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 := by
      exact lt_of_le_of_lt (ENat.coe_le_coe.mpr htime_count) hbefore
    by_cases htime_zero : PoissonProcess.canonicalRenewalCount time value.2 = 0
    · exfalso
      rw [manyServerMarkedCanonicalIdleFractionClockCenteredReward, htime_zero,
        Finset.sum_range_zero] at hlarge
      exact (not_lt_of_ge hlarge) (by simpa using hrewardThreshold_pos)
    · have htime_pos : 0 < PoissonProcess.canonicalRenewalCount time value.2 :=
        Nat.pos_of_ne_zero htime_zero
      have hactive : ∀ index < PoissonProcess.canonicalRenewalCount time value.2,
          value.1 ∈ manyServerMarkedStateLowerExitActiveSet lowerThreshold index := by
        intro index hindex
        have hindex_before : (index : ENat) <
            manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 :=
          lt_of_le_of_lt (ENat.coe_le_coe.mpr (Nat.le_of_lt hindex)) htime_before
        simpa only [manyServerMarkedStateLowerExitActiveSet, Set.mem_setOf_eq] using hindex_before
      have hdecomp :=
        manyServerMarkedCanonicalIdleFractionClockCenteredReward_eq_cappedInitial_add_shifted
          servers lowerThreshold rate time value hstep htime_pos hactive
      have hlarge' : (rewardThreshold : ℝ) ≤
          (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
              (1 - rate * PoissonProcess.interarrival 0 value.2) +
            ∑ index ∈ Finset.range
              (PoissonProcess.canonicalRenewalCount time value.2 - 1),
              manyServerMarkedStateCappedLowerIdleFraction
                  servers lowerThreshold (index + 1) value.1 *
                (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2 := by
        rwa [hdecomp] at hlarge
      have hinitial_lt :
          (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
              (1 - rate * PoissonProcess.interarrival 0 value.2)) ^ 2 <
            (rewardThreshold : ℝ) / 4 := lt_of_not_ge hincoming
      have hsteps_le : PoissonProcess.canonicalRenewalCount time value.2 - 1 ≤ n := by
        omega
      by_contra hnot_shifted
      change ¬ ((rewardThreshold : ℝ) / 4 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun steps => (∑ index ∈ Finset.range steps,
            manyServerMarkedStateCappedLowerIdleFraction
              servers lowerThreshold (index + 1) value.1 *
              (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)) at hnot_shifted
      have hsup_lt :
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun steps => (∑ index ∈ Finset.range steps,
              manyServerMarkedStateCappedLowerIdleFraction
                servers lowerThreshold (index + 1) value.1 *
                (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2) <
            (rewardThreshold : ℝ) / 4 := lt_of_not_ge hnot_shifted
      have hmember : PoissonProcess.canonicalRenewalCount time value.2 - 1 ∈
          Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hsteps_le)
      have htail_lt :
          (∑ index ∈ Finset.range
              (PoissonProcess.canonicalRenewalCount time value.2 - 1),
              manyServerMarkedStateCappedLowerIdleFraction
                  servers lowerThreshold (index + 1) value.1 *
                (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2 <
            (rewardThreshold : ℝ) / 4 :=
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun steps => (∑ index ∈ Finset.range steps,
            manyServerMarkedStateCappedLowerIdleFraction
              servers lowerThreshold (index + 1) value.1 *
              (1 - rate * PoissonProcess.interarrival (index + 1) value.2)) ^ 2)
          hmember).trans_lt hsup_lt
      nlinarith [sq_nonneg
        (manyServerMarkedStateCappedLowerIdleFraction servers lowerThreshold 0 value.1 *
            (1 - rate * PoissonProcess.interarrival 0 value.2) -
          ∑ index ∈ Finset.range
            (PoissonProcess.canonicalRenewalCount time value.2 - 1),
            manyServerMarkedStateCappedLowerIdleFraction
                servers lowerThreshold (index + 1) value.1 *
              (1 - rate * PoissonProcess.interarrival (index + 1) value.2))]
  have hsplit : source.real bad ≤
      source.real clockEvent + source.real exitEvent + source.real initialEvent +
        source.real shiftedEvent := by
    calc
      source.real bad = source.real (bad ∩ good) := hbad_measure
      _ ≤ source.real (((clockEvent ∪ exitEvent) ∪ initialEvent) ∪ shiftedEvent) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ source.real ((clockEvent ∪ exitEvent) ∪ initialEvent) +
          source.real shiftedEvent := measureReal_union_le _ _
      _ ≤ (source.real (clockEvent ∪ exitEvent) + source.real initialEvent) +
          source.real shiftedEvent := by gcongr; exact measureReal_union_le _ _
      _ ≤ (source.real clockEvent + source.real exitEvent + source.real initialEvent) +
          source.real shiftedEvent := by gcongr; exact measureReal_union_le _ _
      _ = _ := by ring
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤ rate * horizon := by
    simpa [rate, trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤ (rate * horizon) / (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hexit_bound :=
    real_mul_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
      initial trafficIntensity serviceRate servers initialLower lowerThreshold n hservers hserviceRate
        margin exitThreshold hmargin_nonneg hexitThreshold_le hmargin
  have hexit_div : source.real exitEvent ≤ (n : ℝ) / exitThreshold := by
    have hexit' : (exitThreshold : ℝ) * source.real exitEvent ≤ n := by
      simpa [rate, trajectory, gaps, source, exitEvent] using hexit_bound
    apply (le_div_iff₀ (by exact_mod_cast hexitThreshold_pos)).mpr
    simpa [mul_comm] using hexit'
  have hinitial_bound :=
    real_mul_measure_manyServerMarkedCappedLowerIdleClockInitialSq_le
      trajectory servers lowerThreshold hservers hrate quarterThreshold
  have hinitial' : (quarterThreshold : ℝ) * source.real initialEvent ≤
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
    simpa [rate, trajectory, gaps, source, initialEvent, quarterThreshold] using hinitial_bound
  have hinitial_div : source.real initialEvent ≤
      ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
        ((rewardThreshold : ℝ) / 4) := by
    apply (le_div_iff₀ hquarter_real_pos).mpr
    simpa [quarterThreshold, mul_comm] using hinitial'
  have hshifted_bound :=
    real_mul_measure_manyServerMarkedCappedLowerIdleClockRewardMaximum_le
      trajectory servers lowerThreshold hservers hrate n quarterThreshold
  have hshifted' : (quarterThreshold : ℝ) * source.real shiftedEvent ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2 := by
    simpa [rate, trajectory, gaps, source, shiftedEvent, quarterThreshold] using hshifted_bound
  have hshifted_div : source.real shiftedEvent ≤
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
        ((rewardThreshold : ℝ) / 4) := by
    apply (le_div_iff₀ hquarter_real_pos).mpr
    simpa [quarterThreshold, mul_comm] using hshifted'
  change source.real bad ≤
    (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
      ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
        ((rewardThreshold : ℝ) / 4) +
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
        ((rewardThreshold : ℝ) / 4)
  exact hsplit.trans (add_le_add (add_le_add (add_le_add hclock_div hexit_div) hinitial_div)
    hshifted_div)

/-- The completed state-weighted clock-reward estimate with the arbitrary
initial queue condition separated as its exact lower-tail event. -/
theorem real_measure_manyServerMarkedCanonicalIdleClockCenteredRewardExcursion_le_from_initial_lowerBarrier_withInitialTail
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold rewardThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hrewardThreshold_pos : 0 < rewardThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (rewardThreshold : ℝ) ≤
      (manyServerMarkedCanonicalIdleFractionClockCenteredReward
        servers rate time value) ^ 2} ≤
      initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4) +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let initialBad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (value.1 0).1 < initialLower}
  let localizedBad : Set ((ℕ → ℕ × (Bool)) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (rewardThreshold : ℝ) ≤
        (manyServerMarkedCanonicalIdleFractionClockCenteredReward
          servers rate time value) ^ 2}
  let rewardEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ∃ time : ℝ, time ≤ horizon ∧ (rewardThreshold : ℝ) ≤
      (manyServerMarkedCanonicalIdleFractionClockCenteredReward
        servers rate time value) ^ 2}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hsubset : rewardEvent ⊆ initialBad ∪ localizedBad := by
    intro value hvalue
    by_cases hinitial : initialLower ≤ (value.1 0).1
    · exact Or.inr ⟨hinitial, hvalue⟩
    · exact Or.inl (Nat.lt_of_not_ge hinitial)
  have htail_measure : source initialBad = initial.toMeasure (Set.Iio initialLower) := by
    simpa [source, initialBad, manyServerMarkedCanonicalInitialQueue] using
      (measure_manyServerMarkedCanonicalInitialQueue_preimage
        initial trafficIntensity serviceRate servers hservers hserviceRate (Set.Iio initialLower))
  have htail : source.real initialBad = initial.toMeasure.real (Set.Iio initialLower) := by
    simp only [Measure.real]
    rw [htail_measure]
  have hlocalized :=
    real_measure_manyServerMarkedCanonicalIdleClockCenteredRewardExcursion_le_from_initial_lowerBarrier
      initial trafficIntensity serviceRate servers initialLower lowerThreshold
        hservers hserviceRate hhorizon n margin exitThreshold rewardThreshold
        hmargin_nonneg hexitThreshold_le hexitThreshold_pos hmargin hrewardThreshold_pos
  have hlocalized' : source.real localizedBad ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
          ((rewardThreshold : ℝ) / 4) +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
          ((rewardThreshold : ℝ) / 4) := by
    simpa [source, localizedBad] using hlocalized
  calc
    source.real rewardEvent ≤ source.real (initialBad ∪ localizedBad) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ source.real initialBad + source.real localizedBad :=
      measureReal_union_le _ _
    _ ≤ initial.toMeasure.real (Set.Iio initialLower) +
        ((rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4) +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4)) := by
        rw [htail]
        gcongr
    _ = initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4) +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) ^ 2) /
            ((rewardThreshold : ℝ) / 4) := by ring

end

end AppliedModelingLib.Probability.Queueing
