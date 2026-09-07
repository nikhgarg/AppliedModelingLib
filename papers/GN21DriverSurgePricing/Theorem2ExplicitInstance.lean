import GN21DriverSurgePricing.MainTheorems

/-!
# GN21 Theorem 2 Explicit Atomic Instance

This file isolates a small atomic measured instance for Theorem 2.  The goal is
to close the paper-facing multiplicative-pricing non-IC endpoint by reducing the
Appendix-D aggregate primitives to rational bounds plus elementary CTMC switch
probability estimates.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-- The explicit atomic trip-length distributions used for Theorem 2. -/
def theorem2AtomicMu : Fin 2 → Measure TripLength
  | 0 => Measure.dirac ((1 : ℝ) / 2)
  | 1 =>
      ((1 : ℝ≥0∞) / 2) • Measure.dirac (1 : ℝ) +
        ((1 : ℝ≥0∞) / 2) • Measure.dirac (6 : ℝ)

/-- The explicit arrival rates used for Theorem 2. -/
def theorem2AtomicArrival : Fin 2 → ℝ
  | 0 => 1
  | 1 => 50

/-- Multiplicative prices `w_i(τ)=m_i τ` in the explicit Theorem 2 instance. -/
def theorem2AtomicM : Fin 2 → ℝ
  | 0 => 4
  | 1 => 40

/-- The deviating policy: accept all in state 0, reject short trips in state 1. -/
def theorem2AtomicDeviation : Fin 2 → TripPolicy
  | 0 => acceptAllPolicy
  | 1 => rejectShortTripsPolicy 1

@[simp] theorem one_half_mem_acceptAllPolicy :
    ((1 : ℝ) / 2) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem one_mem_acceptAllPolicy :
    (1 : ℝ) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem six_mem_acceptAllPolicy :
    (6 : ℝ) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem one_not_mem_rejectShortTripsPolicy_one :
    (1 : ℝ) ∉ rejectShortTripsPolicy 1 := by
  simp [rejectShortTripsPolicy]

@[simp] theorem six_mem_rejectShortTripsPolicy_one :
    (6 : ℝ) ∈ rejectShortTripsPolicy 1 := by
  norm_num [rejectShortTripsPolicy]

theorem theorem2AtomicMu_zero_acceptAll_mass :
    singleStateTripMass (theorem2AtomicMu 0) acceptAllPolicy = 1 := by
  norm_num [singleStateTripMass, theorem2AtomicMu, acceptAllPolicy,
    positiveTripLengths]

theorem theorem2AtomicMu_zero_acceptAll_time :
    singleStateTripTime (theorem2AtomicMu 0) acceptAllPolicy = (1 : ℝ) / 2 := by
  classical
  rw [singleStateTripTime, theorem2AtomicMu, setIntegral_dirac]
  norm_num [acceptAllPolicy, positiveTripLengths]

theorem theorem2AtomicMu_zero_acceptAll_payment :
    singleStateTripPayment (theorem2AtomicMu 0)
        (multiplicativePricing (theorem2AtomicM 0)) acceptAllPolicy = 2 := by
  classical
  rw [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    setIntegral_dirac]
  norm_num [acceptAllPolicy, positiveTripLengths, multiplicativePricing]

theorem theorem2AtomicMu_one_acceptAll_mass :
    singleStateTripMass (theorem2AtomicMu 1) acceptAllPolicy = 1 := by
  norm_num [singleStateTripMass, theorem2AtomicMu, acceptAllPolicy,
    positiveTripLengths, ENNReal.toReal_add]

theorem theorem2AtomicMu_one_rejectShort_mass :
    singleStateTripMass (theorem2AtomicMu 1) (rejectShortTripsPolicy 1) =
      (1 : ℝ) / 2 := by
  simp [singleStateTripMass, theorem2AtomicMu]

theorem theorem2AtomicMu_one_acceptAll_time :
    singleStateTripTime (theorem2AtomicMu 1) acceptAllPolicy = (7 : ℝ) / 2 := by
  classical
  simp only [singleStateTripTime, theorem2AtomicMu, Measure.restrict_add,
    Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
    norm_num
  · exact (integrable_dirac (a := (1 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (1 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact (integrable_dirac (a := (6 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (6 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_time :
    singleStateTripTime (theorem2AtomicMu 1) (rejectShortTripsPolicy 1) = 3 := by
  classical
  simp only [singleStateTripTime, theorem2AtomicMu, Measure.restrict_add,
    Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one, six_mem_rejectShortTripsPolicy_one,
    ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
    norm_num
  · simp
  · exact (integrable_dirac (a := (6 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (6 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_acceptAll_payment :
    singleStateTripPayment (theorem2AtomicMu 1)
        (multiplicativePricing (theorem2AtomicM 1)) acceptAllPolicy = 140 := by
  classical
  simp only [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure, multiplicativePricing]
    norm_num
  · exact
      (integrable_dirac (a := (1 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (1 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (1 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact
      (integrable_dirac (a := (6 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (6 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (6 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_payment :
    singleStateTripPayment (theorem2AtomicMu 1)
        (multiplicativePricing (theorem2AtomicM 1)) (rejectShortTripsPolicy 1) =
      120 := by
  classical
  simp only [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one, six_mem_rejectShortTripsPolicy_one,
    ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure, multiplicativePricing]
    norm_num
  · simp
  · exact
      (integrable_dirac (a := (6 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (6 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (6 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_zero_acceptAll_integral
    (f : TripLength → ℝ) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2AtomicMu 0 =
      f ((1 : ℝ) / 2) := by
  classical
  rw [theorem2AtomicMu, setIntegral_dirac]
  simp only [one_half_mem_acceptAllPolicy, ↓reduceIte]

theorem theorem2AtomicMu_one_acceptAll_integral
    (f : TripLength → ℝ) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2AtomicMu 1 =
      ((1 : ℝ) / 2) * f 1 + ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2AtomicMu, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · exact (integrable_dirac (a := (1 : ℝ)) (f := f)
      (by simp : ‖f (1 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simp : ‖f (6 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectShortTripsPolicy 1, f τ ∂theorem2AtomicMu 1 =
      ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2AtomicMu, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one,
    six_mem_rejectShortTripsPolicy_one, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · simp
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simp : ‖f (6 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

/-- State-0 switch probability at the single state-0 atom. -/
def theorem2AtomicQ0 : ℝ := gn21SwitchProb ((1 : ℝ) / 4) 4 ((1 : ℝ) / 2)

/-- State-1 switch probability at trip length `1`. -/
def theorem2AtomicQ1 : ℝ := gn21SwitchProb 4 ((1 : ℝ) / 4) 1

/-- State-1 switch probability at trip length `6`. -/
def theorem2AtomicQ6 : ℝ := gn21SwitchProb 4 ((1 : ℝ) / 4) 6

theorem theorem2AtomicQ0_le :
    theorem2AtomicQ0 ≤ (1 : ℝ) / 17 := by
  rw [theorem2AtomicQ0, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (-(17 : ℝ) / 8) := Real.exp_nonneg _
  nlinarith

theorem theorem2AtomicQ1_gt :
    (16 : ℝ) / 21 < theorem2AtomicQ1 := by
  have hexp_lt : Real.exp (-(17 : ℝ) / 4) < (4 : ℝ) / 21 := by
    have hbase : (21 : ℝ) / 4 < Real.exp ((17 : ℝ) / 4) := by
      have hadd := Real.add_one_lt_exp
        (show ((17 : ℝ) / 4) ≠ 0 by norm_num)
      norm_num at hadd
      exact hadd
    have hinv :
        (Real.exp ((17 : ℝ) / 4))⁻¹ < ((21 : ℝ) / 4)⁻¹ :=
      inv_strictAnti₀ (by norm_num : 0 < (21 : ℝ) / 4) hbase
    have hexp_rewrite :
        Real.exp (-(17 : ℝ) / 4) = (Real.exp ((17 : ℝ) / 4))⁻¹ := by
      rw [show (-(17 : ℝ) / 4) = -((17 : ℝ) / 4) by ring, Real.exp_neg]
    rw [hexp_rewrite]
    norm_num at hinv ⊢
    exact hinv
  rw [theorem2AtomicQ1, paper_lemma2_switch_probability_formula]
  ring_nf
  nlinarith

theorem theorem2AtomicQ6_le :
    theorem2AtomicQ6 ≤ (16 : ℝ) / 17 := by
  rw [theorem2AtomicQ6, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (-(51 : ℝ) / 2) := Real.exp_nonneg _
  nlinarith

theorem theorem2AtomicQ_bounds :
    theorem2AtomicQ0 ≤ (1 : ℝ) / 17 ∧
      (16 : ℝ) / 21 < theorem2AtomicQ1 ∧
      theorem2AtomicQ6 ≤ (16 : ℝ) / 17 := ⟨theorem2AtomicQ0_le, theorem2AtomicQ1_gt, theorem2AtomicQ6_le⟩

theorem theorem2AtomicQ0_nonneg :
    0 ≤ theorem2AtomicQ0 :=
   paper_lemma2_switch_probability_nonneg ((1 : ℝ) / 4) 4 ((1 : ℝ) / 2)
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicQ1_nonneg :
    0 ≤ theorem2AtomicQ1 :=
   paper_lemma2_switch_probability_nonneg 4 ((1 : ℝ) / 4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicQ6_nonneg :
    0 ≤ theorem2AtomicQ6 :=
   paper_lemma2_switch_probability_nonneg 4 ((1 : ℝ) / 4) 6
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicExitWeight_zero_acceptAll :
    gn21ExitWeightIntegral (theorem2AtomicMu 0) 1 ((1 : ℝ) / 4) 4
        acceptAllPolicy =
      (1 : ℝ) / 4 + theorem2AtomicQ0 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ0
  rw [theorem2AtomicMu_zero_acceptAll_integral]
  ring

theorem theorem2AtomicExitWeight_one_acceptAll :
    gn21ExitWeightIntegral (theorem2AtomicMu 1) 50 4 ((1 : ℝ) / 4)
        acceptAllPolicy =
      4 + 25 * theorem2AtomicQ1 + 25 * theorem2AtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ1 theorem2AtomicQ6
  rw [theorem2AtomicMu_one_acceptAll_integral]
  ring

theorem theorem2AtomicExitWeight_one_rejectShort :
    gn21ExitWeightIntegral (theorem2AtomicMu 1) 50 4 ((1 : ℝ) / 4)
        (rejectShortTripsPolicy 1) =
      4 + 25 * theorem2AtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ6
  rw [theorem2AtomicMu_one_rejectShort_integral]
  ring

theorem theorem2AtomicScaledTime_zero_acceptAll :
    gn21ScaledStateTime (theorem2AtomicMu 0) 1 acceptAllPolicy =
      (3 : ℝ) / 2 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_zero_acceptAll_time]
  norm_num

theorem theorem2AtomicScaledTime_one_acceptAll :
    gn21ScaledStateTime (theorem2AtomicMu 1) 50 acceptAllPolicy = 176 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_one_acceptAll_time]
  norm_num

theorem theorem2AtomicScaledTime_one_rejectShort :
    gn21ScaledStateTime (theorem2AtomicMu 1) 50 (rejectShortTripsPolicy 1) =
      151 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_one_rejectShort_time]
  norm_num

theorem theorem2AtomicScaledEarning_zero_acceptAll :
    gn21ScaledStateEarning (theorem2AtomicMu 0) 1
        (multiplicativePricing (theorem2AtomicM 0)) acceptAllPolicy =
      2 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_zero_acceptAll_payment]
  norm_num

theorem theorem2AtomicScaledEarning_one_acceptAll :
    gn21ScaledStateEarning (theorem2AtomicMu 1) 50
        (multiplicativePricing (theorem2AtomicM 1)) acceptAllPolicy =
      7000 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_one_acceptAll_payment]
  norm_num

theorem theorem2AtomicScaledEarning_one_rejectShort :
    gn21ScaledStateEarning (theorem2AtomicMu 1) 50
        (multiplicativePricing (theorem2AtomicM 1)) (rejectShortTripsPolicy 1) =
      6000 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_one_rejectShort_payment]
  norm_num

theorem theorem2AtomicAggregateReward_acceptAll :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + theorem2AtomicQ0)
        (4 + 25 * theorem2AtomicQ1 + 25 * theorem2AtomicQ6)
        ((3 : ℝ) / 2) 176 2 7000 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [theorem2AtomicExitWeight_zero_acceptAll,
    theorem2AtomicExitWeight_one_acceptAll,
    theorem2AtomicScaledTime_zero_acceptAll,
    theorem2AtomicScaledTime_one_acceptAll,
    theorem2AtomicScaledEarning_zero_acceptAll,
    theorem2AtomicScaledEarning_one_acceptAll]

theorem theorem2AtomicAggregateReward_deviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 1) =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + theorem2AtomicQ0)
        (4 + 25 * theorem2AtomicQ6)
        ((3 : ℝ) / 2) 151 2 6000 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [theorem2AtomicExitWeight_zero_acceptAll,
    theorem2AtomicExitWeight_one_rejectShort,
    theorem2AtomicScaledTime_zero_acceptAll,
    theorem2AtomicScaledTime_one_rejectShort,
    theorem2AtomicScaledEarning_zero_acceptAll,
    theorem2AtomicScaledEarning_one_rejectShort]

theorem theorem2AtomicAggregate_algebra
    {a b c : ℝ}
    (ha_nonneg : 0 ≤ a)
    (hb_lower : (16 : ℝ) / 21 < b)
    (hc_nonneg : 0 ≤ c)
    (ha_upper : a ≤ (1 : ℝ) / 17)
    (hc_upper : c ≤ (16 : ℝ) / 17) :
    gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + a)
        (4 + 25 * b + 25 * c)
        ((3 : ℝ) / 2) 176 2 7000 <
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + a)
        (4 + 25 * c)
        ((3 : ℝ) / 2) 151 2 6000 := by
  have hQi_pos : 0 < (1 : ℝ) / 4 + a := by nlinarith
  have hQall_pos : 0 < 4 + 25 * b + 25 * c := by nlinarith
  have hQdev_pos : 0 < 4 + 25 * c := by nlinarith
  have hden_all_pos :
      0 < ((1 : ℝ) / 4 + a) * 176 +
          (4 + 25 * b + 25 * c) * ((3 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (176 : ℝ)),
      mul_pos hQall_pos (by norm_num : 0 < (3 : ℝ) / 2)]
  have hden_dev_pos :
      0 < ((1 : ℝ) / 4 + a) * 151 +
          (4 + 25 * c) * ((3 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (151 : ℝ)),
      mul_pos hQdev_pos (by norm_num : 0 < (3 : ℝ) / 2)]
  unfold gn21AggregateDynamicReward
  rw [div_lt_div_iff₀ hden_all_pos hden_dev_pos]
  ring_nf
  nlinarith

theorem theorem2AtomicAggregate_profitable :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 1) := by
  rw [theorem2AtomicAggregateReward_acceptAll,
    theorem2AtomicAggregateReward_deviation]
  exact theorem2AtomicAggregate_algebra theorem2AtomicQ0_nonneg
    theorem2AtomicQ1_gt theorem2AtomicQ6_nonneg theorem2AtomicQ0_le
    theorem2AtomicQ6_le

/--
Theorem 2 explicit measured endpoint: the atomic two-state instance with
multiplicative prices has a profitable dynamic deviation, so multiplicative
pricing is not dynamically incentive compatible.
-/
theorem paper_theorem2_multiplicative_measured_not_ic_explicit_atomic :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional theorem2AtomicMu theorem2AtomicArrival
        ((1 : ℝ) / 4) 4
        (fun i => multiplicativePricing (theorem2AtomicM i))) :=
    paper_theorem2_multiplicative_measured_not_ic_of_aggregate_witness
      theorem2AtomicMu theorem2AtomicArrival ((1 : ℝ) / 4) 4
      theorem2AtomicM
      { deviation := theorem2AtomicDeviation
        acceptAll_nondegenerate := by
          apply gn21MeasuredPairNondegenerate_of_positive_measure
          · rw [theorem2AtomicMu_zero_acceptAll_mass]
            norm_num
          · rw [theorem2AtomicMu_one_acceptAll_mass]
            norm_num
          · norm_num [theorem2AtomicArrival]
          · norm_num [theorem2AtomicArrival]
          · norm_num
          · norm_num
          · exact measurableSet_acceptAllPolicy
          · exact measurableSet_acceptAllPolicy
          · intro τ hτ
            exact hτ
          · intro τ hτ
            exact hτ
        deviation_nondegenerate := by
          apply gn21MeasuredPairNondegenerate_of_positive_measure
          · simpa [theorem2AtomicDeviation, theorem2AtomicMu_zero_acceptAll_mass]
          · simpa [theorem2AtomicDeviation, theorem2AtomicMu_one_rejectShort_mass]
          · norm_num [theorem2AtomicArrival]
          · norm_num [theorem2AtomicArrival]
          · norm_num
          · norm_num
          · exact measurableSet_acceptAllPolicy
          · exact measurableSet_rejectShortTripsPolicy 1
          · intro τ hτ
            exact hτ
          · intro τ hτ
            rcases hτ with ⟨hpos, _⟩
            exact hpos
        aggregate_profitable := by
          simpa [theorem2AtomicArrival, theorem2AtomicDeviation,
            theorem2AtomicM] using theorem2AtomicAggregate_profitable }

/-! ## A single explicit instance with profitable deviations in both states -/

/--
Trip-length distribution used for the two-state Theorem 2 witness with
profitable deviations in both states.  Each state has half its mass at trip
length `1` and half at trip length `6`.
-/
def theorem2BothStatesAtomicMix : Measure TripLength :=
  ((1 : ℝ≥0∞) / 2) • Measure.dirac (1 : ℝ) +
    ((1 : ℝ≥0∞) / 2) • Measure.dirac (6 : ℝ)

/-- The explicit two-state trip-length distributions used for the both-state witness. -/
def theorem2BothStatesAtomicMu : Fin 2 → Measure TripLength
  | _ => theorem2BothStatesAtomicMix

/-- Arrival rates in the both-state Theorem 2 witness. -/
def theorem2BothStatesAtomicArrival : Fin 2 → ℝ
  | 0 => 1
  | 1 => 2

/-- Multiplicative prices in the both-state Theorem 2 witness. -/
def theorem2BothStatesAtomicM : Fin 2 → ℝ
  | 0 => 1
  | 1 => 10

/-- Non-surge deviation: reject long trips above cutoff `2`. -/
def theorem2BothStatesAtomicNonsurgeDeviation : Fin 2 → TripPolicy
  | 0 => rejectLongTripsPolicy 2
  | 1 => acceptAllPolicy

/-- Surge deviation: reject short trips below cutoff `2`. -/
def theorem2BothStatesAtomicSurgeDeviation : Fin 2 → TripPolicy
  | 0 => acceptAllPolicy
  | 1 => rejectShortTripsPolicy 2

@[simp] theorem theorem2BothStates_one_mem_rejectLong_two :
    (1 : ℝ) ∈ rejectLongTripsPolicy 2 := by
  norm_num [rejectLongTripsPolicy]

@[simp] theorem theorem2BothStates_six_not_mem_rejectLong_two :
    (6 : ℝ) ∉ rejectLongTripsPolicy 2 := by
  norm_num [rejectLongTripsPolicy]

@[simp] theorem theorem2BothStates_one_not_mem_rejectShort_two :
    (1 : ℝ) ∉ rejectShortTripsPolicy 2 := by
  norm_num [rejectShortTripsPolicy]

@[simp] theorem theorem2BothStates_six_mem_rejectShort_two :
    (6 : ℝ) ∈ rejectShortTripsPolicy 2 := by
  norm_num [rejectShortTripsPolicy]

theorem theorem2BothStatesAtomicMix_acceptAll_mass :
    singleStateTripMass theorem2BothStatesAtomicMix acceptAllPolicy = 1 := by
  norm_num [singleStateTripMass, theorem2BothStatesAtomicMix,
    acceptAllPolicy, positiveTripLengths, ENNReal.toReal_add]

theorem theorem2BothStatesAtomicMix_rejectLong_mass :
    singleStateTripMass theorem2BothStatesAtomicMix (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  simp [singleStateTripMass, theorem2BothStatesAtomicMix]

theorem theorem2BothStatesAtomicMix_rejectShort_mass :
    singleStateTripMass theorem2BothStatesAtomicMix (rejectShortTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  simp [singleStateTripMass, theorem2BothStatesAtomicMix]

theorem theorem2BothStatesAtomicMix_acceptAll_integral
    (f : TripLength → ℝ) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2BothStatesAtomicMix =
      ((1 : ℝ) / 2) * f 1 + ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2BothStatesAtomicMix, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · exact (integrable_dirac (a := (1 : ℝ)) (f := f)
      (by simp : ‖f (1 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simpa using (enorm_lt_top : ‖f (6 : ℝ)‖ₑ < ∞))).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2BothStatesAtomicMix_rejectLong_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectLongTripsPolicy 2, f τ ∂theorem2BothStatesAtomicMix =
      ((1 : ℝ) / 2) * f 1 := by
  classical
  simp only [theorem2BothStatesAtomicMix, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [theorem2BothStates_one_mem_rejectLong_two,
    theorem2BothStates_six_not_mem_rejectLong_two, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · exact (integrable_dirac (a := (1 : ℝ)) (f := f)
      (by simp : ‖f (1 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · simp

theorem theorem2BothStatesAtomicMix_rejectShort_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectShortTripsPolicy 2, f τ ∂theorem2BothStatesAtomicMix =
      ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2BothStatesAtomicMix, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [theorem2BothStates_one_not_mem_rejectShort_two,
    theorem2BothStates_six_mem_rejectShort_two, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · simp
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simp : ‖f (6 : ℝ)‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

/-- Switch probability at trip length `1` for the both-state witness. -/
def theorem2BothStatesAtomicQ1 : ℝ := gn21SwitchProb ((1 : ℝ) / 4) ((1 : ℝ) / 4) 1

/-- Switch probability at trip length `6` for the both-state witness. -/
def theorem2BothStatesAtomicQ6 : ℝ := gn21SwitchProb ((1 : ℝ) / 4) ((1 : ℝ) / 4) 6

theorem theorem2BothStatesAtomicQ1_nonneg :
    0 ≤ theorem2BothStatesAtomicQ1 :=
   paper_lemma2_switch_probability_nonneg
    ((1 : ℝ) / 4) ((1 : ℝ) / 4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2BothStatesAtomicQ6_nonneg :
    0 ≤ theorem2BothStatesAtomicQ6 :=
   paper_lemma2_switch_probability_nonneg
    ((1 : ℝ) / 4) ((1 : ℝ) / 4) 6
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2BothStatesAtomicQ1_gt_one_six :
    (1 : ℝ) / 6 < theorem2BothStatesAtomicQ1 := by
  have hexp_lt : Real.exp (-(1 : ℝ) / 2) < (2 : ℝ) / 3 := by
    have hbase : (3 : ℝ) / 2 < Real.exp ((1 : ℝ) / 2) := by
      have hadd := Real.add_one_lt_exp
        (show ((1 : ℝ) / 2) ≠ 0 by norm_num)
      norm_num at hadd
      exact hadd
    have hinv :
        (Real.exp ((1 : ℝ) / 2))⁻¹ < ((3 : ℝ) / 2)⁻¹ :=
      inv_strictAnti₀ (by norm_num : 0 < (3 : ℝ) / 2) hbase
    have hexp_rewrite :
        Real.exp (-(1 : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2))⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.exp_neg]
    rw [hexp_rewrite]
    norm_num at hinv ⊢
    exact hinv
  rw [theorem2BothStatesAtomicQ1, paper_lemma2_switch_probability_formula]
  ring_nf
  nlinarith

theorem theorem2BothStatesAtomicQ6_le_half :
    theorem2BothStatesAtomicQ6 ≤ (1 : ℝ) / 2 := by
  rw [theorem2BothStatesAtomicQ6, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (-(3 : ℝ)) := Real.exp_nonneg _
  nlinarith

theorem theorem2BothStatesExitWeight_acceptAll_arrival_one :
    gn21ExitWeightIntegral theorem2BothStatesAtomicMix 1
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) acceptAllPolicy =
      (1 : ℝ) / 4 +
        (1 : ℝ) / 2 * theorem2BothStatesAtomicQ1 +
          (1 : ℝ) / 2 * theorem2BothStatesAtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2BothStatesAtomicQ1
    theorem2BothStatesAtomicQ6
  rw [theorem2BothStatesAtomicMix_acceptAll_integral]
  ring

theorem theorem2BothStatesExitWeight_rejectLong_arrival_one :
    gn21ExitWeightIntegral theorem2BothStatesAtomicMix 1
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 4 + (1 : ℝ) / 2 * theorem2BothStatesAtomicQ1 := by
  unfold gn21ExitWeightIntegral theorem2BothStatesAtomicQ1
  rw [theorem2BothStatesAtomicMix_rejectLong_integral]
  ring

theorem theorem2BothStatesExitWeight_acceptAll_arrival_two :
    gn21ExitWeightIntegral theorem2BothStatesAtomicMix 2
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) acceptAllPolicy =
      (1 : ℝ) / 4 + theorem2BothStatesAtomicQ1 +
        theorem2BothStatesAtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2BothStatesAtomicQ1
    theorem2BothStatesAtomicQ6
  rw [theorem2BothStatesAtomicMix_acceptAll_integral]
  ring

theorem theorem2BothStatesExitWeight_rejectShort_arrival_two :
    gn21ExitWeightIntegral theorem2BothStatesAtomicMix 2
        ((1 : ℝ) / 4) ((1 : ℝ) / 4) (rejectShortTripsPolicy 2) =
      (1 : ℝ) / 4 + theorem2BothStatesAtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2BothStatesAtomicQ6
  rw [theorem2BothStatesAtomicMix_rejectShort_integral]
  ring

theorem theorem2BothStatesTime_acceptAll :
    singleStateTripTime theorem2BothStatesAtomicMix acceptAllPolicy =
      (7 : ℝ) / 2 := by
  rw [singleStateTripTime, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_acceptAll_integral (fun τ : TripLength => τ) |>.trans
    (by norm_num)

theorem theorem2BothStatesTime_rejectLong :
    singleStateTripTime theorem2BothStatesAtomicMix (rejectLongTripsPolicy 2) =
      (1 : ℝ) / 2 := by
  rw [singleStateTripTime, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_rejectLong_integral (fun τ : TripLength => τ) |>.trans
    (by norm_num)

theorem theorem2BothStatesTime_rejectShort :
    singleStateTripTime theorem2BothStatesAtomicMix (rejectShortTripsPolicy 2) =
      3 := by
  rw [singleStateTripTime, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_rejectShort_integral (fun τ : TripLength => τ) |>.trans
    (by norm_num)

theorem theorem2BothStatesPayment_acceptAll_m_one :
    singleStateTripPayment theorem2BothStatesAtomicMix (multiplicativePricing 1)
        acceptAllPolicy = (7 : ℝ) / 2 := by
  rw [singleStateTripPayment, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_acceptAll_integral
    (multiplicativePricing 1) |>.trans (by norm_num [multiplicativePricing])

theorem theorem2BothStatesPayment_rejectLong_m_one :
    singleStateTripPayment theorem2BothStatesAtomicMix (multiplicativePricing 1)
        (rejectLongTripsPolicy 2) = (1 : ℝ) / 2 := by
  rw [singleStateTripPayment, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_rejectLong_integral
    (multiplicativePricing 1) |>.trans (by norm_num [multiplicativePricing])

theorem theorem2BothStatesPayment_acceptAll_m_ten :
    singleStateTripPayment theorem2BothStatesAtomicMix (multiplicativePricing 10)
        acceptAllPolicy = 35 := by
  rw [singleStateTripPayment, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_acceptAll_integral
    (multiplicativePricing 10) |>.trans (by norm_num [multiplicativePricing])

theorem theorem2BothStatesPayment_rejectShort_m_ten :
    singleStateTripPayment theorem2BothStatesAtomicMix (multiplicativePricing 10)
        (rejectShortTripsPolicy 2) = 30 := by
  rw [singleStateTripPayment, theorem2BothStatesAtomicMix]
  exact theorem2BothStatesAtomicMix_rejectShort_integral
    (multiplicativePricing 10) |>.trans (by norm_num [multiplicativePricing])

theorem theorem2BothStatesScaledTime_zero_acceptAll :
    gn21ScaledStateTime (theorem2BothStatesAtomicMu 0)
        (theorem2BothStatesAtomicArrival 0) acceptAllPolicy = (9 : ℝ) / 2 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesTime_acceptAll]

theorem theorem2BothStatesScaledTime_zero_rejectLong :
    gn21ScaledStateTime (theorem2BothStatesAtomicMu 0)
        (theorem2BothStatesAtomicArrival 0) (rejectLongTripsPolicy 2) =
      (3 : ℝ) / 2 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesTime_rejectLong]

theorem theorem2BothStatesScaledTime_one_acceptAll :
    gn21ScaledStateTime (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 1) acceptAllPolicy = 8 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesTime_acceptAll]

theorem theorem2BothStatesScaledTime_one_rejectShort :
    gn21ScaledStateTime (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 1) (rejectShortTripsPolicy 2) = 7 := by
  norm_num [gn21ScaledStateTime, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesTime_rejectShort]

theorem theorem2BothStatesScaledEarning_zero_acceptAll :
    gn21ScaledStateEarning (theorem2BothStatesAtomicMu 0)
        (theorem2BothStatesAtomicArrival 0)
        (multiplicativePricing (theorem2BothStatesAtomicM 0)) acceptAllPolicy =
      (7 : ℝ) / 2 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesAtomicM,
    theorem2BothStatesPayment_acceptAll_m_one]

theorem theorem2BothStatesScaledEarning_zero_rejectLong :
    gn21ScaledStateEarning (theorem2BothStatesAtomicMu 0)
        (theorem2BothStatesAtomicArrival 0)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (rejectLongTripsPolicy 2) = (1 : ℝ) / 2 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesAtomicM,
    theorem2BothStatesPayment_rejectLong_m_one]

theorem theorem2BothStatesScaledEarning_one_acceptAll :
    gn21ScaledStateEarning (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 1)
        (multiplicativePricing (theorem2BothStatesAtomicM 1)) acceptAllPolicy =
      70 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesAtomicM,
    theorem2BothStatesPayment_acceptAll_m_ten]

theorem theorem2BothStatesScaledEarning_one_rejectShort :
    gn21ScaledStateEarning (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 1)
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        (rejectShortTripsPolicy 2) = 60 := by
  norm_num [gn21ScaledStateEarning, theorem2BothStatesAtomicMu,
    theorem2BothStatesAtomicArrival, theorem2BothStatesAtomicM,
    theorem2BothStatesPayment_rejectShort_m_ten]

theorem theorem2BothStatesAggregateReward_acceptAll :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 +
          (1 : ℝ) / 2 * theorem2BothStatesAtomicQ1 +
            (1 : ℝ) / 2 * theorem2BothStatesAtomicQ6)
        ((1 : ℝ) / 4 + theorem2BothStatesAtomicQ1 +
          theorem2BothStatesAtomicQ6)
        ((9 : ℝ) / 2) 8 ((7 : ℝ) / 2) 70 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicArrival,
    theorem2BothStatesAtomicM]
  rw [theorem2BothStatesExitWeight_acceptAll_arrival_one,
    theorem2BothStatesExitWeight_acceptAll_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesTime_acceptAll,
    theorem2BothStatesPayment_acceptAll_m_one,
    theorem2BothStatesPayment_acceptAll_m_ten]

theorem theorem2BothStatesAggregateReward_nonsurgeDeviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        (rejectLongTripsPolicy 2) acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * theorem2BothStatesAtomicQ1)
        ((1 : ℝ) / 4 + theorem2BothStatesAtomicQ1 +
          theorem2BothStatesAtomicQ6)
        ((3 : ℝ) / 2) 8 ((1 : ℝ) / 2) 70 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicArrival,
    theorem2BothStatesAtomicM]
  rw [theorem2BothStatesExitWeight_rejectLong_arrival_one,
    theorem2BothStatesExitWeight_acceptAll_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesTime_rejectLong,
    theorem2BothStatesTime_acceptAll,
    theorem2BothStatesPayment_rejectLong_m_one,
    theorem2BothStatesPayment_acceptAll_m_ten]

theorem theorem2BothStatesAggregateReward_surgeDeviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 2) =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 +
          (1 : ℝ) / 2 * theorem2BothStatesAtomicQ1 +
            (1 : ℝ) / 2 * theorem2BothStatesAtomicQ6)
        ((1 : ℝ) / 4 + theorem2BothStatesAtomicQ6)
        ((9 : ℝ) / 2) 7 ((7 : ℝ) / 2) 60 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  simp only [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicArrival,
    theorem2BothStatesAtomicM]
  rw [theorem2BothStatesExitWeight_acceptAll_arrival_one,
    theorem2BothStatesExitWeight_rejectShort_arrival_two]
  norm_num [gn21ScaledStateTime, gn21ScaledStateEarning,
    theorem2BothStatesTime_acceptAll,
    theorem2BothStatesTime_rejectShort,
    theorem2BothStatesPayment_acceptAll_m_one,
    theorem2BothStatesPayment_rejectShort_m_ten]

theorem theorem2BothStatesAggregate_nonsurge_algebra
    {a b : ℝ}
    (ha_nonneg : 0 ≤ a)
    (hb_nonneg : 0 ≤ b)
    (hb_upper : b ≤ (1 : ℝ) / 2) :
    gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b)
        ((1 : ℝ) / 4 + a + b)
        ((9 : ℝ) / 2) 8 ((7 : ℝ) / 2) 70 <
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a)
        ((1 : ℝ) / 4 + a + b)
        ((3 : ℝ) / 2) 8 ((1 : ℝ) / 2) 70 := by
  have hQi_all_pos :
      0 < (1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b := by
    nlinarith
  have hQi_dev_pos : 0 < (1 : ℝ) / 4 + (1 : ℝ) / 2 * a := by
    nlinarith
  have hQj_pos : 0 < (1 : ℝ) / 4 + a + b := by
    nlinarith
  have hden_all_pos :
      0 <
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b) * 8 +
          ((1 : ℝ) / 4 + a + b) * ((9 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_all_pos (by norm_num : 0 < (8 : ℝ)),
      mul_pos hQj_pos (by norm_num : 0 < (9 : ℝ) / 2)]
  have hden_dev_pos :
      0 <
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a) * 8 +
          ((1 : ℝ) / 4 + a + b) * ((3 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_dev_pos (by norm_num : 0 < (8 : ℝ)),
      mul_pos hQj_pos (by norm_num : 0 < (3 : ℝ) / 2)]
  unfold gn21AggregateDynamicReward
  rw [div_lt_div_iff₀ hden_all_pos hden_dev_pos]
  ring_nf
  nlinarith

theorem theorem2BothStatesAggregate_surge_algebra
    {a b : ℝ}
    (ha_lower : (1 : ℝ) / 6 < a)
    (hb_nonneg : 0 ≤ b)
    (hb_upper : b ≤ (1 : ℝ) / 2) :
    gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b)
        ((1 : ℝ) / 4 + a + b)
        ((9 : ℝ) / 2) 8 ((7 : ℝ) / 2) 70 <
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b)
        ((1 : ℝ) / 4 + b)
        ((9 : ℝ) / 2) 7 ((7 : ℝ) / 2) 60 := by
  have ha_nonneg : 0 ≤ a := le_of_lt (lt_trans (by norm_num : 0 < (1 : ℝ) / 6) ha_lower)
  have hQi_pos :
      0 < (1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b := by
    nlinarith
  have hQj_all_pos : 0 < (1 : ℝ) / 4 + a + b := by
    nlinarith
  have hQj_dev_pos : 0 < (1 : ℝ) / 4 + b := by
    nlinarith
  have hden_all_pos :
      0 <
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b) * 8 +
          ((1 : ℝ) / 4 + a + b) * ((9 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (8 : ℝ)),
      mul_pos hQj_all_pos (by norm_num : 0 < (9 : ℝ) / 2)]
  have hden_dev_pos :
      0 <
        ((1 : ℝ) / 4 + (1 : ℝ) / 2 * a + (1 : ℝ) / 2 * b) * 7 +
          ((1 : ℝ) / 4 + b) * ((9 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (7 : ℝ)),
      mul_pos hQj_dev_pos (by norm_num : 0 < (9 : ℝ) / 2)]
  unfold gn21AggregateDynamicReward
  rw [div_lt_div_iff₀ hden_all_pos hden_dev_pos]
  ring_nf
  nlinarith

theorem theorem2BothStatesAggregate_profitable_nonsurge :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        (rejectLongTripsPolicy 2) acceptAllPolicy := by
  rw [theorem2BothStatesAggregateReward_acceptAll,
    theorem2BothStatesAggregateReward_nonsurgeDeviation]
  exact theorem2BothStatesAggregate_nonsurge_algebra
    theorem2BothStatesAtomicQ1_nonneg theorem2BothStatesAtomicQ6_nonneg
    theorem2BothStatesAtomicQ6_le_half

theorem theorem2BothStatesAggregate_profitable_surge :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 2) := by
  rw [theorem2BothStatesAggregateReward_acceptAll,
    theorem2BothStatesAggregateReward_surgeDeviation]
  exact theorem2BothStatesAggregate_surge_algebra
    theorem2BothStatesAtomicQ1_gt_one_six theorem2BothStatesAtomicQ6_nonneg
    theorem2BothStatesAtomicQ6_le_half

theorem theorem2BothStatesAcceptAll_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
      (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      acceptAllPolicy acceptAllPolicy := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_acceptAll_mass]
    norm_num
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_acceptAll_mass]
    norm_num
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num
  · norm_num
  · exact measurableSet_acceptAllPolicy
  · exact measurableSet_acceptAllPolicy
  · intro τ hτ
    exact hτ
  · intro τ hτ
    exact hτ

theorem theorem2BothStatesNonsurgeDeviation_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
      (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      (rejectLongTripsPolicy 2) acceptAllPolicy := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_rejectLong_mass]
    norm_num
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_acceptAll_mass]
    norm_num
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num
  · norm_num
  · exact measurableSet_rejectLongTripsPolicy 2
  · exact measurableSet_acceptAllPolicy
  · intro τ hτ
    exact hτ.1
  · intro τ hτ
    exact hτ

theorem theorem2BothStatesSurgeDeviation_nondegenerate :
    GN21MeasuredPairNondegenerate
      (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
      (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
      ((1 : ℝ) / 4) ((1 : ℝ) / 4)
      acceptAllPolicy (rejectShortTripsPolicy 2) := by
  apply gn21MeasuredPairNondegenerate_of_positive_measure
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_acceptAll_mass]
    norm_num
  · rw [theorem2BothStatesAtomicMu, theorem2BothStatesAtomicMix_rejectShort_mass]
    norm_num
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num [theorem2BothStatesAtomicArrival]
  · norm_num
  · norm_num
  · exact measurableSet_acceptAllPolicy
  · exact measurableSet_rejectShortTripsPolicy 2
  · intro τ hτ
    exact hτ
  · intro τ hτ
    exact hτ.1

/--
Theorem 2 explicit both-state endpoint: in one atomic multiplicative-pricing
instance, accept-all is beaten by a positive finite reject-long cutoff in the
non-surge state and also by a positive finite reject-short cutoff in the surge
state.
-/
theorem paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_atomic :
    dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
          theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
        theorem2BothStatesAtomicNonsurgeDeviation ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
          theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
        theorem2BothStatesAtomicSurgeDeviation := by
  constructor
  · unfold dynamicProfitableDeviation gn21MeasuredDynamicRewardFunctional
    exact
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy acceptAllPolicy
        (theorem2BothStatesAtomicNonsurgeDeviation 0)
        (theorem2BothStatesAtomicNonsurgeDeviation 1)
        theorem2BothStatesAcceptAll_nondegenerate
        theorem2BothStatesNonsurgeDeviation_nondegenerate
        (by
          simpa [theorem2BothStatesAtomicNonsurgeDeviation]
            using theorem2BothStatesAggregate_profitable_nonsurge)
  · unfold dynamicProfitableDeviation gn21MeasuredDynamicRewardFunctional
    exact
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (theorem2BothStatesAtomicMu 0) (theorem2BothStatesAtomicMu 1)
        (theorem2BothStatesAtomicArrival 0) (theorem2BothStatesAtomicArrival 1)
        ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (multiplicativePricing (theorem2BothStatesAtomicM 0))
        (multiplicativePricing (theorem2BothStatesAtomicM 1))
        acceptAllPolicy acceptAllPolicy
        (theorem2BothStatesAtomicSurgeDeviation 0)
        (theorem2BothStatesAtomicSurgeDeviation 1)
        theorem2BothStatesAcceptAll_nondegenerate
        theorem2BothStatesSurgeDeviation_nondegenerate
        (by
          simpa [theorem2BothStatesAtomicSurgeDeviation]
            using theorem2BothStatesAggregate_profitable_surge)

/--
The same both-state witness, with the positive finite cutoffs made explicit in
the theorem statement.
-/
theorem paper_theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_in_both_states_explicit_atomic :
    ((0 < (2 : ℝ) ∧
        rejectsLongTrips 2 (theorem2BothStatesAtomicNonsurgeDeviation 0)) ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
          theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
        theorem2BothStatesAtomicNonsurgeDeviation) ∧
      ((0 < (2 : ℝ) ∧
          rejectsShortTrips 2 (theorem2BothStatesAtomicSurgeDeviation 1)) ∧
        dynamicProfitableDeviation
          (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
            theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
            (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
          theorem2BothStatesAtomicSurgeDeviation) := by
  refine ⟨⟨⟨by norm_num, ?_⟩,
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_atomic.1⟩,
    ⟨⟨by norm_num, ?_⟩,
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_atomic.2⟩⟩
  · intro τ hτ
    simp [theorem2BothStatesAtomicNonsurgeDeviation, rejectLongTripsPolicy, hτ]
  · intro τ hτ
    simp [theorem2BothStatesAtomicSurgeDeviation, rejectShortTripsPolicy]

/--
The same both-state witness refutes dynamic incentive compatibility for the
measured multiplicative reward.
-/
theorem paper_theorem2_multiplicative_measured_not_ic_both_states_explicit_atomic :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
        theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesAtomicM i))) :=
    not_dynamicIncentiveCompatible_of_profitableDeviation
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
        theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
      theorem2BothStatesAtomicNonsurgeDeviation
      paper_theorem2_multiplicative_measured_profitable_deviations_in_both_states_explicit_atomic.1

end

end GN21DriverSurgePricing
