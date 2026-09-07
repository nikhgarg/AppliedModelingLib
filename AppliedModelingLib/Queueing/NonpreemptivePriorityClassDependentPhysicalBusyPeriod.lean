import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentBusyPeriod
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentEventClock

/-!
# Physical busy periods on the class-dependent event clock

This module transports the finite-start busy-period estimate from an abstract
product of uniformized event labels and exponential holding times to the
canonical physical event-race process.  It remains a finite-start result and
makes no stationary or Palm identification.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The finite-start busy holding time evaluated on the canonical physical
class-dependent event race. -/
noncomputable def classDependentNonpreemptivePriorityEventRaceBusyHoldingTime
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) → ENNReal :=
  fun path => classDependentNonpreemptivePriorityBusyHoldingTime initial
    (Probability.finiteExponentialRaceWinnerGapPaths path)

/-- The physical event-race busy holding time is Borel measurable. -/
theorem measurable_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    Measurable (classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial) := by
  exact (measurable_classDependentNonpreemptivePriorityBusyHoldingTime initial).comp
    Probability.measurable_finiteExponentialRaceWinnerGapPaths

/-- Under strict load, the canonical physical event race has finite expected
total time spent in its finite-start busy period. -/
theorem lintegral_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ path, classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial path ∂
      classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService) ≠ ⊤ := by
  have hsplit := classDependentNonpreemptivePriorityEventRaceWinnerGapPaths_hasLaw
    arrivalRate (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  rw [show (∫⁻ path,
      classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial path ∂
        classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) =
      ∫⁻ z, classDependentNonpreemptivePriorityBusyHoldingTime initial z ∂
        ((Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure).prod
          (Probability.IIDStream.measure
            (ProbabilityTheory.expMeasure
              (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
                (exponentialServiceRate meanService)))) ) by
      simpa [classDependentNonpreemptivePriorityEventRaceBusyHoldingTime,
        Function.comp_def] using
        (hsplit.lintegral_comp
          (measurable_classDependentNonpreemptivePriorityBusyHoldingTime initial).aemeasurable)]
  simpa [classDependentNonpreemptivePriorityTotalEventRate_eq] using
    (lintegral_classDependentNonpreemptivePriorityBusyHoldingTime_ne_top
      arrivalRate meanService hn harrivalRate hmeanService hstable initial)

/-- The finite-start physical event-race busy holding time is almost surely
finite under strict load. -/
theorem ae_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime_lt_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∀ᵐ path ∂classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService),
      classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial path < ⊤ := by
  apply MeasureTheory.ae_lt_top
  · exact measurable_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial
  · exact lintegral_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
      arrivalRate meanService hn harrivalRate hmeanService hstable initial

/-- The finite-start mean-work busy charge evaluated on the canonical physical
class-dependent event race. -/
noncomputable def classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (initial : NonpreemptivePriorityState n) :
    (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) → ENNReal :=
  fun path => classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
    arrivalRate meanService initial
    (Probability.finiteExponentialRaceWinnerGapPaths path)

/-- The physical event-race mean-work busy charge is Borel measurable. -/
theorem measurable_classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (initial : NonpreemptivePriorityState n) :
    Measurable (classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge
      arrivalRate meanService initial) := by
  exact (measurable_classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
    arrivalRate meanService initial).comp
      Probability.measurable_finiteExponentialRaceWinnerGapPaths

/-- Strict load gives finite expected physical-time mean-work charge during
the finite-start busy period of the canonical class-dependent event race. -/
theorem lintegral_classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ path,
      classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge
        arrivalRate meanService initial path ∂
      classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService) ≠ ⊤ := by
  have hsplit := classDependentNonpreemptivePriorityEventRaceWinnerGapPaths_hasLaw
    arrivalRate (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  rw [show (∫⁻ path,
      classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge
        arrivalRate meanService initial path ∂
        classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) =
      ∫⁻ z, classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
        arrivalRate meanService initial z ∂
        ((Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure).prod
          (Probability.IIDStream.measure
            (ProbabilityTheory.expMeasure
              (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
                (exponentialServiceRate meanService)))) ) by
      simpa [classDependentNonpreemptivePriorityEventRaceMeanWorkBusyHoldingCharge,
        Function.comp_def] using
        (hsplit.lintegral_comp
          (measurable_classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
            arrivalRate meanService initial).aemeasurable)]
  simpa [classDependentNonpreemptivePriorityTotalEventRate_eq] using
    (lintegral_classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge_ne_top
      arrivalRate meanService hn harrivalRate hmeanService hstable initial)

/-- The busy event at a finite event horizon with an independent external
initial state and the uniformized event-label stream. -/
def externalInitialClassDependentNonpreemptivePriorityBusyEvent
    {σ : Type*} [MeasurableSpace σ] {n : ℕ}
    (initial : σ → NonpreemptivePriorityState n) (horizon : ℕ) :
    Set (σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
  Probability.IIDStream.externalInitialFiniteEventTrajectoryEventSet initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy horizon

/-- Physical busy holding time for an independent random initial state, an IID
uniformized event path, and independent total-clock gaps. -/
noncomputable def externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
    {σ : Type*} [MeasurableSpace σ] {n : ℕ}
    (initial : σ → NonpreemptivePriorityState n) :
    ((σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) × (ℕ → ℝ)) → ENNReal :=
  Probability.IIDStream.externalWeightedENNReward
    (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial) ENNReal.ofReal

/-- The random-initial-state physical busy holding time is Borel when the
finite-horizon busy events are Borel on the explicit external-event carrier. -/
theorem measurable_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
    {σ : Type*} [MeasurableSpace σ] {n : ℕ}
    (initial : σ → NonpreemptivePriorityState n)
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon)) :
    Measurable (externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial) := by
  unfold externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
  exact Measurable.ennreal_tsum fun horizon =>
    Probability.IIDStream.measurable_externalWeightedENNRewardSummand
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial)
      ENNReal.ofReal hbusy ENNReal.measurable_ofReal horizon

/-- Strict load gives finite expected physical busy holding time from an
independent random initial state whenever its Lyapunov work bound is
integrable.  The event measurability and the finite expected initial work are
kept explicit: a stationary-Palm application must prove both bridges. -/
theorem lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_ne_top
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : σ → NonpreemptivePriorityState n)
    (hcount : Measurable (fun z : σ ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2))
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon))
    (hinitial : ∫⁻ x, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService (initial x) /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂ρ ≠ ⊤) :
    ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂(
      (ρ.prod (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService))))) ≠ ⊤ := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let rate : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let E : ℕ → Set (σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
    externalInitialClassDependentNonpreemptivePriorityBusyEvent initial
  letI : IsProbabilityMeasure M := by
    dsimp [M, Probability.IIDStream.measure]
    infer_instance
  have hrate : 0 < rate := by
    dsimp [rate]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hcountFinite : ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
        (ρ.prod M) ≠ ⊤ := by
    simpa [M, law] using
      (lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_ne_top
        ρ arrivalRate meanService hn harrivalRate hmeanService hstable initial hcount hinitial)
  have hcountEq : ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
        (ρ.prod M) = ∑' horizon, (ρ.prod M) (E horizon) := by
    simpa [classDependentNonpreemptivePriorityBusyEventCount, M, law, E,
      externalInitialClassDependentNonpreemptivePriorityBusyEvent] using
      (Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryEventCount
        ρ law initial stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy hbusy)
  have htail : ∑' horizon, (ρ.prod M) (E horizon) ≠ ⊤ := by
    rw [← hcountEq]
    exact hcountFinite
  have hsummable : Summable fun horizon => (ρ.prod M).real (E horizon) :=
    ENNReal.summable_toReal htail
  have hgapNonnegative : ∀ᵐ x ∂μ, 0 ≤ x := by
    let exponentialModel : Probability.Exponential.Model := ⟨rate, hrate⟩
    simpa [μ, exponentialModel] using exponentialModel.ae_nonnegative
  have hgapLIntegral : ∫⁻ x, ENNReal.ofReal x ∂μ = ENNReal.ofReal (1 / rate) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Probability.integrable_id_expMeasure hrate) hgapNonnegative,
      Probability.integral_id_expMeasure hrate]
  have hgapFinite : ∫⁻ x, ENNReal.ofReal x ∂μ ≠ ⊤ := by
    rw [hgapLIntegral]
    exact ENNReal.ofReal_ne_top
  simpa [externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime,
    M, μ, law, rate, E] using
    (Probability.IIDStream.lintegral_externalWeightedENNReward_ne_top
      (ρ.prod M) μ E ENNReal.ofReal hbusy ENNReal.measurable_ofReal
      hsummable hgapFinite)

/-- On the independent uniformized-event and exponential-clock carrier, the
expected physical busy time is exactly the expected number of busy event
slots times the reciprocal total event rate.  This is a Tonelli identity,
not an asymptotic renewal-reward assertion: it is the normalization identity
needed to turn a finite busy excursion into an occupation law. -/
theorem lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_eq
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : σ → NonpreemptivePriorityState n)
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon)) :
    ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂(
      (ρ.prod (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService))))) =
      (∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
          (ρ.prod (Probability.IIDStream.measure
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService)).toMeasure))) *
        ENNReal.ofReal (1 /
          classDependentNonpreemptivePriorityTotalEventRate arrivalRate
            (exponentialServiceRate meanService)) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let rate : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let E : ℕ → Set (σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
    externalInitialClassDependentNonpreemptivePriorityBusyEvent initial
  letI : IsProbabilityMeasure M := by
    dsimp [M, law, Probability.IIDStream.measure]
    infer_instance
  have hrate : 0 < rate := by
    dsimp [rate]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hcount :
      ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
          (ρ.prod M) = ∑' horizon, (ρ.prod M) (E horizon) := by
    simpa [M, law, E, externalInitialClassDependentNonpreemptivePriorityBusyEvent,
      classDependentNonpreemptivePriorityBusyEventCount] using
      (Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryEventCount
        ρ law initial stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy hbusy)
  have hgapNonnegative : ∀ᵐ x ∂μ, 0 ≤ x := by
    let exponentialModel : Probability.Exponential.Model := ⟨rate, hrate⟩
    simpa [μ, exponentialModel] using exponentialModel.ae_nonnegative
  have hgap : ∫⁻ x, ENNReal.ofReal x ∂μ = ENNReal.ofReal (1 / rate) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Probability.integrable_id_expMeasure hrate) hgapNonnegative,
      Probability.integral_id_expMeasure hrate]
  calc
    ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂
        ((ρ.prod M).prod (Probability.IIDStream.measure μ)) =
        (∑' horizon, (ρ.prod M) (E horizon)) *
          ∫⁻ x, ENNReal.ofReal x ∂μ := by
            simpa [externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime,
              E] using
              (Probability.IIDStream.lintegral_externalWeightedENNReward
                (ρ.prod M) μ E ENNReal.ofReal hbusy ENNReal.measurable_ofReal)
    _ = (∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
          classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
            (ρ.prod M)) * ∫⁻ x, ENNReal.ofReal x ∂μ := by rw [← hcount]
    _ = (∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
          classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
            (ρ.prod M)) * ENNReal.ofReal (1 / rate) := by rw [hgap]

/-- An initial family that is active almost surely has a strictly positive
physical busy-excursion normalizer.  Combined with the strict-load finite
bound, this supplies a genuine finite nonzero denominator for a regenerative
occupation construction; it does not by itself identify that occupation law
with a stationary Palm queue. -/
theorem zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_of_active
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : σ → NonpreemptivePriorityState n)
    (hactive : ∀ x, (initial x).active ≠ none)
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon)) :
    0 < ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂(
      (ρ.prod (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService))))) := by
  have hcount :=
    one_le_lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_of_active
      ρ arrivalRate meanService hn harrivalRate hmeanService initial hactive
  have hrate : 0 < classDependentNonpreemptivePriorityTotalEventRate arrivalRate
      (exponentialServiceRate meanService) :=
    classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  rw [lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_eq
    ρ arrivalRate meanService hn harrivalRate hmeanService initial hbusy]
  exact ENNReal.mul_pos
    (lt_of_lt_of_le zero_lt_one hcount).ne'
    (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hrate)).ne'

/-- The random-initial-state busy holding time evaluated directly on the
canonical physical event race. -/
noncomputable def externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
    {σ : Type*} [MeasurableSpace σ] {n : ℕ}
    (initial : σ → NonpreemptivePriorityState n) :
    (σ × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n)) → ENNReal :=
  fun z => externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial
    ((z.1, Probability.finiteExponentialRaceWinnerPath z.2),
      Probability.finiteExponentialRaceGapPath z.2)

/-- Splitting each canonical exponential race into its winner label and gap
path preserves the independent product law, also in the presence of an
independent initial-state carrier. -/
theorem measurePreserving_externalInitialClassDependentNonpreemptivePriorityEventRace_to_split
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i) :
    MeasurePreserving
      (fun z : σ × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) =>
        ((z.1, Probability.finiteExponentialRaceWinnerPath z.2),
          Probability.finiteExponentialRaceGapPath z.2))
      (ρ.prod (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)))
      ((ρ.prod (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService))))) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let rate : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let G : Measure (ℕ → ℝ) := Probability.IIDStream.measure μ
  let R : Measure (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) :=
    classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure M := by
    dsimp [M, law, Probability.IIDStream.measure]
    infer_instance
  have hrate : 0 < rate := by
    dsimp [rate]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure G := by
    dsimp [G, Probability.IIDStream.measure]
    infer_instance
  have hweightTotal : 0 < Probability.finiteExponentialRaceTotalRate
      (classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService)) := by
    change 0 < classDependentNonpreemptivePriorityTotalEventRate arrivalRate
      (exponentialServiceRate meanService)
    exact hrate
  letI : IsProbabilityMeasure R := by
    dsimp [R, classDependentNonpreemptivePriorityEventRaceMeasure]
    exact Probability.isProbabilityMeasure_finiteExponentialRaceEventMeasure
      (classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService))
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate
        (exponentialServiceRate meanService) harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      hweightTotal
  have hsplitLaw := classDependentNonpreemptivePriorityEventRaceWinnerGapPaths_hasLaw
    arrivalRate (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  have hsplit : MeasurePreserving Probability.finiteExponentialRaceWinnerGapPaths
      R (M.prod G) := by
    refine ⟨Probability.measurable_finiteExponentialRaceWinnerGapPaths, ?_⟩
    simpa [R, M, G, μ, law, rate] using hsplitLaw.map_eq
  have hproduct : MeasurePreserving
      (Prod.map id Probability.finiteExponentialRaceWinnerGapPaths)
      (ρ.prod R) (ρ.prod (M.prod G)) :=
    (MeasurePreserving.id ρ).prod hsplit
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      (σ × ((ℕ → ClassDependentNonpreemptivePriorityEvent n) × (ℕ → ℝ))) →
        (σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) × (ℕ → ℝ))
      (ρ.prod (M.prod G)) ((ρ.prod M).prod G) :=
    (measurePreserving_prodAssoc ρ M G).symm
  simpa [Function.comp_def, R, M, G, μ, law, rate] using hassoc.comp hproduct

/-- Strict load transports the random-initial-state physical busy-period bound
to the canonical event race.  The initial state is independent of the race by
the product carrier; applying this theorem to a stationary construction still
requires proving that product representation and its finite-work hypothesis. -/
theorem lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : σ → NonpreemptivePriorityState n)
    (hcount : Measurable (fun z : σ ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2))
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon))
    (hinitial : ∫⁻ x, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService (initial x) /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂ρ ≠ ⊤) :
    ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial z ∂
      (ρ.prod (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))) ≠ ⊤ := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let rate : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ₀ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let G : Measure (ℕ → ℝ) := Probability.IIDStream.measure μ₀
  let R : Measure (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) :=
    classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  have hmap : MeasurePreserving
      (fun z : σ × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) =>
        ((z.1, Probability.finiteExponentialRaceWinnerPath z.2),
          Probability.finiteExponentialRaceGapPath z.2))
      (ρ.prod R) ((ρ.prod M).prod G) := by
    simpa [R, M, G, μ₀, law, rate] using
      (measurePreserving_externalInitialClassDependentNonpreemptivePriorityEventRace_to_split
        ρ arrivalRate meanService hn harrivalRate hmeanService)
  rw [show (∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial z ∂
        (ρ.prod R)) =
      ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂
        ((ρ.prod M).prod G) by
      simpa [externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime,
        Function.comp_def] using
        hmap.hasLaw.lintegral_comp
          (measurable_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
            initial hbusy).aemeasurable]
  simpa [R, M, G, μ₀, law, rate] using
    (lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_ne_top
      ρ arrivalRate meanService hn harrivalRate hmeanService hstable initial
      hcount hbusy hinitial)

/-- An active independent initial family has strictly positive physical busy
time also on the canonical exponential-race carrier.  The proof transports
the independent winner-gap normalization along the exact race splitting law. -/
theorem zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_of_active
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : σ → NonpreemptivePriorityState n)
    (hactive : ∀ x, (initial x).active ≠ none)
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon)) :
    0 < ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial z ∂
      (ρ.prod (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))) := by
  have hmap :=
    measurePreserving_externalInitialClassDependentNonpreemptivePriorityEventRace_to_split
      ρ arrivalRate meanService hn harrivalRate hmeanService
  rw [show (∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial z ∂
        (ρ.prod (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))) =
      ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime initial z ∂
        ((ρ.prod (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
          (Probability.IIDStream.measure
            (ProbabilityTheory.expMeasure
              (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
                (exponentialServiceRate meanService))))) by
      simpa [externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime,
        Function.comp_def] using
        hmap.hasLaw.lintegral_comp
          (measurable_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
            initial hbusy).aemeasurable]
  exact zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_of_active
    ρ arrivalRate meanService hn harrivalRate hmeanService initial hactive hbusy

end

end AppliedModelingLib.Queueing
