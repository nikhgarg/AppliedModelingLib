import GN21DriverSurgePricing.MarkedStoppedPathRestart
import GN21DriverSurgePricing.RenewalCycleSourceBridge

/-!
# Raw GN21 marked stopped-path bridge

This module connects one literal raw GN21 clock/mark product seed to the
marked IID stopped-path result.  It does not introduce a post-thinning seed:
the paired stream is built from the source clock and the source trip-mark
stream on the original raw product space.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace MarkedRestart

/-- The literal pair stream obtained from one raw GN21 clock and one
policy-classified raw trip-mark stream. -/
def gn21RawMarkedPairStream
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Nat -> Step :=
  fun seed n =>
    (gn21RawCycleClock clock n seed,
      gn21AcceptanceMark sigma (gn21RawCycleMark state n seed))

theorem measurable_gn21RawMarkedPairStream
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawMarkedPairStream clock state sigma) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
      ((measurable_pi_apply clock).comp measurable_fst)).prodMk
    ((measurable_gn21AcceptanceMark sigma hsigma).comp
      ((measurable_pi_apply n).comp
        ((measurable_pi_apply state).comp measurable_snd)))

private theorem gn21CycleClockRate_pos
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
  fin_cases clock <;>
    simp [gn21CycleClockRate, harrivalI, harrivalJ, hswitchIJ, hswitchJI]

private theorem gn21AcceptanceProbability_le_one_state
    (muI muJ : Measure TripLength) [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (state : Fin 2) (sigma : TripPolicy) :
    gn21AcceptanceProbability (gn21CycleMarkLaw muI muJ state) sigma <= 1 := by
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    fin_cases state <;> simp only [gn21CycleMarkLaw] <;> infer_instance
  exact gn21AcceptanceProbability_le_one (gn21CycleMarkLaw muI muJ state) sigma

/-- The literal raw GN21 pair stream has the IID exponential-gap/Bernoulli-mark
law associated with the selected source clock, state, and policy. -/
theorem gn21RawMarkedPairStream_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    HasLaw (gn21RawMarkedPairStream clock state sigma)
      (streamMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
        (gn21AcceptanceProbability (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21AcceptanceProbability_le_one_state muI muJ state sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let M := gn21CycleMarkLaw muI muJ state
  let p := gn21AcceptanceProbability M sigma
  have hrate : 0 < rate := by
    exact gn21CycleClockRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI clock
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hp : p <= 1 := by
    dsimp [p]
    exact gn21AcceptanceProbability_le_one M sigma
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI c)
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s
  letI : forall c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (gn21CycleClockRate_pos arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  letI : forall s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp only [gn21CycleMarkLaw] <;> infer_instance
  letI : forall s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s) := fun _ =>
    by infer_instance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  let clockStream : (Fin 4 -> Nat -> Real) -> Nat -> Real := fun clocks => clocks clock
  let rawMarkStream : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength :=
    fun marks => marks state
  let classify : (Nat -> TripLength) -> Nat -> Bool :=
    fun marks n => gn21AcceptanceMark sigma (marks n)
  let B : Measure Bool := Measure.map (gn21AcceptanceMark sigma) M
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    exact Measure.isProbabilityMeasure_map
      (measurable_gn21AcceptanceMark sigma hsigma).aemeasurable
  have hclock_meas : Measurable clockStream := by
    exact measurable_pi_apply clock
  have hrawMark_meas : Measurable rawMarkStream := by
    exact measurable_pi_apply state
  have hclock : HasLaw clockStream
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)
      clockMeasure := by
    change HasLaw (Function.eval clock)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)
      clockMeasure
    simpa [clockMeasure, rate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI c)) clock).hasLaw
  have hrawMark : HasLaw rawMarkStream
      (Measure.infinitePi fun _ : Nat => M) markMeasure := by
    change HasLaw (Function.eval state) (Measure.infinitePi fun _ : Nat => M) markMeasure
    simpa [markMeasure, M] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat =>
          gn21CycleMarkLaw muI muJ s) state).hasLaw
  have hclassify_meas : Measurable classify := by
    apply measurable_pi_lambda
    intro n
    exact (measurable_gn21AcceptanceMark sigma hsigma).comp (measurable_pi_apply n)
  have hclassify : HasLaw classify (IIDStream.measure B)
      (Measure.infinitePi fun _ : Nat => M) := by
    refine ⟨hclassify_meas.aemeasurable, ?_⟩
    simpa [classify, B, IIDStream.measure] using
      (Measure.infinitePi_map_pi (μ := fun _ : Nat => M)
        (f := fun _ : Nat => gn21AcceptanceMark sigma)
        (fun _ : Nat => measurable_gn21AcceptanceMark sigma hsigma))
  have hmarked : HasLaw (classify ∘ rawMarkStream) (IIDStream.measure B) markMeasure :=
    hclassify.comp hrawMark
  have hmarked_meas : Measurable (classify ∘ rawMarkStream) :=
    hclassify_meas.comp hrawMark_meas
  have hfactor : HasLaw
      (Prod.map clockStream (classify ∘ rawMarkStream))
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure B))
      (clockMeasure.prod markMeasure) := by
    refine ⟨((hclock_meas.comp measurable_fst).prodMk
      (hmarked_meas.comp measurable_snd)).aemeasurable, ?_⟩
    calc
      (clockMeasure.prod markMeasure).map
          (Prod.map clockStream (classify ∘ rawMarkStream)) =
          (clockMeasure.map clockStream).prod
            (markMeasure.map (classify ∘ rawMarkStream)) := by
        symm
        exact Measure.map_prod_map clockMeasure markMeasure
          hclock_meas hmarked_meas
      _ = (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure B) := by
        rw [hclock.map_eq, hmarked.map_eq]
  have hzip := IIDStream.zip_hasLaw (ProbabilityTheory.expMeasure rate) B
  have hpaired : HasLaw
      (IIDStream.zip (α := Real) (β := Bool) ∘
        Prod.map clockStream (classify ∘ rawMarkStream))
      (IIDStream.measure ((ProbabilityTheory.expMeasure rate).prod B))
      (clockMeasure.prod markMeasure) := by
    simpa [AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure,
      IIDStream.measure] using hzip.comp hfactor
  have hB : B = (PMF.bernoulli p hp).toMeasure := by
    dsimp [B, p]
    exact measure_map_gn21AcceptanceMark_eq_bernoulli M sigma hsigma
      (gn21AcceptanceProbability M sigma)
      (gn21AcceptanceProbability_le_one M sigma)
      (coe_gn21AcceptanceProbability M sigma)
  change HasLaw (gn21RawMarkedPairStream clock state sigma)
    (streamMeasure rate p hp) (clockMeasure.prod markMeasure)
  rw [hB] at hpaired
  simpa [gn21RawMarkedPairStream, clockStream, rawMarkStream, classify,
    IIDStream.zip, Function.comp_def, streamMeasure, stepLaw] using hpaired

/-- A positive source policy mass makes the literal raw pair stream restart
after its first accepted mark with the same finite IID pair-block law. -/
theorem gn21Raw_postFirstSuccessBlock_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (q : Nat) :
    HasLaw
      (postFirstSuccessBlock q ∘ gn21RawMarkedPairStream clock state sigma)
      (Measure.pi fun _ : Fin q =>
        stepLaw
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
          (gn21AcceptanceProbability (gn21CycleMarkLaw muI muJ state) sigma)
          (gn21AcceptanceProbability_le_one_state muI muJ state sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let M := gn21CycleMarkLaw muI muJ state
  let p := gn21AcceptanceProbability M sigma
  have hrate : 0 < rate := by
    exact gn21CycleClockRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hp : p <= 1 := by
    dsimp [p]
    exact gn21AcceptanceProbability_le_one M sigma
  have hM_mass : 0 < M sigma := by
    exact measure_pos_of_singleStateTripMass_pos M sigma (by simpa [M] using hmass)
  have hpos : 0 < p := by
    dsimp [p, gn21AcceptanceProbability]
    exact ENNReal.toNNReal_pos (ne_of_gt hM_mass) (measure_ne_top M sigma)
  have hraw := gn21RawMarkedPairStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma
  have hrestart := postFirstSuccessBlock_hasLaw hrate p hp hpos q
  change HasLaw
    (postFirstSuccessBlock q ∘ gn21RawMarkedPairStream clock state sigma)
    (Measure.pi fun _ : Fin q => stepLaw rate p hp)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [Function.comp_def, rate, M, p] using hrestart.comp hraw

/-- A positive source policy mass also regenerates the complete literal raw
gap-and-acceptance-pair stream after its first accepted mark.  Unlike the
finite-block result, this is an all-time source-path restart law and can be
iterated in the larger renewal-cycle construction. -/
theorem gn21Raw_postFirstSuccessTail_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw
      (postFirstSuccessTail ∘ gn21RawMarkedPairStream clock state sigma)
      (streamMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
        (gn21AcceptanceProbability (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21AcceptanceProbability_le_one_state muI muJ state sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let M := gn21CycleMarkLaw muI muJ state
  let p := gn21AcceptanceProbability M sigma
  have hrate : 0 < rate := by
    exact gn21CycleClockRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hp : p <= 1 := by
    dsimp [p]
    exact gn21AcceptanceProbability_le_one M sigma
  have hM_mass : 0 < M sigma := by
    exact measure_pos_of_singleStateTripMass_pos M sigma (by simpa [M] using hmass)
  have hpos : 0 < p := by
    dsimp [p, gn21AcceptanceProbability]
    exact ENNReal.toNNReal_pos (ne_of_gt hM_mass) (measure_ne_top M sigma)
  have hraw := gn21RawMarkedPairStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma
  have hrestart := postFirstSuccessTail_hasLaw hrate p hp hpos
  change HasLaw
    (postFirstSuccessTail ∘ gn21RawMarkedPairStream clock state sigma)
    (streamMeasure rate p hp)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [Function.comp_def, rate, M, p] using hrestart.comp hraw

end MarkedRestart

end

end GN21DriverSurgePricing
