import GN21DriverSurgePricing.RawAcceptedArrivalTime
import AppliedModelingLib.Foundations.Probability.AlternatingTwoStateSwitching
import AppliedModelingLib.Foundations.Probability.AlternatingExponentialPrefixResidual
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTwoStreamHeadTail
import AppliedModelingLib.Foundations.Probability.CTMC

/-!
# Literal two-state CTMC path on GN21 raw switch clocks

The raw GN21 seed already contains the two independent state-specific switch
clock streams. This module turns those streams into the concrete alternating
two-state path used by the source model, and exposes the state at the literal
selected-trip completion time. Its transition-law and random-completion
restart proofs remain separate obligations.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

namespace RawTwoStateCTMC

/-- Location of the raw switch clock that is active while the world occupies a
given state. -/
def switchClockIndex : Fin 2 -> Fin 4
  | 0 => 2
  | 1 => 3

/-- The two literal source switch-clock paths, indexed by their current
state. -/
def rawSwitchGaps : GN21RawCycleSeed -> Fin 2 -> Nat -> Real :=
  fun seed state n => gn21RawCycleClock (switchClockIndex state) n seed

theorem measurable_rawSwitchGaps : Measurable rawSwitchGaps := by
  apply measurable_pi_lambda
  intro state
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
    ((measurable_pi_apply (switchClockIndex state)).comp measurable_fst))

/-- The concrete alternating two-state CTMC endpoint at calendar time `t`,
built from the raw source switch-clock streams. -/
noncomputable def stateAt (initial : Fin 2) : GN21RawCycleSeed -> Real -> Fin 2 :=
  fun seed t => AppliedModelingLib.Probability.TwoStateSwitching.stateAt
    initial (rawSwitchGaps seed) t

/-- The raw CTMC endpoint is jointly measurable in the cycle seed and
calendar time. -/
theorem measurable_stateAt (initial : Fin 2) :
    Measurable (fun z : GN21RawCycleSeed × Real => stateAt initial z.1 z.2) := by
  exact (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAt initial).comp
    ((measurable_rawSwitchGaps.comp measurable_fst).prodMk measurable_snd)

/-- The literal raw source law transported to the pair of state-indexed
switch-gap paths.  This is an exact image law, not an assumed CTMC path
measure. -/
noncomputable def rawSwitchPathLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) :
    Measure (Fin 2 -> Nat -> Real) :=
  Measure.map rawSwitchGaps
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)

/-- Raw source endpoint mass, represented through the literal transported
switch-path law. -/
noncomputable def rawStateProbability
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (initial target : Fin 2) (t : Real) : ℝ≥0∞ :=
  AppliedModelingLib.Probability.TwoStateSwitching.stateProbability
    (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI)
    initial target t

/-- Bounded real version of the raw endpoint mass, reserved for the analytic
renewal equation.  Its equality to the original source event is recorded
below, so this coercion does not introduce an abstract transition kernel. -/
noncomputable def rawStateProbabilityReal
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (initial target : Fin 2) (t : Real) : Real :=
  (rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
    initial target t).toReal

theorem isProbabilityMeasure_rawSwitchPathLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure sourceLaw := by
    simpa [sourceLaw] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  exact Measure.isProbabilityMeasure_map measurable_rawSwitchGaps.aemeasurable

/-- The transported-path endpoint mass is literally the original raw source
endpoint event. -/
theorem rawStateProbability_eq_measure_rawStateAt
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (initial target : Fin 2) (t : Real) :
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial target t =
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        {seed | stateAt initial seed t = target} := by
  unfold rawStateProbability rawSwitchPathLaw
    AppliedModelingLib.Probability.TwoStateSwitching.stateProbability
  change (Measure.map rawSwitchGaps
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
      ((fun switchGaps => AppliedModelingLib.Probability.TwoStateSwitching.stateAt
        initial switchGaps t) ⁻¹' {target}) = _
  rw [Measure.map_apply measurable_rawSwitchGaps
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAt_fixedTime
      initial t (measurableSet_singleton _))]
  rfl

theorem measurable_rawStateProbability
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) :
    Measurable (rawStateProbability
      muI muJ arrivalI arrivalJ switchIJ switchJI initial target) := by
  letI : IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_rawSwitchPathLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  simpa only [rawStateProbability] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateProbability
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial target)

theorem measurable_rawStateProbabilityReal
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) :
    Measurable (rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI initial target) := by
  letI : IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_rawSwitchPathLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  simpa only [rawStateProbabilityReal, rawStateProbability] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateProbability_toReal
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial target)

theorem rawStateProbabilityReal_nonneg
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (initial target : Fin 2) (t : Real) :
    0 ≤ rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI initial target t := by
  exact AppliedModelingLib.Probability.TwoStateSwitching.stateProbability_toReal_nonneg
    (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial target t

theorem rawStateProbabilityReal_le_one
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (t : Real) :
    rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI initial target t ≤ 1 := by
  letI : IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_rawSwitchPathLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  exact AppliedModelingLib.Probability.TwoStateSwitching.stateProbability_toReal_le_one
    (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial target t

/-- On every compact time interval, a literal raw endpoint probability is
Lebesgue-integrable.  This is the bounded-measurable analytic input needed to
turn the exponential renewal equation into a continuous primitive; it makes
no Markov or transition-kernel assertion. -/
theorem rawStateProbabilityReal_integrableOn_Icc
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (a b : Real) :
    IntegrableOn
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial target)
      (Set.Icc a b) volume := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
  · exact (measurable_rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initial target).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (rawStateProbabilityReal_nonneg
        muI muJ arrivalI arrivalJ switchIJ switchJI initial target t)]
    exact rawStateProbabilityReal_le_one
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initial target t

/-- The exponentially weighted literal endpoint probability remains locally
integrable.  Keeping this fact source-specific lets the subsequent change of
variables invoke the standard continuous-primitive theorem without assuming
continuity of the endpoint probability itself. -/
theorem rawStateProbabilityReal_exp_weighted_integrableOn_Icc
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI rate : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (a b : Real) :
    IntegrableOn
      (fun u => Real.exp (rate * u) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial target u)
      (Set.Icc a b) volume := by
  apply IntegrableOn.continuousOn_mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (rawStateProbabilityReal_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initial target a b)
    isCompact_Icc

/-- The compact-interval primitive of the exponentially weighted literal
endpoint probability is continuous.  This is an analytic consequence of the
raw law's bounded measurability, not an assumed CTMC regularity property. -/
theorem continuousOn_rawStateProbabilityReal_exp_weighted_primitive
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI rate : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (a b : Real) :
    ContinuousOn (fun x => ∫ u in Set.Icc a x,
      Real.exp (rate * u) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial target u)
      (Set.Icc a b) := by
  exact intervalIntegral.continuousOn_primitive_Icc
    (rawStateProbabilityReal_exp_weighted_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI rate
      harrivalI harrivalJ hswitchIJ hswitchJI initial target a b)

theorem rawStateProbabilityReal_initial_add_eq_otherState
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial initial t +
      rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t = 1 := by
  letI : IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_rawSwitchPathLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  simpa only [rawStateProbabilityReal, rawStateProbability] using
    (AppliedModelingLib.Probability.TwoStateSwitching.stateProbability_toReal_initial_add_eq_otherState
      (μ := rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial t)

/-- Before the literal first raw switch holding time, the concrete source
path remains in its initial state. -/
theorem stateAt_eq_initial_of_lt_firstSwitch
    (initial : Fin 2) (seed : GN21RawCycleSeed) (t : Real)
    (ht : t < rawSwitchGaps seed initial 0) :
    stateAt initial seed t = initial := by
  exact AppliedModelingLib.Probability.TwoStateSwitching.stateAt_eq_initial_of_lt_firstGap
    initial (rawSwitchGaps seed) t ht

/-- The state at the completion of the literal first selected accepted trip.
The selected mark determines the trip duration while the CTMC path is still
the raw alternating switch-clock path. -/
noncomputable def stateAtFirstAcceptedTripCompletion
    (initial state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Fin 2 :=
  fun seed => stateAt initial seed
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)

theorem measurable_stateAtFirstAcceptedTripCompletion
    (initial state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (stateAtFirstAcceptedTripCompletion initial state sigma) := by
  let selected := AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma
  have hselected : Measurable selected := by
    change Measurable
      (AcceptedTripSelection.firstAcceptedTripMark sigma ∘
        AcceptedArrivalTime.rawTripMarkStream state)
    exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)
  have hstate : Measurable (fun seed : GN21RawCycleSeed =>
      stateAt initial seed (selected seed)) :=
    (measurable_stateAt initial).comp (measurable_id.prodMk hselected)
  simpa [stateAtFirstAcceptedTripCompletion, selected] using hstate

/-- The raw CTMC endpoint at the actual calendar completion of the first
accepted request: its accepted-arrival calendar time plus its selected trip
duration.  This differs from `stateAtFirstAcceptedTripCompletion`, which is
the duration-only source observable used in the fixed-state proposal layer. -/
noncomputable def stateAtFirstAcceptedArrivalCalendarCompletion
    (initial : Fin 2) (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Fin 2 :=
  fun seed => stateAt initial seed
    (AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed))

/-- Measurability of the actual accepted-arrival calendar-completion CTMC
endpoint. -/
theorem measurable_stateAtFirstAcceptedArrivalCalendarCompletion
    (initial : Fin 2) (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma) := by
  let completion := fun seed : GN21RawCycleSeed =>
    AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed)
  have hcompletion : Measurable completion := by
    exact AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryCalendarCompletionTime.comp
      (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory
        clock state sigma hsigma)
  simpa [stateAtFirstAcceptedArrivalCalendarCompletion, completion] using
    (measurable_stateAt initial).comp (measurable_id.prodMk hcompletion)

/-- The literal switch-clock bundle is independent of the literal selected
accepted-trip mark.  This is a product-space fact about the raw GN seed; it
does not assume a post-thinning CTMC or replace the selected trip by an
external duration. -/
theorem indepFun_rawSwitchGaps_gn21RawFirstAcceptedTripMark
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    ProbabilityTheory.IndepFun rawSwitchGaps
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw s
  let switchGapsFromClock : (Fin 4 -> Nat -> Real) -> Fin 2 -> Nat -> Real :=
    fun clocks current n => clocks (switchClockIndex current) n
  let selectedFromMarks : (Fin 2 -> Nat -> TripLength) -> TripLength :=
    fun marks => AcceptedTripSelection.firstAcceptedTripMark sigma (marks state)
  have hclockRate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  have hswitchGaps : Measurable switchGapsFromClock := by
    apply measurable_pi_lambda
    intro current
    apply measurable_pi_lambda
    intro n
    exact (measurable_pi_apply n).comp
      (measurable_pi_apply (switchClockIndex current))
  have hselected : Measurable selectedFromMarks := by
    exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (measurable_pi_apply state)
  have hproduct : ProbabilityTheory.IndepFun
      (switchGapsFromClock ∘ Prod.fst) (selectedFromMarks ∘ Prod.snd)
      (clockMeasure.prod markMeasure) :=
    ProbabilityTheory.indepFun_prod hswitchGaps hselected
  change ProbabilityTheory.IndepFun rawSwitchGaps
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
    (clockMeasure.prod markMeasure)
  simpa [rawSwitchGaps, switchGapsFromClock, selectedFromMarks,
    AcceptedTripSelection.gn21RawFirstAcceptedTripMark, gn21RawCycleMark,
    Function.comp_def] using hproduct

/-- The pair of source switch-clock streams has the exact product of its two
canonical exponential-interarrival laws.  This preserves the literal streams
rather than recasting the CTMC endpoint as an assumed transition kernel. -/
def rawSwitchGapPair : GN21RawCycleSeed -> (Nat -> Real) × (Nat -> Real) :=
  fun seed => (rawSwitchGaps seed 0, rawSwitchGaps seed 1)

theorem measurable_rawSwitchGapPair : Measurable rawSwitchGapPair := by
  exact ((measurable_pi_apply 0).comp measurable_rawSwitchGaps).prodMk
    ((measurable_pi_apply 1).comp measurable_rawSwitchGaps)

theorem rawSwitchGapPair_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    HasLaw rawSwitchGapPair
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw s
  have hclockRate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  have hfst : HasLaw (Prod.fst : GN21RawCycleSeed -> Fin 4 -> Nat -> Real)
      clockMeasure (clockMeasure.prod markMeasure) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod]
    simp
  have hcoordIndep : ProbabilityTheory.iIndepFun
      (fun c : Fin 4 => Function.eval c) clockMeasure := by
    simpa only [Function.comp_apply] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c))
        (X := fun _ : Fin 4 => id)
        (fun _ => measurable_id))
  have hleft : HasLaw (Function.eval (2 : Fin 4))
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate 2)) clockMeasure :=
    (measurePreserving_eval_infinitePi
      (fun c : Fin 4 =>
        AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate c)) 2).hasLaw
  have hright : HasLaw (Function.eval (3 : Fin 4))
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate 3)) clockMeasure :=
    (measurePreserving_eval_infinitePi
      (fun c : Fin 4 =>
        AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate c)) 3).hasLaw
  have hpairClock : HasLaw
      (fun clocks : Fin 4 -> Nat -> Real => (clocks 2, clocks 3))
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate 2)).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate 3))) clockMeasure := by
    exact AppliedModelingLib.Probability.indepFun_hasLaw_prodMk hleft hright
      (hcoordIndep.indepFun (by decide : (2 : Fin 4) ≠ 3))
  have hpairRaw := hpairClock.comp hfst
  change HasLaw rawSwitchGapPair
    ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI))
    (clockMeasure.prod markMeasure)
  simpa [rawSwitchGapPair, rawSwitchGaps, gn21RawCycleClock, clockRate,
    gn21CycleClockRate, Function.comp_def] using hpairRaw

/-- Any two distinct literal raw clock streams and an entire state-specific
raw mark stream have their exact three-factor product law.  This retains the
unconsumed source tails, so it is a valid input to a subsequent stopped-race
and regeneration argument; it is not itself such an argument. -/
theorem rawClockPair_markStream_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (left right : Fin 4) (hleft_right : left ≠ right) (state : Fin 2) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      ((seed.1 left, seed.1 right),
        AcceptedArrivalTime.rawTripMarkStream state seed))
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI left)).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI right))).prod
        (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let leftStream : (Fin 4 -> Nat -> Real) -> Nat -> Real := Function.eval left
  let rightStream : (Fin 4 -> Nat -> Real) -> Nat -> Real := Function.eval right
  let markStream : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength := Function.eval state
  have hclockRate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hleft_meas : Measurable leftStream := by
    simpa [leftStream] using (measurable_pi_apply left :
      Measurable (Function.eval left : (Fin 4 -> Nat -> Real) -> Nat -> Real))
  have hright_meas : Measurable rightStream := by
    simpa [rightStream] using (measurable_pi_apply right :
      Measurable (Function.eval right : (Fin 4 -> Nat -> Real) -> Nat -> Real))
  have hmark_meas : Measurable markStream := by
    simpa [markStream] using (measurable_pi_apply state :
      Measurable (Function.eval state :
        (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength))
  have hclock_indep : ProbabilityTheory.iIndepFun
      (fun c : Fin 4 => Function.eval c) clockMeasure := by
    simpa only [Function.comp_apply] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c))
        (X := fun _ : Fin 4 => id)
        (fun _ => measurable_id))
  have hleft : HasLaw leftStream
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate left)) clockMeasure := by
    simpa [leftStream] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) left).hasLaw
  have hright : HasLaw rightStream
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate right)) clockMeasure := by
    simpa [rightStream] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) right).hasLaw
  have hpair_clocks : HasLaw (fun clocks => (leftStream clocks, rightStream clocks))
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate left)).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate right))) clockMeasure := by
    exact AppliedModelingLib.Probability.indepFun_hasLaw_prodMk hleft hright
      (hclock_indep.indepFun hleft_right)
  have hclock_source : HasLaw (Prod.fst : GN21RawCycleSeed -> Fin 4 -> Nat -> Real)
      clockMeasure P := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    change Measure.map Prod.fst (clockMeasure.prod markMeasure) = clockMeasure
    rw [Measure.map_fst_prod]
    simp
  have hpair_source : HasLaw (fun seed : GN21RawCycleSeed =>
      (leftStream seed.1, rightStream seed.1))
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate left)).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate right))) P :=
    hpair_clocks.comp hclock_source
  have hmarks : HasLaw markStream
      (Measure.infinitePi fun _ : Nat => markLaw state) markMeasure := by
    simpa [markStream] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s) state).hasLaw
  have hmark_source : HasLaw (Prod.snd : GN21RawCycleSeed -> Fin 2 -> Nat -> TripLength)
      markMeasure P := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    change Measure.map Prod.snd (clockMeasure.prod markMeasure) = markMeasure
    rw [Measure.map_snd_prod]
    simp
  have hmarks_source : HasLaw (fun seed : GN21RawCycleSeed => markStream seed.2)
      (Measure.infinitePi fun _ : Nat => markLaw state) P :=
    hmarks.comp hmark_source
  have hindep : ProbabilityTheory.IndepFun
      (fun seed : GN21RawCycleSeed => (leftStream seed.1, rightStream seed.1))
      (fun seed : GN21RawCycleSeed => markStream seed.2) P := by
    simpa [P, Function.comp_def] using
      (ProbabilityTheory.indepFun_prod (hleft_meas.prodMk hright_meas) hmark_meas)
  simpa [P, clockRate, markLaw, leftStream, rightStream, markStream,
    gn21RawCycleClock, AcceptedArrivalTime.rawTripMarkStream, gn21RawCycleMark] using
    (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
      hpair_source hmarks_source hindep)

/-- The two literal switch streams and two further distinct literal clock
streams have their exact four-stream product law.  This is a raw-coordinate
statement: it retains whole arrival paths and makes no stopped-process or
restart assertion. -/
theorem rawSwitchGapPair_rawClockPair_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (left right : Fin 4)
    (hleft_right : left ≠ right)
    (hleft_two : left ≠ 2) (hleft_three : left ≠ 3)
    (hright_two : right ≠ 2) (hright_three : right ≠ 3) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      (rawSwitchGapPair seed,
        (AcceptedArrivalTime.rawClockStream left seed,
          AcceptedArrivalTime.rawClockStream right seed)))
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          switchJI)).prod
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI left)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI right))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockLaw : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let leftLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate left)
  let rightLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate right)
  let switchPair : (Fin 4 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) :=
    fun clocks => (clocks 2, clocks 3)
  let arrivalPair : (Fin 4 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) :=
    fun clocks => (clocks left, clocks right)
  let input : (Fin 4 -> Nat -> Real) ->
      ((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> Real)) :=
    fun clocks => (switchPair clocks, arrivalPair clocks)
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate c)
  letI : IsProbabilityMeasure clockLaw := by
    dsimp [clockLaw]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s) := fun s =>
    inferInstance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure leftLaw := by
    dsimp [leftLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate left)
  letI : IsProbabilityMeasure rightLaw := by
    dsimp [rightLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate right)
  have hcoordinateMeas : ∀ c : Fin 4,
      Measurable (fun clocks : Fin 4 -> Nat -> Real => clocks c) := by
    intro c
    exact measurable_pi_apply c
  have hcoordinateIndep : ProbabilityTheory.iIndepFun
      (fun c (clocks : Fin 4 -> Nat -> Real) => clocks c) clockLaw := by
    simpa [clockLaw] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) (fun _ => measurable_id))
  have hclockTwoLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks 2)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ)
      clockLaw := by
    simpa [clockLaw, clockRate, gn21CycleClockRate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) 2).hasLaw
  have hclockThreeLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks 3)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
      clockLaw := by
    simpa [clockLaw, clockRate, gn21CycleClockRate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) 3).hasLaw
  have hswitchPairLaw : HasLaw switchPair switchLaw clockLaw := by
    simpa [switchPair, switchLaw] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
        hclockTwoLaw hclockThreeLaw (hcoordinateIndep.indepFun (by decide)))
  have hleftLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks left)
      leftLaw clockLaw := by
    simpa [leftLaw, clockLaw] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) left).hasLaw
  have hrightLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks right)
      rightLaw clockLaw := by
    simpa [rightLaw, clockLaw] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) right).hasLaw
  have harrivalPairLaw : HasLaw arrivalPair (leftLaw.prod rightLaw) clockLaw := by
    simpa [arrivalPair] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk hleftLaw hrightLaw
        (hcoordinateIndep.indepFun hleft_right))
  have hswitchArrivalIndep : ProbabilityTheory.IndepFun switchPair arrivalPair
      clockLaw := by
    simpa [switchPair, arrivalPair] using
      (hcoordinateIndep.indepFun_prodMk_prodMk hcoordinateMeas 2 3 left right
        (Ne.symm hleft_two) (Ne.symm hright_two)
        (Ne.symm hleft_three) (Ne.symm hright_three))
  have hinputLaw : HasLaw input (switchLaw.prod (leftLaw.prod rightLaw)) clockLaw := by
    simpa [input] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
        hswitchPairLaw harrivalPairLaw hswitchArrivalIndep)
  have hclockSource : HasLaw (Prod.fst : GN21RawCycleSeed -> Fin 4 -> Nat -> Real)
      clockLaw P := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    change Measure.map Prod.fst (clockLaw.prod markLaw) = clockLaw
    rw [Measure.map_fst_prod]
    simp
  have hsource := hinputLaw.comp hclockSource
  refine hsource.congr ?_
  filter_upwards [] with seed
  rfl

/-- The two state-indexed literal mark streams have their source product law.
This is a coordinate factorization only; it does not stop either marked
arrival process. -/
theorem rawTripMarkPair_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      (AcceptedArrivalTime.rawTripMarkStream state seed,
        AcceptedArrivalTime.rawTripMarkStream
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed))
      ((AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockLaw : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let currentLaw := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ state)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let otherLaw := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let pair : (Fin 2 -> Nat -> TripLength) ->
      (Nat -> TripLength) × (Nat -> TripLength) :=
    fun marks => (marks state, marks other)
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate c)
  letI : IsProbabilityMeasure clockLaw := by
    dsimp [clockLaw]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s) := fun s =>
    inferInstance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure currentLaw := by
    dsimp [currentLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure otherLaw := by
    dsimp [otherLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hcoordinateMeas : ∀ s : Fin 2,
      Measurable (fun marks : Fin 2 -> Nat -> TripLength => marks s) := by
    intro s
    exact measurable_pi_apply s
  have hcoordinateIndep : ProbabilityTheory.iIndepFun
      (fun s (marks : Fin 2 -> Nat -> TripLength) => marks s) markLaw := by
    simpa [markLaw] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun s : Fin 2 => Measure.infinitePi fun _ : Nat =>
          gn21CycleMarkLaw muI muJ s) (fun _ => measurable_id))
  have hcurrentLaw : HasLaw (fun marks : Fin 2 -> Nat -> TripLength => marks state)
      currentLaw markLaw := by
    simpa [currentLaw, markLaw, AppliedModelingLib.Probability.IIDStream.measure] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s)
        state).hasLaw
  have hotherLaw : HasLaw (fun marks : Fin 2 -> Nat -> TripLength => marks other)
      otherLaw markLaw := by
    simpa [otherLaw, markLaw, AppliedModelingLib.Probability.IIDStream.measure] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s)
        other).hasLaw
  have hpairLaw : HasLaw pair (currentLaw.prod otherLaw) markLaw := by
    simpa [pair] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk hcurrentLaw hotherLaw
        (hcoordinateIndep.indepFun
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne state).symm))
  have hmarkSource : HasLaw (Prod.snd : GN21RawCycleSeed -> Fin 2 -> Nat -> TripLength)
      markLaw P := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    change Measure.map Prod.snd (clockLaw.prod markLaw) = markLaw
    rw [Measure.map_snd_prod]
    simp
  have hsource := hpairLaw.comp hmarkSource
  simpa [pair, other, currentLaw, otherLaw,
    AcceptedArrivalTime.rawTripMarkStream, gn21RawCycleMark] using hsource

/-- The two literal raw switch-clock tails together with the first holding
time of the initially active state.  This removes precisely the consumed
source coordinate and leaves the other source clock untouched. -/
def rawSwitchTailAndFirstGap (initial : Fin 2) :
    GN21RawCycleSeed -> ((Nat -> Real) × (Nat -> Real)) × Real :=
  fun seed =>
    AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead
      initial (rawSwitchGapPair seed)

theorem measurable_rawSwitchTailAndFirstGap (initial : Fin 2) :
    Measurable (rawSwitchTailAndFirstGap initial) := by
  exact
    (AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead
      initial).comp measurable_rawSwitchGapPair

/-- At the literal first state switch, the unconsumed raw clock pair has its
original product law and is independent of the consumed active holding time.
This is the source-specific distributional counterpart to the pathwise
first-switch restart. -/
theorem rawSwitchTailAndFirstGap_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    HasLaw (rawSwitchTailAndFirstGap initial)
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
        (if initial = 0 then
          ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  have hfactor : HasLaw
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead initial)
      (tails.prod
        (if initial = 0 then
          ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI))
      tails := by
    refine ⟨(AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead
      initial).aemeasurable, ?_⟩
    simpa [tails] using
      (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamAfterActiveHead
        initial hswitchIJ hswitchJI)
  have hraw := rawSwitchGapPair_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
  simpa [rawSwitchTailAndFirstGap, Function.comp_def] using hfactor.fun_comp hraw

/-- The literal raw switch streams after their first use, packaged in state
order. -/
def rawSwitchTailPair (initial : Fin 2) :
    GN21RawCycleSeed -> (Nat -> Real) × (Nat -> Real) :=
  fun seed =>
    (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
      initial (rawSwitchGaps seed) 0,
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
      initial (rawSwitchGaps seed) 1)

theorem rawSwitchTailPair_eq_factorTail
    (initial : Fin 2) (seed : GN21RawCycleSeed) :
    rawSwitchTailPair initial seed = (rawSwitchTailAndFirstGap initial seed).1 := by
  fin_cases initial <;> ext n <;>
    simp [rawSwitchTailPair, rawSwitchTailAndFirstGap,
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst,
      AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead,
      rawSwitchGapPair]

theorem rawSwitchTailAndFirstGap_snd
    (initial : Fin 2) (seed : GN21RawCycleSeed) :
    (rawSwitchTailAndFirstGap initial seed).2 = rawSwitchGaps seed initial 0 := by
  fin_cases initial <;>
    rfl

theorem twoStateGapsOfPair_rawSwitchTailPair
    (initial : Fin 2) (seed : GN21RawCycleSeed) :
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
      (rawSwitchTailPair initial seed) =
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
        initial (rawSwitchGaps seed) := by
  funext state n
  fin_cases state <;> rfl

/-- Reattaching the active holding-time residual to the literal raw tails
is pathwise the state-indexed switch stream after that much time has elapsed
in the initial visit.  This is a deterministic coordinate identity; it does
not assert that the residual is independent of the preceding arrival event. -/
theorem twoStateGapsOfPair_prepend_activeResidual_rawSwitchTailPair
    (initial : Fin 2) (seed : GN21RawCycleSeed) (elapsed : Real) :
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
        initial
        (rawSwitchGaps seed initial 0 - elapsed, rawSwitchTailPair initial seed)) =
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterActiveElapsed
        initial (rawSwitchGaps seed) elapsed := by
  funext state n
  fin_cases initial <;> fin_cases state <;> cases n <;> rfl

/-- Before the first literal switch, shifting the raw calendar path to an
elapsed arrival time and then following a nonnegative trip duration is exactly
the path driven by the residual active holding time and the literal raw tails.
The divergence premise is the concrete nonexplosion condition needed by the
deterministic alternating-path time-shift theorem. -/
theorem stateAt_add_eq_stateAt_prepend_activeResidual_rawSwitchTailPair
    (initial : Fin 2) (seed : GN21RawCycleSeed) (arrival tripDuration : Real)
    (htripDuration : 0 ≤ tripDuration)
    (hbeforeSwitch : arrival < rawSwitchGaps seed initial 0)
    (hdiv : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
          initial (rawSwitchGaps seed))) atTop atTop) :
    stateAt initial seed (arrival + tripDuration) =
      AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
          (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
            initial
            (rawSwitchGaps seed initial 0 - arrival, rawSwitchTailPair initial seed)))
        tripDuration := by
  let gaps := AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
    initial (rawSwitchGaps seed)
  have harrival : ∃ n : Nat,
      arrival < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n gaps :=
    AppliedModelingLib.Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
      gaps hdiv arrival
  have hcompletion : ∃ n : Nat,
      arrival + tripDuration < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n gaps :=
    AppliedModelingLib.Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
      gaps hdiv (arrival + tripDuration)
  have htail : ∃ n : Nat,
      tripDuration < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.PoissonProcess.residualTail arrival gaps) :=
    AppliedModelingLib.Probability.PoissonProcess.exists_residualTail_arrival_gt_of_tendsto
      arrival tripDuration gaps hdiv
  have hstateAtArrival : stateAt initial seed arrival = initial :=
    stateAt_eq_initial_of_lt_firstSwitch initial seed arrival hbeforeSwitch
  have hstateAtArrival' :
      AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (rawSwitchGaps seed) arrival = initial := by
    simpa [stateAt] using hstateAtArrival
  have hshift :=
    AppliedModelingLib.Probability.TwoStateSwitching.stateAt_add_eq_stateAt_afterElapsed
      initial (rawSwitchGaps seed) arrival tripDuration htripDuration
      (by simpa [gaps] using harrival)
      (by simpa [gaps] using hcompletion)
      (by simpa [gaps] using htail)
  have hcount : AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount arrival
      (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
        initial (rawSwitchGaps seed)) = 0 := by
    apply (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_eq_zero_iff
      arrival _).mpr
    left
    simpa [AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
      AppliedModelingLib.Probability.PoissonProcess.interarrival,
      AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps,
      AppliedModelingLib.Probability.TwoStateSwitching.alternatingGap,
      AppliedModelingLib.Probability.TwoStateSwitching.stateAfterSwitches] using hbeforeSwitch
  change AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
      (rawSwitchGaps seed) (arrival + tripDuration) = _
  rw [hshift, hstateAtArrival',
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed_of_count_eq_two_mul
      initial (rawSwitchGaps seed) arrival 0 (by simpa using hcount)]
  have hpairs :
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterPairs
        (rawSwitchGaps seed) 0 = rawSwitchGaps seed := by
    funext state n
    simp [AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterPairs,
      AppliedModelingLib.Probability.PoissonProcess.futureInterarrival,
      AppliedModelingLib.Probability.PoissonProcess.interarrival]
  have hzeroTime : arrival -
      (AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix 0
          (rawSwitchGaps seed initial) +
        AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix 0
          (rawSwitchGaps seed
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial))) =
        arrival := by
    simp [AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix]
  rw [hpairs, hzeroTime]
  exact
    congrArg
      (fun switchGaps => AppliedModelingLib.Probability.TwoStateSwitching.stateAt
        initial switchGaps tripDuration)
      (twoStateGapsOfPair_prepend_activeResidual_rawSwitchTailPair
        initial seed arrival).symm

/-- Before the first literal switch, shifting the *future switch streams* to
accepted-trip completion agrees with first reattaching the active residual at
the accepted arrival and then shifting that literal continuation by the trip
duration.  This is the path-level companion to the preceding endpoint
identity, so it does not replace a future-path claim by an endpoint claim. -/
theorem switchGapsAfterElapsed_add_eq_switchGapsAfterElapsed_prepend_activeResidual_rawSwitchTailPair
    (initial : Fin 2) (seed : GN21RawCycleSeed) (arrival tripDuration : Real)
    (htripDuration : 0 ≤ tripDuration)
    (hbeforeSwitch : arrival < rawSwitchGaps seed initial 0)
    (hdiv : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
          initial (rawSwitchGaps seed))) atTop atTop) :
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
        initial (rawSwitchGaps seed) (arrival + tripDuration) =
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
          (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
            initial
            (rawSwitchGaps seed initial 0 - arrival, rawSwitchTailPair initial seed)))
        tripDuration := by
  let gaps := AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
    initial (rawSwitchGaps seed)
  have harrival : ∃ n : Nat,
      arrival < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n gaps :=
    AppliedModelingLib.Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
      gaps hdiv arrival
  have hcompletion : ∃ n : Nat,
      arrival + tripDuration < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n gaps :=
    AppliedModelingLib.Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
      gaps hdiv (arrival + tripDuration)
  have htail : ∃ n : Nat,
      tripDuration < AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.PoissonProcess.residualTail arrival gaps) :=
    AppliedModelingLib.Probability.PoissonProcess.exists_residualTail_arrival_gt_of_tendsto
      arrival tripDuration gaps hdiv
  have hshift :=
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed_add_eq_switchGapsAfterElapsed_comp
      initial (rawSwitchGaps seed) arrival tripDuration htripDuration
      (by simpa [gaps] using harrival)
      (by simpa [gaps] using hcompletion)
      (by simpa [gaps] using htail)
  have hstateAtArrival : stateAt initial seed arrival = initial :=
    stateAt_eq_initial_of_lt_firstSwitch initial seed arrival hbeforeSwitch
  have hstateAtArrival' :
      AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (rawSwitchGaps seed) arrival = initial := by
    simpa [stateAt] using hstateAtArrival
  have hcount : AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount arrival
      (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
        initial (rawSwitchGaps seed)) = 0 := by
    apply (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_eq_zero_iff
      arrival _).mpr
    left
    simpa [AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
      AppliedModelingLib.Probability.PoissonProcess.interarrival,
      AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps,
      AppliedModelingLib.Probability.TwoStateSwitching.alternatingGap,
      AppliedModelingLib.Probability.TwoStateSwitching.stateAfterSwitches] using hbeforeSwitch
  have hpairs :
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterPairs
        (rawSwitchGaps seed) 0 = rawSwitchGaps seed := by
    funext state n
    simp [AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterPairs,
      AppliedModelingLib.Probability.PoissonProcess.futureInterarrival,
      AppliedModelingLib.Probability.PoissonProcess.interarrival]
  have hzeroTime : arrival -
      (AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix 0
          (rawSwitchGaps seed initial) +
        AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix 0
          (rawSwitchGaps seed
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial))) =
        arrival := by
    simp [AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix]
  have hresidual :
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
          initial (rawSwitchGaps seed) arrival =
        AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
          (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
            initial
            (rawSwitchGaps seed initial 0 - arrival, rawSwitchTailPair initial seed)) := by
    rw [AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed_of_count_eq_two_mul
      initial (rawSwitchGaps seed) arrival 0 (by simpa using hcount), hpairs, hzeroTime]
    exact (twoStateGapsOfPair_prepend_activeResidual_rawSwitchTailPair
      initial seed arrival).symm
  calc
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
        initial (rawSwitchGaps seed) (arrival + tripDuration) =
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
          (rawSwitchGaps seed) arrival)
        (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
          initial (rawSwitchGaps seed) arrival) tripDuration := hshift
    _ = AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
          (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
            initial
            (rawSwitchGaps seed initial 0 - arrival, rawSwitchTailPair initial seed)))
        tripDuration := by rw [hstateAtArrival', hresidual]

/-- The literal raw state-indexed tail pair itself has the original two-stream
product law. -/
theorem rawSwitchTailPair_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    HasLaw (rawSwitchTailPair initial)
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let activeHead := if initial = 0 then
    ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure tails := by
    dsimp [tails]
    infer_instance
  letI : IsProbabilityMeasure activeHead := by
    dsimp [activeHead]
    split_ifs <;>
      apply ProbabilityTheory.isProbabilityMeasure_expMeasure
    · exact hswitchIJ
    · exact hswitchJI
  have hfst : HasLaw
      (Prod.fst : ((Nat -> Real) × (Nat -> Real)) × Real -> (Nat -> Real) × (Nat -> Real))
      tails (tails.prod activeHead) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod]
    simp
  have hfactor := rawSwitchTailAndFirstGap_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial
  have htail := hfst.fun_comp hfactor
  refine htail.congr ?_
  filter_upwards [] with seed
  exact rawSwitchTailPair_eq_factorTail initial seed

theorem rawSwitchGaps_eq_twoStateGapsOfPair (seed : GN21RawCycleSeed) :
    rawSwitchGaps seed =
      AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
        (rawSwitchGapPair seed) := by
  funext state n
  fin_cases state <;> rfl

/-- The literal raw alternating switch path is nonexplosive almost surely.
This is transported from the exact two-switch-stream product law, rather than
assumed as part of a CTMC record. -/
theorem ae_tendsto_arrivalTime_rawSwitchGaps
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
            initial (rawSwitchGaps seed))) atTop atTop := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hpairLaw := rawSwitchGapPair_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
  have hpairs : ∀ᵐ pair ∂Measure.map rawSwitchGapPair P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
            initial
            (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair)))
          atTop atTop := by
    rw [hpairLaw.map_eq]
    exact AppliedModelingLib.Probability.TwoStateSwitching.ae_tendsto_arrivalTime_alternatingGaps_prod
      initial switchIJ switchJI
      hswitchIJ hswitchJI
  have hraw : ∀ᵐ seed ∂P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps
            initial
            (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
              (rawSwitchGapPair seed)))) atTop atTop :=
    ae_of_ae_map measurable_rawSwitchGapPair.aemeasurable hpairs
  filter_upwards [hraw] with seed hseed
  simpa only [rawSwitchGaps_eq_twoStateGapsOfPair seed] using hseed

private theorem rawSwitchRate_pos
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (switchClockIndex state) := by
  fin_cases state <;>
    simp [switchClockIndex, gn21CycleClockRate, hswitchIJ, hswitchJI]

private theorem ae_all_nonnegative_rawSwitchGaps
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ n, 0 ≤ rawSwitchGaps seed state n := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clock := switchClockIndex state
  have hrate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    simpa [clock] using rawSwitchRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state
  have hclock := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ gaps ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock) P,
      ∀ n, 0 ≤ gaps n := by
    rw [hclock.map_eq]
    exact AppliedModelingLib.Probability.PoissonProcess.ae_all_interarrival_nonnegative hrate
  have hraw : ∀ᵐ seed ∂P, ∀ n, 0 ≤ seed.1 clock n :=
    ae_of_ae_map hclock.aemeasurable hsource
  simpa [P, clock, rawSwitchGaps, gn21RawCycleClock] using hraw

private theorem ae_tendsto_rawSwitchGaps
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (rawSwitchGaps seed state)) atTop atTop := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clock := switchClockIndex state
  have hrate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    simpa [clock] using rawSwitchRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state
  have hclock := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ gaps ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock) P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n gaps) atTop atTop := by
    rw [hclock.map_eq]
    exact AppliedModelingLib.Probability.PoissonProcess.ae_arrivalTime_tendsto_atTop hrate
  have hraw : ∀ᵐ seed ∂P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n (seed.1 clock)) atTop atTop :=
    ae_of_ae_map hclock.aemeasurable hsource
  simpa [P, clock, rawSwitchGaps, gn21RawCycleClock] using hraw

/-- On a common full-measure source event, the raw alternating endpoint
restarts after its literal first switch for every nonnegative elapsed time.
The tail law and arbitrary trip-completion restart are separate obligations. -/
theorem ae_forall_stateAt_firstSwitch_eq_switched_tail
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ elapsed : Real, 0 ≤ elapsed →
        stateAt initial seed (rawSwitchGaps seed initial 0 + elapsed) =
          AppliedModelingLib.Probability.TwoStateSwitching.stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
              initial (rawSwitchGaps seed)) elapsed := by
  have hnonneg : ∀ᵐ seed ∂gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ state n, 0 ≤ rawSwitchGaps seed state n := by
    have hzero := ae_all_nonnegative_rawSwitchGaps
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0
    have hone := ae_all_nonnegative_rawSwitchGaps
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1
    filter_upwards [hzero, hone] with seed hzero hone state n
    fin_cases state
    · exact hzero n
    · exact hone n
  have hdiv := ae_tendsto_rawSwitchGaps
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
  filter_upwards [hnonneg, hdiv] with seed hnonneg hdiv elapsed helapsed
  apply AppliedModelingLib.Probability.TwoStateSwitching.stateAt_head_add_eq_switched_tail
    initial (rawSwitchGaps seed) _ elapsed helapsed
  refine AppliedModelingLib.Probability.TwoStateSwitching.tendsto_arrivalTime_alternatingGaps
    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
    (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
      initial (rawSwitchGaps seed)) ?_ ?_
  · intro state n
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst]
    split_ifs with hstate
    · exact hnonneg state (n + 1)
    · exact hnonneg state n
  · have htail_eq :
        AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
            initial (rawSwitchGaps seed)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) =
          rawSwitchGaps seed
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) := by
        funext n
        exact if_neg
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne initial)
    rw [htail_eq]
    exact hdiv

/-- At the literal first source state switch, the raw alternating endpoint
restarts pathwise in the opposite state on the exact unconsumed raw switch
tails. -/
theorem ae_stateAt_firstSwitch_eq_switched_tail
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) (ht : 0 ≤ t) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      stateAt initial seed (rawSwitchGaps seed initial 0 + t) =
        AppliedModelingLib.Probability.TwoStateSwitching.stateAt
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
            initial (rawSwitchGaps seed)) t := by
  have hall := ae_forall_stateAt_firstSwitch_eq_switched_tail
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial
  filter_upwards [hall] with seed hseed
  exact hseed t ht

/-- At any deterministic calendar time, the raw path either has not reached
its literal first switch or is the switched-state tail path at the remaining
elapsed time.  This is the source first-step recursion preceding the endpoint
law calculation. -/
theorem ae_stateAt_eq_firstStep
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      stateAt initial seed t =
        if hfirst : rawSwitchGaps seed initial 0 ≤ t then
          AppliedModelingLib.Probability.TwoStateSwitching.stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterFirst
              initial (rawSwitchGaps seed))
            (t - rawSwitchGaps seed initial 0)
        else initial := by
  have hall := ae_forall_stateAt_firstSwitch_eq_switched_tail
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial
  filter_upwards [hall] with seed hseed
  by_cases hfirst : rawSwitchGaps seed initial 0 ≤ t
  · rw [dif_pos hfirst]
    have hrestart := hseed (t - rawSwitchGaps seed initial 0)
      (sub_nonneg.mpr hfirst)
    rw [show rawSwitchGaps seed initial 0 +
        (t - rawSwitchGaps seed initial 0) = t by ring] at hrestart
    exact hrestart
  · rw [dif_neg hfirst]
    exact stateAt_eq_initial_of_lt_firstSwitch initial seed t
      (lt_of_not_ge hfirst)

/-- The fixed-time raw first-step recursion written solely in terms of the
literal raw tail-and-head factor.  Together with its exact product law, this
is the source endpoint-law representation to be integrated next. -/
theorem ae_stateAt_eq_firstStepStateAt_raw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      stateAt initial seed t =
        AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t
          (rawSwitchTailAndFirstGap initial seed) := by
  have hstep := ae_stateAt_eq_firstStep
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial t
  filter_upwards [hstep] with seed hseed
  have hfactor : rawSwitchTailAndFirstGap initial seed =
      (rawSwitchTailPair initial seed, rawSwitchGaps seed initial 0) := by
    apply Prod.ext
    · exact (rawSwitchTailPair_eq_factorTail initial seed).symm
    · exact rawSwitchTailAndFirstGap_snd initial seed
  rw [hfactor]
  simp only [AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt]
  rw [twoStateGapsOfPair_rawSwitchTailPair]
  exact hseed

/-- Exact fixed-time law of the raw alternating endpoint, expressed as the
measurable first-step functional of its literal source tail-and-head product
factor.  This is a path-law representation; evaluating that product integral
as the closed-form CTMC kernel is a subsequent analytic step. -/
theorem stateAt_hasLaw_firstStepStateAt_raw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    HasLaw (fun seed => stateAt initial seed t)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
          (if initial = 0 then ProbabilityTheory.expMeasure switchIJ
          else ProbabilityTheory.expMeasure switchJI)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let tailLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let factorLaw := tailLaw.prod headLaw
  have hfactor : HasLaw (rawSwitchTailAndFirstGap initial) factorLaw
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [tailLaw, headLaw, factorLaw] using
      (rawSwitchTailAndFirstGap_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial)
  have hfirst : HasLaw
      (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        factorLaw)
      factorLaw :=
    ⟨(AppliedModelingLib.Probability.TwoStateSwitching.measurable_firstStepStateAt
      initial t).aemeasurable, rfl⟩
  have hcomposed := hfirst.fun_comp hfactor
  refine hcomposed.congr ?_
  exact ae_stateAt_eq_firstStepStateAt_raw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial t

/-- The raw source probability of occupying the opposite state satisfies the
literal first-step renewal integral equation.  This is transported from the
source tail-and-head product law, so the integral has the actual exponential
holding-time measure and the actual opposite-state raw tail path.  It is the
measure-level input for a later analytic evaluation to the CTMC closed form. -/
theorem measure_rawStateAt_eq_other_eq_lintegral
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      {seed | stateAt initial seed t =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
      ∫⁻ tail,
        (if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI)
          {head | head ≤ t ∧
            AppliedModelingLib.Probability.TwoStateSwitching.stateAt
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
              (t - head) =
                AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchJI)) := by
  let tailLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let factorLaw := tailLaw.prod headLaw
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
  letI : IsProbabilityMeasure headLaw := by
    dsimp [headLaw]
    split_ifs <;>
      apply ProbabilityTheory.isProbabilityMeasure_expMeasure
    · exact hswitchIJ
    · exact hswitchJI
  have hstate : Measurable (fun seed : GN21RawCycleSeed => stateAt initial seed t) := by
    exact (measurable_stateAt initial).comp (measurable_id.prodMk measurable_const)
  have hfirst : HasLaw (fun seed => stateAt initial seed t)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        factorLaw)
      sourceLaw := by
    simpa [tailLaw, headLaw, factorLaw, sourceLaw] using
      (stateAt_hasLaw_firstStepStateAt_raw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial t)
  calc
    sourceLaw {seed | stateAt initial seed t =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
        (Measure.map (fun seed => stateAt initial seed t) sourceLaw)
          {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          rw [Measure.map_apply hstate (measurableSet_singleton _)]
          rfl
    _ = (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        factorLaw) {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          rw [hfirst.map_eq]
    _ = factorLaw
        ((AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t) ⁻¹'
          {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}) := by
          rw [Measure.map_apply
            (AppliedModelingLib.Probability.TwoStateSwitching.measurable_firstStepStateAt
              initial t)
            (measurableSet_singleton _)]
    _ = ∫⁻ tail, headLaw
        {head | head ≤ t ∧
          AppliedModelingLib.Probability.TwoStateSwitching.stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
            (t - head) =
              AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂tailLaw := by
          exact AppliedModelingLib.Probability.TwoStateSwitching.measure_firstStepStateAt_eq_other
            initial t
    _ = ∫⁻ tail,
        (if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI)
          {head | head ≤ t ∧
            AppliedModelingLib.Probability.TwoStateSwitching.stateAt
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
              (t - head) =
                AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchJI)) := by
          rfl

/-- Transport a fixed endpoint event through the exact raw switch-pair law.
This is the source-to-tail identification used to turn the generic first-step
integral into a Volterra equation stated wholly in terms of raw endpoint
probabilities. -/
theorem measure_rawSwitchGapPair_stateAt_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (t : Real) :
    ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchJI))
      {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) t = target} =
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        {seed | stateAt initial seed t = target} := by
  let pairLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  have hpair : HasLaw rawSwitchGapPair pairLaw sourceLaw := by
    simpa [pairLaw, sourceLaw] using
      (rawSwitchGapPair_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI)
  have hendpoint : Measurable (fun pair : (Nat -> Real) × (Nat -> Real) =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) t) := by
    exact (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAt initial).comp
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair).prodMk
        measurable_const)
  calc
    pairLaw {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) t = target} =
        (Measure.map rawSwitchGapPair sourceLaw)
          {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
            (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) t =
              target} := by
          rw [hpair.map_eq]
    _ = sourceLaw
        (rawSwitchGapPair ⁻¹' {pair |
          AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
            (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) t =
              target}) := by
          exact Measure.map_apply measurable_rawSwitchGapPair
            (hendpoint (measurableSet_singleton _))
    _ = sourceLaw {seed | stateAt initial seed t = target} := by
          congr 1
          ext seed
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
          rfl

/-- The literal raw endpoint events for the initial and opposite states
partition the source probability law.  Together with the first-step Volterra
equation, this supplies both equations of the two-state renewal system before
any real-valued density or differentiability argument is introduced. -/
theorem measure_rawStateAt_eq_initial_add_eq_otherState
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        {seed | stateAt initial seed t = initial} +
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        {seed | stateAt initial seed t =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} = 1 := by
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure sourceLaw := by
    simpa [sourceLaw] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let Einitial : Set GN21RawCycleSeed :=
    {seed | stateAt initial seed t = initial}
  let Eother : Set GN21RawCycleSeed :=
    {seed | stateAt initial seed t =
      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
  have hinitial : MeasurableSet Einitial := by
    exact ((measurable_stateAt initial).comp
      (measurable_id.prodMk measurable_const)) (measurableSet_singleton _)
  have hother : MeasurableSet Eother := by
    exact ((measurable_stateAt initial).comp
      (measurable_id.prodMk measurable_const)) (measurableSet_singleton _)
  have hdisjoint : Disjoint Einitial Eother := by
    refine Set.disjoint_left.2 ?_
    intro seed hinitial hother
    exact AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne initial
      (hother.symm.trans hinitial)
  have hunion : Einitial ∪ Eother = Set.univ := by
    ext seed
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    simpa [stateAt] using
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAt_eq_initial_or_eq_otherState
        initial (rawSwitchGaps seed) t)
  calc
    sourceLaw {seed | stateAt initial seed t = initial} +
        sourceLaw {seed | stateAt initial seed t =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
        sourceLaw (Einitial ∪ Eother) := by
          symm
          exact measure_union hdisjoint hother
    _ = sourceLaw Set.univ := by rw [hunion]
    _ = 1 := measure_univ

/-- Volterra form of the literal raw first-step equation.  The integrand is
the raw probability that the opposite-state source path remains in that state
at the residual time, and the outer measure is the actual initial-state
exponential holding-time law.  This is the source-faithful renewal equation
to be solved before identifying the closed-form CTMC transition probability. -/
theorem measure_rawStateAt_eq_other_eq_lintegral_rawTail
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      {seed | stateAt initial seed t =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
      ∫⁻ head,
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          {seed | head ≤ t ∧ stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            seed (t - head) =
              AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
          else ProbabilityTheory.expMeasure switchJI) := by
  let tailLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let factorLaw := tailLaw.prod headLaw
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
  letI : IsProbabilityMeasure headLaw := by
    dsimp [headLaw]
    split_ifs <;>
      apply ProbabilityTheory.isProbabilityMeasure_expMeasure
    · exact hswitchIJ
    · exact hswitchJI
  have hstate : Measurable (fun seed : GN21RawCycleSeed => stateAt initial seed t) := by
    exact (measurable_stateAt initial).comp (measurable_id.prodMk measurable_const)
  have hfirst : HasLaw (fun seed => stateAt initial seed t)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        factorLaw)
      sourceLaw := by
    simpa [tailLaw, headLaw, factorLaw, sourceLaw] using
      (stateAt_hasLaw_firstStepStateAt_raw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial t)
  have htailEndpoint (u : Real) :
      tailLaw {tail |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAt
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail) u =
            AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
      sourceLaw {seed | stateAt
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) seed u =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
    simpa [tailLaw, sourceLaw] using
      (measure_rawSwitchGapPair_stateAt_eq
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) u)
  calc
    sourceLaw {seed | stateAt initial seed t =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
        (Measure.map (fun seed => stateAt initial seed t) sourceLaw)
          {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          rw [Measure.map_apply hstate (measurableSet_singleton _)]
          rfl
    _ = (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t)
        factorLaw) {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          rw [hfirst.map_eq]
    _ = factorLaw
        ((AppliedModelingLib.Probability.TwoStateSwitching.firstStepStateAt initial t) ⁻¹'
          {AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}) := by
          rw [Measure.map_apply
            (AppliedModelingLib.Probability.TwoStateSwitching.measurable_firstStepStateAt
              initial t)
            (measurableSet_singleton _)]
    _ = ∫⁻ head, tailLaw {tail | head ≤ t ∧
        AppliedModelingLib.Probability.TwoStateSwitching.stateAt
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
          (t - head) =
            AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} ∂headLaw := by
          exact AppliedModelingLib.Probability.TwoStateSwitching.measure_firstStepStateAt_eq_other_lintegral_head
            initial t
    _ = ∫⁻ head, sourceLaw {seed | head ≤ t ∧ stateAt
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
        seed (t - head) =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} ∂headLaw := by
          apply lintegral_congr
          intro head
          by_cases hhead : head ≤ t
          · calc
              tailLaw {tail | head ≤ t ∧
                  AppliedModelingLib.Probability.TwoStateSwitching.stateAt
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
                    (t - head) =
                      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
                  tailLaw {tail |
                    AppliedModelingLib.Probability.TwoStateSwitching.stateAt
                      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                      (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair tail)
                      (t - head) =
                        AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
                    congr 1
                    ext tail
                    simp [hhead]
              _ = sourceLaw {seed | stateAt
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    seed (t - head) =
                      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} :=
                    htailEndpoint (t - head)
              _ = sourceLaw {seed | head ≤ t ∧ stateAt
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    seed (t - head) =
                      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
                    congr 1
                    ext seed
                    simp [hhead]
          · simp [hhead]
    _ = ∫⁻ head,
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          {seed | head ≤ t ∧ stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            seed (t - head) =
              AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
          else ProbabilityTheory.expMeasure switchJI) := by
          rfl

/-- Indicator form of the raw two-state renewal equation.  The integrand is
the literal initial-state mass of the switched raw path, and the indicator
retains the nonnegative residual-time domain explicitly.  This is the exact
`ENNReal` precursor to the bounded real exponential-convolution equation. -/
theorem rawStateProbability_other_eq_lintegral_indicator
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
      ∫⁻ head,
        (Set.Iic t).indicator (fun head =>
          rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head
        ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI) := by
  let sourceLaw := gn21RawCycleSeedMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  calc
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
        sourceLaw {seed | stateAt initial seed t =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          exact rawStateProbability_eq_measure_rawStateAt
            muI muJ arrivalI arrivalJ switchIJ switchJI initial
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t
    _ = ∫⁻ head, sourceLaw {seed | head ≤ t ∧ stateAt
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
        seed (t - head) =
          AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
        ∂headLaw := by
          simpa [sourceLaw, headLaw] using
            (measure_rawStateAt_eq_other_eq_lintegral_rawTail
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initial t)
    _ = ∫⁻ head,
        (Set.Iic t).indicator (fun head =>
          rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head ∂headLaw := by
          apply lintegral_congr
          intro head
          by_cases hhead : head ≤ t
          · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hhead)]
            calc
              sourceLaw {seed | head ≤ t ∧ stateAt
                  (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                  seed (t - head) =
                    AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} =
                  sourceLaw {seed | stateAt
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    seed (t - head) =
                      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
                    congr 1
                    ext seed
                    simp [hhead]
              _ = rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                    (t - head) := by
                    symm
                    exact rawStateProbability_eq_measure_rawStateAt
                      muI muJ arrivalI arrivalJ switchIJ switchJI
                      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
                      (t - head)
          · rw [Set.indicator_of_notMem (Set.mem_Iic.not.mpr hhead)]
            simp [hhead]
    _ = ∫⁻ head,
        (Set.Iic t).indicator (fun head =>
          rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head ∂(if initial = 0 then
              ProbabilityTheory.expMeasure switchIJ else ProbabilityTheory.expMeasure switchJI) := by
          rfl

/-- Finite real integral form of the source renewal equation.  The integrand
is still written as the `toReal` of the exact indicator-valued mass so that
the next density step cannot silently discard finiteness or the residual-time
indicator. -/
theorem rawStateProbabilityReal_other_eq_integral_indicator
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
      ∫ head,
        ((Set.Iic t).indicator (fun head =>
          rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head).toReal
        ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI) := by
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let f : Real -> ℝ≥0∞ := (Set.Iic t).indicator (fun head =>
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
      (t - head))
  have hf : Measurable f := by
    apply Measurable.indicator
    · exact (measurable_rawStateProbability
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)).comp
          (measurable_const.sub measurable_id)
    · exact measurableSet_Iic
  have hfinite : ∀ᵐ head ∂headLaw, f head < ∞ := by
    apply ae_of_all
    intro head
    by_cases hhead : head ∈ Set.Iic t
    · rw [show f head = rawStateProbability
        muI muJ arrivalI arrivalJ switchIJ switchJI
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (t - head) by simp [f, hhead]]
      letI : IsProbabilityMeasure
          (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
        isProbabilityMeasure_rawSwitchPathLaw
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI
      exact lt_top_iff_ne_top.mpr
        (AppliedModelingLib.Probability.TwoStateSwitching.stateProbability_ne_top
          (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
          (t - head))
    · simp [f, hhead]
  have hrealIntegral := MeasureTheory.integral_toReal hf.aemeasurable hfinite
  change (rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial
    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t).toReal = _
  rw [rawStateProbability_other_eq_lintegral_indicator
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial t]
  simpa only [f, headLaw] using hrealIntegral.symm

/-- The preceding real renewal equation, with the real endpoint mass exposed
inside the residual-time indicator. -/
theorem rawStateProbabilityReal_other_eq_integral_indicatorReal
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
      ∫ head,
        (Set.Iic t).indicator (fun head =>
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head
        ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI) := by
  calc
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
        ∫ head,
          ((Set.Iic t).indicator (fun head =>
            rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (t - head)) head).toReal
          ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
          else ProbabilityTheory.expMeasure switchJI) := by
          exact rawStateProbabilityReal_other_eq_integral_indicator
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initial t
    _ = ∫ head,
        (Set.Iic t).indicator (fun head =>
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            (t - head)) head
        ∂(if initial = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI) := by
          apply integral_congr_ae
          apply ae_of_all
          intro head
          by_cases hhead : head ∈ Set.Iic t <;>
            simp [rawStateProbabilityReal, hhead]

/-- Lebesgue-density form of the literal raw renewal equation.  This is the
first point at which the exponential measure is converted to its continuous
density; the source endpoint mass and the residual-time indicator remain
explicit. -/
theorem rawStateProbabilityReal_other_eq_integral_pdf
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) (t : Real) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) t =
      if initial = 0 then
        ∫ head, ProbabilityTheory.exponentialPDFReal switchIJ head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (t - head)) head
          ∂volume
      else
        ∫ head, ProbabilityTheory.exponentialPDFReal switchJI head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
              (t - head)) head
          ∂volume := by
  by_cases hinitial : initial = 0
  · subst initial
    let M : AppliedModelingLib.Probability.Exponential.Model := ⟨switchIJ, hswitchIJ⟩
    calc
      rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
          ∫ head,
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (t - head)) head
            ∂ProbabilityTheory.expMeasure switchIJ := by
              simpa using
                (rawStateProbabilityReal_other_eq_integral_indicatorReal
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI 0 t)
      _ = ∫ head, ProbabilityTheory.exponentialPDFReal switchIJ head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
              (t - head)) head ∂volume := by
              exact M.integral_expMeasure_eq_integral_pdfReal_mul _
      _ = if (0 : Fin 2) = 0 then
          ∫ head, ProbabilityTheory.exponentialPDFReal switchIJ head *
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (t - head)) head ∂volume
        else
          ∫ head, ProbabilityTheory.exponentialPDFReal switchJI head *
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
                (t - head)) head ∂volume := by simp
  · have hinitial_one : initial = 1 := by
      fin_cases initial <;> simp_all
    subst initial
    let M : AppliedModelingLib.Probability.Exponential.Model := ⟨switchJI, hswitchJI⟩
    calc
      rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
          ∫ head,
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (t - head)) head
            ∂ProbabilityTheory.expMeasure switchJI := by
              simpa using
                (rawStateProbabilityReal_other_eq_integral_indicatorReal
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI 1 t)
      _ = ∫ head, ProbabilityTheory.exponentialPDFReal switchJI head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
              (t - head)) head ∂volume := by
              exact M.integral_expMeasure_eq_integral_pdfReal_mul _
      _ = if (1 : Fin 2) = 0 then
          ∫ head, ProbabilityTheory.exponentialPDFReal switchIJ head *
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (t - head)) head ∂volume
        else
          ∫ head, ProbabilityTheory.exponentialPDFReal switchJI head *
            (Set.Iic t).indicator (fun head =>
              rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
                (t - head)) head ∂volume := by simp

/-- For a source path starting at state `0`, the density-form renewal equation
is a compact interval convolution.  The support restriction is supplied by
the exponential density and the retained residual-time indicator, not by an
assumed CTMC semigroup. -/
theorem rawStateProbabilityReal_other_zero_eq_setIntegral_Icc_convolution
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
      ∫ head in Set.Icc 0 t, switchIJ * Real.exp (-(switchIJ * head)) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
          (t - head) := by
  calc
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
        ∫ head, ProbabilityTheory.exponentialPDFReal switchIJ head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
              (t - head)) head := by
          simpa using (rawStateProbabilityReal_other_eq_integral_pdf
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI 0 t)
    _ = ∫ head in Set.Icc 0 t, switchIJ * Real.exp (-(switchIJ * head)) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
          (t - head) := by
          exact AppliedModelingLib.Probability.Exponential.integral_pdfReal_mul_indicator_eq_setIntegral_Icc_convolution
            switchIJ t ht _

/-- The analogous compact interval convolution for a source path starting at
state `1`. -/
theorem rawStateProbabilityReal_other_one_eq_setIntegral_Icc_convolution
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
      ∫ head in Set.Icc 0 t, switchJI * Real.exp (-(switchJI * head)) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
          (t - head) := by
  calc
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
        ∫ head, ProbabilityTheory.exponentialPDFReal switchJI head *
          (Set.Iic t).indicator (fun head =>
            rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
              (t - head)) head := by
          simpa using (rawStateProbabilityReal_other_eq_integral_pdf
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI 1 t)
    _ = ∫ head in Set.Icc 0 t, switchJI * Real.exp (-(switchJI * head)) *
        rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
          (t - head) := by
          exact AppliedModelingLib.Probability.Exponential.integral_pdfReal_mul_indicator_eq_setIntegral_Icc_convolution
            switchJI t ht _

/-- Reversed-time weighted-primitive form of the literal state-`0` renewal
equation.  Its right side is continuous on compact nonnegative intervals by
the bounded-measurable primitive theorem above. -/
theorem rawStateProbabilityReal_other_zero_eq_weighted_primitive
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
      (switchIJ * Real.exp (-(switchIJ * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (switchIJ * u) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) u := by
  calc
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
        ∫ head in Set.Icc 0 t, switchIJ * Real.exp (-(switchIJ * head)) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
            (t - head) :=
              rawStateProbabilityReal_other_zero_eq_setIntegral_Icc_convolution
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI t ht
    _ = (switchIJ * Real.exp (-(switchIJ * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (switchIJ * u) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) u := by
          exact AppliedModelingLib.Probability.Exponential.setIntegral_Icc_exponential_convolution_eq_weighted_primitive
            switchIJ t ht _

/-- Reversed-time weighted-primitive form of the literal state-`1` renewal
equation. -/
theorem rawStateProbabilityReal_other_one_eq_weighted_primitive
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
      (switchJI * Real.exp (-(switchJI * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (switchJI * u) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) u := by
  calc
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
        ∫ head in Set.Icc 0 t, switchJI * Real.exp (-(switchJI * head)) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
            (t - head) :=
              rawStateProbabilityReal_other_one_eq_setIntegral_Icc_convolution
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI t ht
    _ = (switchJI * Real.exp (-(switchJI * t))) *
        ∫ u in Set.Icc 0 t, Real.exp (switchJI * u) *
          rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) u := by
          exact AppliedModelingLib.Probability.Exponential.setIntegral_Icc_exponential_convolution_eq_weighted_primitive
            switchJI t ht _

/-- The literal probability of switching from source state `0` is continuous
on every compact nonnegative time interval.  This is derived from the source
renewal equation and bounded measurability, rather than postulated as an
abstract CTMC transition regularity condition. -/
theorem continuousOn_rawStateProbabilityReal_other_zero_Icc
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (T : Real) (hT : 0 ≤ T) :
    ContinuousOn
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0))
      (Set.Icc 0 T) := by
  let primitive : Real -> Real := fun t => ∫ u in Set.Icc 0 t,
    Real.exp (switchIJ * u) *
      rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) u
  have hprimitive : ContinuousOn primitive (Set.Icc 0 T) := by
    exact continuousOn_rawStateProbabilityReal_exp_weighted_primitive
      muI muJ arrivalI arrivalJ switchIJ switchJI switchIJ
      harrivalI harrivalJ hswitchIJ hswitchJI
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) 0 T
  have hcoefficient : Continuous (fun t : Real =>
      switchIJ * Real.exp (-(switchIJ * t))) := by
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  apply (hcoefficient.continuousOn.mul hprimitive).congr
  intro t ht
  simpa [primitive] using
    (rawStateProbabilityReal_other_zero_eq_weighted_primitive
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht.1)

/-- The literal probability of switching from source state `1` is continuous
on every compact nonnegative time interval. -/
theorem continuousOn_rawStateProbabilityReal_other_one_Icc
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (T : Real) (hT : 0 ≤ T) :
    ContinuousOn
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1))
      (Set.Icc 0 T) := by
  let primitive : Real -> Real := fun t => ∫ u in Set.Icc 0 t,
    Real.exp (switchJI * u) *
      rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) u
  have hprimitive : ContinuousOn primitive (Set.Icc 0 T) := by
    exact continuousOn_rawStateProbabilityReal_exp_weighted_primitive
      muI muJ arrivalI arrivalJ switchIJ switchJI switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) 0 T
  have hcoefficient : Continuous (fun t : Real =>
      switchJI * Real.exp (-(switchJI * t))) := by
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  apply (hcoefficient.continuousOn.mul hprimitive).congr
  intro t ht
  simpa [primitive] using
    (rawStateProbabilityReal_other_one_eq_weighted_primitive
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht.1)

/-- Half-line continuity of the literal source `0 → 1` endpoint
probability, assembled from its compact-interval continuity. -/
theorem continuousOn_rawStateProbabilityReal_other_zero_Ici
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    ContinuousOn
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0))
      (Set.Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hcont := continuousOn_rawStateProbabilityReal_other_zero_Icc
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI (t + 1) (by linarith)
  have hIcc : Set.Icc 0 (t + 1) ∈ 𝓝[Set.Ici 0] t := by
    have hupper : Set.Iio (t + 1) ∈ 𝓝[Set.Ici 0] t :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, hupper] with u hu0 huupper
    exact ⟨hu0, huupper.le⟩
  exact (hcont t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
    hIcc

/-- Half-line continuity of the literal source `1 → 0` endpoint
probability. -/
theorem continuousOn_rawStateProbabilityReal_other_one_Ici
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    ContinuousOn
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1))
      (Set.Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hcont := continuousOn_rawStateProbabilityReal_other_one_Icc
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI (t + 1) (by linarith)
  have hIcc : Set.Icc 0 (t + 1) ∈ 𝓝[Set.Ici 0] t := by
    have hupper : Set.Iio (t + 1) ∈ 𝓝[Set.Ici 0] t :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, hupper] with u hu0 huupper
    exact ⟨hu0, huupper.le⟩
  exact (hcont t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
    hIcc

/-- On positive elapsed times, the literal source probability of moving from
state `0` to state `1` satisfies its first forward equation.  The proof uses
the just-derived continuous weighted primitive and FTC-1; it does not assume
a transition semigroup. -/
theorem hasDerivAt_rawStateProbabilityReal_other_zero_of_pos
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 < t) :
    HasDerivAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0))
      (switchIJ * (1 - rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t) -
        switchIJ * rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI 0
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t)
      t := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let stay1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1 1
  let weighted : Real -> Real := fun u =>
    Real.exp (switchIJ * u) * stay1 u
  let primitiveSet : Real -> Real := fun u => ∫ x in Set.Icc 0 u, weighted x
  let primitiveInterval : Real -> Real := fun u => ∫ x in (0 : Real)..u, weighted x
  let coefficient : Real -> Real := fun u =>
    switchIJ * Real.exp (-(switchIJ * u))
  have hq1cont : ContinuousAt q1 t := by
    have hcont := continuousOn_rawStateProbabilityReal_other_one_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI (t + 1) (by linarith)
    exact hcont.continuousAt (Icc_mem_nhds ht (by linarith))
  have hstay1_eq : stay1 = fun u => 1 - q1 u := by
    funext u
    dsimp [stay1, q1]
    have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1 u
    norm_num at hpartition ⊢
    linarith
  have hstay1cont : ContinuousAt stay1 t := by
    rw [hstay1_eq]
    exact continuousAt_const.sub hq1cont
  have hweightedcont : ContinuousAt weighted t := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.mul
      hstay1cont
  have hweightedMeas : Measurable weighted := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)).mul
        (measurable_rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI 1 1)
  have hweightedInt : IntervalIntegrable weighted volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
    exact rawStateProbabilityReal_exp_weighted_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI switchIJ
      harrivalI harrivalJ hswitchIJ hswitchJI 1 1 0 t
  have hprimitiveIntervalDeriv : HasDerivAt primitiveInterval (weighted t) t := by
    exact intervalIntegral.integral_hasDerivAt_right hweightedInt
      hweightedMeas.stronglyMeasurable.stronglyMeasurableAtFilter hweightedcont
  have hprimitiveEq : primitiveSet =ᶠ[𝓝 t] primitiveInterval := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    dsimp [primitiveSet, primitiveInterval]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu.le]
  have hprimitiveDeriv : HasDerivAt primitiveSet (weighted t) t :=
    hprimitiveIntervalDeriv.congr_of_eventuallyEq hprimitiveEq
  have hcoefficientDeriv : HasDerivAt coefficient
      (-switchIJ * coefficient t) t := by
    have hlinear : HasDerivAt (fun u : Real => -(switchIJ * u)) (-switchIJ) t := by
      simpa using (hasDerivAt_id t).const_mul (-switchIJ)
    have hexp := hlinear.exp
    dsimp [coefficient]
    convert hexp.const_mul switchIJ using 1 <;> ring
  have hproductDeriv : HasDerivAt
      (fun u => coefficient u * primitiveSet u)
      ((-switchIJ * coefficient t) * primitiveSet t + coefficient t * weighted t) t :=
    hcoefficientDeriv.mul hprimitiveDeriv
  have hq0Eq : q0 =ᶠ[𝓝 t] fun u => coefficient u * primitiveSet u := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    simpa [q0, coefficient, primitiveSet, weighted, stay1] using
      (rawStateProbabilityReal_other_zero_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI u hu.le)
  have hq0Deriv : HasDerivAt q0
      ((-switchIJ * coefficient t) * primitiveSet t + coefficient t * weighted t) t :=
    hproductDeriv.congr_of_eventuallyEq hq0Eq
  have hq0value : q0 t = coefficient t * primitiveSet t := by
    simpa [q0, coefficient, primitiveSet, weighted, stay1] using
      (rawStateProbabilityReal_other_zero_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI t ht.le)
  have hexp_cancel : Real.exp (-(switchIJ * t)) *
      Real.exp (switchIJ * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hderivValue :
      (-switchIJ * coefficient t) * primitiveSet t + coefficient t * weighted t =
        switchIJ * (1 - q1 t) - switchIJ * q0 t := by
    dsimp [weighted]
    rw [show stay1 t = 1 - q1 t by rw [hstay1_eq], hq0value]
    dsimp [coefficient, weighted]
    calc
      -switchIJ * (switchIJ * Real.exp (-(switchIJ * t))) * primitiveSet t +
          switchIJ * Real.exp (-(switchIJ * t)) *
            (Real.exp (switchIJ * t) * (1 - q1 t)) =
          -switchIJ * (switchIJ * Real.exp (-(switchIJ * t)) * primitiveSet t) +
            switchIJ * (Real.exp (-(switchIJ * t)) *
              Real.exp (switchIJ * t)) * (1 - q1 t) := by ring
      _ = switchIJ * (1 - q1 t) -
          switchIJ * (switchIJ * Real.exp (-(switchIJ * t)) * primitiveSet t) := by
            rw [hexp_cancel]
            ring
  rw [show rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) = q0 by rfl]
  simpa [q0, q1] using hderivValue ▸ hq0Deriv

/-- The symmetric positive-time forward equation for the literal source
probability of moving from state `1` to state `0`. -/
theorem hasDerivAt_rawStateProbabilityReal_other_one_of_pos
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 < t) :
    HasDerivAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1))
      (switchJI * (1 - rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 0
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t) -
        switchJI * rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI 1
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t)
      t := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let stay0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0 0
  let weighted : Real -> Real := fun u =>
    Real.exp (switchJI * u) * stay0 u
  let primitiveSet : Real -> Real := fun u => ∫ x in Set.Icc 0 u, weighted x
  let primitiveInterval : Real -> Real := fun u => ∫ x in (0 : Real)..u, weighted x
  let coefficient : Real -> Real := fun u =>
    switchJI * Real.exp (-(switchJI * u))
  have hq0cont : ContinuousAt q0 t := by
    have hcont := continuousOn_rawStateProbabilityReal_other_zero_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI (t + 1) (by linarith)
    exact hcont.continuousAt (Icc_mem_nhds ht (by linarith))
  have hstay0_eq : stay0 = fun u => 1 - q0 u := by
    funext u
    dsimp [stay0, q0]
    have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0 u
    norm_num at hpartition ⊢
    linarith
  have hstay0cont : ContinuousAt stay0 t := by
    rw [hstay0_eq]
    exact continuousAt_const.sub hq0cont
  have hweightedcont : ContinuousAt weighted t := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.mul
      hstay0cont
  have hweightedMeas : Measurable weighted := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)).mul
        (measurable_rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI 0 0)
  have hweightedInt : IntervalIntegrable weighted volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
    exact rawStateProbabilityReal_exp_weighted_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0 0 0 t
  have hprimitiveIntervalDeriv : HasDerivAt primitiveInterval (weighted t) t := by
    exact intervalIntegral.integral_hasDerivAt_right hweightedInt
      hweightedMeas.stronglyMeasurable.stronglyMeasurableAtFilter hweightedcont
  have hprimitiveEq : primitiveSet =ᶠ[𝓝 t] primitiveInterval := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    dsimp [primitiveSet, primitiveInterval]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu.le]
  have hprimitiveDeriv : HasDerivAt primitiveSet (weighted t) t :=
    hprimitiveIntervalDeriv.congr_of_eventuallyEq hprimitiveEq
  have hcoefficientDeriv : HasDerivAt coefficient
      (-switchJI * coefficient t) t := by
    have hlinear : HasDerivAt (fun u : Real => -(switchJI * u)) (-switchJI) t := by
      simpa using (hasDerivAt_id t).const_mul (-switchJI)
    have hexp := hlinear.exp
    dsimp [coefficient]
    convert hexp.const_mul switchJI using 1 <;> ring
  have hproductDeriv : HasDerivAt
      (fun u => coefficient u * primitiveSet u)
      ((-switchJI * coefficient t) * primitiveSet t + coefficient t * weighted t) t :=
    hcoefficientDeriv.mul hprimitiveDeriv
  have hq1Eq : q1 =ᶠ[𝓝 t] fun u => coefficient u * primitiveSet u := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    simpa [q1, coefficient, primitiveSet, weighted, stay0] using
      (rawStateProbabilityReal_other_one_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI u hu.le)
  have hq1Deriv : HasDerivAt q1
      ((-switchJI * coefficient t) * primitiveSet t + coefficient t * weighted t) t :=
    hproductDeriv.congr_of_eventuallyEq hq1Eq
  have hq1value : q1 t = coefficient t * primitiveSet t := by
    simpa [q1, coefficient, primitiveSet, weighted, stay0] using
      (rawStateProbabilityReal_other_one_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI t ht.le)
  have hexp_cancel : Real.exp (-(switchJI * t)) *
      Real.exp (switchJI * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hderivValue :
      (-switchJI * coefficient t) * primitiveSet t + coefficient t * weighted t =
        switchJI * (1 - q0 t) - switchJI * q1 t := by
    dsimp [weighted]
    rw [show stay0 t = 1 - q0 t by rw [hstay0_eq], hq1value]
    dsimp [coefficient, weighted]
    calc
      -switchJI * (switchJI * Real.exp (-(switchJI * t))) * primitiveSet t +
          switchJI * Real.exp (-(switchJI * t)) *
            (Real.exp (switchJI * t) * (1 - q0 t)) =
          -switchJI * (switchJI * Real.exp (-(switchJI * t)) * primitiveSet t) +
            switchJI * (Real.exp (-(switchJI * t)) *
              Real.exp (switchJI * t)) * (1 - q0 t) := by ring
      _ = switchJI * (1 - q0 t) -
          switchJI * (switchJI * Real.exp (-(switchJI * t)) * primitiveSet t) := by
            rw [hexp_cancel]
            ring
  rw [show rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) = q1 by rfl]
  simpa [q0, q1] using hderivValue ▸ hq1Deriv

/-- The literal raw process has zero opposite-state mass at time zero.  This
uses the source first-step equation and the no-atom-at-zero property of the
active exponential hold; it is the initial condition needed by the eventual
real-valued renewal/ODE bridge. -/
theorem rawStateProbability_otherState_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) 0 = 0 := by
  let headLaw := if initial = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  have hhead_pos : ∀ᵐ head ∂headLaw, 0 < head := by
    fin_cases initial
    · let M : AppliedModelingLib.Probability.Exponential.Model :=
        ⟨switchIJ, hswitchIJ⟩
      rw [MeasureTheory.ae_iff]
      simpa [headLaw, Set.compl_setOf, M,
        AppliedModelingLib.Probability.Exponential.Model.measure] using M.measure_Iic_zero
    · let M : AppliedModelingLib.Probability.Exponential.Model :=
        ⟨switchJI, hswitchJI⟩
      rw [MeasureTheory.ae_iff]
      simpa [headLaw, Set.compl_setOf, M,
        AppliedModelingLib.Probability.Exponential.Model.measure] using M.measure_Iic_zero
  calc
    rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) 0 =
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          {seed | stateAt initial seed 0 =
            AppliedModelingLib.Probability.TwoStateSwitching.otherState initial} := by
          exact rawStateProbability_eq_measure_rawStateAt
            muI muJ arrivalI arrivalJ switchIJ switchJI initial
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) 0
    _ = ∫⁻ head,
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          {seed | head ≤ 0 ∧ stateAt
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
            seed (0 - head) =
              AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
          ∂headLaw := by
          simpa [headLaw] using
            (measure_rawStateAt_eq_other_eq_lintegral_rawTail
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initial 0)
    _ = 0 := by
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [hhead_pos] with head hhead
          simp [not_le_of_gt hhead]

theorem rawStateProbabilityReal_otherState_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial : Fin 2) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) 0 = 0 := by
  unfold rawStateProbabilityReal
  rw [rawStateProbability_otherState_zero
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial]
  rfl

/-- At the calendar-time boundary, the literal source path has the expected
right derivative from state `0` to state `1`.  A two-sided derivative is not
claimed because the raw path is intentionally defined on negative times by
its initial state. -/
theorem hasDerivWithinAt_rawStateProbabilityReal_other_zero_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    HasDerivWithinAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0))
      switchIJ (Set.Ici 0) 0 := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let stay1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1 1
  let weighted : Real -> Real := fun u =>
    Real.exp (switchIJ * u) * stay1 u
  let primitiveSet : Real -> Real := fun u => ∫ x in Set.Icc 0 u, weighted x
  let primitiveInterval : Real -> Real := fun u => ∫ x in (0 : Real)..u, weighted x
  let coefficient : Real -> Real := fun u =>
    switchIJ * Real.exp (-(switchIJ * u))
  have hq1Within : ContinuousWithinAt q1 (Set.Ici 0) 0 := by
    have hcont := continuousOn_rawStateProbabilityReal_other_one_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1 zero_le_one
    exact (hcont 0 (by simp)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (by norm_num))
  have hstay1_eq : stay1 = fun u => 1 - q1 u := by
    funext u
    dsimp [stay1, q1]
    have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1 u
    norm_num at hpartition ⊢
    linarith
  have hstay1Within : ContinuousWithinAt stay1 (Set.Ici 0) 0 := by
    rw [hstay1_eq]
    exact continuousWithinAt_const.sub hq1Within
  have hweightedWithin : ContinuousWithinAt weighted (Set.Ici 0) 0 := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousWithinAt.mul
      hstay1Within
  have hweightedRight : ContinuousWithinAt weighted (Set.Ioi 0) 0 :=
    hweightedWithin.mono Set.Ioi_subset_Ici_self
  have hweightedMeas : Measurable weighted := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)).mul
        (measurable_rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI 1 1)
  have hweightedInt : IntervalIntegrable weighted volume 0 0 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le le_rfl]
    exact rawStateProbabilityReal_exp_weighted_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI switchIJ
      harrivalI harrivalJ hswitchIJ hswitchJI 1 1 0 0
  have hprimitiveIntervalDeriv : HasDerivWithinAt primitiveInterval (weighted 0)
      (Set.Ici 0) 0 := by
    exact intervalIntegral.integral_hasDerivWithinAt_right hweightedInt
      hweightedMeas.stronglyMeasurable.stronglyMeasurableAtFilter hweightedRight
  have hprimitiveEq : primitiveSet =ᶠ[𝓝[Set.Ici 0] 0] primitiveInterval := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp [primitiveSet, primitiveInterval]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu]
  have hprimitiveDeriv : HasDerivWithinAt primitiveSet (weighted 0)
      (Set.Ici 0) 0 :=
    hprimitiveIntervalDeriv.congr_of_eventuallyEq hprimitiveEq (by
      simp [primitiveSet, primitiveInterval])
  have hcoefficientDeriv : HasDerivWithinAt coefficient
      (-switchIJ * coefficient 0) (Set.Ici 0) 0 := by
    have hlinear : HasDerivAt (fun u : Real => -(switchIJ * u)) (-switchIJ) 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul (-switchIJ)
    have hexp := hlinear.exp
    dsimp [coefficient]
    convert (hexp.const_mul switchIJ).hasDerivWithinAt using 1 <;> ring
  have hproductDeriv : HasDerivWithinAt
      (fun u => coefficient u * primitiveSet u)
      ((-switchIJ * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0)
      (Set.Ici 0) 0 := hcoefficientDeriv.mul hprimitiveDeriv
  have hq0Eq : q0 =ᶠ[𝓝[Set.Ici 0] 0] fun u => coefficient u * primitiveSet u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa [q0, coefficient, primitiveSet, weighted, stay1] using
      (rawStateProbabilityReal_other_zero_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI u hu)
  have hq0Deriv : HasDerivWithinAt q0
      ((-switchIJ * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0)
      (Set.Ici 0) 0 := hproductDeriv.congr_of_eventuallyEq hq0Eq (by
        simpa [q0, coefficient, primitiveSet, weighted, stay1] using
          (rawStateProbabilityReal_other_zero_eq_weighted_primitive
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI 0 le_rfl))
  have hq1zero : q1 0 = 0 := by
    simpa [q1] using (rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1)
  have hstay1zero : stay1 0 = 1 := by
    rw [hstay1_eq]
    simpa [hq1zero]
  have hprimitiveSetZero : primitiveSet 0 = 0 := by
    simp [primitiveSet]
  have hcoefficientZero : coefficient 0 = switchIJ := by
    simp [coefficient]
  have hderivValue :
      (-switchIJ * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0 =
        switchIJ := by
    rw [hprimitiveSetZero, hcoefficientZero]
    dsimp [weighted]
    rw [hstay1zero]
    norm_num
  change HasDerivWithinAt q0 switchIJ (Set.Ici 0) 0
  exact hderivValue ▸ hq0Deriv

/-- The symmetric right derivative at calendar time zero for the literal
source transition from state `1` to state `0`. -/
theorem hasDerivWithinAt_rawStateProbabilityReal_other_one_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    HasDerivWithinAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1))
      switchJI (Set.Ici 0) 0 := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let stay0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0 0
  let weighted : Real -> Real := fun u =>
    Real.exp (switchJI * u) * stay0 u
  let primitiveSet : Real -> Real := fun u => ∫ x in Set.Icc 0 u, weighted x
  let primitiveInterval : Real -> Real := fun u => ∫ x in (0 : Real)..u, weighted x
  let coefficient : Real -> Real := fun u =>
    switchJI * Real.exp (-(switchJI * u))
  have hq0Within : ContinuousWithinAt q0 (Set.Ici 0) 0 := by
    have hcont := continuousOn_rawStateProbabilityReal_other_zero_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1 zero_le_one
    exact (hcont 0 (by simp)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (by norm_num))
  have hstay0_eq : stay0 = fun u => 1 - q0 u := by
    funext u
    dsimp [stay0, q0]
    have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0 u
    norm_num at hpartition ⊢
    linarith
  have hstay0Within : ContinuousWithinAt stay0 (Set.Ici 0) 0 := by
    rw [hstay0_eq]
    exact continuousWithinAt_const.sub hq0Within
  have hweightedWithin : ContinuousWithinAt weighted (Set.Ici 0) 0 := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousWithinAt.mul
      hstay0Within
  have hweightedRight : ContinuousWithinAt weighted (Set.Ioi 0) 0 :=
    hweightedWithin.mono Set.Ioi_subset_Ici_self
  have hweightedMeas : Measurable weighted := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)).mul
        (measurable_rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI 0 0)
  have hweightedInt : IntervalIntegrable weighted volume 0 0 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le le_rfl]
    exact rawStateProbabilityReal_exp_weighted_integrableOn_Icc
      muI muJ arrivalI arrivalJ switchIJ switchJI switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0 0 0 0
  have hprimitiveIntervalDeriv : HasDerivWithinAt primitiveInterval (weighted 0)
      (Set.Ici 0) 0 := by
    exact intervalIntegral.integral_hasDerivWithinAt_right hweightedInt
      hweightedMeas.stronglyMeasurable.stronglyMeasurableAtFilter hweightedRight
  have hprimitiveEq : primitiveSet =ᶠ[𝓝[Set.Ici 0] 0] primitiveInterval := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp [primitiveSet, primitiveInterval]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu]
  have hprimitiveDeriv : HasDerivWithinAt primitiveSet (weighted 0)
      (Set.Ici 0) 0 :=
    hprimitiveIntervalDeriv.congr_of_eventuallyEq hprimitiveEq (by
      simp [primitiveSet, primitiveInterval])
  have hcoefficientDeriv : HasDerivWithinAt coefficient
      (-switchJI * coefficient 0) (Set.Ici 0) 0 := by
    have hlinear : HasDerivAt (fun u : Real => -(switchJI * u)) (-switchJI) 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul (-switchJI)
    have hexp := hlinear.exp
    dsimp [coefficient]
    convert (hexp.const_mul switchJI).hasDerivWithinAt using 1 <;> ring
  have hproductDeriv : HasDerivWithinAt
      (fun u => coefficient u * primitiveSet u)
      ((-switchJI * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0)
      (Set.Ici 0) 0 := hcoefficientDeriv.mul hprimitiveDeriv
  have hq1Eq : q1 =ᶠ[𝓝[Set.Ici 0] 0] fun u => coefficient u * primitiveSet u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa [q1, coefficient, primitiveSet, weighted, stay0] using
      (rawStateProbabilityReal_other_one_eq_weighted_primitive
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI u hu)
  have hq1Deriv : HasDerivWithinAt q1
      ((-switchJI * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0)
      (Set.Ici 0) 0 := hproductDeriv.congr_of_eventuallyEq hq1Eq (by
        simpa [q1, coefficient, primitiveSet, weighted, stay0] using
          (rawStateProbabilityReal_other_one_eq_weighted_primitive
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI 0 le_rfl))
  have hq0zero : q0 0 = 0 := by
    simpa [q0] using (rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0)
  have hstay0zero : stay0 0 = 1 := by
    rw [hstay0_eq]
    simpa [hq0zero]
  have hprimitiveSetZero : primitiveSet 0 = 0 := by
    simp [primitiveSet]
  have hcoefficientZero : coefficient 0 = switchJI := by
    simp [coefficient]
  have hderivValue :
      (-switchJI * coefficient 0) * primitiveSet 0 + coefficient 0 * weighted 0 =
        switchJI := by
    rw [hprimitiveSetZero, hcoefficientZero]
    dsimp [weighted]
    rw [hstay0zero]
    norm_num
  change HasDerivWithinAt q1 switchJI (Set.Ici 0) 0
  exact hderivValue ▸ hq1Deriv

/-- The complete right-forward equation for the literal `0 → 1` endpoint
mass, including the calendar-time boundary. -/
theorem hasDerivWithinAt_rawStateProbabilityReal_other_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : t ∈ Set.Ici (0 : Real)) :
    HasDerivWithinAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0))
      (switchIJ * (1 - rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t) -
        switchIJ * rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI 0
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t)
      (Set.Ici t) t := by
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with rfl | ht
  · have hq0zero := rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0
    have hq1zero := rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1
    have hq0zero' : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 0 1 0 = 0 := by
      simpa using hq0zero
    have hq1zero' : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1 0 0 = 0 := by
      simpa using hq1zero
    convert hasDerivWithinAt_rawStateProbabilityReal_other_zero_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI using 1 <;>
      simp [hq0zero', hq1zero']
  · exact (hasDerivAt_rawStateProbabilityReal_other_zero_of_pos
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht).hasDerivWithinAt

/-- The complete right-forward equation for the literal `1 → 0` endpoint
mass, including time zero. -/
theorem hasDerivWithinAt_rawStateProbabilityReal_other_one
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : t ∈ Set.Ici (0 : Real)) :
    HasDerivWithinAt
      (rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1))
      (switchJI * (1 - rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 0
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t) -
        switchJI * rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI 1
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t)
      (Set.Ici t) t := by
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with rfl | ht
  · have hq0zero := rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0
    have hq1zero := rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1
    have hq0zero' : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 0 1 0 = 0 := by
      simpa using hq0zero
    have hq1zero' : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1 0 0 = 0 := by
      simpa using hq1zero
    convert hasDerivWithinAt_rawStateProbabilityReal_other_one_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI using 1 <;>
      simp [hq0zero', hq1zero']
  · exact (hasDerivAt_rawStateProbabilityReal_other_one_of_pos
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht).hasDerivWithinAt

/-- The two literal directional endpoint masses have the rate-balance
identity forced by their raw forward system and their common zero initial
condition. -/
theorem rawStateProbabilityReal_rate_balance
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    switchJI * rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI 0
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
      switchIJ * rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let difference : Real -> Real := fun u => switchJI * q0 u - switchIJ * q1 u
  have hq0cont := continuousOn_rawStateProbabilityReal_other_zero_Ici
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
  have hq1cont := continuousOn_rawStateProbabilityReal_other_one_Ici
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
  have hdifferenceCont : ContinuousOn difference (Set.Ici 0) := by
    exact (continuousOn_const.mul hq0cont).sub (continuousOn_const.mul hq1cont)
  have hq0zero : q0 0 = 0 := by
    simpa [q0] using (rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0)
  have hq1zero : q1 0 = 0 := by
    simpa [q1] using (rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1)
  have hdifferenceZero : difference 0 = 0 := by
    simp [difference, hq0zero, hq1zero]
  have hdifferenceDeriv : ∀ u ∈ Set.Ici (0 : Real),
      HasDerivWithinAt difference (0 * difference u) (Set.Ici u) u := by
    intro u hu
    have hq0deriv := hasDerivWithinAt_rawStateProbabilityReal_other_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI u hu
    have hq1deriv := hasDerivWithinAt_rawStateProbabilityReal_other_one
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI u hu
    change HasDerivWithinAt (fun v => switchJI * q0 v - switchIJ * q1 v)
      (0 * (switchJI * q0 u - switchIJ * q1 u)) (Set.Ici u) u
    convert (hq0deriv.const_mul switchJI).sub (hq1deriv.const_mul switchIJ) using 1 <;>
      ring
  have hdifference := AppliedModelingLib.eq_zero_of_continuousOn_Ici_of_hasDerivWithinAt_linear
    0 difference hdifferenceZero hdifferenceCont hdifferenceDeriv (t := t) ht
  simpa [difference, q0, q1] using sub_eq_zero.mp hdifference

/-- The literal raw `0 → 1` endpoint mass is the standard closed-form
two-state CTMC switch probability.  The identification follows from the raw
forward system, rate balance, and half-line Grönwall uniqueness. -/
theorem rawStateProbabilityReal_other_zero_eq_twoStateCtmcSwitchProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t =
      AppliedModelingLib.twoStateCtmcSwitchProb switchIJ switchJI t := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  let closed : Real -> Real := AppliedModelingLib.twoStateCtmcSwitchProb
    switchIJ switchJI
  have hsum : switchIJ + switchJI ≠ 0 := by linarith
  have hq0cont := continuousOn_rawStateProbabilityReal_other_zero_Ici
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
  have hq0zero : q0 0 = 0 := by
    simpa [q0] using (rawStateProbabilityReal_otherState_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0)
  have hq0deriv : ∀ u ∈ Set.Ici (0 : Real),
      HasDerivWithinAt q0
        (switchIJ - (switchIJ + switchJI) * q0 u) (Set.Ici u) u := by
    intro u hu
    have hforward := hasDerivWithinAt_rawStateProbabilityReal_other_zero
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI u hu
    have hbalance := rawStateProbabilityReal_rate_balance
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI u hu
    have hq1eq : q1 u = switchJI / switchIJ * q0 u := by
      field_simp [hswitchIJ.ne']
      dsimp [q0, q1] at hbalance ⊢
      linarith
    change HasDerivWithinAt q0
      (switchIJ - (switchIJ + switchJI) * q0 u) (Set.Ici u) u
    convert hforward using 1
    dsimp [q0, q1] at hq1eq ⊢
    rw [hq1eq]
    field_simp [hswitchIJ.ne']
    ring
  have hclosedDeriv : ∀ u : Real, HasDerivAt closed
      (switchIJ - (switchIJ + switchJI) * closed u) u := by
    intro u
    dsimp [closed]
    convert AppliedModelingLib.twoStateCtmcSwitchProb_hasDerivAt
      switchIJ switchJI u using 1
    unfold AppliedModelingLib.twoStateCtmcSwitchProb
    field_simp [hsum]
    ring
  have hclosedCont : Continuous closed := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hclosedDeriv u).continuousAt
  let difference : Real -> Real := fun u => q0 u - closed u
  have hdifferenceCont : ContinuousOn difference (Set.Ici 0) := by
    exact hq0cont.sub hclosedCont.continuousOn
  have hdifferenceZero : difference 0 = 0 := by
    change q0 0 - closed 0 = 0
    rw [hq0zero]
    simp [closed]
  have hdifferenceDeriv : ∀ u ∈ Set.Ici (0 : Real),
      HasDerivWithinAt difference
        (-(switchIJ + switchJI) * difference u) (Set.Ici u) u := by
    intro u hu
    change HasDerivWithinAt (fun v => q0 v - closed v)
      (-(switchIJ + switchJI) * (q0 u - closed u)) (Set.Ici u) u
    convert (hq0deriv u hu).sub (hclosedDeriv u).hasDerivWithinAt using 1
    ring
  have hdifference := AppliedModelingLib.eq_zero_of_continuousOn_Ici_of_hasDerivWithinAt_linear
    (-(switchIJ + switchJI)) difference hdifferenceZero hdifferenceCont hdifferenceDeriv (t := t) ht
  exact sub_eq_zero.mp (by simpa [difference, q0, closed] using hdifference)

/-- The symmetric closed-form identification for the literal raw `1 → 0`
endpoint mass. -/
theorem rawStateProbabilityReal_other_one_eq_twoStateCtmcSwitchProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1) t =
      AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t := by
  let q0 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 0
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0)
  let q1 : Real -> Real := rawStateProbabilityReal
    muI muJ arrivalI arrivalJ switchIJ switchJI 1
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState 1)
  have hbalance := rawStateProbabilityReal_rate_balance
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI t ht
  have hq0 := rawStateProbabilityReal_other_zero_eq_twoStateCtmcSwitchProb
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI t ht
  have hkernelBalance :
      switchJI * AppliedModelingLib.twoStateCtmcSwitchProb switchIJ switchJI t =
        switchIJ * AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t := by
    unfold AppliedModelingLib.twoStateCtmcSwitchProb
    field_simp [show switchIJ + switchJI ≠ 0 by linarith]
    ring
  have hmul : switchIJ * q1 t =
      switchIJ * AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t := by
    calc
      switchIJ * q1 t = switchJI * q0 t := by
        simpa [q0, q1, mul_comm] using hbalance.symm
      _ = switchJI * AppliedModelingLib.twoStateCtmcSwitchProb switchIJ switchJI t := by
        rw [show q0 t = rawStateProbabilityReal
          muI muJ arrivalI arrivalJ switchIJ switchJI 0
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState 0) t by rfl,
          hq0]
      _ = switchIJ * AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t :=
        hkernelBalance
  have hq1 : q1 t = AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t := by
    nlinarith [hswitchIJ]
  simpa [q1] using hq1

/-- Every deterministic endpoint probability of the literal raw alternating
switch-clock path agrees with the two-state CTMC transition kernel.  This
packages the two source-derived opposite-state formulas with the exact
two-state endpoint partition; it does not posit a Markov property at a
random completion time. -/
theorem rawStateProbabilityReal_eq_twoStateCtmcTransitionProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial target : Fin 2) (t : Real) (ht : 0 ≤ t) :
    rawStateProbabilityReal muI muJ arrivalI arrivalJ switchIJ switchJI
      initial target t =
      AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t initial target := by
  fin_cases initial <;> fin_cases target
  · have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 0 t
    have hswitch : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 0 1 t =
        AppliedModelingLib.twoStateCtmcSwitchProb switchIJ switchJI t := by
      simpa using (rawStateProbabilityReal_other_zero_eq_twoStateCtmcSwitchProb
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI t ht)
    have hkernel := AppliedModelingLib.twoStateCtmcStayProb_add_switchProb
      switchIJ switchJI t
    norm_num at hpartition
    change rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI 0 0 t =
      AppliedModelingLib.twoStateCtmcStayProb switchIJ switchJI t
    linarith
  · simpa using (rawStateProbabilityReal_other_zero_eq_twoStateCtmcSwitchProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht)
  · simpa using (rawStateProbabilityReal_other_one_eq_twoStateCtmcSwitchProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI t ht)
  · have hpartition := rawStateProbabilityReal_initial_add_eq_otherState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI 1 t
    have hswitch : rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI 1 0 t =
        AppliedModelingLib.twoStateCtmcSwitchProb switchJI switchIJ t := by
      simpa using (rawStateProbabilityReal_other_one_eq_twoStateCtmcSwitchProb
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI t ht)
    have hkernel := AppliedModelingLib.twoStateCtmcStayProb_add_switchProb
      switchJI switchIJ t
    norm_num at hpartition
    change rawStateProbabilityReal
      muI muJ arrivalI arrivalJ switchIJ switchJI 1 1 t =
      AppliedModelingLib.twoStateCtmcStayProb switchJI switchIJ t
    linarith

/-- The two literal switch paths and literal selected accepted-trip mark have
their exact three-factor product law.  This is the full raw input
factorization needed before identifying the random-duration CTMC endpoint;
it is not a replacement for that path-law proof. -/
theorem rawSwitchGapPair_firstAcceptedTripMark_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (fun seed =>
      (rawSwitchGapPair seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
        (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let switchPairFromGaps : (Fin 2 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) :=
    fun gaps => (gaps 0, gaps 1)
  letI : IsProbabilityMeasure
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hswitchPairFromGaps : Measurable switchPairFromGaps := by
    exact (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hrawSwitchMark : ProbabilityTheory.IndepFun rawSwitchGaps
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    indepFun_rawSwitchGaps_gn21RawFirstAcceptedTripMark
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma
  have hpairMark : ProbabilityTheory.IndepFun rawSwitchGapPair
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    have h := hrawSwitchMark.comp hswitchPairFromGaps measurable_id
    simpa [rawSwitchGapPair, switchPairFromGaps] using h
  exact AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
    (rawSwitchGapPair_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI)
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
    hpairMark

/-- The two literal switch streams factor from the source arrival stream and
trip-mark stream selected for one state.  This is a direct finite-coordinate
product calculation on the raw four-clock/two-mark seed, retaining complete
streams rather than replacing them by a post-thinning input. -/
theorem rawSwitchGapPair_rawTripMarkStream_rawClockStream_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2)
    (hclockTwo : clock ≠ 2) (hclockThree : clock ≠ 3) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      (rawSwitchGapPair seed,
        (AcceptedArrivalTime.rawTripMarkStream state seed,
          AcceptedArrivalTime.rawClockStream clock seed)))
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          switchJI)).prod
        ((AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockLaw : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let arrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate clock)
  let selectedMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let switchPair : (Fin 4 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) :=
    fun clocks => (clocks 2, clocks 3)
  let arrivalStream : (Fin 4 -> Nat -> Real) -> Nat -> Real :=
    fun clocks => clocks clock
  let markStream : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength :=
    fun marks => marks state
  let pairedClocks : (Fin 4 -> Nat -> Real) ->
      ((Nat -> Real) × (Nat -> Real)) × (Nat -> Real) := fun clocks =>
    (switchPair clocks, arrivalStream clocks)
  let reorder : (((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) ×
      (Nat -> TripLength) ->
      ((Nat -> Real) × (Nat -> Real)) × ((Nat -> TripLength) × (Nat -> Real)) :=
    fun z => (z.1.1, (z.2, z.1.2))
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate c)
  letI : IsProbabilityMeasure clockLaw := by
    dsimp [clockLaw]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s) := fun s =>
    inferInstance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure arrivalLaw := by
    dsimp [arrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate clock)
  letI : IsProbabilityMeasure selectedMarkLaw := by
    dsimp [selectedMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hcoordinateMeas : ∀ c : Fin 4,
      Measurable (fun clocks : Fin 4 -> Nat -> Real => clocks c) := by
    intro c
    exact measurable_pi_apply c
  have hcoordinateIndep : ProbabilityTheory.iIndepFun
      (fun c (clocks : Fin 4 -> Nat -> Real) => clocks c) clockLaw := by
    simpa [clockLaw] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) (fun _ => measurable_id))
  have htwo_ne : (2 : Fin 4) ≠ clock := by
    exact Ne.symm hclockTwo
  have hthree_ne : (3 : Fin 4) ≠ clock := by
    exact Ne.symm hclockThree
  have hswitchPairMeas : Measurable switchPair := by
    exact (measurable_pi_apply 2).prodMk (measurable_pi_apply 3)
  have harrivalStreamMeas : Measurable arrivalStream := by
    exact measurable_pi_apply clock
  have hmarkStreamMeas : Measurable markStream := by
    exact measurable_pi_apply state
  have hswitchPairArrivalIndep : ProbabilityTheory.IndepFun switchPair arrivalStream
      clockLaw := by
    simpa [switchPair, arrivalStream] using
      (hcoordinateIndep.indepFun_prodMk hcoordinateMeas 2 3 clock htwo_ne hthree_ne)
  have hclockTwoLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks 2)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ)
      clockLaw := by
    simpa [clockLaw, clockRate, gn21CycleClockRate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) 2).hasLaw
  have hclockThreeLaw : HasLaw (fun clocks : Fin 4 -> Nat -> Real => clocks 3)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
      clockLaw := by
    simpa [clockLaw, clockRate, gn21CycleClockRate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) 3).hasLaw
  have htwoThreeIndep : ProbabilityTheory.IndepFun
      (fun clocks : Fin 4 -> Nat -> Real => clocks 2)
      (fun clocks : Fin 4 -> Nat -> Real => clocks 3) clockLaw := by
    exact hcoordinateIndep.indepFun (by decide)
  have hswitchPairLaw : HasLaw switchPair switchLaw clockLaw := by
    simpa [switchPair, switchLaw] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
        hclockTwoLaw hclockThreeLaw htwoThreeIndep)
  have harrivalLaw : HasLaw arrivalStream arrivalLaw clockLaw := by
    simpa [arrivalStream, arrivalLaw, clockLaw] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) clock).hasLaw
  have hpairedClockLaw : HasLaw pairedClocks (switchLaw.prod arrivalLaw) clockLaw := by
    simpa [pairedClocks] using
      (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
        hswitchPairLaw harrivalLaw hswitchPairArrivalIndep)
  have hmarkLaw : HasLaw markStream selectedMarkLaw markLaw := by
    simpa [markStream, selectedMarkLaw, markLaw,
      AppliedModelingLib.Probability.IIDStream.measure] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ s)
        state).hasLaw
  have hpairedClocksMeas : Measurable pairedClocks :=
    hswitchPairMeas.prodMk harrivalStreamMeas
  have hreorderMeas : Measurable reorder := by
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hreorderMap : Measure.map reorder ((switchLaw.prod arrivalLaw).prod selectedMarkLaw) =
      switchLaw.prod (selectedMarkLaw.prod arrivalLaw) := by
    change Measure.map ((Prod.map id Prod.swap) ∘ MeasurableEquiv.prodAssoc)
      ((switchLaw.prod arrivalLaw).prod selectedMarkLaw) = _
    rw [← Measure.map_map (measurable_id.prodMap measurable_swap)
      MeasurableEquiv.prodAssoc.measurable,
      (measurePreserving_prodAssoc switchLaw arrivalLaw selectedMarkLaw).map_eq,
      ← Measure.map_prod_map switchLaw (arrivalLaw.prod selectedMarkLaw)
        measurable_id measurable_swap,
      Measure.map_id, Measure.prod_swap]
  have hmap : Measure.map (fun seed : GN21RawCycleSeed =>
      (rawSwitchGapPair seed,
        (AcceptedArrivalTime.rawTripMarkStream state seed,
          AcceptedArrivalTime.rawClockStream clock seed))) P =
      switchLaw.prod (selectedMarkLaw.prod arrivalLaw) := by
    calc
      Measure.map (fun seed : GN21RawCycleSeed =>
          (rawSwitchGapPair seed,
            (AcceptedArrivalTime.rawTripMarkStream state seed,
              AcceptedArrivalTime.rawClockStream clock seed))) P =
          Measure.map reorder
            (Measure.map (Prod.map pairedClocks markStream) (clockLaw.prod markLaw)) := by
              change Measure.map (fun seed : GN21RawCycleSeed =>
                (rawSwitchGapPair seed,
                  (AcceptedArrivalTime.rawTripMarkStream state seed,
                    AcceptedArrivalTime.rawClockStream clock seed)))
                  (clockLaw.prod markLaw) = _
              rw [Measure.map_map hreorderMeas
                (hpairedClocksMeas.prodMap hmarkStreamMeas)]
              rfl
      _ = Measure.map reorder ((Measure.map pairedClocks clockLaw).prod
          (Measure.map markStream markLaw)) := by
            rw [← Measure.map_prod_map clockLaw markLaw hpairedClocksMeas hmarkStreamMeas]
      _ = Measure.map reorder ((switchLaw.prod arrivalLaw).prod selectedMarkLaw) := by
            rw [hpairedClockLaw.map_eq, hmarkLaw.map_eq]
      _ = switchLaw.prod (selectedMarkLaw.prod arrivalLaw) := hreorderMap
  refine ⟨?_, ?_⟩
  · exact ((measurable_rawSwitchGapPair.prodMk
      ((AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
        (AcceptedArrivalTime.measurable_rawClockStream clock)))).aemeasurable
  · simpa [P, switchLaw, selectedMarkLaw, arrivalLaw, clockRate,
      gn21CycleClockRate] using hmap

/-- The two literal switch streams factor from the complete stopped
arrival/mark history through the first accepted request.  The history retains
the selected continuous mark, its untouched mark tail, the accumulated
arrival time, and the post-request arrival-gap tail. -/
theorem rawSwitchGapPair_firstAcceptedArrivalHistory_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hclockTwo : clock ≠ 2) (hclockThree : clock ≠ 3) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      (rawSwitchGapPair seed,
        AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed))
      (let inputLaw : Measure ((Nat -> TripLength) × (Nat -> Real)) :=
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
       let historyInput := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
       let switchLaw :=
         (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
           (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
       switchLaw.prod (Measure.map historyInput inputLaw))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let input : GN21RawCycleSeed -> (Nat -> TripLength) × (Nat -> Real) := fun seed =>
    (AcceptedArrivalTime.rawTripMarkStream state seed,
      AcceptedArrivalTime.rawClockStream clock seed)
  let inputLaw : Measure ((Nat -> TripLength) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
  let historyInput := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
  let historyRaw := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma
  let historyPrefix : (Nat -> TripLength) × (Nat -> Real) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun z =>
    (((AcceptedTripSelection.firstAcceptedIndex sigma z.1,
      AcceptedTripSelection.firstAcceptedTripMark sigma z.1),
      AcceptedTripSelection.firstAcceptedTripTail sigma z.1),
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2)
  let historyLaw : Measure ((((Nat × TripLength) × (Nat -> TripLength)) × Real) ×
      (Nat -> Real)) :=
    (Measure.map historyPrefix
      ((AppliedModelingLib.Probability.IIDStream.measure
        (gn21CycleMarkLaw muI muJ state)).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))))).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let transform : ((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> TripLength) × (Nat -> Real)) ->
      ((Nat -> Real) × (Nat -> Real)) ×
        ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) :=
    fun z => (z.1, historyInput z.2)
  have hclockRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hclockRate
  letI : IsProbabilityMeasure inputLaw := by
    dsimp [inputLaw]
    infer_instance
  have hinputMeas : Measurable input := by
    exact (AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
      (AcceptedArrivalTime.measurable_rawClockStream clock)
  have hhistoryInputMeas : Measurable historyInput := by
    simpa [historyInput] using
      AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  have hinput : HasLaw input inputLaw P := by
    simpa [P, input, inputLaw, AcceptedArrivalTime.rawTripMarkStream,
      AcceptedArrivalTime.rawClockStream,
      AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (AcceptedArrivalTime.rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state)
  have hhistoryRaw : HasLaw historyRaw historyLaw P := by
    simpa [P, historyRaw, historyPrefix, historyLaw,
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory,
      AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail,
      AcceptedArrivalTime.rawTripMarkStream, AcceptedArrivalTime.rawClockStream,
      AcceptedTripSelection.gn21RawFirstAcceptedIndex,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
      AcceptedTripSelection.gn21RawFirstAcceptedTripTail,
      gn21RawCycleMark, AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure,
      AppliedModelingLib.Probability.IIDStream.externalIndexTail,
      AppliedModelingLib.Probability.IIDStream.coordinate, Function.comp_def] using
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory_postArrivalGapTail_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass)
  have hhistoryInputMap : Measure.map historyInput inputLaw = historyLaw := by
    calc
      Measure.map historyInput inputLaw = Measure.map historyInput (Measure.map input P) := by
        rw [hinput.map_eq]
      _ = Measure.map (historyInput ∘ input) P := by
        rw [Measure.map_map hhistoryInputMeas hinputMeas]
      _ = Measure.map historyRaw P := by rfl
      _ = historyLaw := hhistoryRaw.map_eq
  have htransformMeas : Measurable transform := by
    exact measurable_fst.prodMk (hhistoryInputMeas.comp measurable_snd)
  have htransformLaw : HasLaw transform (switchLaw.prod historyLaw)
      (switchLaw.prod inputLaw) := by
    refine ⟨htransformMeas.aemeasurable, ?_⟩
    calc
      Measure.map transform (switchLaw.prod inputLaw) =
          (Measure.map id switchLaw).prod (Measure.map historyInput inputLaw) := by
            exact (Measure.map_prod_map switchLaw inputLaw measurable_id hhistoryInputMeas).symm
      _ = switchLaw.prod historyLaw := by
            rw [Measure.map_id, hhistoryInputMap]
  have hpairInput : HasLaw (fun seed : GN21RawCycleSeed =>
      (rawSwitchGapPair seed, input seed)) (switchLaw.prod inputLaw) P := by
    simpa [P, input, inputLaw, switchLaw,
      AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (rawSwitchGapPair_rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state hclockTwo hclockThree)
  have hcomposed := htransformLaw.fun_comp hpairInput
  change HasLaw (fun seed : GN21RawCycleSeed =>
    (rawSwitchGapPair seed,
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed))
    (switchLaw.prod (Measure.map historyInput inputLaw)) P
  rw [hhistoryInputMap]
  refine hcomposed.congr ?_
  filter_upwards [] with seed
  rfl

/-- Under a product law for raw switch gaps and an independent completion
time, the endpoint probability is the integral of its fixed-time endpoint
probabilities.  This is a Fubini identity for the literal alternating path,
not an asserted Markov property at the random time. -/
theorem measure_stateAtPairAtTime_prod_eq_lintegral
    {β : Type*} [MeasurableSpace β]
    (mu : Measure ((Nat -> Real) × (Nat -> Real))) (nu : Measure β)
    [SFinite mu] [SFinite nu]
    (time : β -> Real) (htime : Measurable time) (initial target : Fin 2) :
    (mu.prod nu) {z |
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (z.1, time z.2) = target} =
      ∫⁻ t, mu {pair |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (pair, time t) = target} ∂nu := by
  let f : ((Nat -> Real) × (Nat -> Real)) × β -> ENNReal := fun z =>
    if AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target
    then 1 else 0
  have hf : Measurable f := by
    exact Measurable.ite
      (((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
        (measurable_fst.prodMk (htime.comp measurable_snd))) (measurableSet_singleton _))
      measurable_const measurable_const
  calc
    (mu.prod nu) {z |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (z.1, time z.2) = target} =
        ∫⁻ z, f z ∂(mu.prod nu) := by
          symm
          let E : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
            {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
              (z.1, time z.2) = target}
          have hE : MeasurableSet E :=
            ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
              initial).comp (measurable_fst.prodMk (htime.comp measurable_snd)))
              (measurableSet_singleton _)
          calc
            ∫⁻ z, f z ∂(mu.prod nu) =
                ∫⁻ z, E.indicator (fun _ => 1) z ∂(mu.prod nu) := by
              apply lintegral_congr
              intro z
              by_cases hz : z ∈ E
              · have hz' :
                    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
                      (z.1, time z.2) = target := by
                    simpa [E] using hz
                simp [f, hz', Set.indicator_of_mem hz]
              · have hz' : ¬AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime
                    initial (z.1, time z.2) = target := by
                    simpa [E] using hz
                simp [f, hz', Set.indicator_of_notMem hz]
            _ = ∫⁻ z in E, 1 ∂(mu.prod nu) := by
              rw [MeasureTheory.lintegral_indicator hE]
            _ = (mu.prod nu) E := by simp
            _ = _ := rfl
    _ = ∫⁻ t, ∫⁻ pair, f (pair, t) ∂mu ∂nu := by
      exact MeasureTheory.lintegral_prod_symm' f hf
    _ = ∫⁻ t, mu {pair |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (pair, time t) = target} ∂nu := by
      apply lintegral_congr
      intro t
      let E : Set ((Nat -> Real) × (Nat -> Real)) :=
        {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (pair, time t) = target}
      have hE : MeasurableSet E :=
        ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
          (measurable_id.prodMk measurable_const)) (measurableSet_singleton _)
      calc
        ∫⁻ pair, f (pair, t) ∂mu =
            ∫⁻ pair, E.indicator (fun _ => 1) pair ∂mu := by
          apply lintegral_congr
          intro pair
          by_cases hpair : pair ∈ E
          · have hpair' :
                AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
                  (pair, time t) = target := by
                simpa [E] using hpair
            simp [f, hpair', Set.indicator_of_mem hpair]
          · have hpair' : ¬AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime
                initial (pair, time t) = target := by
                simpa [E] using hpair
            simp [f, hpair', Set.indicator_of_notMem hpair]
        _ = ∫⁻ pair in E, 1 ∂mu := by
          rw [MeasureTheory.lintegral_indicator hE]
        _ = mu E := by simp
        _ = _ := rfl

/-- The literal state-indexed residual switch streams when an ordered raw
switch-pair is observed at an external calendar time. -/
noncomputable def switchGapsAfterPairAtTime (initial : Fin 2) :
    ((Nat -> Real) × (Nat -> Real)) × Real -> Fin 2 -> Nat -> Real :=
  fun pairAndTime =>
    AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
      initial
      (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
        pairAndTime.1)
      pairAndTime.2

/-- Measurability of the product-space literal residual switch streams. -/
theorem measurable_switchGapsAfterPairAtTime (initial : Fin 2) :
    Measurable (switchGapsAfterPairAtTime initial) := by
  exact
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_switchGapsAfterElapsed
      initial).comp
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.comp
        measurable_fst).prodMk measurable_snd)

/-- Integrating either deterministic alternating restart law against an
independent nonnegative external time preserves the exact endpoint/future
factorization.  This is a product-space Fubini argument, not a strong-Markov
assertion. -/
theorem measure_stateAtPairAtTime_switchGapsAfter_prod_factor
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [SFinite nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ᵐ t ∂nu, 0 ≤ time t) (initial target : Fin 2)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
      {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (z.1, time z.2) = target}
    let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2)
    (mu.prod nu) (Set.inter stateEvent (future ⁻¹' B)) =
      (mu.prod nu) stateEvent *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target}
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let D : Set ((Nat -> Real) × (Nat -> Real)) :=
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B
  let jointEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
    Set.inter stateEvent (future ⁻¹' B)
  let fiber : β -> Set ((Nat -> Real) × (Nat -> Real)) := fun t =>
    Set.inter
      {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (pair, time t) = target}
      {pair | future (pair, t) ∈ B}
  let pathLaw : Measure (Fin 2 -> Nat -> Real) :=
    Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu
  let stateMass : Real -> ENNReal :=
    AppliedModelingLib.Probability.TwoStateSwitching.stateProbability pathLaw initial target
  let f : ((Nat -> Real) × (Nat -> Real)) × β -> ENNReal := fun z =>
    if z ∈ jointEvent then 1 else 0
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : IsProbabilityMeasure pathLaw := by
    dsimp [pathLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  have hstateEvent : MeasurableSet stateEvent :=
    ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))) (measurableSet_singleton target)
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hjointEvent : MeasurableSet jointEvent :=
    hstateEvent.inter (hfuture hB)
  have hf : Measurable f := by
    exact Measurable.ite hjointEvent measurable_const measurable_const
  have hfiberMeas : ∀ t : β, MeasurableSet (fiber t) := by
    intro t
    exact
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
        initial).comp (measurable_id.prodMk measurable_const))
        (measurableSet_singleton target) |>.inter
      ((hfuture.comp (measurable_id.prodMk measurable_const)) hB)
  have hinner : ∀ t : β, ∫⁻ pair, f (pair, t) ∂mu = mu (fiber t) := by
    intro t
    calc
      ∫⁻ pair, f (pair, t) ∂mu =
          ∫⁻ pair, (fiber t).indicator (fun _ => 1) pair ∂mu := by
            apply lintegral_congr
            intro pair
            by_cases hpair : pair ∈ fiber t
            · have hjoint : (pair, t) ∈ jointEvent := by
                simpa [jointEvent, fiber] using hpair
              simp [f, hjoint, Set.indicator_of_mem hpair]
            · have hjoint : (pair, t) ∉ jointEvent := by
                simpa [jointEvent, fiber] using hpair
              simp [f, hjoint, Set.indicator_of_notMem hpair]
      _ = ∫⁻ _ in fiber t, 1 ∂mu := by
        rw [MeasureTheory.lintegral_indicator (hfiberMeas t)]
      _ = mu (fiber t) := by simp
  have hstateSection : ∀ t : β,
      mu {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (pair, time t) = target} = stateMass (time t) := by
    intro t
    change mu {pair |
      AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair pair) (time t) = target} =
      pathLaw {gaps |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAt initial gaps (time t) = target}
    exact (Measure.map_apply
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAt_fixedTime initial (time t))
        (measurableSet_singleton target))).symm
  have hstateMassMeas : Measurable stateMass := by
    simpa [stateMass] using
      (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateProbability
        pathLaw initial target)
  have hdet : ∀ᵐ t ∂nu, mu (fiber t) = stateMass (time t) * mu D := by
    filter_upwards [hnonneg] with t ht
    calc
      mu (fiber t) =
          mu (Set.inter
            {pair | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
              (pair, time t) = target}
            ((fun pair => future (pair, t)) ⁻¹' B)) := by rfl
      _ = mu {pair |
          AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
            (pair, time t) = target} * mu D := by
          fin_cases initial
          · simpa [mu, future, D, switchGapsAfterPairAtTime,
              AppliedModelingLib.Probability.PoissonProcess.alternatingZeroStartFuture] using
              (AppliedModelingLib.Probability.PoissonProcess.measure_alternatingZeroStart_state_future_factor
                hswitchIJ hswitchJI (time t) ht target B hB)
          · simpa [mu, future, D, switchGapsAfterPairAtTime,
              AppliedModelingLib.Probability.PoissonProcess.alternatingOneStartFuture] using
              (AppliedModelingLib.Probability.PoissonProcess.measure_alternatingOneStart_state_future_factor
                hswitchIJ hswitchJI (time t) ht target B hB)
      _ = stateMass (time t) * mu D := by rw [hstateSection]
  have hendpoint : (mu.prod nu) stateEvent = ∫⁻ t, stateMass (time t) ∂nu := by
    calc
      (mu.prod nu) stateEvent = ∫⁻ t, mu {pair |
          AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
            (pair, time t) = target} ∂nu := by
          exact measure_stateAtPairAtTime_prod_eq_lintegral mu nu time htime initial target
      _ = ∫⁻ t, stateMass (time t) ∂nu := by
          apply lintegral_congr
          intro t
          exact hstateSection t
  calc
    (mu.prod nu) (Set.inter stateEvent (future ⁻¹' B)) =
        (mu.prod nu) jointEvent := by rfl
    _ = ∫⁻ z, f z ∂(mu.prod nu) := by
      symm
      calc
        ∫⁻ z, f z ∂(mu.prod nu) =
            ∫⁻ z, jointEvent.indicator (fun _ => 1) z ∂(mu.prod nu) := by
              apply lintegral_congr
              intro z
              by_cases hz : z ∈ jointEvent <;>
                simp [f, hz, Set.indicator_of_mem, Set.indicator_of_notMem]
        _ = ∫⁻ z in jointEvent, 1 ∂(mu.prod nu) := by
          rw [MeasureTheory.lintegral_indicator hjointEvent]
        _ = (mu.prod nu) jointEvent := by simp
    _ = ∫⁻ t, ∫⁻ pair, f (pair, t) ∂mu ∂nu := by
      exact MeasureTheory.lintegral_prod_symm' f hf
    _ = ∫⁻ t, mu (fiber t) ∂nu := by
      apply lintegral_congr
      intro t
      exact hinner t
    _ = ∫⁻ t, stateMass (time t) * mu D ∂nu := by
      exact lintegral_congr_ae hdet
    _ = (∫⁻ t, stateMass (time t) ∂nu) * mu D := by
      exact MeasureTheory.lintegral_mul_const (mu D) (hstateMassMeas.comp htime)
    _ = (mu.prod nu) stateEvent * mu D := by rw [← hendpoint]

/-- The alternating endpoint/residual factorization remains valid jointly with
any measurable external-history event.  The proof applies the general
product-space factorization to the restricted history law; it is not a
conditional or strong-Markov assertion. -/
theorem measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [SFinite nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ᵐ t ∂nu, 0 ≤ time t) (initial target : Fin 2)
    (A : Set β) (hA : MeasurableSet A)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
      {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (z.1, time z.2) = target}
    let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2)
    let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) := Set.univ ×ˢ A
    (mu.prod nu) (Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)) =
      (mu.prod nu) (Set.inter stateEvent historyEvent) *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target}
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) := Set.univ ×ˢ A
  let jointEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
    Set.inter stateEvent (future ⁻¹' B)
  let historyLaw := nu.restrict A
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : SFinite historyLaw := by
    dsimp [historyLaw]
    infer_instance
  have hstateEvent : MeasurableSet stateEvent :=
    ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))) (measurableSet_singleton target)
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hjointEvent : MeasurableSet jointEvent := hstateEvent.inter (hfuture hB)
  have hhistoryEvent : MeasurableSet historyEvent := by
    simpa [historyEvent] using (MeasurableSet.univ.prod hA)
  have hproductRestrict : mu.prod historyLaw =
      (mu.prod nu).restrict historyEvent := by
    simpa [historyLaw, historyEvent] using
      (MeasureTheory.Measure.prod_restrict (μ := mu) (ν := nu) Set.univ A)
  have hnonnegRestrict : ∀ᵐ t ∂historyLaw, 0 ≤ time t := by
    exact MeasureTheory.ae_restrict_of_ae hnonneg
  have hfactor := measure_stateAtPairAtTime_switchGapsAfter_prod_factor
    switchIJ switchJI hswitchIJ hswitchJI historyLaw time htime hnonnegRestrict
    initial target B hB
  have hrawJoint : (mu.prod nu)
      (Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)) =
      (mu.prod historyLaw) jointEvent := by
    calc
      (mu.prod nu) (Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)) =
          (mu.prod nu) (Set.inter jointEvent historyEvent) := by
            congr 1
            ext z
            change
              ((z ∈ stateEvent ∧ z ∈ historyEvent) ∧ z ∈ future ⁻¹' B) ↔
                ((z ∈ stateEvent ∧ z ∈ future ⁻¹' B) ∧ z ∈ historyEvent)
            tauto
      _ = ((mu.prod nu).restrict historyEvent) jointEvent := by
            rw [MeasureTheory.Measure.restrict_apply hjointEvent]
            rfl
      _ = (mu.prod historyLaw) jointEvent := by rw [← hproductRestrict]
  have hrawEndpoint : (mu.prod nu) (Set.inter stateEvent historyEvent) =
      (mu.prod historyLaw) stateEvent := by
    calc
      (mu.prod nu) (Set.inter stateEvent historyEvent) =
          ((mu.prod nu).restrict historyEvent) stateEvent := by
            rw [MeasureTheory.Measure.restrict_apply hstateEvent]
            rfl
      _ = (mu.prod historyLaw) stateEvent := by rw [← hproductRestrict]
  calc
    (mu.prod nu) (Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)) =
        (mu.prod historyLaw) jointEvent := hrawJoint
    _ = (mu.prod historyLaw) stateEvent *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [jointEvent, stateEvent, future, mu, historyLaw] using hfactor
    _ = (mu.prod nu) (Set.inter stateEvent historyEvent) *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [← hrawEndpoint]

/-- The post-time alternating switch residual is independent of the complete
pair consisting of its literal endpoint state and any probabilistic external
history.  This is derived by splitting a measurable endpoint--history event
over the two finite endpoint states and applying the event-level source
factorization above; it is not a strong-Markov premise. -/
theorem indepFun_stateAtPairAtTime_history_switchGapsAfter
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [IsProbabilityMeasure nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ᵐ t ∂nu, 0 ≤ time t) (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    (fun z : ((Nat -> Real) × (Nat -> Real)) × β =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (z.1, time z.2), z.2)) ⟂ᵢ[mu.prod nu]
      (fun z => switchGapsAfterPairAtTime initial (z.1, time z.2)) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2)
  let joint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 × β := fun z =>
    (endpoint z, z.2)
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hjoint : Measurable joint := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))).prodMk measurable_snd
  refine ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro C B hC hB
  let C0 : Set β := (fun b : β => (0, b)) ⁻¹' C
  let C1 : Set β := (fun b : β => (1, b)) ⁻¹' C
  have hC0 : MeasurableSet C0 := hC.preimage (measurable_const.prodMk measurable_id)
  have hC1 : MeasurableSet C1 := hC.preimage (measurable_const.prodMk measurable_id)
  let stateEvent : Fin 2 -> Set (((Nat -> Real) × (Nat -> Real)) × β) := fun target =>
    {z | endpoint z = target}
  let historyEvent : Fin 2 -> Set (((Nat -> Real) × (Nat -> Real)) × β) := fun target =>
    Set.univ ×ˢ if target = 0 then C0 else C1
  let piece : Fin 2 -> Set (((Nat -> Real) × (Nat -> Real)) × β) := fun target =>
    stateEvent target ∩ historyEvent target
  have hstateEvent (target : Fin 2) : MeasurableSet (stateEvent target) := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))) (measurableSet_singleton target)
  have hhistoryEvent (target : Fin 2) : MeasurableSet (historyEvent target) := by
    fin_cases target
    · simpa [historyEvent] using MeasurableSet.univ.prod hC0
    · simpa [historyEvent] using MeasurableSet.univ.prod hC1
  have hpiece (target : Fin 2) : MeasurableSet (piece target) :=
    (hstateEvent target).inter (hhistoryEvent target)
  have hdecomp : joint ⁻¹' C = piece 0 ∪ piece 1 := by
    ext z
    rcases z with ⟨w, b⟩
    generalize he : AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (w, time b) = e
    fin_cases e <;> simp [joint, endpoint, piece, stateEvent, historyEvent, C0, C1, he]
  have hdisjoint : Disjoint (piece 0) (piece 1) := by
    apply Set.disjoint_left.2
    intro z hz0 hz1
    have h0 : endpoint z = 0 := hz0.1
    have h1 : endpoint z = 1 := hz1.1
    simp [h0] at h1
  have hfactor (target : Fin 2) :
      (mu.prod nu) (piece target ∩ future ⁻¹' B) =
        (mu.prod nu) (piece target) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
    have h := measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
      switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial target
      (if target = 0 then C0 else C1) (by
        fin_cases target <;> simp [hC0, hC1]) B hB
    simpa [mu, endpoint, future, stateEvent, historyEvent, piece] using h
  have hfutureMeasure : (mu.prod nu) (future ⁻¹' B) =
      mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
    have hfactorUniv (target : Fin 2) :
        (mu.prod nu) (stateEvent target ∩ future ⁻¹' B) =
          (mu.prod nu) (stateEvent target) *
            mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
      have h := measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
        switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial target
        Set.univ MeasurableSet.univ B hB
      dsimp only at h
      have huniv : (Set.univ ×ˢ (Set.univ : Set β)) =
          (Set.univ : Set (((Nat -> Real) × (Nat -> Real)) × β)) := by
        ext z
        simp
      have hinter : stateEvent target ∩
          (Set.univ : Set (((Nat -> Real) × (Nat -> Real)) × β)) = stateEvent target := by
        ext z
        constructor
        · intro hz
          exact hz.1
        · intro hz
          exact ⟨hz, Set.mem_univ z⟩
      rw [huniv] at h
      change (mu.prod nu) ((stateEvent target ∩ Set.univ) ∩ future ⁻¹' B) =
        (mu.prod nu) (stateEvent target ∩ Set.univ) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) at h
      rw [hinter] at h
      exact h
    have hstateCover : stateEvent 0 ∪ stateEvent 1 = Set.univ := by
      ext z
      generalize he : endpoint z = e
      fin_cases e <;> simp [stateEvent, he]
    have hstateDisjoint : Disjoint (stateEvent 0) (stateEvent 1) := by
      apply Set.disjoint_left.2
      intro z hz0 hz1
      have h0 : endpoint z = 0 := hz0
      have h1 : endpoint z = 1 := hz1
      simp [h0] at h1
    have hcoverFuture : future ⁻¹' B =
        (stateEvent 0 ∩ future ⁻¹' B) ∪ (stateEvent 1 ∩ future ⁻¹' B) := by
      ext z
      constructor
      · intro hz
        have hstate : z ∈ stateEvent 0 ∪ stateEvent 1 := by
          rw [hstateCover]
          exact Set.mem_univ z
        rcases hstate with hstate | hstate
        · exact Or.inl ⟨hstate, hz⟩
        · exact Or.inr ⟨hstate, hz⟩
      · intro hz
        rcases hz with hz | hz
        · exact hz.2
        · exact hz.2
    have hsum : (mu.prod nu) (stateEvent 0) + (mu.prod nu) (stateEvent 1) = 1 := by
      rw [← measure_union hstateDisjoint (hstateEvent 1), hstateCover, measure_univ]
    calc
      (mu.prod nu) (future ⁻¹' B) =
          (mu.prod nu) ((stateEvent 0 ∩ future ⁻¹' B) ∪
            (stateEvent 1 ∩ future ⁻¹' B)) := congrArg (mu.prod nu) hcoverFuture
      _ = (mu.prod nu) (stateEvent 0 ∩ future ⁻¹' B) +
          (mu.prod nu) (stateEvent 1 ∩ future ⁻¹' B) := by
            rw [measure_union (hstateDisjoint.mono Set.inter_subset_left Set.inter_subset_left)
              ((hstateEvent 1).inter (hfuture hB))]
      _ = ((mu.prod nu) (stateEvent 0) + (mu.prod nu) (stateEvent 1)) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
            rw [hfactorUniv 0, hfactorUniv 1, add_mul]
      _ = _ := by rw [hsum, one_mul]
  have hdecompFuture : (joint ⁻¹' C) ∩ future ⁻¹' B =
      (piece 0 ∩ future ⁻¹' B) ∪ (piece 1 ∩ future ⁻¹' B) := by
    rw [hdecomp]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have hdisjointFuture : Disjoint (piece 0 ∩ future ⁻¹' B) (piece 1 ∩ future ⁻¹' B) :=
    hdisjoint.mono Set.inter_subset_left Set.inter_subset_left
  have hjointMeasure : (mu.prod nu) (joint ⁻¹' C) =
      (mu.prod nu) (piece 0) + (mu.prod nu) (piece 1) := by
    rw [hdecomp]
    exact measure_union hdisjoint (hpiece 1)
  have hunionFuture : (mu.prod nu)
      ((piece 0 ∩ future ⁻¹' B) ∪ (piece 1 ∩ future ⁻¹' B)) =
      (mu.prod nu) (piece 0 ∩ future ⁻¹' B) +
        (mu.prod nu) (piece 1 ∩ future ⁻¹' B) := by
    exact measure_union hdisjointFuture ((hpiece 1).inter (hfuture hB))
  change (mu.prod nu) (joint ⁻¹' C ∩ future ⁻¹' B) =
    (mu.prod nu) (joint ⁻¹' C) * (mu.prod nu) (future ⁻¹' B)
  rw [hdecompFuture, hunionFuture, hfactor 0, hfactor 1,
    hjointMeasure, hfutureMeasure, add_mul]

/-- The literal endpoint together with the complete external history has a
product law with the post-time alternating switch residual.  This packages
the event-level tail factorization as a transportable source law, while
retaining (rather than discarding) every external coordinate that may encode
an elapsed reward or holding time. -/
theorem stateAtPairAtTime_history_switchGapsAfter_joint_hasLaw
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [IsProbabilityMeasure nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ b, 0 ≤ time b) (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (z.1, time z.2)
    let joint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 × β := fun z =>
      (endpoint z, z.2)
    let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2)
    HasLaw (fun z : ((Nat -> Real) × (Nat -> Real)) × β =>
      (joint z, future z))
      ((Measure.map joint (mu.prod nu)).prod
        (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu))
      (mu.prod nu) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2)
  let joint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 × β := fun z =>
    (endpoint z, z.2)
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let switchLaw : Measure (Fin 2 -> Nat -> Real) := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu
  let source := mu.prod nu
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hjoint : Measurable joint := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))).prodMk measurable_snd
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hindep : joint ⟂ᵢ[source] future := by
    simpa [joint, future, source, mu, endpoint] using
      (indepFun_stateAtPairAtTime_history_switchGapsAfter
        switchIJ switchJI hswitchIJ hswitchJI nu time htime
        (ae_of_all _ hnonneg) initial)
  have hfutureLaw : Measure.map future source = switchLaw := by
    apply Measure.ext
    intro B hB
    let stateEvent : Fin 2 -> Set (((Nat -> Real) × (Nat -> Real)) × β) := fun target =>
      {z | endpoint z = target}
    have hstateEvent (target : Fin 2) : MeasurableSet (stateEvent target) := by
      exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
        (measurable_fst.prodMk (htime.comp measurable_snd))) (measurableSet_singleton target)
    have hfactor (target : Fin 2) :
        source (stateEvent target ∩ future ⁻¹' B) =
          source (stateEvent target) *
            mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
      have h := measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
        switchIJ switchJI hswitchIJ hswitchJI nu time htime (ae_of_all _ hnonneg) initial target
        Set.univ MeasurableSet.univ B hB
      dsimp only at h
      have huniv : (Set.univ ×ˢ (Set.univ : Set β)) =
          (Set.univ : Set (((Nat -> Real) × (Nat -> Real)) × β)) := by
        ext z
        simp
      rw [huniv] at h
      change source ((stateEvent target ∩ Set.univ) ∩ future ⁻¹' B) =
        source (stateEvent target ∩ Set.univ) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) at h
      rw [Set.inter_univ] at h
      simpa [source, stateEvent, future, endpoint] using h
    have hcover : stateEvent 0 ∪ stateEvent 1 = Set.univ := by
      ext z
      generalize he : endpoint z = e
      fin_cases e <;> simp [stateEvent, he]
    have hdisjoint : Disjoint (stateEvent 0) (stateEvent 1) := by
      apply Set.disjoint_left.2
      intro z hz0 hz1
      have h0 : endpoint z = 0 := hz0
      have h1 : endpoint z = 1 := hz1
      simp [h0] at h1
    have hcoverFuture : future ⁻¹' B =
        (stateEvent 0 ∩ future ⁻¹' B) ∪ (stateEvent 1 ∩ future ⁻¹' B) := by
      ext z
      constructor
      · intro hz
        have hstate : z ∈ stateEvent 0 ∪ stateEvent 1 := by
          rw [hcover]
          exact Set.mem_univ z
        rcases hstate with hstate | hstate
        · exact Or.inl ⟨hstate, hz⟩
        · exact Or.inr ⟨hstate, hz⟩
      · intro hz
        rcases hz with hz | hz
        · exact hz.2
        · exact hz.2
    have hsum : source (stateEvent 0) + source (stateEvent 1) = 1 := by
      rw [← measure_union hdisjoint (hstateEvent 1), hcover, measure_univ]
    calc
      Measure.map future source B = source (future ⁻¹' B) := Measure.map_apply hfuture hB
      _ = source ((stateEvent 0 ∩ future ⁻¹' B) ∪ (stateEvent 1 ∩ future ⁻¹' B)) :=
        congrArg source hcoverFuture
      _ = source (stateEvent 0 ∩ future ⁻¹' B) +
          source (stateEvent 1 ∩ future ⁻¹' B) := by
            rw [measure_union (hdisjoint.mono Set.inter_subset_left Set.inter_subset_left)
              ((hstateEvent 1).inter (hfuture hB))]
      _ = (source (stateEvent 0) + source (stateEvent 1)) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
            rw [hfactor 0, hfactor 1, add_mul]
      _ = mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
            rw [hsum, one_mul]
      _ = switchLaw B := by
            symm
            exact Measure.map_apply
              AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair hB
  refine ⟨(hjoint.prodMk hfuture).aemeasurable, ?_⟩
  calc
    Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × β =>
        (joint z, future z)) source =
        (Measure.map joint source).prod (Measure.map future source) := by
          rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
            hjoint.aemeasurable hfuture.aemeasurable).mp hindep]
    _ = (Measure.map joint source).prod switchLaw := by rw [hfutureLaw]
    _ = _ := by rfl

/-- After any independent nonnegative external time, the literal alternating
switch-stream residual factors from every measurable external-history event.
This sums the two endpoint-conditioned product-space factorizations, so it
does not introduce a CTMC strong-Markov assumption or discard the endpoint
by a restart convention. -/
theorem measure_switchGapsAfterPairAtTime_prod_history_factor
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [SFinite nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ᵐ t ∂nu, 0 ≤ time t) (initial : Fin 2)
    (A : Set β) (hA : MeasurableSet A)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) := Set.univ ×ˢ A
    let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2)
    (mu.prod nu) (Set.inter historyEvent (future ⁻¹' B)) =
      (mu.prod nu) historyEvent *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let stateEvent (target : Fin 2) : Set (((Nat -> Real) × (Nat -> Real)) × β) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target}
  let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) × β) := Set.univ ×ˢ A
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let H := historyEvent
  let F : Set (((Nat -> Real) × (Nat -> Real)) × β) := future ⁻¹' B
  let Einitial := stateEvent initial
  let Eother := stateEvent (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
  have hH : MeasurableSet H := by
    simpa [H, historyEvent] using (MeasurableSet.univ.prod hA)
  have hF : MeasurableSet F := by
    exact hB.preimage
      ((measurable_switchGapsAfterPairAtTime initial).comp
        (measurable_fst.prodMk (htime.comp measurable_snd)))
  have hEinitial : MeasurableSet Einitial := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
      initial).comp (measurable_fst.prodMk (htime.comp measurable_snd)))
        (measurableSet_singleton _)
  have hEother : MeasurableSet Eother := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
      initial).comp (measurable_fst.prodMk (htime.comp measurable_snd)))
        (measurableSet_singleton _)
  have hdisjointEndpoints : Disjoint Einitial Eother := by
    refine Set.disjoint_left.2 ?_
    intro z hinitial hother
    exact AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne initial
      (hother.symm.trans hinitial)
  have hendpointUnion : Einitial ∪ Eother = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    simpa [Einitial, Eother, stateEvent,
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime] using
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAt_eq_initial_or_eq_otherState
        initial
        (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair z.1)
        (time z.2))
  have hleft := measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
    switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial initial A hA B hB
  have hright := measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
    switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial) A hA B hB
  have hpiecesDisjoint : Disjoint ((Einitial ∩ H) ∩ F) ((Eother ∩ H) ∩ F) := by
    refine Set.disjoint_left.2 ?_
    intro z hleft hright
    exact (Set.disjoint_left.1 hdisjointEndpoints) hleft.1.1 hright.1.1
  have hpiecesUnion : ((Einitial ∩ H) ∩ F) ∪ ((Eother ∩ H) ∩ F) = H ∩ F := by
    ext z
    constructor
    · rintro (hleft | hright)
      · exact ⟨hleft.1.2, hleft.2⟩
      · exact ⟨hright.1.2, hright.2⟩
    · intro h
      have hendpoint : z ∈ Einitial ∪ Eother := by
        rw [hendpointUnion]
        simp
      rcases hendpoint with hinitial | hother
      · exact Or.inl ⟨⟨hinitial, h.1⟩, h.2⟩
      · exact Or.inr ⟨⟨hother, h.1⟩, h.2⟩
  have hendpointPiecesDisjoint : Disjoint (Einitial ∩ H) (Eother ∩ H) := by
    refine Set.disjoint_left.2 ?_
    intro z hleft hright
    exact (Set.disjoint_left.1 hdisjointEndpoints) hleft.1 hright.1
  have hendpointPiecesUnion : (Einitial ∩ H) ∪ (Eother ∩ H) = H := by
    ext z
    constructor
    · rintro (hleft | hright)
      · exact hleft.2
      · exact hright.2
    · intro h
      have hendpoint : z ∈ Einitial ∪ Eother := by
        rw [hendpointUnion]
        simp
      rcases hendpoint with hinitial | hother
      · exact Or.inl ⟨hinitial, h⟩
      · exact Or.inr ⟨hother, h⟩
  calc
    (mu.prod nu) (H ∩ F) =
        (mu.prod nu) (((Einitial ∩ H) ∩ F) ∪ ((Eother ∩ H) ∩ F)) := by
          rw [hpiecesUnion]
    _ = (mu.prod nu) ((Einitial ∩ H) ∩ F) +
        (mu.prod nu) ((Eother ∩ H) ∩ F) := by
          exact measure_union hpiecesDisjoint ((hEother.inter hH).inter hF)
    _ = (mu.prod nu) (Einitial ∩ H) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) +
        (mu.prod nu) (Eother ∩ H) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [mu, stateEvent, historyEvent, future, H, F, Einitial, Eother] using
            congrArg₂ (· + ·) hleft hright
    _ = ((mu.prod nu) (Einitial ∩ H) + (mu.prod nu) (Eother ∩ H)) *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [add_mul]
    _ = (mu.prod nu) ((Einitial ∩ H) ∪ (Eother ∩ H)) *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [measure_union hendpointPiecesDisjoint (hEother.inter hH)]
    _ = (mu.prod nu) H *
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [hendpointPiecesUnion]

/-- The full external input and the literal alternating switch residual are
independent.  This is the map-level form of the preceding event
factorization; it keeps the external time and all of its companion data
available for subsequent source constructions. -/
theorem indepFun_snd_switchGapsAfterPairAtTime
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [IsProbabilityMeasure nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ b, 0 ≤ time b) (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    (fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) ⟂ᵢ[mu.prod nu]
      (fun z => switchGapsAfterPairAtTime initial (z.1, time z.2)) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hfactor (A : Set β) (hA : MeasurableSet A)
      (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
      (mu.prod nu) ((Set.univ ×ˢ A) ∩ (future ⁻¹' B)) =
        (mu.prod nu) (Set.univ ×ˢ A) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
    simpa [mu, future] using
      (measure_switchGapsAfterPairAtTime_prod_history_factor
        switchIJ switchJI hswitchIJ hswitchJI nu time htime
        (ae_of_all _ hnonneg) initial A hA B hB)
  have hsnd (A : Set β) (hA : MeasurableSet A) :
      (mu.prod nu) ((fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) ⁻¹' A) =
        (mu.prod nu) (Set.univ ×ˢ A) := by
    congr 1
    ext z
    simp
  have hfutureMeasure (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
      (mu.prod nu) (future ⁻¹' B) =
        mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
    calc
      (mu.prod nu) (future ⁻¹' B) =
          (mu.prod nu) ((Set.univ ×ˢ Set.univ) ∩ (future ⁻¹' B)) := by
            congr 1
            ext z
            simp
      _ = (mu.prod nu) (Set.univ ×ˢ Set.univ) *
          mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) :=
            hfactor Set.univ MeasurableSet.univ B hB
      _ = mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
            simp
  refine ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro A B hA hB
  change (mu.prod nu)
      ((fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) ⁻¹' A ∩ future ⁻¹' B) =
    (mu.prod nu) ((fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) ⁻¹' A) *
      (mu.prod nu) (future ⁻¹' B)
  rw [hsnd A hA, hfutureMeasure B hB]
  convert hfactor A hA B hB using 1
  congr 1
  ext z
  simp

/-- The joint source law of an arbitrary external input and the future
alternating switch streams.  The residual has the original ordered
state-indexed switch-stream law and is independent of the full external
input, not merely of its elapsed-time projection. -/
theorem switchGapsAfterPairAtTime_withExternal_hasLaw
    {β : Type*} [MeasurableSpace β]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) [IsProbabilityMeasure nu] (time : β -> Real) (htime : Measurable time)
    (hnonneg : ∀ b, 0 ≤ time b) (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    HasLaw (fun z : ((Nat -> Real) × (Nat -> Real)) × β =>
      (z.2, switchGapsAfterPairAtTime initial (z.1, time z.2)))
      (nu.prod (Measure.map
        AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu))
      (mu.prod nu) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let future : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let switchLaw : Measure (Fin 2 -> Nat -> Real) := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hsnd : Measurable (fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) :=
    measurable_snd
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hind : (fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) ⟂ᵢ[mu.prod nu]
      future := by
    simpa [mu, future] using
      (indepFun_snd_switchGapsAfterPairAtTime
        switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial)
  have hfutureLaw : Measure.map future (mu.prod nu) = switchLaw := by
    apply Measure.ext
    intro B hB
    calc
      Measure.map future (mu.prod nu) B = (mu.prod nu) (future ⁻¹' B) := by
        exact Measure.map_apply hfuture hB
      _ = mu (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
        have h := measure_switchGapsAfterPairAtTime_prod_history_factor
          switchIJ switchJI hswitchIJ hswitchJI nu time htime
          (ae_of_all _ hnonneg) initial Set.univ MeasurableSet.univ B hB
        dsimp only at h
        have huniv : (Set.univ ×ˢ (Set.univ : Set β)) =
            (Set.univ : Set (((Nat -> Real) × (Nat -> Real)) × β)) := by
          ext z
          simp
        have hinter : (Set.univ : Set (((Nat -> Real) × (Nat -> Real)) × β)).inter
            (future ⁻¹' B) = future ⁻¹' B := by
          ext z
          constructor
          · intro hz
            exact hz.2
          · intro hz
            exact ⟨Set.mem_univ z, hz⟩
        rw [huniv, hinter, measure_univ, one_mul] at h
        exact h
      _ = switchLaw B := by
        symm
        exact Measure.map_apply
          AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair hB
  refine ⟨(hsnd.prodMk hfuture).aemeasurable, ?_⟩
  calc
    Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × β => (z.2, future z))
        (mu.prod nu) =
        (Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × β => z.2) (mu.prod nu)).prod
          (Measure.map future (mu.prod nu)) := by
            exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
              hsnd.aemeasurable hfuture.aemeasurable).mp hind
    _ = nu.prod switchLaw := by
      rw [hfutureLaw, Measure.map_snd_prod, measure_univ, one_smul]

/-- The literal state-indexed switch streams remaining after the first
selected accepted trip completes.  This is a concrete source observable; its
law is derived below rather than built into the definition. -/
noncomputable def switchGapsAfterFirstAcceptedTripCompletion
    (initial state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Fin 2 -> Nat -> Real := fun seed =>
  AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
    initial (rawSwitchGaps seed)
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)

/-- Measurability of the literal post-completion switch-stream observable. -/
theorem measurable_switchGapsAfterFirstAcceptedTripCompletion
    (initial state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (switchGapsAfterFirstAcceptedTripCompletion initial state sigma) := by
  let selected := AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma
  have hselected : Measurable selected := by
    change Measurable
      (AcceptedTripSelection.firstAcceptedTripMark sigma ∘
        AcceptedArrivalTime.rawTripMarkStream state)
    exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)
  have hfuture : Measurable (fun seed : GN21RawCycleSeed =>
      AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed
        initial (rawSwitchGaps seed) (selected seed)) :=
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_switchGapsAfterElapsed
      initial).comp (measurable_rawSwitchGaps.prodMk hselected)
  simpa [switchGapsAfterFirstAcceptedTripCompletion, selected] using hfuture

/-- The literal state-indexed switch streams remaining after the actual
calendar completion of the first accepted request. -/
noncomputable def switchGapsAfterFirstAcceptedArrivalCalendarCompletion
    (initial : Fin 2) (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Fin 2 -> Nat -> Real := fun seed =>
  AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed initial
    (rawSwitchGaps seed)
    (AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed))

/-- Measurability of the literal post-calendar-completion switch streams. -/
theorem measurable_switchGapsAfterFirstAcceptedArrivalCalendarCompletion
    (initial : Fin 2) (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (switchGapsAfterFirstAcceptedArrivalCalendarCompletion initial clock state sigma) := by
  let completion := fun seed : GN21RawCycleSeed =>
    AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma seed)
  have hcompletion : Measurable completion := by
    exact AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryCalendarCompletionTime.comp
      (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory
        clock state sigma hsigma)
  simpa [switchGapsAfterFirstAcceptedArrivalCalendarCompletion, completion] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_switchGapsAfterElapsed
      initial).comp (measurable_rawSwitchGaps.prodMk hcompletion)

/-- Exact source law of the raw CTMC endpoint at the literal selected-trip
completion.  The result combines the raw switch-clock pair and the literal
selected mark before applying the concrete alternating-path endpoint
functional; it does not replace the endpoint with the analytic CTMC kernel.
Evaluating this product-law pushforward remains a separate analytic step. -/
theorem stateAtFirstAcceptedTripCompletion_hasLaw_raw_product
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (stateAtFirstAcceptedTripCompletion initial state sigma)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial)
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchJI)).prod
          (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let switchLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let inputLaw := switchLaw.prod selectedLaw
  have hinput : HasLaw (fun seed =>
      (rawSwitchGapPair seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
      inputLaw
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [switchLaw, selectedLaw, inputLaw] using
      (rawSwitchGapPair_firstAcceptedTripMark_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hendpoint : HasLaw
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial)
        inputLaw)
      inputLaw :=
    ⟨(AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
      initial).aemeasurable, rfl⟩
  have hcomposed := hendpoint.fun_comp hinput
  refine hcomposed.congr ?_
  filter_upwards [] with seed
  simp only [stateAtFirstAcceptedTripCompletion,
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime]
  rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
  rfl

/-- The raw completion endpoint and literal post-completion state-indexed
switch streams factor exactly for either displayed initial state.  The
selected trip duration is integrated as an independent external clock over
the deterministic alternating restart law; no CTMC strong-Markov property is
assumed. -/
theorem measure_stateAtFirstAcceptedTripCompletion_switchGapsAfter_factor
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial state target : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    sourceLaw (Set.inter
      {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
      ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)) =
      sourceLaw {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target} *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let inputLaw := switchLaw.prod selectedLaw
  let input : GN21RawCycleSeed -> ((Nat -> Real) × (Nat -> Real)) × Real := fun seed =>
    (rawSwitchGapPair seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
  let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) × Real) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial z = target}
  let jointEvent : Set (((Nat -> Real) × (Nat -> Real)) × Real) :=
    Set.inter stateEvent (switchGapsAfterPairAtTime initial ⁻¹' B)
  let endpointEvent : Set GN21RawCycleSeed :=
    {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
  let rawJointEvent : Set GN21RawCycleSeed :=
    Set.inter endpointEvent
      ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)
  letI : IsProbabilityMeasure sourceLaw := by
    simpa [sourceLaw] using
      (isProbabilityMeasure_gn21RawCycleSeedMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI)
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hinput : HasLaw input inputLaw sourceLaw := by
    simpa [input, inputLaw, switchLaw, selectedLaw, sourceLaw] using
      (rawSwitchGapPair_firstAcceptedTripMark_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ t ∂selectedLaw, 0 ≤ t := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun t ht => by
        have htpos : 0 < t := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset ht
        exact htpos.le))
  have hstateEvent : MeasurableSet stateEvent :=
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial)
      (measurableSet_singleton target)
  have hjointEvent : MeasurableSet jointEvent :=
    hstateEvent.inter ((measurable_switchGapsAfterPairAtTime initial) hB)
  have hinputMeas : Measurable input := by
    have hselected : Measurable
        (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma) := by
      change Measurable
        (AcceptedTripSelection.firstAcceptedTripMark sigma ∘
          AcceptedArrivalTime.rawTripMarkStream state)
      exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)
    exact measurable_rawSwitchGapPair.prodMk hselected
  have hrawJointPreimage : input ⁻¹' jointEvent = rawJointEvent := by
    ext seed
    change
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (rawSwitchGapPair seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) = target ∧
        switchGapsAfterPairAtTime initial
          (rawSwitchGapPair seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) ∈ B) ↔
      (stateAt initial seed
          (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) = target ∧
        switchGapsAfterFirstAcceptedTripCompletion initial state sigma seed ∈ B)
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime,
      switchGapsAfterPairAtTime, stateAt,
      switchGapsAfterFirstAcceptedTripCompletion]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
  have hendpointPreimage : input ⁻¹' stateEvent = endpointEvent := by
    ext seed
    change
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
        (rawSwitchGapPair seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) = target ↔
      stateAt initial seed
        (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) = target
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime, stateAt]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
  have hrawJoint : sourceLaw rawJointEvent = inputLaw jointEvent := by
    calc
      sourceLaw rawJointEvent = sourceLaw (input ⁻¹' jointEvent) := by
        rw [hrawJointPreimage]
      _ = (Measure.map input sourceLaw) jointEvent := by
        exact (Measure.map_apply hinputMeas hjointEvent).symm
      _ = inputLaw jointEvent := by rw [hinput.map_eq]
  have hendpoint : sourceLaw endpointEvent = inputLaw stateEvent := by
    calc
      sourceLaw endpointEvent = sourceLaw (input ⁻¹' stateEvent) := by
        rw [hendpointPreimage]
      _ = (Measure.map input sourceLaw) stateEvent := by
        exact (Measure.map_apply hinputMeas hstateEvent).symm
      _ = inputLaw stateEvent := by rw [hinput.map_eq]
  calc
    sourceLaw (Set.inter
        {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
        ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)) =
        sourceLaw rawJointEvent := by rfl
    _ = inputLaw jointEvent := hrawJoint
    _ = inputLaw stateEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
      simpa [inputLaw, jointEvent, stateEvent, switchLaw, selectedLaw] using
        (measure_stateAtPairAtTime_switchGapsAfter_prod_factor
          switchIJ switchJI hswitchIJ hswitchJI selectedLaw id measurable_id hselectedNonneg
          initial target B hB)
    _ = sourceLaw endpointEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
      rw [← hendpoint]
    _ = sourceLaw {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target} *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
      rfl

/-- The literal post-completion switch residual factors jointly from every
measurable event of the complete stopped arrival/mark history and the
completion endpoint.  This transports the history-indexed product-space
factorization through the raw GN seed; it does not invoke a CTMC strong-Markov
property. -/
theorem measure_stateAtFirstAcceptedTripCompletion_switchGapsAfter_history_factor
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (initial state target : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hclockTwo : clock ≠ 2) (hclockThree : clock ≠ 3)
    (A : Set ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)))
    (hA : MeasurableSet A)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma
    sourceLaw (Set.inter
      (Set.inter
        {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
        (history ⁻¹' A))
      ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)) =
      sourceLaw (Set.inter
        {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
        (history ⁻¹' A)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let historyInputLaw : Measure ((Nat -> TripLength) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
  let historyLaw : Measure ((((Nat × TripLength) × (Nat -> TripLength)) × Real) ×
      (Nat -> Real)) :=
    Measure.map (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma) historyInputLaw
  let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma
  let time := AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength
  let input : GN21RawCycleSeed -> ((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) := fun seed =>
    (rawSwitchGapPair seed, history seed)
  let inputLaw := switchLaw.prod historyLaw
  let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real))) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target}
  let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real))) := Set.univ ×ˢ A
  let future : ((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) ->
      Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let inputJointEvent := Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)
  let inputEndpointEvent := Set.inter stateEvent historyEvent
  let endpointEvent : Set GN21RawCycleSeed :=
    {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
  let rawHistoryEvent : Set GN21RawCycleSeed := history ⁻¹' A
  let rawJointEvent : Set GN21RawCycleSeed := Set.inter
    (Set.inter endpointEvent rawHistoryEvent)
    ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)
  let rawEndpointEvent : Set GN21RawCycleSeed := Set.inter endpointEvent rawHistoryEvent
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  letI : IsProbabilityMeasure sourceLaw := by
    simpa [sourceLaw] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  have hclockRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hclockRate
  letI : IsProbabilityMeasure historyInputLaw := by
    dsimp [historyInputLaw]
    infer_instance
  have hhistoryMeas : Measurable history := by
    simpa [history] using
      AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory clock state sigma hsigma
  have hhistoryInputMeas : Measurable
      (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma) := by
    exact AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistoryInputMeas.aemeasurable
  letI : IsProbabilityMeasure inputLaw := by
    dsimp [inputLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hinput : HasLaw input inputLaw sourceLaw := by
    simpa [input, inputLaw, switchLaw, historyLaw, historyInputLaw, sourceLaw,
      AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (rawSwitchGapPair_firstAcceptedArrivalHistory_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass
        hclockTwo hclockThree)
  have htimeMeas : Measurable time := by
    simpa [time] using AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryTripLength
  have hselected : HasLaw
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      selectedLaw sourceLaw := by
    simpa [selectedLaw, sourceLaw] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ t ∂selectedLaw, 0 ≤ t := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun t ht => by
        have htpos : 0 < t := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset ht
        exact htpos.le))
  have hrawSelectedNonneg : ∀ᵐ seed ∂sourceLaw,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
    exact (hselected.ae_iff (p := fun t : TripLength => 0 ≤ t) (by fun_prop)).mpr
      hselectedNonneg
  have hsnd : HasLaw Prod.snd historyLaw inputLaw := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [MeasureTheory.Measure.map_snd_prod]
    simp
  have hhistoryLaw := hsnd.fun_comp hinput
  change HasLaw history historyLaw sourceLaw at hhistoryLaw
  have htimeRaw : ∀ᵐ seed ∂sourceLaw, 0 ≤ time (history seed) := by
    filter_upwards [hrawSelectedNonneg] with seed hseed
    simpa [time, history] using hseed
  have htimeNonneg : ∀ᵐ h ∂historyLaw, 0 ≤ time h := by
    exact (hhistoryLaw.ae_iff (p := fun h => 0 ≤ time h) (by fun_prop)).mp htimeRaw
  have hstateEvent : MeasurableSet stateEvent :=
    ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htimeMeas.comp measurable_snd))) (measurableSet_singleton target)
  have hhistoryEvent : MeasurableSet historyEvent := by
    simpa [historyEvent] using (MeasurableSet.univ.prod hA)
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htimeMeas.comp measurable_snd))
  have hinputJointEvent : MeasurableSet inputJointEvent :=
    (hstateEvent.inter hhistoryEvent).inter (hfuture hB)
  have hinputEndpointEvent : MeasurableSet inputEndpointEvent :=
    hstateEvent.inter hhistoryEvent
  have hinputMeas : Measurable input :=
    measurable_rawSwitchGapPair.prodMk hhistoryMeas
  have hinputJointPreimage : input ⁻¹' inputJointEvent = rawJointEvent := by
    ext seed
    dsimp [inputJointEvent, rawJointEvent, input, stateEvent, historyEvent,
      future, endpointEvent, rawHistoryEvent]
    change
      ((AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (rawSwitchGapPair seed, time (history seed)) = target ∧
        (rawSwitchGapPair seed ∈ Set.univ ∧ history seed ∈ A)) ∧
        switchGapsAfterPairAtTime initial (rawSwitchGapPair seed, time (history seed)) ∈ B) ↔
      ((stateAtFirstAcceptedTripCompletion initial state sigma seed = target ∧ history seed ∈ A) ∧
        switchGapsAfterFirstAcceptedTripCompletion initial state sigma seed ∈ B)
    simp only [Set.mem_univ, true_and]
    have htimeHistory : time (history seed) =
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
      simpa [time, history] using
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength_gn21RawFirstAcceptedArrivalHistory
          clock state sigma seed)
    rw [htimeHistory]
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime,
      switchGapsAfterPairAtTime, stateAt, stateAtFirstAcceptedTripCompletion,
      switchGapsAfterFirstAcceptedTripCompletion]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
  have hinputEndpointPreimage : input ⁻¹' inputEndpointEvent = rawEndpointEvent := by
    ext seed
    dsimp [inputEndpointEvent, rawEndpointEvent, input, stateEvent, historyEvent,
      endpointEvent, rawHistoryEvent]
    change
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (rawSwitchGapPair seed, time (history seed)) = target ∧
        (rawSwitchGapPair seed ∈ Set.univ ∧ history seed ∈ A)) ↔
      (stateAtFirstAcceptedTripCompletion initial state sigma seed = target ∧ history seed ∈ A)
    simp only [Set.mem_univ, true_and]
    have htimeHistory : time (history seed) =
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
      simpa [time, history] using
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength_gn21RawFirstAcceptedArrivalHistory
          clock state sigma seed)
    rw [htimeHistory]
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime, stateAt,
      stateAtFirstAcceptedTripCompletion]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
  have hrawJoint : sourceLaw rawJointEvent = inputLaw inputJointEvent := by
    calc
      sourceLaw rawJointEvent = sourceLaw (input ⁻¹' inputJointEvent) := by
        rw [hinputJointPreimage]
      _ = (Measure.map input sourceLaw) inputJointEvent := by
        exact (Measure.map_apply hinputMeas hinputJointEvent).symm
      _ = inputLaw inputJointEvent := by rw [hinput.map_eq]
  have hrawEndpoint : sourceLaw rawEndpointEvent = inputLaw inputEndpointEvent := by
    calc
      sourceLaw rawEndpointEvent = sourceLaw (input ⁻¹' inputEndpointEvent) := by
        rw [hinputEndpointPreimage]
      _ = (Measure.map input sourceLaw) inputEndpointEvent := by
        exact (Measure.map_apply hinputMeas hinputEndpointEvent).symm
      _ = inputLaw inputEndpointEvent := by rw [hinput.map_eq]
  calc
    sourceLaw (Set.inter
        (Set.inter
          {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
          (history ⁻¹' A))
        ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)) =
        sourceLaw rawJointEvent := by rfl
    _ = inputLaw inputJointEvent := hrawJoint
    _ = inputLaw inputEndpointEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [inputLaw, inputJointEvent, inputEndpointEvent, stateEvent, historyEvent,
            future, switchLaw, historyLaw, time] using
            (measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
              switchIJ switchJI hswitchIJ hswitchJI historyLaw time htimeMeas htimeNonneg
              initial target A hA B hB)
    _ = sourceLaw rawEndpointEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [← hrawEndpoint]
    _ = sourceLaw (Set.inter
        {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}
        (history ⁻¹' A)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rfl

/-- The literal post-completion switch residual factors jointly from every
measurable stopped accepted-arrival history event and the CTMC endpoint at
the *actual calendar completion time*.  The stopped history retains both the
accepted request's elapsed arrival time and its selected duration, so this is
the calendar-time counterpart to the duration-only proposal-layer result
above; it is a product-space source calculation, not a strong-Markov axiom. -/
theorem measure_stateAtFirstAcceptedArrivalCalendarCompletion_switchGapsAfter_history_factor
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (initial state target : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hclockTwo : clock ≠ 2) (hclockThree : clock ≠ 3)
    (A : Set ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)))
    (hA : MeasurableSet A)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma
    sourceLaw (Set.inter
      (Set.inter
        {seed | stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target}
        (history ⁻¹' A))
      ((switchGapsAfterFirstAcceptedArrivalCalendarCompletion initial clock state sigma) ⁻¹' B)) =
      sourceLaw (Set.inter
        {seed | stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target}
        (history ⁻¹' A)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let historyInputLaw : Measure ((Nat -> TripLength) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
  let historyLaw : Measure ((((Nat × TripLength) × (Nat -> TripLength)) × Real) ×
      (Nat -> Real)) :=
    Measure.map (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma) historyInputLaw
  let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory clock state sigma
  let time := AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime
  let input : GN21RawCycleSeed -> ((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) := fun seed =>
    (rawSwitchGapPair seed, history seed)
  let inputLaw := switchLaw.prod historyLaw
  let stateEvent : Set (((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real))) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, time z.2) = target}
  let historyEvent : Set (((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real))) := Set.univ ×ˢ A
  let future : ((Nat -> Real) × (Nat -> Real)) ×
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) ->
      Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let inputJointEvent := Set.inter (Set.inter stateEvent historyEvent) (future ⁻¹' B)
  let inputEndpointEvent := Set.inter stateEvent historyEvent
  let endpointEvent : Set GN21RawCycleSeed :=
    {seed | stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target}
  let rawHistoryEvent : Set GN21RawCycleSeed := history ⁻¹' A
  let rawJointEvent : Set GN21RawCycleSeed := Set.inter
    (Set.inter endpointEvent rawHistoryEvent)
    ((switchGapsAfterFirstAcceptedArrivalCalendarCompletion initial clock state sigma) ⁻¹' B)
  let rawEndpointEvent : Set GN21RawCycleSeed := Set.inter endpointEvent rawHistoryEvent
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  letI : IsProbabilityMeasure sourceLaw := by
    simpa [sourceLaw] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  have hclockRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hclockRate
  letI : IsProbabilityMeasure historyInputLaw := by
    dsimp [historyInputLaw]
    infer_instance
  have hhistoryMeas : Measurable history := by
    simpa [history] using
      AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory clock state sigma hsigma
  have hhistoryInputMeas : Measurable
      (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma) := by
    exact AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistoryInputMeas.aemeasurable
  letI : IsProbabilityMeasure inputLaw := by
    dsimp [inputLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hinput : HasLaw input inputLaw sourceLaw := by
    simpa [input, inputLaw, switchLaw, historyLaw, historyInputLaw, sourceLaw,
      AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (rawSwitchGapPair_firstAcceptedArrivalHistory_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass
        hclockTwo hclockThree)
  have htimeMeas : Measurable time := by
    simpa [time] using
      AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryCalendarCompletionTime
  have hselected : HasLaw
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      selectedLaw sourceLaw := by
    simpa [selectedLaw, sourceLaw] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ t ∂selectedLaw, 0 ≤ t := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun t ht => by
        have htpos : 0 < t := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset ht
        exact htpos.le))
  have hrawSelectedNonneg : ∀ᵐ seed ∂sourceLaw,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
    exact (hselected.ae_iff (p := fun t : TripLength => 0 ≤ t) (by fun_prop)).mpr
      hselectedNonneg
  have hrawArrivalNonneg : ∀ᵐ seed ∂sourceLaw,
      0 ≤ AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
    simpa [sourceLaw] using
      (AcceptedArrivalTime.ae_gn21RawFirstAcceptedArrivalTime_nonnegative
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma)
  have hsnd : HasLaw Prod.snd historyLaw inputLaw := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [MeasureTheory.Measure.map_snd_prod]
    simp
  have hhistoryLaw := hsnd.fun_comp hinput
  change HasLaw history historyLaw sourceLaw at hhistoryLaw
  have htimeRaw : ∀ᵐ seed ∂sourceLaw, 0 ≤ time (history seed) := by
    filter_upwards [hrawArrivalNonneg, hrawSelectedNonneg] with seed harrival hselected
    simpa [time, history,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime_gn21RawFirstAcceptedArrivalHistory]
      using add_nonneg harrival hselected
  have htimeNonneg : ∀ᵐ h ∂historyLaw, 0 ≤ time h := by
    exact (hhistoryLaw.ae_iff (p := fun h => 0 ≤ time h) (by fun_prop)).mp htimeRaw
  have hstateEvent : MeasurableSet stateEvent :=
    ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htimeMeas.comp measurable_snd))) (measurableSet_singleton target)
  have hhistoryEvent : MeasurableSet historyEvent := by
    simpa [historyEvent] using (MeasurableSet.univ.prod hA)
  have hfuture : Measurable future := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htimeMeas.comp measurable_snd))
  have hinputJointEvent : MeasurableSet inputJointEvent :=
    (hstateEvent.inter hhistoryEvent).inter (hfuture hB)
  have hinputEndpointEvent : MeasurableSet inputEndpointEvent :=
    hstateEvent.inter hhistoryEvent
  have hinputMeas : Measurable input :=
    measurable_rawSwitchGapPair.prodMk hhistoryMeas
  have hinputJointPreimage : input ⁻¹' inputJointEvent = rawJointEvent := by
    ext seed
    dsimp [inputJointEvent, rawJointEvent, input, stateEvent, historyEvent,
      future, endpointEvent, rawHistoryEvent]
    change
      ((AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (rawSwitchGapPair seed, time (history seed)) = target ∧
        (rawSwitchGapPair seed ∈ Set.univ ∧ history seed ∈ A)) ∧
        switchGapsAfterPairAtTime initial (rawSwitchGapPair seed, time (history seed)) ∈ B) ↔
      ((stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target ∧
        history seed ∈ A) ∧
        switchGapsAfterFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed ∈ B)
    simp only [Set.mem_univ, true_and]
    have htimeHistory : time (history seed) =
        AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime clock state sigma seed +
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
      simpa [time, history] using
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime_gn21RawFirstAcceptedArrivalHistory
          clock state sigma seed)
    rw [htimeHistory]
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime,
      switchGapsAfterPairAtTime, stateAt,
      stateAtFirstAcceptedArrivalCalendarCompletion,
      switchGapsAfterFirstAcceptedArrivalCalendarCompletion]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
    rw [← htimeHistory]
  have hinputEndpointPreimage : input ⁻¹' inputEndpointEvent = rawEndpointEvent := by
    ext seed
    dsimp [inputEndpointEvent, rawEndpointEvent, input, stateEvent, historyEvent,
      endpointEvent, rawHistoryEvent]
    change
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (rawSwitchGapPair seed, time (history seed)) = target ∧
        (rawSwitchGapPair seed ∈ Set.univ ∧ history seed ∈ A)) ↔
      (stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target ∧
        history seed ∈ A)
    simp only [Set.mem_univ, true_and]
    have htimeHistory : time (history seed) =
        AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime clock state sigma seed +
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
      simpa [time, history] using
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryCalendarCompletionTime_gn21RawFirstAcceptedArrivalHistory
          clock state sigma seed)
    rw [htimeHistory]
    simp only [AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime, stateAt,
      stateAtFirstAcceptedArrivalCalendarCompletion]
    rw [← rawSwitchGaps_eq_twoStateGapsOfPair seed]
    rw [← htimeHistory]
  have hrawJoint : sourceLaw rawJointEvent = inputLaw inputJointEvent := by
    calc
      sourceLaw rawJointEvent = sourceLaw (input ⁻¹' inputJointEvent) := by
        rw [hinputJointPreimage]
      _ = (Measure.map input sourceLaw) inputJointEvent := by
        exact (Measure.map_apply hinputMeas hinputJointEvent).symm
      _ = inputLaw inputJointEvent := by rw [hinput.map_eq]
  have hrawEndpoint : sourceLaw rawEndpointEvent = inputLaw inputEndpointEvent := by
    calc
      sourceLaw rawEndpointEvent = sourceLaw (input ⁻¹' inputEndpointEvent) := by
        rw [hinputEndpointPreimage]
      _ = (Measure.map input sourceLaw) inputEndpointEvent := by
        exact (Measure.map_apply hinputMeas hinputEndpointEvent).symm
      _ = inputLaw inputEndpointEvent := by rw [hinput.map_eq]
  calc
    sourceLaw (Set.inter
        (Set.inter
          {seed | stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target}
          (history ⁻¹' A))
        ((switchGapsAfterFirstAcceptedArrivalCalendarCompletion initial clock state sigma) ⁻¹' B)) =
        sourceLaw rawJointEvent := by rfl
    _ = inputLaw inputJointEvent := hrawJoint
    _ = inputLaw inputEndpointEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [inputLaw, inputJointEvent, inputEndpointEvent, stateEvent, historyEvent,
            future, switchLaw, historyLaw, time] using
            (measure_stateAtPairAtTime_switchGapsAfter_prod_history_factor
              switchIJ switchJI hswitchIJ hswitchJI historyLaw time htimeMeas htimeNonneg
              initial target A hA B hB)
    _ = sourceLaw rawEndpointEvent *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [← hrawEndpoint]
    _ = sourceLaw (Set.inter
        {seed | stateAtFirstAcceptedArrivalCalendarCompletion initial clock state sigma seed = target}
        (history ⁻¹' A)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rfl

/-- After a selected trip completes, the literal future switch streams factor
from every measurable event of the complete stopped arrival/mark history.
This is the two-state sum of the endpoint-conditioned source factorization;
it is not a strong-Markov assumption. -/
theorem measure_switchGapsAfterFirstAcceptedTripCompletion_history_factor
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (initial state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hclockTwo : clock ≠ 2) (hclockThree : clock ≠ 3)
    (A : Set ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)))
    (hA : MeasurableSet A)
    (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory
      clock state sigma
    sourceLaw (Set.inter (history ⁻¹' A)
      ((switchGapsAfterFirstAcceptedTripCompletion initial state sigma) ⁻¹' B)) =
      sourceLaw (history ⁻¹' A) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let history := AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory
    clock state sigma
  let future := switchGapsAfterFirstAcceptedTripCompletion initial state sigma
  let H : Set GN21RawCycleSeed := history ⁻¹' A
  let F : Set GN21RawCycleSeed := future ⁻¹' B
  let Einitial : Set GN21RawCycleSeed :=
    {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = initial}
  let Eother : Set GN21RawCycleSeed :=
    {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed =
      AppliedModelingLib.Probability.TwoStateSwitching.otherState initial}
  have hH : MeasurableSet H := by
    exact hA.preimage
      (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory
        clock state sigma hsigma)
  have hF : MeasurableSet F := by
    exact hB.preimage
      (measurable_switchGapsAfterFirstAcceptedTripCompletion initial state sigma hsigma)
  have hEinitial : MeasurableSet Einitial := by
    exact (measurable_stateAtFirstAcceptedTripCompletion initial state sigma hsigma)
      (measurableSet_singleton _)
  have hEother : MeasurableSet Eother := by
    exact (measurable_stateAtFirstAcceptedTripCompletion initial state sigma hsigma)
      (measurableSet_singleton _)
  have hdisjointEndpoints : Disjoint Einitial Eother := by
    refine Set.disjoint_left.2 ?_
    intro seed hinit hother
    exact AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne initial
      (hother.symm.trans hinit)
  have hendpointUnion : Einitial ∪ Eother = Set.univ := by
    ext seed
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    simpa [stateAtFirstAcceptedTripCompletion] using
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAt_eq_initial_or_eq_otherState
        initial (rawSwitchGaps seed)
        (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
  have hleft := measure_stateAtFirstAcceptedTripCompletion_switchGapsAfter_history_factor
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
    clock initial state initial sigma hsigma hsigma_subset hmass
    hclockTwo hclockThree A hA B hB
  have hright := measure_stateAtFirstAcceptedTripCompletion_switchGapsAfter_history_factor
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
    clock initial state
    (AppliedModelingLib.Probability.TwoStateSwitching.otherState initial)
    sigma hsigma hsigma_subset hmass
    hclockTwo hclockThree A hA B hB
  have hpiecesDisjoint : Disjoint ((Einitial ∩ H) ∩ F) ((Eother ∩ H) ∩ F) := by
    refine Set.disjoint_left.2 ?_
    intro seed hleft hright
    exact (Set.disjoint_left.1 hdisjointEndpoints) hleft.1.1 hright.1.1
  have hpiecesUnion : ((Einitial ∩ H) ∩ F) ∪ ((Eother ∩ H) ∩ F) = H ∩ F := by
    ext seed
    constructor
    · rintro (hleft | hright)
      · exact ⟨hleft.1.2, hleft.2⟩
      · exact ⟨hright.1.2, hright.2⟩
    · intro h
      have hendpoint : seed ∈ Einitial ∪ Eother := by
        rw [hendpointUnion]
        simp
      rcases hendpoint with hinit | hother
      · exact Or.inl ⟨⟨hinit, h.1⟩, h.2⟩
      · exact Or.inr ⟨⟨hother, h.1⟩, h.2⟩
  have hendpointPiecesDisjoint : Disjoint (Einitial ∩ H) (Eother ∩ H) := by
    refine Set.disjoint_left.2 ?_
    intro seed hleft hright
    exact (Set.disjoint_left.1 hdisjointEndpoints) hleft.1 hright.1
  have hendpointPiecesUnion : (Einitial ∩ H) ∪ (Eother ∩ H) = H := by
    ext seed
    constructor
    · rintro (hleft | hright)
      · exact hleft.2
      · exact hright.2
    · intro h
      have hendpoint : seed ∈ Einitial ∪ Eother := by
        rw [hendpointUnion]
        simp
      rcases hendpoint with hinit | hother
      · exact Or.inl ⟨hinit, h⟩
      · exact Or.inr ⟨hother, h⟩
  calc
    sourceLaw (H ∩ F) =
        sourceLaw (((Einitial ∩ H) ∩ F) ∪ ((Eother ∩ H) ∩ F)) := by
          rw [hpiecesUnion]
    _ = sourceLaw ((Einitial ∩ H) ∩ F) + sourceLaw ((Eother ∩ H) ∩ F) := by
          exact measure_union hpiecesDisjoint ((hEother.inter hH).inter hF)
    _ = sourceLaw (Einitial ∩ H) *
          switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) +
        sourceLaw (Eother ∩ H) *
          switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [sourceLaw, switchLaw, H, F, Einitial, Eother, history, future] using
            congrArg₂ (· + ·) hleft hright
    _ = (sourceLaw (Einitial ∩ H) + sourceLaw (Eother ∩ H)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [add_mul]
    _ = sourceLaw ((Einitial ∩ H) ∪ (Eother ∩ H)) *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [measure_union hendpointPiecesDisjoint (hEother.inter hH)]
    _ = sourceLaw H *
        switchLaw (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [hendpointPiecesUnion]

/-- The literal raw CTMC endpoint at the first selected-trip completion is
the selected-mark average of its literal deterministic-time endpoint mass.
The independence used here is the proved raw three-factor product law. -/
theorem measure_stateAtFirstAcceptedTripCompletion_eq_lintegral_rawStateProbability
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial state target : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target} =
      ∫⁻ t, rawStateProbability muI muJ arrivalI arrivalJ switchIJ switchJI initial target t
        ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let switchLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hendpoint : HasLaw (stateAtFirstAcceptedTripCompletion initial state sigma)
      (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial)
        (switchLaw.prod selectedLaw)) sourceLaw := by
    simpa [switchLaw, selectedLaw, sourceLaw] using
      (stateAtFirstAcceptedTripCompletion_hasLaw_raw_product
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial state sigma hsigma hmass)
  have hselected : Measurable (stateAtFirstAcceptedTripCompletion initial state sigma) :=
    measurable_stateAtFirstAcceptedTripCompletion initial state sigma hsigma
  calc
    sourceLaw {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target} =
        (Measure.map (stateAtFirstAcceptedTripCompletion initial state sigma) sourceLaw)
          {target} := by
            rw [Measure.map_apply hselected (measurableSet_singleton _)]
            rfl
    _ = (Measure.map
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial)
        (switchLaw.prod selectedLaw)) {target} := by
          rw [hendpoint.map_eq]
    _ = (switchLaw.prod selectedLaw) {z |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial z = target} := by
          rw [Measure.map_apply
            (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial)
            (measurableSet_singleton _)]
          rfl
    _ = ∫⁻ t, switchLaw {pair |
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
          (pair, t) = target} ∂selectedLaw := by
          exact measure_stateAtPairAtTime_prod_eq_lintegral
            switchLaw selectedLaw id measurable_id initial target
    _ = ∫⁻ t, rawStateProbability
        muI muJ arrivalI arrivalJ switchIJ switchJI initial target t ∂selectedLaw := by
          apply lintegral_congr
          intro t
          calc
            switchLaw {pair |
                AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
                  (pair, t) = target} =
                sourceLaw {seed | stateAt initial seed t = target} := by
                  simpa [switchLaw, sourceLaw,
                    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime] using
                    (measure_rawSwitchGapPair_stateAt_eq
                      muI muJ arrivalI arrivalJ switchIJ switchJI
                      harrivalI harrivalJ hswitchIJ hswitchJI initial target t)
            _ = rawStateProbability
                muI muJ arrivalI arrivalJ switchIJ switchJI initial target t := by
                  symm
                  exact rawStateProbability_eq_measure_rawStateAt
                    muI muJ arrivalI arrivalJ switchIJ switchJI initial target t

/-- Under the source's feasible positive-trip policy domain, the literal
state at selected-trip completion has the expected two-state CTMC transition
probability.  The proof first identifies the actual endpoint event with its
raw fixed-time average, and only then applies the deterministic-time kernel
theorem on the selected-mark support. -/
theorem measure_stateAtFirstAcceptedTripCompletion_toReal_eq_integral_kernel
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initial state target : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}).toReal =
      ∫ t, AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t initial target
        ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let sourceLaw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let rawProbability := rawStateProbability
    muI muJ arrivalI arrivalJ switchIJ switchJI initial target
  letI : IsProbabilityMeasure
      (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_rawSwitchPathLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  have hraw_meas : Measurable rawProbability := by
    simpa [rawProbability] using (measurable_rawStateProbability
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initial target)
  have hraw_finite : ∀ᵐ t ∂selectedLaw, rawProbability t < ∞ := by
    apply ae_of_all
    intro t
    simpa [rawProbability] using
      (lt_top_iff_ne_top.mpr
        (AppliedModelingLib.Probability.TwoStateSwitching.stateProbability_ne_top
          (rawSwitchPathLaw muI muJ arrivalI arrivalJ switchIJ switchJI) initial target t))
  have hendpoint := measure_stateAtFirstAcceptedTripCompletion_eq_lintegral_rawStateProbability
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initial state target sigma hsigma hmass
  have hnonneg : ∀ᵐ t ∂selectedLaw, 0 ≤ t := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun t ht => by
        have htpos : 0 < t := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset ht
        exact htpos.le))
  calc
    (sourceLaw {seed | stateAtFirstAcceptedTripCompletion initial state sigma seed = target}).toReal =
        (∫⁻ t, rawProbability t ∂selectedLaw).toReal := by
          exact congrArg ENNReal.toReal
            (by simpa [sourceLaw, selectedLaw, rawProbability] using hendpoint)
    _ = ∫ t, (rawProbability t).toReal ∂selectedLaw := by
          symm
          exact integral_toReal hraw_meas.aemeasurable hraw_finite
    _ = ∫ t, rawStateProbabilityReal
        muI muJ arrivalI arrivalJ switchIJ switchJI initial target t ∂selectedLaw := by
          rfl
    _ = ∫ t, AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t initial target
        ∂selectedLaw := by
          apply integral_congr_ae
          filter_upwards [hnonneg] with t ht
          exact rawStateProbabilityReal_eq_twoStateCtmcTransitionProb
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initial target t ht

/-- An endpoint together with the external coordinate that determines its
clock is independent of an untouched independent companion and the literal
future switch tail.  Keeping the clock coordinate on the left is essential
when the caller records an elapsed holding time or reward alongside the
endpoint.  This is a source-product transport, not a strong-Markov assertion.
-/
theorem stateAtPairAtTime_history_companion_switchGapsAfter_hasLaw
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) (kappa : Measure γ) [IsProbabilityMeasure nu] [IsProbabilityMeasure kappa]
    (time : β -> Real) (htime : Measurable time) (hnonneg : ∀ b, 0 ≤ time b)
    (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial (z.1, time z.2)
    let joint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 × β := fun z =>
      (endpoint z, z.2)
    let future : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2.1)
    HasLaw (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
      (joint (z.1, z.2.1), (z.2.2, future z)))
      ((Measure.map joint (mu.prod nu)).prod
        (kappa.prod (Measure.map
          AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu)))
      (mu.prod (nu.prod kappa)) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial (z.1, time z.2)
  let joint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 × β := fun z =>
    (endpoint z, z.2)
  let futureBase : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, time z.2)
  let future : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 -> Nat -> Real := fun z =>
    futureBase (z.1, z.2.1)
  let switchLaw : Measure (Fin 2 -> Nat -> Real) := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu
  let baseSource := mu.prod nu
  let source := mu.prod (nu.prod kappa)
  let baseTarget := (Measure.map joint baseSource).prod switchLaw
  let target := (Measure.map joint baseSource).prod (kappa.prod switchLaw)
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure baseSource := by
    dsimp [baseSource]
    infer_instance
  letI : IsProbabilityMeasure (Measure.map joint baseSource) :=
    Measure.isProbabilityMeasure_map
      (((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
        (measurable_fst.prodMk (htime.comp measurable_snd))).prodMk measurable_snd).aemeasurable
  letI : IsProbabilityMeasure baseTarget := by
    dsimp [baseTarget]
    infer_instance
  have hjoint : Measurable joint := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))).prodMk measurable_snd
  have hfutureBase : Measurable futureBase := by
    exact (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  let baseMap : ((Nat -> Real) × (Nat -> Real)) × β ->
      (Fin 2 × β) × (Fin 2 -> Nat -> Real) := fun z => (joint z, futureBase z)
  have hbaseMap : Measurable baseMap := hjoint.prodMk hfutureBase
  have hbase : HasLaw baseMap baseTarget baseSource := by
    simpa [baseMap, baseTarget, baseSource, joint, futureBase, mu, endpoint, switchLaw] using
      (stateAtPairAtTime_history_switchGapsAfter_joint_hasLaw
        switchIJ switchJI hswitchIJ hswitchJI nu time htime hnonneg initial)
  let hbaseMeasurePreserving : MeasurePreserving baseMap baseSource baseTarget :=
    ⟨hbaseMap, hbase.map_eq⟩
  let reassoc : ((Nat -> Real) × (Nat -> Real)) × (β × γ) ->
      (((Nat -> Real) × (Nat -> Real)) × β) × γ := MeasurableEquiv.prodAssoc.symm
  have hreassoc : MeasurePreserving reassoc source (baseSource.prod kappa) := by
    simpa [reassoc, source, baseSource] using
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc mu nu kappa))
  let factor : (((Nat -> Real) × (Nat -> Real)) × β) × γ ->
      ((Fin 2 × β) × (Fin 2 -> Nat -> Real)) × γ := Prod.map baseMap id
  have hfactor : MeasurePreserving factor (baseSource.prod kappa) (baseTarget.prod kappa) := by
    simpa [factor] using
      (MeasurePreserving.prod hbaseMeasurePreserving (MeasurePreserving.id kappa))
  let reassociate : ((Fin 2 × β) × (Fin 2 -> Nat -> Real)) × γ ->
      (Fin 2 × β) × ((Fin 2 -> Nat -> Real) × γ) := MeasurableEquiv.prodAssoc
  have hReassociate : MeasurePreserving reassociate (baseTarget.prod kappa)
      ((Measure.map joint baseSource).prod (switchLaw.prod kappa)) := by
    simpa [reassociate, baseTarget] using
      (measurePreserving_prodAssoc (Measure.map joint baseSource) switchLaw kappa)
  let swapTail : (Fin 2 × β) × ((Fin 2 -> Nat -> Real) × γ) ->
      (Fin 2 × β) × (γ × (Fin 2 -> Nat -> Real)) :=
    Prod.map id Prod.swap
  have hswapTail : MeasurePreserving swapTail
      ((Measure.map joint baseSource).prod (switchLaw.prod kappa)) target := by
    let hswap : MeasurePreserving
        (Prod.swap : (Fin 2 -> Nat -> Real) × γ -> γ × (Fin 2 -> Nat -> Real))
        (switchLaw.prod kappa) (kappa.prod switchLaw) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    simpa [swapTail, target] using
      (MeasurePreserving.prod (MeasurePreserving.id (Measure.map joint baseSource)) hswap)
  let output : ((Nat -> Real) × (Nat -> Real)) × (β × γ) ->
      (Fin 2 × β) × (γ × (Fin 2 -> Nat -> Real)) := fun z =>
    (joint (z.1, z.2.1), (z.2.2, future z))
  have houtput : output = swapTail ∘ reassociate ∘ factor ∘ reassoc := by
    rfl
  have htransport : MeasurePreserving output source target := by
    rw [houtput]
    exact hswapTail.comp (hReassociate.comp (hfactor.comp hreassoc))
  simpa [output, target, source, joint, future, futureBase, mu, endpoint, switchLaw,
    baseSource] using htransport.hasLaw

/-- An endpoint read from a literal switch pair at an external clock is
independent of the pair of an untouched independent companion and the
literal future switch tail.  This is a source-product transport, not a
strong-Markov assertion. -/
theorem stateAtPairAtTime_companion_switchGapsAfter_hasLaw
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (switchIJ switchJI : Real) (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (nu : Measure β) (kappa : Measure γ) [IsProbabilityMeasure nu] [IsProbabilityMeasure kappa]
    (time : β -> Real) (htime : Measurable time) (hnonneg : ∀ b, 0 ≤ time b)
    (initial : Fin 2) :
    let mu :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial (z.1, time z.2)
    let future : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 -> Nat -> Real := fun z =>
      switchGapsAfterPairAtTime initial (z.1, time z.2.1)
    HasLaw (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
      (endpoint (z.1, z.2.1), (z.2.2, future z)))
      ((Measure.map endpoint (mu.prod nu)).prod
        (kappa.prod (Measure.map
          AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu)))
      (mu.prod (nu.prod kappa)) := by
  classical
  dsimp
  let mu : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let endpoint : ((Nat -> Real) × (Nat -> Real)) × β -> Fin 2 := fun z =>
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial (z.1, time z.2)
  let historyTime : β × γ -> Real := fun z => time z.1
  let future : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 -> Nat -> Real := fun z =>
    switchGapsAfterPairAtTime initial (z.1, historyTime z.2)
  let endpointCompanion : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 × γ := fun z =>
    (endpoint (z.1, z.2.1), z.2.2)
  let switchLaw : Measure (Fin 2 -> Nat -> Real) := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair mu
  let source := mu.prod (nu.prod kappa)
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : IsProbabilityMeasure switchLaw :=
    Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistoryTime : Measurable historyTime := htime.comp measurable_fst
  have hfuture : Measurable future :=
    (measurable_switchGapsAfterPairAtTime initial).comp
      (measurable_fst.prodMk (hhistoryTime.comp measurable_snd))
  have hendpoint : Measurable endpoint :=
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (htime.comp measurable_snd))
  have hendpointCompanion : Measurable endpointCompanion :=
    (hendpoint.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hpair : Measurable (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
      (endpointCompanion z, future z)) := hendpointCompanion.prodMk hfuture
  have hindepBase := indepFun_stateAtPairAtTime_history_switchGapsAfter
    switchIJ switchJI hswitchIJ hswitchJI (nu.prod kappa) historyTime hhistoryTime
    (ae_of_all _ (fun z => hnonneg z.1)) initial
  let jointHistory : ((Nat -> Real) × (Nat -> Real)) × (β × γ) -> Fin 2 × (β × γ) := fun z =>
    (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime initial
      (z.1, historyTime z.2), z.2)
  let dropHistory : Fin 2 × (β × γ) -> Fin 2 × γ := fun z => (z.1, z.2.2)
  have hdropHistory : Measurable dropHistory := measurable_fst.prodMk
    (measurable_snd.comp measurable_snd)
  have hjointHistory : Measurable jointHistory :=
    ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime initial).comp
      (measurable_fst.prodMk (hhistoryTime.comp measurable_snd))).prodMk measurable_snd
  have hendpointCompanion_eq : endpointCompanion = dropHistory ∘ jointHistory := by rfl
  have hindep : endpointCompanion ⟂ᵢ[source] future := by
    rw [hendpointCompanion_eq]
    exact hindepBase.comp hdropHistory measurable_id
  have hfuturePair := switchGapsAfterPairAtTime_withExternal_hasLaw
    switchIJ switchJI hswitchIJ hswitchJI (nu.prod kappa) historyTime hhistoryTime
    (fun z => hnonneg z.1) initial
  have hfutureLaw : Measure.map future source = switchLaw := by
    have hmap := hfuturePair.map_eq
    have hsnd : Measurable (Prod.snd : (β × γ) × (Fin 2 -> Nat -> Real) -> Fin 2 -> Nat -> Real) :=
      measurable_snd
    calc
      Measure.map future source = Measure.map Prod.snd
          (Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
            (z.2, future z)) source) := by
              symm
              calc
                Measure.map Prod.snd
                    (Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
                      (z.2, future z)) source) =
                    Measure.map (Prod.snd ∘ fun z : ((Nat -> Real) × (Nat -> Real)) ×
                      (β × γ) => (z.2, future z)) source := by
                        rw [Measure.map_map hsnd (measurable_snd.prodMk hfuture)]
                _ = Measure.map future source := by rfl
      _ = Measure.map Prod.snd ((nu.prod kappa).prod switchLaw) := by rw [hmap]
      _ = switchLaw := by rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hendpointCompanionLaw : Measure.map endpointCompanion source =
      (Measure.map endpoint (mu.prod nu)).prod kappa := by
    let reassoc : ((Nat -> Real) × (Nat -> Real)) × (β × γ) ->
        (((Nat -> Real) × (Nat -> Real)) × β) × γ := MeasurableEquiv.prodAssoc.symm
    let factor : (((Nat -> Real) × (Nat -> Real)) × β) × γ -> Fin 2 × γ :=
      Prod.map endpoint id
    have hreassoc : MeasurePreserving reassoc source ((mu.prod nu).prod kappa) := by
      simpa [reassoc, source] using
        (MeasurePreserving.symm MeasurableEquiv.prodAssoc
          (measurePreserving_prodAssoc mu nu kappa))
    have hfactor : Measurable factor := hendpoint.prodMap measurable_id
    calc
      Measure.map endpointCompanion source =
          Measure.map factor (Measure.map reassoc source) := by
            rw [show endpointCompanion = factor ∘ reassoc by rfl,
              Measure.map_map hfactor hreassoc.measurable]
      _ = Measure.map factor ((mu.prod nu).prod kappa) := by rw [hreassoc.map_eq]
      _ = (Measure.map endpoint (mu.prod nu)).prod (Measure.map id kappa) := by
            rw [show factor = Prod.map endpoint id by rfl,
              ← Measure.map_prod_map (mu.prod nu) kappa hendpoint measurable_id]
      _ = _ := by rw [Measure.map_id]
  let reassociate : (Fin 2 × γ) × (Fin 2 -> Nat -> Real) ->
      Fin 2 × (γ × (Fin 2 -> Nat -> Real)) := MeasurableEquiv.prodAssoc
  have hreassociate : Measurable reassociate := MeasurableEquiv.prodAssoc.measurable
  refine ⟨(hreassociate.comp hpair).aemeasurable, ?_⟩
  calc
    Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
        (endpoint (z.1, z.2.1), (z.2.2, future z))) source =
        Measure.map reassociate (Measure.map (fun z => (endpointCompanion z, future z)) source) := by
          rw [show (fun z : ((Nat -> Real) × (Nat -> Real)) × (β × γ) =>
            (endpoint (z.1, z.2.1), (z.2.2, future z))) =
              reassociate ∘ (fun z => (endpointCompanion z, future z)) by rfl,
            Measure.map_map hreassociate hpair]
    _ = Measure.map reassociate
        ((Measure.map endpointCompanion source).prod (Measure.map future source)) := by
          rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
            hendpointCompanion.aemeasurable hfuture.aemeasurable).mp hindep]
    _ = Measure.map reassociate (((Measure.map endpoint (mu.prod nu)).prod kappa).prod
        switchLaw) := by rw [hendpointCompanionLaw, hfutureLaw]
    _ = (Measure.map endpoint (mu.prod nu)).prod (kappa.prod switchLaw) := by
      simpa [reassociate] using
        (Measure.prodAssoc_prod (μ := Measure.map endpoint (mu.prod nu))
          (ν := kappa) (τ := switchLaw))

end RawTwoStateCTMC

end

end GN21DriverSurgePricing
