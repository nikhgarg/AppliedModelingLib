import GN21DriverSurgePricing.RawPostThinningRaceBridge
import GN21DriverSurgePricing.RawRenewalCycleConstruction
import AppliedModelingLib.Foundations.Probability.IndependentPairLaw

/-!
# Literal calendar continuation seeds for GN21

The raw one-subcycle source calculations expose residual marked-arrival and
switch streams.  This module begins the global-calendar construction by
putting those *same literal tails* back into the raw-seed layout.  In
particular, the switch-first branch below is not an iid proposal draw: every
next-seed coordinate is a deterministic tail of the original source path.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- The fresh-tail package produced by a switch-first marked-renewal stop:
the departing mark and gap tails, followed by untouched switch and incoming
continuation inputs. -/
abbrev GN21SwitchFirstMarkedTailWithCompanion :=
  ((Nat -> TripLength) × (Nat -> Real)) ×
    (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))

/-- Reassemble the two state-marked arrival continuations and the two switch
continuations into GN's fixed state-labelled raw-seed layout.  The `state`
argument says which marked-arrival component is the departing one; it does
not relabel the source states. -/
def gn21RawCycleSeedOfStateContinuation (state : Fin 2) :
    GN21SwitchFirstJointContinuation -> GN21RawCycleSeed
  | z =>
      match state with
      | 0 =>
        ((fun | 0 => z.1.1 | 1 => z.2.2.1 | 2 => z.2.1.1 | 3 => z.2.1.2),
          fun | 0 => z.1.2 | 1 => z.2.2.2)
      | 1 =>
        ((fun | 0 => z.2.2.1 | 1 => z.1.1 | 2 => z.2.1.1 | 3 => z.2.1.2),
          fun | 0 => z.2.2.2 | 1 => z.1.2)

/-- The literal next raw seed on a switch-first source branch.  It is the
source-tail reassembly, not a new sample of four clocks and two mark streams.
-/
noncomputable def gn21RawSwitchFirstNextCycleSeed (state : Fin 2) :
    GN21RawCycleSeed -> GN21RawCycleSeed :=
  gn21RawCycleSeedOfStateContinuation state ∘
    gn21RawSwitchFirstJointContinuation state

theorem measurable_gn21RawCycleSeedOfStateContinuation (state : Fin 2) :
    Measurable (gn21RawCycleSeedOfStateContinuation state) := by
  fin_cases state
  · apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro clock
      fin_cases clock
      · exact measurable_fst.comp measurable_fst
      · exact (measurable_fst.comp (measurable_snd.comp measurable_snd))
      · exact (measurable_fst.comp (measurable_fst.comp measurable_snd))
      · exact (measurable_snd.comp (measurable_fst.comp measurable_snd))
    · apply measurable_pi_lambda
      intro s
      fin_cases s
      · exact measurable_snd.comp measurable_fst
      · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
  · apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro clock
      fin_cases clock
      · exact (measurable_fst.comp (measurable_snd.comp measurable_snd))
      · exact measurable_fst.comp measurable_fst
      · exact (measurable_fst.comp (measurable_fst.comp measurable_snd))
      · exact (measurable_snd.comp (measurable_fst.comp measurable_snd))
    · apply measurable_pi_lambda
      intro s
      fin_cases s
      · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
      · exact measurable_snd.comp measurable_fst

theorem measurable_gn21RawSwitchFirstNextCycleSeed (state : Fin 2) :
    Measurable (gn21RawSwitchFirstNextCycleSeed state) := by
  exact (measurable_gn21RawCycleSeedOfStateContinuation state).comp
    (measurable_gn21RawSwitchFirstJointContinuation state)

/-- The literal active switch head and the deterministically reassembled next
raw seed on a switch-first source branch.  The head is retained separately so
the branch's elapsed time can later be carried jointly with its fresh seed. -/
noncomputable def gn21RawSwitchFirstHeadAndNextCycleSeed (state : Fin 2) :
    GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
  let z := gn21RawSwitchFirstJointContinuationInput state seed
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
    (fun t : Real => max 0 t) (z.1.1.1, z.1.2)
  let tail :=
    (AppliedModelingLib.Probability.IIDStream.externalIndexTail
      (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) (history, z.2),
      AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail
        (fun t : Real => max 0 t) (z.1.1.1, z.1.2))
  (history.1,
    gn21RawCycleSeedOfStateContinuation state ((tail.2, tail.1), z.1.1.2))

theorem measurable_gn21RawSwitchFirstHeadAndNextCycleSeed (state : Fin 2) :
    Measurable (gn21RawSwitchFirstHeadAndNextCycleSeed state) := by
  let input := gn21RawSwitchFirstJointContinuationInput state
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
    (fun t : Real => max 0 t)
  let index : Real × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let tail := AppliedModelingLib.Probability.IIDStream.externalIndexTail
    (α := TripLength) index
  let residual := AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail
    (fun t : Real => max 0 t)
  have hinput : Measurable input :=
    measurable_gn21RawSwitchFirstJointContinuationInput state
  have htime : Measurable (fun t : Real => max 0 t) :=
    measurable_const.max measurable_id
  have hhistory : Measurable history := by
    simpa [history] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimePastHistory
        (fun t : Real => max 0 t) htime)
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have htail : Measurable tail := by
    simpa [tail] using
      (AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail
        (α := TripLength) index hindex)
  have hresidual : Measurable residual := by
    simpa [residual] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeResidualTail
        (fun t : Real => max 0 t) htime)
  let continuation : GN21SwitchFirstJointContinuationInput ->
      GN21SwitchFirstJointContinuation := fun z =>
    let h := history (z.1.1.1, z.1.2)
    let t := (tail (h, z.2), residual (z.1.1.1, z.1.2))
    ((t.2, t.1), z.1.1.2)
  have hcontinuation : Measurable continuation := by
    exact
      (((hresidual.comp
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst))).prodMk
        (htail.comp
          ((hhistory.comp
            ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
              (measurable_snd.comp measurable_fst))).prodMk measurable_snd))).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hhead : Measurable (fun z : GN21SwitchFirstJointContinuationInput =>
      (history (z.1.1.1, z.1.2)).1) :=
    measurable_fst.comp (hhistory.comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)))
  have houtput : Measurable (fun z : GN21SwitchFirstJointContinuationInput =>
      ((history (z.1.1.1, z.1.2)).1,
        gn21RawCycleSeedOfStateContinuation state (continuation z))) :=
    hhead.prodMk ((measurable_gn21RawCycleSeedOfStateContinuation state).comp hcontinuation)
  simpa [gn21RawSwitchFirstHeadAndNextCycleSeed, input, history, index, tail,
    residual, continuation] using houtput.comp hinput

/-- The unnormalized law of the literal active switch head on the totalized
no-hit branch.  It retains the realized marked-arrival prefix only to define
the event, then projects it away; the companion and all fresh tails are not
part of this history measure. -/
noncomputable def gn21SwitchFirstHeadHistoryMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) (state : Fin 2)
    (sigma : TripPolicy) : Measure Real :=
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let headLaw := if state = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let departingArrivalLaw :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let departingMarkLaw :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
    (fun t : Real => max 0 t)
  let A := AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
    (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma
  Measure.map Prod.fst
    (Measure.map Prod.fst
      (((Measure.map history (headLaw.prod departingArrivalLaw)).prod
        departingMarkLaw).restrict A))

/-- The literal calendar time at which the first accepted trip in the current
open state completes.  This is kept as a raw-source observable: the accepted
arrival time and its selected duration are both read from the same seed. -/
noncomputable def gn21RawAcceptedCalendarCompletionTime
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Real :=
  fun seed => (gn21RawPostThinningRaceSeed state sigma seed).1 +
    (gn21RawPostThinningRaceSeed state sigma seed).2.2

theorem measurable_gn21RawAcceptedCalendarCompletionTime
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedCalendarCompletionTime state sigma) := by
  exact (measurable_fst.comp
    (measurable_gn21RawPostThinningRaceSeed state sigma hsigma)).add
      (measurable_snd.comp
      (measurable_snd.comp
        (measurable_gn21RawPostThinningRaceSeed state sigma hsigma)))

/-- On the literal accepted-winner branch, the subcycle time is exactly the
accepted arrival time plus its selected trip duration.  This is a pathwise
branch identity; it does not use a conditional-law replacement. -/
theorem gn21RawPostThinningRaceSubcycleTime_eq_acceptedCalendarCompletionTime
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (haccepted : seed ∈ gn21RawPostThinningRaceAcceptedFirst state sigma) :
    gn21RawPostThinningRaceSubcycleTime state sigma seed =
      gn21RawAcceptedCalendarCompletionTime state sigma seed := by
  have hle : (gn21RawPostThinningRaceSeed state sigma seed).1 ≤
      (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
    exact le_of_not_gt (by
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using haccepted)
  simp [gn21RawPostThinningRaceSubcycleTime,
    gn21RawPostThinningRaceAcceptedContribution,
    gn21RawPostThinningRaceMinimum,
    AppliedModelingLib.Probability.exponentialRaceMinimum,
    gn21RawAcceptedCalendarCompletionTime, Set.indicator_of_mem haccepted,
    min_eq_left hle]

/-- The literal marked arrival input of one physical state after the accepted
trip's completion time.  The external coordinate is the original raw seed,
so this definition retains the actual source path rather than sampling an
independent post-completion input. -/
noncomputable def gn21RawAcceptedCompletionMarkedArrivalResidual
    (state : Fin 2) (sigma : TripPolicy) (arrivalState : Fin 2) :
    GN21RawCycleSeed -> (Nat -> Real) × (Nat -> TripLength) := fun seed =>
  AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
    (fun source : GN21RawCycleSeed =>
      gn21RawAcceptedCalendarCompletionTime state sigma source)
    ((seed,
      AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex arrivalState) seed),
      AcceptedArrivalTime.rawTripMarkStream arrivalState seed)

theorem measurable_gn21RawAcceptedCompletionMarkedArrivalResidual
    (state : Fin 2) (sigma : TripPolicy) (arrivalState : Fin 2)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma arrivalState) := by
  let time := gn21RawAcceptedCalendarCompletionTime state sigma
  let input : GN21RawCycleSeed ->
      (GN21RawCycleSeed × (Nat -> Real)) × (Nat -> TripLength) := fun seed =>
    ((seed, AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex arrivalState) seed),
      AcceptedArrivalTime.rawTripMarkStream arrivalState seed)
  have htime : Measurable time :=
    measurable_gn21RawAcceptedCalendarCompletionTime state sigma hsigma
  have hinput : Measurable input :=
    (measurable_id.prodMk
      (AcceptedArrivalTime.measurable_rawClockStream
        (gn21ArrivalClockIndex arrivalState))).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream arrivalState)
  exact (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
    (α := TripLength) time htime).comp hinput

/-- The literal next raw seed at an accepted-trip completion.  Both physical
arrival streams are residualized at the *same actual completion time* and the
switch streams are the already constructed literal completion tails.  No
coordinate in this definition is an iid proposal draw. -/
noncomputable def gn21RawAcceptedCompletionNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> GN21RawCycleSeed :=
  fun seed =>
    ((fun | 0 => (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 0 seed).1
          | 1 => (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 1 seed).1
          | 2 => (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 0
          | 3 => (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 1),
      fun | 0 => (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 0 seed).2
          | 1 => (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 1 seed).2)

theorem measurable_gn21RawAcceptedCompletionNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedCompletionNextCycleSeed state sigma) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro clock
    fin_cases clock
    · exact measurable_fst.comp
        (measurable_gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 0 hsigma)
    · exact measurable_fst.comp
        (measurable_gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 1 hsigma)
    · exact (measurable_pi_apply 0).comp
        (measurable_gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma hsigma)
    · exact (measurable_pi_apply 1).comp
        (measurable_gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma hsigma)
  · apply measurable_pi_lambda
    intro arrivalState
    fin_cases arrivalState
    · exact measurable_snd.comp
        (measurable_gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 0 hsigma)
    · exact measurable_snd.comp
        (measurable_gn21RawAcceptedCompletionMarkedArrivalResidual state sigma 1 hsigma)

/-- The literal raw seed after one open-state subcycle: use the source-tail
switch-first continuation exactly when the switch wins, and otherwise use the
literal accepted-trip completion continuation.  This is a deterministic map
of one raw source seed, not an independently sampled proposal seed. -/
noncomputable def gn21RawPostThinningRaceNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> GN21RawCycleSeed :=
  by
    classical
    exact fun seed => if seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma then
      gn21RawSwitchFirstNextCycleSeed state seed else
      gn21RawAcceptedCompletionNextCycleSeed state sigma seed

theorem measurable_gn21RawPostThinningRaceNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceNextCycleSeed state sigma) := by
  apply Measurable.ite
  · let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  · exact measurable_gn21RawSwitchFirstNextCycleSeed state
  · exact measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma

/-- The literal state in which the next open-state subcycle begins.  On a
switch-first branch it is the other state; on an accepted branch it is the
actual CTMC endpoint at selected-trip calendar completion. -/
noncomputable def gn21RawPostThinningRaceNextState
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Fin 2 :=
  by
    classical
    exact fun seed => if seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma then
      AppliedModelingLib.Probability.TwoStateSwitching.otherState state else
      gn21RawPostThinningRaceCalendarCompletionState state sigma seed

theorem measurable_gn21RawPostThinningRaceNextState
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceNextState state sigma) := by
  apply Measurable.ite
  · let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  · exact measurable_const
  · exact measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma

/-- The next-state transition is the literal raw exit event used in GN's
one-subcycle calculation. -/
theorem preimage_gn21RawPostThinningRaceNextState_otherState
    (state : Fin 2) (sigma : TripPolicy) :
    (gn21RawPostThinningRaceNextState state sigma) ⁻¹'
      {AppliedModelingLib.Probability.TwoStateSwitching.otherState state} =
      gn21RawPostThinningRaceExitState state sigma := by
  ext seed
  by_cases hswitch : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma
  · simp [gn21RawPostThinningRaceNextState, hswitch,
      gn21RawPostThinningRaceExitState]
  · simp [gn21RawPostThinningRaceNextState, hswitch,
      gn21RawPostThinningRaceExitState,
      gn21RawPostThinningRaceAcceptedFirst]

/-- For a two-state calendar subcycle, preserving the current state is
exactly the complement of the literal cross-state exit event. -/
theorem preimage_gn21RawPostThinningRaceNextState_self
    (state : Fin 2) (sigma : TripPolicy) :
    (gn21RawPostThinningRaceNextState state sigma) ⁻¹' {state} =
      (gn21RawPostThinningRaceExitState state sigma)ᶜ := by
  have hother := preimage_gn21RawPostThinningRaceNextState_otherState state sigma
  ext seed
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
  constructor
  · intro hself hexit
    have hotherState : gn21RawPostThinningRaceNextState state sigma seed =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState state := by
      have hmem : seed ∈
          (gn21RawPostThinningRaceNextState state sigma) ⁻¹'
            {AppliedModelingLib.Probability.TwoStateSwitching.otherState state} := by
        rw [hother]
        exact hexit
      simpa using hmem
    exact AppliedModelingLib.Probability.TwoStateSwitching.otherState_ne state
      (hotherState.symm.trans hself)
  · intro hnotExit
    have hnotOther : gn21RawPostThinningRaceNextState state sigma seed ≠
        AppliedModelingLib.Probability.TwoStateSwitching.otherState state := by
      intro heq
      apply hnotExit
      rw [← hother]
      simpa using heq
    have hcases (x : Fin 2) : x = state ∨
        x = AppliedModelingLib.Probability.TwoStateSwitching.otherState state := by
      fin_cases x <;> fin_cases state <;> simp
    exact (hcases _).resolve_right hnotOther

/-- Advance one literal open-state subcycle.  Both coordinates are read from
the current source tail: the new state is the physical state at the next open
subcycle, and the new raw seed is the corresponding unconsumed calendar tail.
-/
noncomputable def gn21RawCalendarAdvance (policy : Fin 2 -> TripPolicy) :
    (Fin 2 × GN21RawCycleSeed) -> Fin 2 × GN21RawCycleSeed := fun z =>
  (gn21RawPostThinningRaceNextState z.1 (policy z.1) z.2,
    gn21RawPostThinningRaceNextCycleSeed z.1 (policy z.1) z.2)

/-- Literal state--seed trajectory through consecutive open-state subcycles,
all built by deterministic residualization of a single initial raw seed. -/
noncomputable def gn21RawCalendarTrace (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) : Nat -> GN21RawCycleSeed -> Fin 2 × GN21RawCycleSeed
  | 0 => fun seed => (initialState, seed)
  | n + 1 => fun seed =>
      gn21RawCalendarAdvance policy (gn21RawCalendarTrace initialState policy n seed)

/-- The state at the beginning of the `n`th literal open-state subcycle. -/
noncomputable def gn21RawCalendarTraceState (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) : GN21RawCycleSeed -> Fin 2 :=
  fun seed => (gn21RawCalendarTrace initialState policy n seed).1

/-- The unconsumed literal raw seed at the beginning of the `n`th open-state
subcycle. -/
noncomputable def gn21RawCalendarTraceSeed (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) : GN21RawCycleSeed -> GN21RawCycleSeed :=
  fun seed => (gn21RawCalendarTrace initialState policy n seed).2

theorem gn21RawCalendarTrace_zero (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (seed : GN21RawCycleSeed) :
    gn21RawCalendarTrace initialState policy 0 seed = (initialState, seed) := rfl

theorem gn21RawCalendarTrace_succ (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) (seed : GN21RawCycleSeed) :
    gn21RawCalendarTrace initialState policy (n + 1) seed =
      gn21RawCalendarAdvance policy (gn21RawCalendarTrace initialState policy n seed) := rfl

theorem gn21RawCalendarTraceState_zero (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) :
    gn21RawCalendarTraceState initialState policy 0 = fun _ => initialState := by
  rfl

theorem gn21RawCalendarTraceSeed_zero (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) :
    gn21RawCalendarTraceSeed initialState policy 0 = id := by
  rfl

theorem gn21RawCalendarTraceState_succ (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) (seed : GN21RawCycleSeed) :
    gn21RawCalendarTraceState initialState policy (n + 1) seed =
      gn21RawPostThinningRaceNextState
        (gn21RawCalendarTraceState initialState policy n seed)
        (policy (gn21RawCalendarTraceState initialState policy n seed))
        (gn21RawCalendarTraceSeed initialState policy n seed) := by
  rfl

theorem gn21RawCalendarTraceSeed_succ (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) (seed : GN21RawCycleSeed) :
    gn21RawCalendarTraceSeed initialState policy (n + 1) seed =
      gn21RawPostThinningRaceNextCycleSeed
        (gn21RawCalendarTraceState initialState policy n seed)
        (policy (gn21RawCalendarTraceState initialState policy n seed))
        (gn21RawCalendarTraceSeed initialState policy n seed) := by
  rfl

theorem measurable_gn21RawCalendarAdvance (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) :
    Measurable (gn21RawCalendarAdvance policy) := by
  suffices hmeas : Measurable (fun z : Fin 2 × GN21RawCycleSeed =>
    if z.1 = 0 then
      (gn21RawPostThinningRaceNextState 0 (policy 0) z.2,
        gn21RawPostThinningRaceNextCycleSeed 0 (policy 0) z.2)
    else
      (gn21RawPostThinningRaceNextState 1 (policy 1) z.2,
        gn21RawPostThinningRaceNextCycleSeed 1 (policy 1) z.2)) by
    convert hmeas using 1
    funext z
    rcases z with ⟨state, seed⟩
    fin_cases state <;> simp [gn21RawCalendarAdvance]
  apply Measurable.ite
  · exact measurableSet_eq.preimage measurable_fst
  · exact (measurable_gn21RawPostThinningRaceNextState 0 (policy 0) (hpolicy 0)).prodMk
      (measurable_gn21RawPostThinningRaceNextCycleSeed 0 (policy 0) (hpolicy 0)) |>.comp
        measurable_snd
  · exact (measurable_gn21RawPostThinningRaceNextState 1 (policy 1) (hpolicy 1)).prodMk
      (measurable_gn21RawPostThinningRaceNextCycleSeed 1 (policy 1) (hpolicy 1)) |>.comp
        measurable_snd

theorem measurable_gn21RawCalendarTrace (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : Measurable (gn21RawCalendarTrace initialState policy n) := by
  induction n with
  | zero => exact measurable_const.prodMk measurable_id
  | succ n ih =>
      exact (measurable_gn21RawCalendarAdvance policy hpolicy).comp ih

theorem measurable_gn21RawCalendarTraceState (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : Measurable (gn21RawCalendarTraceState initialState policy n) := by
  exact measurable_fst.comp (measurable_gn21RawCalendarTrace initialState policy hpolicy n)

theorem measurable_gn21RawCalendarTraceSeed (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : Measurable (gn21RawCalendarTraceSeed initialState policy n) := by
  exact measurable_snd.comp (measurable_gn21RawCalendarTrace initialState policy hpolicy n)

/-- The literal event that the first `n` open-state subcycles have not yet
left their initial physical state.  It is defined from the same residualized
calendar trace rather than from an IID proposal-seed sequence. -/
noncomputable def gn21RawCalendarTraceNoExitEvent (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) : Nat -> Set GN21RawCycleSeed
  | 0 => Set.univ
  | n + 1 => gn21RawCalendarTraceNoExitEvent initialState policy n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ

/-- The event that the literal calendar trace never leaves its initial state. -/
noncomputable def gn21RawCalendarTraceNeverExitEvent (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) : Set GN21RawCycleSeed :=
  ⋂ n : Nat, gn21RawCalendarTraceNoExitEvent initialState policy n

/-- The literal event that the calendar remains in its initial physical state
through the first `n` open subcycles and then crosses to the other state in
subcycle `n`. -/
noncomputable def gn21RawCalendarTraceExitEvent (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) : Set GN21RawCycleSeed :=
  gn21RawCalendarTraceNoExitEvent initialState policy n ∩
    (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
      (gn21RawPostThinningRaceExitState initialState (policy initialState))

/-- The index of the literal first cross-state exit.  The value is totalized
at zero only when no such exit exists; that event is later proved null under
GN's positive-rate and positive-policy-mass primitives. -/
noncomputable def gn21RawCalendarFirstExitIndex (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (seed : GN21RawCycleSeed) : Nat := by
  classical
  exact if h : ∃ n, seed ∈ gn21RawCalendarTraceExitEvent initialState policy n then
    Nat.find h else 0

/-- The literal raw tail immediately after the totalized first cross-state
exit index. -/
noncomputable def gn21RawCalendarPostExitSeed (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) : GN21RawCycleSeed -> GN21RawCycleSeed :=
  fun seed => gn21RawCalendarTraceSeed initialState policy
    (gn21RawCalendarFirstExitIndex initialState policy seed + 1) seed

/-- The contribution of a raw-tail reward from subcycle `n` of a physical
state sojourn.  The indicator is the literal event that the calendar has not
left its initial state before that subcycle. -/
noncomputable def gn21RawCalendarTraceNoExitReward
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (reward : GN21RawCycleSeed -> Real) (n : Nat) : GN21RawCycleSeed -> Real :=
  (gn21RawCalendarTraceNoExitEvent initialState policy n).indicator
    (fun seed => reward (gn21RawCalendarTraceSeed initialState policy n seed))

/-- The bounded literal calendar reward accumulated while the trace remains
in its initial physical state.  This is a finite sum on one residualized raw
source seed, not a reward along a separately sampled proposal path. -/
noncomputable def gn21RawCalendarCappedStateStoppedReward
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (reward : GN21RawCycleSeed -> Real) (cap : Nat) : GN21RawCycleSeed -> Real :=
  fun seed => ∑ n ∈ Finset.range (cap + 1),
    gn21RawCalendarTraceNoExitReward initialState policy reward n seed

/-- The total literal calendar reward accumulated through the physical-state
exit.  On the null never-exit event this uses `tsum`'s total definition; the
almost-sure finite-exit theorem below supplies the intended source semantics. -/
noncomputable def gn21RawCalendarStoppedStateReward
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (reward : GN21RawCycleSeed -> Real) : GN21RawCycleSeed -> Real :=
  fun seed => ∑' n : Nat,
    gn21RawCalendarTraceNoExitReward initialState policy reward n seed

/-- The literal calendar time accumulated from an initial physical state
through its next cross-state exit. -/
noncomputable def gn21RawCalendarStoppedStateTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> Real :=
  gn21RawCalendarStoppedStateReward initialState policy
    (gn21RawPostThinningRaceSubcycleTime initialState (policy initialState))

/-- The literal calendar earnings accumulated from an initial physical state
through its next cross-state exit. -/
noncomputable def gn21RawCalendarStoppedStateEarning
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> Real :=
  gn21RawCalendarStoppedStateReward initialState policy
    (gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState))

/-- The elapsed time in the first `n` literal subcycles, evaluated along a
same-state continuation prefix.  The definition is total, while its later
product law is restricted to the literal event on which every displayed
subcycle has in fact remained in `initialState`. -/
noncomputable def gn21RawCalendarNoExitAccumulatedTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    Nat -> GN21RawCycleSeed -> Real
  | 0 => fun _ => 0
  | n + 1 => fun seed =>
      gn21RawCalendarNoExitAccumulatedTime initialState policy n seed +
        gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy n seed)

theorem gn21RawCalendarNoExitAccumulatedTime_zero
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    gn21RawCalendarNoExitAccumulatedTime initialState policy 0 = fun _ => 0 := rfl

theorem gn21RawCalendarNoExitAccumulatedTime_succ
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) (n : Nat)
    (seed : GN21RawCycleSeed) :
    gn21RawCalendarNoExitAccumulatedTime initialState policy (n + 1) seed =
      gn21RawCalendarNoExitAccumulatedTime initialState policy n seed +
        gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy n seed) := rfl

theorem norm_gn21RawCalendarTraceNoExitReward
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (reward : GN21RawCycleSeed -> Real) (n : Nat) (seed : GN21RawCycleSeed) :
    ‖gn21RawCalendarTraceNoExitReward initialState policy reward n seed‖ =
      gn21RawCalendarTraceNoExitReward initialState policy (fun z => ‖reward z‖) n seed := by
  by_cases h : seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n <;>
    simp [gn21RawCalendarTraceNoExitReward, Set.indicator, h]

theorem measurableSet_gn21RawCalendarTraceNoExitEvent (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : MeasurableSet (gn21RawCalendarTraceNoExitEvent initialState policy n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
      exact ih.inter
        ((measurableSet_gn21RawPostThinningRaceExitState initialState
          (policy initialState) (hpolicy initialState)).compl.preimage
          (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n))

theorem measurableSet_gn21RawCalendarTraceExitEvent (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : MeasurableSet (gn21RawCalendarTraceExitEvent initialState policy n) := by
  exact (measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n).inter
    ((measurableSet_gn21RawPostThinningRaceExitState initialState
      (policy initialState) (hpolicy initialState)).preimage
      (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n))

/-- On the no-exit event through a given subcycle index, the literal calendar
is still in its initial state at that index. -/
theorem gn21RawCalendarTraceState_eq_initial_on_noExitEvent
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (n : Nat) (seed : GN21RawCycleSeed)
    (hnoExit : seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n) :
    gn21RawCalendarTraceState initialState policy n seed = initialState := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
        (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ at hnoExit
      rcases hnoExit with ⟨hprior, hcurrent⟩
      have hstate := ih hprior
      rw [gn21RawCalendarTraceState_succ, hstate]
      change gn21RawCalendarTraceSeed initialState policy n seed ∈
        (gn21RawPostThinningRaceNextState initialState (policy initialState)) ⁻¹'
          {initialState}
      rw [preimage_gn21RawPostThinningRaceNextState_self]
      exact hcurrent

/-- Coordinatewise, the accepted-completion raw seed retains each state-local
marked arrival suffix at the actual trip-completion clock time. -/
theorem gn21RawAcceptedCompletionNextCycleSeed_arrivals
    (state : Fin 2) (sigma : TripPolicy) (arrivalState : Fin 2)
    (seed : GN21RawCycleSeed) :
    ((gn21RawAcceptedCompletionNextCycleSeed state sigma seed).1
      (gn21ArrivalClockIndex arrivalState),
      (gn21RawAcceptedCompletionNextCycleSeed state sigma seed).2 arrivalState) =
      gn21RawAcceptedCompletionMarkedArrivalResidual state sigma arrivalState seed := by
  fin_cases arrivalState <;> rfl

/-- Coordinatewise, the accepted-completion raw seed retains exactly the
literal future state-indexed switch streams. -/
theorem gn21RawAcceptedCompletionNextCycleSeed_switchGaps
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    ((gn21RawAcceptedCompletionNextCycleSeed state sigma seed).1 2,
      (gn21RawAcceptedCompletionNextCycleSeed state sigma seed).1 3) =
      ((gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 0,
        (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 1) := by
  rfl

/-- The post-accepted active marked input retains the selected duration,
the literal arrival-gap tail after the accepted request, and the literal
uninspected mark tail.  This is the raw data to which the further trip-time
shift is applied; it is not a separately sampled post-completion process. -/
noncomputable def gn21RawPostAcceptedMarkedInput
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> ((TripLength × (Nat -> Real)) × (Nat -> TripLength)) :=
  fun seed =>
    ((AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed,
      AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
        (gn21ArrivalClockIndex state) state sigma seed),
      AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed)

theorem measurable_gn21RawPostAcceptedMarkedInput
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostAcceptedMarkedInput state sigma) := by
  apply Measurable.prodMk
  · exact ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
      (AcceptedArrivalTime.measurable_gn21RawPostFirstAcceptedArrivalGapTail
        (gn21ArrivalClockIndex state) state sigma hsigma)
  · exact (AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)

/-- On the raw source, the selected accepted trip duration factors from the
complete literal marked renewal input after that request.  The proof combines
the stopped-mark tail factor with the post-request arrival-gap factor; it does
not call a restart or strong-Markov axiom. -/
theorem gn21RawPostAcceptedMarkedInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawPostAcceptedMarkedInput state sigma)
      (Measure.prod
        (Measure.prod (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))))
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let M := gn21CycleMarkLaw muI muJ state
  let Q := gn21AcceptedTripLaw M sigma
  let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let marks := AppliedModelingLib.Probability.IIDStream.measure M
  let history : (Nat -> TripLength) × (Nat -> Real) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun z =>
    (((AcceptedTripSelection.firstAcceptedIndex sigma z.1,
      AcceptedTripSelection.firstAcceptedTripMark sigma z.1),
      AcceptedTripSelection.firstAcceptedTripTail sigma z.1),
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2)
  let H := Measure.map history
    (marks.prod (AppliedModelingLib.Probability.IIDStream.measure
      (ProbabilityTheory.expMeasure rate)))
  let p : (((Nat × TripLength) × (Nat -> TripLength)) × Real) ->
      TripLength × (Nat -> TripLength) := fun h => (h.1.1.2, h.1.2)
  let source : GN21RawCycleSeed ->
      ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) :=
    AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory
      (gn21ArrivalClockIndex state) state sigma
  let selectedTail : GN21RawCycleSeed -> TripLength × (Nat -> TripLength) := fun seed =>
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed)
  have hrate : 0 < rate := by
    dsimp [rate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability M sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hrate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure rate)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hhistoryMeas : Measurable history := by
    change Measurable (fun z : (Nat -> TripLength) × (Nat -> Real) =>
      (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma z).1)
    exact measurable_fst.comp
      (AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma)
  letI : IsProbabilityMeasure H :=
    Measure.isProbabilityMeasure_map hhistoryMeas.aemeasurable
  have hsourceMeas : Measurable source := by
    exact AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalHistory
      (gn21ArrivalClockIndex state) state sigma hsigma
  have hhistory : HasLaw source (H.prod gaps) P := by
    simpa [source, H, history, P, M, rate, marks, gaps,
      AppliedModelingLib.Probability.IIDStream.measure] using
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalHistory_postArrivalGapTail_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        (gn21ArrivalClockIndex state) state sigma hsigma hmass)
  have hselectedTail : HasLaw selectedTail (Q.prod marks) P := by
    let indexMark : GN21RawCycleSeed -> (Nat × TripLength) × (Nat -> TripLength) := fun seed =>
      ((AcceptedTripSelection.gn21RawFirstAcceptedIndex state sigma seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed),
        AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed)
    let project : ((Nat × TripLength) × (Nat -> TripLength)) ->
        TripLength × (Nat -> TripLength) := fun z => (z.1.2, z.2)
    let K := Measure.map (fun path : Nat -> TripLength =>
      (AcceptedTripSelection.firstAcceptedIndex sigma path,
        AcceptedTripSelection.firstAcceptedTripMark sigma path)) marks
    have hindexPairMeas : Measurable (fun path : Nat -> TripLength =>
        (AcceptedTripSelection.firstAcceptedIndex sigma path,
          AcceptedTripSelection.firstAcceptedTripMark sigma path)) :=
      (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma)
    letI : IsProbabilityMeasure K :=
      Measure.isProbabilityMeasure_map hindexPairMeas.aemeasurable
    have hindexMarkMeas : Measurable indexMark :=
      (((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
        ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state))).prodMk
        ((AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state))
    have hindexMark : HasLaw indexMark (K.prod marks) P := by
      simpa [indexMark, K, P, M, marks,
        AppliedModelingLib.Probability.IIDStream.measure] using
        (AcceptedTripSelection.gn21RawFirstAcceptedIndexTripMarkTail_hasLaw
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
    have hselected : HasLaw (AcceptedTripSelection.firstAcceptedTripMark sigma) Q marks := by
      simpa [Q, M, marks] using
        (AcceptedTripSelection.firstAcceptedTripMark_hasLaw M sigma hsigma hmass)
    have hproject : Measurable project :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hprojectLaw : Measure.map project (K.prod marks) = Q.prod marks := by
      rw [show project = Prod.map (fun z : Nat × TripLength => z.2) id by rfl,
        ← Measure.map_prod_map K marks (measurable_snd) measurable_id,
        Measure.map_id]
      have hK : Measure.map (fun z : Nat × TripLength => z.2) K = Q := by
        change Measure.map (fun z : Nat × TripLength => z.2)
          (Measure.map (fun path : Nat -> TripLength =>
            (AcceptedTripSelection.firstAcceptedIndex sigma path,
              AcceptedTripSelection.firstAcceptedTripMark sigma path)) marks) = Q
        rw [Measure.map_map measurable_snd hindexPairMeas]
        simpa using hselected.map_eq
      rw [hK]
    have hselectedTailMeas : Measurable selectedTail :=
      ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
        ((AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state))
    refine ⟨hselectedTailMeas.aemeasurable, ?_⟩
    calc
      Measure.map selectedTail P = Measure.map (project ∘ indexMark) P := by rfl
      _ = Measure.map project (Measure.map indexMark P) := by
        rw [Measure.map_map hproject hindexMarkMeas]
      _ = Measure.map project (K.prod marks) := by rw [hindexMark.map_eq]
      _ = Q.prod marks := hprojectLaw
  have hp : Measurable p :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)
  have hpH : Measure.map p H = Q.prod marks := by
    calc
      Measure.map p H = Measure.map p (Measure.map Prod.fst (H.prod gaps)) := by
        simp
      _ = Measure.map (p ∘ Prod.fst) (H.prod gaps) := by
        rw [Measure.map_map hp measurable_fst]
      _ = Measure.map (p ∘ Prod.fst) (Measure.map source P) := by
        rw [hhistory.map_eq]
      _ = Measure.map ((p ∘ Prod.fst) ∘ source) P := by
        rw [Measure.map_map (hp.comp measurable_fst) hsourceMeas]
      _ = Measure.map selectedTail P := by rfl
      _ = Q.prod marks := hselectedTail.map_eq
  let observe : ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real)) ->
      (TripLength × (Nat -> TripLength)) × (Nat -> Real) := fun z => (p z.1, z.2)
  let reorder : ((TripLength × (Nat -> TripLength)) × (Nat -> Real)) ->
      (TripLength × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.1.1, z.2), z.1.2)
  have hobserve : Measurable observe :=
    (hp.comp measurable_fst).prodMk measurable_snd
  have hmapObserve : Measure.map observe (H.prod gaps) = (Q.prod marks).prod gaps := by
    rw [show observe = Prod.map p id by rfl,
      ← Measure.map_prod_map H gaps hp measurable_id, hpH, Measure.map_id]
  have hswap : MeasurePreserving
      (Prod.swap : (Nat -> TripLength) × (Nat -> Real) ->
        (Nat -> Real) × (Nat -> TripLength))
      (marks.prod gaps) (gaps.prod marks) :=
    Measure.measurePreserving_swap
  let passoc1 := measurePreserving_prodAssoc Q marks gaps
  let pswap := MeasurePreserving.prod (MeasurePreserving.id Q) hswap
  let passoc2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc Q gaps marks)
  have hmapReorder : Measure.map reorder ((Q.prod marks).prod gaps) = (Q.prod gaps).prod marks := by
    have hcomp : reorder = MeasurableEquiv.prodAssoc.symm ∘
        (Prod.map id Prod.swap) ∘ MeasurableEquiv.prodAssoc := by
      funext z
      rfl
    rw [hcomp]
    simpa [passoc1, pswap, passoc2] using
      (passoc2.comp (pswap.comp passoc1)).map_eq
  have hreorder : Measurable reorder :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hraw : Measurable (reorder ∘ observe) := hreorder.comp hobserve
  refine ⟨(measurable_gn21RawPostAcceptedMarkedInput state sigma hsigma).aemeasurable, ?_⟩
  calc
    Measure.map (gn21RawPostAcceptedMarkedInput state sigma) P =
        Measure.map (reorder ∘ observe) (Measure.map source P) := by
          rw [Measure.map_map hraw hsourceMeas]
          rfl
    _ = Measure.map (reorder ∘ observe) (H.prod gaps) := by rw [hhistory.map_eq]
    _ = Measure.map reorder (Measure.map observe (H.prod gaps)) := by
          symm
          exact Measure.map_map hreorder hobserve
    _ = Measure.map reorder ((Q.prod marks).prod gaps) := by rw [hmapObserve]
    _ = (Q.prod gaps).prod marks := hmapReorder

/-- On the literal raw source, the currently open state's marked arrival
residual at accepted-trip completion is obtained by first removing the
accepted request and then advancing that uninspected marked suffix through
the selected trip duration.  The equality is almost sure only because the
renewal paths are represented by total functions on their null exceptional
inputs; no arrival process is independently restarted. -/
theorem ae_gn21RawAcceptedCompletionMarkedArrivalResidual_current_eq_postAccepted
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed =
        AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun _ : Unit => AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
          (((), AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
              (gn21ArrivalClockIndex state) state sigma seed),
            AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clock := gn21ArrivalClockIndex state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let markLaw := gn21CycleMarkLaw muI muJ state
  let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let marks := AppliedModelingLib.Probability.IIDStream.measure markLaw
  let raw : GN21RawCycleSeed -> (Nat -> Real) × (Nat -> TripLength) := fun seed =>
    (AcceptedArrivalTime.rawClockStream clock seed,
      AcceptedArrivalTime.rawTripMarkStream state seed)
  have hrate : 0 < rate := by
    dsimp [rate, clock, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hraw : HasLaw raw (gaps.prod marks) P := by
    simpa [raw, gaps, marks, rate, clock, markLaw,
      AcceptedArrivalTime.rawClockStream, AcceptedArrivalTime.rawTripMarkStream,
      gn21RawCycleClock, gn21RawCycleMark,
      AppliedModelingLib.Probability.IIDStream.measure] using
      (gn21RawCycleClockStream_markStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state)
  have hprefixSource : ∀ᵐ paths ∂Measure.map raw P, ∀ n : Nat,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit =>
          AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix n paths.1)
        (((), paths.1), paths.2) =
      (AppliedModelingLib.Probability.PoissonProcess.futureInterarrival n paths.1,
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun _ : Unit => n) ((), paths.2)) := by
    rw [hraw.map_eq]
    simpa [gaps, marks] using
      (AppliedModelingLib.Probability.PoissonProcess.ae_externalTimeMarkedResidualTail_arrivalPrefix_eq_future
        markLaw hrate)
  have hprefix : ∀ᵐ seed ∂P, ∀ n : Nat,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit =>
          AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix n (raw seed).1)
        (((), (raw seed).1), (raw seed).2) =
      (AppliedModelingLib.Probability.PoissonProcess.futureInterarrival n (raw seed).1,
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun _ : Unit => n) ((), (raw seed).2)) :=
    Measure.tendsto_ae_map hraw.aemeasurable hprefixSource
  have hcycleSource : ∀ᵐ paths ∂Measure.map raw P, ∀ (s h : Real), 0 ≤ h →
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit => s + h) (((), paths.1), paths.2) =
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit => h)
          (((), AppliedModelingLib.Probability.PoissonProcess.residualTail s paths.1),
            AppliedModelingLib.Probability.IIDStream.externalIndexTail
              (fun _ : Unit =>
                AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount s paths.1)
              ((), paths.2)) := by
    rw [hraw.map_eq]
    simpa [gaps, marks] using
      (AppliedModelingLib.Probability.PoissonProcess.ae_externalTimeMarkedResidualTail_add_eq_comp_all
        markLaw hrate)
  have hcycle : ∀ᵐ seed ∂P, ∀ (s h : Real), 0 ≤ h →
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit => s + h) (((), (raw seed).1), (raw seed).2) =
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun _ : Unit => h)
          (((), AppliedModelingLib.Probability.PoissonProcess.residualTail s (raw seed).1),
            AppliedModelingLib.Probability.IIDStream.externalIndexTail
              (fun _ : Unit =>
                AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount s (raw seed).1)
              ((), (raw seed).2)) :=
    Measure.tendsto_ae_map hraw.aemeasurable hcycleSource
  let selectedLaw := gn21AcceptedTripLaw markLaw sigma
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability markLaw sigma hmass
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      selectedLaw P := by
    simpa [P, selectedLaw, markLaw] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ duration ∂selectedLaw, 0 ≤ duration := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hrawNonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hselectedNonneg
  filter_upwards [hprefix, hcycle, hrawNonneg] with seed hprefix hcycle hnonneg
  let n := AcceptedTripSelection.firstAcceptedIndex sigma
    (AcceptedArrivalTime.rawTripMarkStream state seed)
  let arrival := AppliedModelingLib.Probability.PoissonProcess.arrivalTime n (raw seed).1
  let duration := AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed
  have harrival : arrival =
      AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix (n + 1) (raw seed).1 := by
    simp [arrival, n, AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
      AppliedModelingLib.Probability.PoissonProcess.arrivalPrefix,
      Finset.sum_range_succ]
  have hfirst := hprefix (n + 1)
  have hcycleHere := hcycle arrival duration (by simpa [duration] using hnonneg)
  change AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun _ : GN21RawCycleSeed => arrival + duration) ((seed, (raw seed).1), (raw seed).2) = _
  change AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun _ : Unit => arrival + duration) (((), (raw seed).1), (raw seed).2) = _
  rw [hcycleHere]
  have hresidual :
      AppliedModelingLib.Probability.PoissonProcess.residualTail arrival (raw seed).1 =
        AppliedModelingLib.Probability.PoissonProcess.futureInterarrival (n + 1) (raw seed).1 := by
    exact congrArg Prod.fst (harrival ▸ hfirst)
  have hmarks :
      AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun _ : Unit =>
            AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount arrival (raw seed).1)
          ((), (raw seed).2) =
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun _ : Unit => n + 1) ((), (raw seed).2) := by
    exact congrArg Prod.snd (harrival ▸ hfirst)
  rw [hresidual, hmarks]
  have hpostGaps :
      AppliedModelingLib.Probability.PoissonProcess.futureInterarrival (n + 1) (raw seed).1 =
        AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
          (gn21ArrivalClockIndex state) state sigma seed := by
    funext k
    simp [n, raw, clock, AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail,
      AppliedModelingLib.Probability.PoissonProcess.futureInterarrival,
      AppliedModelingLib.Probability.PoissonProcess.interarrival,
      Nat.add_assoc]
  have hn : n = AppliedModelingLib.Probability.IIDStream.firstHit sigma
      (fun q => gn21RawCycleMark state q seed) := by
    rw [show n = AcceptedTripSelection.firstAcceptedIndex sigma
      (AcceptedArrivalTime.rawTripMarkStream state seed) by rfl,
      AcceptedTripSelection.firstAcceptedIndex_eq_firstHit]
    rfl
  have hpostMarks :
      AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun _ : Unit => n + 1) ((), (raw seed).2) =
        AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed := by
    funext k
    dsimp [raw]
    change AppliedModelingLib.Probability.IIDStream.externalIndexTail
        (fun _ : Unit => n + 1) ((), fun q => gn21RawCycleMark state q seed) k =
      AppliedModelingLib.Probability.IIDStream.postFirstHitTail sigma
        (fun q => gn21RawCycleMark state q seed) k
    rw [hn]
    simp [
      AppliedModelingLib.Probability.IIDStream.postFirstHitTail,
      AppliedModelingLib.Probability.IIDStream.externalIndexTail,
      AppliedModelingLib.Probability.IIDStream.coordinate,
      Nat.add_assoc]
  rw [hpostGaps, hpostMarks]

/-- The current open state's literal marked arrival input at accepted-trip
completion has its original source law.  Its proof uses the selected-duration
and post-request-tail factorization together with a marked renewal residual
at that duration; the `max` totalization is removed on the source-a.s.
positive-duration carrier supplied by the paper's policy domain. -/
theorem gn21RawAcceptedCompletionMarkedArrivalResidual_current_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state)
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let M := gn21CycleMarkLaw muI muJ state
  let Q := gn21AcceptedTripLaw M sigma
  let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let marks := AppliedModelingLib.Probability.IIDStream.measure M
  have hrate : 0 < rate := by
    dsimp [rate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability M sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hpost : HasLaw (gn21RawPostAcceptedMarkedInput state sigma)
      ((Q.prod gaps).prod marks) P := by
    simpa [P, Q, M, rate, gaps, marks] using
      (gn21RawPostAcceptedMarkedInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have htime : Measurable (fun duration : TripLength => max 0 duration) :=
    measurable_const.max measurable_id
  have hgeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_hasLaw
      Q M hrate (fun duration : TripLength => max 0 duration) htime
      (fun duration => le_max_left 0 duration)
  have hmax : HasLaw (fun seed =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun duration : TripLength => max 0 duration)
        (gn21RawPostAcceptedMarkedInput state sigma seed))
      (gaps.prod marks) P := by
    exact hgeneric.comp hpost
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      Q P := by
    simpa [P, Q, M] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hnonnegQ : ∀ᵐ duration ∂Q, 0 ≤ duration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hnonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hnonnegQ
  have hcurrent :=
    ae_gn21RawAcceptedCompletionMarkedArrivalResidual_current_eq_postAccepted
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
      state sigma hsigma hsigma_subset hmass
  refine hmax.congr ?_
  filter_upwards [hcurrent, hnonneg] with seed hcurrent hnonneg
  calc
    gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed =
        AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun _ : Unit => AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
          (((), AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
              (gn21ArrivalClockIndex state) state sigma seed),
            AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed) := hcurrent
    _ = AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun duration : TripLength => max 0 duration)
          (gn21RawPostAcceptedMarkedInput state sigma seed) := by
      unfold AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      apply Prod.ext
      · simp [gn21RawPostAcceptedMarkedInput,
          AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail,
          max_eq_right hnonneg]
      · funext n
        simp [gn21RawPostAcceptedMarkedInput,
          AppliedModelingLib.Probability.IIDStream.externalIndexTail,
          max_eq_right hnonneg]

/-- The accepted-trip completion clock as an observable of the complete
switch/current-arrival external coordinate.  The `max` only totalizes the
null exceptional inputs on which a raw renewal path has a negative gap; the
following source-a.e. comparison returns it to the literal calendar clock. -/
noncomputable def gn21AcceptedCompletionExternalTime
    (state : Fin 2) (sigma : TripPolicy) : GN21SwitchFirstExternalSeed -> Real :=
  fun source => max 0
    (AppliedModelingLib.Probability.PoissonProcess.arrivalTime
      (AcceptedTripSelection.firstAcceptedIndex sigma source.2) source.1.2 +
      AcceptedTripSelection.firstAcceptedTripMark sigma source.2)

theorem measurable_gn21AcceptedCompletionExternalTime
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21AcceptedCompletionExternalTime state sigma) := by
  let historyInput : GN21SwitchFirstExternalSeed ->
      (Nat -> TripLength) × (Nat -> Real) := fun source => (source.2, source.1.2)
  have hhistoryInput : Measurable historyInput := by
    exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hhistory := (AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams
    sigma hsigma).comp hhistoryInput
  have harrival : Measurable (fun source : GN21SwitchFirstExternalSeed =>
      (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
        (historyInput source)).1.2) :=
    measurable_snd.comp (measurable_fst.comp hhistory)
  have hmark : Measurable (fun source : GN21SwitchFirstExternalSeed =>
      AcceptedTripSelection.firstAcceptedTripMark sigma source.2) :=
    (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      measurable_snd
  simpa [gn21AcceptedCompletionExternalTime, historyInput,
    AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using
    measurable_const.max (harrival.add hmark)

theorem gn21AcceptedCompletionExternalTime_nonnegative
    (state : Fin 2) (sigma : TripPolicy) (source : GN21SwitchFirstExternalSeed) :
    0 ≤ gn21AcceptedCompletionExternalTime state sigma source := by
  exact le_max_left _ _

/-- Keep the whole external completion coordinate jointly with the incoming
state's literal marked arrival residual.  The source product law means that
the latter can be advanced through the actual accepted-trip completion clock
without independently restarting either marked arrival stream. -/
noncomputable def gn21RawAcceptedCompletionIncomingResidualWithExternal
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed ->
      GN21SwitchFirstExternalSeed × ((Nat -> Real) × (Nat -> TripLength)) :=
  fun seed =>
    (gn21RawSwitchFirstExternalSeed state seed,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (gn21AcceptedCompletionExternalTime state sigma)
        (gn21RawSwitchFirstIncomingArrivalInput state seed))

theorem measurable_gn21RawAcceptedCompletionIncomingResidualWithExternal
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma) := by
  exact (measurable_gn21RawSwitchFirstExternalSeed state).prodMk
    ((AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (gn21AcceptedCompletionExternalTime state sigma)
      (measurable_gn21AcceptedCompletionExternalTime state sigma hsigma)).comp
      (measurable_gn21RawSwitchFirstIncomingArrivalInput state))

/-- The external completion coordinate and the literal incoming marked
arrival residual have their exact source product law.  This retains all
switch/current-arrival information on which the completion time depends. -/
theorem gn21RawAcceptedCompletionIncomingResidualWithExternal_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    HasLaw (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma)
      (((((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchJI)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state)))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))).prod
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let externalLaw : Measure GN21SwitchFirstExternalSeed :=
    (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchJI)).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state)))).prod
      (AppliedModelingLib.Probability.IIDStream.measure
        (gn21CycleMarkLaw muI muJ state))
  let incomingRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))
  let incomingGaps :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure incomingRate
  let incomingBaseMarkLaw :=
    (gn21CycleMarkLaw muI muJ
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))
  let incomingMarkLaw := AppliedModelingLib.Probability.IIDStream.measure incomingBaseMarkLaw
  have hcurrentRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state) := by
    dsimp [gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hincomingRate : 0 < incomingRate := by
    dsimp [incomingRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state))) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hcurrentRate
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure incomingBaseMarkLaw := by
    dsimp [incomingBaseMarkLaw]
    infer_instance
  letI : IsProbabilityMeasure externalLaw := by
    dsimp [externalLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hinput : HasLaw (gn21RawSwitchFirstIncomingArrivalInput state)
      ((externalLaw.prod incomingGaps).prod incomingMarkLaw) P := by
    simpa [P, externalLaw, incomingRate, incomingGaps, incomingBaseMarkLaw,
      incomingMarkLaw] using
      (gn21RawSwitchFirstIncomingArrivalInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hgeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_joint_hasLaw
      externalLaw incomingBaseMarkLaw hincomingRate
      (gn21AcceptedCompletionExternalTime state sigma)
      (measurable_gn21AcceptedCompletionExternalTime state sigma hsigma)
      (gn21AcceptedCompletionExternalTime_nonnegative state sigma)
      id measurable_id
  have hcomposed := hgeneric.comp hinput
  change HasLaw (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma)
    (externalLaw.prod (incomingGaps.prod incomingMarkLaw)) P
  simpa [gn21RawAcceptedCompletionIncomingResidualWithExternal] using hcomposed

/-- The incoming factor above is the literal incoming marked-arrival
residual at the actual accepted-trip completion time, almost surely.  The
comparison removes only the totalization on the raw renewal null set. -/
theorem ae_gn21RawAcceptedCompletionIncomingResidualWithExternal_snd_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma seed).2 =
        gn21RawAcceptedCompletionMarkedArrivalResidual state sigma
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let Q := gn21AcceptedTripLaw M sigma
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability M sigma hmass
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      Q P := by
    simpa [P, Q, M] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonnegQ : ∀ᵐ duration ∂Q, 0 ≤ duration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hselectedNonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hselectedNonnegQ
  have harrivalNonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
        (gn21ArrivalClockIndex state) state sigma seed := by
    simpa [P] using (AcceptedArrivalTime.ae_gn21RawFirstAcceptedArrivalTime_nonnegative
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
      (gn21ArrivalClockIndex state) state sigma)
  filter_upwards [harrivalNonneg, hselectedNonneg] with seed harrival hselected
  have hcompletion : 0 ≤ gn21RawAcceptedCalendarCompletionTime state sigma seed := by
    simpa [gn21RawAcceptedCalendarCompletionTime, gn21RawPostThinningRaceSeed] using
      add_nonneg harrival hselected
  have hcompletion' : 0 ≤
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma
            (AcceptedArrivalTime.rawTripMarkStream state seed))
          (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed) +
        AcceptedTripSelection.firstAcceptedTripMark sigma
          (AcceptedArrivalTime.rawTripMarkStream state seed) := by
    simpa [gn21RawAcceptedCalendarCompletionTime, gn21RawPostThinningRaceSeed,
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark] using hcompletion
  have hmax := max_eq_right hcompletion'
  have hmarkStream : (fun n => gn21RawCycleMark state n seed) =
      AcceptedArrivalTime.rawTripMarkStream state seed := by
    rfl
  unfold gn21RawAcceptedCompletionIncomingResidualWithExternal
  unfold gn21RawAcceptedCompletionMarkedArrivalResidual
  unfold AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
  apply Prod.ext
  · simp [gn21AcceptedCompletionExternalTime,
      gn21RawAcceptedCalendarCompletionTime, gn21RawPostThinningRaceSeed,
      gn21RawSwitchFirstIncomingArrivalInput, gn21RawSwitchFirstExternalSeed,
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail,
      hmax, hmarkStream]
  · funext n
    simp [gn21AcceptedCompletionExternalTime,
      gn21RawAcceptedCalendarCompletionTime, gn21RawPostThinningRaceSeed,
      gn21RawSwitchFirstIncomingArrivalInput, gn21RawSwitchFirstExternalSeed,
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
      AppliedModelingLib.Probability.IIDStream.externalIndexTail,
      hmax, hmarkStream]

/-- All source coordinates needed for an accepted-trip continuation: the
literal switch pair, the complete stopped active-arrival history (including
its post-request gap tail), and the untouched incoming marked arrival input.
This is a deterministic projection of one raw seed. -/
abbrev GN21AcceptedCompletionHistoryInput :=
  ((((Nat -> Real) × (Nat -> Real)) ×
    ((((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real))) ×
      ((Nat -> Real) × (Nat -> TripLength)))

noncomputable def gn21RawAcceptedCompletionHistoryInput
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedCompletionHistoryInput := fun seed =>
  ((RawTwoStateCTMC.rawSwitchGapPair seed,
    AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
      (AcceptedArrivalTime.rawTripMarkStream state seed,
        AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed)),
    (AcceptedArrivalTime.rawClockStream
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) seed,
      AcceptedArrivalTime.rawTripMarkStream
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed))

theorem measurable_gn21RawAcceptedCompletionHistoryInput
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedCompletionHistoryInput state sigma) := by
  exact (RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
    ((AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma).comp
      ((AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
        (AcceptedArrivalTime.measurable_rawClockStream
          (gn21ArrivalClockIndex state))))).prodMk
    ((AcceptedArrivalTime.measurable_rawClockStream
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))

/-- The accepted-completion history input has the exact raw source product
law.  In particular, the stopped active history factors from both literal
switch streams and the untouched incoming marked arrival input.  This is the
joint factorization required before residualizing both arrival streams at the
same completion clock. -/
theorem gn21RawAcceptedCompletionHistoryInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    HasLaw (gn21RawAcceptedCompletionHistoryInput state sigma)
      ((((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchJI)).prod
        ((Measure.map (fun z : (Nat -> TripLength) × (Nat -> Real) =>
            (((AcceptedTripSelection.firstAcceptedIndex sigma z.1,
              AcceptedTripSelection.firstAcceptedTripMark sigma z.1),
              AcceptedTripSelection.firstAcceptedTripTail sigma z.1),
              AppliedModelingLib.Probability.PoissonProcess.arrivalTime
                (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2))
            ((AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ state)).prod
              (AppliedModelingLib.Probability.IIDStream.measure
                (ProbabilityTheory.expMeasure
                  (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                    (gn21ArrivalClockIndex state)))))).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))).prod
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let activeGaps :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let activeMarkLaw := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ state)
  let incomingRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex other)
  let incomingGaps :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure incomingRate
  let incomingMarkLaw := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let prefixHistory : (Nat -> TripLength) × (Nat -> Real) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun z =>
    (((AcceptedTripSelection.firstAcceptedIndex sigma z.1,
      AcceptedTripSelection.firstAcceptedTripMark sigma z.1),
      AcceptedTripSelection.firstAcceptedTripTail sigma z.1),
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2)
  let activeHistoryLaw := (Measure.map prefixHistory
    (activeMarkLaw.prod (AppliedModelingLib.Probability.IIDStream.measure
      (ProbabilityTheory.expMeasure activeRate)))).prod activeGaps
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hincomingRate : 0 < incomingRate := by
    dsimp [incomingRate, other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
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
  letI : IsProbabilityMeasure activeGaps := by
    dsimp [activeGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure activeMarkLaw := by
    dsimp [activeMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure activeRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hactiveRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure activeRate)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hinput : HasLaw (gn21RawSwitchFirstIncomingArrivalInput state)
      ((((switchLaw.prod activeGaps).prod activeMarkLaw).prod incomingGaps).prod
        incomingMarkLaw) P := by
    simpa [P, switchLaw, activeRate, activeGaps, activeMarkLaw,
      incomingRate, incomingGaps, incomingMarkLaw, other] using
      (gn21RawSwitchFirstIncomingArrivalInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  let source := ((((switchLaw.prod activeGaps).prod activeMarkLaw).prod incomingGaps).prod
    incomingMarkLaw)
  let reordered := (switchLaw.prod (activeMarkLaw.prod activeGaps)).prod
    (incomingGaps.prod incomingMarkLaw)
  let reorder : (GN21SwitchFirstExternalSeed × (Nat -> Real)) × (Nat -> TripLength) ->
      (((Nat -> Real) × (Nat -> Real)) × ((Nat -> TripLength) × (Nat -> Real))) ×
        ((Nat -> Real) × (Nat -> TripLength)) := fun z =>
    ((z.1.1.1.1, (z.1.1.2, z.1.1.1.2)), (z.1.2, z.2))
  let p1 := measurePreserving_prodAssoc
    ((switchLaw.prod activeGaps).prod activeMarkLaw) incomingGaps incomingMarkLaw
  let p2 := MeasurePreserving.prod
    (measurePreserving_prodAssoc switchLaw activeGaps activeMarkLaw)
    (MeasurePreserving.id (incomingGaps.prod incomingMarkLaw))
  let swapAM : MeasurePreserving
      (Prod.swap : (Nat -> Real) × (Nat -> TripLength) ->
        (Nat -> TripLength) × (Nat -> Real))
      (activeGaps.prod activeMarkLaw) (activeMarkLaw.prod activeGaps) := by
    exact ⟨measurable_swap, Measure.prod_swap⟩
  let p3 := MeasurePreserving.prod
    (MeasurePreserving.prod (MeasurePreserving.id switchLaw) swapAM)
    (MeasurePreserving.id (incomingGaps.prod incomingMarkLaw))
  have hreorder : MeasurePreserving reorder source reordered := by
    simpa [reorder, source, reordered] using (p3.comp (p2.comp p1))
  let history := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
  have hhistory : Measurable history :=
    AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  have hhistoryLaw : Measure.map history (activeMarkLaw.prod activeGaps) = activeHistoryLaw := by
    simpa [history, activeHistoryLaw, prefixHistory, activeMarkLaw, activeGaps,
      activeRate, AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams_hasLaw_prod
        (gn21CycleMarkLaw muI muJ state) hactiveRate sigma hsigma).map_eq
  let transform :
      (((Nat -> Real) × (Nat -> Real)) × ((Nat -> TripLength) × (Nat -> Real))) ×
          ((Nat -> Real) × (Nat -> TripLength)) -> GN21AcceptedCompletionHistoryInput := fun z =>
    ((z.1.1, history z.1.2), z.2)
  have htransform : Measurable transform := by
    exact ((measurable_fst.comp measurable_fst).prodMk
      (hhistory.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have htransformLaw : Measure.map transform reordered =
      (switchLaw.prod activeHistoryLaw).prod (incomingGaps.prod incomingMarkLaw) := by
    calc
      Measure.map transform reordered =
          (Measure.map (Prod.map id history) (switchLaw.prod (activeMarkLaw.prod activeGaps))).prod
            (incomingGaps.prod incomingMarkLaw) := by
              rw [show transform = Prod.map (Prod.map id history) id by rfl,
                ← Measure.map_prod_map (switchLaw.prod (activeMarkLaw.prod activeGaps))
                  (incomingGaps.prod incomingMarkLaw)
                  (measurable_id.prodMap hhistory) measurable_id,
                Measure.map_id]
      _ = (switchLaw.prod activeHistoryLaw).prod (incomingGaps.prod incomingMarkLaw) := by
        rw [← Measure.map_prod_map switchLaw (activeMarkLaw.prod activeGaps)
          measurable_id hhistory, Measure.map_id, hhistoryLaw]
  have htrans : HasLaw transform
      ((switchLaw.prod activeHistoryLaw).prod (incomingGaps.prod incomingMarkLaw)) reordered :=
    ⟨htransform.aemeasurable, htransformLaw⟩
  have hfinal := htrans.comp (hreorder.hasLaw.comp hinput)
  change HasLaw (gn21RawAcceptedCompletionHistoryInput state sigma)
    ((switchLaw.prod activeHistoryLaw).prod (incomingGaps.prod incomingMarkLaw)) P
  simpa [transform, reorder,
    gn21RawAcceptedCompletionHistoryInput,
    gn21RawSwitchFirstIncomingArrivalInput, gn21RawSwitchFirstExternalSeed,
    history] using hfinal

/-- The departing state's next arrival stream on a switch-first branch is
the literal marked-renewal residual obtained from the current source seed. -/
theorem gn21RawSwitchFirstNextCycleSeed_departing_arrival
    (state : Fin 2) (seed : GN21RawCycleSeed) :
    (gn21RawSwitchFirstNextCycleSeed state seed).1 (gn21ArrivalClockIndex state) =
      (gn21RawSwitchFirstJointContinuation state seed).1.1 := by
  fin_cases state <;> rfl

/-- The departing state's next mark stream on a switch-first branch is the
literal uninspected marked suffix, paired with its residual gap stream. -/
theorem gn21RawSwitchFirstNextCycleSeed_departing_marks
    (state : Fin 2) (seed : GN21RawCycleSeed) :
    (gn21RawSwitchFirstNextCycleSeed state seed).2 state =
      (gn21RawSwitchFirstJointContinuation state seed).1.2 := by
  fin_cases state <;> rfl

/-- The incoming state's next arrival stream on a switch-first branch is its
literal renewal residual at the very same switch time. -/
theorem gn21RawSwitchFirstNextCycleSeed_incoming_arrival
    (state : Fin 2) (seed : GN21RawCycleSeed) :
    (gn21RawSwitchFirstNextCycleSeed state seed).1
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) =
      (gn21RawSwitchFirstJointContinuation state seed).2.2.1 := by
  fin_cases state <;> rfl

/-- The incoming state's next mark stream on a switch-first branch is its
literal marked suffix at that switch time. -/
theorem gn21RawSwitchFirstNextCycleSeed_incoming_marks
    (state : Fin 2) (seed : GN21RawCycleSeed) :
    (gn21RawSwitchFirstNextCycleSeed state seed).2
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) =
      (gn21RawSwitchFirstJointContinuation state seed).2.2.2 := by
  fin_cases state <;> rfl

/-- The two switch clocks in the next switch-first seed are exactly the
surviving literal state-indexed switch tails. -/
theorem gn21RawSwitchFirstNextCycleSeed_switch_gaps
    (state : Fin 2) (seed : GN21RawCycleSeed) :
    ((gn21RawSwitchFirstNextCycleSeed state seed).1 2,
      (gn21RawSwitchFirstNextCycleSeed state seed).1 3) =
      (gn21RawSwitchFirstJointContinuation state seed).2.1 := by
  fin_cases state <;> rfl

/-- The ordinary raw source viewed in the coordinate order used by the
switch-first continuation: departing marked arrivals, both switch streams,
then incoming marked arrivals.  This is a projection of one raw seed. -/
def gn21RawCycleSeedStateContinuationInput (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstJointContinuation := fun seed =>
  ((seed.1 (gn21ArrivalClockIndex state), seed.2 state),
    ((seed.1 2, seed.1 3),
      (seed.1 (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)),
        seed.2 (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))

theorem measurable_gn21RawCycleSeedStateContinuationInput (state : Fin 2) :
    Measurable (gn21RawCycleSeedStateContinuationInput state) := by
  exact
    ((AcceptedArrivalTime.measurable_rawClockStream (gn21ArrivalClockIndex state)).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
      (RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
        ((AcceptedArrivalTime.measurable_rawClockStream
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))).prodMk
          (AcceptedArrivalTime.measurable_rawTripMarkStream
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))

/-- Reassembly is literally inverse to this state-ordered raw projection. -/
theorem gn21RawCycleSeedOfStateContinuation_comp_input (state : Fin 2) :
    gn21RawCycleSeedOfStateContinuation state ∘
        gn21RawCycleSeedStateContinuationInput state = id := by
  funext seed
  fin_cases state
  · apply Prod.ext
    · funext clock
      fin_cases clock <;> rfl
    · funext s
      fin_cases s <;> rfl
  · apply Prod.ext
    · funext clock
      fin_cases clock <;> rfl
    · funext s
      fin_cases s <;> rfl

/-- Product law of a raw seed written in state-continuation order. -/
def gn21StateContinuationMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) (state : Fin 2) :
    Measure GN21SwitchFirstJointContinuation :=
  ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
        (gn21ArrivalClockIndex state))).prod
    (AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state))).prod
    (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchJI)).prod
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))

/-- The unnormalized literal no-hit mass retained by a switch-first
continuation.  It is deliberately a source event mass, rather than a new
transition or regeneration assumption. -/
def gn21SwitchFirstNoHitMass
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (state : Fin 2) (sigma : TripPolicy) : ENNReal :=
  ((Measure.map
      (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
        (fun t : Real => max 0 t))
      ((if state = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))))).prod
      (AppliedModelingLib.Probability.IIDStream.measure
        (gn21CycleMarkLaw muI muJ state))
      (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
        (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma))

/-- The state-ordered raw coordinate projection has exactly the product law
of its two marked arrival streams and two switch streams. -/
theorem gn21RawCycleSeedStateContinuationInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (gn21RawCycleSeedStateContinuationInput state)
      (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state))).prod
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchJI)).prod
          ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
            (AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let W := (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let B := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
  let N := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))
  let input := gn21RawSwitchFirstIncomingArrivalInput state
  let reorder : (GN21SwitchFirstExternalSeed × (Nat -> Real)) × (Nat -> TripLength) ->
      GN21SwitchFirstJointContinuation := fun z =>
    ((z.1.1.1.2, z.1.1.2), (z.1.1.1.1, (z.1.2, z.2)))
  let source := (((W.prod A).prod M).prod B).prod N
  let target := (A.prod M).prod (W.prod (B.prod N))
  have hrate : ∀ clock : Fin 4,
      0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    intro clock
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate _)
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate _)
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hsource : HasLaw input source P := by
    simpa [input, source, W, A, M, B, N, P] using
      (gn21RawSwitchFirstIncomingArrivalInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  let p0 := measurePreserving_prodAssoc ((W.prod A).prod M) B N
  let p1 := MeasurePreserving.prod (measurePreserving_prodAssoc W A M)
    (MeasurePreserving.id (B.prod N))
  let swapWM : MeasurePreserving
      (Prod.map Prod.swap id :
        (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength))) ×
            ((Nat -> Real) × (Nat -> TripLength)) ->
          (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> Real))) ×
            ((Nat -> Real) × (Nat -> TripLength)))
      ((W.prod (A.prod M)).prod (B.prod N))
      (((A.prod M).prod W).prod (B.prod N)) := by
    refine ⟨measurable_swap.prodMap measurable_id, ?_⟩
    rw [← Measure.map_prod_map (W.prod (A.prod M)) (B.prod N)
      measurable_swap measurable_id, Measure.prod_swap, Measure.map_id]
  let p3 := measurePreserving_prodAssoc (A.prod M) W (B.prod N)
  have hreorder : MeasurePreserving reorder source target := by
    simpa [reorder, source, target] using (p3.comp (swapWM.comp (p1.comp p0)))
  have hfinal := hreorder.hasLaw.comp hsource
  change HasLaw (gn21RawCycleSeedStateContinuationInput state) target P
  refine hfinal.congr ?_
  filter_upwards [] with seed
  rfl

/-- Reassembling a continuation-order source product returns exactly the raw
GN seed law.  Together with the pathwise inverse above, this is the law-level
statement that no independent proposal seed is introduced by reassembly. -/
theorem map_gn21RawCycleSeedOfStateContinuation
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    Measure.map (gn21RawCycleSeedOfStateContinuation state)
      (gn21StateContinuationMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state) =
      gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let input := gn21RawCycleSeedStateContinuationInput state
  let continuation := gn21StateContinuationMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI state
  have hinput : HasLaw input continuation P := by
    simpa [input, continuation, gn21StateContinuationMeasure] using
      (gn21RawCycleSeedStateContinuationInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  calc
    Measure.map (gn21RawCycleSeedOfStateContinuation state) continuation =
        Measure.map (gn21RawCycleSeedOfStateContinuation state) (Measure.map input P) := by
          rw [hinput.map_eq]
    _ = Measure.map (gn21RawCycleSeedOfStateContinuation state ∘ input) P := by
          rw [Measure.map_map (measurable_gn21RawCycleSeedOfStateContinuation state)
            (measurable_gn21RawCycleSeedStateContinuationInput state)]
    _ = Measure.map id P := by
          rw [gn21RawCycleSeedOfStateContinuation_comp_input]
    _ = P := Measure.map_id

/-- On the literal totalized switch-first carrier, the reassembled next raw
seed has the original raw-seed law scaled only by the actual no-hit source
mass.  This turns the earlier joint continuation kernel into an iterable
source transition without resampling a proposal seed. -/
theorem map_gn21RawSwitchFirstNextCycleSeed_restrict_noHit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measure.map (gn21RawSwitchFirstNextCycleSeed state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawSwitchFirstJointNoHit state sigma)) =
      (gn21SwitchFirstNoHitMass muI muJ arrivalI arrivalJ switchIJ switchJI state sigma) •
        gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let continuation := gn21StateContinuationMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI state
  let mass := gn21SwitchFirstNoHitMass
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  rw [gn21RawSwitchFirstNextCycleSeed, ← Measure.map_map
    (measurable_gn21RawCycleSeedOfStateContinuation state)
    (measurable_gn21RawSwitchFirstJointContinuation state)]
  rw [map_gn21RawSwitchFirstJointContinuation_restrict_noHit
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma]
  rw [Measure.map_smul]
  simpa [P, continuation, mass, gn21StateContinuationMeasure,
    gn21SwitchFirstNoHitMass] using
    congrArg (fun m : Measure GN21RawCycleSeed => mass • m)
      (map_gn21RawCycleSeedOfStateContinuation
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)

/-- The totalized switch-first branch carries its literal active holding time
jointly with a fresh reassembled raw seed.  This is an event-restricted
product law, not a conditional resampling statement. -/
theorem map_gn21RawSwitchFirstHeadAndNextCycleSeed_restrict_noHit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measure.map (gn21RawSwitchFirstHeadAndNextCycleSeed state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawSwitchFirstJointNoHit state sigma)) =
      (gn21SwitchFirstHeadHistoryMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let tailLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let headLaw : Measure Real := if state = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let departingArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let departingMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let incomingArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex other))
  let incomingMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingArrivalLaw.prod incomingMarkLaw
  let companionLaw := tailLaw.prod incomingLaw
  let sourceLaw := ((headLaw.prod companionLaw).prod departingArrivalLaw).prod departingMarkLaw
  let time : Real -> Real := fun t => max 0 t
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory time
  let index : Real × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let A := AppliedModelingLib.Probability.IIDStream.externalIndexNoHit index sigma
  let carrier : Set GN21SwitchFirstJointContinuationInput :=
    {z | (history (z.1.1.1, z.1.2), z.2) ∈ A}
  let input : GN21RawCycleSeed -> GN21SwitchFirstJointContinuationInput :=
    gn21RawSwitchFirstJointContinuationInput state
  let sourceOutput : GN21SwitchFirstJointContinuationInput ->
      (Real × (Nat × (Nat -> Real))) ×
        GN21SwitchFirstMarkedTailWithCompanion := fun z =>
    let h := history (z.1.1.1, z.1.2)
    (h,
      ((AppliedModelingLib.Probability.IIDStream.externalIndexTail index (h, z.2),
        AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail time
          (z.1.1.1, z.1.2)), z.1.1.2))
  let continuation : GN21SwitchFirstMarkedTailWithCompanion ->
      GN21SwitchFirstJointContinuation := fun z => ((z.1.2, z.1.1), z.2)
  let tailSeed : GN21SwitchFirstMarkedTailWithCompanion ->
      GN21RawCycleSeed := gn21RawCycleSeedOfStateContinuation state ∘ continuation
  let project : (Real × (Nat × (Nat -> Real))) ×
      GN21SwitchFirstMarkedTailWithCompanion ->
      Real × GN21RawCycleSeed := fun z => (z.1.1, tailSeed z.2)
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure tailLaw := by dsimp [tailLaw]; infer_instance
  letI : IsProbabilityMeasure headLaw := by
    dsimp [headLaw]
    split
    · exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchIJ
    · exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchJI
  letI : IsProbabilityMeasure departingArrivalLaw := by
    dsimp [departingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex state))
  letI : IsProbabilityMeasure departingMarkLaw := by
    dsimp [departingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingArrivalLaw := by
    dsimp [incomingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex other))
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by dsimp [incomingLaw]; infer_instance
  letI : IsProbabilityMeasure companionLaw := by dsimp [companionLaw]; infer_instance
  have hinputLaw : HasLaw input sourceLaw P := by
    simpa [input, sourceLaw, companionLaw, incomingLaw, incomingArrivalLaw,
      incomingMarkLaw, tailLaw, headLaw, departingArrivalLaw, departingMarkLaw,
      clockRate, other, P] using
      (gn21RawSwitchFirstJointContinuationInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hinput : Measurable input := measurable_gn21RawSwitchFirstJointContinuationInput state
  have htime : Measurable time := measurable_const.max measurable_id
  have hhistory : Measurable history := by
    simpa [history] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimePastHistory time htime)
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have htail : Measurable (AppliedModelingLib.Probability.IIDStream.externalIndexTail
      (α := TripLength) index) :=
    AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail index hindex
  have hresidual : Measurable
      (AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail time) :=
    AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeResidualTail time htime
  have hsourceOutput : Measurable sourceOutput := by
    exact
      ((hhistory.comp
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst))).prodMk
        (((htail.comp
          ((hhistory.comp
            ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
              (measurable_snd.comp measurable_fst))).prodMk measurable_snd)).prodMk
          (hresidual.comp
            ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
              (measurable_snd.comp measurable_fst)))).prodMk
          (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  have hA : AppliedModelingLib.Probability.IIDStream.ExternalIndexPrefixEvent index A :=
    AppliedModelingLib.Probability.IIDStream.externalIndexNoHit_prefixEvent index sigma hsigma
  have hcarrier : MeasurableSet carrier := by
    exact (AppliedModelingLib.Probability.IIDStream.measurableSet_externalIndexPrefixEvent
      index hindex A hA).preimage
        ((hhistory.comp
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  have hcontinuation : Measurable continuation :=
    ((measurable_snd.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd
  have htailSeed : Measurable tailSeed :=
    (measurable_gn21RawCycleSeedOfStateContinuation state).comp hcontinuation
  have hproject : Measurable project :=
    (measurable_fst.comp measurable_fst).prodMk (htailSeed.comp measurable_snd)
  let tailLawOut : Measure GN21SwitchFirstMarkedTailWithCompanion :=
    (departingMarkLaw.prod departingArrivalLaw).prod companionLaw
  let continuationLaw := gn21StateContinuationMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI state
  have hcontinuationLaw : Measure.map continuation tailLawOut = continuationLaw := by
    change Measure.map (Prod.map Prod.swap id)
      ((departingMarkLaw.prod departingArrivalLaw).prod companionLaw) = continuationLaw
    rw [← Measure.map_prod_map (departingMarkLaw.prod departingArrivalLaw) companionLaw
      measurable_swap measurable_id, Measure.prod_swap, Measure.map_id]
    rfl
  have htailSeedLaw : Measure.map tailSeed tailLawOut = P := by
    change Measure.map (gn21RawCycleSeedOfStateContinuation state ∘ continuation) tailLawOut = P
    calc
      Measure.map (gn21RawCycleSeedOfStateContinuation state ∘ continuation) tailLawOut =
          Measure.map (gn21RawCycleSeedOfStateContinuation state)
            (Measure.map continuation tailLawOut) := by
              rw [Measure.map_map
                (measurable_gn21RawCycleSeedOfStateContinuation state) hcontinuation]
      _ = Measure.map (gn21RawCycleSeedOfStateContinuation state) continuationLaw := by
            rw [hcontinuationLaw]
      _ = P := by
            simpa [continuationLaw, P] using
              (map_gn21RawCycleSeedOfStateContinuation
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hfactor :=
    AppliedModelingLib.Probability.PoissonProcess.map_externalTimeMarkedResidualTail_withPastHistoryAndCompanion_restrict_eq_prod
      headLaw companionLaw (gn21CycleMarkLaw muI muJ state)
      (hrate (gn21ArrivalClockIndex state)) time htime (fun _ => le_max_left _ _)
      A hA
  rw [← gn21RawSwitchFirstSplitNoHit_eq_jointNoHit]
  calc
    Measure.map (gn21RawSwitchFirstHeadAndNextCycleSeed state)
        (P.restrict (gn21RawSwitchFirstSplitNoHit state sigma)) =
        Measure.map (project ∘ sourceOutput)
          (Measure.map input (P.restrict (input ⁻¹' carrier))) := by
            rw [show gn21RawSwitchFirstSplitNoHit state sigma = input ⁻¹' carrier by rfl,
              show gn21RawSwitchFirstHeadAndNextCycleSeed state =
                (project ∘ sourceOutput) ∘ input by
                  funext seed
                  rfl,
              Measure.map_map (hproject.comp hsourceOutput) hinput]
    _ = Measure.map (project ∘ sourceOutput) (sourceLaw.restrict carrier) := by
          rw [← Measure.restrict_map hinput hcarrier, hinputLaw.map_eq]
    _ = Measure.map project (Measure.map sourceOutput (sourceLaw.restrict carrier)) := by
          rw [Measure.map_map hproject hsourceOutput]
    _ = Measure.map project
        ((Measure.map Prod.fst
          (((Measure.map history (headLaw.prod departingArrivalLaw)).prod
            departingMarkLaw).restrict A)).prod tailLawOut) := by
          exact congrArg (Measure.map project) (by
            simpa [sourceOutput, sourceLaw, carrier, history, time, A, index, tailLawOut] using
              hfactor)
    _ = (gn21SwitchFirstHeadHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P := by
          rw [show project = Prod.map Prod.fst tailSeed by rfl,
            ← Measure.map_prod_map
              (Measure.map Prod.fst
                (((Measure.map history (headLaw.prod departingArrivalLaw)).prod
                  departingMarkLaw).restrict A)) tailLawOut
              measurable_fst htailSeed,
            htailSeedLaw]
          rfl

/-- On the literal strict switch-first branch, the retained head is exactly
the raw competing-race minimum and the deterministic tail reassembly is the
ordinary switch-first next seed. -/
theorem gn21RawSwitchFirstHeadAndNextCycleSeed_eq_actual_of_switchesFirst
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (hswitch : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma) :
    gn21RawSwitchFirstHeadAndNextCycleSeed state seed =
      (gn21RawPostThinningRaceMinimum state sigma seed,
        gn21RawSwitchFirstNextCycleSeed state seed) := by
  have hlt : (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
      (gn21RawPostThinningRaceSeed state sigma seed).1 := by
    simpa [gn21RawPostThinningRaceSwitchesFirst] using hswitch
  have hminimum : gn21RawPostThinningRaceMinimum state sigma seed =
      (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
    simp [gn21RawPostThinningRaceMinimum,
      AppliedModelingLib.Probability.exponentialRaceMinimum, min_eq_right hlt.le]
  apply Prod.ext
  · change (gn21RawSwitchFirstJointContinuationInput state seed).1.1.1 = _
    change (gn21RawSwitchFirstJointContinuationInput state seed).1.1.1 =
      gn21RawPostThinningRaceMinimum state sigma seed
    rw [hminimum]
    change (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2 = _
    rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
    rfl
  · rfl

/-- The source history/seed product law on the paper's literal strict
switch-first event.  The only event transport is the established source-a.e.
equivalence of that event with the totalized no-hit carrier. -/
theorem map_gn21RawPostThinningRaceSwitchFirstHistoryAndNextCycleSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (fun seed =>
      (gn21RawPostThinningRaceMinimum state sigma seed,
        gn21RawSwitchFirstNextCycleSeed state seed))
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      (gn21SwitchFirstHeadHistoryMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let strict := gn21RawPostThinningRaceSwitchesFirst state sigma
  let noHit := gn21RawSwitchFirstJointNoHit state sigma
  have htotal_raw :=
    ae_gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch_iff_noAcceptedBeforeSwitch
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma
  have hstrict_raw := ae_gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hjoint : noHit =ᵐ[P] strict := by
    filter_upwards [htotal_raw, hstrict_raw] with seed htotal hstrict
    change (seed ∈ gn21RawSwitchFirstJointNoHit state sigma) =
      (seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma)
    rw [gn21RawSwitchFirstJointNoHit_eq_externalNoHit]
    exact propext (htotal.trans hstrict.symm)
  have hrestrict : P.restrict strict = P.restrict noHit :=
    (Measure.restrict_congr_set hjoint).symm
  have hmem : ∀ᵐ seed ∂P.restrict strict, seed ∈ strict := by
    have hstrictMeas : MeasurableSet strict := by
      dsimp [strict, gn21RawPostThinningRaceSwitchesFirst]
      exact measurableSet_lt
        ((measurable_fst.comp measurable_snd).comp
          (measurable_gn21RawPostThinningRaceSeed state sigma hsigma))
        (measurable_fst.comp (measurable_gn21RawPostThinningRaceSeed state sigma hsigma))
    exact MeasureTheory.ae_restrict_mem hstrictMeas
  calc
    Measure.map (fun seed =>
        (gn21RawPostThinningRaceMinimum state sigma seed,
          gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict strict) =
        Measure.map (gn21RawSwitchFirstHeadAndNextCycleSeed state) (P.restrict strict) := by
          apply Measure.map_congr
          filter_upwards [hmem] with seed hseed
          exact (gn21RawSwitchFirstHeadAndNextCycleSeed_eq_actual_of_switchesFirst
            state sigma seed hseed).symm
    _ = Measure.map (gn21RawSwitchFirstHeadAndNextCycleSeed state) (P.restrict noHit) := by
          rw [hrestrict]
    _ = _ := map_gn21RawSwitchFirstHeadAndNextCycleSeed_restrict_noHit
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma

/-- The same literal-next-seed factorization on the paper's strict
switch-first event.  The only transport is the existing source-a.e.
identification of strict switch-first with the totalized no-hit carrier. -/
theorem map_gn21RawSwitchFirstNextCycleSeed_restrict_switchesFirst
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawSwitchFirstNextCycleSeed state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      (gn21SwitchFirstNoHitMass muI muJ arrivalI arrivalJ switchIJ switchJI state sigma) •
        gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let continuation := gn21RawSwitchFirstJointContinuation state
  let reassemble := gn21RawCycleSeedOfStateContinuation state
  calc
    Measure.map (gn21RawSwitchFirstNextCycleSeed state)
        (P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
        Measure.map reassemble
          (Measure.map continuation
            (P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma))) := by
              rw [gn21RawSwitchFirstNextCycleSeed, ← Measure.map_map
                (measurable_gn21RawCycleSeedOfStateContinuation state)
                (measurable_gn21RawSwitchFirstJointContinuation state)]
    _ = Measure.map reassemble
          (Measure.map continuation
            (P.restrict (gn21RawSwitchFirstJointNoHit state sigma)) ) := by
              exact congrArg (Measure.map reassemble)
                (map_gn21RawSwitchFirstJointContinuation_restrict_switchesFirst_eq_noHit
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
    _ = Measure.map (gn21RawSwitchFirstNextCycleSeed state)
          (P.restrict (gn21RawSwitchFirstJointNoHit state sigma)) := by
              rw [gn21RawSwitchFirstNextCycleSeed, ← Measure.map_map
                (measurable_gn21RawCycleSeedOfStateContinuation state)
                (measurable_gn21RawSwitchFirstJointContinuation state)]
    _ = _ := map_gn21RawSwitchFirstNextCycleSeed_restrict_noHit
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma

/-- The active accepted prefix together with both literal tails: the accepted
request index/mark/arrival time, then the uninspected mark tail and the
post-request interarrival tail. -/
abbrev GN21AcceptedArrivalPrefixAndTails :=
  ((Nat × TripLength) × Real) × ((Nat -> TripLength) × (Nat -> Real))

/-- The complete source coordinate needed before conditioning the accepted
race: active accepted prefix and both active tails, both switch streams, and
the untouched incoming marked-arrival input.  It is a deterministic raw-seed
projection, so later race residualization cannot discard a literal tail. -/
abbrev GN21AcceptedArrivalPrefixTailsWithContinuation :=
  GN21AcceptedArrivalPrefixAndTails ×
    (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))

noncomputable def gn21RawAcceptedArrivalPrefixTailsWithContinuation
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedArrivalPrefixTailsWithContinuation := fun seed =>
  ((((AcceptedTripSelection.gn21RawFirstAcceptedIndex state sigma seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed),
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
        (gn21ArrivalClockIndex state) state sigma seed),
    (AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed,
      AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
        (gn21ArrivalClockIndex state) state sigma seed)),
    (RawTwoStateCTMC.rawSwitchGapPair seed,
      (AcceptedArrivalTime.rawClockStream
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) seed,
        AcceptedArrivalTime.rawTripMarkStream
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed)))

theorem measurable_gn21RawAcceptedArrivalPrefixTailsWithContinuation
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedArrivalPrefixTailsWithContinuation state sigma) := by
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · exact (((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
        ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state))).prodMk
          (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalTime
            (gn21ArrivalClockIndex state) state sigma hsigma)
    · exact ((AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
        (AcceptedArrivalTime.measurable_gn21RawPostFirstAcceptedArrivalGapTail
          (gn21ArrivalClockIndex state) state sigma hsigma)
  · exact RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
      ((AcceptedArrivalTime.measurable_rawClockStream
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))).prodMk
        (AcceptedArrivalTime.measurable_rawTripMarkStream
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))

/-- Before the accepted-versus-switch race is restricted, the full accepted
prefix/tails coordinate factors from the literal switch and incoming marked
inputs.  This is the source product law needed to carry every continuation
coordinate through the race; it is deliberately stronger than the earlier
accepted-time/selected-mark marginal. -/
theorem gn21RawAcceptedArrivalPrefixTailsWithContinuation_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeMarks := AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)
    let activeGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
    let prefixLaw := Measure.map (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
        AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
      (activeMarks.prod activeGaps)
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    HasLaw (gn21RawAcceptedArrivalPrefixTailsWithContinuation state sigma)
      ((prefixLaw.prod (activeMarks.prod activeGaps)).prod (switchLaw.prod incomingLaw))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeBase := gn21CycleMarkLaw muI muJ state
  let activeMarks := AppliedModelingLib.Probability.IIDStream.measure activeBase
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let activeGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    activeRate
  let prefixLaw : Measure ((Nat × TripLength) × Real) := Measure.map
    (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
        AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
    (activeMarks.prod activeGaps)
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let incomingGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let incomingMarks := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingGaps.prod incomingMarks
  let companionLaw := switchLaw.prod incomingLaw
  let sourceLaw := (activeGaps.prod activeMarks).prod companionLaw
  let targetLaw := (prefixLaw.prod (activeMarks.prod activeGaps)).prod companionLaw
  let history := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
  let unbundle :
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) ->
        GN21AcceptedArrivalPrefixAndTails := fun h =>
    ((h.1.1.1, h.1.2), (h.1.1.2, h.2))
  let activeTransform : (Nat -> Real) × (Nat -> TripLength) ->
      GN21AcceptedArrivalPrefixAndTails := fun z =>
    unbundle (history (z.2, z.1))
  let transform : GN21SwitchFirstJointContinuation ->
      GN21AcceptedArrivalPrefixTailsWithContinuation := fun z =>
    (activeTransform z.1, z.2)
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure activeBase := by
    dsimp [activeBase]
    infer_instance
  letI : IsProbabilityMeasure activeMarks := by
    dsimp [activeMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure activeGaps := by
    dsimp [activeGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
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
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure incomingMarks := by
    dsimp [incomingMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hhistory : Measurable history :=
    AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  have hunbundle : Measurable unbundle := by
    exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hactiveTransform : Measurable activeTransform := by
    exact hunbundle.comp (hhistory.comp measurable_swap)
  have htransform : Measurable transform := by
    exact (hactiveTransform.comp measurable_fst).prodMk measurable_snd
  have hswap : HasLaw (Prod.swap : (Nat -> Real) × (Nat -> TripLength) ->
      (Nat -> TripLength) × (Nat -> Real))
      (activeMarks.prod activeGaps) (activeGaps.prod activeMarks) := by
    simpa using (Measure.measurePreserving_swap
      (μ := activeGaps) (ν := activeMarks)).hasLaw
  have hpaired : HasLaw (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      (((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
          AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime
            (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2),
        (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1,
          AppliedModelingLib.Probability.IIDStream.externalIndexTail
            (fun marks => AcceptedTripSelection.firstAcceptedIndex sigma marks + 1) paths)))
      (prefixLaw.prod (activeMarks.prod activeGaps)) (activeMarks.prod activeGaps) := by
    simpa [prefixLaw, activeMarks, activeGaps, activeBase] using
      (AcceptedArrivalTime.firstAcceptedArrivalPrefixAndTails_hasLaw_prod
        activeBase hactiveRate sigma hsigma hmass)
  have hactive : HasLaw activeTransform
      (prefixLaw.prod (activeMarks.prod activeGaps)) (activeGaps.prod activeMarks) := by
    simpa [activeTransform, unbundle, history,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using hpaired.comp hswap
  have hsource : HasLaw (gn21RawCycleSeedStateContinuationInput state)
      sourceLaw P := by
    simpa [sourceLaw, companionLaw, switchLaw, incomingLaw, incomingGaps,
      incomingMarks, activeGaps, activeMarks, activeBase, activeRate, other, P] using
      (gn21RawCycleSeedStateContinuationInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have htrans : HasLaw transform targetLaw sourceLaw := by
    refine ⟨htransform.aemeasurable, ?_⟩
    rw [show transform = Prod.map activeTransform id by rfl,
      ← Measure.map_prod_map (activeGaps.prod activeMarks) companionLaw
        hactiveTransform measurable_id,
      hactive.map_eq, Measure.map_id]
  have hfinal := htrans.comp hsource
  change HasLaw (gn21RawAcceptedArrivalPrefixTailsWithContinuation state sigma) targetLaw P
  refine hfinal.congr ?_
  filter_upwards [] with seed
  rfl

/-- On the active marked-renewal source itself, the accepted arrival time and
selected mark factor jointly from both literal tails.  The accepted index is
intentionally discarded here: it is not needed after the source tails have
been retained, and dropping it exposes the independent exponential race clock
without discarding either continuation stream. -/
theorem gn21ActiveAcceptedArrivalTimeMarkAndTails_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let M := gn21CycleMarkLaw muI muJ state
    let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let marks := AppliedModelingLib.Probability.IIDStream.measure M
    let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
    let selectedLaw := gn21AcceptedTripLaw M sigma
    HasLaw (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      Prod.mk
        (AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2,
          AcceptedTripSelection.firstAcceptedTripMark sigma paths.1)
        (Prod.mk (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1)
          (AppliedModelingLib.Probability.IIDStream.externalIndexTail
            (fun stream => AcceptedTripSelection.firstAcceptedIndex sigma stream + 1) paths)))
      (((ProbabilityTheory.expMeasure
          (rate * singleStateTripMass M sigma)).prod selectedLaw).prod (marks.prod gaps))
      (marks.prod gaps) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let marks := AppliedModelingLib.Probability.IIDStream.measure M
  let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let selectedLaw := gn21AcceptedTripLaw M sigma
  let prefixLaw : Measure ((Nat × TripLength) × Real) := Measure.map
    (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
        AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
    (marks.prod gaps)
  let rawInput : GN21RawCycleSeed -> (Nat -> TripLength) × (Nat -> Real) := fun seed =>
    (AcceptedArrivalTime.rawTripMarkStream state seed,
      AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed)
  let pairTimeMark : (Nat -> TripLength) × (Nat -> Real) -> Real × TripLength := fun paths =>
    (AppliedModelingLib.Probability.PoissonProcess.arrivalTime
      (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2,
      AcceptedTripSelection.firstAcceptedTripMark sigma paths.1)
  let dropIndex : ((Nat × TripLength) × Real) -> Real × TripLength := fun p =>
    (p.2, p.1.2)
  let paired : (Nat -> TripLength) × (Nat -> Real) ->
      GN21AcceptedArrivalPrefixAndTails := fun paths =>
    Prod.mk
      (Prod.mk (AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
          AcceptedTripSelection.firstAcceptedTripMark sigma paths.1)
        (AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
      (Prod.mk (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1)
        (AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun stream => AcceptedTripSelection.firstAcceptedIndex sigma stream + 1) paths))
  let output : GN21AcceptedArrivalPrefixAndTails ->
      (Real × TripLength) × ((Nat -> TripLength) × (Nat -> Real)) := fun z =>
    (dropIndex z.1, z.2)
  have hrate : 0 < rate := by
    dsimp [rate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hrate
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability M sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hhistory := AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
  have hpairTimeMark : Measurable pairTimeMark := by
    let project : (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) ->
        Real × TripLength := fun history => (history.1.2, history.1.1.1.2)
    have hproject : Measurable project := by
      exact (measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
    simpa [pairTimeMark, project,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using hproject.comp hhistory
  have hpaired : HasLaw paired (prefixLaw.prod (marks.prod gaps)) (marks.prod gaps) := by
    simpa [paired, prefixLaw, marks, gaps, M] using
      (AcceptedArrivalTime.firstAcceptedArrivalPrefixAndTails_hasLaw_prod
        M hrate sigma hsigma hmass)
  have hpairedMeas : Measurable paired := by
    let unbundle :
        (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) ->
          GN21AcceptedArrivalPrefixAndTails := fun h =>
      ((h.1.1.1, h.1.2), (h.1.1.2, h.2))
    have hunbundle : Measurable unbundle := by
      exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    simpa [paired, unbundle,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using
      hunbundle.comp hhistory
  have hrawInput : HasLaw rawInput (marks.prod gaps) P := by
    simpa [rawInput, marks, gaps, M, rate, P] using
      (AcceptedArrivalTime.rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        (gn21ArrivalClockIndex state) state)
  have hrawTimeMark : HasLaw (fun seed : GN21RawCycleSeed =>
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
        (gn21ArrivalClockIndex state) state sigma seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
      ((ProbabilityTheory.expMeasure
        (rate * singleStateTripMass M sigma)).prod selectedLaw) P := by
    simpa [rate, M, selectedLaw, P] using
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        (gn21ArrivalClockIndex state) state sigma hsigma hmass)
  have htimeMark : HasLaw pairTimeMark
      ((ProbabilityTheory.expMeasure
        (rate * singleStateTripMass M sigma)).prod selectedLaw) (marks.prod gaps) := by
    refine ⟨hpairTimeMark.aemeasurable, ?_⟩
    calc
      Measure.map pairTimeMark (marks.prod gaps) =
          Measure.map pairTimeMark (Measure.map rawInput P) := by rw [hrawInput.map_eq]
      _ = Measure.map (pairTimeMark ∘ rawInput) P := by
          rw [Measure.map_map hpairTimeMark
            ((AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
              (AcceptedArrivalTime.measurable_rawClockStream (gn21ArrivalClockIndex state)))]
      _ = Measure.map (fun seed : GN21RawCycleSeed =>
          (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
            (gn21ArrivalClockIndex state) state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) P := by
              rfl
      _ = _ := hrawTimeMark.map_eq
  have hdropIndexMeas : Measurable dropIndex := by
    exact measurable_snd.prodMk
      (measurable_snd.comp measurable_fst)
  have hdrop : Measure.map dropIndex prefixLaw =
      (ProbabilityTheory.expMeasure
        (rate * singleStateTripMass M sigma)).prod selectedLaw := by
    calc
      Measure.map dropIndex prefixLaw =
          Measure.map dropIndex
            (Measure.map (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
              ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
                AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
                AppliedModelingLib.Probability.PoissonProcess.arrivalTime
                  (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
              (marks.prod gaps)) := by rfl
      _ = Measure.map pairTimeMark (marks.prod gaps) := by
          let prefixProject :
              (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) ->
                ((Nat × TripLength) × Real) := fun h => (h.1.1.1, h.1.2)
          have hprefixProject : Measurable prefixProject := by
            exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
              (measurable_snd.comp measurable_fst)
          have hprefixMeas : Measurable (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
              ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
                AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
                AppliedModelingLib.Probability.PoissonProcess.arrivalTime
                  (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2)) := by
            simpa [prefixProject,
              AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using
              hprefixProject.comp hhistory
          rw [Measure.map_map hdropIndexMeas hprefixMeas]
          rfl
      _ = _ := htimeMark.map_eq
  have houtput : Measurable output := by
    exact ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd
  have hfinal : HasLaw (output ∘ paired)
      (((ProbabilityTheory.expMeasure
        (rate * singleStateTripMass M sigma)).prod selectedLaw).prod (marks.prod gaps))
      (marks.prod gaps) := by
    refine ⟨(houtput.comp hpairedMeas).aemeasurable, ?_⟩
    rw [← Measure.map_map houtput hpairedMeas]
    rw [hpaired.map_eq]
    rw [show output = Prod.map dropIndex id by rfl,
      ← Measure.map_prod_map prefixLaw (marks.prod gaps) hdropIndexMeas measurable_id,
      hdrop, Measure.map_id]
  simpa [output, paired, dropIndex, Function.comp_def] using hfinal

/-- The index-free accepted prefix/tails coordinate together with the two
literal switch streams and untouched incoming marked input.  This is the
product-space carrier immediately before the accepted-versus-switch race is
conditioned. -/
abbrev GN21AcceptedArrivalTimeMarkTailsWithContinuation :=
  ((Real × TripLength) × ((Nat -> TripLength) × (Nat -> Real))) ×
    (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))

noncomputable def gn21RawAcceptedArrivalTimeMarkTailsWithContinuation
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedArrivalTimeMarkTailsWithContinuation := fun seed =>
  (((AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
      (gn21ArrivalClockIndex state) state sigma seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed),
    (AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed,
      AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
        (gn21ArrivalClockIndex state) state sigma seed)),
    (RawTwoStateCTMC.rawSwitchGapPair seed,
      (AcceptedArrivalTime.rawClockStream
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) seed,
        AcceptedArrivalTime.rawTripMarkStream
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed)))

theorem measurable_gn21RawAcceptedArrivalTimeMarkTailsWithContinuation
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma) := by
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · exact (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalTime
        (gn21ArrivalClockIndex state) state sigma hsigma).prodMk
        ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
          (AcceptedArrivalTime.measurable_rawTripMarkStream state))
    · exact ((AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)).prodMk
        (AcceptedArrivalTime.measurable_gn21RawPostFirstAcceptedArrivalGapTail
          (gn21ArrivalClockIndex state) state sigma hsigma)
  · exact RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
      ((AcceptedArrivalTime.measurable_rawClockStream
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))).prodMk
        (AcceptedArrivalTime.measurable_rawTripMarkStream
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))

/-- The index-free accepted prefix/tails coordinate factors jointly from the
literal switch and incoming marked inputs.  It combines the source-separated
active time/mark/tails theorem with GN's state-ordered raw product, rather
than replacing any coordinate by a restarted sample. -/
theorem gn21RawAcceptedArrivalTimeMarkTailsWithContinuation_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let M := gn21CycleMarkLaw muI muJ state
    let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let activeMarks := AppliedModelingLib.Probability.IIDStream.measure M
    let activeGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
    let activeOutput :=
      ((ProbabilityTheory.expMeasure (rate * singleStateTripMass M sigma)).prod
        (gn21AcceptedTripLaw M sigma)).prod (activeMarks.prod activeGaps)
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    HasLaw (gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma)
      (activeOutput.prod (switchLaw.prod incomingLaw))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let activeMarks := AppliedModelingLib.Probability.IIDStream.measure M
  let activeGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let selectedLaw := gn21AcceptedTripLaw M sigma
  let activeOutput :=
    ((ProbabilityTheory.expMeasure (rate * singleStateTripMass M sigma)).prod selectedLaw).prod
      (activeMarks.prod activeGaps)
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let incomingGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let incomingMarks := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingGaps.prod incomingMarks
  let companionLaw := switchLaw.prod incomingLaw
  let sourceLaw := (activeGaps.prod activeMarks).prod companionLaw
  let targetLaw := activeOutput.prod companionLaw
  let activeTransform : (Nat -> Real) × (Nat -> TripLength) ->
      (Real × TripLength) × ((Nat -> TripLength) × (Nat -> Real)) := fun z =>
    ((AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.2) z.1,
      AcceptedTripSelection.firstAcceptedTripMark sigma z.2),
      (AcceptedTripSelection.firstAcceptedTripTail sigma z.2,
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun stream => AcceptedTripSelection.firstAcceptedIndex sigma stream + 1) (z.2, z.1)))
  let transform : GN21SwitchFirstJointContinuation ->
      GN21AcceptedArrivalTimeMarkTailsWithContinuation := fun z =>
    (activeTransform z.1, z.2)
  have hrate : 0 < rate := by
    dsimp [rate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure M := by
    dsimp [M]
    infer_instance
  letI : IsProbabilityMeasure activeMarks := by
    dsimp [activeMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure activeGaps := by
    dsimp [activeGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hrate
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability M sigma hmass
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (rate * singleStateTripMass M sigma)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (mul_pos hrate hmass)
  letI : IsProbabilityMeasure activeOutput := by
    dsimp [activeOutput]
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
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure incomingMarks := by
    dsimp [incomingMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hactiveTransform : Measurable activeTransform := by
    let history := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
    let project : (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) ->
        (Real × TripLength) × ((Nat -> TripLength) × (Nat -> Real)) := fun h =>
      ((h.1.2, h.1.1.1.2), (h.1.1.2, h.2))
    have hhistory : Measurable history :=
      AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
    have hproject : Measurable project := by
      exact ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    simpa [activeTransform, project, history,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams] using
      hproject.comp (hhistory.comp measurable_swap)
  have htransform : Measurable transform := by
    exact (hactiveTransform.comp measurable_fst).prodMk measurable_snd
  have hswap : HasLaw (Prod.swap : (Nat -> Real) × (Nat -> TripLength) ->
      (Nat -> TripLength) × (Nat -> Real))
      (activeMarks.prod activeGaps) (activeGaps.prod activeMarks) := by
    simpa using (Measure.measurePreserving_swap
      (μ := activeGaps) (ν := activeMarks)).hasLaw
  have hactive : HasLaw activeTransform activeOutput (activeGaps.prod activeMarks) := by
    simpa [activeTransform, activeOutput, activeMarks, activeGaps, M, rate, selectedLaw] using
      (gn21ActiveAcceptedArrivalTimeMarkAndTails_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass).comp hswap
  have hsource : HasLaw (gn21RawCycleSeedStateContinuationInput state)
      sourceLaw P := by
    simpa [sourceLaw, companionLaw, switchLaw, incomingLaw, incomingGaps,
      incomingMarks, activeGaps, activeMarks, M, rate, other, P] using
      (gn21RawCycleSeedStateContinuationInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have htrans : HasLaw transform targetLaw sourceLaw := by
    refine ⟨htransform.aemeasurable, ?_⟩
    rw [show transform = Prod.map activeTransform id by rfl,
      ← Measure.map_prod_map (activeGaps.prod activeMarks) companionLaw
        hactiveTransform measurable_id,
      hactive.map_eq, Measure.map_id]
  have hfinal := htrans.comp hsource
  change HasLaw (gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma) targetLaw P
  refine hfinal.congr ?_
  filter_upwards [] with seed
  rfl

/-- Full retained source input for the accepted-winner exponential race.  The
leading coordinate is the two-switch tail after removing the active head; the
right race clock is that literal head, while the left race clock, selected
trip, both active marked tails, and incoming marked input are all retained. -/
abbrev GN21AcceptedWinnerFullRaceInput :=
  (((Nat -> Real) × (Nat -> Real)) × Real) ×
    (Real × (TripLength ×
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))))

noncomputable def gn21RawAcceptedWinnerFullRaceInput
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedWinnerFullRaceInput := fun seed =>
  let z := gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma seed
  (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed,
    (z.1.1.1,
      (z.1.1.2,
        ((z.1.2.2, z.1.2.1), z.2.2))))

theorem measurable_gn21RawAcceptedWinnerFullRaceInput
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedWinnerFullRaceInput state sigma) := by
  let z := gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma
  have hz : Measurable z :=
    measurable_gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma hsigma
  have hswitch : Measurable (RawTwoStateCTMC.rawSwitchTailAndFirstGap state) :=
    RawTwoStateCTMC.measurable_rawSwitchTailAndFirstGap state
  have htime : Measurable (fun seed => (z seed).1.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp hz))
  have hmark : Measurable (fun seed => (z seed).1.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hz))
  have hgapTail : Measurable (fun seed => (z seed).1.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp hz))
  have hmarkTail : Measurable (fun seed => (z seed).1.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_fst.comp hz))
  have hincoming : Measurable (fun seed => (z seed).2.2) :=
    measurable_snd.comp (measurable_snd.comp hz)
  exact hswitch.prodMk (htime.prodMk
    (hmark.prodMk ((hgapTail.prodMk hmarkTail).prodMk hincoming)))

/-- Exact source law of the full accepted-winner race input.  The leading
switch-tail coordinate and every marked-arrival continuation are retained
while exposing the independent accepted-arrival and active-switch heads to
the race theorem. -/
theorem gn21RawAcceptedWinnerFullRaceInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let activeTailMarks := AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)
    let activeTailGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      activeRate
    let switchTails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let activeSwitchHead := if state = 0 then ProbabilityTheory.expMeasure switchIJ
      else ProbabilityTheory.expMeasure switchJI
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    HasLaw (gn21RawAcceptedWinnerFullRaceInput state sigma)
      ((switchTails.prod activeSwitchHead).prod
        ((ProbabilityTheory.expMeasure acceptedRate).prod
          ((gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma).prod
            ((activeTailGaps.prod activeTailMarks).prod incomingLaw))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeBase := gn21CycleMarkLaw muI muJ state
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass activeBase sigma
  let selectedLaw := gn21AcceptedTripLaw activeBase sigma
  let activeTailMarks := AppliedModelingLib.Probability.IIDStream.measure activeBase
  let activeTailGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    activeRate
  let switchTails : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let activeSwitchHead : Measure Real := if state = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let incomingGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let incomingMarks := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingGaps.prod incomingMarks
  let sourceLaw :=
    ((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod
      (activeTailMarks.prod activeTailGaps) |>.prod (switchTails.prod incomingLaw)
  let targetLaw := (switchTails.prod activeSwitchHead).prod
    ((ProbabilityTheory.expMeasure acceptedRate).prod
      (selectedLaw.prod ((activeTailGaps.prod activeTailMarks).prod incomingLaw)))
  let full := gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma
  let reorder : GN21AcceptedArrivalTimeMarkTailsWithContinuation ->
      GN21AcceptedWinnerFullRaceInput := fun z =>
    (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state z.2.1,
      (z.1.1.1, (z.1.1.2, ((z.1.2.2, z.1.2.1), z.2.2))))
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos hactiveRate hmass
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure activeBase := by
    dsimp [activeBase]
    infer_instance
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure acceptedRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability activeBase sigma hmass
  letI : IsProbabilityMeasure activeTailMarks := by
    dsimp [activeTailMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure activeTailGaps := by
    dsimp [activeTailGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchTails := by
    dsimp [switchTails]
    infer_instance
  letI : IsProbabilityMeasure activeSwitchHead := by
    dsimp [activeSwitchHead]
    split
    · exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchIJ
    · exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchJI
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure incomingMarks := by
    dsimp [incomingMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  letI : IsProbabilityMeasure targetLaw := by
    dsimp [targetLaw]
    infer_instance
  have hfull : HasLaw full sourceLaw P := by
    simpa [full, sourceLaw, activeBase, activeRate, acceptedRate, selectedLaw,
      activeTailMarks, activeTailGaps, switchTails, incomingLaw, incomingGaps,
      incomingMarks, other, P] using
      (gn21RawAcceptedArrivalTimeMarkTailsWithContinuation_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  let hfront : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod
        ((activeTailMarks.prod activeTailGaps).prod (switchTails.prod incomingLaw)))
      ((activeTailMarks.prod activeTailGaps).prod
        (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod
          (switchTails.prod incomingLaw))) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let hmoveSwitchInner : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod
        (switchTails.prod incomingLaw))
      (switchTails.prod
        (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod incomingLaw)) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let hmoveSwitch : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      ((activeTailMarks.prod activeTailGaps).prod
        (switchTails.prod
          (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod incomingLaw)))
      (switchTails.prod ((activeTailMarks.prod activeTailGaps).prod
        (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod incomingLaw))) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let hmoveTime : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      ((activeTailMarks.prod activeTailGaps).prod
        (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod incomingLaw))
      (((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw).prod
        ((activeTailMarks.prod activeTailGaps).prod incomingLaw)) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let hswapActive : MeasurePreserving
      (Prod.swap : (Nat -> TripLength) × (Nat -> Real) -> (Nat -> Real) × (Nat -> TripLength))
      (activeTailMarks.prod activeTailGaps) (activeTailGaps.prod activeTailMarks) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let htimeAssoc := measurePreserving_prodAssoc
    (ProbabilityTheory.expMeasure acceptedRate) selectedLaw
    ((activeTailGaps.prod activeTailMarks).prod incomingLaw)
  let hswitchSplit : MeasurePreserving
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state)
      switchTails (switchTails.prod activeSwitchHead) := by
    refine ⟨AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead state, ?_⟩
    simpa [switchTails, activeSwitchHead] using
      (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamAfterActiveHead
        state hswitchIJ hswitchJI)
  let p0 := measurePreserving_prodAssoc
    ((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw)
    (activeTailMarks.prod activeTailGaps) (switchTails.prod incomingLaw)
  let p1 := hfront
  let p2 := MeasurePreserving.prod (MeasurePreserving.id (activeTailMarks.prod activeTailGaps))
    hmoveSwitchInner
  let p3 := hmoveSwitch
  let p4 := MeasurePreserving.prod (MeasurePreserving.id switchTails) hmoveTime
  let p5 := MeasurePreserving.prod (MeasurePreserving.id switchTails)
    (MeasurePreserving.prod (MeasurePreserving.id
      ((ProbabilityTheory.expMeasure acceptedRate).prod selectedLaw))
      (MeasurePreserving.prod hswapActive (MeasurePreserving.id incomingLaw)))
  let p6 := MeasurePreserving.prod (MeasurePreserving.id switchTails) htimeAssoc
  let p7 := MeasurePreserving.prod hswitchSplit
    (MeasurePreserving.id
      ((ProbabilityTheory.expMeasure acceptedRate).prod
        (selectedLaw.prod ((activeTailGaps.prod activeTailMarks).prod incomingLaw))))
  have hreorder : MeasurePreserving reorder sourceLaw targetLaw := by
    simpa [reorder, sourceLaw, targetLaw] using
      (p7.comp (p6.comp (p5.comp (p4.comp (p3.comp (p2.comp (p1.comp p0)))))))
  have hfinal := hreorder.hasLaw.comp hfull
  change HasLaw (gn21RawAcceptedWinnerFullRaceInput state sigma) targetLaw P
  simpa [gn21RawAcceptedWinnerFullRaceInput, full, reorder] using hfinal

/-- The full source continuation after the accepted arrival wins the local
race.  Its first coordinate is the elapsed local race time; its second is
the fresh active-switch residual together with every literal tail retained by
`GN21AcceptedWinnerFullRaceInput`. -/
abbrev GN21AcceptedWinnerFullResidualInput :=
  Real × (Real ×
    (((Nat -> Real) × (Nat -> Real)) ×
      (TripLength ×
        (((Nat -> Real) × (Nat -> TripLength)) ×
          ((Nat -> Real) × (Nat -> TripLength))))))

/-- Apply the accepted-winner residual transformation without replacing any
continuation coordinate by a new draw. -/
noncomputable def gn21RawAcceptedWinnerFullResidualInput
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedWinnerFullResidualInput :=
  AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux ∘
    gn21RawAcceptedWinnerFullRaceInput state sigma

theorem measurable_gn21RawAcceptedWinnerFullResidualInput
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedWinnerFullResidualInput state sigma) := by
  exact
    (AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidualWithLeadingAux).comp
      (measurable_gn21RawAcceptedWinnerFullRaceInput state sigma hsigma)

/-- On the literal accepted-first event, the full continuation has the exact
unnormalized residual-race law.  In particular, conditioning creates only the
fresh exponential residual of the active switch head: the two switch tails,
selected mark, and both marked-arrival continuations are retained jointly. -/
theorem map_gn21RawAcceptedWinnerFullResidualInput_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (RawTwoStateCTMC.switchClockIndex state)
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeTailMarks := AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)
    let activeTailGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      activeRate
    let switchTails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    Measure.map (gn21RawAcceptedWinnerFullResidualInput state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        (ProbabilityTheory.expMeasure (acceptedRate + switchRate)).prod
          ((ProbabilityTheory.expMeasure switchRate).prod
            (switchTails.prod
              (selectedLaw.prod
                ((activeTailGaps.prod activeTailMarks).prod incomingLaw)))) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeBase := gn21CycleMarkLaw muI muJ state
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass activeBase sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let selectedLaw := gn21AcceptedTripLaw activeBase sigma
  let activeTailMarks := AppliedModelingLib.Probability.IIDStream.measure activeBase
  let activeTailGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    activeRate
  let switchTails : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let incomingGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let incomingMarks := AppliedModelingLib.Probability.IIDStream.measure
    (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingGaps.prod incomingMarks
  let sourceLaw := (switchTails.prod (ProbabilityTheory.expMeasure switchRate)).prod
    ((ProbabilityTheory.expMeasure acceptedRate).prod
      (selectedLaw.prod ((activeTailGaps.prod activeTailMarks).prod incomingLaw)))
  let carrier := AppliedModelingLib.Probability.exponentialRaceLeftWinnerLeadingAuxCarrier
    (α := (Nat -> Real) × (Nat -> Real))
    (β := TripLength ×
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) )
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure activeBase := by
    dsimp [activeBase]
    infer_instance
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure acceptedRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure switchRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability activeBase sigma hmass
  letI : IsProbabilityMeasure activeTailMarks := by
    dsimp [activeTailMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure activeTailGaps := by
    dsimp [activeTailGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure switchTails := by
    dsimp [switchTails]
    infer_instance
  letI : IsProbabilityMeasure incomingGaps := by
    dsimp [incomingGaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure incomingMarks := by
    dsimp [incomingMarks, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hsource : HasLaw (gn21RawAcceptedWinnerFullRaceInput state sigma) sourceLaw P := by
    have hraw := gn21RawAcceptedWinnerFullRaceInput_hasLaw
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
    fin_cases state <;>
      simpa [sourceLaw, P, activeBase, activeRate, acceptedRate, switchRate, selectedLaw,
        activeTailMarks, activeTailGaps, switchTails, incomingLaw, incomingGaps, incomingMarks,
        other, RawTwoStateCTMC.switchClockIndex, gn21CycleClockRate] using hraw
  have hpreimage : (gn21RawAcceptedWinnerFullRaceInput state sigma) ⁻¹' carrier =
      gn21RawPostThinningRaceAcceptedFirst state sigma := by
    ext seed
    change
      AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime (gn21ArrivalClockIndex state)
        state sigma seed ≤ (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2 ↔
        ¬(gn21RawPostThinningRaceSeed state sigma seed).2.1 <
          (gn21RawPostThinningRaceSeed state sigma seed).1
    rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
    simp [gn21RawPostThinningRaceSeed, not_lt]
    rfl
  have hcarrier : MeasurableSet carrier := by
    simpa [carrier] using
      (AppliedModelingLib.Probability.measurableSet_exponentialRaceLeftWinnerLeadingAuxCarrier
        (α := (Nat -> Real) × (Nat -> Real))
        (β := TripLength ×
          (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))))
  change Measure.map (gn21RawAcceptedWinnerFullResidualInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        (ProbabilityTheory.expMeasure (acceptedRate + switchRate)).prod
          ((ProbabilityTheory.expMeasure switchRate).prod
            (switchTails.prod
              (selectedLaw.prod
                ((activeTailGaps.prod activeTailMarks).prod incomingLaw))))
  calc
    Measure.map (gn21RawAcceptedWinnerFullResidualInput state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map
          (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
          (Measure.map (gn21RawAcceptedWinnerFullRaceInput state sigma)
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [show gn21RawAcceptedWinnerFullResidualInput state sigma =
                AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux ∘
                  gn21RawAcceptedWinnerFullRaceInput state sigma by rfl,
                Measure.map_map
                  AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidualWithLeadingAux
                  (measurable_gn21RawAcceptedWinnerFullRaceInput state sigma hsigma)]
    _ = Measure.map
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
        ((Measure.map (gn21RawAcceptedWinnerFullRaceInput state sigma) P).restrict carrier) := by
          rw [← hpreimage, Measure.restrict_map
            (measurable_gn21RawAcceptedWinnerFullRaceInput state sigma hsigma) hcarrier]
    _ = Measure.map
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
        (sourceLaw.restrict carrier) := by rw [hsource.map_eq]
    _ = ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        (ProbabilityTheory.expMeasure (acceptedRate + switchRate)).prod
          ((ProbabilityTheory.expMeasure switchRate).prod
            (switchTails.prod
              (selectedLaw.prod
                ((activeTailGaps.prod activeTailMarks).prod incomingLaw)))) := by
          simpa [sourceLaw, carrier] using
            (AppliedModelingLib.Probability.map_exponentialRaceLeftWinnerResidualWithLeadingAux_expMeasure_prod_restrict
              (ν := switchTails)
              (ξ := selectedLaw.prod ((activeTailGaps.prod activeTailMarks).prod incomingLaw))
              hacceptedRate hswitchRate)

/-- The complete literal input immediately after an accepted arrival wins the
open-state race.  The residual active switch head is reattached to its
literal state-indexed tails, while the elapsed accepted-arrival time,
selected trip duration, and both marked-arrival continuations remain exposed
for the later calendar-completion residual maps. -/
abbrev GN21AcceptedWinnerPostRaceCalendarInput :=
  ((Nat -> Real) × (Nat -> Real)) ×
    (Real × (TripLength ×
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))))

noncomputable def gn21RawAcceptedWinnerPostRaceCalendarInput
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21AcceptedWinnerPostRaceCalendarInput := fun seed =>
  let z := gn21RawAcceptedWinnerFullResidualInput state sigma seed
  (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
      state (z.2.1, z.2.2.1),
    (z.1, (z.2.2.2.1, z.2.2.2.2)))

theorem measurable_gn21RawAcceptedWinnerPostRaceCalendarInput
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma) := by
  let z := gn21RawAcceptedWinnerFullResidualInput state sigma
  have hz : Measurable z :=
    measurable_gn21RawAcceptedWinnerFullResidualInput state sigma hsigma
  have hswitch : Measurable (fun seed =>
      AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
        state ((z seed).2.1, (z seed).2.2.1)) := by
    exact (AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamPrependActiveHeadFromHeadTail
      state).comp
        ((measurable_fst.comp (measurable_snd.comp hz)).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hz))))
  have htime : Measurable (fun seed => (z seed).1) := measurable_fst.comp hz
  have hduration : Measurable (fun seed => (z seed).2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hz)))
  have hactive : Measurable (fun seed => (z seed).2.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hz))))
  have hincoming : Measurable (fun seed => (z seed).2.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hz))))
  exact hswitch.prodMk (htime.prodMk (hduration.prodMk (hactive.prodMk hincoming)))

/-- The post-race calendar input has the exact accepted-branch law.  The
active switch residual is reattached to the same literal tails before any
calendar-time residual is taken, so this theorem has no hidden restart draw. -/
theorem map_gn21RawAcceptedWinnerPostRaceCalendarInput_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (RawTwoStateCTMC.switchClockIndex state)
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeTailMarks := AppliedModelingLib.Probability.IIDStream.measure
      (gn21CycleMarkLaw muI muJ state)
    let activeTailGaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      activeRate
    let switchTails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        (switchTails.prod
          ((ProbabilityTheory.expMeasure (acceptedRate + switchRate)).prod
            (selectedLaw.prod ((activeTailGaps.prod activeTailMarks).prod incomingLaw)))) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeBase := gn21CycleMarkLaw muI muJ state
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass activeBase sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let S := ProbabilityTheory.expMeasure switchRate
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw activeBase sigma
  let M := AppliedModelingLib.Probability.IIDStream.measure activeBase
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let I :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))).prod
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other))
  let R := Q.prod ((G.prod M).prod I)
  let fullLaw := T.prod (S.prod (W.prod R))
  let outputLaw := W.prod (T.prod R)
  let full := gn21RawAcceptedWinnerFullResidualInput state sigma
  let join := AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
    state
  let reorder : GN21AcceptedWinnerFullResidualInput ->
      (Real × ((Nat -> Real) × (Nat -> Real))) × (Real × (TripLength ×
        (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))))) :=
    fun z => ((z.2.1, z.2.2.1), (z.1, z.2.2.2))
  let transform : GN21AcceptedWinnerFullResidualInput ->
      GN21AcceptedWinnerPostRaceCalendarInput := fun z =>
    (join (reorder z).1, (reorder z).2)
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure activeBase := by
    dsimp [activeBase]
    infer_instance
  letI : IsProbabilityMeasure S := ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability activeBase sigma hmass
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure G := by
    dsimp [G]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ other) := by
    fin_cases state <;>
      simp [other, gn21CycleMarkLaw,
        AppliedModelingLib.Probability.TwoStateSwitching.otherState] <;>
      infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure
        (gn21CycleMarkLaw muI muJ other)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    infer_instance
  letI : IsProbabilityMeasure fullLaw := by
    dsimp [fullLaw]
    infer_instance
  letI : IsProbabilityMeasure outputLaw := by
    dsimp [outputLaw]
    infer_instance
  have hfull : Measure.map full
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) • fullLaw := by
    have hraw := map_gn21RawAcceptedWinnerFullResidualInput_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
    fin_cases state <;>
      simpa [P, activeBase, activeRate, acceptedRate, switchRate, S, T, Q, M, G, W, I, R,
        fullLaw, other, RawTwoStateCTMC.switchClockIndex, gn21CycleClockRate] using hraw
  have hjoin : MeasurePreserving join (S.prod W) W := by
    have hjoinraw :=
      AppliedModelingLib.Probability.PoissonProcess.map_twoStreamPrependActiveHeadFromHeadTail
        state hswitchIJ hswitchJI
    refine ⟨AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamPrependActiveHeadFromHeadTail
      state, ?_⟩
    fin_cases state <;>
      simpa [join, S, W, switchRate, RawTwoStateCTMC.switchClockIndex,
        gn21CycleClockRate] using hjoinraw
  let p1 : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      fullLaw (S.prod (T.prod (W.prod R))) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let p2 : MeasurePreserving
      (Prod.map id AppliedModelingLib.Probability.productFrontSwap)
      (S.prod (T.prod (W.prod R))) (S.prod (W.prod (T.prod R))) := by
    exact MeasurePreserving.prod (MeasurePreserving.id S)
      ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
        AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let p3 : MeasurePreserving
      (AppliedModelingLib.Probability.productFrontSwap)
      (S.prod (W.prod (T.prod R))) (W.prod (S.prod (T.prod R))) := by
    exact ⟨AppliedModelingLib.Probability.measurable_productFrontSwap,
      AppliedModelingLib.Probability.map_productFrontSwap _ _ _⟩
  let p4 := (measurePreserving_prodAssoc W S (T.prod R)).symm
  let p5 : MeasurePreserving
      (Prod.map (Prod.swap : (((Nat -> Real) × (Nat -> Real)) × Real) ->
        Real × ((Nat -> Real) × (Nat -> Real)) ) id)
      ((W.prod S).prod (T.prod R)) ((S.prod W).prod (T.prod R)) := by
    exact MeasurePreserving.prod
      ⟨measurable_swap, Measure.prod_swap⟩
      (MeasurePreserving.id (T.prod R))
  have hreorder : MeasurePreserving reorder fullLaw ((S.prod W).prod (T.prod R)) := by
    simpa [reorder, fullLaw] using (p5.comp (p4.comp (p3.comp (p2.comp p1))))
  have htransform : MeasurePreserving transform fullLaw outputLaw := by
    have hjoinProd := MeasurePreserving.prod hjoin (MeasurePreserving.id (T.prod R))
    simpa [transform, outputLaw] using hjoinProd.comp hreorder
  change Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) • outputLaw
  calc
    Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map transform (Measure.map full
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
            rw [show gn21RawAcceptedWinnerPostRaceCalendarInput state sigma = transform ∘ full by rfl,
              Measure.map_map htransform.measurable
                (measurable_gn21RawAcceptedWinnerFullResidualInput state sigma hsigma)]
    _ = Measure.map transform
        (ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) • fullLaw) := by rw [hfull]
    _ = ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        Measure.map transform fullLaw := by rw [Measure.map_smul]
    _ = ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) • outputLaw := by
      rw [htransform.map_eq]

/-- The state-continuation coordinate at selected-trip completion.  The
active marked tail begins immediately after the accepted request and is
shifted by its selected duration; the incoming marked input and reassembled
switch path are shifted from their respective literal origins: elapsed arrival
plus duration for the incoming stream, and duration after reattachment for
the switch path. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarCompletionContinuation
    (state : Fin 2) : GN21AcceptedWinnerPostRaceCalendarInput ->
      GN21SwitchFirstJointContinuation := fun z =>
  let switchGaps := RawTwoStateCTMC.switchGapsAfterPairAtTime state
    (z.1, max 0 z.2.2.1)
  let active := AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
    (fun duration : Real => max 0 duration) ((z.2.2.1, z.2.2.2.1.1), z.2.2.2.1.2)
  let incoming := AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
    (fun time : Real => max 0 time) ((z.2.1 + z.2.2.1, z.2.2.2.2.1), z.2.2.2.2.2)
  (active, ((switchGaps 0, switchGaps 1), incoming))

/-- Advance the full literal accepted-winner continuation to the selected
trip's calendar completion and reassemble it in fixed raw-seed labels.  This
is a deterministic source map, not a new sample. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarCompletionSeed
    (state : Fin 2) : GN21AcceptedWinnerPostRaceCalendarInput -> GN21RawCycleSeed :=
  gn21RawCycleSeedOfStateContinuation state ∘
    gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state

theorem measurable_gn21AcceptedWinnerPostRaceCalendarCompletionContinuation
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state) := by
  let switchInput : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((Nat -> Real) × (Nat -> Real)) × Real := fun z =>
    (z.1, max 0 z.2.2.1)
  let activeInput : GN21AcceptedWinnerPostRaceCalendarInput ->
      (Real × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.2.2.1, z.2.2.2.1.1), z.2.2.2.1.2)
  let incomingInput : GN21AcceptedWinnerPostRaceCalendarInput ->
      (Real × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.2.1 + z.2.2.1, z.2.2.2.2.1), z.2.2.2.2.2)
  have hswitchInput : Measurable switchInput :=
    measurable_fst.prodMk
      (measurable_const.max
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hactiveInput : Measurable activeInput :=
    (((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))))).prodMk
      (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd)))))
  have hincomingInput : Measurable incomingInput :=
    (((measurable_fst.comp measurable_snd).add
      (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))).prodMk
      (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hswitch : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      RawTwoStateCTMC.switchGapsAfterPairAtTime state (switchInput z)) :=
    (RawTwoStateCTMC.measurable_switchGapsAfterPairAtTime state).comp hswitchInput
  have hactive : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun duration : Real => max 0 duration) (activeInput z)) :=
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun duration : Real => max 0 duration)
      (measurable_const.max measurable_id)).comp hactiveInput
  have hincoming : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun time : Real => max 0 time) (incomingInput z)) :=
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun time : Real => max 0 time)
      (measurable_const.max measurable_id)).comp hincomingInput
  exact hactive.prodMk
    (((((measurable_pi_apply 0).comp hswitch).prodMk
      ((measurable_pi_apply 1).comp hswitch))).prodMk hincoming)

theorem measurable_gn21AcceptedWinnerPostRaceCalendarCompletionSeed
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state) := by
  exact (measurable_gn21RawCycleSeedOfStateContinuation state).comp
    (measurable_gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state)

/-- Before discarding the accepted-arrival elapsed time and selected duration,
retain the literal post-race switch pair together with both marked-arrival
tails residualized at their actual completion clocks.  This is the source
coordinate needed to carry the completion endpoint jointly with the next
raw seed. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarResidualSourceInput
    (state : Fin 2) : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) :=
  fun z =>
    (((z.1, (z.2.1, z.2.2.1)),
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun time : Real => max 0 time)
        ((z.2.1 + z.2.2.1, z.2.2.2.2.1), z.2.2.2.2.2)),
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun duration : Real => max 0 duration)
        ((z.2.2.1, z.2.2.2.1.1), z.2.2.2.1.2))

/-- The literal accepted-branch subcycle time read from its retained calendar
source coordinate.  The duration `max` only totalizes values outside the
positive selected-trip support. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarResidualSourceTime
    (state : Fin 2) :
    ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) -> Real :=
  fun z => z.1.1.2.1 + max 0 z.1.1.2.2

theorem measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceTime
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarResidualSourceTime state) := by
  exact (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).add
    (measurable_const.max
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))

/-- On the positive selected-duration carrier, the retained accepted-branch
time is the literal accepted arrival time plus the selected duration. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceTime_eq_acceptedCalendarCompletionTime
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (hduration : 0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) :
    gn21AcceptedWinnerPostRaceCalendarResidualSourceTime state
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
        (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)) =
      gn21RawAcceptedCalendarCompletionTime state sigma seed := by
  simp only [gn21AcceptedWinnerPostRaceCalendarResidualSourceTime,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceInput,
    gn21RawAcceptedWinnerPostRaceCalendarInput,
    gn21RawAcceptedWinnerFullResidualInput,
    gn21RawAcceptedWinnerFullRaceInput,
    gn21RawAcceptedArrivalTimeMarkTailsWithContinuation,
    Function.comp_apply,
    AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux,
    AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail,
    gn21RawAcceptedCalendarCompletionTime,
    gn21RawPostThinningRaceSeed]
  rw [max_eq_right hduration]

/-- The selected-trip coordinate retained by the accepted calendar source is
the literal selected mark of the original raw seed. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceTrip_eq_rawSelectedTrip
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
      (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)).1.1.2.2 =
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
  rfl

/-- The accepted source retains the literal competing-race holding time before
any calendar-completion residualization. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceRaceTime_eq_rawMinimum
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (haccepted : seed ∈ gn21RawPostThinningRaceAcceptedFirst state sigma) :
    (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
      (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)).1.1.2.1 =
      gn21RawPostThinningRaceMinimum state sigma seed := by
  have hle : (gn21RawPostThinningRaceSeed state sigma seed).1 ≤
      (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
    exact le_of_not_gt (by
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using haccepted)
  have hle' : AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime
      (gn21ArrivalClockIndex state) state sigma seed ≤
      gn21RawCycleClock (RawTwoStateCTMC.switchClockIndex state) 0 seed := by
    simpa [gn21RawPostThinningRaceSeed] using hle
  simp [gn21AcceptedWinnerPostRaceCalendarResidualSourceInput,
    gn21RawAcceptedWinnerPostRaceCalendarInput,
    gn21RawAcceptedWinnerFullResidualInput,
    gn21RawAcceptedWinnerFullRaceInput,
    gn21RawAcceptedArrivalTimeMarkTailsWithContinuation,
    Function.comp_apply,
    AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux,
    gn21RawPostThinningRaceMinimum,
    AppliedModelingLib.Probability.exponentialRaceMinimum,
    gn21RawPostThinningRaceSeed, min_eq_left hle']

theorem measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state) := by
  let incomingInput : GN21AcceptedWinnerPostRaceCalendarInput ->
      (Real × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.2.1 + z.2.2.1, z.2.2.2.2.1), z.2.2.2.2.2)
  let activeInput : GN21AcceptedWinnerPostRaceCalendarInput ->
      (Real × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.2.2.1, z.2.2.2.1.1), z.2.2.2.1.2)
  have hhead : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      (z.1, (z.2.1, z.2.2.1))) := by
    exact measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hincomingInput : Measurable incomingInput := by
    exact (((measurable_fst.comp measurable_snd).add
      (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))).prodMk
      (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hactiveInput : Measurable activeInput := by
    exact (((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))))).prodMk
      (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd)))))
  have hincoming : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun time : Real => max 0 time) (incomingInput z)) :=
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun time : Real => max 0 time)
      (measurable_const.max measurable_id)).comp hincomingInput
  have hactive : Measurable (fun z : GN21AcceptedWinnerPostRaceCalendarInput =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun duration : Real => max 0 duration) (activeInput z)) :=
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun duration : Real => max 0 duration)
      (measurable_const.max measurable_id)).comp hactiveInput
  simpa [gn21AcceptedWinnerPostRaceCalendarResidualSourceInput, incomingInput, activeInput] using
    (hhead.prodMk hincoming).prodMk hactive

/-- The totalized accepted-winner calendar-completion continuation has the
ordinary state-continuation product law.  The `max` maps in the definition
only totalize off-support real inputs; all source times are later identified
with their literal nonnegative calendar values. -/
theorem map_gn21AcceptedWinnerPostRaceCalendarCompletionContinuation
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state)
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod
          (selectedLaw.prod (activeLaw.prod incomingLaw)))) =
      gn21StateContinuationMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let B := W.prod (T.prod Q)
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let incomingSource := ((B.prod A).prod H).prod N
  let incomingOutput := (B.prod I).prod A
  let activeSource := ((B.prod I).prod G).prod M
  let activeOutput := (B.prod I).prod A
  let rest := (T.prod Q).prod (I.prod A)
  let switchOutput := rest.prod
    (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W)
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure G :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure incomingSource := by
    dsimp [incomingSource]
    infer_instance
  letI : IsProbabilityMeasure incomingOutput := by
    dsimp [incomingOutput]
    infer_instance
  letI : IsProbabilityMeasure activeSource := by
    dsimp [activeSource]
    infer_instance
  letI : IsProbabilityMeasure activeOutput := by
    dsimp [activeOutput]
    infer_instance
  letI : IsProbabilityMeasure rest := by
    dsimp [rest]
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) :=
    Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure switchOutput := by
    dsimp [switchOutput]
    infer_instance
  let incomingReorder : GN21AcceptedWinnerPostRaceCalendarInput ->
      (((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × (Nat -> Real)) ×
        (Nat -> TripLength) := fun z =>
    ((((z.1, (z.2.1, z.2.2.1)), z.2.2.2.1), z.2.2.2.2.1), z.2.2.2.2.2)
  let p1 := (measurePreserving_prodAssoc W T (Q.prod (A.prod I))).symm
  let p2 := (measurePreserving_prodAssoc (W.prod T) Q (A.prod I)).symm
  let p3 := MeasurePreserving.prod (measurePreserving_prodAssoc W T Q)
    (MeasurePreserving.id (A.prod I))
  let p4 := MeasurePreserving.prod (MeasurePreserving.id B)
    (measurePreserving_prodAssoc A H N).symm
  let p5 := (measurePreserving_prodAssoc B (A.prod H) N).symm
  let p6 := MeasurePreserving.prod (measurePreserving_prodAssoc B A H).symm
    (MeasurePreserving.id N)
  have hincomingReorder : MeasurePreserving incomingReorder source incomingSource := by
    simpa [incomingReorder, source, incomingSource, B, A, I] using
      (p6.comp (p5.comp (p4.comp (p3.comp (p2.comp p1)))))
  let incomingTime : ((Nat -> Real) × (Nat -> Real)) × (Real × TripLength) -> Real :=
    fun b => max 0 (b.2.1 + b.2.2)
  have hincomingTime : Measurable incomingTime :=
    measurable_const.max
      ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd))
  have hincomingGeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_withCompanion_joint_hasLaw
      B A (gn21CycleMarkLaw muI muJ other) hincomingRate incomingTime hincomingTime
      (fun _ => le_max_left _ _)
  let afterIncoming : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) := fun z =>
    let y := incomingReorder z
    ((y.1.1.1,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        incomingTime ((y.1.1.1, y.1.2), y.2)), y.1.1.2)
  have hafterIncoming : HasLaw afterIncoming incomingOutput source := by
    simpa [afterIncoming, incomingReorder, incomingOutput, incomingSource, B, A, I, H, N,
      incomingTime] using hincomingGeneric.comp hincomingReorder.hasLaw
  let activeReorder : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      (((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.1, z.2.1), z.2.2)
  have hactiveReorder : MeasurePreserving activeReorder incomingOutput activeSource := by
    simpa [activeReorder, incomingOutput, activeSource, B, A, I] using
      (measurePreserving_prodAssoc (B.prod I) G M).symm
  let activeTime : (((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength)) -> Real := fun b => max 0 b.1.2.2
  have hactiveTime : Measurable activeTime :=
    measurable_const.max
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hactiveGeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_joint_hasLaw
      (B.prod I) (gn21CycleMarkLaw muI muJ state) hactiveRate activeTime hactiveTime
      (fun _ => le_max_left _ _) id measurable_id
  let afterActive : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) := fun z =>
    let y := activeReorder (afterIncoming z)
    (y.1.1,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        activeTime ((y.1.1, y.1.2), y.2))
  have hafterActive : HasLaw afterActive activeOutput source := by
    simpa [afterActive, activeReorder, activeOutput, activeSource, B, A, I, G, M,
      activeTime] using hactiveGeneric.comp (hactiveReorder.hasLaw.comp hafterIncoming)
  let switchReorder : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      ((Nat -> Real) × (Nat -> Real)) ×
        ((Real × TripLength) × (((Nat -> Real) × (Nat -> TripLength)) ×
          ((Nat -> Real) × (Nat -> TripLength)))) := fun z =>
    (z.1.1.1, (z.1.1.2, (z.1.2, z.2)))
  have hswitchReorder : MeasurePreserving switchReorder activeOutput (W.prod rest) := by
    simpa [switchReorder, activeOutput, rest, B, I, A] using
      ((measurePreserving_prodAssoc W (T.prod Q) (I.prod A)).comp
        (measurePreserving_prodAssoc B I A))
  let switchTime : (Real × TripLength) × (((Nat -> Real) × (Nat -> TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) -> Real := fun r => max 0 r.1.2
  have hswitchTime : Measurable switchTime :=
    measurable_const.max (measurable_snd.comp measurable_fst)
  have hswitchGeneric := RawTwoStateCTMC.switchGapsAfterPairAtTime_withExternal_hasLaw
    switchIJ switchJI hswitchIJ hswitchJI rest switchTime hswitchTime
    (fun _ => le_max_left _ _) state
  let afterSwitch : GN21AcceptedWinnerPostRaceCalendarInput ->
      (((Real × TripLength) × (((Nat -> Real) × (Nat -> TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength)))) × (Fin 2 -> Nat -> Real)) := fun z =>
    let y := switchReorder (afterActive z)
    (y.2, RawTwoStateCTMC.switchGapsAfterPairAtTime state (y.1, switchTime y.2))
  have hafterSwitch : HasLaw afterSwitch switchOutput source := by
    simpa [afterSwitch, switchReorder, switchOutput, rest, W, switchTime] using
      hswitchGeneric.comp (hswitchReorder.hasLaw.comp hafterActive)
  let statePair : (Fin 2 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) :=
    fun gaps => (gaps 0, gaps 1)
  have hstatePair : Measurable statePair :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hstatePairLaw : Measure.map statePair
      (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) = W := by
    calc
      Measure.map statePair
          (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) =
          Measure.map (statePair ∘
            AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair) W := by
              rw [Measure.map_map hstatePair
                AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair]
      _ = Measure.map id W := by
        rfl
      _ = W := Measure.map_id
  let dropTime : (Real × TripLength) × (((Nat -> Real) × (Nat -> TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) ->
      ((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)) :=
    fun r => r.2
  have hdropTime : Measure.map dropTime rest = I.prod A := by
    simpa [dropTime, rest] using (Measure.map_snd_prod (T.prod Q) (I.prod A))
  let finalReorder : (((Nat -> Real) × (Nat -> TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> Real)) ->
      ((Nat -> Real) × (Nat -> TripLength)) ×
        (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength))) := fun z =>
    (z.1.2, (z.2, z.1.1))
  let finalMap : (((Real × TripLength) × (((Nat -> Real) × (Nat -> TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength)))) × (Fin 2 -> Nat -> Real)) ->
      GN21SwitchFirstJointContinuation := fun z =>
    finalReorder (dropTime z.1, statePair z.2)
  have hfinalReorder : MeasurePreserving finalReorder
      ((I.prod A).prod W) (A.prod (W.prod I)) := by
    let swapIA : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) ×
          ((Nat -> Real) × (Nat -> TripLength)) ->
          ((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))
        (I.prod A) (A.prod I) := ⟨measurable_swap, Measure.prod_swap⟩
    let swapIW : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> Real)) ->
          ((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))
        (I.prod W) (W.prod I) := ⟨measurable_swap, Measure.prod_swap⟩
    let p1 := MeasurePreserving.prod swapIA (MeasurePreserving.id W)
    let p2 := measurePreserving_prodAssoc A I W
    let p3 := MeasurePreserving.prod (MeasurePreserving.id A) swapIW
    simpa [finalReorder] using (p3.comp (p2.comp p1))
  have hfinalMapMeas : Measurable finalMap :=
    hfinalReorder.measurable.comp (measurable_snd.prodMap hstatePair)
  have hfinalMap : Measure.map finalMap switchOutput = A.prod (W.prod I) := by
    calc
      Measure.map finalMap switchOutput =
          Measure.map finalReorder
            (Measure.map (Prod.map dropTime statePair) switchOutput) := by
              rw [show finalMap = finalReorder ∘ Prod.map dropTime statePair by rfl,
                Measure.map_map hfinalReorder.measurable
                  (measurable_snd.prodMap hstatePair)]
      _ = Measure.map finalReorder ((I.prod A).prod W) := by
        rw [show switchOutput = rest.prod
          (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) by rfl,
          ← Measure.map_prod_map rest
            (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W)
            measurable_snd hstatePair,
          hdropTime, hstatePairLaw]
      _ = A.prod (W.prod I) := hfinalReorder.map_eq
  change Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state) source =
    A.prod (W.prod I)
  calc
    Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state) source =
        Measure.map finalMap (Measure.map afterSwitch source) := by
          rw [show gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state =
            finalMap ∘ afterSwitch by rfl,
            AEMeasurable.map_map_of_aemeasurable hfinalMapMeas.aemeasurable
              hafterSwitch.aemeasurable]
    _ = Measure.map finalMap switchOutput := by rw [hafterSwitch.map_eq]
    _ = A.prod (W.prod I) := hfinalMap

/-- The retained post-race switch pair, elapsed time, selected duration, and
both completion-residual marked-arrival inputs have their literal product
law.  Keeping the elapsed and duration coordinates here is essential: the
completion endpoint will be read from the same switch pair in the subsequent
joint state--seed argument. -/
theorem map_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    Measure.map (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state)
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod
          (selectedLaw.prod (activeLaw.prod incomingLaw)))) =
      ((switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw)).prod incomingLaw).prod
        activeLaw := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let B := W.prod (T.prod Q)
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let incomingSource := ((B.prod A).prod H).prod N
  let incomingOutput := (B.prod I).prod A
  let activeSource := ((B.prod I).prod G).prod M
  let activeOutput := (B.prod I).prod A
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure G :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure incomingSource := by
    dsimp [incomingSource]
    infer_instance
  letI : IsProbabilityMeasure incomingOutput := by
    dsimp [incomingOutput]
    infer_instance
  letI : IsProbabilityMeasure activeSource := by
    dsimp [activeSource]
    infer_instance
  letI : IsProbabilityMeasure activeOutput := by
    dsimp [activeOutput]
    infer_instance
  let incomingReorder : GN21AcceptedWinnerPostRaceCalendarInput ->
      (((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × (Nat -> Real)) ×
        (Nat -> TripLength) := fun z =>
    ((((z.1, (z.2.1, z.2.2.1)), z.2.2.2.1), z.2.2.2.2.1), z.2.2.2.2.2)
  let p1 := (measurePreserving_prodAssoc W T (Q.prod (A.prod I))).symm
  let p2 := (measurePreserving_prodAssoc (W.prod T) Q (A.prod I)).symm
  let p3 := MeasurePreserving.prod (measurePreserving_prodAssoc W T Q)
    (MeasurePreserving.id (A.prod I))
  let p4 := MeasurePreserving.prod (MeasurePreserving.id B)
    (measurePreserving_prodAssoc A H N).symm
  let p5 := (measurePreserving_prodAssoc B (A.prod H) N).symm
  let p6 := MeasurePreserving.prod (measurePreserving_prodAssoc B A H).symm
    (MeasurePreserving.id N)
  have hincomingReorder : MeasurePreserving incomingReorder source incomingSource := by
    simpa [incomingReorder, source, incomingSource, B, A, I] using
      (p6.comp (p5.comp (p4.comp (p3.comp (p2.comp p1)))))
  let incomingTime : ((Nat -> Real) × (Nat -> Real)) × (Real × TripLength) -> Real :=
    fun b => max 0 (b.2.1 + b.2.2)
  have hincomingTime : Measurable incomingTime :=
    measurable_const.max
      ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd))
  have hincomingGeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_withCompanion_joint_hasLaw
      B A (gn21CycleMarkLaw muI muJ other) hincomingRate incomingTime hincomingTime
      (fun _ => le_max_left _ _)
  let afterIncoming : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) := fun z =>
    let y := incomingReorder z
    ((y.1.1.1,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        incomingTime ((y.1.1.1, y.1.2), y.2)), y.1.1.2)
  have hafterIncoming : HasLaw afterIncoming incomingOutput source := by
    simpa [afterIncoming, incomingReorder, incomingOutput, incomingSource, B, A, I, H, N,
      incomingTime] using hincomingGeneric.comp hincomingReorder.hasLaw
  let activeReorder : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      (((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((z.1, z.2.1), z.2.2)
  have hactiveReorder : MeasurePreserving activeReorder incomingOutput activeSource := by
    simpa [activeReorder, incomingOutput, activeSource, B, A, I] using
      (measurePreserving_prodAssoc (B.prod I) G M).symm
  let activeTime : (((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength)) -> Real := fun b => max 0 b.1.2.2
  have hactiveTime : Measurable activeTime :=
    measurable_const.max
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hactiveGeneric :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_joint_hasLaw
      (B.prod I) (gn21CycleMarkLaw muI muJ state) hactiveRate activeTime hactiveTime
      (fun _ => le_max_left _ _) id measurable_id
  let afterActive : GN21AcceptedWinnerPostRaceCalendarInput ->
      ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
        ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) := fun z =>
    let y := activeReorder (afterIncoming z)
    (y.1.1,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        activeTime ((y.1.1, y.1.2), y.2))
  have hafterActive : HasLaw afterActive activeOutput source := by
    simpa [afterActive, activeReorder, activeOutput, activeSource, B, I, A, G, M,
      activeTime] using hactiveGeneric.comp (hactiveReorder.hasLaw.comp hafterIncoming)
  change Measure.map (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state) source =
    activeOutput
  simpa [gn21AcceptedWinnerPostRaceCalendarResidualSourceInput, afterActive, activeReorder,
    afterIncoming, incomingReorder, incomingTime, activeTime] using hafterActive.map_eq

/-- Read the calendar-completion CTMC endpoint from the retained post-race
switch pair and selected duration.  The input already begins at the accepted
arrival, so only the selected duration advances that pair. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint
    (state : Fin 2) :
    ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) -> Fin 2 :=
  fun z => AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
    (z.1.1.1, max 0 z.1.1.2.2)

/-- Reassemble the next raw seed from the retained marked-arrival residuals
and the literal future switch tail at the same completion clock. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed
    (state : Fin 2) :
    ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      GN21RawCycleSeed := fun z =>
  let future := RawTwoStateCTMC.switchGapsAfterPairAtTime state
    (z.1.1.1, max 0 z.1.1.2.2)
  gn21RawCycleSeedOfStateContinuation state
    (z.2, ((future 0, future 1), z.1.2))

theorem measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state) := by
  let input : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      ((Nat -> Real) × (Nat -> Real)) × Real := fun z =>
    (z.1.1.1, max 0 z.1.1.2.2)
  have hinput : Measurable input := by
    exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_const.max
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  simpa [gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint, input] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp hinput

theorem measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state) := by
  let input : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      ((Nat -> Real) × (Nat -> Real)) × Real := fun z =>
    (z.1.1.1, max 0 z.1.1.2.2)
  have hinput : Measurable input := by
    exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_const.max
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  let future : ((((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
      ((Nat -> Real) × (Nat -> TripLength)) -> Fin 2 -> Nat -> Real := fun z =>
    RawTwoStateCTMC.switchGapsAfterPairAtTime state (input z)
  have hfuture : Measurable future :=
    (RawTwoStateCTMC.measurable_switchGapsAfterPairAtTime state).comp hinput
  have hcontinuation : Measurable (fun z : ((((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
      ((Nat -> Real) × (Nat -> TripLength)) =>
      (z.2, (((future z) 0, (future z) 1), z.1.2))) := by
    exact measurable_snd.prodMk
      (((((measurable_pi_apply 0).comp hfuture).prodMk
        ((measurable_pi_apply 1).comp hfuture))).prodMk
        (measurable_snd.comp measurable_fst))
  simpa [gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed, input, future] using
    (measurable_gn21RawCycleSeedOfStateContinuation state).comp hcontinuation

/-- Reassemble a raw continuation seed from the tail factor in the accepted
history/tail product law.  Its argument contains the two retained marked
arrival inputs and the completed switch residual, with no history coordinate
discarded or resampled. -/
noncomputable def gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed
    (state : Fin 2) :
    (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
      (Fin 2 -> Nat -> Real) -> GN21RawCycleSeed := fun z =>
  gn21RawCycleSeedOfStateContinuation state
    (z.1.2, ((z.2 0, z.2 1), z.1.1))

theorem measurable_gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed
    (state : Fin 2) :
    Measurable (gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state) := by
  have hinput : Measurable (fun z :
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
        (Fin 2 -> Nat -> Real) =>
      (z.1.2, ((z.2 0, z.2 1), z.1.1))) := by
    exact (measurable_snd.comp measurable_fst).prodMk
      (((((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd))).prodMk
        (measurable_fst.comp measurable_fst))
  exact (measurable_gn21RawCycleSeedOfStateContinuation state).comp hinput

/-- The literal reassembly of an accepted-history tail has the original raw
seed law.  This is only a coordinate reordering and the existing
state-continuation seed law; it does not sample a new continuation. -/
theorem map_gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state))).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    let switchTailLaw := Measure.map
      AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair switchLaw
    Measure.map (gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state)
      ((incomingLaw.prod activeLaw).prod switchTailLaw) =
      gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let A :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let R := I.prod A
  let switchTailLaw := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    infer_instance
  letI : IsProbabilityMeasure switchTailLaw := by
    dsimp [switchTailLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let tailPair : (Fin 2 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) := fun f =>
    (f 0, f 1)
  have htailPair : Measurable tailPair := by
    exact (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have htailPair_comp : tailPair ∘
      AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair = id := by
    funext pair
    rcases pair with ⟨left, right⟩
    rfl
  have htailPairLaw : Measure.map tailPair switchTailLaw = W := by
    change Measure.map tailPair
      (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) = W
    calc
      Measure.map tailPair
          (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) =
          Measure.map (tailPair ∘
            AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair) W := by
              rw [Measure.map_map htailPair
                AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair]
      _ = Measure.map id W := by rw [htailPair_comp]
      _ = W := Measure.map_id
  let htailPairMeasurePreserving : MeasurePreserving tailPair switchTailLaw W :=
    ⟨htailPair, htailPairLaw⟩
  let reorderSeed :
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
        (Fin 2 -> Nat -> Real) -> GN21SwitchFirstJointContinuation := fun z =>
    (z.1.2, ((z.2 0, z.2 1), z.1.1))
  have hreorderSeed : Measurable reorderSeed := by
    exact (measurable_snd.comp measurable_fst).prodMk
      (((((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd))).prodMk
        (measurable_fst.comp measurable_fst))
  have hseedReorder : MeasurePreserving reorderSeed (R.prod switchTailLaw)
      (A.prod (W.prod I)) := by
    let p1 := measurePreserving_prodAssoc I A switchTailLaw
    let swapAF : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real) ->
          (Fin 2 -> Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)))
        (A.prod switchTailLaw) (switchTailLaw.prod A) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let p2 := MeasurePreserving.prod (MeasurePreserving.id I) swapAF
    let p3 := (measurePreserving_prodAssoc I switchTailLaw A).symm
    let p4 : MeasurePreserving
        (Prod.swap : ((((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real)) ×
          ((Nat -> Real) × (Nat -> TripLength))) ->
          (((Nat -> Real) × (Nat -> TripLength)) ×
            (((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real))))
        ((I.prod switchTailLaw).prod A) (A.prod (I.prod switchTailLaw)) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let swapFI : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real) ->
          (Fin 2 -> Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)))
        (I.prod switchTailLaw) (switchTailLaw.prod I) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let p5 := MeasurePreserving.prod (MeasurePreserving.id A) swapFI
    let p6 := MeasurePreserving.prod (MeasurePreserving.id A)
      (MeasurePreserving.prod htailPairMeasurePreserving (MeasurePreserving.id I))
    simpa [reorderSeed, R, A, I, switchTailLaw, tailPair] using
      (p6.comp (p5.comp (p4.comp (p3.comp (p2.comp p1)))))
  calc
    Measure.map (gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state)
        (R.prod switchTailLaw) =
        Measure.map (gn21RawCycleSeedOfStateContinuation state)
          (Measure.map reorderSeed (R.prod switchTailLaw)) := by
            rw [show gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state =
              gn21RawCycleSeedOfStateContinuation state ∘ reorderSeed by rfl,
              Measure.map_map (measurable_gn21RawCycleSeedOfStateContinuation state) hreorderSeed]
    _ = Measure.map (gn21RawCycleSeedOfStateContinuation state)
        (A.prod (W.prod I)) := by rw [hseedReorder.map_eq]
    _ = P := by
      simpa [P, A, W, I] using
        (map_gn21RawCycleSeedOfStateContinuation
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state)

/-- The retained-coordinate next-seed construction is definitionally the
totalized calendar-completion seed after applying the two literal
marked-arrival residual maps. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed_eq_completionSeed
    (state : Fin 2) (z : GN21AcceptedWinnerPostRaceCalendarInput) :
    gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z) =
      gn21AcceptedWinnerPostRaceCalendarCompletionSeed state z := by
  rfl

/-- On the factored accepted-winner calendar input, the literal completion
endpoint and the literal next raw seed have the endpoint marginal times the
original raw-seed law.  This is the joint source kernel needed for iteration;
it is obtained by retaining both marked residuals and applying the CTMC
endpoint/companion/future-tail transport, not by a restart assumption. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceJoint_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    let source := switchLaw.prod
      ((ProbabilityTheory.expMeasure (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))).prod
        (selectedLaw.prod (activeLaw.prod incomingLaw)))
    let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    HasLaw (fun z =>
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z),
      gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z)))
      (stateLaw.prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) source := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let E := T.prod Q
  let R := I.prod A
  let B := W.prod E
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let retainedLaw := (B.prod I).prod A
  let genericSource := W.prod (E.prod R)
  let switchTailLaw := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W
  let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2)) B
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure G :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure retainedLaw := by
    dsimp [retainedLaw]
    infer_instance
  letI : IsProbabilityMeasure genericSource := by
    dsimp [genericSource]
    infer_instance
  letI : IsProbabilityMeasure switchTailLaw := by
    dsimp [switchTailLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure stateLaw := by
    dsimp [stateLaw]
    exact Measure.isProbabilityMeasure_map
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp
        (measurable_fst.prodMk
          (measurable_const.max (measurable_snd.comp measurable_snd)))).aemeasurable
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hretained : HasLaw (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state)
      retainedLaw source := by
    refine ⟨(measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state).aemeasurable, ?_⟩
    simpa [retainedLaw, source, W, T, Q, A, I, activeRate, acceptedRate, switchRate,
      G, M, H, N, other] using
      (map_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  let reorderRetained : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      ((Nat -> Real) × (Nat -> Real)) × ((Real × TripLength) ×
        (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))) := fun z =>
    (z.1.1.1, (z.1.1.2, (z.1.2, z.2)))
  let p1 := measurePreserving_prodAssoc B I A
  let p2 := measurePreserving_prodAssoc W E (I.prod A)
  have hreorderRetained : MeasurePreserving reorderRetained retainedLaw genericSource := by
    simpa [reorderRetained, retainedLaw, genericSource, B, E, R, I, A] using (p2.comp p1)
  have hgeneric := RawTwoStateCTMC.stateAtPairAtTime_companion_switchGapsAfter_hasLaw
    switchIJ switchJI hswitchIJ hswitchJI E R
    (fun z : Real × TripLength => max 0 z.2)
    (measurable_const.max measurable_snd) (fun _ => le_max_left _ _) state
  let tailPair : (Fin 2 -> Nat -> Real) -> (Nat -> Real) × (Nat -> Real) := fun f =>
    (f 0, f 1)
  have htailPair : Measurable tailPair := by
    exact (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have htailPair_comp : tailPair ∘
      AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair = id := by
    funext pair
    rcases pair with ⟨left, right⟩
    rfl
  have htailPairLaw : Measure.map tailPair switchTailLaw = W := by
    change Measure.map tailPair
      (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) = W
    calc
      Measure.map tailPair
          (Measure.map AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W) =
          Measure.map (tailPair ∘
            AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair) W := by
              rw [Measure.map_map htailPair
                AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair]
      _ = Measure.map id W := by rw [htailPair_comp]
      _ = W := Measure.map_id
  let htailPairMeasurePreserving : MeasurePreserving tailPair switchTailLaw W :=
    ⟨htailPair, htailPairLaw⟩
  let reorderSeed :
      (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
        (Fin 2 -> Nat -> Real) -> GN21SwitchFirstJointContinuation := fun z =>
    (z.1.2, ((z.2 0, z.2 1), z.1.1))
  have hreorderSeed : Measurable reorderSeed := by
    exact (measurable_snd.comp measurable_fst).prodMk
      (((((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd))).prodMk
        (measurable_fst.comp measurable_fst))
  let reassemble := gn21RawCycleSeedOfStateContinuation state ∘ reorderSeed
  have hreassemble : Measurable reassemble := by
    exact (measurable_gn21RawCycleSeedOfStateContinuation state).comp hreorderSeed
  have hseedReorder : MeasurePreserving reorderSeed (R.prod switchTailLaw)
      (A.prod (W.prod I)) := by
    let p1 := measurePreserving_prodAssoc I A switchTailLaw
    let swapAF : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real) ->
          (Fin 2 -> Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)))
        (A.prod switchTailLaw) (switchTailLaw.prod A) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let p2 := MeasurePreserving.prod (MeasurePreserving.id I) swapAF
    let p3 := (measurePreserving_prodAssoc I switchTailLaw A).symm
    let p4 : MeasurePreserving
        (Prod.swap :
          ((((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real)) ×
            ((Nat -> Real) × (Nat -> TripLength))) ->
          (((Nat -> Real) × (Nat -> TripLength)) ×
            (((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real))))
        ((I.prod switchTailLaw).prod A) (A.prod (I.prod switchTailLaw)) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let swapFI : MeasurePreserving
        (Prod.swap : ((Nat -> Real) × (Nat -> TripLength)) × (Fin 2 -> Nat -> Real) ->
          (Fin 2 -> Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)))
        (I.prod switchTailLaw) (switchTailLaw.prod I) :=
      ⟨measurable_swap, Measure.prod_swap⟩
    let p5 := MeasurePreserving.prod (MeasurePreserving.id A) swapFI
    let p6 := MeasurePreserving.prod (MeasurePreserving.id A)
      (MeasurePreserving.prod htailPairMeasurePreserving (MeasurePreserving.id I))
    simpa [reorderSeed, R, A, I, switchTailLaw, tailPair] using
      (p6.comp (p5.comp (p4.comp (p3.comp (p2.comp p1)))))
  have hseedLaw : Measure.map reassemble (R.prod switchTailLaw) = P := by
    calc
      Measure.map reassemble (R.prod switchTailLaw) =
          Measure.map (gn21RawCycleSeedOfStateContinuation state)
            (Measure.map reorderSeed (R.prod switchTailLaw)) := by
              rw [show reassemble = gn21RawCycleSeedOfStateContinuation state ∘ reorderSeed by rfl,
                Measure.map_map (measurable_gn21RawCycleSeedOfStateContinuation state)
                  hreorderSeed]
      _ = Measure.map (gn21RawCycleSeedOfStateContinuation state)
          (A.prod (W.prod I)) := by rw [hseedReorder.map_eq]
      _ = P := by
        simpa [P, A, W, I] using
          (map_gn21RawCycleSeedOfStateContinuation
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI state)
  letI : IsProbabilityMeasure (R.prod switchTailLaw) := by infer_instance
  let hseedMeasurePreserving : MeasurePreserving reassemble (R.prod switchTailLaw) P :=
    ⟨hreassemble, hseedLaw⟩
  let hpairReassemble := MeasurePreserving.prod (MeasurePreserving.id stateLaw)
    hseedMeasurePreserving
  have hjointGeneric : HasLaw (fun z =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.1.2),
        reassemble (z.2.2,
          RawTwoStateCTMC.switchGapsAfterPairAtTime state (z.1, max 0 z.2.1.2))))
      (stateLaw.prod P) genericSource := by
    simpa [stateLaw, switchTailLaw, genericSource, E, R, B, W, T, Q, I, A,
      reassemble] using hpairReassemble.hasLaw.fun_comp hgeneric
  have htoGeneric : HasLaw (reorderRetained ∘
      gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state) genericSource source :=
    hreorderRetained.hasLaw.fun_comp hretained
  simpa [source, stateLaw, genericSource, reorderRetained, reassemble,
    reorderSeed,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed] using
    hjointGeneric.fun_comp htoGeneric

/-- On the factored accepted-winner source, the literal completion endpoint
and the complete elapsed-race history factor from the untouched marked-arrival
and switch residuals.  The history retains both the winning-race time and the
selected duration so later time or reward summaries are measurable images of
this law rather than extra restart premises. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceHistoryTail_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    let source := switchLaw.prod
      ((ProbabilityTheory.expMeasure (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))).prod
        (selectedLaw.prod (activeLaw.prod incomingLaw)))
    let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2), z.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    let switchTailLaw := Measure.map
      AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair switchLaw
    HasLaw (fun z =>
      let r := gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z
      ((gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state r, r.1.1.2),
        ((r.1.2, r.2), RawTwoStateCTMC.switchGapsAfterPairAtTime state
          (r.1.1.1, max 0 r.1.1.2.2))) )
      (historyLaw.prod ((incomingLaw.prod activeLaw).prod switchTailLaw)) source := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let E := T.prod Q
  let R := I.prod A
  let B := W.prod E
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let retainedLaw := (B.prod I).prod A
  let genericSource := W.prod (E.prod R)
  let switchTailLaw := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W
  let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) B
  let targetTailLaw := R.prod switchTailLaw
  have hhistoryMap : Measurable (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp
      (measurable_fst.prodMk
        (measurable_const.max (measurable_snd.comp measurable_snd)))).prodMk measurable_snd
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure G :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsProbabilityMeasure retainedLaw := by
    dsimp [retainedLaw]
    infer_instance
  letI : IsProbabilityMeasure genericSource := by
    dsimp [genericSource]
    infer_instance
  letI : IsProbabilityMeasure switchTailLaw := by
    dsimp [switchTailLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistoryMap.aemeasurable
  letI : IsProbabilityMeasure targetTailLaw := by
    dsimp [targetTailLaw]
    infer_instance
  have hretained : HasLaw (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state)
      retainedLaw source := by
    refine ⟨(measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state).aemeasurable, ?_⟩
    simpa [retainedLaw, source, W, T, Q, A, I, activeRate, acceptedRate, switchRate,
      G, M, H, N, other] using
      (map_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  let reorderRetained : ((((Nat -> Real) × (Nat -> Real)) × (Real × TripLength)) ×
      ((Nat -> Real) × (Nat -> TripLength))) × ((Nat -> Real) × (Nat -> TripLength)) ->
      ((Nat -> Real) × (Nat -> Real)) × ((Real × TripLength) ×
        (((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength)))) := fun z =>
    (z.1.1.1, (z.1.1.2, (z.1.2, z.2)))
  let p1 := measurePreserving_prodAssoc B I A
  let p2 := measurePreserving_prodAssoc W E (I.prod A)
  have hreorderRetained : MeasurePreserving reorderRetained retainedLaw genericSource := by
    simpa [reorderRetained, retainedLaw, genericSource, B, E, R, I, A] using (p2.comp p1)
  have hgeneric := RawTwoStateCTMC.stateAtPairAtTime_history_companion_switchGapsAfter_hasLaw
    switchIJ switchJI hswitchIJ hswitchJI E R
    (fun z : Real × TripLength => max 0 z.2)
    (measurable_const.max measurable_snd) (fun _ => le_max_left _ _) state
  have htoGeneric : HasLaw (reorderRetained ∘
      gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state) genericSource source :=
    hreorderRetained.hasLaw.fun_comp hretained
  simpa [source, historyLaw, targetTailLaw, genericSource, reorderRetained,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceInput] using
    hgeneric.fun_comp htoGeneric

/-- On the factored accepted-winner source, the complete stopped history and
the reassembled literal next seed have product law.  The next seed is built
from the retained arrival and switch tails, so this is a joint history/seed
statement rather than a marginal restart law. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceHistoryNextSeed_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let activeLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate).prod
        (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state))
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    let source := switchLaw.prod
      ((ProbabilityTheory.expMeasure (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))).prod
        (selectedLaw.prod (activeLaw.prod incomingLaw)))
    let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2), z.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    HasLaw (fun z =>
      let r := gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z
      ((gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state r, r.1.1.2),
        gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state r))
      (historyLaw.prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) source := by
  dsimp
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let T := ProbabilityTheory.expMeasure
    (acceptedRate + gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (RawTwoStateCTMC.switchClockIndex state))
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) (W.prod (T.prod Q))
  let switchTailLaw := Measure.map
    AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair W
  let tailLaw := (I.prod A).prod switchTailLaw
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (RawTwoStateCTMC.switchClockIndex state) := by
    simp only [RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hincomingRate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex other) := by
    dsimp [other, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure G :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hactiveRate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure H :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hincomingRate
  letI : IsProbabilityMeasure N := by
    dsimp [N, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  letI : IsProbabilityMeasure switchTailLaw := by
    dsimp [switchTailLaw]
    exact Measure.isProbabilityMeasure_map
      AppliedModelingLib.Probability.TwoStateSwitching.measurable_twoStateGapsOfPair.aemeasurable
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
  have hhistoryMap : Measurable (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) := by
    exact ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp
      (measurable_fst.prodMk
        (measurable_const.max (measurable_snd.comp measurable_snd)))).prodMk measurable_snd
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistoryMap.aemeasurable
  let tailNext := gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state
  let pairNext : (Fin 2 × (Real × TripLength)) ×
      ((((Nat -> Real) × (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> TripLength))) ×
        (Fin 2 -> Nat -> Real)) ->
      (Fin 2 × (Real × TripLength)) × GN21RawCycleSeed := fun z => (z.1, tailNext z.2)
  have hhistoryTail : HasLaw (fun z =>
      let r := gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z
      ((gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state r, r.1.1.2),
        ((r.1.2, r.2), RawTwoStateCTMC.switchGapsAfterPairAtTime state
          (r.1.1.1, max 0 r.1.1.2.2))) )
      (historyLaw.prod tailLaw) source := by
    simpa [activeRate, acceptedRate, T, Q, G, M, A, W, other, H, N, I,
      source, historyLaw, switchTailLaw, tailLaw] using
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceHistoryTail_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have htailNextLaw : Measure.map tailNext tailLaw = P := by
    simpa [activeRate, G, M, A, W, other, H, N, I, switchTailLaw, tailLaw,
      tailNext, P] using
      (map_gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  let htailNextMP : MeasurePreserving tailNext tailLaw P :=
    ⟨measurable_gn21AcceptedWinnerPostRaceCalendarHistoryTailNextSeed state, htailNextLaw⟩
  let hpairNext : MeasurePreserving pairNext (historyLaw.prod tailLaw)
      (historyLaw.prod P) := by
    simpa [pairNext, Prod.map] using
      (MeasurePreserving.prod (MeasurePreserving.id historyLaw) htailNextMP)
  simpa [pairNext, tailNext,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed] using
    hpairNext.hasLaw.fun_comp hhistoryTail

/-- The retained-source endpoint is the accepted-winner restart endpoint once
the selected trip duration is on its source support.  This is a pathwise
coordinate identity, separate from the a.e. transport back to the direct raw
calendar path. -/
theorem gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint_eq_restartCompletionState
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (hduration : 0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed) :
    gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
        (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)) =
      gn21PostThinningRaceAcceptedWinnerRestartCompletionState state
        (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  simp only [gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint,
    gn21AcceptedWinnerPostRaceCalendarResidualSourceInput,
    gn21RawAcceptedWinnerPostRaceCalendarInput,
    gn21PostThinningRaceAcceptedWinnerRestartCompletionState,
    gn21RawPostThinningRaceAcceptedWinnerRestartSeed,
    gn21PostThinningRaceAcceptedWinnerRestartFactor,
    gn21RawAcceptedWinnerFullResidualInput,
    gn21RawAcceptedWinnerFullRaceInput,
    gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed,
    gn21RawPostThinningRaceWithSwitchTailSeed,
    Function.comp_apply,
    AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux,
    AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail,
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime,
    gn21RawAcceptedArrivalTimeMarkTailsWithContinuation]
  rw [max_eq_right hduration]

/-- The literal accepted-winner continuation, advanced to calendar completion
and then reassembled in raw labels.  Its `max` totalizations are removed on
the original source carrier by the subsequent source-a.e. comparison. -/
noncomputable def gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> GN21RawCycleSeed :=
  gn21AcceptedWinnerPostRaceCalendarCompletionSeed state ∘
    gn21RawAcceptedWinnerPostRaceCalendarInput state sigma

theorem measurable_gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma) := by
  exact (measurable_gn21AcceptedWinnerPostRaceCalendarCompletionSeed state).comp
    (measurable_gn21RawAcceptedWinnerPostRaceCalendarInput state sigma hsigma)

/-- On the accepted-winner source event, the totalized literal
calendar-completion continuation has the original raw-seed law, multiplied
only by the actual accepted-race probability.  This is the accepted half of
the one-step seed kernel before its source-a.e. identification with the
direct raw calendar observable. -/
theorem map_gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let p := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  have hpost : Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) = p • source := by
    simpa [P, activeRate, acceptedRate, switchRate, T, Q, G, M, A, W, H, N, I, source,
      p, other] using
      (map_gn21RawAcceptedWinnerPostRaceCalendarInput_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hcontinuation : Measure.map
      (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state) source =
      gn21StateContinuationMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state := by
    simpa [activeRate, acceptedRate, switchRate, T, Q, G, M, A, W, H, N, I, source, other] using
      (map_gn21AcceptedWinnerPostRaceCalendarCompletionContinuation
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hseed : Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state) source = P := by
    calc
      Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state) source =
          Measure.map (gn21RawCycleSeedOfStateContinuation state)
            (Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state) source) := by
              rw [gn21AcceptedWinnerPostRaceCalendarCompletionSeed,
                ← Measure.map_map (measurable_gn21RawCycleSeedOfStateContinuation state)
                  (measurable_gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state)]
      _ = Measure.map (gn21RawCycleSeedOfStateContinuation state)
          (gn21StateContinuationMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state) := by
            rw [hcontinuation]
      _ = P := by
        simpa [P] using (map_gn21RawCycleSeedOfStateContinuation
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state)
  change Measure.map (gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma)
    (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) = p • P
  calc
    Measure.map (gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state)
          (Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed,
                ← Measure.map_map
                  (measurable_gn21AcceptedWinnerPostRaceCalendarCompletionSeed state)
                  (measurable_gn21RawAcceptedWinnerPostRaceCalendarInput state sigma hsigma)]
    _ = Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state) (p • source) := by
          rw [hpost]
    _ = p • Measure.map (gn21AcceptedWinnerPostRaceCalendarCompletionSeed state) source := by
          rw [Measure.map_smul]
    _ = p • P := by rw [hseed]

/-- On the raw accepted-winner carrier, the totalized calendar-completion
candidate is almost surely the literal direct next seed.  The proof identifies
all three retained pieces jointly: the current marked tail, incoming marked
tail, and state-indexed future switch path.  It transports no strong-Markov
or independently refreshed continuation assumption. -/
theorem ae_gn21RawAcceptedCompletionNextCycleSeed_eq_postRaceCalendarCompletionSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)),
      gn21RawAcceptedCompletionNextCycleSeed state sigma seed =
        gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma seed := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      Q P := by
    simpa [P, Q] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonnegQ : ∀ᵐ duration ∂Q, 0 ≤ duration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hselectedNonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hselectedNonnegQ
  have hcurrent : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma),
      gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed =
        AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun _ : Unit => AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
          (((), AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
              (gn21ArrivalClockIndex state) state sigma seed),
            AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed) := by
    exact MeasureTheory.ae_restrict_of_ae
      (ae_gn21RawAcceptedCompletionMarkedArrivalResidual_current_eq_postAccepted
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hincoming : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma),
      (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma seed).2 =
        gn21RawAcceptedCompletionMarkedArrivalResidual state sigma
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed := by
    exact MeasureTheory.ae_restrict_of_ae
      (ae_gn21RawAcceptedCompletionIncomingResidualWithExternal_snd_eq
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hendpoint :=
    ae_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_eq_acceptedWinnerRestartCompletionEndpointFuture_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hswitch : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma),
      gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed =
        gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state
          (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
    filter_upwards [hendpoint] with seed hseed
    exact congrArg Prod.snd hseed
  filter_upwards [MeasureTheory.ae_restrict_of_ae hselectedNonneg,
    hcurrent, hincoming, hswitch] with seed hnonneg hcurrent hincoming hswitch
  let candidate := gn21AcceptedWinnerPostRaceCalendarCompletionContinuation state
    (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)
  have hactive : candidate.1 =
      gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed := by
    calc
      candidate.1 = AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun duration : TripLength => max 0 duration)
          (gn21RawPostAcceptedMarkedInput state sigma seed) := by rfl
      _ = AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun _ : Unit => AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
          (((), AcceptedArrivalTime.gn21RawPostFirstAcceptedArrivalGapTail
              (gn21ArrivalClockIndex state) state sigma seed),
            AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed) := by
          unfold AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          apply Prod.ext
          · simp [gn21RawPostAcceptedMarkedInput,
              AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail,
              max_eq_right hnonneg]
          · funext n
            simp [gn21RawPostAcceptedMarkedInput,
              AppliedModelingLib.Probability.IIDStream.externalIndexTail,
              max_eq_right hnonneg]
      _ = gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed := hcurrent.symm
  have hincoming' : candidate.2.2 =
      gn21RawAcceptedCompletionMarkedArrivalResidual state sigma
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed := by
    calc
      candidate.2.2 =
          (gn21RawAcceptedCompletionIncomingResidualWithExternal state sigma seed).2 := by rfl
      _ = _ := hincoming
  have hprojection :
      let z := gn21RawAcceptedWinnerFullResidualInput state sigma seed
      (z.1, (z.2.1, (z.2.2.1, z.2.2.2.1))) =
        gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma seed := by
    simp only [gn21RawAcceptedWinnerFullResidualInput,
      gn21RawAcceptedWinnerFullRaceInput,
      gn21RawAcceptedArrivalTimeMarkTailsWithContinuation,
      gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed,
      gn21RawPostThinningRaceWithSwitchTailSeed,
      Function.comp_apply,
      AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux]
  have hswitchCandidate : AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
      candidate.2.1 =
      gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state
        (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
    have hduration' : 0 ≤
        (gn21RawAcceptedArrivalTimeMarkTailsWithContinuation state sigma seed).1.1.2 := by
      simpa [gn21RawAcceptedArrivalTimeMarkTailsWithContinuation,
        gn21RawPostThinningRaceSeed] using hnonneg
    simp only [candidate, gn21AcceptedWinnerPostRaceCalendarCompletionContinuation,
      gn21RawAcceptedWinnerPostRaceCalendarInput,
      gn21RawAcceptedWinnerFullResidualInput,
      gn21RawPostThinningRaceAcceptedWinnerRestartSeed,
      gn21PostThinningRaceAcceptedWinnerRestartFactor,
      gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps,
      Function.comp_apply]
    rw [max_eq_right]
    · rw [show
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux
          (gn21RawAcceptedWinnerFullRaceInput state sigma seed)).2.2.2.1 =
          (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma seed).2.2.2 by
          simpa using congrArg (fun z => z.2.2.2) hprojection]
      rw [show
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux
          (gn21RawAcceptedWinnerFullRaceInput state sigma seed)).2.1 =
          (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma seed).2.1 by
          simpa using congrArg (fun z => z.2.1) hprojection]
      rw [show
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux
          (gn21RawAcceptedWinnerFullRaceInput state sigma seed)).2.2.1 =
          (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma seed).2.2.1 by
          simpa using congrArg (fun z => z.2.2.1) hprojection]
      unfold RawTwoStateCTMC.switchGapsAfterPairAtTime
      have hpair (g : Fin 2 -> Nat -> Real) :
          AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair
            (g 0, g 1) = g := by
        funext i n
        fin_cases i <;> rfl
      exact hpair _
    · simpa [gn21RawAcceptedWinnerFullRaceInput,
        gn21RawAcceptedArrivalTimeMarkTailsWithContinuation] using hduration'
  have hswitchPair : candidate.2.1 =
      ((gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 0,
        (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 1) := by
    apply Prod.ext
    · simpa [AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair] using
        congrFun (hswitchCandidate.trans hswitch.symm) 0
    · simpa [AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair] using
        congrFun (hswitchCandidate.trans hswitch.symm) 1
  have hdirect : gn21RawAcceptedCompletionNextCycleSeed state sigma seed =
      gn21RawCycleSeedOfStateContinuation state
        (gn21RawAcceptedCompletionMarkedArrivalResidual state sigma state seed,
          (((gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 0,
            (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed) 1),
          gn21RawAcceptedCompletionMarkedArrivalResidual state sigma
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed)) := by
    fin_cases state <;> rfl
  rw [hdirect]
  change gn21RawCycleSeedOfStateContinuation state _ =
    gn21RawCycleSeedOfStateContinuation state candidate
  congr 1
  apply Prod.ext
  · exact hactive.symm
  · apply Prod.ext
    · exact hswitchPair.symm
    · exact hincoming'.symm

/-- On the raw accepted-winner restriction, the literal subcycle time agrees
almost everywhere with the retained accepted-source time coordinate.  The
branch identity supplies the accepted carrier; selected-trip support removes
only the source's off-support `max` totalization. -/
theorem ae_gn21RawPostThinningRaceSubcycleTime_eq_postRaceCalendarResidualSourceTime_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)),
      gn21RawPostThinningRaceSubcycleTime state sigma seed =
        gn21AcceptedWinnerPostRaceCalendarResidualSourceTime state
          (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
            (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let S := gn21RawPostThinningRaceAcceptedFirst state sigma
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      Q P := by
    simpa [P, Q] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hnonnegQ : ∀ᵐ duration ∂Q, 0 ≤ duration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hnonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hnonnegQ
  have hS : MeasurableSet S := by
    simpa [S] using measurableSet_gn21RawPostThinningRaceAcceptedFirst state sigma hsigma
  filter_upwards [MeasureTheory.ae_restrict_of_ae hnonneg,
    MeasureTheory.ae_restrict_mem hS] with seed hnonneg haccepted
  calc
    gn21RawPostThinningRaceSubcycleTime state sigma seed =
        gn21RawAcceptedCalendarCompletionTime state sigma seed :=
      gn21RawPostThinningRaceSubcycleTime_eq_acceptedCalendarCompletionTime
        state sigma seed haccepted
    _ = gn21AcceptedWinnerPostRaceCalendarResidualSourceTime state
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
          (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)) :=
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceTime_eq_acceptedCalendarCompletionTime
        state sigma seed hnonneg).symm

/-- On the weak accepted-winner source event, the direct calendar-completion
state agrees almost everywhere with the endpoint read from the retained
post-race coordinate.  The only nondefinitional step is removal of the
off-support `max` totalization using the selected-duration support fact. -/
theorem ae_gn21RawPostThinningRaceCalendarCompletionState_eq_postRaceCalendarResidualSourceEndpoint_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)),
      gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
        gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state
          (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
            (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hselected : HasLaw (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      Q P := by
    simpa [P, Q] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hnonnegQ : ∀ᵐ duration ∂Q, 0 ≤ duration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun duration hmem => by
        have hpositive : 0 < duration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hnonneg : ∀ᵐ seed ∂P,
      0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
    (hselected.ae_iff (p := fun duration : TripLength => 0 ≤ duration)
      (by fun_prop)).mpr hnonnegQ
  have hrestart :=
    ae_gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  filter_upwards [MeasureTheory.ae_restrict_of_ae hnonneg, hrestart] with seed hnonneg hrestart
  exact hrestart.trans
    (gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint_eq_restartCompletionState
      state sigma seed hnonneg).symm

/-- The actual accepted-completion next seed has the original raw product law
on the weak accepted-winner source event, scaled exactly by the accepted-race
probability.  This is a transport through the preceding joint source-a.e.
identity, not a regenerative-cycle assertion. -/
theorem map_gn21RawAcceptedCompletionNextCycleSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawAcceptedCompletionNextCycleSeed state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  calc
    Measure.map (gn21RawAcceptedCompletionNextCycleSeed state sigma)
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
          (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma)
          ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
            (gn21RawPostThinningRaceAcceptedFirst state sigma)) := by
              apply Measure.map_congr
              exact ae_gn21RawAcceptedCompletionNextCycleSeed_eq_postRaceCalendarCompletionSeed_restrict
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
    _ = _ := map_gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass

/-- The actual accepted branch has the endpoint marginal times the original
raw-seed law jointly.  The factored-source product law is transported through
the literal post-race map and then through separate source-a.e. identities
for the direct endpoint and direct next seed. -/
theorem map_gn21RawAcceptedCompletionStateAndNextCycleSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    Measure.map (fun seed =>
      (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed))
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))) •
        (stateLaw.prod
          (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let p := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2)) (W.prod (T.prod Q))
  let candidate : GN21AcceptedWinnerPostRaceCalendarInput -> Fin 2 × GN21RawCycleSeed :=
    fun z =>
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z),
      gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z))
  have hcandidate : Measurable candidate := by
    exact ((measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state).comp
      (measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state)).prodMk
      ((measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state).comp
        (measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state))
  have hsource : HasLaw candidate (stateLaw.prod P) source := by
    simpa [candidate, source, stateLaw, P, W, T, Q, A, I, G, M, H, N, other,
      activeRate, acceptedRate, switchRate] using
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceJoint_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hpost : Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) = p • source := by
    simpa [P, activeRate, acceptedRate, switchRate, T, Q, G, M, A, W, H, N, I,
      source, p, other] using
      (map_gn21RawAcceptedWinnerPostRaceCalendarInput_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hcandidateMap : Measure.map
      (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      p • (stateLaw.prod P) := by
    calc
      Measure.map (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
          Measure.map candidate
            (Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
              (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
                rw [Measure.map_map hcandidate
                  (measurable_gn21RawAcceptedWinnerPostRaceCalendarInput state sigma hsigma)]
      _ = Measure.map candidate (p • source) := by rw [hpost]
      _ = p • Measure.map candidate source := by rw [Measure.map_smul]
      _ = p • (stateLaw.prod P) := by rw [hsource.map_eq]
  have hstate :=
    ae_gn21RawPostThinningRaceCalendarCompletionState_eq_postRaceCalendarResidualSourceEndpoint_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hseed :=
    ae_gn21RawAcceptedCompletionNextCycleSeed_eq_postRaceCalendarCompletionSeed_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  calc
    Measure.map (fun seed =>
        (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
          gn21RawAcceptedCompletionNextCycleSeed state sigma seed))
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) := by
            apply Measure.map_congr
            filter_upwards [hstate, hseed] with seed hstate hseed
            apply Prod.ext
            · exact hstate
            · calc
                gn21RawAcceptedCompletionNextCycleSeed state sigma seed =
                    gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma seed := hseed
                _ = (candidate (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)).2 := by
                  rfl
    _ = p • (stateLaw.prod P) := hcandidateMap

/-- The actual accepted branch retains the literal race-completion history
(state, competing-race holding time, and selected trip) jointly with its next raw
seed.  It is a transport of the factored-source history/seed product through
the raw accepted carrier, not a conditional restart assertion. -/
theorem map_gn21RawAcceptedCompletionHistoryAndNextCycleSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2), z.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    Measure.map (fun seed =>
      ((gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
        (gn21RawPostThinningRaceMinimum state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)),
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed))
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))) •
        (historyLaw.prod
          (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let G := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure activeRate
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := G.prod M
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let H := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex other))
  let N := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let I := H.prod N
  let source := W.prod (T.prod (Q.prod (A.prod I)))
  let p := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  let historyLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) (W.prod (T.prod Q))
  let candidate : GN21AcceptedWinnerPostRaceCalendarInput ->
      (Fin 2 × (Real × TripLength)) × GN21RawCycleSeed := fun z =>
    let r := gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state z
    ((gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state r, r.1.1.2),
      gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state r)
  have hcandidate : Measurable candidate := by
    let r := gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
    have hr : Measurable r :=
      measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceInput state
    have hhistory : Measurable (fun z =>
        (gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state (r z),
          (r z).1.1.2)) := by
      exact ((measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceEndpoint state).comp hr).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).comp hr)
    exact hhistory.prodMk
      ((measurable_gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed state).comp hr)
  have hsource : HasLaw candidate (historyLaw.prod P) source := by
    simpa [candidate, source, historyLaw, P, W, T, Q, A, I, G, M, H, N, other,
      activeRate, acceptedRate, switchRate] using
      (gn21AcceptedWinnerPostRaceCalendarResidualSourceHistoryNextSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hpost : Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) = p • source := by
    simpa [P, activeRate, acceptedRate, switchRate, T, Q, G, M, A, W, H, N, I,
      source, p, other] using
      (map_gn21RawAcceptedWinnerPostRaceCalendarInput_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hcandidateMap : Measure.map
      (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      p • (historyLaw.prod P) := by
    calc
      Measure.map (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
          Measure.map candidate
            (Measure.map (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
              (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
                rw [Measure.map_map hcandidate
                  (measurable_gn21RawAcceptedWinnerPostRaceCalendarInput state sigma hsigma)]
      _ = Measure.map candidate (p • source) := by rw [hpost]
      _ = p • Measure.map candidate source := by rw [Measure.map_smul]
      _ = p • (historyLaw.prod P) := by rw [hsource.map_eq]
  have hstate :=
    ae_gn21RawPostThinningRaceCalendarCompletionState_eq_postRaceCalendarResidualSourceEndpoint_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hseed :=
    ae_gn21RawAcceptedCompletionNextCycleSeed_eq_postRaceCalendarCompletionSeed_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have haccepted : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma),
      seed ∈ gn21RawPostThinningRaceAcceptedFirst state sigma := by
    exact MeasureTheory.ae_restrict_mem
      (measurableSet_gn21RawPostThinningRaceAcceptedFirst state sigma hsigma)
  calc
    Measure.map (fun seed =>
        ((gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
          (gn21RawPostThinningRaceMinimum state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)),
          gn21RawAcceptedCompletionNextCycleSeed state sigma seed))
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (candidate ∘ gn21RawAcceptedWinnerPostRaceCalendarInput state sigma)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) := by
            apply Measure.map_congr
            filter_upwards [hstate, hseed, haccepted] with seed hstate hseed haccepted
            apply Prod.ext
            · apply Prod.ext
              · exact hstate
              · apply Prod.ext
                · exact
                    (gn21AcceptedWinnerPostRaceCalendarResidualSourceRaceTime_eq_rawMinimum
                      state sigma seed haccepted).symm
                · exact
                    (gn21AcceptedWinnerPostRaceCalendarResidualSourceTrip_eq_rawSelectedTrip
                      state sigma seed).symm
            · calc
                gn21RawAcceptedCompletionNextCycleSeed state sigma seed =
                    gn21RawAcceptedWinnerPostRaceCalendarCompletionSeed state sigma seed := hseed
                _ = (candidate (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)).2 := by
                  change gn21AcceptedWinnerPostRaceCalendarCompletionSeed state
                    (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed) = _
                  exact
                    (gn21AcceptedWinnerPostRaceCalendarResidualSourceNextSeed_eq_completionSeed
                      state (gn21RawAcceptedWinnerPostRaceCalendarInput state sigma seed)).symm
    _ = p • (historyLaw.prod P) := hcandidateMap

/-- The observable record of one literal open-state subcycle.  A switch-first
branch records its holding time, while an accepted branch also records the
completion state and selected duration.  The sum tag keeps these two physical
outcomes disjoint without assigning an artificial trip to a switch. -/
abbrev GN21RawPostThinningRaceHistory :=
  Real ⊕ (Fin 2 × (Real × TripLength))

/-- The state in which the next open subcycle begins, read from a tagged
one-subcycle history. -/
def gn21RawPostThinningRaceHistoryNextState (state : Fin 2) :
    GN21RawPostThinningRaceHistory -> Fin 2
  | Sum.inl _ => AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  | Sum.inr z => z.1

theorem measurable_gn21RawPostThinningRaceHistoryNextState (state : Fin 2) :
    Measurable (gn21RawPostThinningRaceHistoryNextState state) := by
  apply measurable_fun_sum
  · change Measurable (fun _ : Real =>
      AppliedModelingLib.Probability.TwoStateSwitching.otherState state)
    exact measurable_const
  · change Measurable (fun z : Fin 2 × (Real × TripLength) => z.1)
    exact measurable_fst

/-- The literal one-subcycle history in the common tagged record space. -/
noncomputable def gn21RawPostThinningRaceHistory
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21RawPostThinningRaceHistory := by
  classical
  exact fun seed => if seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma then
    Sum.inl (gn21RawPostThinningRaceMinimum state sigma seed)
  else
    Sum.inr (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
      (gn21RawPostThinningRaceMinimum state sigma seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))

/-- The tagged literal history paired with the literal residual raw seed. -/
noncomputable def gn21RawPostThinningRaceHistoryAndNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21RawPostThinningRaceHistory × GN21RawCycleSeed :=
  fun seed => (gn21RawPostThinningRaceHistory state sigma seed,
    gn21RawPostThinningRaceNextCycleSeed state sigma seed)

/-- The state recorded by a literal tagged subcycle history agrees pathwise
with the state used by the literal calendar advance. -/
theorem gn21RawPostThinningRaceHistoryNextState_eq_nextState
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    gn21RawPostThinningRaceHistoryNextState state
      (gn21RawPostThinningRaceHistory state sigma seed) =
      gn21RawPostThinningRaceNextState state sigma seed := by
  classical
  by_cases hswitch : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma <;>
    simp [gn21RawPostThinningRaceHistoryNextState,
      gn21RawPostThinningRaceHistory, gn21RawPostThinningRaceNextState, hswitch]

/-- The elapsed calendar time recorded by a tagged literal subcycle history. -/
def gn21RawPostThinningRaceHistoryTime : GN21RawPostThinningRaceHistory -> Real
  | Sum.inl holdingTime => holdingTime
  | Sum.inr z => z.2.1 + z.2.2

theorem measurable_gn21RawPostThinningRaceHistoryTime :
    Measurable gn21RawPostThinningRaceHistoryTime := by
  apply measurable_fun_sum
  · change Measurable (fun t : Real => t)
    exact measurable_id
  · change Measurable (fun z : Fin 2 × (Real × TripLength) => z.2.1 + z.2.2)
    exact (measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd)

/-- The payment recorded by a tagged literal subcycle history.  A
switch-first history has no accepted trip and therefore contributes zero. -/
noncomputable def gn21RawPostThinningRaceHistoryEarning
    (w : PricingFunction) : GN21RawPostThinningRaceHistory -> Real
  | Sum.inl _ => 0
  | Sum.inr z => w z.2.2

theorem measurable_gn21RawPostThinningRaceHistoryEarning
    (w : PricingFunction) (hw : Measurable w) :
    Measurable (gn21RawPostThinningRaceHistoryEarning w) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact hw.comp (measurable_snd.comp measurable_snd)

/-- The history-time observation agrees pathwise with the literal subcycle
time used by the calendar reward construction. -/
theorem gn21RawPostThinningRaceHistoryTime_eq_subcycleTime
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    gn21RawPostThinningRaceHistoryTime
      (gn21RawPostThinningRaceHistory state sigma seed) =
      gn21RawPostThinningRaceSubcycleTime state sigma seed := by
  classical
  by_cases hswitch : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma
  · have hnotAccepted : seed ∉ gn21RawPostThinningRaceAcceptedFirst state sigma := by
      have hlt : (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
          (gn21RawPostThinningRaceSeed state sigma seed).1 := by
        simpa [gn21RawPostThinningRaceSwitchesFirst] using hswitch
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using not_le_of_gt hlt
    simp [gn21RawPostThinningRaceHistoryTime, gn21RawPostThinningRaceHistory,
      gn21RawPostThinningRaceSubcycleTime, gn21RawPostThinningRaceAcceptedContribution,
      gn21RawPostThinningRaceSeed, hswitch, hnotAccepted]
  · have haccepted : seed ∈ gn21RawPostThinningRaceAcceptedFirst state sigma := by
      have hle : (gn21RawPostThinningRaceSeed state sigma seed).1 ≤
          (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
        exact le_of_not_gt (by
          simpa [gn21RawPostThinningRaceSwitchesFirst] using hswitch)
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using hle
    simp [gn21RawPostThinningRaceHistoryTime, gn21RawPostThinningRaceHistory,
      gn21RawPostThinningRaceSubcycleTime, gn21RawPostThinningRaceAcceptedContribution,
      gn21RawPostThinningRaceSeed, hswitch, haccepted]

/-- The history payment observation agrees pathwise with the literal
one-subcycle earning. -/
theorem gn21RawPostThinningRaceHistoryEarning_eq_subcycleEarning
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (seed : GN21RawCycleSeed) :
    gn21RawPostThinningRaceHistoryEarning w
      (gn21RawPostThinningRaceHistory state sigma seed) =
      gn21RawPostThinningRaceSubcycleEarning state w sigma seed := by
  classical
  by_cases hswitch : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma
  · have hnotAccepted : seed ∉ gn21RawPostThinningRaceAcceptedFirst state sigma := by
      have hlt : (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
          (gn21RawPostThinningRaceSeed state sigma seed).1 := by
        simpa [gn21RawPostThinningRaceSwitchesFirst] using hswitch
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using not_le_of_gt hlt
    simp [gn21RawPostThinningRaceHistoryEarning, gn21RawPostThinningRaceHistory,
      gn21RawPostThinningRaceSubcycleEarning,
      gn21RawPostThinningRaceAcceptedContribution,
      gn21RawPostThinningRaceSeed, hswitch, hnotAccepted]
  · have haccepted : seed ∈ gn21RawPostThinningRaceAcceptedFirst state sigma := by
      have hle : (gn21RawPostThinningRaceSeed state sigma seed).1 ≤
          (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
        exact le_of_not_gt (by
          simpa [gn21RawPostThinningRaceSwitchesFirst] using hswitch)
      simpa [gn21RawPostThinningRaceAcceptedFirst,
        gn21RawPostThinningRaceSwitchesFirst] using hle
    simp [gn21RawPostThinningRaceHistoryEarning, gn21RawPostThinningRaceHistory,
      gn21RawPostThinningRaceSubcycleEarning,
      gn21RawPostThinningRaceAcceptedContribution,
      gn21RawPostThinningRaceSeed, hswitch, haccepted]

theorem measurable_gn21RawPostThinningRaceHistory
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceHistory state sigma) := by
  let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
  have hswitch : MeasurableSet (gn21RawPostThinningRaceSwitchesFirst state sigma) :=
    measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hminimum : Measurable (gn21RawPostThinningRaceMinimum state sigma) := by
    simpa [gn21RawPostThinningRaceMinimum,
      AppliedModelingLib.Probability.exponentialRaceMinimum] using
      (measurable_fst.comp raceMeas).min
        (measurable_fst.comp (measurable_snd.comp raceMeas))
  have hselected : Measurable
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma) := by
    exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)
  apply Measurable.ite hswitch
  · exact measurable_inl.comp hminimum
  · exact measurable_inr.comp
      ((measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma).prodMk
        (hminimum.prodMk hselected))

theorem measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma) := by
  exact (measurable_gn21RawPostThinningRaceHistory state sigma hsigma).prodMk
    (measurable_gn21RawPostThinningRaceNextCycleSeed state sigma hsigma)

theorem measurable_gn21RawPostThinningRaceSubcycleTime
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceSubcycleTime state sigma) := by
  have hhistory := measurable_gn21RawPostThinningRaceHistoryTime.comp
    (measurable_gn21RawPostThinningRaceHistory state sigma hsigma)
  convert hhistory using 1
  funext seed
  simpa [Function.comp_def] using
    (gn21RawPostThinningRaceHistoryTime_eq_subcycleTime state sigma seed).symm

/-- A measurable fold of the complete histories in a literal same-state
continuation prefix.  It is totalized outside the no-exit event; the product
theorem below is deliberately stated only on that literal event. -/
noncomputable def gn21RawCalendarNoExitHistoryFold
    {β : Type*} (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β) :
    Nat -> GN21RawCycleSeed -> β
  | 0 => fun _ => initial
  | n + 1 => fun seed =>
      update (gn21RawCalendarNoExitHistoryFold initialState policy initial update n seed)
        (gn21RawPostThinningRaceHistory initialState (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy n seed))

theorem measurable_gn21RawCalendarNoExitHistoryFold
    {β : Type*} [MeasurableSpace β]
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β)
    (hupdate : Measurable fun z : β × GN21RawPostThinningRaceHistory => update z.1 z.2)
    (n : Nat) :
    Measurable (gn21RawCalendarNoExitHistoryFold initialState policy initial update n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : GN21RawCycleSeed => initial)
      exact measurable_const
  | succ n ih =>
      change Measurable (fun seed => update
        (gn21RawCalendarNoExitHistoryFold initialState policy initial update n seed)
        (gn21RawPostThinningRaceHistory initialState (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy n seed)))
      exact hupdate.comp (ih.prodMk
        ((measurable_gn21RawPostThinningRaceHistory initialState
          (policy initialState) (hpolicy initialState)).comp
          (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n)))

theorem measurable_gn21RawCalendarNoExitAccumulatedTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (n : Nat) :
    Measurable (gn21RawCalendarNoExitAccumulatedTime initialState policy n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : GN21RawCycleSeed => (0 : Real))
      exact measurable_const
  | succ n ih =>
      change Measurable (fun seed =>
        gn21RawCalendarNoExitAccumulatedTime initialState policy n seed +
          gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)
            (gn21RawCalendarTraceSeed initialState policy n seed))
      exact ih.add ((measurable_gn21RawPostThinningRaceSubcycleTime initialState
        (policy initialState) (hpolicy initialState)).comp
        (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n))

/-- The earnings accumulated in the first `n` literal subcycles of a
same-state continuation prefix. -/
noncomputable def gn21RawCalendarNoExitAccumulatedEarning
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy) :
    Nat -> GN21RawCycleSeed -> Real
  | 0 => fun _ => 0
  | n + 1 => fun seed =>
      gn21RawCalendarNoExitAccumulatedEarning initialState w policy n seed +
        gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy n seed)

theorem gn21RawCalendarNoExitAccumulatedEarning_eq_historyFold
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (n : Nat) :
    gn21RawCalendarNoExitAccumulatedEarning initialState w policy n =
      gn21RawCalendarNoExitHistoryFold initialState policy 0
        (fun earned history => earned + gn21RawPostThinningRaceHistoryEarning w history) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext seed
      rw [gn21RawCalendarNoExitAccumulatedEarning,
        gn21RawCalendarNoExitHistoryFold, ih]
      simp only [gn21RawPostThinningRaceHistoryEarning_eq_subcycleEarning]

theorem gn21RawCalendarNoExitAccumulatedEarning_eq_sum_range
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (n : Nat) (seed : GN21RawCycleSeed) :
    gn21RawCalendarNoExitAccumulatedEarning initialState w policy n seed =
      ∑ m ∈ Finset.range n,
        gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy m seed) := by
  induction n with
  | zero => simp [gn21RawCalendarNoExitAccumulatedEarning]
  | succ n ih =>
      change
        gn21RawCalendarNoExitAccumulatedEarning initialState w policy n seed +
          gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)
            (gn21RawCalendarTraceSeed initialState policy n seed) = _
      rw [ih, Finset.sum_range_succ]

theorem measurable_gn21RawCalendarNoExitAccumulatedEarning
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (hw : Measurable w)
    (n : Nat) :
    Measurable (gn21RawCalendarNoExitAccumulatedEarning initialState w policy n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun seed =>
        gn21RawCalendarNoExitAccumulatedEarning initialState w policy n seed +
          gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)
            (gn21RawCalendarTraceSeed initialState policy n seed))
      exact ih.add
        ((measurable_gn21RawPostThinningRaceAcceptedContribution initialState
          (policy initialState) w (hpolicy initialState) hw).comp
          (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n))

/-- The unnormalized history law of one literal subcycle.  Its two summands
are the disjoint switch-first and accepted-completion histories; only the
residual raw seed is factored to the right. -/
noncomputable def gn21RawPostThinningRaceHistoryMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) (state : Fin 2)
    (sigma : TripPolicy) : Measure GN21RawPostThinningRaceHistory :=
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let switchLaw :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let acceptedHistoryLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2))
    (switchLaw.prod
      ((ProbabilityTheory.expMeasure (acceptedRate +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
  Measure.map (fun t : Real => Sum.inl t)
      (gn21SwitchFirstHeadHistoryMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state sigma) +
    ENNReal.ofReal (acceptedRate / (acceptedRate +
      gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
        (RawTwoStateCTMC.switchClockIndex state))) •
      Measure.map (fun z : Fin 2 × (Real × TripLength) => Sum.inr z) acceptedHistoryLaw

/-- The literal one-subcycle history and its residual raw seed have a product
law.  The history retains the branch-specific holding-time data, while the
right factor is the actual unconsumed source tail with its original law. -/
theorem map_gn21RawPostThinningRaceHistoryAndNextCycleSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  classical
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let S := gn21RawPostThinningRaceSwitchesFirst state sigma
  let A := gn21RawPostThinningRaceAcceptedFirst state sigma
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let acceptedHistoryLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2), z.2)) (W.prod (T.prod Q))
  let switchHistoryLaw :=
    gn21SwitchFirstHeadHistoryMeasure muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  let p := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  have hclockRate : ∀ c : Fin 4,
      0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI c := by
    intro c
    fin_cases c <;> simp [gn21CycleClockRate, harrivalI, harrivalJ, hswitchIJ, hswitchJI]
  have hactiveRate : 0 < activeRate := by
    exact hclockRate (gn21ArrivalClockIndex state)
  have hswitchRate : 0 < switchRate := by
    exact hclockRate (RawTwoStateCTMC.switchClockIndex state)
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure switchIJ) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchIJ
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure switchJI) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchJI
  letI : IsProbabilityMeasure
      (if state = 0 then ProbabilityTheory.expMeasure switchIJ
        else ProbabilityTheory.expMeasure switchJI) := by
    split <;> infer_instance
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI c)) := by
    intro c
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ s)) := by
    intro s
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure T :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsFiniteMeasure switchHistoryLaw := by
    dsimp [switchHistoryLaw, gn21SwitchFirstHeadHistoryMeasure]
    infer_instance
  letI : IsFiniteMeasure acceptedHistoryLaw := by
    dsimp [acceptedHistoryLaw]
    infer_instance
  let historyLaw : Measure GN21RawPostThinningRaceHistory :=
    Measure.map (fun t : Real => Sum.inl t) switchHistoryLaw +
      p • Measure.map (fun z : Fin 2 × (Real × TripLength) => Sum.inr z) acceptedHistoryLaw
  have hS : MeasurableSet S := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hminimum : Measurable (gn21RawPostThinningRaceMinimum state sigma) := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    simpa [gn21RawPostThinningRaceMinimum,
      AppliedModelingLib.Probability.exponentialRaceMinimum] using
      (measurable_fst.comp raceMeas).min
        (measurable_fst.comp (measurable_snd.comp raceMeas))
  have hselected : Measurable
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma) := by
    exact (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)
  have hswitchPair : Measurable (fun seed : GN21RawCycleSeed =>
      (gn21RawPostThinningRaceMinimum state sigma seed,
        gn21RawSwitchFirstNextCycleSeed state seed)) :=
    hminimum.prodMk (measurable_gn21RawSwitchFirstNextCycleSeed state)
  have hacceptedPair : Measurable (fun seed : GN21RawCycleSeed =>
      ((gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
        (gn21RawPostThinningRaceMinimum state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)),
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) :=
    ((measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma).prodMk
      (hminimum.prodMk hselected)).prodMk
      (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma)
  have htagInl : Measurable (fun t : Real =>
      (Sum.inl t : GN21RawPostThinningRaceHistory)) := measurable_inl
  have htagInr : Measurable (fun z : Fin 2 × (Real × TripLength) =>
      (Sum.inr z : GN21RawPostThinningRaceHistory)) := measurable_inr
  have htagInlPair : Measurable (Prod.map
      (fun t : Real => (Sum.inl t : GN21RawPostThinningRaceHistory))
      (id : GN21RawCycleSeed -> GN21RawCycleSeed)) :=
    htagInl.prodMap measurable_id
  have htagInrPair : Measurable (Prod.map
      (fun z : Fin 2 × (Real × TripLength) =>
        (Sum.inr z : GN21RawPostThinningRaceHistory))
      (id : GN21RawCycleSeed -> GN21RawCycleSeed)) :=
    htagInr.prodMap measurable_id
  have hswitchSource : Measure.map (fun seed =>
      (gn21RawPostThinningRaceMinimum state sigma seed,
        gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) =
      switchHistoryLaw.prod P := by
    simpa [P, S, switchHistoryLaw] using
      (map_gn21RawPostThinningRaceSwitchFirstHistoryAndNextCycleSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hacceptedSource : Measure.map (fun seed =>
      ((gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
        (gn21RawPostThinningRaceMinimum state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)),
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) =
      p • (acceptedHistoryLaw.prod P) := by
    simpa [P, A, activeRate, acceptedRate, switchRate, T, Q, W,
      acceptedHistoryLaw, p] using
      (map_gn21RawAcceptedCompletionHistoryAndNextCycleSeed_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hswitch : Measure.map (fun seed =>
      ((Sum.inl (gn21RawPostThinningRaceMinimum state sigma seed) :
          GN21RawPostThinningRaceHistory),
        gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) =
      (Measure.map (fun t : Real => (Sum.inl t : GN21RawPostThinningRaceHistory))
        switchHistoryLaw).prod P := by
    calc
      Measure.map (fun seed =>
          ((Sum.inl (gn21RawPostThinningRaceMinimum state sigma seed) :
              GN21RawPostThinningRaceHistory),
            gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) =
          Measure.map (Prod.map
            (fun t : Real => (Sum.inl t : GN21RawPostThinningRaceHistory)) id)
            (Measure.map (fun seed =>
              (gn21RawPostThinningRaceMinimum state sigma seed,
                gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S)) := by
              rw [Measure.map_map htagInlPair hswitchPair]
              rfl
      _ = Measure.map (Prod.map
          (fun t : Real => (Sum.inl t : GN21RawPostThinningRaceHistory)) id)
          (switchHistoryLaw.prod P) := by rw [hswitchSource]
      _ = (Measure.map (fun t : Real =>
          (Sum.inl t : GN21RawPostThinningRaceHistory)) switchHistoryLaw).prod P := by
            rw [← Measure.map_prod_map switchHistoryLaw P htagInl measurable_id,
              Measure.map_id]
  have haccepted : Measure.map (fun seed =>
      ((Sum.inr (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
          (gn21RawPostThinningRaceMinimum state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) :
          GN21RawPostThinningRaceHistory),
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) =
      p • (Measure.map (fun z : Fin 2 × (Real × TripLength) =>
        (Sum.inr z : GN21RawPostThinningRaceHistory)) acceptedHistoryLaw).prod P := by
    calc
      Measure.map (fun seed =>
          ((Sum.inr (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
            (gn21RawPostThinningRaceMinimum state sigma seed,
              AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) :
            GN21RawPostThinningRaceHistory),
          gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) =
          Measure.map (Prod.map
            (fun z : Fin 2 × (Real × TripLength) =>
              (Sum.inr z : GN21RawPostThinningRaceHistory)) id)
            (Measure.map (fun seed =>
              ((gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
                (gn21RawPostThinningRaceMinimum state sigma seed,
                  AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)),
                gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A)) := by
              rw [Measure.map_map htagInrPair hacceptedPair]
              rfl
      _ = Measure.map (Prod.map
          (fun z : Fin 2 × (Real × TripLength) =>
            (Sum.inr z : GN21RawPostThinningRaceHistory)) id)
          (p • (acceptedHistoryLaw.prod P)) := by rw [hacceptedSource]
      _ = p • Measure.map (Prod.map
          (fun z : Fin 2 × (Real × TripLength) =>
            (Sum.inr z : GN21RawPostThinningRaceHistory)) id)
          (acceptedHistoryLaw.prod P) := by rw [Measure.map_smul]
      _ = p • (Measure.map (fun z : Fin 2 × (Real × TripLength) =>
          (Sum.inr z : GN21RawPostThinningRaceHistory)) acceptedHistoryLaw).prod P := by
            rw [← Measure.map_prod_map acceptedHistoryLaw P htagInr measurable_id,
              Measure.map_id]
  change Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma) P =
    historyLaw.prod P
  calc
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma) P =
        Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
          (P.restrict S + P.restrict Sᶜ) := by
            rw [Measure.restrict_add_restrict_compl hS]
    _ = Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
          (P.restrict S) +
        Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
          (P.restrict Sᶜ) := by
            rw [Measure.map_add _ _
              (measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma hsigma)]
    _ = Measure.map (fun seed =>
          ((Sum.inl (gn21RawPostThinningRaceMinimum state sigma seed) :
              GN21RawPostThinningRaceHistory),
            gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) +
        Measure.map (fun seed =>
          ((Sum.inr (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
            (gn21RawPostThinningRaceMinimum state sigma seed,
              AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) :
            GN21RawPostThinningRaceHistory),
            gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) := by
          congr 1
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS] with seed hseed
            have hseed' : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            simp [gn21RawPostThinningRaceHistoryAndNextCycleSeed,
              gn21RawPostThinningRaceHistory,
              gn21RawPostThinningRaceNextCycleSeed, hseed']
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS.compl] with seed hseed
            have hseed' : seed ∉ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            simp [gn21RawPostThinningRaceHistoryAndNextCycleSeed,
              gn21RawPostThinningRaceHistory,
              gn21RawPostThinningRaceNextCycleSeed, hseed']
    _ = (Measure.map (fun t : Real =>
          (Sum.inl t : GN21RawPostThinningRaceHistory)) switchHistoryLaw).prod P +
        p • (Measure.map (fun z : Fin 2 × (Real × TripLength) =>
          (Sum.inr z : GN21RawPostThinningRaceHistory)) acceptedHistoryLaw).prod P := by
            rw [hswitch, haccepted]
    _ = historyLaw.prod P := by
          dsimp only [historyLaw]
          rw [Measure.add_prod, Measure.prod_smul_left]

/-- The one-subcycle tagged history law is s-finite, derived from its literal
raw-source pushforward rather than imposed as an auxiliary process premise. -/
theorem sfinite_gn21RawPostThinningRaceHistoryMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    SFinite (gn21RawPostThinningRaceHistoryMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI state sigma) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let pair := gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hpair : Measurable pair :=
    measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma hsigma
  have hfull : Measure.map pair P =
      (gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P := by
    simpa [pair, P] using
      (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hhistory : Measure.map (gn21RawPostThinningRaceHistory state sigma) P =
      gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma := by
    calc
      Measure.map (gn21RawPostThinningRaceHistory state sigma) P =
          Measure.map (Prod.fst ∘ pair) P := by rfl
      _ = Measure.map Prod.fst (Measure.map pair P) := by
            rw [Measure.map_map measurable_fst hpair]
      _ = Measure.map Prod.fst
          ((gn21RawPostThinningRaceHistoryMeasure
            muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P) := by rw [hfull]
      _ = gn21RawPostThinningRaceHistoryMeasure
          muI muJ arrivalI arrivalJ switchIJ switchJI state sigma := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hhistory]
  infer_instance

/-- Restricting a literal subcycle by any next-state fiber still leaves its
complete tagged history independent of the residual raw seed.  This is the
event-bearing form used to concatenate same-state subcycles and cross-state
exits on the one calendar source path. -/
theorem map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_nextState
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state targetState : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹' {targetState}
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
      (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {targetState})) =
      ((gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).restrict historyEvent).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹' {targetState}
  let sourceEvent := (gn21RawPostThinningRaceNextState state sigma) ⁻¹' {targetState}
  let pair := gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hpair : Measurable pair :=
    measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma hsigma
  have hfull : Measure.map pair P =
      (gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P := by
    simpa [pair, P] using
      (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hhistoryMap : Measure.map (gn21RawPostThinningRaceHistory state sigma) P =
      gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma := by
    calc
      Measure.map (gn21RawPostThinningRaceHistory state sigma) P =
          Measure.map (Prod.fst ∘ pair) P := by rfl
      _ = Measure.map Prod.fst (Measure.map pair P) := by
            rw [Measure.map_map measurable_fst hpair]
      _ = Measure.map Prod.fst
          ((gn21RawPostThinningRaceHistoryMeasure
            muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P) := by rw [hfull]
      _ = gn21RawPostThinningRaceHistoryMeasure
          muI muJ arrivalI arrivalJ switchIJ switchJI state sigma := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
  letI : SFinite (gn21RawPostThinningRaceHistoryMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI state sigma) := by
    rw [← hhistoryMap]
    infer_instance
  have hhistoryEvent : MeasurableSet historyEvent :=
    (measurableSet_singleton targetState).preimage
      (measurable_gn21RawPostThinningRaceHistoryNextState state)
  have hpairEvent : MeasurableSet (historyEvent ×ˢ (Set.univ : Set GN21RawCycleSeed)) :=
    hhistoryEvent.prod MeasurableSet.univ
  have hpreimage : pair ⁻¹' (historyEvent ×ˢ (Set.univ : Set GN21RawCycleSeed)) =
      sourceEvent := by
    ext seed
    change (pair seed).1 ∈ historyEvent ∧ (pair seed).2 ∈ Set.univ ↔
      seed ∈ sourceEvent
    simp only [Set.mem_univ, and_true]
    change (gn21RawPostThinningRaceHistory state sigma seed ∈ historyEvent) ↔
      seed ∈ sourceEvent
    change gn21RawPostThinningRaceHistoryNextState state
        (gn21RawPostThinningRaceHistory state sigma seed) = targetState ↔
      gn21RawPostThinningRaceNextState state sigma seed = targetState
    rw [gn21RawPostThinningRaceHistoryNextState_eq_nextState]
  calc
    Measure.map pair (P.restrict sourceEvent) =
        Measure.map pair (P.restrict (pair ⁻¹'
          (historyEvent ×ˢ (Set.univ : Set GN21RawCycleSeed)))) := by rw [hpreimage]
    _ = (Measure.map pair P).restrict
        (historyEvent ×ˢ (Set.univ : Set GN21RawCycleSeed)) := by
          rw [← Measure.restrict_map hpair hpairEvent]
    _ = ((gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).prod P).restrict
        (historyEvent ×ˢ (Set.univ : Set GN21RawCycleSeed)) := by
          rw [map_gn21RawPostThinningRaceHistoryAndNextCycleSeed
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass]
    _ = ((gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).restrict historyEvent).prod P := by
          rw [← Measure.restrict_prod_eq_prod_univ]

/-- Any measurable observation of the complete tagged subcycle history remains
independent of the literal residual raw seed on each next-state fiber. -/
theorem map_gn21RawPostThinningRaceHistoryFunctionAndNextCycleSeed_restrict_nextState
    {β : Type*} [MeasurableSpace β]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state targetState : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (f : GN21RawPostThinningRaceHistory -> β) (hf : Measurable f) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹' {targetState}
    Measure.map (fun seed =>
      (f (gn21RawPostThinningRaceHistory state sigma seed),
        gn21RawPostThinningRaceNextCycleSeed state sigma seed))
      (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {targetState})) =
      (Measure.map f
        ((gn21RawPostThinningRaceHistoryMeasure
          muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).restrict historyEvent)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹' {targetState}
  let sourceEvent := (gn21RawPostThinningRaceNextState state sigma) ⁻¹' {targetState}
  let historyLaw := gn21RawPostThinningRaceHistoryMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  let pair := gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma
  let output := fun seed : GN21RawCycleSeed =>
    (f (gn21RawPostThinningRaceHistory state sigma seed),
      gn21RawPostThinningRaceNextCycleSeed state sigma seed)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : SFinite historyLaw := by
    simpa [historyLaw] using
      (sfinite_gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hpair : Measurable pair :=
    measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma hsigma
  have hmap : Measurable (Prod.map f (id : GN21RawCycleSeed -> GN21RawCycleSeed)) :=
    hf.prodMap measurable_id
  calc
    Measure.map output (P.restrict sourceEvent) =
        Measure.map (Prod.map f (id : GN21RawCycleSeed -> GN21RawCycleSeed))
          (Measure.map pair (P.restrict sourceEvent)) := by
            rw [Measure.map_map hmap hpair]
            rfl
    _ = Measure.map (Prod.map f (id : GN21RawCycleSeed -> GN21RawCycleSeed))
        ((historyLaw.restrict historyEvent).prod P) := by
          rw [show Measure.map pair (P.restrict sourceEvent) =
            (historyLaw.restrict historyEvent).prod P by
              simpa [pair, P, sourceEvent, historyEvent, historyLaw] using
                (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_nextState
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI state targetState sigma hsigma
                  hsigma_subset hmass)]
    _ = (Measure.map f (historyLaw.restrict historyEvent)).prod P := by
          rw [← Measure.map_prod_map (historyLaw.restrict historyEvent) P hf measurable_id,
            Measure.map_id]

/-- On a literal same-state continuation, the complete one-subcycle history
and fresh raw tail retain the event-bearing product law. -/
theorem map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_noExit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹' {state}
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
      (P.restrict (gn21RawPostThinningRaceExitState state sigma)ᶜ) =
      ((gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).restrict historyEvent).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hself := preimage_gn21RawPostThinningRaceNextState_self state sigma
  calc
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceExitState state sigma)ᶜ) =
        Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
          (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {state})) := by
            rw [hself]
    _ = _ := map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_nextState
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state state sigma hsigma hsigma_subset hmass

/-- On a literal cross-state exit, the complete one-subcycle history and
fresh raw tail retain the event-bearing product law. -/
theorem map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_exit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let historyEvent := (gn21RawPostThinningRaceHistoryNextState state) ⁻¹'
      {AppliedModelingLib.Probability.TwoStateSwitching.otherState state}
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
      (P.restrict (gn21RawPostThinningRaceExitState state sigma)) =
      ((gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI state sigma).restrict historyEvent).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  have hother := preimage_gn21RawPostThinningRaceNextState_otherState state sigma
  calc
    Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceExitState state sigma)) =
        Measure.map (gn21RawPostThinningRaceHistoryAndNextCycleSeed state sigma)
          (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {other})) := by
            rw [hother]
    _ = _ := by
      simpa [other] using
        (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_nextState
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state other sigma hsigma hsigma_subset hmass)

/-- On the literal switch-first branch, the next state is deterministically
the other state and the literal next raw seed has its original law.  This is
recorded as an explicit joint product measure for the later branch sum. -/
theorem map_gn21RawSwitchFirstStateAndNextCycleSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (fun seed =>
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state,
        gn21RawSwitchFirstNextCycleSeed state seed))
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      gn21SwitchFirstNoHitMass muI muJ arrivalI arrivalJ switchIJ switchJI state sigma •
        ((Measure.dirac
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)).prod
          (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let S := gn21RawPostThinningRaceSwitchesFirst state sigma
  let switchMass := gn21SwitchFirstNoHitMass
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hnext : Measurable (gn21RawSwitchFirstNextCycleSeed state) :=
    measurable_gn21RawSwitchFirstNextCycleSeed state
  have hseed : Measure.map (gn21RawSwitchFirstNextCycleSeed state)
      (P.restrict S) = switchMass • P := by
    simpa [P, S, switchMass] using
      (map_gn21RawSwitchFirstNextCycleSeed_restrict_switchesFirst
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  calc
    Measure.map (fun seed =>
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state,
          gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) =
        Measure.map (Prod.mk
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))
          (Measure.map (gn21RawSwitchFirstNextCycleSeed state) (P.restrict S)) := by
            rw [Measure.map_map measurable_prodMk_left hnext]
            rfl
    _ = Measure.map (Prod.mk
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))
          (switchMass • P) := by rw [hseed]
    _ = switchMass • Measure.map (Prod.mk
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) P := by
            rw [Measure.map_smul]
    _ = switchMass • ((Measure.dirac
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)).prod P) := by
            rw [Measure.dirac_prod]

/-- The literal one-subcycle state and next raw seed have a product-form
transition law.  The next-state marginal is the explicit mixture of the
switch-first point mass and the accepted-completion endpoint law; conditional
on that state, the next raw seed has its original law. -/
theorem map_gn21RawPostThinningRaceStateAndNextCycleSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
      (gn21ArrivalClockIndex state)
    let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let switchLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × TripLength) =>
        AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
          (z.1, max 0 z.2.2))
      (switchLaw.prod
        ((ProbabilityTheory.expMeasure (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))).prod selectedLaw))
    Measure.map (fun seed =>
      (gn21RawPostThinningRaceNextState state sigma seed,
        gn21RawPostThinningRaceNextCycleSeed state sigma seed))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ((gn21SwitchFirstNoHitMass muI muJ arrivalI arrivalJ switchIJ switchJI state sigma •
        Measure.dirac (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) +
        ENNReal.ofReal (acceptedRate / (acceptedRate +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) • stateLaw).prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let S := gn21RawPostThinningRaceSwitchesFirst state sigma
  let A := gn21RawPostThinningRaceAcceptedFirst state sigma
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let switchMass := gn21SwitchFirstNoHitMass
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  let acceptedMass := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2)) (W.prod (T.prod Q))
  have hactiveRate : 0 < activeRate := by
    dsimp [activeRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := mul_pos hactiveRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := ProbabilityTheory.isProbabilityMeasure_expMeasure
    (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchIJ
  letI : IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI) :=
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitchJI
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    infer_instance
  letI : IsProbabilityMeasure stateLaw := by
    dsimp [stateLaw]
    exact Measure.isProbabilityMeasure_map
      ((AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp
        (measurable_fst.prodMk
          (measurable_const.max (measurable_snd.comp measurable_snd)))).aemeasurable
  have hS : MeasurableSet S := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hnextPair : Measurable (fun seed =>
      (gn21RawPostThinningRaceNextState state sigma seed,
        gn21RawPostThinningRaceNextCycleSeed state sigma seed)) := by
    exact (measurable_gn21RawPostThinningRaceNextState state sigma hsigma).prodMk
      (Measurable.ite hS (measurable_gn21RawSwitchFirstNextCycleSeed state)
        (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma))
  have hswitchLaw : Measure.map (fun seed =>
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state,
        gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) =
      switchMass • ((Measure.dirac
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)).prod P) := by
    simpa [P, S, switchMass] using
      (map_gn21RawSwitchFirstStateAndNextCycleSeed_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hacceptedLaw : Measure.map (fun seed =>
      (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
        gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) =
      acceptedMass • (stateLaw.prod P) := by
    simpa [P, A, activeRate, acceptedRate, switchRate, T, Q, W, stateLaw, acceptedMass] using
      (map_gn21RawAcceptedCompletionStateAndNextCycleSeed_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  calc
    Measure.map (fun seed =>
        (gn21RawPostThinningRaceNextState state sigma seed,
          gn21RawPostThinningRaceNextCycleSeed state sigma seed)) P =
        Measure.map (fun seed =>
          (gn21RawPostThinningRaceNextState state sigma seed,
            gn21RawPostThinningRaceNextCycleSeed state sigma seed))
          (P.restrict S + P.restrict Sᶜ) := by
            rw [Measure.restrict_add_restrict_compl hS]
    _ = Measure.map (fun seed =>
          (gn21RawPostThinningRaceNextState state sigma seed,
            gn21RawPostThinningRaceNextCycleSeed state sigma seed)) (P.restrict S) +
        Measure.map (fun seed =>
          (gn21RawPostThinningRaceNextState state sigma seed,
            gn21RawPostThinningRaceNextCycleSeed state sigma seed)) (P.restrict Sᶜ) := by
            rw [Measure.map_add _ _ hnextPair]
    _ = Measure.map (fun seed =>
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state,
            gn21RawSwitchFirstNextCycleSeed state seed)) (P.restrict S) +
        Measure.map (fun seed =>
          (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
            gn21RawAcceptedCompletionNextCycleSeed state sigma seed)) (P.restrict A) := by
          congr 1
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS] with seed hseed
            have hseed' : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            simp [gn21RawPostThinningRaceNextState,
              gn21RawPostThinningRaceNextCycleSeed, hseed']
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS.compl] with seed hseed
            have hseed' : seed ∉ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            simp [gn21RawPostThinningRaceNextState,
              gn21RawPostThinningRaceNextCycleSeed, hseed']
    _ = switchMass • ((Measure.dirac
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)).prod P) +
        acceptedMass • (stateLaw.prod P) := by
          rw [hswitchLaw, hacceptedLaw]
    _ = ((switchMass • Measure.dirac
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) +
        acceptedMass • stateLaw).prod P := by
          rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]

/-- The literal next raw seed is independent of the literal next state under
the source raw-seed law.  This rewrites the explicit branch mixture from the
preceding theorem by its actual next-state marginal, which is the form needed
to iterate the transition on one calendar source path. -/
theorem map_gn21RawPostThinningRaceStateAndNextCycleSeed_eq_stateMarginal_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (fun seed =>
      (gn21RawPostThinningRaceNextState state sigma seed,
        gn21RawPostThinningRaceNextCycleSeed state sigma seed))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (Measure.map (gn21RawPostThinningRaceNextState state sigma)
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)).prod
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let activeRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let acceptedRate := activeRate * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let W : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let stateLaw := Measure.map (fun z : ((Nat -> Real) × (Nat -> Real)) ×
      (Real × TripLength) =>
      AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
        (z.1, max 0 z.2.2)) (W.prod (T.prod Q))
  let switchMass := gn21SwitchFirstNoHitMass
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  let acceptedMass := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  let mixedStateLaw :=
    (switchMass • Measure.dirac
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) +
      acceptedMass • stateLaw
  let pairMap := fun seed : GN21RawCycleSeed =>
    (gn21RawPostThinningRaceNextState state sigma seed,
      gn21RawPostThinningRaceNextCycleSeed state sigma seed)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hS : MeasurableSet (gn21RawPostThinningRaceSwitchesFirst state sigma) := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hpairMap : Measurable pairMap := by
    exact (measurable_gn21RawPostThinningRaceNextState state sigma hsigma).prodMk
      (Measurable.ite hS (measurable_gn21RawSwitchFirstNextCycleSeed state)
        (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma))
  have htotal : Measure.map pairMap P = mixedStateLaw.prod P := by
    simpa [pairMap, P, activeRate, acceptedRate, switchRate, T, Q, W, stateLaw,
      switchMass, acceptedMass, mixedStateLaw] using
      (map_gn21RawPostThinningRaceStateAndNextCycleSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hstateMarginal : Measure.map (gn21RawPostThinningRaceNextState state sigma) P =
      mixedStateLaw := by
    calc
      Measure.map (gn21RawPostThinningRaceNextState state sigma) P =
          Measure.map (Prod.fst ∘ pairMap) P := by rfl
      _ = Measure.map Prod.fst (Measure.map pairMap P) := by
        rw [← Measure.map_map measurable_fst hpairMap]
      _ = Measure.map Prod.fst (mixedStateLaw.prod P) := by rw [htotal]
      _ = mixedStateLaw := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc
    Measure.map (fun seed =>
        (gn21RawPostThinningRaceNextState state sigma seed,
          gn21RawPostThinningRaceNextCycleSeed state sigma seed)) P =
        Measure.map pairMap P := by rfl
    _ = mixedStateLaw.prod P := htotal
    _ = (Measure.map (gn21RawPostThinningRaceNextState state sigma) P).prod P := by
      rw [hstateMarginal]

/-- A literal calendar advance preserves the product form of any finite
state distribution and the raw source tail.  This integrates the two
state-specific one-subcycle kernels; it does not replace the calendar tail by
a separately sampled seed. -/
theorem map_gn21RawCalendarAdvance_stateMarginal_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (stateLaw : Measure (Fin 2)) [IsProbabilityMeasure stateLaw] :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarAdvance policy) (stateLaw.prod P) =
      (Measure.map (fun z => (gn21RawCalendarAdvance policy z).1) (stateLaw.prod P)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let advance := gn21RawCalendarAdvance policy
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hadvance : Measurable advance := by
    simpa [advance] using measurable_gn21RawCalendarAdvance policy hpolicy
  have hstateAdvance : Measurable (fun z => (advance z).1) := measurable_fst.comp hadvance
  have hsplit : stateLaw = stateLaw {0} • Measure.dirac (0 : Fin 2) +
      stateLaw {1} • Measure.dirac (1 : Fin 2) := by
    apply Measure.ext_of_singleton
    intro state
    fin_cases state <;> simp
  have hsplitProd : stateLaw.prod P =
      stateLaw {0} • ((Measure.dirac (0 : Fin 2)).prod P) +
        stateLaw {1} • ((Measure.dirac (1 : Fin 2)).prod P) := by
    calc
      stateLaw.prod P =
          (stateLaw {0} • Measure.dirac (0 : Fin 2) +
            stateLaw {1} • Measure.dirac (1 : Fin 2)).prod P := by
            exact congrArg (fun nu : Measure (Fin 2) => nu.prod P) hsplit
      _ = stateLaw {0} • ((Measure.dirac 0).prod P) +
          stateLaw {1} • ((Measure.dirac 1).prod P) := by
            rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
  have hfixed (state : Fin 2) :
      Measure.map advance ((Measure.dirac state).prod P) =
        (Measure.map (fun z => (advance z).1) ((Measure.dirac state).prod P)).prod P := by
    have hone : Measure.map (fun seed =>
        (gn21RawPostThinningRaceNextState state (policy state) seed,
          gn21RawPostThinningRaceNextCycleSeed state (policy state) seed)) P =
        (Measure.map (gn21RawPostThinningRaceNextState state (policy state)) P).prod P := by
      simpa [P] using
        (map_gn21RawPostThinningRaceStateAndNextCycleSeed_eq_stateMarginal_prod
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state (policy state)
          (hpolicy state) (hpolicy_subset state) (hpolicy_mass state))
    calc
      Measure.map advance ((Measure.dirac state).prod P) =
          Measure.map (fun seed =>
            (gn21RawPostThinningRaceNextState state (policy state) seed,
              gn21RawPostThinningRaceNextCycleSeed state (policy state) seed)) P := by
            rw [Measure.dirac_prod, Measure.map_map hadvance measurable_prodMk_left]
            rfl
      _ = (Measure.map (gn21RawPostThinningRaceNextState state (policy state)) P).prod P := hone
      _ = (Measure.map (fun z => (advance z).1) ((Measure.dirac state).prod P)).prod P := by
            congr 1
            rw [Measure.dirac_prod,
              Measure.map_map hstateAdvance measurable_prodMk_left]
            rfl
  have hstate :
      Measure.map (fun z => (advance z).1) (stateLaw.prod P) =
        stateLaw {0} • Measure.map (fun z => (advance z).1)
          ((Measure.dirac (0 : Fin 2)).prod P) +
          stateLaw {1} • Measure.map (fun z => (advance z).1)
            ((Measure.dirac (1 : Fin 2)).prod P) := by
    calc
      Measure.map (fun z => (advance z).1) (stateLaw.prod P) =
          Measure.map (fun z => (advance z).1)
            (stateLaw {0} • ((Measure.dirac (0 : Fin 2)).prod P) +
              stateLaw {1} • ((Measure.dirac (1 : Fin 2)).prod P)) := by rw [hsplitProd]
      _ = stateLaw {0} • Measure.map (fun z => (advance z).1)
          ((Measure.dirac (0 : Fin 2)).prod P) +
          stateLaw {1} • Measure.map (fun z => (advance z).1)
            ((Measure.dirac (1 : Fin 2)).prod P) := by
            rw [Measure.map_add _ _ hstateAdvance, Measure.map_smul, Measure.map_smul]
  calc
    Measure.map advance (stateLaw.prod P) =
        Measure.map advance
          (stateLaw {0} • ((Measure.dirac (0 : Fin 2)).prod P) +
            stateLaw {1} • ((Measure.dirac (1 : Fin 2)).prod P)) := by rw [hsplitProd]
    _ = stateLaw {0} • Measure.map advance ((Measure.dirac (0 : Fin 2)).prod P) +
        stateLaw {1} • Measure.map advance ((Measure.dirac (1 : Fin 2)).prod P) := by
          rw [Measure.map_add _ _ hadvance, Measure.map_smul, Measure.map_smul]
    _ = stateLaw {0} •
          (Measure.map (fun z => (advance z).1) ((Measure.dirac (0 : Fin 2)).prod P)).prod P +
        stateLaw {1} •
          (Measure.map (fun z => (advance z).1) ((Measure.dirac (1 : Fin 2)).prod P)).prod P := by
          rw [hfixed 0, hfixed 1]
    _ = (stateLaw {0} • Measure.map (fun z => (advance z).1)
          ((Measure.dirac (0 : Fin 2)).prod P) +
          stateLaw {1} • Measure.map (fun z => (advance z).1)
            ((Measure.dirac (1 : Fin 2)).prod P)).prod P := by
          rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
    _ = (Measure.map (fun z => (advance z).1) (stateLaw.prod P)).prod P := by rw [hstate]

/-- At every deterministic open-subcycle index, the literal calendar state is
independent of the still-unconsumed raw seed.  This is an induction over the
single residualized source path, not an iid proposal-path construction. -/
theorem map_gn21RawCalendarTrace_eq_stateMarginal_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTrace initialState policy n) P =
      (Measure.map (gn21RawCalendarTraceState initialState policy n) P).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let advance := gn21RawCalendarAdvance policy
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hadvance : Measurable advance := by
    simpa [advance] using measurable_gn21RawCalendarAdvance policy hpolicy
  induction n with
  | zero =>
      calc
        Measure.map (gn21RawCalendarTrace initialState policy 0) P =
            (Measure.dirac initialState).prod P := by
              rw [Measure.dirac_prod]
              rfl
        _ = (Measure.map (gn21RawCalendarTraceState initialState policy 0) P).prod P := by
              rw [gn21RawCalendarTraceState_zero, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
      let stateLaw := Measure.map (gn21RawCalendarTraceState initialState policy n) P
      letI : IsProbabilityMeasure stateLaw := by
        exact Measure.isProbabilityMeasure_map
          (measurable_gn21RawCalendarTraceState initialState policy hpolicy n).aemeasurable
      have htrace : Measurable (gn21RawCalendarTrace initialState policy n) :=
        measurable_gn21RawCalendarTrace initialState policy hpolicy n
      have hstateAdvance : Measurable (fun z => (advance z).1) := measurable_fst.comp hadvance
      have hstep : Measure.map advance (stateLaw.prod P) =
          (Measure.map (fun z => (advance z).1) (stateLaw.prod P)).prod P := by
        simpa [P, advance, stateLaw] using
          (map_gn21RawCalendarAdvance_stateMarginal_prod
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI policy hpolicy hpolicy_subset hpolicy_mass
            stateLaw)
      have hnextState :
          Measure.map (gn21RawCalendarTraceState initialState policy (n + 1)) P =
            Measure.map (fun z => (advance z).1) (stateLaw.prod P) := by
        calc
          Measure.map (gn21RawCalendarTraceState initialState policy (n + 1)) P =
              Measure.map (fun z => (advance z).1)
                (Measure.map (gn21RawCalendarTrace initialState policy n) P) := by
                  rw [Measure.map_map hstateAdvance htrace]
                  rfl
          _ = Measure.map (fun z => (advance z).1) (stateLaw.prod P) := by
                rw [ih]
      calc
        Measure.map (gn21RawCalendarTrace initialState policy (n + 1)) P =
            Measure.map advance (Measure.map (gn21RawCalendarTrace initialState policy n) P) := by
              rw [Measure.map_map hadvance htrace]
              rfl
        _ = Measure.map advance (stateLaw.prod P) := by rw [ih]
        _ = (Measure.map (fun z => (advance z).1) (stateLaw.prod P)).prod P := hstep
        _ = (Measure.map (gn21RawCalendarTraceState initialState policy (n + 1)) P).prod P := by
              rw [hnextState]

/-- The literal unconsumed raw seed has its original source law at every
deterministic open-subcycle index. -/
theorem map_gn21RawCalendarTraceSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTraceSeed initialState policy n) P = P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have htrace : Measurable (gn21RawCalendarTrace initialState policy n) :=
    measurable_gn21RawCalendarTrace initialState policy hpolicy n
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarTraceState initialState policy n) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarTraceState initialState policy hpolicy n).aemeasurable
  have hfactor := map_gn21RawCalendarTrace_eq_stateMarginal_prod
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
    hpolicy hpolicy_subset hpolicy_mass n
  calc
    Measure.map (gn21RawCalendarTraceSeed initialState policy n) P =
        Measure.map Prod.snd (Measure.map (gn21RawCalendarTrace initialState policy n) P) := by
          change Measure.map (Prod.snd ∘ gn21RawCalendarTrace initialState policy n) P = _
          rw [← Measure.map_map measurable_snd htrace]
    _ = Measure.map Prod.snd
        ((Measure.map (gn21RawCalendarTraceState initialState policy n) P).prod P) := by rw [hfactor]
    _ = P := by rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Conditioning one literal subcycle on any specified next physical state
still leaves its next raw seed with the original law, scaled by that state's
actual transition mass. -/
theorem map_gn21RawPostThinningRaceNextCycleSeed_restrict_nextState
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (nextState : Fin 2) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
      (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {nextState})) =
      (Measure.map (gn21RawPostThinningRaceNextState state sigma) P {nextState}) • P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let pairMap := fun seed : GN21RawCycleSeed =>
    (gn21RawPostThinningRaceNextState state sigma seed,
      gn21RawPostThinningRaceNextCycleSeed state sigma seed)
  let stateLaw := Measure.map (gn21RawPostThinningRaceNextState state sigma) P
  let carrier : Set (Fin 2 × GN21RawCycleSeed) := {nextState} ×ˢ Set.univ
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hpairMap : Measurable pairMap := by
    let S := gn21RawPostThinningRaceSwitchesFirst state sigma
    have hS : MeasurableSet S := by
      let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
      exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
        (measurable_fst.comp raceMeas)
    exact (measurable_gn21RawPostThinningRaceNextState state sigma hsigma).prodMk
      (Measurable.ite hS (measurable_gn21RawSwitchFirstNextCycleSeed state)
        (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma))
  have hcarrier : MeasurableSet carrier :=
    measurableSet_singleton nextState |>.prod MeasurableSet.univ
  have hpreimage : pairMap ⁻¹' carrier =
      (gn21RawPostThinningRaceNextState state sigma) ⁻¹' {nextState} := by
    ext seed
    simp [pairMap, carrier]
  have hfactor : Measure.map pairMap P = stateLaw.prod P := by
    simpa [P, pairMap, stateLaw] using
      (map_gn21RawPostThinningRaceStateAndNextCycleSeed_eq_stateMarginal_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  calc
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
        (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {nextState})) =
        Measure.map Prod.snd (Measure.map pairMap (P.restrict (pairMap ⁻¹' carrier))) := by
          rw [← hpreimage]
          change Measure.map (Prod.snd ∘ pairMap) (P.restrict (pairMap ⁻¹' carrier)) = _
          rw [← Measure.map_map measurable_snd hpairMap]
    _ = Measure.map Prod.snd ((Measure.map pairMap P).restrict carrier) := by
          rw [Measure.restrict_map hpairMap hcarrier]
    _ = Measure.map Prod.snd ((stateLaw.prod P).restrict carrier) := by rw [hfactor]
    _ = Measure.map Prod.snd ((stateLaw.restrict {nextState}).prod P) := by
          rw [Measure.restrict_prod_eq_prod_univ]
    _ = stateLaw {nextState} • P := by
          rw [Measure.map_snd_prod]
          simp
    _ = (Measure.map (gn21RawPostThinningRaceNextState state sigma) P {nextState}) • P := by
          rfl

/-- On the literal no-exit branch, the next raw seed has the original source
law, with its exact no-exit mass retained. -/
theorem map_gn21RawPostThinningRaceNextCycleSeed_restrict_noExit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
      (P.restrict (gn21RawPostThinningRaceExitState state sigma)ᶜ) =
      (P (gn21RawPostThinningRaceExitState state sigma)ᶜ) • P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hnext : Measurable (gn21RawPostThinningRaceNextState state sigma) :=
    measurable_gn21RawPostThinningRaceNextState state sigma hsigma
  have hself := preimage_gn21RawPostThinningRaceNextState_self state sigma
  calc
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceExitState state sigma)ᶜ) =
        Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
          (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {state})) := by
            rw [hself]
    _ = (Measure.map (gn21RawPostThinningRaceNextState state sigma) P {state}) • P := by
          simpa [P] using
            (map_gn21RawPostThinningRaceNextCycleSeed_restrict_nextState
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass state)
    _ = (P (gn21RawPostThinningRaceExitState state sigma)ᶜ) • P := by
          congr 1
          rw [Measure.map_apply hnext (measurableSet_singleton state), hself]

/-- On the literal cross-state exit branch, the next raw seed has the
original source law, with the exact exit mass retained. -/
theorem map_gn21RawPostThinningRaceNextCycleSeed_restrict_exit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
      (P.restrict (gn21RawPostThinningRaceExitState state sigma)) =
      (P (gn21RawPostThinningRaceExitState state sigma)) • P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let otherState := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  have hnext : Measurable (gn21RawPostThinningRaceNextState state sigma) :=
    measurable_gn21RawPostThinningRaceNextState state sigma hsigma
  have hother := preimage_gn21RawPostThinningRaceNextState_otherState state sigma
  calc
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceExitState state sigma)) =
        Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
          (P.restrict ((gn21RawPostThinningRaceNextState state sigma) ⁻¹' {otherState})) := by
            rw [hother]
    _ = (Measure.map (gn21RawPostThinningRaceNextState state sigma) P {otherState}) • P := by
          simpa [P, otherState] using
            (map_gn21RawPostThinningRaceNextCycleSeed_restrict_nextState
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
              otherState)
    _ = (P (gn21RawPostThinningRaceExitState state sigma)) • P := by
          congr 1
          rw [Measure.map_apply hnext (measurableSet_singleton otherState), hother]

/-- Every finite measurable summary of a literal same-state history prefix is
independent of the unconsumed raw seed, on the actual no-exit event.  This is
the deterministic-index regeneration statement from which the random
first-exit construction is assembled. -/
theorem map_gn21RawCalendarNoExitHistoryFoldAndTraceSeed_restrict_noExitEvent
    {β : Type*} [MeasurableSpace β]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β)
    (hupdate : Measurable fun z : β × GN21RawPostThinningRaceHistory => update z.1 z.2)
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let A := gn21RawCalendarTraceNoExitEvent initialState policy n
    let fold := gn21RawCalendarNoExitHistoryFold initialState policy initial update n
    let tail := gn21RawCalendarTraceSeed initialState policy n
    Measure.map (fun seed => (fold seed, tail seed)) (P.restrict A) =
      (Measure.map fold (P.restrict A)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let historyEvent := (gn21RawPostThinningRaceHistoryNextState initialState) ⁻¹' {initialState}
  let historyLaw := gn21RawPostThinningRaceHistoryMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI initialState (policy initialState)
  let K := historyLaw.restrict historyEvent
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : SFinite historyLaw := by
    simpa [historyLaw] using
      (sfinite_gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState))
  letI : SFinite K := inferInstance
  induction n with
  | zero =>
      simp only [gn21RawCalendarNoExitHistoryFold, gn21RawCalendarTraceSeed,
        gn21RawCalendarTrace, gn21RawCalendarTraceNoExitEvent, Measure.restrict_univ]
      change Measure.map (fun seed : GN21RawCycleSeed => (initial, seed)) P =
        (Measure.map (fun _ : GN21RawCycleSeed => initial) P).prod P
      rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_prod]
  | succ n ih =>
      let A := gn21RawCalendarTraceNoExitEvent initialState policy n
      let tail := gn21RawCalendarTraceSeed initialState policy n
      let fold := gn21RawCalendarNoExitHistoryFold initialState policy initial update n
      let nextTail := gn21RawCalendarTraceSeed initialState policy (n + 1)
      let nextFold := gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1)
      let H := gn21RawPostThinningRaceHistory initialState (policy initialState)
      let next := gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState)
      let pair := fun seed : GN21RawCycleSeed => (fold seed, tail seed)
      let step := gn21RawPostThinningRaceHistoryAndNextCycleSeed initialState
        (policy initialState)
      let L := Measure.map fold (P.restrict A)
      let leftUpdate : β × GN21RawPostThinningRaceHistory -> β := fun z => update z.1 z.2
      let combine : β × (GN21RawPostThinningRaceHistory × GN21RawCycleSeed) ->
          β × GN21RawCycleSeed := fun z => (leftUpdate (z.1, z.2.1), z.2.2)
      let transformed : β × GN21RawCycleSeed -> β × GN21RawCycleSeed := fun z =>
        (update z.1 (H z.2), next z.2)
      have hA : MeasurableSet A :=
        measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
      have htail : Measurable tail :=
        measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
      have hR : MeasurableSet R :=
        (measurableSet_gn21RawPostThinningRaceExitState initialState
          (policy initialState) (hpolicy initialState)).compl
      have hpre : MeasurableSet (tail ⁻¹' R) := hR.preimage htail
      have hpair : Measurable pair :=
        (measurable_gn21RawCalendarNoExitHistoryFold initialState policy hpolicy
          initial update hupdate n).prodMk htail
      have hstep : Measurable step :=
        measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed initialState
          (policy initialState) (hpolicy initialState)
      have hnextTail : Measurable nextTail :=
        measurable_gn21RawCalendarTraceSeed initialState policy hpolicy (n + 1)
      have hnextFold : Measurable nextFold :=
        measurable_gn21RawCalendarNoExitHistoryFold initialState policy hpolicy
          initial update hupdate (n + 1)
      have hnextPair : Measurable (fun seed => (nextFold seed, nextTail seed)) :=
        hnextFold.prodMk hnextTail
      have hleftUpdate : Measurable leftUpdate := by
        exact hupdate
      have hcombine : Measurable combine := by
        exact (hupdate.comp (measurable_fst.prodMk
          (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd)
      have htransformed : transformed = combine ∘ Prod.map id step := by
        rfl
      have hassoc : combine ∘ MeasurableEquiv.prodAssoc = Prod.map leftUpdate id := by
        rfl
      letI : SFinite (P.restrict A) := inferInstance
      letI : SFinite L := inferInstance
      have hrestrict : (P.restrict A).restrict (tail ⁻¹' R) =
          P.restrict (A ∩ tail ⁻¹' R) := by
        rw [Measure.restrict_restrict hpre]
        simp only [Set.inter_comm]
      have hprevious : Measure.map pair (P.restrict (A ∩ tail ⁻¹' R)) =
          L.prod (P.restrict R) := by
        calc
          Measure.map pair (P.restrict (A ∩ tail ⁻¹' R)) =
              Measure.map pair ((P.restrict A).restrict (tail ⁻¹' R)) := by rw [hrestrict]
          _ = Measure.map pair ((P.restrict A).restrict
              (pair ⁻¹' (Set.univ ×ˢ R))) := by
                congr 3
                ext seed
                simp [pair]
          _ = (Measure.map pair (P.restrict A)).restrict (Set.univ ×ˢ R) := by
              exact (Measure.restrict_map hpair (MeasurableSet.univ.prod hR)).symm
          _ = (L.prod P).restrict (Set.univ ×ˢ R) := by
              rw [show Measure.map pair (P.restrict A) = L.prod P by
                simpa [P, A, fold, tail, pair] using ih]
          _ = L.prod (P.restrict R) := by
              rw [← Measure.prod_restrict, Measure.restrict_univ]
      have hstepLaw : Measure.map step (P.restrict R) = K.prod P := by
        simpa [P, R, historyEvent, historyLaw, K, step] using
          (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_noExit
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
            (hpolicy initialState) (hpolicy_subset initialState)
            (hpolicy_mass initialState))
      have hsource : Measure.map (fun seed => (nextFold seed, nextTail seed))
          (P.restrict (A ∩ tail ⁻¹' R)) =
          Measure.map transformed (Measure.map pair (P.restrict (A ∩ tail ⁻¹' R))) := by
        rw [Measure.map_map (by
          exact ((hupdate.comp (measurable_fst.prodMk
            ((measurable_gn21RawPostThinningRaceHistory initialState
              (policy initialState) (hpolicy initialState)).comp measurable_snd))).prodMk
            ((measurable_gn21RawPostThinningRaceNextCycleSeed initialState
              (policy initialState) (hpolicy initialState)).comp measurable_snd))) hpair]
        apply Measure.map_congr
        filter_upwards [MeasureTheory.ae_restrict_mem (hA.inter hpre)] with seed hseed
        have hstate := gn21RawCalendarTraceState_eq_initial_on_noExitEvent
          initialState policy n seed hseed.1
        change (nextFold seed, nextTail seed) = transformed (pair seed)
        simp only [nextFold, gn21RawCalendarNoExitHistoryFold, transformed, pair, H, tail]
        rw [show nextTail seed = next (tail seed) by
          rw [show nextTail seed = gn21RawPostThinningRaceNextCycleSeed
            (gn21RawCalendarTraceState initialState policy n seed)
            (policy (gn21RawCalendarTraceState initialState policy n seed)) (tail seed) by rfl,
            hstate]]
      have hjoint : Measure.map (fun seed => (nextFold seed, nextTail seed))
          (P.restrict (A ∩ tail ⁻¹' R)) =
          (Measure.map leftUpdate (L.prod K)).prod P := by
        calc
          Measure.map (fun seed => (nextFold seed, nextTail seed))
              (P.restrict (A ∩ tail ⁻¹' R)) =
              Measure.map transformed (Measure.map pair (P.restrict (A ∩ tail ⁻¹' R))) := hsource
          _ = Measure.map transformed (L.prod (P.restrict R)) := by rw [hprevious]
          _ = Measure.map combine
              (Measure.map (Prod.map id step) (L.prod (P.restrict R))) := by
                rw [Measure.map_map hcombine (measurable_id.prodMap hstep), htransformed]
          _ = Measure.map combine (L.prod (Measure.map step (P.restrict R))) := by
                rw [← Measure.map_prod_map L (P.restrict R) measurable_id hstep,
                  Measure.map_id]
          _ = Measure.map combine (L.prod (K.prod P)) := by rw [hstepLaw]
          _ = Measure.map combine
              (Measure.map MeasurableEquiv.prodAssoc ((L.prod K).prod P)) := by
                rw [(measurePreserving_prodAssoc L K P).map_eq]
          _ = Measure.map (Prod.map leftUpdate id) ((L.prod K).prod P) := by
                rw [Measure.map_map hcombine MeasurableEquiv.prodAssoc.measurable, hassoc]
          _ = (Measure.map leftUpdate (L.prod K)).prod P := by
                rw [← Measure.map_prod_map (L.prod K) P hleftUpdate measurable_id,
                  Measure.map_id]
      have hfoldLaw : Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' R)) =
          Measure.map leftUpdate (L.prod K) := by
        calc
          Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' R)) =
              Measure.map Prod.fst
                (Measure.map (fun seed => (nextFold seed, nextTail seed))
                  (P.restrict (A ∩ tail ⁻¹' R))) := by
                rw [Measure.map_map measurable_fst hnextPair]
                rfl
          _ = Measure.map Prod.fst ((Measure.map leftUpdate (L.prod K)).prod P) := by
                rw [hjoint]
          _ = Measure.map leftUpdate (L.prod K) := by simp
      change Measure.map (fun seed => (nextFold seed, nextTail seed))
          (P.restrict (A ∩ tail ⁻¹' R)) =
        (Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' R))).prod P
      rw [hfoldLaw]
      exact hjoint

/-- The concrete elapsed-time prefix is the history fold that adds the
time coordinate of each literal subcycle. -/
theorem gn21RawCalendarNoExitAccumulatedTime_eq_historyFold
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) (n : Nat) :
    gn21RawCalendarNoExitAccumulatedTime initialState policy n =
      gn21RawCalendarNoExitHistoryFold initialState policy (0 : Real)
        (fun elapsed history => elapsed + gn21RawPostThinningRaceHistoryTime history) n := by
  funext seed
  induction n generalizing seed with
  | zero => rfl
  | succ n ih =>
      rw [gn21RawCalendarNoExitAccumulatedTime_succ, ih]
      simp only [gn21RawCalendarNoExitHistoryFold]
      congr 1
      exact (gn21RawPostThinningRaceHistoryTime_eq_subcycleTime initialState
        (policy initialState) (gn21RawCalendarTraceSeed initialState policy n seed)).symm

theorem gn21RawCalendarNoExitAccumulatedTime_eq_sum_range
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) (n : Nat)
    (seed : GN21RawCycleSeed) :
    gn21RawCalendarNoExitAccumulatedTime initialState policy n seed =
      ∑ m ∈ Finset.range n,
        gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)
          (gn21RawCalendarTraceSeed initialState policy m seed) := by
  induction n with
  | zero => simp [gn21RawCalendarNoExitAccumulatedTime]
  | succ n ih =>
      rw [gn21RawCalendarNoExitAccumulatedTime_succ, ih]
      rw [Finset.sum_range_succ]

/-- The accumulated literal elapsed time of a finite same-state prefix and
its unconsumed raw seed obey the exact event-bearing product law. -/
theorem map_gn21RawCalendarNoExitAccumulatedTimeAndTraceSeed_restrict_noExitEvent
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let A := gn21RawCalendarTraceNoExitEvent initialState policy n
    let elapsed := gn21RawCalendarNoExitAccumulatedTime initialState policy n
    let tail := gn21RawCalendarTraceSeed initialState policy n
    Measure.map (fun seed => (elapsed seed, tail seed)) (P.restrict A) =
      (Measure.map elapsed (P.restrict A)).prod P := by
  dsimp
  let update : Real -> GN21RawPostThinningRaceHistory -> Real := fun elapsed history =>
    elapsed + gn21RawPostThinningRaceHistoryTime history
  have hupdate : Measurable fun z : Real × GN21RawPostThinningRaceHistory => update z.1 z.2 :=
    measurable_fst.add (measurable_gn21RawPostThinningRaceHistoryTime.comp measurable_snd)
  rw [gn21RawCalendarNoExitAccumulatedTime_eq_historyFold initialState policy n]
  exact map_gn21RawCalendarNoExitHistoryFoldAndTraceSeed_restrict_noExitEvent
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
    hpolicy hpolicy_subset hpolicy_mass 0 update hupdate n

/-- At a literal first cross-state exit, a measurable fold of the whole
same-state prefix and the post-exit raw tail retain the exact product law.
The fold includes the exit subcycle itself. -/
theorem map_gn21RawCalendarNoExitHistoryFoldAndTraceSeed_restrict_exitEvent
    {β : Type*} [MeasurableSpace β]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β)
    (hupdate : Measurable fun z : β × GN21RawPostThinningRaceHistory => update z.1 z.2)
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let exitEvent := gn21RawCalendarTraceExitEvent initialState policy n
    let fold := gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1)
    let tail := gn21RawCalendarTraceSeed initialState policy (n + 1)
    Measure.map (fun seed => (fold seed, tail seed)) (P.restrict exitEvent) =
      (Measure.map fold (P.restrict exitEvent)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawCalendarTraceNoExitEvent initialState policy n
  let E := gn21RawPostThinningRaceExitState initialState (policy initialState)
  let tail := gn21RawCalendarTraceSeed initialState policy n
  let fold := gn21RawCalendarNoExitHistoryFold initialState policy initial update n
  let nextTail := gn21RawCalendarTraceSeed initialState policy (n + 1)
  let nextFold := gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1)
  let H := gn21RawPostThinningRaceHistory initialState (policy initialState)
  let next := gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState)
  let historyEvent := (gn21RawPostThinningRaceHistoryNextState initialState) ⁻¹'
    {AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState}
  let historyLaw := gn21RawPostThinningRaceHistoryMeasure
    muI muJ arrivalI arrivalJ switchIJ switchJI initialState (policy initialState)
  let K := historyLaw.restrict historyEvent
  let pair := fun seed : GN21RawCycleSeed => (fold seed, tail seed)
  let step := gn21RawPostThinningRaceHistoryAndNextCycleSeed initialState
    (policy initialState)
  let L := Measure.map fold (P.restrict A)
  let leftUpdate : β × GN21RawPostThinningRaceHistory -> β := fun z => update z.1 z.2
  let combine : β × (GN21RawPostThinningRaceHistory × GN21RawCycleSeed) ->
      β × GN21RawCycleSeed := fun z => (leftUpdate (z.1, z.2.1), z.2.2)
  let transformed : β × GN21RawCycleSeed -> β × GN21RawCycleSeed := fun z =>
    (update z.1 (H z.2), next z.2)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : SFinite historyLaw := by
    simpa [historyLaw] using
      (sfinite_gn21RawPostThinningRaceHistoryMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState))
  letI : SFinite K := inferInstance
  letI : SFinite (P.restrict A) := inferInstance
  letI : SFinite L := inferInstance
  have hA : MeasurableSet A :=
    measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
  have htail : Measurable tail :=
    measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
  have hE : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState initialState
      (policy initialState) (hpolicy initialState)
  have hpre : MeasurableSet (tail ⁻¹' E) := hE.preimage htail
  have hpair : Measurable pair :=
    (measurable_gn21RawCalendarNoExitHistoryFold initialState policy hpolicy
      initial update hupdate n).prodMk htail
  have hstep : Measurable step :=
    measurable_gn21RawPostThinningRaceHistoryAndNextCycleSeed initialState
      (policy initialState) (hpolicy initialState)
  have hnextTail : Measurable nextTail :=
    measurable_gn21RawCalendarTraceSeed initialState policy hpolicy (n + 1)
  have hnextFold : Measurable nextFold :=
    measurable_gn21RawCalendarNoExitHistoryFold initialState policy hpolicy
      initial update hupdate (n + 1)
  have hnextPair : Measurable (fun seed => (nextFold seed, nextTail seed)) :=
    hnextFold.prodMk hnextTail
  have hleftUpdate : Measurable leftUpdate := hupdate
  have hcombine : Measurable combine :=
    (hupdate.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have htransformed : transformed = combine ∘ Prod.map id step := rfl
  have hassoc : combine ∘ MeasurableEquiv.prodAssoc = Prod.map leftUpdate id := rfl
  have hrestrict : (P.restrict A).restrict (tail ⁻¹' E) =
      P.restrict (A ∩ tail ⁻¹' E) := by
    rw [Measure.restrict_restrict hpre]
    simp only [Set.inter_comm]
  have hprevious : Measure.map pair (P.restrict (A ∩ tail ⁻¹' E)) =
      L.prod (P.restrict E) := by
    calc
      Measure.map pair (P.restrict (A ∩ tail ⁻¹' E)) =
          Measure.map pair ((P.restrict A).restrict (tail ⁻¹' E)) := by rw [hrestrict]
      _ = Measure.map pair ((P.restrict A).restrict
          (pair ⁻¹' (Set.univ ×ˢ E))) := by
            congr 3
            ext seed
            simp [pair]
      _ = (Measure.map pair (P.restrict A)).restrict (Set.univ ×ˢ E) := by
          exact (Measure.restrict_map hpair (MeasurableSet.univ.prod hE)).symm
      _ = (L.prod P).restrict (Set.univ ×ˢ E) := by
          rw [show Measure.map pair (P.restrict A) = L.prod P by
            simpa [P, A, fold, tail, pair] using
              (map_gn21RawCalendarNoExitHistoryFoldAndTraceSeed_restrict_noExitEvent
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
                hpolicy hpolicy_subset hpolicy_mass initial update hupdate n)]
      _ = L.prod (P.restrict E) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hstepLaw : Measure.map step (P.restrict E) = K.prod P := by
    simpa [P, E, historyEvent, historyLaw, K, step] using
      (map_gn21RawPostThinningRaceHistoryAndNextCycleSeed_restrict_exit
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_subset initialState)
        (hpolicy_mass initialState))
  have hsource : Measure.map (fun seed => (nextFold seed, nextTail seed))
      (P.restrict (A ∩ tail ⁻¹' E)) =
      Measure.map transformed (Measure.map pair (P.restrict (A ∩ tail ⁻¹' E))) := by
    rw [Measure.map_map (by
      exact ((hupdate.comp (measurable_fst.prodMk
        ((measurable_gn21RawPostThinningRaceHistory initialState
          (policy initialState) (hpolicy initialState)).comp measurable_snd))).prodMk
        ((measurable_gn21RawPostThinningRaceNextCycleSeed initialState
          (policy initialState) (hpolicy initialState)).comp measurable_snd))) hpair]
    apply Measure.map_congr
    filter_upwards [MeasureTheory.ae_restrict_mem (hA.inter hpre)] with seed hseed
    have hstate := gn21RawCalendarTraceState_eq_initial_on_noExitEvent
      initialState policy n seed hseed.1
    change (nextFold seed, nextTail seed) = transformed (pair seed)
    simp only [nextFold, gn21RawCalendarNoExitHistoryFold, transformed, pair, H, tail]
    rw [show nextTail seed = next (tail seed) by
      rw [show nextTail seed = gn21RawPostThinningRaceNextCycleSeed
        (gn21RawCalendarTraceState initialState policy n seed)
        (policy (gn21RawCalendarTraceState initialState policy n seed)) (tail seed) by rfl,
        hstate]]
  have hjoint : Measure.map (fun seed => (nextFold seed, nextTail seed))
      (P.restrict (A ∩ tail ⁻¹' E)) =
      (Measure.map leftUpdate (L.prod K)).prod P := by
    calc
      Measure.map (fun seed => (nextFold seed, nextTail seed))
          (P.restrict (A ∩ tail ⁻¹' E)) =
          Measure.map transformed (Measure.map pair (P.restrict (A ∩ tail ⁻¹' E))) := hsource
      _ = Measure.map transformed (L.prod (P.restrict E)) := by rw [hprevious]
      _ = Measure.map combine
          (Measure.map (Prod.map id step) (L.prod (P.restrict E))) := by
            rw [Measure.map_map hcombine (measurable_id.prodMap hstep), htransformed]
      _ = Measure.map combine (L.prod (Measure.map step (P.restrict E))) := by
            rw [← Measure.map_prod_map L (P.restrict E) measurable_id hstep,
              Measure.map_id]
      _ = Measure.map combine (L.prod (K.prod P)) := by rw [hstepLaw]
      _ = Measure.map combine
          (Measure.map MeasurableEquiv.prodAssoc ((L.prod K).prod P)) := by
            rw [(measurePreserving_prodAssoc L K P).map_eq]
      _ = Measure.map (Prod.map leftUpdate id) ((L.prod K).prod P) := by
            rw [Measure.map_map hcombine MeasurableEquiv.prodAssoc.measurable, hassoc]
      _ = (Measure.map leftUpdate (L.prod K)).prod P := by
            rw [← Measure.map_prod_map (L.prod K) P hleftUpdate measurable_id,
              Measure.map_id]
  have hfoldLaw : Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' E)) =
      Measure.map leftUpdate (L.prod K) := by
    calc
      Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' E)) =
          Measure.map Prod.fst
            (Measure.map (fun seed => (nextFold seed, nextTail seed))
              (P.restrict (A ∩ tail ⁻¹' E))) := by
            rw [Measure.map_map measurable_fst hnextPair]
            rfl
      _ = Measure.map Prod.fst ((Measure.map leftUpdate (L.prod K)).prod P) := by
            rw [hjoint]
      _ = Measure.map leftUpdate (L.prod K) := by simp
  change Measure.map (fun seed => (nextFold seed, nextTail seed))
      (P.restrict (A ∩ tail ⁻¹' E)) =
    (Measure.map nextFold (P.restrict (A ∩ tail ⁻¹' E))).prod P
  rw [hfoldLaw]
  exact hjoint

/-- Along the actual calendar trace, conditioning on no cross-state exit in
the first `n` subcycles leaves the remaining literal raw tail at its original
law, scaled by the exact continuation-event mass. -/
theorem map_gn21RawCalendarTraceSeed_restrict_noExitEvent
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTraceSeed initialState policy n)
      (P.restrict (gn21RawCalendarTraceNoExitEvent initialState policy n)) =
      (P (gn21RawCalendarTraceNoExitEvent initialState policy n)) • P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  induction n with
  | zero =>
      change Measure.map id (P.restrict Set.univ) = (P Set.univ) • P
      rw [Measure.restrict_univ, Measure.map_id, measure_univ, one_smul]
  | succ n ih =>
      let A := gn21RawCalendarTraceNoExitEvent initialState policy n
      let tail := gn21RawCalendarTraceSeed initialState policy n
      let nextTail := gn21RawCalendarTraceSeed initialState policy (n + 1)
      have hA : MeasurableSet A :=
        measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
      have htail : Measurable tail :=
        measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
      have hR : MeasurableSet R :=
        (measurableSet_gn21RawPostThinningRaceExitState initialState
          (policy initialState) (hpolicy initialState)).compl
      have hpre : MeasurableSet (tail ⁻¹' R) := hR.preimage htail
      have hrestrict : (P.restrict A).restrict (tail ⁻¹' R) =
          P.restrict (A ∩ tail ⁻¹' R) := by
        rw [Measure.restrict_restrict hpre]
        simp only [Set.inter_comm]
      have htailRestrict :
          Measure.map tail (P.restrict (A ∩ tail ⁻¹' R)) =
            (Measure.map tail (P.restrict A)).restrict R := by
        calc
          Measure.map tail (P.restrict (A ∩ tail ⁻¹' R)) =
              Measure.map tail ((P.restrict A).restrict (tail ⁻¹' R)) := by rw [hrestrict]
          _ = (Measure.map tail (P.restrict A)).restrict R := by
              rw [← Measure.restrict_map htail hR]
      have hmass : P (A ∩ tail ⁻¹' R) = P A * P R := by
        calc
          P (A ∩ tail ⁻¹' R) = (P.restrict A) (tail ⁻¹' R) := by
            rw [Measure.restrict_apply hpre]
            simp only [Set.inter_comm]
          _ = Measure.map tail (P.restrict A) R := by
            rw [Measure.map_apply htail hR]
          _ = (P A • P) R := by
            rw [show Measure.map tail (P.restrict A) = P A • P by
              simpa [P, A, tail] using ih]
          _ = P A * P R := by simp
      have hnextSeed : Measurable
          (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState)) :=
        measurable_gn21RawPostThinningRaceNextCycleSeed initialState
          (policy initialState) (hpolicy initialState)
      have hstep : Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' R)) =
          Measure.map (fun seed =>
            gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState) (tail seed))
            (P.restrict (A ∩ tail ⁻¹' R)) := by
        apply Measure.map_congr
        filter_upwards [MeasureTheory.ae_restrict_mem (hA.inter hpre)] with seed hseed
        have hstate := gn21RawCalendarTraceState_eq_initial_on_noExitEvent
          initialState policy n seed hseed.1
        rw [show nextTail seed =
          gn21RawPostThinningRaceNextCycleSeed
            (gn21RawCalendarTraceState initialState policy n seed)
            (policy (gn21RawCalendarTraceState initialState policy n seed))
            (tail seed) by rfl, hstate]
      change Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' R)) =
        (P (A ∩ tail ⁻¹' R)) • P
      calc
        Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' R)) =
            Measure.map (fun seed =>
              gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState) (tail seed))
              (P.restrict (A ∩ tail ⁻¹' R)) := hstep
        _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
            (Measure.map tail (P.restrict (A ∩ tail ⁻¹' R)) ) := by
              rw [Measure.map_map hnextSeed htail]
              rfl
        _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
            ((Measure.map tail (P.restrict A)).restrict R) := by rw [htailRestrict]
        _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
            ((P A • P).restrict R) := by
              rw [show Measure.map tail (P.restrict A) = P A • P by simpa [P, A, tail] using ih]
        _ = (P A * P R) • P := by
              rw [Measure.restrict_smul, Measure.map_smul,
                map_gn21RawPostThinningRaceNextCycleSeed_restrict_noExit
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
                  (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState),
                smul_smul]
        _ = (P (A ∩ tail ⁻¹' R)) • P := by rw [hmass]

/-- Conditioning on exit from the initial physical state in exactly subcycle
`n` leaves the literal raw tail after that exit at its original source law,
with the exact first-exit-event mass retained. -/
theorem map_gn21RawCalendarTraceSeed_restrict_exitEvent
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTraceSeed initialState policy (n + 1))
      (P.restrict (gn21RawCalendarTraceExitEvent initialState policy n)) =
      (P (gn21RawCalendarTraceExitEvent initialState policy n)) • P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawCalendarTraceNoExitEvent initialState policy n
  let E := gn21RawPostThinningRaceExitState initialState (policy initialState)
  let tail := gn21RawCalendarTraceSeed initialState policy n
  let nextTail := gn21RawCalendarTraceSeed initialState policy (n + 1)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hA : MeasurableSet A :=
    measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
  have htail : Measurable tail :=
    measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
  have hE : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState initialState
      (policy initialState) (hpolicy initialState)
  have hpre : MeasurableSet (tail ⁻¹' E) := hE.preimage htail
  have hrestrict : (P.restrict A).restrict (tail ⁻¹' E) =
      P.restrict (A ∩ tail ⁻¹' E) := by
    rw [Measure.restrict_restrict hpre]
    simp only [Set.inter_comm]
  have htailRestrict :
      Measure.map tail (P.restrict (A ∩ tail ⁻¹' E)) =
        (Measure.map tail (P.restrict A)).restrict E := by
    calc
      Measure.map tail (P.restrict (A ∩ tail ⁻¹' E)) =
          Measure.map tail ((P.restrict A).restrict (tail ⁻¹' E)) := by rw [hrestrict]
      _ = (Measure.map tail (P.restrict A)).restrict E := by
          rw [← Measure.restrict_map htail hE]
  have hmass : P (A ∩ tail ⁻¹' E) = P A * P E := by
    calc
      P (A ∩ tail ⁻¹' E) = (P.restrict A) (tail ⁻¹' E) := by
        rw [Measure.restrict_apply hpre]
        simp only [Set.inter_comm]
      _ = Measure.map tail (P.restrict A) E := by
        rw [Measure.map_apply htail hE]
      _ = (P A • P) E := by
        rw [show Measure.map tail (P.restrict A) = P A • P by
          simpa [P, A, tail] using
            (map_gn21RawCalendarTraceSeed_restrict_noExitEvent
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
              hpolicy hpolicy_subset hpolicy_mass n)]
      _ = P A * P E := by simp
  have hnextSeed : Measurable
      (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState)) :=
    measurable_gn21RawPostThinningRaceNextCycleSeed initialState
      (policy initialState) (hpolicy initialState)
  have hstep : Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' E)) =
      Measure.map (fun seed =>
        gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState) (tail seed))
        (P.restrict (A ∩ tail ⁻¹' E)) := by
    apply Measure.map_congr
    filter_upwards [MeasureTheory.ae_restrict_mem (hA.inter hpre)] with seed hseed
    have hstate := gn21RawCalendarTraceState_eq_initial_on_noExitEvent
      initialState policy n seed hseed.1
    rw [show nextTail seed =
      gn21RawPostThinningRaceNextCycleSeed
        (gn21RawCalendarTraceState initialState policy n seed)
        (policy (gn21RawCalendarTraceState initialState policy n seed))
        (tail seed) by rfl, hstate]
  change Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' E)) =
    (P (A ∩ tail ⁻¹' E)) • P
  calc
    Measure.map nextTail (P.restrict (A ∩ tail ⁻¹' E)) =
        Measure.map (fun seed =>
          gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState) (tail seed))
          (P.restrict (A ∩ tail ⁻¹' E)) := hstep
    _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
        (Measure.map tail (P.restrict (A ∩ tail ⁻¹' E))) := by
          rw [Measure.map_map hnextSeed htail]
          rfl
    _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
        ((Measure.map tail (P.restrict A)).restrict E) := by rw [htailRestrict]
    _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed initialState (policy initialState))
        ((P A • P).restrict E) := by
          rw [show Measure.map tail (P.restrict A) = P A • P by
            simpa [P, A, tail] using
              (map_gn21RawCalendarTraceSeed_restrict_noExitEvent
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
                hpolicy hpolicy_subset hpolicy_mass n)]
    _ = (P A * P E) • P := by
          rw [Measure.restrict_smul, Measure.map_smul,
            map_gn21RawPostThinningRaceNextCycleSeed_restrict_exit
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
              (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState),
            smul_smul]
    _ = (P (A ∩ tail ⁻¹' E)) • P := by rw [hmass]

/-- The literal calendar continuation event has the geometric mass implied by
repeated same-state residualization. -/
theorem measure_gn21RawCalendarTraceNoExitEvent
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    P (gn21RawCalendarTraceNoExitEvent initialState policy n) =
      (P (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ) ^ n := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  induction n with
  | zero => simp [gn21RawCalendarTraceNoExitEvent]
  | succ n ih =>
      let A := gn21RawCalendarTraceNoExitEvent initialState policy n
      let tail := gn21RawCalendarTraceSeed initialState policy n
      have htail : Measurable tail :=
        measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
      have hR : MeasurableSet R :=
        (measurableSet_gn21RawPostThinningRaceExitState initialState
          (policy initialState) (hpolicy initialState)).compl
      have hpre : MeasurableSet (tail ⁻¹' R) := hR.preimage htail
      have hmass : P (A ∩ tail ⁻¹' R) = P A * P R := by
        calc
          P (A ∩ tail ⁻¹' R) = (P.restrict A) (tail ⁻¹' R) := by
            rw [Measure.restrict_apply hpre]
            simp only [Set.inter_comm]
          _ = Measure.map tail (P.restrict A) R := by
            rw [Measure.map_apply htail hR]
          _ = (P A • P) R := by
            rw [show Measure.map tail (P.restrict A) = P A • P by
              simpa [P, A, tail] using
                (map_gn21RawCalendarTraceSeed_restrict_noExitEvent
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
                  hpolicy hpolicy_subset hpolicy_mass n)]
          _ = P A * P R := by simp
      change P (A ∩ tail ⁻¹' R) = (P R) ^ (n + 1)
      rw [hmass]
      rw [show P A = P R ^ n by simpa [P, R, A] using ih, pow_succ]

/-- If a same-state continuation has probability strictly below one, the
literal calendar trace leaves that state after finitely many subcycles almost
surely.  The proof uses the nested actual-trace events and their geometric
mass, rather than an independently proposed sequence of subcycles. -/
theorem measure_gn21RawCalendarTraceNeverExitEvent_eq_zero_of_noExit_lt_one
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hnoExit_lt_one :
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ < 1) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawCalendarTraceNeverExitEvent initialState policy) = 0 := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  have hsubset : ∀ n : Nat,
      Never ⊆ gn21RawCalendarTraceNoExitEvent initialState policy n := by
    intro n seed hseed
    exact Set.mem_iInter.mp hseed n
  have hbound : ∀ n : Nat, P Never ≤ (P R) ^ n := by
    intro n
    calc
      P Never ≤ P (gn21RawCalendarTraceNoExitEvent initialState policy n) :=
        measure_mono (hsubset n)
      _ = (P R) ^ n := by
        simpa [P, R] using
          (measure_gn21RawCalendarTraceNoExitEvent
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
            hpolicy hpolicy_subset hpolicy_mass n)
  have hpow : Tendsto (fun n : Nat => (P R) ^ n) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simpa [P, R] using hnoExit_lt_one)
  change P Never = 0
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbound
  · exact bot_le

/-- Under GN's positive-rate and positive-policy-mass primitives, the literal
calendar trace cannot remain forever in its initial state. -/
theorem measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawCalendarTraceNeverExitEvent initialState policy) = 0 := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState initialState (policy initialState)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_meas : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState initialState
      (policy initialState) (hpolicy initialState)
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
          (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState))
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hnoExit_lt_one : P Eᶜ < 1 := by
    rw [measure_compl hE_meas (measure_ne_top P E), measure_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hE_pos.ne'
  simpa [P, E] using
    (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero_of_noExit_lt_one
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass hnoExit_lt_one)

/-- Almost every literal raw seed produces a finite subcycle index at which
the calendar trace has left its initial state. -/
theorem ae_exists_gn21RawCalendarTraceExit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∃ n, seed ∉ gn21RawCalendarTraceNoExitEvent initialState policy n := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  have hzero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hset :
      {seed | ¬ ∃ n, seed ∉ gn21RawCalendarTraceNoExitEvent initialState policy n} = Never := by
    ext seed
    simp [Never, gn21RawCalendarTraceNeverExitEvent]
  rw [MeasureTheory.ae_iff]
  change P {seed | ¬ ∃ n, seed ∉ gn21RawCalendarTraceNoExitEvent initialState policy n} = 0
  rw [hset]
  exact hzero

/-- The literal no-exit events are decreasing in the number of completed
same-state subcycles. -/
theorem gn21RawCalendarTraceNoExitEvent_antitone (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) :
    Antitone (gn21RawCalendarTraceNoExitEvent initialState policy) := by
  apply antitone_nat_of_succ_le
  intro n seed hseed
  change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
    (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
      (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ at hseed
  exact hseed.1

/-- The exact literal first-exit events for distinct subcycle indices are
pairwise disjoint. -/
theorem gn21RawCalendarTraceExitEvent_pairwiseDisjoint (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) :
    Pairwise (Function.onFun Disjoint (gn21RawCalendarTraceExitEvent initialState policy)) := by
  intro n m hne
  refine Set.disjoint_left.2 ?_
  intro seed hn hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcontinue : seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy (n + 1) :=
      (gn21RawCalendarTraceNoExitEvent_antitone initialState policy)
        (Nat.succ_le_of_lt hlt) hm.1
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState)) at hn
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ at hcontinue
    exact hcontinue.2 hn.2
  · have hcontinue : seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy (m + 1) :=
      (gn21RawCalendarTraceNoExitEvent_antitone initialState policy)
        (Nat.succ_le_of_lt hgt) hn.1
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy m ∩
      (gn21RawCalendarTraceSeed initialState policy m) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState)) at hm
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy m ∩
      (gn21RawCalendarTraceSeed initialState policy m) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ at hcontinue
    exact hcontinue.2 hm.2

/-- The union of the exact literal first-exit events is precisely the
complement of never leaving the initial physical state. -/
theorem iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    ⋃ n : Nat, gn21RawCalendarTraceExitEvent initialState policy n =
      (gn21RawCalendarTraceNeverExitEvent initialState policy)ᶜ := by
  classical
  ext seed
  constructor
  · intro hunion hnever
    rcases Set.mem_iUnion.mp hunion with ⟨n, hn⟩
    have hcontinue := Set.mem_iInter.mp hnever (n + 1)
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState)) at hn
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ at hcontinue
    exact hcontinue.2 hn.2
  · intro hnotNever
    have hfailure : ∃ n, seed ∉ gn21RawCalendarTraceNoExitEvent initialState policy n := by
      simpa [gn21RawCalendarTraceNeverExitEvent] using hnotNever
    let n := Nat.find hfailure
    have hnfail : seed ∉ gn21RawCalendarTraceNoExitEvent initialState policy n :=
      Nat.find_spec hfailure
    have hn_ne_zero : n ≠ 0 := by
      intro hzero
      apply hnfail
      simpa [hzero, gn21RawCalendarTraceNoExitEvent]
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨k, hk⟩
    rw [hk] at hnfail
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    have hprior : seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy k := by
      apply not_not.mp
      apply Nat.find_min hfailure
      change k < n
      rw [hk]
      exact Nat.lt_succ_self k
    have hnotContinue : seed ∉
        (gn21RawCalendarTraceSeed initialState policy k) ⁻¹'
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ := by
      intro hcontinue
      apply hnfail
      exact ⟨hprior, hcontinue⟩
    change seed ∈ gn21RawCalendarTraceNoExitEvent initialState policy k ∩
      (gn21RawCalendarTraceSeed initialState policy k) ⁻¹'
        (gn21RawPostThinningRaceExitState initialState (policy initialState))
    refine ⟨hprior, ?_⟩
    simpa using hnotContinue

/-- On an exact literal first-exit event, the totalized first-exit index is
that event's subcycle index. -/
theorem gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent
    {initialState : Fin 2} {policy : Fin 2 -> TripPolicy} {n : Nat}
    {seed : GN21RawCycleSeed}
    (hmem : seed ∈ gn21RawCalendarTraceExitEvent initialState policy n) :
    gn21RawCalendarFirstExitIndex initialState policy seed = n := by
  classical
  let hexists : ∃ m, seed ∈ gn21RawCalendarTraceExitEvent initialState policy m :=
    ⟨n, hmem⟩
  rw [gn21RawCalendarFirstExitIndex, dif_pos hexists]
  apply Nat.le_antisymm
  · exact Nat.find_min' hexists hmem
  · apply le_of_not_gt
    intro hlt
    have hne : n ≠ Nat.find hexists := (Nat.ne_of_lt hlt).symm
    exact (Set.disjoint_left.mp
      (gn21RawCalendarTraceExitEvent_pairwiseDisjoint initialState policy hne))
      hmem (Nat.find_spec hexists)

/-- The zero fiber of the totalized first-exit index contains the literal
immediate-exit event and, only on the null exceptional branch, never exit. -/
theorem gn21RawCalendarFirstExitIndex_event_zero (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) :
    {seed | gn21RawCalendarFirstExitIndex initialState policy seed = 0} =
      gn21RawCalendarTraceExitEvent initialState policy 0 ∪
        gn21RawCalendarTraceNeverExitEvent initialState policy := by
  ext seed
  classical
  constructor
  · intro hzero
    change gn21RawCalendarFirstExitIndex initialState policy seed = 0 at hzero
    by_cases hexists : ∃ n, seed ∈ gn21RawCalendarTraceExitEvent initialState policy n
    · left
      have hfind : Nat.find hexists = 0 := by
        unfold gn21RawCalendarFirstExitIndex at hzero
        rw [dif_pos hexists] at hzero
        exact hzero
      have hspec := Nat.find_spec hexists
      rw [hfind] at hspec
      exact hspec
    · right
      have hnotUnion : seed ∉ ⋃ n : Nat,
          gn21RawCalendarTraceExitEvent initialState policy n := by
        intro hunion
        rcases Set.mem_iUnion.mp hunion with ⟨n, hn⟩
        exact hexists ⟨n, hn⟩
      rw [iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent] at hnotUnion
      simpa using hnotUnion
  · rintro (hexit | hnever)
    · exact gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hexit
    · have hnone : ¬ ∃ n, seed ∈ gn21RawCalendarTraceExitEvent initialState policy n := by
        rintro ⟨n, hn⟩
        have hunion : seed ∈ ⋃ n : Nat,
            gn21RawCalendarTraceExitEvent initialState policy n :=
          Set.mem_iUnion.mpr ⟨n, hn⟩
        rw [iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent] at hunion
        exact hunion hnever
      change gn21RawCalendarFirstExitIndex initialState policy seed = 0
      unfold gn21RawCalendarFirstExitIndex
      rw [dif_neg hnone]

/-- Positive fibers of the totalized first-exit index are the corresponding
exact literal first-exit events. -/
theorem gn21RawCalendarFirstExitIndex_event_succ (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (n : Nat) :
    {seed | gn21RawCalendarFirstExitIndex initialState policy seed = n + 1} =
      gn21RawCalendarTraceExitEvent initialState policy (n + 1) := by
  ext seed
  classical
  constructor
  · intro hindex
    change gn21RawCalendarFirstExitIndex initialState policy seed = n + 1 at hindex
    by_cases hexists : ∃ m, seed ∈ gn21RawCalendarTraceExitEvent initialState policy m
    · have hfind : Nat.find hexists = n + 1 := by
        unfold gn21RawCalendarFirstExitIndex at hindex
        rw [dif_pos hexists] at hindex
        exact hindex
      have hspec := Nat.find_spec hexists
      rw [hfind] at hspec
      exact hspec
    · exfalso
      have hzero : gn21RawCalendarFirstExitIndex initialState policy seed = 0 := by
        unfold gn21RawCalendarFirstExitIndex
        rw [dif_neg hexists]
      rw [hzero] at hindex
      omega
  · intro hexit
    exact gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hexit

/-- The totalized first-exit index has measurable fibers. -/
theorem measurableSet_gn21RawCalendarFirstExitIndex_event (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state))
    (n : Nat) : MeasurableSet
      {seed | gn21RawCalendarFirstExitIndex initialState policy seed = n} := by
  cases n with
  | zero =>
      rw [gn21RawCalendarFirstExitIndex_event_zero]
      apply (measurableSet_gn21RawCalendarTraceExitEvent initialState policy hpolicy 0).union
      rw [show gn21RawCalendarTraceNeverExitEvent initialState policy =
          ⋂ n : Nat, gn21RawCalendarTraceNoExitEvent initialState policy n by rfl]
      apply MeasurableSet.iInter
      intro n
      exact measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
  | succ n =>
      rw [gn21RawCalendarFirstExitIndex_event_succ]
      exact measurableSet_gn21RawCalendarTraceExitEvent initialState policy hpolicy (n + 1)

/-- The literal raw tail immediately after the totalized first cross-state
exit is measurable. -/
theorem measurable_gn21RawCalendarPostExitSeed (initialState : Fin 2)
    (policy : Fin 2 -> TripPolicy) (hpolicy : ∀ state, MeasurableSet (policy state)) :
    Measurable (gn21RawCalendarPostExitSeed initialState policy) := by
  change Measurable (fun seed => gn21RawCalendarTraceSeed initialState policy
    (gn21RawCalendarFirstExitIndex initialState policy seed + 1) seed)
  let h : ∀ seed : GN21RawCycleSeed, ∃ n,
      gn21RawCalendarFirstExitIndex initialState policy seed = n :=
    fun seed => ⟨gn21RawCalendarFirstExitIndex initialState policy seed, rfl⟩
  have hmeas : Measurable (fun seed : GN21RawCycleSeed =>
      gn21RawCalendarTraceSeed initialState policy (Nat.find (h seed) + 1) seed) :=
    Measurable.find
      (fun n => measurable_gn21RawCalendarTraceSeed initialState policy hpolicy (n + 1))
      (fun n => measurableSet_gn21RawCalendarFirstExitIndex_event initialState policy hpolicy n)
      h
  convert hmeas using 1
  funext seed
  rw [show Nat.find (h seed) = gn21RawCalendarFirstExitIndex initialState policy seed by
    exact (Nat.find_spec (h seed)).symm]

/-- A totalized measurable summary of every literal history through the first
cross-state exit.  On the null never-exit branch its index is totalized at
zero, consistently with `gn21RawCalendarFirstExitIndex`. -/
noncomputable def gn21RawCalendarFirstExitHistoryFold
    {β : Type*} (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β) :
    GN21RawCycleSeed -> β := fun seed =>
  gn21RawCalendarNoExitHistoryFold initialState policy initial update
    (gn21RawCalendarFirstExitIndex initialState policy seed + 1) seed

theorem measurable_gn21RawCalendarFirstExitHistoryFold
    {β : Type*} [MeasurableSpace β]
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β)
    (hupdate : Measurable fun z : β × GN21RawPostThinningRaceHistory => update z.1 z.2) :
    Measurable (gn21RawCalendarFirstExitHistoryFold initialState policy initial update) := by
  change Measurable (fun seed =>
    gn21RawCalendarNoExitHistoryFold initialState policy initial update
      (gn21RawCalendarFirstExitIndex initialState policy seed + 1) seed)
  let h : ∀ seed : GN21RawCycleSeed, ∃ n,
      gn21RawCalendarFirstExitIndex initialState policy seed = n :=
    fun seed => ⟨gn21RawCalendarFirstExitIndex initialState policy seed, rfl⟩
  have hmeas : Measurable (fun seed : GN21RawCycleSeed =>
      gn21RawCalendarNoExitHistoryFold initialState policy initial update
        (Nat.find (h seed) + 1) seed) :=
    Measurable.find
      (fun n => measurable_gn21RawCalendarNoExitHistoryFold initialState policy hpolicy
        initial update hupdate (n + 1))
      (fun n => measurableSet_gn21RawCalendarFirstExitIndex_event initialState policy hpolicy n)
      h
  convert hmeas using 1
  funext seed
  rw [show Nat.find (h seed) = gn21RawCalendarFirstExitIndex initialState policy seed by
    exact (Nat.find_spec (h seed)).symm]

/-- The elapsed time accumulated through the actual first cross-state exit,
read as the time-coordinate fold of its complete literal history. -/
noncomputable def gn21RawCalendarFirstExitAccumulatedTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> Real :=
  gn21RawCalendarFirstExitHistoryFold initialState policy 0
    (fun elapsed history => elapsed + gn21RawPostThinningRaceHistoryTime history)

theorem measurable_gn21RawCalendarFirstExitAccumulatedTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) :
    Measurable (gn21RawCalendarFirstExitAccumulatedTime initialState policy) := by
  exact measurable_gn21RawCalendarFirstExitHistoryFold initialState policy hpolicy 0
    (fun elapsed history => elapsed + gn21RawPostThinningRaceHistoryTime history)
    (measurable_fst.add (measurable_gn21RawPostThinningRaceHistoryTime.comp measurable_snd))

/-- The payment accumulated through the actual first cross-state exit, read
from the same complete measurable history fold as the time coordinate. -/
noncomputable def gn21RawCalendarFirstExitAccumulatedEarning
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> Real :=
  gn21RawCalendarFirstExitHistoryFold initialState policy 0
    (fun earned history => earned + gn21RawPostThinningRaceHistoryEarning w history)

theorem measurable_gn21RawCalendarFirstExitAccumulatedEarning
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (hw : Measurable w) :
    Measurable (gn21RawCalendarFirstExitAccumulatedEarning initialState w policy) := by
  exact measurable_gn21RawCalendarFirstExitHistoryFold initialState policy hpolicy 0
    (fun earned history => earned + gn21RawPostThinningRaceHistoryEarning w history)
    (measurable_fst.add
      ((measurable_gn21RawPostThinningRaceHistoryEarning w hw).comp measurable_snd))

/-- On a literal exact first-exit event, the finite history-fold elapsed time
is exactly the existing stopped calendar-time definition. -/
theorem gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime_of_mem_exitEvent
    {initialState : Fin 2} {policy : Fin 2 -> TripPolicy} {n : Nat}
    {seed : GN21RawCycleSeed}
    (hmem : seed ∈ gn21RawCalendarTraceExitEvent initialState policy n) :
    gn21RawCalendarFirstExitAccumulatedTime initialState policy seed =
      gn21RawCalendarStoppedStateTime initialState policy seed := by
  let A := gn21RawCalendarTraceNoExitEvent initialState policy
  let E := gn21RawPostThinningRaceExitState initialState (policy initialState)
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let sub : Nat -> Real := fun m =>
    gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)
      (gn21RawCalendarTraceSeed initialState policy m seed)
  have hA_n : seed ∈ A n := hmem.1
  have hnotA_succ : seed ∉ A (n + 1) := by
    intro hcontinue
    change seed ∈ A n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹' R at hcontinue
    change seed ∈ A n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹' E at hmem
    exact hcontinue.2 hmem.2
  have hnotA (m : Nat) (hm : n + 1 ≤ m) : seed ∉ A m := by
    intro hA_m
    apply hnotA_succ
    exact (gn21RawCalendarTraceNoExitEvent_antitone initialState policy hm) hA_m
  have hstopped : gn21RawCalendarStoppedStateTime initialState policy seed =
      ∑ m ∈ Finset.range (n + 1), sub m := by
    change (∑' m : Nat, gn21RawCalendarTraceNoExitReward initialState policy
      (gn21RawPostThinningRaceSubcycleTime initialState (policy initialState)) m seed) = _
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hA_m : seed ∈ A m :=
        (gn21RawCalendarTraceNoExitEvent_antitone initialState policy hmle) hA_n
      simp [gn21RawCalendarTraceNoExitReward, sub, A, Set.indicator_of_mem hA_m]
    · intro m hm
      have hmle : n + 1 ≤ m := Nat.le_of_not_gt (by
        simpa [Finset.mem_range] using hm)
      rw [gn21RawCalendarTraceNoExitReward, Set.indicator_of_notMem (hnotA m hmle)]
  have hindex := gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hmem
  calc
    gn21RawCalendarFirstExitAccumulatedTime initialState policy seed =
        gn21RawCalendarNoExitHistoryFold initialState policy 0
          (fun elapsed history => elapsed + gn21RawPostThinningRaceHistoryTime history)
          (n + 1) seed := by
            simp [gn21RawCalendarFirstExitAccumulatedTime,
              gn21RawCalendarFirstExitHistoryFold, hindex]
    _ = gn21RawCalendarNoExitAccumulatedTime initialState policy (n + 1) seed := by
          rw [← gn21RawCalendarNoExitAccumulatedTime_eq_historyFold initialState policy (n + 1)]
    _ = ∑ m ∈ Finset.range (n + 1), sub m := by
          simpa [sub] using
            (gn21RawCalendarNoExitAccumulatedTime_eq_sum_range initialState policy (n + 1) seed)
    _ = gn21RawCalendarStoppedStateTime initialState policy seed := hstopped.symm

/-- On an exact first-exit fiber, the finite history-fold payment is exactly
the existing stopped calendar-earning sum. -/
theorem gn21RawCalendarFirstExitAccumulatedEarning_eq_stoppedStateEarning_of_mem_exitEvent
    {initialState : Fin 2} {w : PricingFunction} {policy : Fin 2 -> TripPolicy}
    {n : Nat} {seed : GN21RawCycleSeed}
    (hmem : seed ∈ gn21RawCalendarTraceExitEvent initialState policy n) :
    gn21RawCalendarFirstExitAccumulatedEarning initialState w policy seed =
      gn21RawCalendarStoppedStateEarning initialState w policy seed := by
  let A := gn21RawCalendarTraceNoExitEvent initialState policy
  let E := gn21RawPostThinningRaceExitState initialState (policy initialState)
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let sub : Nat -> Real := fun m =>
    gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)
      (gn21RawCalendarTraceSeed initialState policy m seed)
  have hA_n : seed ∈ A n := hmem.1
  have hnotA_succ : seed ∉ A (n + 1) := by
    intro hcontinue
    change seed ∈ A n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹' R at hcontinue
    change seed ∈ A n ∩
      (gn21RawCalendarTraceSeed initialState policy n) ⁻¹' E at hmem
    exact hcontinue.2 hmem.2
  have hnotA (m : Nat) (hm : n + 1 ≤ m) : seed ∉ A m := by
    intro hA_m
    apply hnotA_succ
    exact (gn21RawCalendarTraceNoExitEvent_antitone initialState policy hm) hA_m
  have hstopped : gn21RawCalendarStoppedStateEarning initialState w policy seed =
      ∑ m ∈ Finset.range (n + 1), sub m := by
    change (∑' m : Nat, gn21RawCalendarTraceNoExitReward initialState policy
      (gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState)) m seed) = _
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hA_m : seed ∈ A m :=
        (gn21RawCalendarTraceNoExitEvent_antitone initialState policy hmle) hA_n
      simp [gn21RawCalendarTraceNoExitReward, sub, A, Set.indicator_of_mem hA_m]
    · intro m hm
      have hmle : n + 1 ≤ m := Nat.le_of_not_gt (by
        simpa [Finset.mem_range] using hm)
      rw [gn21RawCalendarTraceNoExitReward, Set.indicator_of_notMem (hnotA m hmle)]
  have hindex := gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hmem
  calc
    gn21RawCalendarFirstExitAccumulatedEarning initialState w policy seed =
        gn21RawCalendarNoExitHistoryFold initialState policy 0
          (fun earned history => earned + gn21RawPostThinningRaceHistoryEarning w history)
          (n + 1) seed := by
            simp [gn21RawCalendarFirstExitAccumulatedEarning,
              gn21RawCalendarFirstExitHistoryFold, hindex]
    _ = gn21RawCalendarNoExitAccumulatedEarning initialState w policy (n + 1) seed := by
          rw [← gn21RawCalendarNoExitAccumulatedEarning_eq_historyFold]
    _ = ∑ m ∈ Finset.range (n + 1), sub m := by
          simpa [sub] using
            (gn21RawCalendarNoExitAccumulatedEarning_eq_sum_range
              initialState w policy (n + 1) seed)
    _ = gn21RawCalendarStoppedStateEarning initialState w policy seed := hstopped.symm

/-- The measurable first-exit history fold agrees almost surely with the
existing stopped calendar-time sum; only the totalization on never-exit paths
can differ, and that event has zero source probability. -/
theorem ae_gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    gn21RawCalendarFirstExitAccumulatedTime initialState policy =ᵐ[P]
      gn21RawCalendarStoppedStateTime initialState policy := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Exit := gn21RawCalendarTraceExitEvent initialState policy
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  let good : Set GN21RawCycleSeed := ⋃ n : Nat, Exit n
  have hnever_zero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hgood_ae : ∀ᵐ seed ∂P, seed ∈ good := by
    rw [MeasureTheory.ae_iff]
    have hunion : good = Neverᶜ := by
      simpa [good, Exit, Never] using
        (iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent initialState policy)
    change P goodᶜ = 0
    rw [hunion]
    simpa using hnever_zero
  filter_upwards [hgood_ae] with seed hseed
  rcases Set.mem_iUnion.mp hseed with ⟨n, hn⟩
  exact gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime_of_mem_exitEvent hn

/-- The measurable first-exit payment fold agrees almost surely with the
existing stopped payment sum; as for time, only the null never-exit branch is
totalized differently. -/
theorem ae_gn21RawCalendarFirstExitAccumulatedEarning_eq_stoppedStateEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    gn21RawCalendarFirstExitAccumulatedEarning initialState w policy =ᵐ[P]
      gn21RawCalendarStoppedStateEarning initialState w policy := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Exit := gn21RawCalendarTraceExitEvent initialState policy
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  let good : Set GN21RawCycleSeed := ⋃ n : Nat, Exit n
  have hnever_zero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hgood_ae : ∀ᵐ seed ∂P, seed ∈ good := by
    rw [MeasureTheory.ae_iff]
    have hunion : good = Neverᶜ := by
      simpa [good, Exit, Never] using
        (iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent initialState policy)
    change P goodᶜ = 0
    rw [hunion]
    simpa using hnever_zero
  filter_upwards [hgood_ae] with seed hseed
  rcases Set.mem_iUnion.mp hseed with ⟨n, hn⟩
  exact
    gn21RawCalendarFirstExitAccumulatedEarning_eq_stoppedStateEarning_of_mem_exitEvent hn

/-- The literal raw tail after the a.s.-finite first cross-state exit has its
original source law.  The proof sums the exact disjoint first-exit fibers;
the totalization branch is the already-proved null never-exit event. -/
theorem map_gn21RawCalendarPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarPostExitSeed initialState policy) P = P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Exit := gn21RawCalendarTraceExitEvent initialState policy
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  let good : Set GN21RawCycleSeed := ⋃ n : Nat, Exit n
  let postTail := gn21RawCalendarPostExitSeed initialState policy
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hnever_zero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hgood_ae : ∀ᵐ seed ∂P, seed ∈ good := by
    rw [MeasureTheory.ae_iff]
    have hunion : good = Neverᶜ := by
      simpa [good, Exit, Never] using
        (iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent initialState policy)
    change P goodᶜ = 0
    rw [hunion]
    simpa using hnever_zero
  have hpostTail : Measurable postTail := by
    simpa [postTail] using
      (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)
  have hsum_exit : ∑' n : Nat, P (Exit n) = 1 := by
    calc
      ∑' n : Nat, P (Exit n) = P good := by
        symm
        exact measure_iUnion
          (by simpa [Exit] using
            (gn21RawCalendarTraceExitEvent_pairwiseDisjoint initialState policy))
          (by
            intro n
            simpa [Exit] using
              (measurableSet_gn21RawCalendarTraceExitEvent initialState policy hpolicy n))
      _ = P Set.univ := by
        apply measure_congr
        filter_upwards [hgood_ae] with seed hseed
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          exact hseed
      _ = 1 := measure_univ
  apply Measure.ext
  intro s hs
  let pieces : Nat -> Set GN21RawCycleSeed := fun n =>
    Exit n ∩ (gn21RawCalendarTraceSeed initialState policy (n + 1)) ⁻¹' s
  have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
    intro n
    exact (measurableSet_gn21RawCalendarTraceExitEvent initialState policy hpolicy n).inter
      (hs.preimage (measurable_gn21RawCalendarTraceSeed initialState policy hpolicy (n + 1)))
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hne
    refine Set.disjoint_left.2 ?_
    intro seed hn hm
    exact (Set.disjoint_left.mp
      (gn21RawCalendarTraceExitEvent_pairwiseDisjoint initialState policy hne))
      hn.1 hm.1
  have hpieces_union : ⋃ n : Nat, pieces n = postTail ⁻¹' s ∩ good := by
    ext seed
    constructor
    · intro hpieces
      rcases Set.mem_iUnion.mp hpieces with ⟨n, hn⟩
      refine ⟨?_, Set.mem_iUnion.mpr ⟨n, hn.1⟩⟩
      change gn21RawCalendarPostExitSeed initialState policy seed ∈ s
      unfold gn21RawCalendarPostExitSeed
      rw [gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hn.1]
      exact hn.2
    · rintro ⟨hpost, hgood⟩
      rcases Set.mem_iUnion.mp hgood with ⟨n, hn⟩
      apply Set.mem_iUnion.mpr
      refine ⟨n, hn, ?_⟩
      change gn21RawCalendarPostExitSeed initialState policy seed ∈ s at hpost
      unfold gn21RawCalendarPostExitSeed at hpost
      rw [gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hn] at hpost
      exact hpost
  have hmeasure_pieces : P (postTail ⁻¹' s) = ∑' n : Nat, P (pieces n) := by
    calc
      P (postTail ⁻¹' s) = P (postTail ⁻¹' s ∩ good) := by
        apply measure_congr
        filter_upwards [hgood_ae] with seed hseed
        apply propext
        constructor
        · intro hpost
          exact ⟨hpost, hseed⟩
        · exact fun hpost => hpost.1
      _ = P (⋃ n : Nat, pieces n) := by rw [hpieces_union]
      _ = ∑' n : Nat, P (pieces n) := measure_iUnion hpieces_disjoint hpieces_meas
  have hpiece_factor : ∀ n : Nat, P (pieces n) = P (Exit n) * P s := by
    intro n
    let tail := gn21RawCalendarTraceSeed initialState policy (n + 1)
    have htail : Measurable tail :=
      measurable_gn21RawCalendarTraceSeed initialState policy hpolicy (n + 1)
    have hpre : MeasurableSet (tail ⁻¹' s) := hs.preimage htail
    have hmap : Measure.map tail (P.restrict (Exit n)) = P (Exit n) • P := by
      simpa [P, Exit, tail] using
        (map_gn21RawCalendarTraceSeed_restrict_exitEvent
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
          hpolicy hpolicy_subset hpolicy_mass n)
    calc
      P (pieces n) = (P.restrict (Exit n)) (tail ⁻¹' s) := by
        rw [Measure.restrict_apply hpre]
        simp only [pieces, tail, Set.inter_comm]
      _ = Measure.map tail (P.restrict (Exit n)) s := by
        rw [Measure.map_apply htail hs]
      _ = (P (Exit n) • P) s := by rw [hmap]
      _ = P (Exit n) * P s := by simp
  calc
    Measure.map postTail P s = P (postTail ⁻¹' s) := Measure.map_apply hpostTail hs
    _ = ∑' n : Nat, P (pieces n) := hmeasure_pieces
    _ = ∑' n : Nat, P (Exit n) * P s := by
      apply tsum_congr
      intro n
      exact hpiece_factor n
    _ = (∑' n : Nat, P (Exit n)) * P s := ENNReal.tsum_mul_right
    _ = P s := by rw [hsum_exit, one_mul]

/-- The complete measurable history summary through the actual random first
cross-state exit is independent of the literal post-exit raw tail.  This is
proved by summing the disjoint, event-bearing finite exit kernels rather than
postulating a strong-Markov restart. -/
theorem map_gn21RawCalendarFirstExitHistoryFoldAndPostExitSeed
    {β : Type*} [MeasurableSpace β]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (initial : β) (update : β -> GN21RawPostThinningRaceHistory -> β)
    (hupdate : Measurable fun z : β × GN21RawPostThinningRaceHistory => update z.1 z.2) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let fold := gn21RawCalendarFirstExitHistoryFold initialState policy initial update
    let postTail := gn21RawCalendarPostExitSeed initialState policy
    Measure.map (fun seed => (fold seed, postTail seed)) P =
      (Measure.map fold P).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Exit := gn21RawCalendarTraceExitEvent initialState policy
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  let good : Set GN21RawCycleSeed := ⋃ n : Nat, Exit n
  let fold := gn21RawCalendarFirstExitHistoryFold initialState policy initial update
  let postTail := gn21RawCalendarPostExitSeed initialState policy
  let pair := fun seed : GN21RawCycleSeed => (fold seed, postTail seed)
  let M : Nat -> Measure β := fun n => Measure.map
    (gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1))
    (P.restrict (Exit n))
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hnever_zero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hgood_ae : ∀ᵐ seed ∂P, seed ∈ good := by
    rw [MeasureTheory.ae_iff]
    have hunion : good = Neverᶜ := by
      simpa [good, Exit, Never] using
        (iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent initialState policy)
    change P goodᶜ = 0
    rw [hunion]
    simpa using hnever_zero
  have hExit : ∀ n, MeasurableSet (Exit n) := fun n =>
    measurableSet_gn21RawCalendarTraceExitEvent initialState policy hpolicy n
  have hdisjoint : Pairwise (Function.onFun Disjoint Exit) := by
    simpa [Exit] using
      (gn21RawCalendarTraceExitEvent_pairwiseDisjoint initialState policy)
  have hdecomp : P = Measure.sum fun n : Nat => P.restrict (Exit n) := by
    calc
      P = P.restrict good := (Measure.restrict_eq_self_of_ae_mem hgood_ae).symm
      _ = Measure.sum fun n : Nat => P.restrict (Exit n) :=
        Measure.restrict_iUnion hdisjoint hExit
  have hfold : Measurable fold := by
    simpa [fold] using
      (measurable_gn21RawCalendarFirstExitHistoryFold initialState policy hpolicy
        initial update hupdate)
  have hpostTail : Measurable postTail := by
    simpa [postTail] using
      (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)
  have hpair : Measurable pair := hfold.prodMk hpostTail
  have hmapPair : Measure.map pair P =
      Measure.sum fun n : Nat => Measure.map pair (P.restrict (Exit n)) := by
    calc
      Measure.map pair P = Measure.map pair (Measure.sum fun n : Nat =>
          P.restrict (Exit n)) := by rw [← hdecomp]
      _ = Measure.sum fun n : Nat => Measure.map pair (P.restrict (Exit n)) :=
        Measure.map_sum hpair.aemeasurable
  have hfold_branch (n : Nat) : Measure.map fold (P.restrict (Exit n)) = M n := by
    apply Measure.map_congr
    filter_upwards [MeasureTheory.ae_restrict_mem (hExit n)] with seed hseed
    have hindex := gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hseed
    simp [fold, gn21RawCalendarFirstExitHistoryFold, hindex]
  have hmapFold : Measure.map fold P = Measure.sum M := by
    calc
      Measure.map fold P = Measure.map fold (Measure.sum fun n : Nat =>
          P.restrict (Exit n)) := by rw [← hdecomp]
      _ = Measure.sum fun n : Nat => Measure.map fold (P.restrict (Exit n)) :=
        Measure.map_sum hfold.aemeasurable
      _ = Measure.sum M := by
        congr 1
        funext n
        exact hfold_branch n
  have hbranch (n : Nat) : Measure.map pair (P.restrict (Exit n)) = (M n).prod P := by
    have hpair_eq : Measure.map pair (P.restrict (Exit n)) =
        Measure.map (fun seed =>
          (gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1) seed,
            gn21RawCalendarTraceSeed initialState policy (n + 1) seed))
          (P.restrict (Exit n)) := by
      apply Measure.map_congr
      filter_upwards [MeasureTheory.ae_restrict_mem (hExit n)] with seed hseed
      have hindex := gn21RawCalendarFirstExitIndex_eq_of_mem_exitEvent hseed
      simp [pair, fold, postTail, gn21RawCalendarFirstExitHistoryFold,
        gn21RawCalendarPostExitSeed, hindex]
    calc
      Measure.map pair (P.restrict (Exit n)) =
          Measure.map (fun seed =>
            (gn21RawCalendarNoExitHistoryFold initialState policy initial update (n + 1) seed,
              gn21RawCalendarTraceSeed initialState policy (n + 1) seed))
            (P.restrict (Exit n)) := hpair_eq
      _ = (M n).prod P := by
        simpa [P, Exit, M] using
          (map_gn21RawCalendarNoExitHistoryFoldAndTraceSeed_restrict_exitEvent
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
            hpolicy hpolicy_subset hpolicy_mass initial update hupdate n)
  calc
    Measure.map pair P = Measure.sum fun n : Nat =>
        Measure.map pair (P.restrict (Exit n)) := hmapPair
    _ = Measure.sum fun n : Nat => (M n).prod P := by
      congr 1
      funext n
      exact hbranch n
    _ = (Measure.sum M).prod P := by rw [Measure.prod_sum_left]
    _ = (Measure.map fold P).prod P := by rw [hmapFold]

/-- GN's existing stopped state-sojourn time is independent of the literal
raw tail after the actual first cross-state exit. -/
theorem map_gn21RawCalendarStoppedStateTimeAndPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (fun seed =>
      (gn21RawCalendarStoppedStateTime initialState policy seed,
        gn21RawCalendarPostExitSeed initialState policy seed)) P =
      (Measure.map (gn21RawCalendarStoppedStateTime initialState policy) P).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let Exit := gn21RawCalendarTraceExitEvent initialState policy
  let Never := gn21RawCalendarTraceNeverExitEvent initialState policy
  let good : Set GN21RawCycleSeed := ⋃ n : Nat, Exit n
  let foldedTime := gn21RawCalendarFirstExitAccumulatedTime initialState policy
  let stoppedTime := gn21RawCalendarStoppedStateTime initialState policy
  let postTail := gn21RawCalendarPostExitSeed initialState policy
  let update : Real -> GN21RawPostThinningRaceHistory -> Real := fun elapsed history =>
    elapsed + gn21RawPostThinningRaceHistoryTime history
  have hupdate : Measurable fun z : Real × GN21RawPostThinningRaceHistory => update z.1 z.2 :=
    measurable_fst.add (measurable_gn21RawPostThinningRaceHistoryTime.comp measurable_snd)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hnever_zero : P Never = 0 := by
    simpa [P, Never] using
      (measure_gn21RawCalendarTraceNeverExitEvent_eq_zero
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hgood_ae : ∀ᵐ seed ∂P, seed ∈ good := by
    rw [MeasureTheory.ae_iff]
    have hunion : good = Neverᶜ := by
      simpa [good, Exit, Never] using
        (iUnion_gn21RawCalendarTraceExitEvent_eq_compl_neverExitEvent initialState policy)
    change P goodᶜ = 0
    rw [hunion]
    simpa using hnever_zero
  have htime_ae : foldedTime =ᵐ[P] stoppedTime := by
    filter_upwards [hgood_ae] with seed hseed
    rcases Set.mem_iUnion.mp hseed with ⟨n, hn⟩
    simpa [foldedTime, stoppedTime] using
      (gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime_of_mem_exitEvent hn)
  have hpair_ae : (fun seed => (stoppedTime seed, postTail seed)) =ᵐ[P]
      (fun seed => (foldedTime seed, postTail seed)) := by
    filter_upwards [htime_ae] with seed htime
    rw [htime]
  have hmapTime : Measure.map stoppedTime P = Measure.map foldedTime P := by
    apply Measure.map_congr
    filter_upwards [htime_ae] with seed htime
    exact htime.symm
  calc
    Measure.map (fun seed => (stoppedTime seed, postTail seed)) P =
        Measure.map (fun seed => (foldedTime seed, postTail seed)) P :=
          Measure.map_congr hpair_ae
    _ = (Measure.map foldedTime P).prod P := by
      simpa [P, foldedTime, postTail, update] using
        (map_gn21RawCalendarFirstExitHistoryFoldAndPostExitSeed
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
          hpolicy hpolicy_subset hpolicy_mass 0 update hupdate)
    _ = (Measure.map stoppedTime P).prod P := by rw [hmapTime]

/-- Two literal regenerative tail kernels compose without resampling: the
first summary, second summary, and final raw tail have their iterated product
law on the original source space. -/
theorem map_compose_freshRawTailKernels
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (P : Measure α) [IsProbabilityMeasure P]
    (B : Measure β) (C : Measure γ) [SFinite B] [SFinite C]
    (f : α -> β × α) (g : α -> γ × α)
    (hf : Measurable f) (hg : Measurable g)
    (hF : Measure.map f P = B.prod P)
    (hG : Measure.map g P = C.prod P) :
    Measure.map (fun x => (((f x).1, (g (f x).2).1), (g (f x).2).2)) P =
      (B.prod C).prod P := by
  let combine : β × (γ × α) -> (β × γ) × α := fun z => ((z.1, z.2.1), z.2.2)
  have hcombine : Measurable combine :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have houtput : (fun x => (((f x).1, (g (f x).2).1), (g (f x).2).2)) =
      combine ∘ Prod.map id g ∘ f := by
    rfl
  have hassoc : combine ∘ MeasurableEquiv.prodAssoc = id := by
    rfl
  calc
    Measure.map (fun x => (((f x).1, (g (f x).2).1), (g (f x).2).2)) P =
        Measure.map combine (Measure.map (Prod.map id g) (Measure.map f P)) := by
          rw [Measure.map_map hcombine (measurable_id.prodMap hg),
            Measure.map_map (hcombine.comp (measurable_id.prodMap hg)) hf, houtput]
          rfl
    _ = Measure.map combine (Measure.map (Prod.map id g) (B.prod P)) := by rw [hF]
    _ = Measure.map combine (B.prod (Measure.map g P)) := by
          rw [← Measure.map_prod_map B P measurable_id hg, Measure.map_id]
    _ = Measure.map combine (B.prod (C.prod P)) := by rw [hG]
    _ = Measure.map combine
        (Measure.map MeasurableEquiv.prodAssoc ((B.prod C).prod P)) := by
          rw [(measurePreserving_prodAssoc B C P).map_eq]
    _ = (B.prod C).prod P := by
          rw [Measure.map_map hcombine MeasurableEquiv.prodAssoc.measurable, hassoc,
            Measure.map_id]

/-- The measurable finite-history calendar time, rather than its a.e.-equal
stopped-sum presentation, factors from the literal post-exit source tail. -/
theorem map_gn21RawCalendarFirstExitAccumulatedTimeAndPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (fun seed =>
      (gn21RawCalendarFirstExitAccumulatedTime initialState policy seed,
        gn21RawCalendarPostExitSeed initialState policy seed)) P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod P := by
  let update : Real -> GN21RawPostThinningRaceHistory -> Real := fun elapsed history =>
    elapsed + gn21RawPostThinningRaceHistoryTime history
  have hupdate : Measurable fun z : Real × GN21RawPostThinningRaceHistory => update z.1 z.2 :=
    measurable_fst.add (measurable_gn21RawPostThinningRaceHistoryTime.comp measurable_snd)
  simpa [gn21RawCalendarFirstExitAccumulatedTime, update] using
    (map_gn21RawCalendarFirstExitHistoryFoldAndPostExitSeed
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass 0 update hupdate)

/-- One complete alternating two-state calendar cycle: first exit from the
given state, then first exit from the opposite state, retaining the same
literal raw tail after both exits. -/
noncomputable def gn21RawCalendarTwoStateTimeAndPostExitSeed
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> (Real × Real) × GN21RawCycleSeed :=
  fun seed =>
    let first :=
      (gn21RawCalendarFirstExitAccumulatedTime initialState policy seed,
        gn21RawCalendarPostExitSeed initialState policy seed)
    let second :=
      (gn21RawCalendarFirstExitAccumulatedTime
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)
          policy first.2,
        gn21RawCalendarPostExitSeed
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)
          policy first.2)
    ((first.1, second.1), second.2)

theorem measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) :
    Measurable (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy) := by
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let first : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedTime initialState policy seed,
      gn21RawCalendarPostExitSeed initialState policy seed)
  let second : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedTime other policy seed,
      gn21RawCalendarPostExitSeed other policy seed)
  have hfirst : Measurable first :=
    (measurable_gn21RawCalendarFirstExitAccumulatedTime initialState policy hpolicy).prodMk
      (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)
  have hsecond : Measurable second :=
    (measurable_gn21RawCalendarFirstExitAccumulatedTime other policy hpolicy).prodMk
      (measurable_gn21RawCalendarPostExitSeed other policy hpolicy)
  change Measurable (fun seed => (((first seed).1, (second (first seed).2).1),
    (second (first seed).2).2))
  exact ((measurable_fst.comp hfirst).prodMk
    ((measurable_fst.comp hsecond).comp (measurable_snd.comp hfirst))).prodMk
      ((measurable_snd.comp hsecond).comp (measurable_snd.comp hfirst))

/-- The two physical state sojourns in one alternating calendar cycle, and
the literal tail after that cycle, have the exact iterated product law. -/
theorem map_gn21RawCalendarTwoStateTimeAndPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy) P =
      ((Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
        (Measure.map (gn21RawCalendarFirstExitAccumulatedTime
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState) policy) P)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let first : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedTime initialState policy seed,
      gn21RawCalendarPostExitSeed initialState policy seed)
  let second : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedTime other policy seed,
      gn21RawCalendarPostExitSeed other policy seed)
  have hfirst : Measurable first :=
    (measurable_gn21RawCalendarFirstExitAccumulatedTime initialState policy hpolicy).prodMk
      (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)
  have hsecond : Measurable second :=
    (measurable_gn21RawCalendarFirstExitAccumulatedTime other policy hpolicy).prodMk
      (measurable_gn21RawCalendarPostExitSeed other policy hpolicy)
  have hfirst_law : Measure.map first P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod P := by
    simpa [P, first] using
      (map_gn21RawCalendarFirstExitAccumulatedTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hsecond_law : Measure.map second P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P).prod P := by
    simpa [P, second] using
      (map_gn21RawCalendarFirstExitAccumulatedTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI other policy
        hpolicy hpolicy_subset hpolicy_mass)
  simpa [gn21RawCalendarTwoStateTimeAndPostExitSeed, other, first, second] using
    (map_compose_freshRawTailKernels P
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P)
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
      first second hfirst hsecond hfirst_law hsecond_law)

/-- The `n`th physical-calendar sojourn in the initial state, obtained by
iterating the same literal two-exit tail rather than drawing fresh cycles. -/
noncomputable def gn21RawCalendarAlternatingCycleInitialStateTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) (n : Nat) :
    GN21RawCycleSeed -> Real := fun seed =>
  (AppliedModelingLib.Probability.regenerativeSummary
    (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy) n seed).1

/-- The companion physical-calendar sojourn in the opposite state in the
same two-exit cycle. -/
noncomputable def gn21RawCalendarAlternatingCycleOtherStateTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy) (n : Nat) :
    GN21RawCycleSeed -> Real := fun seed =>
  (AppliedModelingLib.Probability.regenerativeSummary
    (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy) n seed).2

theorem measurable_gn21RawCalendarAlternatingCycleInitialStateTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (n : Nat) :
    Measurable (gn21RawCalendarAlternatingCycleInitialStateTime initialState policy n) :=
  measurable_fst.comp
    (AppliedModelingLib.Probability.measurable_regenerativeSummary
      (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy)
      (measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy) n)

theorem measurable_gn21RawCalendarAlternatingCycleOtherStateTime
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (n : Nat) :
    Measurable (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy n) :=
  measurable_snd.comp
    (AppliedModelingLib.Probability.measurable_regenerativeSummary
      (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy)
      (measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy) n)

/-- Successive initial-state calendar sojourns are pairwise independent under
the original raw source law. -/
theorem pairwise_gn21RawCalendarAlternatingCycleInitialStateTime_indepFun
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Pairwise (fun n m => ProbabilityTheory.IndepFun
      (gn21RawCalendarAlternatingCycleInitialStateTime initialState policy n)
      (gn21RawCalendarAlternatingCycleInitialStateTime initialState policy m) P) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedTime initialState policy hpolicy).aemeasurable
  let step := gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hindep := AppliedModelingLib.Probability.regenerativeSummary_pairwise_indepFun
    P B step hstep hstep_law
  intro n m hnm
  simpa [gn21RawCalendarAlternatingCycleInitialStateTime, step] using
    (hindep hnm).comp measurable_fst measurable_fst

/-- The opposite-state physical-calendar sojourns are pairwise independent
under the same literal two-exit tail construction. -/
theorem pairwise_gn21RawCalendarAlternatingCycleOtherStateTime_indepFun
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Pairwise (fun n m => ProbabilityTheory.IndepFun
      (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy n)
      (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy m) P) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedTime initialState policy hpolicy).aemeasurable
  let step := gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  have hindep := AppliedModelingLib.Probability.regenerativeSummary_pairwise_indepFun
    P B step hstep hstep_law
  intro n m hnm
  simpa [gn21RawCalendarAlternatingCycleOtherStateTime, step] using
    (hindep hnm).comp measurable_snd measurable_snd

/-- Initial-state sojourns in all alternating calendar cycles have the same
law as the first physical calendar cycle. -/
theorem identDistrib_gn21RawCalendarAlternatingCycleInitialStateTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleInitialStateTime initialState policy n)
      (gn21RawCalendarAlternatingCycleInitialStateTime initialState policy 0) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
  let step := gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  simpa [gn21RawCalendarAlternatingCycleInitialStateTime, step, Function.comp_def] using
    (AppliedModelingLib.Probability.regenerativeSummary_identDistrib
      P B step hstep hstep_law n).comp measurable_fst

/-- Opposite-state sojourns in all alternating calendar cycles have the same
law as the opposite-state sojourn in the first physical calendar cycle. -/
theorem identDistrib_gn21RawCalendarAlternatingCycleOtherStateTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy n)
      (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy 0) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
  let step := gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  simpa [gn21RawCalendarAlternatingCycleOtherStateTime, step, Function.comp_def] using
    (AppliedModelingLib.Probability.regenerativeSummary_identDistrib
      P B step hstep hstep_law n).comp measurable_snd

/-- A literal calendar subcycle contribution remains integrable when its
one-subcycle raw reward is integrable. -/
theorem integrable_gn21RawCalendarTraceNoExitReward
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (reward : GN21RawCycleSeed -> Real)
    (hreward : Integrable reward
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (n : Nat) :
    Integrable (gn21RawCalendarTraceNoExitReward initialState policy reward n)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawCalendarTraceNoExitEvent initialState policy n
  let tail := gn21RawCalendarTraceSeed initialState policy n
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hA : MeasurableSet A :=
    measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
  have htail : Measurable tail :=
    measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
  have hmap : Measure.map tail (P.restrict A) = P A • P := by
    simpa [P, A, tail] using
      (map_gn21RawCalendarTraceSeed_restrict_noExitEvent
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass n)
  have hrewardMap : Integrable reward (Measure.map tail (P.restrict A)) := by
    rw [hmap]
    exact hreward.smul_measure (measure_ne_top P A)
  have hrewardTail : Integrable (reward ∘ tail) (P.restrict A) :=
    hrewardMap.comp_aemeasurable htail.aemeasurable
  apply (MeasureTheory.integrable_indicator_iff hA).2
  simpa [gn21RawCalendarTraceNoExitReward, Function.comp_def] using hrewardTail

/-- Each literal calendar subcycle contribution has the geometric
continuation multiplier times the original one-subcycle raw-reward mean. -/
theorem integral_gn21RawCalendarTraceNoExitReward
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (reward : GN21RawCycleSeed -> Real)
    (hreward : Integrable reward
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (n : Nat) :
    (∫ seed, gn21RawCalendarTraceNoExitReward initialState policy reward n seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ).toReal ^ n *
        (∫ seed, reward seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawCalendarTraceNoExitEvent initialState policy n
  let tail := gn21RawCalendarTraceSeed initialState policy n
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hA : MeasurableSet A :=
    measurableSet_gn21RawCalendarTraceNoExitEvent initialState policy hpolicy n
  have htail : Measurable tail :=
    measurable_gn21RawCalendarTraceSeed initialState policy hpolicy n
  have hmap : Measure.map tail (P.restrict A) = P A • P := by
    simpa [P, A, tail] using
      (map_gn21RawCalendarTraceSeed_restrict_noExitEvent
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass n)
  have hrewardMap : AEStronglyMeasurable reward (Measure.map tail (P.restrict A)) := by
    rw [hmap]
    exact AEStronglyMeasurable.smul_measure hreward.aestronglyMeasurable (P A)
  have hmass : P A = (P R) ^ n := by
    simpa [P, A, R] using
      (measure_gn21RawCalendarTraceNoExitEvent
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass n)
  calc
    (∫ seed, gn21RawCalendarTraceNoExitReward initialState policy reward n seed ∂P) =
        ∫ seed in A, reward (tail seed) ∂P := by
          rw [gn21RawCalendarTraceNoExitReward, integral_indicator hA]
    _ = ∫ seed, reward seed ∂Measure.map tail (P.restrict A) := by
          exact (integral_map htail.aemeasurable hrewardMap).symm
    _ = ∫ seed, reward seed ∂(P A • P) := by rw [hmap]
    _ = (P A).toReal * (∫ seed, reward seed ∂P) := by
          simp [integral_smul_measure]
    _ = (P R).toReal ^ n * (∫ seed, reward seed ∂P) := by
          rw [hmass, ENNReal.toReal_pow]


/-- The expected bounded literal calendar reward is the corresponding finite
geometric sum times its original one-subcycle raw-reward mean. -/
theorem integral_gn21RawCalendarCappedStateStoppedReward
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (reward : GN21RawCycleSeed -> Real)
    (hreward : Integrable reward
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (cap : Nat) :
    (∫ seed, gn21RawCalendarCappedStateStoppedReward initialState policy reward cap seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑ n ∈ Finset.range (cap + 1),
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ).toReal ^ n) *
        (∫ seed, reward seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let q := (P R).toReal
  let mean := ∫ seed, reward seed ∂P
  calc
    (∫ seed, gn21RawCalendarCappedStateStoppedReward initialState policy reward cap seed ∂P) =
        ∑ n ∈ Finset.range (cap + 1),
          ∫ seed, gn21RawCalendarTraceNoExitReward initialState policy reward n seed ∂P := by
            change (∫ seed, ∑ n ∈ Finset.range (cap + 1),
              gn21RawCalendarTraceNoExitReward initialState policy reward n seed ∂P) = _
            rw [integral_finset_sum]
            intro n hn
            exact integrable_gn21RawCalendarTraceNoExitReward
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
              hpolicy hpolicy_subset hpolicy_mass reward hreward n
    _ = ∑ n ∈ Finset.range (cap + 1), q ^ n * mean := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa [P, R, q, mean] using
            (integral_gn21RawCalendarTraceNoExitReward
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
              hpolicy hpolicy_subset hpolicy_mass reward hreward n)
    _ = (∑ n ∈ Finset.range (cap + 1), q ^ n) * mean := by
          rw [Finset.sum_mul]
    _ = _ := by rfl

/-- A literal calendar reward accumulated through physical-state exit is
integrable whenever its one-subcycle raw reward is integrable. -/
theorem integrable_gn21RawCalendarStoppedStateReward
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (reward : GN21RawCycleSeed -> Real)
    (hreward : Integrable reward
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) :
    Integrable (gn21RawCalendarStoppedStateReward initialState policy reward)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let q := (P R).toReal
  let F : Nat -> GN21RawCycleSeed -> Real := fun n =>
    gn21RawCalendarTraceNoExitReward initialState policy reward n
  have hq : Summable fun n : Nat => q ^ n := by
    apply summable_geometric_of_lt_one ENNReal.toReal_nonneg
    simpa [P, R, q] using
      (measureReal_gn21RawPostThinningRaceNoExit_lt_one
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState))
  have hF_integrable (n : Nat) : Integrable (F n) P := by
    simpa [F, P] using
      (integrable_gn21RawCalendarTraceNoExitReward
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass reward hreward n)
  have hF_norm_integral (n : Nat) :
      (∫ seed, ‖F n seed‖ ∂P) = q ^ n * ∫ seed, ‖reward seed‖ ∂P := by
    have hnorm : (fun seed => ‖F n seed‖) =
        gn21RawCalendarTraceNoExitReward initialState policy (fun z => ‖reward z‖) n := by
      funext seed
      exact norm_gn21RawCalendarTraceNoExitReward initialState policy reward n seed
    rw [hnorm]
    simpa [P, R, q] using
      (integral_gn21RawCalendarTraceNoExitReward
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass (fun z => ‖reward z‖) hreward.norm n)
  have hsum_norm : Summable fun n : Nat => ∫ seed, ‖F n seed‖ ∂P := by
    exact (hq.mul_right (∫ seed, ‖reward seed‖ ∂P)).congr fun n =>
      (hF_norm_integral n).symm
  simpa [gn21RawCalendarStoppedStateReward, F, P] using
    (AppliedModelingLib.Probability.IIDStream.integrable_tsum_of_summable_integral_norm
      F hF_integrable hsum_norm)

/-- The literal calendar reward through physical-state exit has the exact
geometric stopped-reward expectation. -/
theorem integral_gn21RawCalendarStoppedStateReward
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (reward : GN21RawCycleSeed -> Real)
    (hreward : Integrable reward
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) :
    (∫ seed, gn21RawCalendarStoppedStateReward initialState policy reward seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ).toReal ^ n) *
        (∫ seed, reward seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let R := (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ
  let q := (P R).toReal
  let F : Nat -> GN21RawCycleSeed -> Real := fun n =>
    gn21RawCalendarTraceNoExitReward initialState policy reward n
  have hq : Summable fun n : Nat => q ^ n := by
    apply summable_geometric_of_lt_one ENNReal.toReal_nonneg
    simpa [P, R, q] using
      (measureReal_gn21RawPostThinningRaceNoExit_lt_one
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState))
  have hF_integrable (n : Nat) : Integrable (F n) P := by
    simpa [F, P] using
      (integrable_gn21RawCalendarTraceNoExitReward
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass reward hreward n)
  have hF_integral (n : Nat) :
      (∫ seed, F n seed ∂P) = q ^ n * ∫ seed, reward seed ∂P := by
    simpa [F, P, R, q] using
      (integral_gn21RawCalendarTraceNoExitReward
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass reward hreward n)
  have hF_norm_integral (n : Nat) :
      (∫ seed, ‖F n seed‖ ∂P) = q ^ n * ∫ seed, ‖reward seed‖ ∂P := by
    have hnorm : (fun seed => ‖F n seed‖) =
        gn21RawCalendarTraceNoExitReward initialState policy (fun z => ‖reward z‖) n := by
      funext seed
      exact norm_gn21RawCalendarTraceNoExitReward initialState policy reward n seed
    rw [hnorm]
    simpa [P, R, q] using
      (integral_gn21RawCalendarTraceNoExitReward
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass (fun z => ‖reward z‖) hreward.norm n)
  have hsum_norm : Summable fun n : Nat => ∫ seed, ‖F n seed‖ ∂P := by
    exact (hq.mul_right (∫ seed, ‖reward seed‖ ∂P)).congr fun n =>
      (hF_norm_integral n).symm
  calc
    (∫ seed, gn21RawCalendarStoppedStateReward initialState policy reward seed ∂P) =
        ∫ seed, ∑' n : Nat, F n seed ∂P := by rfl
    _ = ∑' n : Nat, ∫ seed, F n seed ∂P := by
          exact (MeasureTheory.integral_tsum_of_summable_integral_norm
            hF_integrable hsum_norm).symm
    _ = ∑' n : Nat, q ^ n * ∫ seed, reward seed ∂P := by
          exact tsum_congr hF_integral
    _ = (∑' n : Nat, q ^ n) * ∫ seed, reward seed ∂P := by
          rw [tsum_mul_right]
    _ = _ := by rfl

/-- The literal calendar state-sojourn time is integrable under the source
trip-length integrability condition. -/
theorem integrable_gn21RawCalendarStoppedStateTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htime : IntegrableOn (fun tau : TripLength => tau) (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    Integrable (gn21RawCalendarStoppedStateTime initialState policy)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa [gn21RawCalendarStoppedStateTime] using
    (integrable_gn21RawCalendarStoppedStateReward
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass
      (gn21RawPostThinningRaceSubcycleTime initialState (policy initialState))
      (integrable_gn21RawPostThinningRaceSubcycleTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_mass initialState) htime))

/-- The literal calendar state-sojourn time has the exact geometric
stopped-subcycle expectation. -/
theorem integral_gn21RawCalendarStoppedStateTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htime : IntegrableOn (fun tau : TripLength => tau) (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarStoppedStateTime initialState policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ).toReal ^ n) *
        (∫ seed, gn21RawPostThinningRaceSubcycleTime initialState (policy initialState) seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa [gn21RawCalendarStoppedStateTime] using
    (integral_gn21RawCalendarStoppedStateReward
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass
      (gn21RawPostThinningRaceSubcycleTime initialState (policy initialState))
      (integrable_gn21RawPostThinningRaceSubcycleTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
        (hpolicy initialState) (hpolicy_mass initialState) htime))

/-- The actual calendar state-sojourn time agrees with the paper's expected
state time in a larger renewal cycle. -/
theorem integral_gn21RawCalendarStoppedStateTime_eq_expectedStateTimeInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htime : IntegrableOn (fun tau : TripLength => tau) (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarStoppedStateTime initialState policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateTimeInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex initialState))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ initialState) (policy initialState))
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex initialState))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState)) (policy initialState))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)))
          (policy initialState)) := by
  rw [integral_gn21RawCalendarStoppedStateTime
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
    hpolicy hpolicy_subset hpolicy_mass htime,
    integral_gn21RawPostThinningRaceSubcycleTime_eq
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
      (hpolicy initialState) (hpolicy_mass initialState) htime,
    tsum_measureReal_gn21RawPostThinningRaceNoExit_pow_eq_inv_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
      (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState)]
  simp only [gn21ExpectedStateTimeInRenewalCycle, div_eq_mul_inv, mul_comm]

/-- The measurable first-exit history-fold time inherits integrability from
the a.e.-equal literal stopped calendar sum. -/
theorem integrable_gn21RawCalendarFirstExitAccumulatedTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htime : IntegrableOn (fun tau : TripLength => tau) (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    Integrable (gn21RawCalendarFirstExitAccumulatedTime initialState policy)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  exact (integrable_gn21RawCalendarStoppedStateTime
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
    hpolicy hpolicy_subset hpolicy_mass htime).congr
      (ae_gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass).symm

/-- The measurable history-fold time has the paper's exact expected
state-sojourn value because it differs from the literal stopped sum only on a
null never-exit event. -/
theorem integral_gn21RawCalendarFirstExitAccumulatedTime_eq_expectedStateTimeInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htime : IntegrableOn (fun tau : TripLength => tau) (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarFirstExitAccumulatedTime initialState policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateTimeInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex initialState))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ initialState) (policy initialState))
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex initialState))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState)) (policy initialState))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)))
          (policy initialState)) := by
  calc
    (∫ seed, gn21RawCalendarFirstExitAccumulatedTime initialState policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        ∫ seed, gn21RawCalendarStoppedStateTime initialState policy seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
      integral_congr_ae
        (ae_gn21RawCalendarFirstExitAccumulatedTime_eq_stoppedStateTime
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
          hpolicy hpolicy_subset hpolicy_mass)
    _ = _ := integral_gn21RawCalendarStoppedStateTime_eq_expectedStateTimeInRenewalCycle
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass htime

/-- The literal calendar state-sojourn earnings are integrable under the
source accepted-payment integrability condition. -/
theorem integrable_gn21RawCalendarStoppedStateEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hpayment : IntegrableOn w (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    Integrable (gn21RawCalendarStoppedStateEarning initialState w policy)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa [gn21RawCalendarStoppedStateEarning] using
    (integrable_gn21RawCalendarStoppedStateReward
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass
      (gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState))
      (integrable_gn21RawPostThinningRaceSubcycleEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w (policy initialState)
        (hpolicy initialState) (hpolicy_mass initialState) hpayment))

/-- The literal calendar state-sojourn earnings have the exact geometric
stopped-subcycle expectation. -/
theorem integral_gn21RawCalendarStoppedStateEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hpayment : IntegrableOn w (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarStoppedStateEarning initialState w policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState initialState (policy initialState))ᶜ).toReal ^ n) *
        (∫ seed,
          gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState) seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa [gn21RawCalendarStoppedStateEarning] using
    (integral_gn21RawCalendarStoppedStateReward
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass
      (gn21RawPostThinningRaceSubcycleEarning initialState w (policy initialState))
      (integrable_gn21RawPostThinningRaceSubcycleEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w (policy initialState)
        (hpolicy initialState) (hpolicy_mass initialState) hpayment))

/-- The actual calendar state-sojourn earnings agree with the paper's expected
state earnings in a larger renewal cycle. -/
theorem integral_gn21RawCalendarStoppedStateEarning_eq_expectedStateEarningInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hpayment : IntegrableOn w (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarStoppedStateEarning initialState w policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateEarningInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex initialState))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ initialState) (policy initialState))
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex initialState))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ initialState) w (policy initialState))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)))
          (policy initialState)) := by
  rw [integral_gn21RawCalendarStoppedStateEarning
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
    hpolicy hpolicy_subset hpolicy_mass hpayment,
    integral_gn21RawPostThinningRaceSubcycleEarning_eq
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState w (policy initialState)
      (hpolicy initialState) (hpolicy_mass initialState) hpayment,
    tsum_measureReal_gn21RawPostThinningRaceNoExit_pow_eq_inv_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState (policy initialState)
      (hpolicy initialState) (hpolicy_subset initialState) (hpolicy_mass initialState)]
  simp only [gn21ExpectedStateEarningInRenewalCycle, div_eq_mul_inv, mul_comm]

/-- The measurable first-exit payment fold inherits integrability from the
a.e.-equal literal stopped payment sum. -/
theorem integrable_gn21RawCalendarFirstExitAccumulatedEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hpayment : IntegrableOn w (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    Integrable (gn21RawCalendarFirstExitAccumulatedEarning initialState w policy)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  exact (integrable_gn21RawCalendarStoppedStateEarning
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
    hpolicy hpolicy_subset hpolicy_mass hpayment).congr
      (ae_gn21RawCalendarFirstExitAccumulatedEarning_eq_stoppedStateEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass).symm

/-- The measurable first-exit payment fold has the paper's exact expected
state earning because it differs from the stopped sum only on a null path. -/
theorem integral_gn21RawCalendarFirstExitAccumulatedEarning_eq_expectedStateEarningInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hpayment : IntegrableOn w (policy initialState)
      (gn21CycleMarkLaw muI muJ initialState)) :
    (∫ seed, gn21RawCalendarFirstExitAccumulatedEarning initialState w policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateEarningInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex initialState))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ initialState) (policy initialState))
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex initialState))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ initialState) w (policy initialState))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ initialState)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex initialState))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)))
          (policy initialState)) := by
  calc
    (∫ seed, gn21RawCalendarFirstExitAccumulatedEarning initialState w policy seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        ∫ seed, gn21RawCalendarStoppedStateEarning initialState w policy seed
          ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
      integral_congr_ae
        (ae_gn21RawCalendarFirstExitAccumulatedEarning_eq_stoppedStateEarning
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
          hpolicy hpolicy_subset hpolicy_mass)
    _ = _ := integral_gn21RawCalendarStoppedStateEarning_eq_expectedStateEarningInRenewalCycle
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
      hpolicy hpolicy_subset hpolicy_mass hpayment


/-- Combining the literal switch-first and accepted-completion maps yields a
one-subcycle raw-seed transition with the original raw law.  This stationarity
result is deliberately marginal: the associated calendar endpoint state must
still be retained jointly before it can support a recursive alternating-cycle
construction. -/
theorem map_gn21RawPostThinningRaceNextCycleSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let S := gn21RawPostThinningRaceSwitchesFirst state sigma
  let A := gn21RawPostThinningRaceAcceptedFirst state sigma
  let switchMass := gn21SwitchFirstNoHitMass
    muI muJ arrivalI arrivalJ switchIJ switchJI state sigma
  let acceptedMass := ENNReal.ofReal
    ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
        (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
        (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
        gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state)))
  have hS : MeasurableSet S := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hnext : Measurable (gn21RawPostThinningRaceNextCycleSeed state sigma) := by
    exact Measurable.ite hS (measurable_gn21RawSwitchFirstNextCycleSeed state)
      (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma)
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hswitchLaw : Measure.map (gn21RawSwitchFirstNextCycleSeed state)
      (P.restrict S) = switchMass • P := by
    simpa [P, S, switchMass] using
      (map_gn21RawSwitchFirstNextCycleSeed_restrict_switchesFirst
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hacceptedLaw : Measure.map (gn21RawAcceptedCompletionNextCycleSeed state sigma)
      (P.restrict A) = acceptedMass • P := by
    simpa [P, A, acceptedMass] using
      (map_gn21RawAcceptedCompletionNextCycleSeed_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hswitchMass : switchMass = P S := by
    calc
      switchMass = (switchMass • P) Set.univ := by simp
      _ = Measure.map (gn21RawSwitchFirstNextCycleSeed state) (P.restrict S) Set.univ := by
        rw [hswitchLaw]
      _ = (P.restrict S) Set.univ := by
        rw [Measure.map_apply (measurable_gn21RawSwitchFirstNextCycleSeed state)
          MeasurableSet.univ]
        simp
      _ = P S := by simp [Measure.restrict_apply]
  have hacceptedMass : acceptedMass = P A := by
    calc
      acceptedMass = (acceptedMass • P) Set.univ := by simp
      _ = Measure.map (gn21RawAcceptedCompletionNextCycleSeed state sigma)
          (P.restrict A) Set.univ := by rw [hacceptedLaw]
      _ = (P.restrict A) Set.univ := by
        rw [Measure.map_apply
          (measurable_gn21RawAcceptedCompletionNextCycleSeed state sigma hsigma)
          MeasurableSet.univ]
        simp
      _ = P A := by simp [Measure.restrict_apply, A]
  have hmassSum : switchMass + acceptedMass = 1 := by
    rw [hswitchMass, hacceptedMass]
    simpa [A, S] using (measure_add_measure_compl (μ := P) hS)
  calc
    Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma) P =
        Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma)
          (P.restrict S + P.restrict Sᶜ) := by rw [Measure.restrict_add_restrict_compl hS]
    _ = Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma) (P.restrict S) +
        Measure.map (gn21RawPostThinningRaceNextCycleSeed state sigma) (P.restrict Sᶜ) := by
          rw [Measure.map_add _ _ hnext]
    _ = Measure.map (gn21RawSwitchFirstNextCycleSeed state) (P.restrict S) +
        Measure.map (gn21RawAcceptedCompletionNextCycleSeed state sigma) (P.restrict A) := by
          congr 1
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS] with seed hseed
            have hseed' : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            rw [gn21RawPostThinningRaceNextCycleSeed, if_pos hseed']
          · apply Measure.map_congr
            filter_upwards [MeasureTheory.ae_restrict_mem hS.compl] with seed hseed
            have hseed' : seed ∉ gn21RawPostThinningRaceSwitchesFirst state sigma := by
              simpa [S] using hseed
            rw [gn21RawPostThinningRaceNextCycleSeed, if_neg hseed']
    _ = switchMass • P + acceptedMass • P := by rw [hswitchLaw, hacceptedLaw]
    _ = (switchMass + acceptedMass) • P := by rw [add_smul]
    _ = P := by rw [hmassSum, one_smul]

/-- The opposite-state time in the first alternating physical cycle has the
same law as an ordinary measurable first-exit time started from that opposite
state. -/
theorem identDistrib_gn21RawCalendarAlternatingCycleOtherStateTime_zero_accumulated
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy 0)
      (gn21RawCalendarFirstExitAccumulatedTime
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState) policy) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedTime initialState policy hpolicy).aemeasurable
  let step := gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy hpolicy
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateTimeAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
        hpolicy hpolicy_subset hpolicy_mass)
  let q : (Real × Real) × GN21RawCycleSeed -> Real := fun z => z.1.2
  have hq : Measurable q := measurable_snd.comp measurable_fst
  refine ⟨(measurable_gn21RawCalendarAlternatingCycleOtherStateTime
    initialState policy hpolicy 0).aemeasurable,
    (measurable_gn21RawCalendarFirstExitAccumulatedTime other policy hpolicy).aemeasurable, ?_⟩
  calc
    Measure.map (gn21RawCalendarAlternatingCycleOtherStateTime initialState policy 0) P =
        Measure.map q (Measure.map step P) := by
            change Measure.map (fun seed => (step seed).1.2) P = _
            rw [Measure.map_map hq hstep]
            rfl
    _ = Measure.map q (B.prod P) := by rw [hstep_law]
    _ = Measure.map Prod.snd B := by
      calc
        Measure.map q (B.prod P) =
            Measure.map Prod.snd (Measure.map Prod.fst (B.prod P)) := by
              rw [Measure.map_map measurable_snd measurable_fst]
              rfl
        _ = Measure.map Prod.snd B := by simp
    _ = Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P := by
      change Measure.map Prod.snd
        ((Measure.map (gn21RawCalendarFirstExitAccumulatedTime initialState policy) P).prod
          (Measure.map (gn21RawCalendarFirstExitAccumulatedTime other policy) P)) = _
      rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The literal global-calendar construction supplies the IID-cycle interface
used by GN's Lemma 3: its two time coordinates are actual alternating
state-sojourns generated by one source path's successive deterministic tails. -/
noncomputable def gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
  (gn21RawCalendarFirstExitAccumulatedEarning initialState w policy seed,
    gn21RawCalendarPostExitSeed initialState policy seed)

theorem measurable_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state)) (hw : Measurable w) :
    Measurable
      (gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed initialState w policy) :=
  (measurable_gn21RawCalendarFirstExitAccumulatedEarning initialState w policy
    hpolicy hw).prodMk
    (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)

/-- A first physical-state payment and the literal raw tail after its exit
factor exactly; this is the reward counterpart of the time-tail product law. -/
theorem map_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : Measurable w) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map
      (gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed initialState w policy) P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState w policy) P).prod P := by
  let update : Real -> GN21RawPostThinningRaceHistory -> Real := fun earned history =>
    earned + gn21RawPostThinningRaceHistoryEarning w history
  have hupdate : Measurable fun z : Real × GN21RawPostThinningRaceHistory => update z.1 z.2 :=
    measurable_fst.add
      ((measurable_gn21RawPostThinningRaceHistoryEarning w hw).comp measurable_snd)
  simpa [gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed,
    gn21RawCalendarFirstExitAccumulatedEarning, update] using
    (map_gn21RawCalendarFirstExitHistoryFoldAndPostExitSeed
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI initialState policy
      hpolicy hpolicy_subset hpolicy_mass 0 update hupdate)

/-- One complete literal two-state calendar payment cycle, retaining the
same deterministic tail after both physical-state exits. -/
noncomputable def gn21RawCalendarTwoStateEarningAndPostExitSeed
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy) :
    GN21RawCycleSeed -> (Real × Real) × GN21RawCycleSeed := fun seed =>
  let first :=
    (gn21RawCalendarFirstExitAccumulatedEarning initialState (w initialState) policy seed,
      gn21RawCalendarPostExitSeed initialState policy seed)
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let second :=
    (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy first.2,
      gn21RawCalendarPostExitSeed other policy first.2)
  ((first.1, second.1), second.2)

/-- Time and payment observations advance through exactly the same literal
two-exit raw tail.  Thus the two coordinate families used in Lemma 1 remain
indexed by one calendar path rather than merely by equal-law paths. -/
theorem gn21RawCalendarTwoStateTimeAndEarning_regenerativeTail_eq
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy) :
    AppliedModelingLib.Probability.regenerativeTail
      (gn21RawCalendarTwoStateTimeAndPostExitSeed initialState policy) =
      AppliedModelingLib.Probability.regenerativeTail
        (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy) := by
  rfl

theorem measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hw : ∀ state, Measurable (w state)) :
    Measurable (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy) := by
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let first : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedEarning initialState (w initialState) policy seed,
      gn21RawCalendarPostExitSeed initialState policy seed)
  let second : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy seed,
      gn21RawCalendarPostExitSeed other policy seed)
  have hfirst : Measurable first :=
    (measurable_gn21RawCalendarFirstExitAccumulatedEarning initialState (w initialState)
      policy hpolicy (hw initialState)).prodMk
      (measurable_gn21RawCalendarPostExitSeed initialState policy hpolicy)
  have hsecond : Measurable second :=
    (measurable_gn21RawCalendarFirstExitAccumulatedEarning other (w other)
      policy hpolicy (hw other)).prodMk
      (measurable_gn21RawCalendarPostExitSeed other policy hpolicy)
  change Measurable (fun seed => (((first seed).1, (second (first seed).2).1),
    (second (first seed).2).2))
  exact ((measurable_fst.comp hfirst).prodMk
    ((measurable_fst.comp hsecond).comp (measurable_snd.comp hfirst))).prodMk
      ((measurable_snd.comp hsecond).comp (measurable_snd.comp hfirst))

theorem map_gn21RawCalendarTwoStateEarningAndPostExitSeed
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Measure.map (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy) P =
      ((Measure.map
        (gn21RawCalendarFirstExitAccumulatedEarning initialState (w initialState) policy) P).prod
        (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)
          (w (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)) policy) P)).prod P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let first : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedEarning initialState (w initialState) policy seed,
      gn21RawCalendarPostExitSeed initialState policy seed)
  let second : GN21RawCycleSeed -> Real × GN21RawCycleSeed := fun seed =>
    (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy seed,
      gn21RawCalendarPostExitSeed other policy seed)
  have hfirst : Measurable first :=
    measurable_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed initialState
      (w initialState) policy hpolicy (hw initialState)
  have hsecond : Measurable second :=
    measurable_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed other
      (w other) policy hpolicy (hw other)
  have hfirst_law : Measure.map first P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy) P).prod P := by
    simpa [P, first] using
      (map_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState (w initialState) policy
        hpolicy hpolicy_subset hpolicy_mass (hw initialState))
  have hsecond_law : Measure.map second P =
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P).prod P := by
    simpa [P, second] using
      (map_gn21RawCalendarFirstExitAccumulatedEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI other (w other) policy
        hpolicy hpolicy_subset hpolicy_mass (hw other))
  simpa [gn21RawCalendarTwoStateEarningAndPostExitSeed, other, first, second] using
    (map_compose_freshRawTailKernels P
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy) P)
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
      first second hfirst hsecond hfirst_law hsecond_law)

/-- Actual initial-state payments in successive alternating calendar cycles. -/
noncomputable def gn21RawCalendarAlternatingCycleInitialStateEarning
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (n : Nat) : GN21RawCycleSeed -> Real := fun seed =>
  (AppliedModelingLib.Probability.regenerativeSummary
    (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy) n seed).1

/-- Actual opposite-state payments in the same successive calendar cycles. -/
noncomputable def gn21RawCalendarAlternatingCycleOtherStateEarning
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (n : Nat) : GN21RawCycleSeed -> Real := fun seed =>
  (AppliedModelingLib.Probability.regenerativeSummary
    (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy) n seed).2

theorem measurable_gn21RawCalendarAlternatingCycleInitialStateEarning
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hw : ∀ state, Measurable (w state)) (n : Nat) :
    Measurable (gn21RawCalendarAlternatingCycleInitialStateEarning initialState w policy n) :=
  measurable_fst.comp
    (AppliedModelingLib.Probability.measurable_regenerativeSummary
      (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy)
      (measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
        hpolicy hw) n)

theorem measurable_gn21RawCalendarAlternatingCycleOtherStateEarning
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hw : ∀ state, Measurable (w state)) (n : Nat) :
    Measurable (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy n) :=
  measurable_snd.comp
    (AppliedModelingLib.Probability.measurable_regenerativeSummary
      (gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy)
      (measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
        hpolicy hw) n)

theorem pairwise_gn21RawCalendarAlternatingCycleInitialStateEarning_indepFun
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Pairwise (fun n m => ProbabilityTheory.IndepFun
      (gn21RawCalendarAlternatingCycleInitialStateEarning initialState w policy n)
      (gn21RawCalendarAlternatingCycleInitialStateEarning initialState w policy m) P) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
      (w initialState) policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy hpolicy (hw initialState)).aemeasurable
  let step := gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy hpolicy hw
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass hw)
  have hindep := AppliedModelingLib.Probability.regenerativeSummary_pairwise_indepFun
    P B step hstep hstep_law
  intro n m hnm
  simpa [gn21RawCalendarAlternatingCycleInitialStateEarning, step] using
    (hindep hnm).comp measurable_fst measurable_fst

theorem pairwise_gn21RawCalendarAlternatingCycleOtherStateEarning_indepFun
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    Pairwise (fun n m => ProbabilityTheory.IndepFun
      (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy n)
      (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy m) P) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
      (w initialState) policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy hpolicy (hw initialState)).aemeasurable
  let step := gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy hpolicy hw
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass hw)
  have hindep := AppliedModelingLib.Probability.regenerativeSummary_pairwise_indepFun
    P B step hstep hstep_law
  intro n m hnm
  simpa [gn21RawCalendarAlternatingCycleOtherStateEarning, step] using
    (hindep hnm).comp measurable_snd measurable_snd

theorem identDistrib_gn21RawCalendarAlternatingCycleInitialStateEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleInitialStateEarning initialState w policy n)
      (gn21RawCalendarAlternatingCycleInitialStateEarning initialState w policy 0) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
      (w initialState) policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
  let step := gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy hpolicy hw
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass hw)
  simpa [gn21RawCalendarAlternatingCycleInitialStateEarning, step, Function.comp_def] using
    (AppliedModelingLib.Probability.regenerativeSummary_identDistrib
      P B step hstep hstep_law n).comp measurable_fst

theorem identDistrib_gn21RawCalendarAlternatingCycleOtherStateEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) (n : Nat) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy n)
      (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy 0) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
      (w initialState) policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
  let step := gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy hpolicy hw
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass hw)
  simpa [gn21RawCalendarAlternatingCycleOtherStateEarning, step, Function.comp_def] using
    (AppliedModelingLib.Probability.regenerativeSummary_identDistrib
      P B step hstep hstep_law n).comp measurable_snd

/-- The opposite-state payment in the first alternating cycle has the law of
an ordinary first-exit payment started from that opposite state. -/
theorem identDistrib_gn21RawCalendarAlternatingCycleOtherStateEarning_zero_accumulated
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (initialState : Fin 2) (w : Fin 2 -> PricingFunction) (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (hw : ∀ state, Measurable (w state)) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    ProbabilityTheory.IdentDistrib
      (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy 0)
      (gn21RawCalendarFirstExitAccumulatedEarning
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)
        (w (AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState)) policy) P P := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initialState
  let B : Measure (Real × Real) :=
    (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
      (w initialState) policy) P).prod
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other (w other) policy) P)
  letI : IsProbabilityMeasure
      (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_gn21RawCalendarFirstExitAccumulatedEarning initialState
        (w initialState) policy hpolicy (hw initialState)).aemeasurable
  let step := gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy
  have hstep : Measurable step :=
    measurable_gn21RawCalendarTwoStateEarningAndPostExitSeed initialState w policy hpolicy hw
  have hstep_law : Measure.map step P = B.prod P := by
    simpa [P, B, step, other] using
      (map_gn21RawCalendarTwoStateEarningAndPostExitSeed
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initialState w policy
        hpolicy hpolicy_subset hpolicy_mass hw)
  let q : (Real × Real) × GN21RawCycleSeed -> Real := fun z => z.1.2
  have hq : Measurable q := measurable_snd.comp measurable_fst
  refine ⟨(measurable_gn21RawCalendarAlternatingCycleOtherStateEarning
    initialState w policy hpolicy hw 0).aemeasurable,
    (measurable_gn21RawCalendarFirstExitAccumulatedEarning other (w other)
      policy hpolicy (hw other)).aemeasurable, ?_⟩
  calc
    Measure.map (gn21RawCalendarAlternatingCycleOtherStateEarning initialState w policy 0) P =
        Measure.map q (Measure.map step P) := by
            change Measure.map (fun seed => (step seed).1.2) P = _
            rw [Measure.map_map hq hstep]
            rfl
    _ = Measure.map q (B.prod P) := by rw [hstep_law]
    _ = Measure.map Prod.snd B := by
      calc
        Measure.map q (B.prod P) =
            Measure.map Prod.snd (Measure.map Prod.fst (B.prod P)) := by
              rw [Measure.map_map measurable_snd measurable_fst]
              rfl
        _ = Measure.map Prod.snd B := by simp
    _ = Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other
        (w other) policy) P := by
      change Measure.map Prod.snd
        ((Measure.map (gn21RawCalendarFirstExitAccumulatedEarning initialState
          (w initialState) policy) P).prod
          (Measure.map (gn21RawCalendarFirstExitAccumulatedEarning other
            (w other) policy) P)) = _
      rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The literal global-calendar construction supplies the IID-cycle interface
used by GN's Lemma 3: its two time coordinates are actual alternating
state-sojourns generated by one source path's successive deterministic tails. -/
noncomputable def gn21TimeFractionIIDCycleModel_of_actualCalendar
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htimeI : IntegrableOn (fun tau : TripLength => tau) (policy 0) muI)
    (htimeJ : IntegrableOn (fun tau : TripLength => tau) (policy 1) muJ) :
    GN21TimeFractionIIDCycleModel
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI (policy 0) (policy 1) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let initial : Fin 2 := 0
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initial
  let timeI := gn21RawCalendarAlternatingCycleInitialStateTime initial policy
  let timeJ := gn21RawCalendarAlternatingCycleOtherStateTime initial policy
  have htimeI_source : Integrable
      (gn21RawCalendarFirstExitAccumulatedTime initial policy) P := by
    simpa [P, initial, gn21CycleMarkLaw] using
      (integrable_gn21RawCalendarFirstExitAccumulatedTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass (by simpa [initial] using htimeI))
  have htimeJ_source : Integrable
      (gn21RawCalendarFirstExitAccumulatedTime other policy) P := by
    simpa [P, initial, other, gn21CycleMarkLaw] using
      (integrable_gn21RawCalendarFirstExitAccumulatedTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI other policy
        hpolicy hpolicy_subset hpolicy_mass (by simpa [initial, other] using htimeJ))
  have htimeJ_zero : ProbabilityTheory.IdentDistrib (timeJ 0)
      (gn21RawCalendarFirstExitAccumulatedTime other policy) P P := by
    simpa [P, initial, other, timeJ] using
      (identDistrib_gn21RawCalendarAlternatingCycleOtherStateTime_zero_accumulated
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass)
  refine
    { stateTimeI := timeI
      stateTimeJ := timeJ
      arrivalI_pos := harrivalI
      arrivalJ_pos := harrivalJ
      switchIJ_pos := hswitchIJ
      switchJI_pos := hswitchJI
      σI_measurable := hpolicy 0
      σJ_measurable := hpolicy 1
      σI_subset := hpolicy_subset 0
      σJ_subset := hpolicy_subset 1
      massI_pos := ?_
      massJ_pos := ?_
      stateTimeI_integrable := ?_
      stateTimeJ_integrable := htimeJ_zero.integrable_iff.mpr htimeJ_source
      stateTimeI_independent := ?_
      stateTimeJ_independent := ?_
      stateTimeI_identDistrib := ?_
      stateTimeJ_identDistrib := ?_
      stateTimeI_mean_eq := ?_
      stateTimeJ_mean_eq := ?_ }
  · simpa [gn21CycleMarkLaw] using hpolicy_mass 0
  · simpa [gn21CycleMarkLaw] using hpolicy_mass 1
  · simpa [timeI, initial, gn21RawCalendarAlternatingCycleInitialStateTime,
      AppliedModelingLib.Probability.regenerativeSummary,
      gn21RawCalendarTwoStateTimeAndPostExitSeed] using htimeI_source
  · simpa [P, initial, timeI] using
      (pairwise_gn21RawCalendarAlternatingCycleInitialStateTime_indepFun
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass)
  · simpa [P, initial, timeJ] using
      (pairwise_gn21RawCalendarAlternatingCycleOtherStateTime_indepFun
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass)
  · intro n
    simpa [P, initial, timeI] using
      (identDistrib_gn21RawCalendarAlternatingCycleInitialStateTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass n)
  · intro n
    simpa [P, initial, timeJ] using
      (identDistrib_gn21RawCalendarAlternatingCycleOtherStateTime
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial policy
        hpolicy hpolicy_subset hpolicy_mass n)
  · calc
      (∫ seed, timeI 0 seed ∂P) =
          ∫ seed, gn21RawCalendarFirstExitAccumulatedTime initial policy seed ∂P := by
            simp [timeI, initial, gn21RawCalendarAlternatingCycleInitialStateTime,
              AppliedModelingLib.Probability.regenerativeSummary,
              gn21RawCalendarTwoStateTimeAndPostExitSeed]
      _ = _ := by
        simpa [P, initial, gn21CycleClockRate, gn21ArrivalClockIndex,
          RawTwoStateCTMC.switchClockIndex, gn21CycleMarkLaw] using
          (integral_gn21RawCalendarFirstExitAccumulatedTime_eq_expectedStateTimeInRenewalCycle
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initial policy
            hpolicy hpolicy_subset hpolicy_mass (by simpa [initial] using htimeI))
  · calc
      (∫ seed, timeJ 0 seed ∂P) =
          ∫ seed, gn21RawCalendarFirstExitAccumulatedTime other policy seed ∂P :=
        htimeJ_zero.integral_eq
      _ = _ := by
        simpa [P, initial, other, gn21CycleClockRate, gn21ArrivalClockIndex,
          RawTwoStateCTMC.switchClockIndex, gn21CycleMarkLaw] using
          (integral_gn21RawCalendarFirstExitAccumulatedTime_eq_expectedStateTimeInRenewalCycle
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI other policy
            hpolicy hpolicy_subset hpolicy_mass
            (by simpa [initial, other] using htimeJ))

/-- The literal global-calendar construction also supplies Lemma 1's payment
cycles.  `hwI` and `hwJ` are the source's regularity facts for the payment
functions; they are used only to expose measurable observables, not as new
economic restrictions on the displayed result. -/
noncomputable def gn21DynamicIIDCycleModel_of_actualCalendar
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htimeI : IntegrableOn (fun tau : TripLength => tau) (policy 0) muI)
    (htimeJ : IntegrableOn (fun tau : TripLength => tau) (policy 1) muJ)
    (hpaymentI : IntegrableOn wI (policy 0) muI)
    (hpaymentJ : IntegrableOn wJ (policy 1) muJ)
    (hwI : Measurable wI) (hwJ : Measurable wJ) :
    GN21DynamicIIDCycleModel
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ (policy 0) (policy 1) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let initial : Fin 2 := 0
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState initial
  let prices : Fin 2 -> PricingFunction := fun state => if state = 0 then wI else wJ
  let timeModel : GN21TimeFractionIIDCycleModel P muI muJ arrivalI arrivalJ
      switchIJ switchJI (policy 0) (policy 1) :=
    gn21TimeFractionIIDCycleModel_of_actualCalendar
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI policy
      hpolicy hpolicy_subset hpolicy_mass htimeI htimeJ
  let earningI := gn21RawCalendarAlternatingCycleInitialStateEarning initial prices policy
  let earningJ := gn21RawCalendarAlternatingCycleOtherStateEarning initial prices policy
  have hprices : ∀ state, Measurable (prices state) := by
    intro state
    fin_cases state <;> simp [prices, hwI, hwJ]
  have hpaymentI_source : Integrable
      (gn21RawCalendarFirstExitAccumulatedEarning initial (prices initial) policy) P := by
    simpa [P, initial, prices, gn21CycleMarkLaw] using
      (integrable_gn21RawCalendarFirstExitAccumulatedEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial (prices initial) policy
        hpolicy hpolicy_subset hpolicy_mass (by simpa [initial, prices] using hpaymentI))
  have hpaymentJ_source : Integrable
      (gn21RawCalendarFirstExitAccumulatedEarning other (prices other) policy) P := by
    simpa [P, initial, other, prices, gn21CycleMarkLaw] using
      (integrable_gn21RawCalendarFirstExitAccumulatedEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI other (prices other) policy
        hpolicy hpolicy_subset hpolicy_mass
        (by simpa [initial, other, prices] using hpaymentJ))
  have hpaymentJ_zero : ProbabilityTheory.IdentDistrib (earningJ 0)
      (gn21RawCalendarFirstExitAccumulatedEarning other (prices other) policy) P P := by
    simpa [P, initial, other, prices, earningJ] using
      (identDistrib_gn21RawCalendarAlternatingCycleOtherStateEarning_zero_accumulated
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial prices policy
        hpolicy hpolicy_subset hpolicy_mass hprices)
  refine
    { toGN21TimeFractionIIDCycleModel := timeModel
      stateEarningI := earningI
      stateEarningJ := earningJ
      stateEarningI_integrable := ?_
      stateEarningJ_integrable := hpaymentJ_zero.integrable_iff.mpr hpaymentJ_source
      stateEarningI_independent := ?_
      stateEarningJ_independent := ?_
      stateEarningI_identDistrib := ?_
      stateEarningJ_identDistrib := ?_
      stateEarningI_mean_eq := ?_
      stateEarningJ_mean_eq := ?_ }
  · simpa [earningI, initial, gn21RawCalendarAlternatingCycleInitialStateEarning,
      AppliedModelingLib.Probability.regenerativeSummary,
      gn21RawCalendarTwoStateEarningAndPostExitSeed] using hpaymentI_source
  · simpa [P, initial, prices, earningI] using
      (pairwise_gn21RawCalendarAlternatingCycleInitialStateEarning_indepFun
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial prices policy
        hpolicy hpolicy_subset hpolicy_mass hprices)
  · simpa [P, initial, prices, earningJ] using
      (pairwise_gn21RawCalendarAlternatingCycleOtherStateEarning_indepFun
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial prices policy
        hpolicy hpolicy_subset hpolicy_mass hprices)
  · intro n
    simpa [P, initial, prices, earningI] using
      (identDistrib_gn21RawCalendarAlternatingCycleInitialStateEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial prices policy
        hpolicy hpolicy_subset hpolicy_mass hprices n)
  · intro n
    simpa [P, initial, prices, earningJ] using
      (identDistrib_gn21RawCalendarAlternatingCycleOtherStateEarning
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI initial prices policy
        hpolicy hpolicy_subset hpolicy_mass hprices n)
  · calc
      (∫ seed, earningI 0 seed ∂P) =
          ∫ seed, gn21RawCalendarFirstExitAccumulatedEarning
            initial (prices initial) policy seed ∂P := by
            simp [earningI, initial, gn21RawCalendarAlternatingCycleInitialStateEarning,
              AppliedModelingLib.Probability.regenerativeSummary,
              gn21RawCalendarTwoStateEarningAndPostExitSeed]
      _ = _ := by
        simpa [P, initial, prices, gn21CycleClockRate, gn21ArrivalClockIndex,
          RawTwoStateCTMC.switchClockIndex, gn21CycleMarkLaw] using
          (integral_gn21RawCalendarFirstExitAccumulatedEarning_eq_expectedStateEarningInRenewalCycle
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI initial (prices initial) policy
            hpolicy hpolicy_subset hpolicy_mass
            (by simpa [initial, prices] using hpaymentI))
  · calc
      (∫ seed, earningJ 0 seed ∂P) =
          ∫ seed, gn21RawCalendarFirstExitAccumulatedEarning
            other (prices other) policy seed ∂P := hpaymentJ_zero.integral_eq
      _ = _ := by
        simpa [P, initial, other, prices, gn21CycleClockRate, gn21ArrivalClockIndex,
          RawTwoStateCTMC.switchClockIndex, gn21CycleMarkLaw] using
          (integral_gn21RawCalendarFirstExitAccumulatedEarning_eq_expectedStateEarningInRenewalCycle
            muI muJ arrivalI arrivalJ switchIJ switchJI
            harrivalI harrivalJ hswitchIJ hswitchJI other (prices other) policy
            hpolicy hpolicy_subset hpolicy_mass
            (by simpa [initial, other, prices] using hpaymentJ))

/-- Lemma 1's dynamic reward decomposition for one literal raw calendar path.
The state times and payments are successive deterministic-tail observations,
not independently resampled renewal-cycle proposals. -/
theorem paper_lemma1_stochastic_dynamic_reward_decomposition_of_actual_calendar
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htimeI : IntegrableOn (fun tau : TripLength => tau) (policy 0) muI)
    (htimeJ : IntegrableOn (fun tau : TripLength => tau) (policy 1) muJ)
    (hpaymentI : IntegrableOn wI (policy 0) muI)
    (hpaymentJ : IntegrableOn wJ (policy 1) muJ)
    (hwI : Measurable wI) (hwJ : Measurable wJ) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto
        (fun n : Nat =>
          ((∑ k ∈ Finset.range n,
            gn21RawCalendarAlternatingCycleInitialStateEarning 0
              (fun state => if state = 0 then wI else wJ) policy k seed) +
            (∑ k ∈ Finset.range n,
              gn21RawCalendarAlternatingCycleOtherStateEarning 0
                (fun state => if state = 0 then wI else wJ) policy k seed)) /
            ((∑ k ∈ Finset.range n,
              gn21RawCalendarAlternatingCycleInitialStateTime 0 policy k seed) +
              (∑ k ∈ Finset.range n,
                gn21RawCalendarAlternatingCycleOtherStateTime 0 policy k seed)))
        atTop
        (nhds
          (gn21MeasuredDynamicReward muI muJ arrivalI arrivalJ switchIJ
            switchJI wI wJ (policy 0) (policy 1))) := by
  let C := gn21DynamicIIDCycleModel_of_actualCalendar
    muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ
    harrivalI harrivalJ hswitchIJ hswitchJI policy
    hpolicy hpolicy_subset hpolicy_mass htimeI htimeJ hpaymentI hpaymentJ hwI hwJ
  simpa [C, gn21DynamicIIDCycleModel_of_actualCalendar,
    gn21TimeFractionIIDCycleModel_of_actualCalendar] using
    (paper_lemma1_stochastic_dynamic_reward_decomposition_of_iid_cycles C)

/-- Lemma 3's renewal-cycle time fraction for the literal calendar process.
Unlike the earlier raw-seed-path route, every summand here is read from one
raw source path by successively taking its deterministic post-exit tail. -/
theorem paper_lemma3_stochastic_time_fraction_formula_of_actual_calendar
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (policy : Fin 2 -> TripPolicy)
    (hpolicy : ∀ state, MeasurableSet (policy state))
    (hpolicy_subset : ∀ state, policy state ⊆ acceptAllPolicy)
    (hpolicy_mass : ∀ state,
      0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) (policy state))
    (htimeI : IntegrableOn (fun tau : TripLength => tau) (policy 0) muI)
    (htimeJ : IntegrableOn (fun tau : TripLength => tau) (policy 1) muJ) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto
        (fun n : Nat =>
          (∑ k ∈ Finset.range n,
            gn21RawCalendarAlternatingCycleInitialStateTime 0 policy k seed) /
            ((∑ k ∈ Finset.range n,
              gn21RawCalendarAlternatingCycleInitialStateTime 0 policy k seed) +
              (∑ k ∈ Finset.range n,
                gn21RawCalendarAlternatingCycleOtherStateTime 0 policy k seed)))
        atTop
        (nhds
          (gn21MeasuredTimeFraction muI muJ arrivalI arrivalJ switchIJ
            switchJI (policy 0) (policy 1))) := by
  let C := gn21TimeFractionIIDCycleModel_of_actualCalendar
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI policy
    hpolicy hpolicy_subset hpolicy_mass htimeI htimeJ
  simpa [C, gn21TimeFractionIIDCycleModel_of_actualCalendar] using
    (paper_lemma3_stochastic_time_fraction_formula_of_iid_cycles C)

end

end GN21DriverSurgePricing
