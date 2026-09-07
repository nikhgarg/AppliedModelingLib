import GN21DriverSurgePricing.AcceptedTripSelection
import AppliedModelingLib.Foundations.Probability.IndependentPairLaw
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

/-!
# Literal first accepted-arrival time for GN21

This module keeps the marked-Poisson timing construction on the original raw
GN21 clock-and-mark product seed.  In particular, the first accepted-arrival
time is an observable of that seed, rather than a coordinate of a separately
supplied post-thinning model.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace AcceptedArrivalTime

/-- The literal raw trip-mark stream selected by a source state. -/
def rawTripMarkStream (state : Fin 2) : GN21RawCycleSeed -> Nat -> TripLength :=
  fun seed n => gn21RawCycleMark state n seed

/-- The literal raw exponential interarrival stream selected by a source
clock. -/
def rawClockStream (clock : Fin 4) : GN21RawCycleSeed -> Nat -> Real :=
  fun seed n => gn21RawCycleClock clock n seed

/-- The actual arrival time of the first raw request whose trip mark is
accepted.  It is totalized only on the null no-accepted-mark event through
`firstAcceptedIndex`. -/
noncomputable def gn21RawFirstAcceptedArrivalTime
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Real :=
  fun seed => AppliedModelingLib.Probability.PoissonProcess.arrivalTime
    (AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed))
    (rawClockStream clock seed)

/-- The arrival-clock suffix strictly after the literal accepted request.
The first entry is the next raw interarrival gap, because the accepted
request's own gap is already included in `gn21RawFirstAcceptedArrivalTime`. -/
noncomputable def gn21RawPostFirstAcceptedArrivalGapTail
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Nat -> Real :=
  fun seed n => rawClockStream clock seed
    (AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed) + 1 + n)

theorem measurable_rawTripMarkStream (state : Fin 2) :
    Measurable (rawTripMarkStream state) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
    ((measurable_pi_apply state).comp measurable_snd))

theorem measurable_rawClockStream (clock : Fin 4) :
    Measurable (rawClockStream clock) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
    ((measurable_pi_apply clock).comp measurable_fst))

theorem measurable_rawFirstAcceptedIndex
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (fun seed : GN21RawCycleSeed =>
      AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed)) := by
  exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp
    (measurable_rawTripMarkStream state)

theorem measurable_gn21RawFirstAcceptedArrivalTime
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawFirstAcceptedArrivalTime clock state sigma) := by
  let index : GN21RawCycleSeed -> Nat := fun seed =>
    AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed)
  have hindex : Measurable index := by
    simpa [index] using measurable_rawFirstAcceptedIndex state sigma hsigma
  have hindex_event : forall n, MeasurableSet {seed | index seed = n} := by
    intro n
    simpa only [Set.preimage_setOf_eq] using hindex (measurableSet_singleton n)
  let h : forall seed : GN21RawCycleSeed, exists n, index seed = n :=
    fun seed => ⟨index seed, rfl⟩
  have hmeas : Measurable (fun seed : GN21RawCycleSeed =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime (Nat.find (h seed))
        (rawClockStream clock seed)) :=
    Measurable.find
      (fun n =>
        (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
          (measurable_rawClockStream clock))
      hindex_event h
  convert hmeas using 1
  funext seed
  have hfind : Nat.find (h seed) = index seed := (Nat.find_spec (h seed)).symm
  simp [gn21RawFirstAcceptedArrivalTime, index, hfind]

/-- The raw post-accepted arrival suffix is measurable. -/
theorem measurable_gn21RawPostFirstAcceptedArrivalGapTail
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostFirstAcceptedArrivalGapTail clock state sigma) := by
  let index : (Nat -> TripLength) -> Nat := fun marks =>
    AcceptedTripSelection.firstAcceptedIndex sigma marks + 1
  have hindex : Measurable index := by
    exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).add_const 1
  have hinput : Measurable (fun seed : GN21RawCycleSeed =>
      (rawTripMarkStream state seed, rawClockStream clock seed)) :=
    (measurable_rawTripMarkStream state).prodMk (measurable_rawClockStream clock)
  simpa [index, gn21RawPostFirstAcceptedArrivalGapTail, rawTripMarkStream,
    rawClockStream, AppliedModelingLib.Probability.IIDStream.externalIndexTail,
    AppliedModelingLib.Probability.IIDStream.coordinate] using
    ((AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail
      (α := Real) index hindex).comp hinput)

/-- The complete source-observable history through the first accepted request:
its index, selected mark, untouched mark tail, literal arrival time, and the
arrival-gap tail strictly after that request.  The definition is on the
marked-stream/arrival-stream product so it can be transported through an
explicit source product law. -/
noncomputable def firstAcceptedArrivalHistoryOfStreams
    (sigma : TripPolicy) :
    ((Nat -> TripLength) × (Nat -> Real)) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) :=
  fun paths =>
    ((((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
      AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
      AcceptedTripSelection.firstAcceptedTripTail sigma paths.1),
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2),
      AppliedModelingLib.Probability.IIDStream.externalIndexTail
        (fun marks => AcceptedTripSelection.firstAcceptedIndex sigma marks + 1)
        paths)

/-- The complete stopped arrival/mark history is measurable on its direct
marked-stream/arrival-stream source carrier. -/
theorem measurable_firstAcceptedArrivalHistoryOfStreams
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (firstAcceptedArrivalHistoryOfStreams sigma) := by
  let stopped : (Nat -> TripLength) ->
      ((Nat × TripLength) × (Nat -> TripLength)) := fun marks =>
    ((AcceptedTripSelection.firstAcceptedIndex sigma marks,
      AcceptedTripSelection.firstAcceptedTripMark sigma marks),
      AcceptedTripSelection.firstAcceptedTripTail sigma marks)
  have hstopped : Measurable stopped := by
    exact
      ((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma)).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma)
  have harrival : Measurable (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2) := by
    let index : (Nat -> TripLength) × (Nat -> Real) -> Nat := fun paths =>
      AcceptedTripSelection.firstAcceptedIndex sigma paths.1
    have hindex : Measurable index := by
      exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp
        measurable_fst
    have hindexEvent : ∀ n, MeasurableSet {paths | index paths = n} := by
      intro n
      simpa only [Set.preimage_setOf_eq] using hindex (measurableSet_singleton n)
    let h : ∀ paths : (Nat -> TripLength) × (Nat -> Real), ∃ n, index paths = n :=
      fun paths => ⟨index paths, rfl⟩
    have hmeas : Measurable (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (Nat.find (h paths)) paths.2) :=
      Measurable.find
        (fun n =>
          (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
            measurable_snd)
        hindexEvent h
    convert hmeas using 1
    funext paths
    have hfind : Nat.find (h paths) = index paths := (Nat.find_spec (h paths)).symm
    simp [index, hfind]
  let tailIndex : (Nat -> TripLength) -> Nat := fun marks =>
    AcceptedTripSelection.firstAcceptedIndex sigma marks + 1
  have htailIndex : Measurable tailIndex := by
    exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).add_const 1
  have htail : Measurable (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
      AppliedModelingLib.Probability.IIDStream.externalIndexTail tailIndex paths) := by
    exact AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail
      (α := Real) tailIndex htailIndex
  exact ((hstopped.comp measurable_fst).prodMk harrival).prodMk htail

/-- On a direct product of an IID trip-mark stream and an exponential
interarrival stream, the complete literal history through the first accepted
mark factors from the remaining arrival-gap tail.  This is the generic
stopped-source statement used to retain independent companion coordinates in
calendar constructions; it does not introduce a post-thinning process. -/
theorem firstAcceptedArrivalHistoryOfStreams_hasLaw_prod
    (markLaw : Measure TripLength) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    HasLaw (firstAcceptedArrivalHistoryOfStreams sigma)
      ((Measure.map (fun z : (Nat -> TripLength) × (Nat -> Real) =>
          (((AcceptedTripSelection.firstAcceptedIndex sigma z.1,
            AcceptedTripSelection.firstAcceptedTripMark sigma z.1),
            AcceptedTripSelection.firstAcceptedTripTail sigma z.1),
            AppliedModelingLib.Probability.PoissonProcess.arrivalTime
              (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2))
          ((AppliedModelingLib.Probability.IIDStream.measure markLaw).prod
            (AppliedModelingLib.Probability.IIDStream.measure
              (ProbabilityTheory.expMeasure rate)))).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate))
      ((AppliedModelingLib.Probability.IIDStream.measure markLaw).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  let I := AppliedModelingLib.Probability.IIDStream.measure markLaw
  let E := ProbabilityTheory.expMeasure rate
  let gaps := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate
  let index : (Nat -> TripLength) -> Nat := fun marks =>
    AcceptedTripSelection.firstAcceptedIndex sigma marks + 1
  let stopped : (Nat -> TripLength) ->
      ((Nat × TripLength) × (Nat -> TripLength)) := fun marks =>
    ((AcceptedTripSelection.firstAcceptedIndex sigma marks,
      AcceptedTripSelection.firstAcceptedTripMark sigma marks),
      AcceptedTripSelection.firstAcceptedTripTail sigma marks)
  let f : ((Nat -> TripLength) × (Nat -> Real)) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun z =>
    (stopped z.1,
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2)
  let prefixValue : ∀ n : Nat,
      (Nat -> TripLength) × (Finset.range n -> Real) ->
        (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun n z =>
    (stopped z.1, ∑ i ∈ (Finset.range n).attach, z.2 i)
  letI : IsProbabilityMeasure E :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure E) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hrate
  letI : IsProbabilityMeasure I := by
    dsimp [I, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hindex : Measurable index := by
    exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).add_const 1
  have hstopped : Measurable stopped := by
    exact
      ((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma)).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma)
  have harrival : Measurable (fun z : (Nat -> TripLength) × (Nat -> Real) =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2) := by
    let K : (Nat -> TripLength) × (Nat -> Real) -> Nat := fun z =>
      AcceptedTripSelection.firstAcceptedIndex sigma z.1
    have hK : Measurable K := by
      exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp measurable_fst
    have hKevent : ∀ n, MeasurableSet {z | K z = n} := by
      intro n
      simpa only [Set.preimage_setOf_eq] using hK (measurableSet_singleton n)
    let h : ∀ z : (Nat -> TripLength) × (Nat -> Real), ∃ n, K z = n :=
      fun z => ⟨K z, rfl⟩
    have hmeas : Measurable (fun z : (Nat -> TripLength) × (Nat -> Real) =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime (Nat.find (h z)) z.2) :=
      Measurable.find
        (fun n =>
          (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
            measurable_snd)
        hKevent h
    convert hmeas using 1
    funext z
    have hfind : Nat.find (h z) = K z := (Nat.find_spec (h z)).symm
    simp [K, hfind]
  have hf : Measurable f := by
    exact (hstopped.comp measurable_fst).prodMk harrival
  have hprefixValue : ∀ n, Measurable (prefixValue n) := by
    intro n
    apply (hstopped.comp measurable_fst).prodMk
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).comp measurable_snd
  have hfactor : ∀ z, f z =
      prefixValue (index z.1)
        (AppliedModelingLib.Probability.IIDStream.stateInitialPrefix (index z.1) z) := by
    intro z
    apply Prod.ext
    · rfl
    · simp [f, prefixValue, index,
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
        AppliedModelingLib.Probability.PoissonProcess.interarrival,
        AppliedModelingLib.Probability.IIDStream.stateInitialPrefix,
        AppliedModelingLib.Probability.IIDStream.coordinate, Finset.sum_attach]
  have hindep : IndepFun f
      (AppliedModelingLib.Probability.IIDStream.externalIndexTail index)
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) := by
    apply AppliedModelingLib.Probability.IIDStream.indepFun_of_externalIndexPrefixEvent_tail
      I E index hindex f
    intro S hS
    exact AppliedModelingLib.Probability.IIDStream.externalIndexPrefixEvent_preimage_of_initialPrefixFactor
      index prefixValue hprefixValue f hfactor S hS
  have hfirstLaw : HasLaw f
      (Measure.map f (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)))
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) := by
    exact ⟨hf.aemeasurable, rfl⟩
  have htailLaw :=
    AppliedModelingLib.Probability.IIDStream.externalIndexTail_hasLaw I E index hindex
  have hjoint := AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
    hfirstLaw htailLaw hindep
  simpa [I, E, gaps, index, stopped, f,
    firstAcceptedArrivalHistoryOfStreams,
    AppliedModelingLib.Probability.IIDStream.measure,
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure,
    AppliedModelingLib.Probability.IIDStream.externalIndexTail,
    AppliedModelingLib.Probability.IIDStream.coordinate] using hjoint

/-- The first-hit event for a paired marked-interarrival coordinate stream. -/
noncomputable def pairHit (sigma : TripPolicy) : Set (TripLength × Real) :=
  Prod.fst ⁻¹' sigma

/-- The stopped accepted-request prefix of one stream whose coordinates pair
each trip mark with its literal interarrival gap. -/
noncomputable def pairedFirstAcceptedPrefix (sigma : TripPolicy) :
    (Nat -> TripLength × Real) -> ((Nat × TripLength) × Real) := fun omega =>
  ((AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma) omega,
      (AppliedModelingLib.Probability.IIDStream.firstHitValue (pairHit sigma) omega).1),
    AppliedModelingLib.Probability.PoissonProcess.arrivalTime
      (AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma) omega)
      (fun n => (omega n).2))

/-- Split a paired source tail back into its literal mark and gap tails. -/
noncomputable def unzipPairedStream :
    (Nat -> TripLength × Real) -> (Nat -> TripLength) × (Nat -> Real) := fun omega =>
  (fun n => (omega n).1, fun n => (omega n).2)

theorem measurable_pairHit (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (pairHit sigma) := by
  exact hsigma.preimage measurable_fst

theorem measurable_unzipPairedStream : Measurable unzipPairedStream := by
  apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro n
  · exact measurable_fst.comp (measurable_pi_apply n)
  · exact measurable_snd.comp (measurable_pi_apply n)

theorem measurable_pairedFirstAcceptedPrefix
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (pairedFirstAcceptedPrefix sigma) := by
  let hit := pairHit sigma
  let index : (Nat -> TripLength × Real) -> Nat :=
    AppliedModelingLib.Probability.IIDStream.firstHit hit
  have hhit : MeasurableSet hit := by
    simpa [hit] using measurable_pairHit sigma hsigma
  have hindex : Measurable index := by
    simpa [index] using
      (AppliedModelingLib.Probability.IIDStream.measurable_firstHit hit hhit)
  have hindexEvent : ∀ n, MeasurableSet {omega | index omega = n} := by
    intro n
    simpa only [Set.preimage_setOf_eq] using hindex (measurableSet_singleton n)
  let gaps : (Nat -> TripLength × Real) -> Nat -> Real := fun omega n => (omega n).2
  have hgaps : Measurable gaps := by
    apply measurable_pi_lambda
    intro n
    exact measurable_snd.comp (measurable_pi_apply n)
  let h : ∀ omega : Nat -> TripLength × Real, ∃ n, index omega = n :=
    fun omega => ⟨index omega, rfl⟩
  have htime : Measurable (fun omega : Nat -> TripLength × Real =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (Nat.find (h omega)) (gaps omega)) :=
    Measurable.find
      (fun n => (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp hgaps)
      hindexEvent h
  have htime' : Measurable (fun omega : Nat -> TripLength × Real =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (index omega) (gaps omega)) := by
    convert htime using 1
    funext omega
    have hfind : Nat.find (h omega) = index omega := (Nat.find_spec (h omega)).symm
    rw [hfind]
  simpa [pairedFirstAcceptedPrefix, hit, index, gaps] using
    ((hindex.prodMk
      (measurable_fst.comp
        (AppliedModelingLib.Probability.IIDStream.measurable_firstHitValue hit hhit))).prodMk
      htime')

theorem pairedFirstAcceptedPrefix_prefixEvent
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (S : Set ((Nat × TripLength) × Real)) (hS : MeasurableSet S) :
    AppliedModelingLib.Probability.IIDStream.FirstHitPrefixEvent (pairHit sigma)
      ((pairedFirstAcceptedPrefix sigma) ⁻¹' S) := by
  classical
  intro n
  let hit := pairHit sigma
  let last : Finset.range (n + 1) :=
    ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩
  let prefixValue : (Finset.range (n + 1) -> TripLength × Real) ->
      ((Nat × TripLength) × Real) := fun pref =>
    ((n, (pref last).1), ∑ i ∈ (Finset.range (n + 1)).attach, (pref i).2)
  have hprefixValue : Measurable prefixValue := by
    apply (measurable_const.prodMk (measurable_fst.comp (measurable_pi_apply last))).prodMk
    apply Finset.measurable_sum
    intro i _
    exact measurable_snd.comp (measurable_pi_apply i)
  have hhit : MeasurableSet hit := by
    simpa [hit] using measurable_pairHit sigma hsigma
  rcases AppliedModelingLib.Probability.IIDStream.firstHitEvent_prefix_measurable hit hhit n with
    ⟨E, hE, hpreE⟩
  refine MeasurableSpace.measurableSet_comap.2
    ⟨prefixValue ⁻¹' S ∩ E, (hprefixValue hS).inter hE, ?_⟩
  ext omega
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hprefix, hfirst⟩
    have hfirst' : omega ∈ AppliedModelingLib.Probability.IIDStream.firstHitEvent hit n := by
      rw [← hpreE]
      exact hfirst
    have hindex := AppliedModelingLib.Probability.IIDStream.firstHit_eq_of_mem_firstHitEvent
      hfirst'
    have hindex' : AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma) omega = n := by
      simpa [hit] using hindex
    have hprefixEval : prefixValue
        (AppliedModelingLib.Probability.IIDStream.streamPrefix n omega) =
        ((n, (omega n).1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
            (fun k => (omega k).2)) := by
      unfold prefixValue
      apply Prod.ext
      · apply Prod.ext <;> rfl
      · simp only [AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
          AppliedModelingLib.Probability.PoissonProcess.interarrival,
          AppliedModelingLib.Probability.IIDStream.streamPrefix,
          AppliedModelingLib.Probability.IIDStream.coordinate]
        exact Finset.sum_attach (Finset.range (n + 1)) (fun x => (omega x).2)
    have hpairEval : pairedFirstAcceptedPrefix sigma omega =
        ((n, (omega n).1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
            (fun k => (omega k).2)) := by
      simp [pairedFirstAcceptedPrefix,
        AppliedModelingLib.Probability.IIDStream.firstHitValue, hindex']
    refine ⟨?_, hfirst'⟩
    rw [hprefixEval] at hprefix
    rw [hpairEval]
    exact hprefix
  · rintro ⟨hprefix, hfirst⟩
    have hfirst' : AppliedModelingLib.Probability.IIDStream.streamPrefix n omega ∈ E := by
      change omega ∈ AppliedModelingLib.Probability.IIDStream.streamPrefix n ⁻¹' E
      rw [hpreE]
      exact hfirst
    have hindex := AppliedModelingLib.Probability.IIDStream.firstHit_eq_of_mem_firstHitEvent
      hfirst
    have hindex' : AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma) omega = n := by
      simpa [hit] using hindex
    have hprefixEval : prefixValue
        (AppliedModelingLib.Probability.IIDStream.streamPrefix n omega) =
        ((n, (omega n).1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
            (fun k => (omega k).2)) := by
      unfold prefixValue
      apply Prod.ext
      · apply Prod.ext <;> rfl
      · simp only [AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
          AppliedModelingLib.Probability.PoissonProcess.interarrival,
          AppliedModelingLib.Probability.IIDStream.streamPrefix,
          AppliedModelingLib.Probability.IIDStream.coordinate]
        exact Finset.sum_attach (Finset.range (n + 1)) (fun x => (omega x).2)
    have hpairEval : pairedFirstAcceptedPrefix sigma omega =
        ((n, (omega n).1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
            (fun k => (omega k).2)) := by
      simp [pairedFirstAcceptedPrefix,
        AppliedModelingLib.Probability.IIDStream.firstHitValue, hindex']
    refine ⟨?_, hfirst'⟩
    rw [hpairEval] at hprefix
    rw [hprefixEval]
    exact hprefix

theorem pairedFirstAcceptedPrefix_zip_eq (sigma : TripPolicy)
    (paths : (Nat -> TripLength) × (Nat -> Real)) :
    pairedFirstAcceptedPrefix sigma
      (AppliedModelingLib.Probability.IIDStream.zip paths) =
      ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
          AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2) := by
  classical
  have hfirst : AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma)
      (AppliedModelingLib.Probability.IIDStream.zip paths) =
      AcceptedTripSelection.firstAcceptedIndex sigma paths.1 := by
    rw [AcceptedTripSelection.firstAcceptedIndex_eq_firstHit]
    unfold AppliedModelingLib.Probability.IIDStream.firstHit
    simp only [pairHit, AppliedModelingLib.Probability.IIDStream.zip,
      Set.mem_preimage]
  apply Prod.ext
  · apply Prod.ext
    · exact hfirst
    · simp [pairedFirstAcceptedPrefix,
        AppliedModelingLib.Probability.IIDStream.firstHitValue,
        AppliedModelingLib.Probability.IIDStream.zip, hfirst,
        AcceptedTripSelection.firstAcceptedTripMark_eq_firstHitValue,
        AcceptedTripSelection.firstAcceptedIndex_eq_firstHit]
  · simp [pairedFirstAcceptedPrefix,
      AppliedModelingLib.Probability.IIDStream.zip, hfirst]

theorem unzip_postFirstHitTail_zip_eq (sigma : TripPolicy)
    (paths : (Nat -> TripLength) × (Nat -> Real)) :
    unzipPairedStream
      (AppliedModelingLib.Probability.IIDStream.postFirstHitTail (pairHit sigma)
        (AppliedModelingLib.Probability.IIDStream.zip paths)) =
      (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1,
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun marks => AcceptedTripSelection.firstAcceptedIndex sigma marks + 1) paths) := by
  classical
  have hfirst : AppliedModelingLib.Probability.IIDStream.firstHit (pairHit sigma)
      (AppliedModelingLib.Probability.IIDStream.zip paths) =
      AcceptedTripSelection.firstAcceptedIndex sigma paths.1 := by
    rw [AcceptedTripSelection.firstAcceptedIndex_eq_firstHit]
    unfold AppliedModelingLib.Probability.IIDStream.firstHit
    simp only [pairHit, AppliedModelingLib.Probability.IIDStream.zip,
      Set.mem_preimage]
  apply Prod.ext
  · funext n
    simp [unzipPairedStream,
      AppliedModelingLib.Probability.IIDStream.postFirstHitTail,
      AppliedModelingLib.Probability.IIDStream.coordinate,
      AppliedModelingLib.Probability.IIDStream.zip,
      AcceptedTripSelection.firstAcceptedTripTail,
      AcceptedTripSelection.firstAcceptedIndex_eq_firstHit,
      hfirst]
  · funext n
    simp [unzipPairedStream,
      AppliedModelingLib.Probability.IIDStream.postFirstHitTail,
      AppliedModelingLib.Probability.IIDStream.coordinate,
      AppliedModelingLib.Probability.IIDStream.zip,
      AppliedModelingLib.Probability.IIDStream.externalIndexTail,
      hfirst]

/-- The accepted marked-arrival prefix factors from both literal tails. -/
theorem firstAcceptedArrivalPrefixAndTails_hasLaw_prod
    (markLaw : Measure TripLength) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass markLaw sigma) :
    HasLaw
      (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
        (((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
            AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime
            (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2),
        (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1,
          AppliedModelingLib.Probability.IIDStream.externalIndexTail
            (fun marks => AcceptedTripSelection.firstAcceptedIndex sigma marks + 1) paths)))
      (
        (Measure.map (fun paths : (Nat -> TripLength) × (Nat -> Real) =>
          ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
            AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime
            (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2))
          (
            (AppliedModelingLib.Probability.IIDStream.measure markLaw).prod
            (AppliedModelingLib.Probability.IIDStream.measure
              (ProbabilityTheory.expMeasure rate))
          )
        ).prod
        (
          (AppliedModelingLib.Probability.IIDStream.measure markLaw).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)
        )
      )
      (
        (AppliedModelingLib.Probability.IIDStream.measure markLaw).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)
      ) := by
  classical
  let M := AppliedModelingLib.Probability.IIDStream.measure markLaw
  let E := ProbabilityTheory.expMeasure rate
  let G := AppliedModelingLib.Probability.IIDStream.measure E
  let pairLaw := markLaw.prod E
  let pairStream := AppliedModelingLib.Probability.IIDStream.measure pairLaw
  let source := M.prod G
  let pref : (Nat -> TripLength × Real) -> ((Nat × TripLength) × Real) :=
    pairedFirstAcceptedPrefix sigma
  let tail : (Nat -> TripLength × Real) -> Nat -> TripLength × Real :=
    AppliedModelingLib.Probability.IIDStream.postFirstHitTail (pairHit sigma)
  let output : (Nat -> TripLength × Real) ->
      ((Nat × TripLength) × Real) × ((Nat -> TripLength) × (Nat -> Real)) := fun omega =>
    (pref omega, unzipPairedStream (tail omega))
  let rawPrefix : (Nat -> TripLength) × (Nat -> Real) -> ((Nat × TripLength) × Real) :=
    fun paths =>
      ((AcceptedTripSelection.firstAcceptedIndex sigma paths.1,
          AcceptedTripSelection.firstAcceptedTripMark sigma paths.1),
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime
          (AcceptedTripSelection.firstAcceptedIndex sigma paths.1) paths.2)
  let rawOutput : (Nat -> TripLength) × (Nat -> Real) ->
      ((Nat × TripLength) × Real) × ((Nat -> TripLength) × (Nat -> Real)) := fun paths =>
    (rawPrefix paths,
      (AcceptedTripSelection.firstAcceptedTripTail sigma paths.1,
        AppliedModelingLib.Probability.IIDStream.externalIndexTail
          (fun marks => AcceptedTripSelection.firstAcceptedIndex sigma marks + 1) paths))
  letI : IsProbabilityMeasure E := ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure G := by
    dsimp [G, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure pairLaw := by
    dsimp [pairLaw]
    infer_instance
  letI : IsProbabilityMeasure pairStream := by
    dsimp [pairStream, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhit : MeasurableSet (pairHit sigma) := measurable_pairHit sigma hsigma
  have hmass' : 0 < markLaw sigma :=
    measure_pos_of_singleStateTripMass_pos markLaw sigma hmass
  have hpairMass : 0 < pairLaw (pairHit sigma) := by
    calc
      pairLaw (pairHit sigma) = Measure.map Prod.fst pairLaw sigma := by
        rw [Measure.map_apply measurable_fst hsigma]
        rfl
      _ = markLaw sigma := by
        rw [Measure.map_fst_prod, MeasureTheory.measure_univ, one_smul]
      _ > 0 := hmass'
  have hprefixMeas : Measurable pref := by
    simpa [pref] using measurable_pairedFirstAcceptedPrefix sigma hsigma
  have htailMeas : Measurable tail := by
    simpa [tail] using
      AppliedModelingLib.Probability.IIDStream.measurable_postFirstHitTail
        (pairHit sigma) hhit
  have hprefixLaw : HasLaw pref (Measure.map pref pairStream) pairStream :=
    ⟨hprefixMeas.aemeasurable, rfl⟩
  have htailLaw : HasLaw tail pairStream pairStream := by
    simpa [tail, pairStream, pairLaw] using
      (AppliedModelingLib.Probability.IIDStream.postFirstHitTail_hasLaw
        pairLaw (pairHit sigma) hhit hpairMass)
  have hindep : IndepFun pref tail pairStream := by
    simpa [pref, tail, pairStream, pairLaw] using
      (AppliedModelingLib.Probability.IIDStream.indepFun_of_firstHitPrefixEvent_tail
        pairLaw (pairHit sigma) hhit hpairMass pref hprefixMeas
        (fun S hS => pairedFirstAcceptedPrefix_prefixEvent sigma hsigma S hS))
  have hjoint := AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
    hprefixLaw htailLaw hindep
  have hzip : HasLaw (AppliedModelingLib.Probability.IIDStream.zip
      (α := TripLength) (β := Real)) pairStream source := by
    simpa [pairStream, pairLaw, source, M, G, E] using
      (AppliedModelingLib.Probability.IIDStream.zip_hasLaw markLaw E)
  have hunzip : HasLaw unzipPairedStream source pairStream := by
    refine ⟨measurable_unzipPairedStream.aemeasurable, ?_⟩
    calc
      Measure.map unzipPairedStream pairStream =
          Measure.map unzipPairedStream
            (Measure.map (AppliedModelingLib.Probability.IIDStream.zip
              (α := TripLength) (β := Real)) source) := by rw [hzip.map_eq]
      _ = Measure.map (unzipPairedStream ∘
          AppliedModelingLib.Probability.IIDStream.zip) source := by
            rw [Measure.map_map measurable_unzipPairedStream
              AppliedModelingLib.Probability.IIDStream.measurable_zip]
      _ = source := by
        convert Measure.map_id using 1
  let transform : ((Nat × TripLength) × Real) × (Nat -> TripLength × Real) ->
      ((Nat × TripLength) × Real) × ((Nat -> TripLength) × (Nat -> Real)) := fun z =>
    (z.1, unzipPairedStream z.2)
  have htransformMeas : Measurable transform := by
    exact measurable_fst.prodMk (measurable_unzipPairedStream.comp measurable_snd)
  have htransformLaw : Measure.map transform
      ((Measure.map pref pairStream).prod pairStream) =
      (Measure.map pref pairStream).prod source := by
    rw [show transform = Prod.map id unzipPairedStream by rfl,
      ← Measure.map_prod_map (Measure.map pref pairStream) pairStream
        measurable_id measurable_unzipPairedStream,
      Measure.map_id, hunzip.map_eq]
  have htrans : HasLaw transform ((Measure.map pref pairStream).prod source)
      ((Measure.map pref pairStream).prod pairStream) :=
    ⟨htransformMeas.aemeasurable, htransformLaw⟩
  have houtput : HasLaw output ((Measure.map pref pairStream).prod source) pairStream := by
    simpa [output, transform] using htrans.comp hjoint
  have hprefixMap : Measure.map pref pairStream = Measure.map rawPrefix source := by
    calc
      Measure.map pref pairStream = Measure.map pref
          (Measure.map (AppliedModelingLib.Probability.IIDStream.zip
            (α := TripLength) (β := Real)) source) := by rw [hzip.map_eq]
      _ = Measure.map (pref ∘ AppliedModelingLib.Probability.IIDStream.zip) source := by
        rw [Measure.map_map hprefixMeas
          AppliedModelingLib.Probability.IIDStream.measurable_zip]
      _ = Measure.map rawPrefix source := by
        congr 1
        funext paths
        simpa [pref, rawPrefix] using pairedFirstAcceptedPrefix_zip_eq sigma paths
  have hraw : HasLaw (output ∘ AppliedModelingLib.Probability.IIDStream.zip)
      ((Measure.map rawPrefix source).prod source) source := by
    simpa [hprefixMap] using houtput.comp hzip
  have houtputEq : output ∘ AppliedModelingLib.Probability.IIDStream.zip = rawOutput := by
    funext paths
    simp only [Function.comp_apply, output, rawOutput, pref, tail]
    rw [pairedFirstAcceptedPrefix_zip_eq sigma paths,
      unzip_postFirstHitTail_zip_eq sigma paths]
  change HasLaw rawOutput ((Measure.map rawPrefix source).prod source) source
  rw [houtputEq] at hraw
  exact hraw

/-- The selected trip length retained in a stopped arrival/mark history. -/
noncomputable def firstAcceptedArrivalHistoryTripLength :
    (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) -> TripLength :=
  fun history => history.1.1.1.2

/-- The selected trip-length coordinate of the stopped history is measurable. -/
theorem measurable_firstAcceptedArrivalHistoryTripLength :
    Measurable firstAcceptedArrivalHistoryTripLength := by
  exact measurable_snd.comp
    (measurable_fst.comp (measurable_fst.comp measurable_fst))

/-- The literal calendar completion time encoded by a stopped accepted-arrival
history: the elapsed time of the accepted request plus its selected trip
duration.  Keeping this as a history functional makes explicit that the
second shift is made at the actual calendar completion, rather than merely at
the selected duration measured from the beginning of the source path. -/
noncomputable def firstAcceptedArrivalHistoryCalendarCompletionTime :
    (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) -> Real :=
  fun history => history.1.2 + firstAcceptedArrivalHistoryTripLength history

/-- Measurability of the calendar completion time carried by the stopped
accepted-arrival history. -/
theorem measurable_firstAcceptedArrivalHistoryCalendarCompletionTime :
    Measurable firstAcceptedArrivalHistoryCalendarCompletionTime := by
  exact (measurable_snd.comp measurable_fst).add
    measurable_firstAcceptedArrivalHistoryTripLength

/-- The same stopped history on the literal GN raw seed. -/
noncomputable def gn21RawFirstAcceptedArrivalHistory
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) × (Nat -> Real) :=
  fun seed => firstAcceptedArrivalHistoryOfStreams sigma
    (rawTripMarkStream state seed, rawClockStream clock seed)

/-- Measurability of the literal raw stopped arrival/mark history. -/
theorem measurable_gn21RawFirstAcceptedArrivalHistory
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawFirstAcceptedArrivalHistory clock state sigma) := by
  exact (measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma).comp
    ((measurable_rawTripMarkStream state).prodMk (measurable_rawClockStream clock))

/-- On the raw GN seed, the selected history coordinate is the literal first
accepted trip mark. -/
theorem firstAcceptedArrivalHistoryTripLength_gn21RawFirstAcceptedArrivalHistory
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    firstAcceptedArrivalHistoryTripLength
      (gn21RawFirstAcceptedArrivalHistory clock state sigma seed) =
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
  rfl

/-- On the literal GN source, the calendar completion coordinate of the
stopped history is exactly the accepted request's arrival time plus its
selected duration. -/
theorem firstAcceptedArrivalHistoryCalendarCompletionTime_gn21RawFirstAcceptedArrivalHistory
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    firstAcceptedArrivalHistoryCalendarCompletionTime
      (gn21RawFirstAcceptedArrivalHistory clock state sigma seed) =
      gn21RawFirstAcceptedArrivalTime clock state sigma seed +
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed := by
  rfl

/-- The literal raw mark stream and literal raw request-clock stream have the
source product law, with their order chosen for an external mark-selected
clock-tail argument. -/
theorem rawTripMarkStream_rawClockStream_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) :
    HasLaw (fun seed : GN21RawCycleSeed =>
      (rawTripMarkStream state seed, rawClockStream clock seed))
      ((AppliedModelingLib.Probability.IIDStream.measure
        (gn21CycleMarkLaw muI muJ state)).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let E := ProbabilityTheory.expMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hrate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure M) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure E) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hraw := gn21RawCycleClockStream_markStream_hasLaw_prod
    muI muJ arrivalI arrivalJ switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
    clock state
  have hswap : HasLaw (Prod.swap : (Nat -> Real) × (Nat -> TripLength) ->
      (Nat -> TripLength) × (Nat -> Real))
      ((AppliedModelingLib.Probability.IIDStream.measure M).prod
        (AppliedModelingLib.Probability.IIDStream.measure E))
      ((AppliedModelingLib.Probability.IIDStream.measure E).prod
        (AppliedModelingLib.Probability.IIDStream.measure M)) := by
    simpa [AppliedModelingLib.Probability.IIDStream.measure] using
      (Measure.measurePreserving_swap
        (μ := AppliedModelingLib.Probability.IIDStream.measure E)
        (ν := AppliedModelingLib.Probability.IIDStream.measure M)).hasLaw
  simpa [P, M, E, rawTripMarkStream, rawClockStream,
    AppliedModelingLib.Probability.IIDStream.measure,
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
    hswap.comp hraw

/-- The complete raw marked history through the first accepted request factors
from the complete arrival-clock tail after that request.  The index is chosen
by the actual mark stream, and the tail starts after the accepted request's
own interarrival gap; this is a stopped-source factorization rather than an
independent post-thinning input. -/
theorem gn21RawFirstAcceptedMarkHistory_postArrivalGapTail_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw
      (fun seed =>
        (((AcceptedTripSelection.gn21RawFirstAcceptedIndex state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed),
          AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed),
          gn21RawPostFirstAcceptedArrivalGapTail clock state sigma seed))
      ((Measure.map (fun marks : Nat -> TripLength =>
          ((AcceptedTripSelection.firstAcceptedIndex sigma marks,
            AcceptedTripSelection.firstAcceptedTripMark sigma marks),
            AcceptedTripSelection.firstAcceptedTripTail sigma marks))
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let E := ProbabilityTheory.expMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
  let I := AppliedModelingLib.Probability.IIDStream.measure M
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let index : (Nat -> TripLength) -> Nat := fun marks =>
    AcceptedTripSelection.firstAcceptedIndex sigma marks + 1
  let stopped : (Nat -> TripLength) ->
      ((Nat × TripLength) × (Nat -> TripLength)) := fun marks =>
    ((AcceptedTripSelection.firstAcceptedIndex sigma marks,
      AcceptedTripSelection.firstAcceptedTripMark sigma marks),
      AcceptedTripSelection.firstAcceptedTripTail sigma marks)
  have hrate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure I := by
    dsimp [I, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hinput : HasLaw (fun seed : GN21RawCycleSeed =>
      (rawTripMarkStream state seed, rawClockStream clock seed))
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) P := by
    letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure E) := by
      dsimp [AppliedModelingLib.Probability.IIDStream.measure]
      infer_instance
    simpa [I, P, M, E] using
      (rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state)
  have hindex : Measurable index := by
    exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).add_const 1
  have hstopped : Measurable stopped := by
    exact
      ((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma)).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma)
  have hgeneric :=
    AppliedModelingLib.Probability.IIDStream.externalIndexTail_joint_hasLaw
      I E index hindex stopped hstopped
  simpa [P, M, E, I, index, stopped, gn21RawPostFirstAcceptedArrivalGapTail,
    rawTripMarkStream, rawClockStream,
    AcceptedTripSelection.gn21RawFirstAcceptedIndex,
    AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
    AcceptedTripSelection.gn21RawFirstAcceptedTripTail,
    gn21RawCycleMark, AppliedModelingLib.Probability.IIDStream.measure,
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure,
    Function.comp_def] using hgeneric.comp hinput

/-- The raw history through the first accepted request, including the literal
elapsed arrival time of that request, factors from the remaining arrival-clock
tail.  The proof is event-level: on each mark-selected index fiber, the
elapsed time is a measurable sum of exactly the consumed gaps.  Thus this is
not an invocation of a continuous-time strong-Markov property. -/
theorem gn21RawFirstAcceptedArrivalHistory_postArrivalGapTail_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw
      (fun seed =>
        ((((AcceptedTripSelection.gn21RawFirstAcceptedIndex state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed),
          AcceptedTripSelection.gn21RawFirstAcceptedTripTail state sigma seed),
          gn21RawFirstAcceptedArrivalTime clock state sigma seed),
          gn21RawPostFirstAcceptedArrivalGapTail clock state sigma seed))
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
                (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))))).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let E := ProbabilityTheory.expMeasure
    (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)
  let I := AppliedModelingLib.Probability.IIDStream.measure M
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let index : (Nat -> TripLength) -> Nat := fun marks =>
    AcceptedTripSelection.firstAcceptedIndex sigma marks + 1
  let stopped : (Nat -> TripLength) ->
      ((Nat × TripLength) × (Nat -> TripLength)) := fun marks =>
    ((AcceptedTripSelection.firstAcceptedIndex sigma marks,
      AcceptedTripSelection.firstAcceptedTripMark sigma marks),
      AcceptedTripSelection.firstAcceptedTripTail sigma marks)
  let f : ((Nat -> TripLength) × (Nat -> Real)) ->
      (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun z =>
    (stopped z.1,
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2)
  let prefixValue : ∀ n : Nat,
      (Nat -> TripLength) × (Finset.range n -> Real) ->
        (((Nat × TripLength) × (Nat -> TripLength)) × Real) := fun n z =>
    (stopped z.1, ∑ i ∈ (Finset.range n).attach, z.2 i)
  have hrate : 0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
    fin_cases clock <;> simp [gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure I := by
    dsimp [I, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure E) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hinput : HasLaw (fun seed : GN21RawCycleSeed =>
      (rawTripMarkStream state seed, rawClockStream clock seed))
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) P := by
    simpa [I, P, M, E] using
      (rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state)
  have hindex : Measurable index := by
    exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).add_const 1
  have hstopped : Measurable stopped := by
    exact
      ((AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma)).prodMk
        (AcceptedTripSelection.measurable_firstAcceptedTripTail sigma hsigma)
  have harrival : Measurable (fun z : (Nat -> TripLength) × (Nat -> Real) =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AcceptedTripSelection.firstAcceptedIndex sigma z.1) z.2) := by
    let K : (Nat -> TripLength) × (Nat -> Real) -> Nat := fun z =>
      AcceptedTripSelection.firstAcceptedIndex sigma z.1
    have hK : Measurable K := by
      exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp measurable_fst
    have hKevent : ∀ n, MeasurableSet {z | K z = n} := by
      intro n
      simpa only [Set.preimage_setOf_eq] using hK (measurableSet_singleton n)
    let h : ∀ z : (Nat -> TripLength) × (Nat -> Real), ∃ n, K z = n :=
      fun z => ⟨K z, rfl⟩
    have hmeas : Measurable (fun z : (Nat -> TripLength) × (Nat -> Real) =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime (Nat.find (h z)) z.2) :=
      Measurable.find
        (fun n =>
          (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
            measurable_snd)
        hKevent h
    convert hmeas using 1
    funext z
    have hfind : Nat.find (h z) = K z := (Nat.find_spec (h z)).symm
    simp [K, hfind]
  have hf : Measurable f := by
    exact (hstopped.comp measurable_fst).prodMk harrival
  have hprefixValue : ∀ n, Measurable (prefixValue n) := by
    intro n
    apply (hstopped.comp measurable_fst).prodMk
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).comp measurable_snd
  have hfactor : ∀ z, f z =
      prefixValue (index z.1)
        (AppliedModelingLib.Probability.IIDStream.stateInitialPrefix (index z.1) z) := by
    intro z
    apply Prod.ext
    · rfl
    · simp [f, prefixValue, index,
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime,
        AppliedModelingLib.Probability.PoissonProcess.interarrival,
        AppliedModelingLib.Probability.IIDStream.stateInitialPrefix,
        AppliedModelingLib.Probability.IIDStream.coordinate, Finset.sum_attach]
  have hindep : IndepFun f
      (AppliedModelingLib.Probability.IIDStream.externalIndexTail index)
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) := by
    apply AppliedModelingLib.Probability.IIDStream.indepFun_of_externalIndexPrefixEvent_tail
      I E index hindex f
    intro S hS
    exact AppliedModelingLib.Probability.IIDStream.externalIndexPrefixEvent_preimage_of_initialPrefixFactor
      index prefixValue hprefixValue f hfactor S hS
  have hfirstLaw : HasLaw f
      (Measure.map f (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)))
      (I.prod (AppliedModelingLib.Probability.IIDStream.measure E)) := by
    exact ⟨hf.aemeasurable, rfl⟩
  have htailLaw :=
    AppliedModelingLib.Probability.IIDStream.externalIndexTail_hasLaw I E index hindex
  have hjoint := AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
    hfirstLaw htailLaw hindep
  simpa [P, M, E, I, index, stopped, f, gn21RawFirstAcceptedArrivalTime,
    gn21RawPostFirstAcceptedArrivalGapTail, rawTripMarkStream, rawClockStream,
    AcceptedTripSelection.gn21RawFirstAcceptedIndex,
    AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
    AcceptedTripSelection.gn21RawFirstAcceptedTripTail, gn21RawCycleMark,
    AppliedModelingLib.Probability.IIDStream.measure,
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure,
    AppliedModelingLib.Probability.IIDStream.externalIndexTail,
    AppliedModelingLib.Probability.IIDStream.coordinate, Function.comp_def] using
    hjoint.comp hinput

/-- At a fixed raw-clock horizon, the accepted-count is zero exactly when
every actual raw request before that horizon is rejected. -/
theorem rawAcceptedRequestCount_eq_zero_iff
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (t : Real) (seed : GN21RawCycleSeed) :
    gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
      ∀ i : Fin (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t
        (seed.1 clock)), rawTripMarkStream state seed i ∉ sigma := by
  classical
  unfold gn21RawAcceptedRequestCount gn21RawFiniteHorizonMarkedSample
  unfold AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.kept
    AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.keptInMarks
  rw [Finset.card_eq_zero]
  rw [AppliedModelingLib.successIndexSet_eq_iff]
  simp [rawTripMarkStream, gn21AcceptanceMark]

private theorem rawClockRate_pos
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
  fin_cases clock <;>
    simp [gn21CycleClockRate, harrivalI, harrivalJ, hswitchIJ, hswitchJI]

private theorem measurableSet_exists_accepted
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet {marks : Nat -> TripLength | ∃ n, marks n ∈ sigma} := by
  rw [show {marks : Nat -> TripLength | ∃ n, marks n ∈ sigma} =
      ⋃ n, {marks | marks n ∈ sigma} by
        ext marks
        simp]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_pi_apply n) hsigma

/-- Positive accepted source mass makes the literal raw GN21 mark stream
contain an accepted trip almost surely. -/
theorem ae_rawTripMarkStream_exists_accepted
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∃ n, rawTripMarkStream state seed n ∈ sigma := by
  let M := gn21CycleMarkLaw muI muJ state
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hsource : ∀ᵐ marks ∂IIDStream.measure M, ∃ n, marks n ∈ sigma :=
    AcceptedTripSelection.ae_exists_accepted M sigma hsigma (by simpa [M] using hmass)
  have hraw := gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state
  have hsource_map : ∀ᵐ marks ∂Measure.map (rawTripMarkStream state)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∃ n, marks n ∈ sigma := by
    change ∀ᵐ marks ∂Measure.map (fun seed : GN21RawCycleSeed => seed.2 state)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∃ n, marks n ∈ sigma
    rw [hraw.map_eq]
    simpa [rawTripMarkStream, M] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    (measurableSet_exists_accepted sigma hsigma)).mp hsource_map
  simpa [rawTripMarkStream] using hpull

private theorem measurableSet_all_nonnegative_rawClock :
    MeasurableSet {clockPath : Nat -> Real | ∀ n, 0 ≤ clockPath n} := by
  rw [show {clockPath : Nat -> Real | ∀ n, 0 ≤ clockPath n} =
      ⋂ n, {clockPath | 0 ≤ clockPath n} by
        ext clockPath
        simp]
  apply MeasurableSet.iInter
  intro n
  exact (measurable_pi_apply n) measurableSet_Ici

/-- The literal raw GN21 clock path has nonnegative gaps almost surely. -/
theorem ae_rawClockStream_nonnegative
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ n, 0 ≤ rawClockStream clock seed n := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ clockPath
      ∂AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate,
      ∀ n, 0 ≤ clockPath n :=
    (AppliedModelingLib.Probability.PoissonProcess.ae_all_interarrival_positive hrate).mono
      (fun _ hpos n => (hpos n).le)
  have hraw := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource_map : ∀ᵐ clockPath ∂Measure.map (rawClockStream clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, 0 ≤ clockPath n := by
    change ∀ᵐ clockPath ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, 0 ≤ clockPath n
    rw [hraw.map_eq]
    simpa [rawClockStream, rate] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    measurableSet_all_nonnegative_rawClock).mp hsource_map
  simpa [rawClockStream] using hpull

/-- The literal raw request-clock arrivals are nonexplosive.  This is
transported from the source exponential-interarrival law, so later randomized
clock arguments need not insert a renewal-process assumption. -/
theorem ae_rawClockStream_arrivalTime_tendsto_atTop
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (rawClockStream clock seed)) atTop atTop := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hraw := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ clockPath ∂Measure.map (rawClockStream clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath) atTop atTop := by
    change ∀ᵐ clockPath ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath) atTop atTop
    rw [hraw.map_eq]
    simpa [rate] using
      AppliedModelingLib.Probability.PoissonProcess.ae_arrivalTime_tendsto_atTop hrate
  exact Measure.tendsto_ae_map hraw.aemeasurable hsource

/-- The literal raw request-clock arrival epochs are almost surely monotone. -/
theorem ae_rawClockStream_arrivalTime_monotone
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Monotone (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (rawClockStream clock seed)) := by
  filter_upwards [ae_rawClockStream_nonnegative muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock] with seed hnonneg
  exact AppliedModelingLib.Probability.PoissonProcess.arrivalTime_mono_of_nonnegative
    (rawClockStream clock seed) hnonneg

private theorem measurableSet_rawClock_count_threshold (t : Real) :
    MeasurableSet {clockPath : Nat -> Real |
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} := by
  rw [show {clockPath : Nat -> Real |
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} =
      ⋂ n, {clockPath |
        n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} by
        ext clockPath
        simp]
  apply MeasurableSet.iInter
  intro n
  exact
    (measurableSet_lt measurable_const
      (AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount t)).iff
      (measurableSet_le
        (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n)
        measurable_const)

/-- The raw clock's count/arrival threshold relation holds almost surely at
every request index for a fixed calendar time. -/
theorem ae_rawClock_count_threshold
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t
        (rawClockStream clock seed) ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (rawClockStream clock seed) ≤ t := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ clockPath
      ∂AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate,
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t :=
    (AppliedModelingLib.Probability.PoissonProcess.ae_lt_canonicalRenewalCount_iff_arrivalTime_le
      hrate).mono (fun _ hthreshold n => hthreshold t n)
  have hraw := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource_map : ∀ᵐ clockPath ∂Measure.map (rawClockStream clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t := by
    change ∀ᵐ clockPath ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t
    rw [hraw.map_eq]
    simpa [rawClockStream, rate] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    (measurableSet_rawClock_count_threshold t)).mp hsource_map
  simpa [rawClockStream] using hpull

/-- On a path with an accepted raw mark and a nonexplosive monotone request
clock, the first accepted-arrival time exceeds `t` exactly when the raw
accepted-request count through `t` is zero. -/
theorem rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (t : Real)
    (seed : GN21RawCycleSeed)
    (haccepted : ∃ n, gn21RawCycleMark state n seed ∈ sigma)
    (hgap : ∀ n, 0 ≤ gn21RawCycleClock clock n seed)
    (hthreshold : ∀ n,
      n < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock) ↔
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n (seed.1 clock) ≤ t) :
    gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
      t < gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  classical
  let marks : Nat -> TripLength := fun n => gn21RawCycleMark state n seed
  let index : Nat := AcceptedTripSelection.firstAcceptedIndex sigma marks
  let h : ∃ n, marks n ∈ sigma := by simpa [marks] using haccepted
  have hfirst : marks ∈ AcceptedTripSelection.firstAcceptedEvent sigma (Nat.find h) := by
    rw [AcceptedTripSelection.mem_firstAcceptedEvent_iff]
    refine ⟨Nat.find_spec h, ?_⟩
    intro m hm
    exact Nat.find_min h hm
  have hindex : index = Nat.find h := by
    exact AcceptedTripSelection.firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst
  have hindex_accepted : marks index ∈ sigma := by
    rw [hindex]
    exact (AcceptedTripSelection.mem_firstAcceptedEvent_iff sigma marks (Nat.find h)).mp
      hfirst |>.1
  have hindex_noearlier : ∀ m < index, marks m ∉ sigma := by
    intro m hm
    rw [hindex] at hm
    exact (AcceptedTripSelection.mem_firstAcceptedEvent_iff sigma marks (Nat.find h)).mp
      hfirst |>.2 m hm
  have hclock_nonnegative : ∀ n, 0 ≤ (seed.1 clock) n := by
    intro n
    simpa [gn21RawCycleClock] using hgap n
  have hclock_mono : Monotone (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n (seed.1 clock)) :=
    AppliedModelingLib.Probability.PoissonProcess.arrivalTime_mono_of_nonnegative
      (seed.1 clock) hclock_nonnegative
  change gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
    t < AppliedModelingLib.Probability.PoissonProcess.arrivalTime index (seed.1 clock)
  constructor
  · intro hzero
    by_contra hnot
    have htime_le : AppliedModelingLib.Probability.PoissonProcess.arrivalTime index (seed.1 clock) ≤ t :=
      le_of_not_gt hnot
    have hindex_lt : index <
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock) :=
      (hthreshold index).mpr htime_le
    have hreject := (rawAcceptedRequestCount_eq_zero_iff clock state sigma t seed).mp hzero
    exact hreject ⟨index, hindex_lt⟩ (by simpa [marks] using hindex_accepted)
  · intro htime
    refine (rawAcceptedRequestCount_eq_zero_iff clock state sigma t seed).mpr ?_
    intro i himem
    have hindex_le : index ≤ (i : Nat) := by
      by_contra hnot
      have hlt : (i : Nat) < index := Nat.lt_of_not_ge hnot
      exact (hindex_noearlier (i : Nat) hlt) (by simpa [marks] using himem)
    have hi_time : AppliedModelingLib.Probability.PoissonProcess.arrivalTime (i : Nat)
        (seed.1 clock) ≤ t :=
      (hthreshold (i : Nat)).mp i.isLt
    have htime_le : AppliedModelingLib.Probability.PoissonProcess.arrivalTime index
        (seed.1 clock) ≤ t :=
      (hclock_mono hindex_le).trans hi_time
    exact (not_le_of_gt htime) htime_le

/-- At each fixed calendar time, the zero retained-count event and the tail
event of the literal first accepted-arrival time agree almost surely. -/
theorem ae_rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
        t < gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  have haccepted := ae_rawTripMarkStream_exists_accepted
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hgap := ae_rawClockStream_nonnegative muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthreshold := ae_rawClock_count_threshold muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock t
  filter_upwards [haccepted, hgap, hthreshold] with seed haccepted hgap hthreshold
  apply rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    clock state sigma t seed
  · simpa [rawTripMarkStream] using haccepted
  · simpa [rawClockStream] using hgap
  · simpa [rawClockStream] using hthreshold

/-- The literal first accepted-arrival time is nonnegative almost surely under
the raw positive-rate clock model. -/
theorem ae_gn21RawFirstAcceptedArrivalTime_nonnegative
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      0 ≤ gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  have hgap := ae_rawClockStream_nonnegative muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  filter_upwards [hgap] with seed hgap
  change 0 ≤ AppliedModelingLib.Probability.PoissonProcess.arrivalTime
    (AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed))
    (rawClockStream clock seed)
  exact AppliedModelingLib.Probability.PoissonProcess.arrivalTime_nonnegative_of_interarrival_nonnegative
    (rawClockStream clock seed) hgap _

/-- The literal first accepted-arrival observable has the exponential survival
probability at every nonnegative deterministic time.  This is obtained from
the actual finite-horizon accepted-count law, not from a separately supplied
thinned clock. -/
theorem gn21RawFirstAcceptedArrivalTime_tail_real
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (t : Real) (ht : 0 ≤ t) :
    (Measure.map (gn21RawFirstAcceptedArrivalTime clock state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)).real
        (Set.Ioi t) =
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).real (Set.Ioi t) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let thinnedRate := rate * singleStateTripMass M sigma
  let mean : ℝ≥0 := NNReal.mk (rate * t) (mul_nonneg
    (rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI clock).le ht) *
    gn21AcceptanceProbability M sigma
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthinnedRate : 0 < thinnedRate := by
    exact mul_pos hrate (by simpa [M] using hmass)
  have htail_event := ae_rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass t
  have htail_set :
      (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) =ᵐ[P]
        {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} := by
    filter_upwards [htail_event] with seed hseed
    simpa [Set.mem_preimage] using hseed.symm
  have htail_measure :
      P.real (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) =
        P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} := by
    simpa [Measure.real] using congrArg ENNReal.toReal (MeasureTheory.measure_congr htail_set)
  have hcount_law : HasLaw (gn21RawAcceptedRequestCount clock state sigma t)
      (ProbabilityTheory.poissonMeasure mean) P := by
    simpa [P, M, rate, mean] using
      (gn21RawAcceptedRequestCount_hasLaw_poisson_of_sourceMass
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma t ht)
  have hcount_zero :
      P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} =
        (ProbabilityTheory.poissonMeasure mean).real {0} := by
    change (P (gn21RawAcceptedRequestCount clock state sigma t ⁻¹'
      ({0} : Set Nat))).toReal =
        (ProbabilityTheory.poissonMeasure mean).real {0}
    rw [← Measure.map_apply_of_aemeasurable hcount_law.aemeasurable
      (measurableSet_singleton 0)]
    change (P.map (gn21RawAcceptedRequestCount clock state sigma t)).real {0} = _
    rw [hcount_law.map_eq]
  have hmean : (mean : Real) = thinnedRate * t := by
    dsimp [mean, thinnedRate]
    rw [gn21AcceptanceProbability_toReal_eq_singleStateTripMass]
    ring
  let E : AppliedModelingLib.Probability.Exponential.Model := ⟨thinnedRate, hthinnedRate⟩
  have hexp_tail :
      (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi t) =
        Real.exp (-(thinnedRate * t)) := by
    simpa [E, AppliedModelingLib.Probability.Exponential.Model.measure] using
      E.measure_Ioi_toReal ht
  calc
    (Measure.map (gn21RawFirstAcceptedArrivalTime clock state sigma) P).real (Set.Ioi t) =
        P.real (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) := by
          rw [MeasureTheory.map_measureReal_apply
            (measurable_gn21RawFirstAcceptedArrivalTime clock state sigma hsigma)
            measurableSet_Ioi]
    _ = P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} :=
      htail_measure
    _ = (ProbabilityTheory.poissonMeasure mean).real {0} := hcount_zero
    _ = Real.exp (-(thinnedRate * t)) := by
      rw [ProbabilityTheory.poissonMeasure_real_singleton]
      simp [hmean]
    _ = (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi t) := hexp_tail.symm
    _ = (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).real (Set.Ioi t) := by
      simp [thinnedRate, rate, M]

/-- The first accepted request in the literal GN21 raw marked-Poisson seed
arrives at an exponential time with the source-thinned rate. -/
theorem gn21RawFirstAcceptedArrivalTime_hasLaw_expMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawFirstAcceptedArrivalTime clock state sigma)
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let thinnedRate := rate * singleStateTripMass M sigma
  let T := gn21RawFirstAcceptedArrivalTime clock state sigma
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthinnedRate : 0 < thinnedRate := by
    exact mul_pos hrate (by simpa [M] using hmass)
  have hTmeas : Measurable T := by
    simpa [T] using measurable_gn21RawFirstAcceptedArrivalTime clock state sigma hsigma
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (P.map T) :=
    Measure.isProbabilityMeasure_map hTmeas.aemeasurable
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure thinnedRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hthinnedRate
  change HasLaw T (ProbabilityTheory.expMeasure thinnedRate) P
  refine ⟨hTmeas.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro x
  apply (MeasureTheory.measureReal_eq_measureReal_iff).mp
  by_cases hx : 0 ≤ x
  · have htail :
        (P.map T).real (Set.Ioi x) =
          (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi x) := by
      simpa [P, M, rate, thinnedRate, T] using
        (gn21RawFirstAcceptedArrivalTime_tail_real
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass x hx)
    have hcomp : (Set.Iic x)ᶜ = Set.Ioi x := by
      ext y
      simp
    have hleft := MeasureTheory.probReal_add_probReal_compl
      (μ := P.map T) (s := Set.Iic x) measurableSet_Iic
    have hright := MeasureTheory.probReal_add_probReal_compl
      (μ := ProbabilityTheory.expMeasure thinnedRate) (s := Set.Iic x)
      measurableSet_Iic
    rw [hcomp] at hleft hright
    linarith
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hTnonneg : ∀ᵐ seed ∂P, 0 ≤ T seed := by
      simpa [P, T] using
        (ae_gn21RawFirstAcceptedArrivalTime_nonnegative
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma)
    have hnotmem : ∀ᵐ seed ∂P, seed ∉ T ⁻¹' Set.Iic x := by
      filter_upwards [hTnonneg] with seed hnonneg hmem
      change T seed ≤ x at hmem
      linarith
    have hzero : P (T ⁻¹' Set.Iic x) = 0 :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr hnotmem
    have hleft : (P.map T).real (Set.Iic x) = 0 := by
      rw [MeasureTheory.map_measureReal_apply hTmeas measurableSet_Iic]
      simp [Measure.real, hzero]
    have hright : (ProbabilityTheory.expMeasure thinnedRate).real (Set.Iic x) = 0 := by
      rw [← ProbabilityTheory.cdf_eq_real,
        ProbabilityTheory.cdf_expMeasure_eq hthinnedRate x, if_neg hx]
    exact hleft.trans hright.symm

private theorem measurable_arrivalFromClockBundleIndex
    (clock : Fin 4) :
    Measurable (fun z : (Fin 4 -> Nat -> Real) × Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime z.2 (z.1 clock)) := by
  let index : (Fin 4 -> Nat -> Real) × Nat -> Nat := Prod.snd
  let h : ∀ z : (Fin 4 -> Nat -> Real) × Nat, ∃ n, index z = n :=
    fun z => ⟨index z, rfl⟩
  have hindex_event : ∀ n, MeasurableSet {z | index z = n} := by
    intro n
    simpa only [Set.preimage_setOf_eq] using
      (measurable_snd (measurableSet_singleton n))
  have hmeas := Measurable.find
    (fun n =>
      (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
        ((measurable_pi_apply clock).comp measurable_fst))
    hindex_event h
  convert hmeas using 1
  funext z
  have hfind : Nat.find (h z) = index z := (Nat.find_spec (h z)).symm
  simp [index, hfind]

/-- On the literal GN21 raw product seed, the elapsed time to the first
accepted request is independent of the conditional trip mark selected at that
request. The proof factors the raw clock bundle from the full marked stream
and then uses the stopped index/mark factorization; it supplies neither
independence nor a post-thinning renewal law as an assumption. -/
theorem indepFun_gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ProbabilityTheory.IndepFun (gn21RawFirstAcceptedArrivalTime clock state sigma)
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
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rawStream : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength :=
    Function.eval state
  let index : (Fin 2 -> Nat -> TripLength) -> Nat :=
    fun marks => AcceptedTripSelection.firstAcceptedIndex sigma (rawStream marks)
  let mark : (Fin 2 -> Nat -> TripLength) -> TripLength :=
    fun marks => AcceptedTripSelection.firstAcceptedTripMark sigma (rawStream marks)
  let pairPB : (Fin 2 -> Nat -> TripLength) -> Nat × TripLength :=
    fun marks => (index marks, mark marks)
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
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure M) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hrawMeas : Measurable rawStream := by
    simpa [rawStream] using (measurable_pi_apply state :
      Measurable (Function.eval state :
        (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength))
  have hindexPath : Measurable (AcceptedTripSelection.firstAcceptedIndex sigma) := by
    exact AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma
  have hmarkPath : Measurable (AcceptedTripSelection.firstAcceptedTripMark sigma) := by
    exact AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma
  have hindex : Measurable index := hindexPath.comp hrawMeas
  have hmark : Measurable mark := hmarkPath.comp hrawMeas
  have hstream : HasLaw rawStream (IIDStream.measure M) markMeasure := by
    simpa [rawStream, M, IIDStream.measure] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s) state).hasLaw
  have hselected : ProbabilityTheory.IndepFun
      (AcceptedTripSelection.firstAcceptedIndex sigma)
      (AcceptedTripSelection.firstAcceptedTripMark sigma) (IIDStream.measure M) := by
    exact AcceptedTripSelection.indepFun_firstAcceptedIndex_firstAcceptedTripMark
      M sigma hsigma (by simpa [M] using hmass)
  have hpairIID : (IIDStream.measure M).map
      (fun marks => (AcceptedTripSelection.firstAcceptedIndex sigma marks,
        AcceptedTripSelection.firstAcceptedTripMark sigma marks)) =
      ((IIDStream.measure M).map (AcceptedTripSelection.firstAcceptedIndex sigma)).prod
        ((IIDStream.measure M).map (AcceptedTripSelection.firstAcceptedTripMark sigma)) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hindexPath.aemeasurable hmarkPath.aemeasurable).mp hselected
  have hpairPB : markMeasure.map pairPB =
      (markMeasure.map index).prod (markMeasure.map mark) := by
    calc
      markMeasure.map pairPB = (markMeasure.map rawStream).map
          (fun marks => (AcceptedTripSelection.firstAcceptedIndex sigma marks,
            AcceptedTripSelection.firstAcceptedTripMark sigma marks)) := by
        rw [Measure.map_map (hindexPath.prodMk hmarkPath) hrawMeas]
        rfl
      _ = (IIDStream.measure M).map
          (fun marks => (AcceptedTripSelection.firstAcceptedIndex sigma marks,
            AcceptedTripSelection.firstAcceptedTripMark sigma marks)) := by
        rw [hstream.map_eq]
      _ = ((IIDStream.measure M).map (AcceptedTripSelection.firstAcceptedIndex sigma)).prod
          ((IIDStream.measure M).map (AcceptedTripSelection.firstAcceptedTripMark sigma)) :=
        hpairIID
      _ = ((markMeasure.map rawStream).map
          (AcceptedTripSelection.firstAcceptedIndex sigma)).prod
          ((markMeasure.map rawStream).map
            (AcceptedTripSelection.firstAcceptedTripMark sigma)) := by
        rw [hstream.map_eq]
      _ = (markMeasure.map index).prod (markMeasure.map mark) := by
        rw [Measure.map_map hindexPath hrawMeas,
          Measure.map_map hmarkPath hrawMeas]
        rfl
  let X : (Fin 4 -> Nat -> Real) × (Fin 2 -> Nat -> TripLength) ->
      (Fin 4 -> Nat -> Real) × Nat := fun z => (z.1, index z.2)
  let Y : (Fin 4 -> Nat -> Real) × (Fin 2 -> Nat -> TripLength) -> TripLength :=
    fun z => mark z.2
  have hX : (clockMeasure.prod markMeasure).map X =
      clockMeasure.prod (markMeasure.map index) := by
    simpa [X] using
      (Measure.map_prod_map clockMeasure markMeasure measurable_id hindex).symm
  have hY : (clockMeasure.prod markMeasure).map Y = markMeasure.map mark := by
    calc
      (clockMeasure.prod markMeasure).map Y =
          (clockMeasure.prod markMeasure).map (mark ∘ Prod.snd) := by rfl
      _ = ((clockMeasure.prod markMeasure).map Prod.snd).map mark := by
        rw [Measure.map_map hmark measurable_snd]
      _ = markMeasure.map mark := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hvector : ProbabilityTheory.IndepFun X Y (clockMeasure.prod markMeasure) := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((measurable_fst.prodMk (hindex.comp measurable_snd)).aemeasurable)
      (hmark.comp measurable_snd).aemeasurable).mpr
    calc
      (clockMeasure.prod markMeasure).map (fun z => (X z, Y z)) =
          ((clockMeasure.prod markMeasure).map (Prod.map id pairPB)).map
            (MeasurableEquiv.prodAssoc.symm :
              (Fin 4 -> Nat -> Real) × (Nat × TripLength) ->
                ((Fin 4 -> Nat -> Real) × Nat) × TripLength) := by
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap (hindex.prodMk hmark))]
          rfl
      _ = (clockMeasure.prod (markMeasure.map pairPB)).map
          (MeasurableEquiv.prodAssoc.symm :
            (Fin 4 -> Nat -> Real) × (Nat × TripLength) ->
              ((Fin 4 -> Nat -> Real) × Nat) × TripLength) := by
          rw [← Measure.map_prod_map clockMeasure markMeasure measurable_id
            (hindex.prodMk hmark)]
          rw [Measure.map_id]
      _ = (clockMeasure.prod ((markMeasure.map index).prod (markMeasure.map mark))).map
          (MeasurableEquiv.prodAssoc.symm :
            (Fin 4 -> Nat -> Real) × (Nat × TripLength) ->
              ((Fin 4 -> Nat -> Real) × Nat) × TripLength) := by
          rw [hpairPB]
      _ = (clockMeasure.prod (markMeasure.map index)).prod (markMeasure.map mark) := by
          exact (measurePreserving_prodAssoc clockMeasure (markMeasure.map index)
            (markMeasure.map mark)).symm.map_eq
      _ = ((clockMeasure.prod markMeasure).map X).prod
          ((clockMeasure.prod markMeasure).map Y) := by
          rw [hX, hY]
  let arrivalFrom : (Fin 4 -> Nat -> Real) × Nat -> Real := fun z =>
    AppliedModelingLib.Probability.PoissonProcess.arrivalTime z.2 (z.1 clock)
  have harrivalFrom : Measurable arrivalFrom := by
    simpa [arrivalFrom] using measurable_arrivalFromClockBundleIndex clock
  have hfinal := hvector.comp harrivalFrom measurable_id
  change ProbabilityTheory.IndepFun
    (gn21RawFirstAcceptedArrivalTime clock state sigma)
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma) P
  simpa [P, X, Y, arrivalFrom, index, mark, rawStream,
    gn21RawFirstAcceptedArrivalTime, rawTripMarkStream,
    AcceptedTripSelection.gn21RawFirstAcceptedTripMark,
    gn21RawCycleMark, Function.comp_def] using hfinal

/-- The literal first accepted-arrival delay and literal selected accepted
trip mark have the exact product of the thinned exponential and conditional
mark laws. This packages source-derived marginals and factorization, rather
than accepting a post-thinning pair as an input. -/
theorem gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (fun seed =>
      (gn21RawFirstAcceptedArrivalTime clock state sigma seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
      ((ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).prod
        (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let T := gn21RawFirstAcceptedArrivalTime clock state sigma
  let selected := AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have htime : HasLaw T
      (ProbabilityTheory.expMeasure (rate * singleStateTripMass M sigma)) P := by
    simpa [T, rate, M, P] using
      (gn21RawFirstAcceptedArrivalTime_hasLaw_expMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass)
  have hselected : HasLaw selected (gn21AcceptedTripLaw M sigma) P := by
    simpa [selected, M, P] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hindep : ProbabilityTheory.IndepFun T selected P := by
    simpa [T, selected, P] using
      (indepFun_gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass)
  simpa [T, selected, rate, M, P] using
    (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk htime hselected hindep)

/-- The source two-state CTMC's opposite-state transition probability,
evaluated at the literal selected accepted-trip duration, has exactly the
conditional-mark expectation used in the paper's cross-subcycle term. This
is transport through the actual stopped mark, not a separately supplied trip
duration. -/
theorem integral_gn21SwitchProb_gn21RawFirstAcceptedTripMark_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (∫ seed, gn21SwitchProb switchIJ switchJI
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∫ tau in sigma, gn21SwitchProb switchIJ switchJI tau
        ∂gn21CycleMarkLaw muI muJ state) /
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let selected := AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  have hselected : HasLaw selected (gn21AcceptedTripLaw M sigma) P := by
    simpa [selected, M, P] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  calc
    (∫ seed, gn21SwitchProb switchIJ switchJI (selected seed) ∂P) =
        ∫ tau, gn21SwitchProb switchIJ switchJI tau ∂gn21AcceptedTripLaw M sigma := by
          simpa [Function.comp_def] using hselected.integral_comp
            (continuous_gn21SwitchProb switchIJ switchJI).aestronglyMeasurable
    _ = (∫ tau in sigma, gn21SwitchProb switchIJ switchJI tau ∂M) /
        singleStateTripMass M sigma := by
          exact gn21AcceptedTripLaw_integral_switchProb M sigma switchIJ switchJI hmass
    _ = (∫ tau in sigma, gn21SwitchProb switchIJ switchJI tau
        ∂gn21CycleMarkLaw muI muJ state) /
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
          rfl


end AcceptedArrivalTime

end

end GN21DriverSurgePricing
