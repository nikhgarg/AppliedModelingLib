import GN21DriverSurgePricing.RenewalCycleSourceBridge
import GN21DriverSurgePricing.RawTwoStateCTMC
import AppliedModelingLib.Foundations.Probability.ExponentialRaceMinimum
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalExternalTimeMarkedResidualTail

/-!
# Literal post-thinning race bridge for GN21

This downstream bridge identifies the paper's three-coordinate post-thinning
race seed with literal observables of the GN21 raw product seed.  It is kept
downstream of both source components to avoid making either construction
circular.  The result is an input-law transport only: stopped source tails
and post-completion regeneration remain separate obligations.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Location of the literal raw request clock associated with each open state.
Together with `RawTwoStateCTMC.switchClockIndex`, this identifies the two
distinct source clock streams used by a state-specific competing race. -/
def gn21ArrivalClockIndex : Fin 2 -> Fin 4
  | 0 => 0
  | 1 => 1

/-- The first post-thinning competing-race inputs as observables of the
literal raw GN21 seed: the first accepted request delay, the active switch
delay, and the selected conditional trip mark. -/
def gn21RawPostThinningRaceSeed (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21PostThinningRaceSeed :=
  fun seed =>
    (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime (gn21ArrivalClockIndex state)
      state sigma seed,
    (gn21RawCycleClock (RawTwoStateCTMC.switchClockIndex state) 0 seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))

theorem measurable_gn21RawPostThinningRaceSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceSeed state sigma) := by
  exact
    (AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalTime
      (gn21ArrivalClockIndex state) state sigma hsigma).prodMk
    (((measurable_pi_apply 0).comp
      (AcceptedArrivalTime.measurable_rawClockStream
        (RawTwoStateCTMC.switchClockIndex state))).prodMk
      ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)))

/-- The literal first accepted-arrival delay, currently active switching gap,
and selected accepted mark have exactly the product law of the paper's
post-thinning race seed.  This is an equality in law for actual raw-source
observables, obtained by retaining the complete independent clock and mark
tails until the final measurable transport.  It does not assert the stopped
tail or post-completion regeneration law. -/
theorem gn21RawPostThinningRaceSeed_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawPostThinningRaceSeed state sigma)
      (gn21PostThinningRaceSeedMeasure (gn21CycleMarkLaw muI muJ state)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state)) sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let arrClock := gn21ArrivalClockIndex state
  let switchClock := RawTwoStateCTMC.switchClockIndex state
  let S := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (clockRate switchClock)
  let A := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (clockRate arrClock)
  let M := Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state
  let E := ProbabilityTheory.expMeasure (clockRate switchClock)
  let T := ProbabilityTheory.expMeasure
    (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harr_rate : 0 < clockRate arrClock := by
    dsimp [clockRate, arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitch_rate : 0 < clockRate switchClock := by
    dsimp [clockRate, switchClock, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      hswitch_rate
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      harr_rate
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitch_rate
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure (mul_pos harr_rate hmass)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let firstPair : (Nat -> Real) × (Nat -> TripLength) -> Real × TripLength := fun z =>
    (AppliedModelingLib.Probability.PoissonProcess.arrivalTime
      (AcceptedTripSelection.firstAcceptedIndex sigma z.2) z.1,
    AcceptedTripSelection.firstAcceptedTripMark sigma z.2)
  have hfirstPair : Measurable firstPair := by
    let index : (Nat -> Real) × (Nat -> TripLength) -> Nat := fun z =>
      AcceptedTripSelection.firstAcceptedIndex sigma z.2
    have hindex : Measurable index :=
      (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp measurable_snd
    have hindex_event : ∀ n, MeasurableSet {z | index z = n} := by
      intro n
      simpa only [Set.preimage_setOf_eq] using hindex (measurableSet_singleton n)
    let h : ∀ z : (Nat -> Real) × (Nat -> TripLength), ∃ n, index z = n :=
      fun z => ⟨index z, rfl⟩
    have htime : Measurable (fun z : (Nat -> Real) × (Nat -> TripLength) =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime (Nat.find (h z)) z.1) :=
      Measurable.find
        (fun n => (AppliedModelingLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
          measurable_fst)
        hindex_event h
    have htime' : Measurable (fun z : (Nat -> Real) × (Nat -> TripLength) =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime (index z) z.1) := by
      convert htime using 1
      funext z
      rw [show Nat.find (h z) = index z by
        exact (Nat.find_spec (h z)).symm]
    exact htime'.prodMk
      ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp measurable_snd)
  have hinputs : HasLaw (fun seed : GN21RawCycleSeed =>
      ((seed.1 switchClock, seed.1 arrClock),
        AcceptedArrivalTime.rawTripMarkStream state seed))
      ((S.prod A).prod M) P := by
    have hneq : switchClock ≠ arrClock := by
      dsimp [switchClock, arrClock, RawTwoStateCTMC.switchClockIndex, gn21ArrivalClockIndex]
      fin_cases state <;> decide
    simpa [S, A, M, P, clockRate, switchClock, arrClock] using
      (RawTwoStateCTMC.rawClockPair_markStream_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI switchClock arrClock hneq state)
  let arrMarkPair : GN21RawCycleSeed -> (Nat -> Real) × (Nat -> TripLength) := fun seed =>
    (seed.1 arrClock, AcceptedArrivalTime.rawTripMarkStream state seed)
  have harrMarkMeas : Measurable arrMarkPair := by
    exact ((measurable_pi_apply arrClock).comp measurable_fst).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)
  let projectArrivalMark : ((Nat -> Real) × (Nat -> Real)) × (Nat -> TripLength) ->
      (Nat -> Real) × (Nat -> TripLength) := Prod.map Prod.snd id
  have hprojectArrivalMark : Measurable projectArrivalMark := by
    exact measurable_snd.prodMap measurable_id
  have harrMarkInput : HasLaw projectArrivalMark (A.prod M) ((S.prod A).prod M) := by
    refine ⟨hprojectArrivalMark.aemeasurable, ?_⟩
    change Measure.map (Prod.map Prod.snd id) ((S.prod A).prod M) = A.prod M
    rw [← Measure.map_prod_map (S.prod A) M measurable_snd measurable_id]
    simp only [Measure.map_snd_prod, Measure.map_id, measure_univ, one_smul]
  have harrMark : HasLaw arrMarkPair (A.prod M) P := by
    simpa [arrMarkPair, projectArrivalMark, Function.comp_def] using harrMarkInput.comp hinputs
  have hfirstPairLaw : HasLaw firstPair (T.prod Q) (A.prod M) := by
    refine ⟨hfirstPair.aemeasurable, ?_⟩
    calc
      Measure.map firstPair (A.prod M) = Measure.map firstPair (Measure.map arrMarkPair P) := by
        rw [harrMark.map_eq]
      _ = Measure.map (firstPair ∘ arrMarkPair) P := by
        rw [Measure.map_map hfirstPair harrMarkMeas]
      _ = Measure.map (fun seed =>
          (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) P := by
          rfl
      _ = T.prod Q := by
          simpa [T, Q, P, clockRate, arrClock] using
            (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark_hasLaw_prod
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI
              arrClock state sigma hsigma hmass).map_eq
  have hassoc : HasLaw (MeasurableEquiv.prodAssoc :
      ((Nat -> Real) × (Nat -> Real)) × (Nat -> TripLength) ->
        (Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)))
      (S.prod (A.prod M)) ((S.prod A).prod M) :=
    (measurePreserving_prodAssoc S A M).hasLaw
  have hpair : HasLaw (Prod.map id firstPair :
      (Nat -> Real) × ((Nat -> Real) × (Nat -> TripLength)) ->
        (Nat -> Real) × (Real × TripLength))
      (S.prod (T.prod Q)) (S.prod (A.prod M)) := by
    refine ⟨(measurable_id.prodMap hfirstPair).aemeasurable, ?_⟩
    rw [← Measure.map_prod_map S (A.prod M) measurable_id hfirstPair,
      Measure.map_id, hfirstPairLaw.map_eq]
  let head : (Nat -> Real) -> Real := fun gaps => gaps 0
  have hheadMeas : Measurable head := by
    exact measurable_pi_apply 0
  have hhead : HasLaw head E S := by
    simpa [head, E, S,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (measurePreserving_eval_infinitePi
        (fun _ : Nat => ProbabilityTheory.expMeasure (clockRate switchClock)) 0).hasLaw
  have hheadPair : HasLaw (Prod.map head id :
      (Nat -> Real) × (Real × TripLength) -> Real × (Real × TripLength))
      (E.prod (T.prod Q)) (S.prod (T.prod Q)) := by
    refine ⟨(hheadMeas.prodMap measurable_id).aemeasurable, ?_⟩
    rw [← Measure.map_prod_map S (T.prod Q) hheadMeas
      measurable_id, hhead.map_eq, Measure.map_id]
  let reorder : Real × (Real × TripLength) -> Real × (Real × TripLength) := fun z =>
    (z.2.1, (z.1, z.2.2))
  have hassocBack : HasLaw (MeasurableEquiv.prodAssoc.symm :
      Real × (Real × TripLength) -> (Real × Real) × TripLength)
      ((E.prod T).prod Q) (E.prod (T.prod Q)) :=
    (measurePreserving_prodAssoc E T Q).symm.hasLaw
  have hswap : HasLaw (fun z : (Real × Real) × TripLength => (z.1.swap, z.2))
      ((T.prod E).prod Q) ((E.prod T).prod Q) := by
    have hswapMeas : Measurable (fun z : (Real × Real) × TripLength =>
        (z.1.swap, z.2)) := by
      exact ((measurable_swap : Measurable (Prod.swap : Real × Real -> Real × Real)).comp
        measurable_fst).prodMk measurable_snd
    refine ⟨hswapMeas.aemeasurable, ?_⟩
    change Measure.map (Prod.map Prod.swap id) ((E.prod T).prod Q) = (T.prod E).prod Q
    rw [← Measure.map_prod_map (E.prod T) Q measurable_swap measurable_id,
      Measure.prod_swap, Measure.map_id]
  have hassocForward : HasLaw (MeasurableEquiv.prodAssoc :
      (Real × Real) × TripLength -> Real × (Real × TripLength))
      (T.prod (E.prod Q)) ((T.prod E).prod Q) :=
    (measurePreserving_prodAssoc T E Q).hasLaw
  have hReorder : HasLaw reorder (T.prod (E.prod Q)) (E.prod (T.prod Q)) := by
    have h := hassocForward.comp (hswap.comp hassocBack)
    simpa [reorder, Function.comp_def] using h
  have hpre := hheadPair.comp (hpair.comp (hassoc.comp hinputs))
  have hfinal := hReorder.comp hpre
  simpa [gn21RawPostThinningRaceSeed, gn21PostThinningRaceSeedMeasure, P, T, E, Q,
    clockRate, arrClock, switchClock, head, firstPair, reorder, Function.comp_def,
    AcceptedArrivalTime.rawTripMarkStream, gn21RawCycleClock] using hfinal

/-- The literal first accepted-arrival clock and active switch clock do not
tie under the GN raw-source law.  This derives the source paper's weak versus
strict race-convention equivalence from the continuous exponential product
law; it is not an additional economic or behavioral assumption. -/
theorem measure_gn21RawPostThinningRaceTie_eq_zero
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 =
        (gn21RawPostThinningRaceSeed state sigma seed).2.1} = 0 := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let arrivalRate := clockRate (gn21ArrivalClockIndex state) *
    singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
  let T := ProbabilityTheory.expMeasure arrivalRate
  let S := ProbabilityTheory.expMeasure switchRate
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let project : ℝ × (ℝ × TripLength) -> ℝ × ℝ := fun z => (z.1, z.2.1)
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, clockRate, gn21ArrivalClockIndex]
    fin_cases state
    · simpa [gn21CycleClockRate] using mul_pos harrivalI hmass
    · simpa [gn21CycleClockRate] using mul_pos harrivalJ hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, clockRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure harrivalRate
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hproject : Measurable project := by
    exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hprojectLaw : HasLaw project (T.prod S) (T.prod (S.prod Q)) := by
    refine ⟨hproject.aemeasurable, ?_⟩
    change Measure.map project (T.prod (S.prod Q)) = T.prod S
    rw [show project = Prod.map id Prod.fst by rfl,
      ← Measure.map_prod_map T (S.prod Q) measurable_id measurable_fst,
      Measure.map_id, Measure.map_fst_prod]
    simp
  have hsource := gn21RawPostThinningRaceSeed_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hraceLaw : HasLaw (project ∘ gn21RawPostThinningRaceSeed state sigma)
      (T.prod S) P := by
    simpa [P, T, S, Q, clockRate, arrivalRate, switchRate, project,
      Function.comp_def] using hprojectLaw.fun_comp hsource
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := by
    exact measurableSet_eq_fun measurable_fst measurable_snd
  have htie : (T.prod S) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    have hae := AppliedModelingLib.Probability.ae_fst_ne_snd_expMeasure_prod
      arrivalRate switchRate
    rw [MeasureTheory.ae_iff] at hae
    simpa [T, S] using hae
  calc
    P {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 =
        (gn21RawPostThinningRaceSeed state sigma seed).2.1} =
        P ((project ∘ gn21RawPostThinningRaceSeed state sigma) ⁻¹'
          {p : ℝ × ℝ | p.1 = p.2}) := by rfl
    _ = Measure.map (project ∘ gn21RawPostThinningRaceSeed state sigma) P
        {p : ℝ × ℝ | p.1 = p.2} := by
          exact (Measure.map_apply
            (hproject.comp (measurable_gn21RawPostThinningRaceSeed state sigma hsigma))
            hdiag).symm
    _ = (T.prod S) {p : ℝ × ℝ | p.1 = p.2} := by rw [hraceLaw.map_eq]
    _ = 0 := htie

/-- The holding time until either an accepted request arrives or the open-state
clock switches is a literal raw-source observable.  It has the exponential
law at the sum of the accepted-arrival and switching rates. -/
def gn21RawPostThinningRaceMinimum (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Real :=
  fun seed => AppliedModelingLib.Probability.exponentialRaceMinimum
    ((gn21RawPostThinningRaceSeed state sigma seed).1,
      (gn21RawPostThinningRaceSeed state sigma seed).2.1)

/-- The branch on which the open-state switch occurs before the next accepted
request.  The strict convention is immaterial because the two continuous
clocks tie only on a null event. -/
def gn21RawPostThinningRaceSwitchesFirst (state : Fin 2) (sigma : TripPolicy) :
    Set GN21RawCycleSeed :=
  {seed |
    (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
      (gn21RawPostThinningRaceSeed state sigma seed).1}

/-- The branch on which the accepted arrival occurs before or simultaneously
with the active switch.  The weak inequality fixes the tie convention; ties
have zero probability under the continuous exponential input law. -/
def gn21RawPostThinningRaceAcceptedFirst (state : Fin 2) (sigma : TripPolicy) :
    Set GN21RawCycleSeed :=
  (gn21RawPostThinningRaceSwitchesFirst state sigma)ᶜ

/-- On the accepted-arrival branch, retain the elapsed race time, subtract it
from the active switch clock, and retain the selected accepted trip mark. -/
def gn21RawPostThinningRaceAcceptedWinnerResidualSeed
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21PostThinningRaceSeed :=
  AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidual ∘
    gn21RawPostThinningRaceSeed state sigma

theorem measurable_gn21RawPostThinningRaceAcceptedWinnerResidualSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma) := by
  exact
    (AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidual).comp
      (measurable_gn21RawPostThinningRaceSeed state sigma hsigma)

/-- The literal open-state race together with the unconsumed active-switch
tail and untouched opposite-state switch stream.  The outer pair is ordered
as (switch tails, active head), followed by (accepted-arrival time, mark), so
the density-level residual race theorem applies without treating a restart as
an input. -/
abbrev GN21PostThinningRaceWithSwitchTailSeed :=
  (((Nat -> Real) × (Nat -> Real)) × Real) × (Real × TripLength)

def gn21RawPostThinningRaceWithSwitchTailSeed
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21PostThinningRaceWithSwitchTailSeed :=
  fun seed =>
    (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed,
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime (gn21ArrivalClockIndex state)
        state sigma seed,
      AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))

/-- The raw coordinates observed before refreshing the incoming state's marked
arrival input after an open-state switch.  They contain both switch streams,
the departing state's full arrival stream, and its full mark stream. -/
abbrev GN21SwitchFirstExternalSeed :=
  (((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) × (Nat -> TripLength)

def gn21RawSwitchFirstExternalSeed (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstExternalSeed := fun seed =>
  ((RawTwoStateCTMC.rawSwitchGapPair seed,
      AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed),
    AcceptedArrivalTime.rawTripMarkStream state seed)

/-- The independent incoming marked-arrival input, paired after the complete
switch-first external coordinate.  This ordering is chosen so the external
time residual theorem applies to the literal source coordinates. -/
def gn21RawSwitchFirstIncomingArrivalInput (state : Fin 2) :
    GN21RawCycleSeed ->
      (GN21SwitchFirstExternalSeed × (Nat -> Real)) × (Nat -> TripLength) := fun seed =>
  ((gn21RawSwitchFirstExternalSeed state seed,
      AcceptedArrivalTime.rawClockStream
        (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) seed),
    AcceptedArrivalTime.rawTripMarkStream
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed)

/-- A total external time for the incoming arrival residual.  On the
source-a.s. nonnegative-gap event it is the literal active switch holding
time; `max 0` only fixes the otherwise-null exceptional inputs. -/
def gn21SwitchFirstExternalTime : Fin 2 -> GN21SwitchFirstExternalSeed -> Real
  | 0, b => max 0 (b.1.1.1 0)
  | 1, b => max 0 (b.1.1.2 0)

/-- The literal active switch holding time read from the same external
coordinate.  It is measurable but only nonnegative on the source-a.s.
positive-gap event, so the residual-law theorem uses its `max 0` version. -/
def gn21SwitchFirstRawTime : Fin 2 -> GN21SwitchFirstExternalSeed -> Real
  | 0, b => b.1.1.1 0
  | 1, b => b.1.1.2 0

theorem measurable_gn21RawSwitchFirstExternalSeed (state : Fin 2) :
    Measurable (gn21RawSwitchFirstExternalSeed state) := by
  exact (RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
    (AcceptedArrivalTime.measurable_rawClockStream (gn21ArrivalClockIndex state))).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream state)

theorem measurable_gn21RawSwitchFirstIncomingArrivalInput (state : Fin 2) :
    Measurable (gn21RawSwitchFirstIncomingArrivalInput state) := by
  exact ((measurable_gn21RawSwitchFirstExternalSeed state).prodMk
    (AcceptedArrivalTime.measurable_rawClockStream
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))

theorem measurable_gn21SwitchFirstExternalTime (state : Fin 2) :
    Measurable (gn21SwitchFirstExternalTime state) := by
  fin_cases state
  · exact measurable_const.max
      ((measurable_pi_apply 0).comp
        ((measurable_fst.comp measurable_fst).comp measurable_fst))
  · exact measurable_const.max
      ((measurable_pi_apply 0).comp
        ((measurable_snd.comp measurable_fst).comp measurable_fst))

theorem measurable_gn21SwitchFirstRawTime (state : Fin 2) :
    Measurable (gn21SwitchFirstRawTime state) := by
  fin_cases state
  · exact (measurable_pi_apply 0).comp
      ((measurable_fst.comp measurable_fst).comp measurable_fst)
  · exact (measurable_pi_apply 0).comp
      ((measurable_snd.comp measurable_fst).comp measurable_fst)

/-- The nonnegative switch clock used as an external time for the departing
marked-arrival stream.  Keeping this time on the switch-pair coordinate makes
the departing prefix event a literal external-time no-hit event. -/
def gn21SwitchFirstSwitchTime : Fin 2 -> (Nat -> Real) × (Nat -> Real) -> Real
  | 0, gaps => max 0 (gaps.1 0)
  | 1, gaps => max 0 (gaps.2 0)

theorem measurable_gn21SwitchFirstSwitchTime (state : Fin 2) :
    Measurable (gn21SwitchFirstSwitchTime state) := by
  fin_cases state
  · exact measurable_const.max ((measurable_pi_apply 0).comp measurable_fst)
  · exact measurable_const.max ((measurable_pi_apply 0).comp measurable_snd)

theorem gn21SwitchFirstSwitchTime_nonnegative
    (state : Fin 2) (gaps : (Nat -> Real) × (Nat -> Real)) :
    0 ≤ gn21SwitchFirstSwitchTime state gaps := by
  fin_cases state <;> exact le_max_left _ _

/-- The literal future departing marked-arrival input after a switch-first
event.  It consumes exactly the arrivals and marks exposed before the actual
switch clock; it does not introduce a replacement arrival process. -/
noncomputable def gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual
    (state : Fin 2) : GN21RawCycleSeed -> (Nat -> Real) × (Nat -> TripLength) :=
  fun seed =>
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (gn21SwitchFirstSwitchTime state)
      (gn21RawSwitchFirstExternalSeed state seed)

theorem measurable_gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual
    (state : Fin 2) :
    Measurable (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state) := by
  exact
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (gn21SwitchFirstSwitchTime state)
      (measurable_gn21SwitchFirstSwitchTime state)).comp
      (measurable_gn21RawSwitchFirstExternalSeed state)

/-- The number of departing-state raw arrivals completed by the literal
switch time.  Unlike a fresh clock, this count is read from the actual raw
arrival stream already present in the switch-first external coordinate. -/
noncomputable def gn21SwitchFirstDepartingArrivalCount (state : Fin 2) :
    ((Nat -> Real) × (Nat -> Real)) × (Nat -> Real) -> Nat := fun b =>
  AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
    (match state with
      | 0 => b.1.1 0
      | 1 => b.1.2 0) b.2

theorem measurable_gn21SwitchFirstDepartingArrivalCount (state : Fin 2) :
    Measurable (gn21SwitchFirstDepartingArrivalCount state) := by
  fin_cases state
  · change Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) × (Nat -> Real) =>
      AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount (b.1.1 0) b.2)
    have hinput : Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) ×
        (Nat -> Real) => (b.1.1 0, b.2)) := by
      exact ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst)).prodMk
        (show Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) ×
          (Nat -> Real) => b.2) from measurable_snd)
    exact AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount_joint.comp
      hinput
  · change Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) × (Nat -> Real) =>
      AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount (b.1.2 0) b.2)
    have hinput : Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) ×
        (Nat -> Real) => (b.1.2 0, b.2)) := by
      exact ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst)).prodMk
        (show Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) ×
          (Nat -> Real) => b.2) from measurable_snd)
    exact AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount_joint.comp
      hinput

/-- The same departing-arrival count, evaluated at the totalized external
switch time.  It is globally nonnegative, which is the domain required by the
external-time residual theorem.  Under the source law it agrees a.e. with the
literal raw-time count below. -/
noncomputable def gn21SwitchFirstDepartingExternalArrivalCount (state : Fin 2) :
    ((Nat -> Real) × (Nat -> Real)) × (Nat -> Real) -> Nat := fun b =>
  AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
    (gn21SwitchFirstSwitchTime state b.1) b.2

theorem measurable_gn21SwitchFirstDepartingExternalArrivalCount (state : Fin 2) :
    Measurable (gn21SwitchFirstDepartingExternalArrivalCount state) := by
  have hinput : Measurable (fun b : ((Nat -> Real) × (Nat -> Real)) ×
      (Nat -> Real) => (gn21SwitchFirstSwitchTime state b.1, b.2)) := by
    exact ((measurable_gn21SwitchFirstSwitchTime state).comp measurable_fst).prodMk
      measurable_snd
  exact AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount_joint.comp
    hinput

/-- The literal finite-prefix event that every departing-state request before
the switch is rejected.  The arrival count and marks are both raw source
coordinates, so this does not delete or resample the rejected requests. -/
def gn21SwitchFirstDepartingNoAcceptedCarrier
    (state : Fin 2) (sigma : TripPolicy) : Set GN21SwitchFirstExternalSeed :=
  AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
    (gn21SwitchFirstDepartingArrivalCount state) sigma

/-- The totalized external-time version of the literal no-accepted-prefix
carrier.  This is the exact event used by the residual factorization; the
separate a.e. bridge below returns it to the raw source event. -/
def gn21SwitchFirstDepartingNoAcceptedExternalCarrier
    (state : Fin 2) (sigma : TripPolicy) : Set GN21SwitchFirstExternalSeed :=
  AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
    (gn21SwitchFirstDepartingExternalArrivalCount state) sigma

/-- The corresponding event on the literal GN raw seed. -/
def gn21RawPostThinningRaceNoAcceptedBeforeSwitch
    (state : Fin 2) (sigma : TripPolicy) : Set GN21RawCycleSeed :=
  (gn21RawSwitchFirstExternalSeed state) ⁻¹'
    (gn21SwitchFirstDepartingNoAcceptedCarrier state sigma)

/-- The pullback of the totalized external-time no-hit carrier. -/
def gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch
    (state : Fin 2) (sigma : TripPolicy) : Set GN21RawCycleSeed :=
  (gn21RawSwitchFirstExternalSeed state) ⁻¹'
    (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma)

theorem measurableSet_gn21SwitchFirstDepartingNoAcceptedCarrier
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21SwitchFirstDepartingNoAcceptedCarrier state sigma) := by
  exact AppliedModelingLib.Probability.IIDStream.measurableSet_externalIndexPrefixEvent
    (gn21SwitchFirstDepartingArrivalCount state)
    (measurable_gn21SwitchFirstDepartingArrivalCount state)
    (gn21SwitchFirstDepartingNoAcceptedCarrier state sigma)
    (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit_prefixEvent
      (gn21SwitchFirstDepartingArrivalCount state) sigma hsigma)

theorem measurableSet_gn21SwitchFirstDepartingNoAcceptedExternalCarrier
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma) := by
  exact AppliedModelingLib.Probability.IIDStream.measurableSet_externalIndexPrefixEvent
    (gn21SwitchFirstDepartingExternalArrivalCount state)
    (measurable_gn21SwitchFirstDepartingExternalArrivalCount state)
    (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma)
    (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit_prefixEvent
      (gn21SwitchFirstDepartingExternalArrivalCount state) sigma hsigma)

theorem measurableSet_gn21RawPostThinningRaceNoAcceptedBeforeSwitch
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21RawPostThinningRaceNoAcceptedBeforeSwitch state sigma) := by
  exact (measurableSet_gn21SwitchFirstDepartingNoAcceptedCarrier state sigma hsigma).preimage
    (measurable_gn21RawSwitchFirstExternalSeed state)

theorem measurableSet_gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma) := by
  exact (measurableSet_gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma hsigma).preimage
    (measurable_gn21RawSwitchFirstExternalSeed state)

/-- On a nonexplosive monotone raw arrival path with an eventual accepted
mark, the literal no-accepted-prefix carrier is exactly the strict
switch-first event.  An arrival at the switch time is counted in the exposed
prefix, so this is a pathwise strict comparison rather than a tie convention. -/
theorem gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch_of_sourcePath
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (hfuture : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed)) atTop atTop)
    (hmono : Monotone (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed)))
    (haccepted : ∃ n, AcceptedArrivalTime.rawTripMarkStream state seed n ∈ sigma) :
    seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma ↔
      seed ∈ gn21RawPostThinningRaceNoAcceptedBeforeSwitch state sigma := by
  classical
  let gaps : Nat -> Real := AcceptedArrivalTime.rawClockStream
    (gn21ArrivalClockIndex state) seed
  let marks : Nat -> TripLength := AcceptedArrivalTime.rawTripMarkStream state seed
  let t : Real := RawTwoStateCTMC.rawSwitchGaps seed state 0
  let k : Nat := AcceptedTripSelection.firstAcceptedIndex sigma marks
  have haccepted' : ∃ n, marks n ∈ sigma := by
    simpa [marks] using haccepted
  have hk : k = Nat.find haccepted' := by
    simp [k, AcceptedTripSelection.firstAcceptedIndex_eq_firstHit,
      AppliedModelingLib.Probability.IIDStream.firstHit, haccepted']
  have hacceptedAtK : marks k ∈ sigma := by
    rw [hk]
    exact Nat.find_spec haccepted'
  have hprior : ∀ i < k, marks i ∉ sigma := by
    intro i hi
    rw [hk] at hi
    exact Nat.find_min haccepted' hi
  have hnext : t <
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t gaps) gaps := by
    exact AppliedModelingLib.Probability.PoissonProcess.lt_arrivalTime_canonicalRenewalCount
      t gaps (AppliedModelingLib.Probability.PoissonProcess.exists_arrivalTime_gt_of_tendsto_atTop
        gaps hfuture t)
  have hleft : seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma ↔
      t < AppliedModelingLib.Probability.PoissonProcess.arrivalTime k gaps := by
    simp [gn21RawPostThinningRaceSwitchesFirst, gn21RawPostThinningRaceSeed,
      t, k, gaps, marks, AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime,
      RawTwoStateCTMC.rawSwitchGaps, gn21RawCycleClock]
  have hright : seed ∈ gn21RawPostThinningRaceNoAcceptedBeforeSwitch state sigma ↔
      ∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t gaps →
        marks i ∉ sigma := by
    fin_cases state <;> simp [gn21RawPostThinningRaceNoAcceptedBeforeSwitch,
      gn21SwitchFirstDepartingNoAcceptedCarrier,
      AppliedModelingLib.Probability.IIDStream.externalIndexNoHit,
      gn21RawSwitchFirstExternalSeed, gn21SwitchFirstDepartingArrivalCount,
      RawTwoStateCTMC.rawSwitchGapPair, t, gaps, marks]
  rw [hleft, hright]
  constructor
  · intro hswitch i hi
    by_contra hiAccepted
    by_cases hik : i < k
    · exact hprior i hik hiAccepted
    · have hki : k ≤ i := Nat.le_of_not_gt hik
      have harrival_le :
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime k gaps ≤
            AppliedModelingLib.Probability.PoissonProcess.arrivalTime i gaps := hmono hki
      have hcount :
          AppliedModelingLib.Probability.PoissonProcess.arrivalTime i gaps ≤ t :=
        (AppliedModelingLib.Probability.PoissonProcess.lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
          gaps hfuture hmono t i).mp hi
      linarith
  · intro hnoAccepted
    have hcount_le :
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t gaps ≤ k := by
      by_contra hnot
      have hklt : k <
          AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t gaps :=
        Nat.lt_of_not_ge hnot
      exact hnoAccepted k hklt hacceptedAtK
    exact hnext.trans_le (hmono hcount_le)

/-- Under the literal positive-rate GN source law, strict switch-first agrees
almost surely with the explicit no-accepted-prefix carrier.  The source
nonexplosion, monotonicity, and eventual-acceptance facts are each transported
from existing raw source coordinates; no conditional restart statement is
used. -/
theorem ae_gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      seed ∈ gn21RawPostThinningRaceSwitchesFirst state sigma ↔
        seed ∈ gn21RawPostThinningRaceNoAcceptedBeforeSwitch state sigma := by
  filter_upwards [
    AcceptedArrivalTime.ae_rawClockStream_arrivalTime_tendsto_atTop
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI (gn21ArrivalClockIndex state),
    AcceptedArrivalTime.ae_rawClockStream_arrivalTime_monotone
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI (gn21ArrivalClockIndex state),
    AcceptedArrivalTime.ae_rawTripMarkStream_exists_accepted
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass] with
      seed hfuture hmono haccepted
  exact gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch_of_sourcePath
    state sigma seed hfuture hmono haccepted

theorem gn21SwitchFirstExternalTime_nonnegative (state : Fin 2)
    (b : GN21SwitchFirstExternalSeed) :
    0 ≤ gn21SwitchFirstExternalTime state b := by
  fin_cases state <;> exact le_max_left _ _

theorem gn21SwitchFirstExternalTime_raw_eq_max (state : Fin 2)
    (seed : GN21RawCycleSeed) :
    gn21SwitchFirstExternalTime state (gn21RawSwitchFirstExternalSeed state seed) =
      max 0 (RawTwoStateCTMC.rawSwitchGaps seed state 0) := by
  fin_cases state <;> rfl

theorem gn21SwitchFirstRawTime_raw_eq (state : Fin 2)
    (seed : GN21RawCycleSeed) :
    gn21SwitchFirstRawTime state (gn21RawSwitchFirstExternalSeed state seed) =
      RawTwoStateCTMC.rawSwitchGaps seed state 0 := by
  fin_cases state <;> rfl

theorem ae_gn21SwitchFirstRawTime_nonnegative
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      0 ≤ gn21SwitchFirstRawTime state (gn21RawSwitchFirstExternalSeed state seed) := by
  have hraw := AcceptedArrivalTime.ae_rawClockStream_nonnegative
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI
    (RawTwoStateCTMC.switchClockIndex state)
  filter_upwards [hraw] with seed hseed
  rw [gn21SwitchFirstRawTime_raw_eq]
  simpa [RawTwoStateCTMC.rawSwitchGaps,
    AcceptedArrivalTime.rawClockStream, gn21RawCycleClock] using hseed 0

theorem ae_gn21SwitchFirstExternalTime_eq_rawTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      gn21SwitchFirstExternalTime state (gn21RawSwitchFirstExternalSeed state seed) =
        gn21SwitchFirstRawTime state (gn21RawSwitchFirstExternalSeed state seed) := by
  filter_upwards [ae_gn21SwitchFirstRawTime_nonnegative
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state] with seed hseed
  rw [gn21SwitchFirstExternalTime_raw_eq_max,
    gn21SwitchFirstRawTime_raw_eq]
  exact max_eq_right (by
    simpa only [gn21SwitchFirstRawTime_raw_eq] using hseed)

/-- The globally defined external-time no-hit event agrees a.e. with the
literal raw switch-time event.  This is a totalization device only: positive
raw switch gaps make the two prefix lengths identical. -/
theorem ae_gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch_iff_noAcceptedBeforeSwitch
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      seed ∈ gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma ↔
        seed ∈ gn21RawPostThinningRaceNoAcceptedBeforeSwitch state sigma := by
  filter_upwards [ae_gn21SwitchFirstExternalTime_eq_rawTime
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state] with seed htime
  have hcount :
      gn21SwitchFirstDepartingExternalArrivalCount state
          (gn21RawSwitchFirstExternalSeed state seed).1 =
        gn21SwitchFirstDepartingArrivalCount state
          (gn21RawSwitchFirstExternalSeed state seed).1 := by
    fin_cases state
    · change AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (max 0 ((gn21RawSwitchFirstExternalSeed 0 seed).1.1.1 0))
          ((gn21RawSwitchFirstExternalSeed 0 seed).1.2) =
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          ((gn21RawSwitchFirstExternalSeed 0 seed).1.1.1 0)
          ((gn21RawSwitchFirstExternalSeed 0 seed).1.2)
      exact congrArg
        (fun t => AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t
          ((gn21RawSwitchFirstExternalSeed 0 seed).1.2))
        (by simpa [gn21SwitchFirstExternalTime, gn21SwitchFirstRawTime] using htime)
    · change AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (max 0 ((gn21RawSwitchFirstExternalSeed 1 seed).1.1.2 0))
          ((gn21RawSwitchFirstExternalSeed 1 seed).1.2) =
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          ((gn21RawSwitchFirstExternalSeed 1 seed).1.1.2 0)
          ((gn21RawSwitchFirstExternalSeed 1 seed).1.2)
      exact congrArg
        (fun t => AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t
          ((gn21RawSwitchFirstExternalSeed 1 seed).1.2))
        (by simpa [gn21SwitchFirstExternalTime, gn21SwitchFirstRawTime] using htime)
  change
    (∀ i, i < gn21SwitchFirstDepartingExternalArrivalCount state
        (gn21RawSwitchFirstExternalSeed state seed).1 →
      (gn21RawSwitchFirstExternalSeed state seed).2 i ∉ sigma) ↔
    ∀ i, i < gn21SwitchFirstDepartingArrivalCount state
        (gn21RawSwitchFirstExternalSeed state seed).1 →
      (gn21RawSwitchFirstExternalSeed state seed).2 i ∉ sigma
  rw [hcount]

private theorem map_reorder_five_product
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    (μd : Measure δ) (μe : Measure ε)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] [SFinite μe] :
    Measure.map (fun z : ((α × β) × γ) × (δ × ε) =>
      ((((z.1.1.1, z.1.1.2), z.2.1), z.1.2), z.2.2))
      (((μa.prod μb).prod μc).prod (μd.prod μe)) =
      (((μa.prod μb).prod μd).prod μc).prod μe := by
  let p1 := measurePreserving_prodAssoc (μa.prod μb) μc (μd.prod μe)
  let p2 := MeasurePreserving.prod (MeasurePreserving.id (μa.prod μb))
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μc μd μe))
  let pswap : MeasurePreserving (Prod.swap : γ × δ -> δ × γ)
      (μc.prod μd) (μd.prod μc) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p3 := MeasurePreserving.prod (MeasurePreserving.id (μa.prod μb))
    (MeasurePreserving.prod pswap (MeasurePreserving.id μe))
  let p4 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (μa.prod μb) (μd.prod μc) μe)
  let p5 := MeasurePreserving.prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (μa.prod μb) μd μc))
    (MeasurePreserving.id μe)
  have hcomp := p5.comp (p4.comp (p3.comp (p2.comp p1)))
  have hfun : (fun z : ((α × β) × γ) × (δ × ε) =>
      ((((z.1.1.1, z.1.1.2), z.2.1), z.1.2), z.2.2)) =
      Prod.map (MeasurableEquiv.prodAssoc.symm) id ∘
        MeasurableEquiv.prodAssoc.symm ∘
          Prod.map id (Prod.map Prod.swap id) ∘
            Prod.map id (MeasurableEquiv.prodAssoc.symm) ∘
              MeasurableEquiv.prodAssoc := by
    funext z
    rfl
  rw [hfun]
  exact hcomp.map_eq

private theorem map_pair_restrict_preimage_prod
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (X : Ω -> α) (Y : Ω -> β)
    (hX : Measurable X) (hY : Measurable Y)
    (hsource : HasLaw (fun omega => (X omega, Y omega)) (μ.prod ν) P)
    (s : Set α) (hs : MeasurableSet s) :
    Measure.map (fun omega => (X omega, Y omega)) (P.restrict (X ⁻¹' s)) =
      (μ.restrict s).prod ν := by
  let pair : Ω -> α × β := fun omega => (X omega, Y omega)
  let carrier : Set (α × β) := s ×ˢ Set.univ
  have hpair : Measurable pair := hX.prodMk hY
  have hcarrier : MeasurableSet carrier := hs.prod MeasurableSet.univ
  have hpreimage : pair ⁻¹' carrier = X ⁻¹' s := by
    ext omega
    simp [pair, carrier]
  calc
    Measure.map (fun omega => (X omega, Y omega)) (P.restrict (X ⁻¹' s)) =
        Measure.map pair (P.restrict (pair ⁻¹' carrier)) := by
          rw [hpreimage]
    _ = (Measure.map pair P).restrict carrier := by
          rw [Measure.restrict_map hpair hcarrier]
    _ = (μ.prod ν).restrict carrier := by rw [hsource.map_eq]
    _ = (μ.restrict s).prod ν := by
          simpa [carrier] using (Measure.restrict_prod_eq_prod_univ (μ := μ)
            (ν := ν) s).symm

/-- Transport a restricted source law through an observable before applying a
deterministic continuation map.  The restriction remains a preimage event;
this helper never substitutes an independently sampled continuation. -/
private theorem map_restrict_preimage
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (μ : Measure α) (X : Ω -> α) (Y : α -> β)
    (hX : Measurable X) (hY : Measurable Y)
    (hsource : HasLaw X μ P) (s : Set α) (hs : MeasurableSet s) :
    Measure.map (fun omega => Y (X omega)) (P.restrict (X ⁻¹' s)) =
      Measure.map Y (μ.restrict s) := by
  calc
    Measure.map (fun omega => Y (X omega)) (P.restrict (X ⁻¹' s)) =
        Measure.map Y (Measure.map X (P.restrict (X ⁻¹' s))) := by
          rw [Measure.map_map hY hX]
          rfl
    _ = Measure.map Y ((Measure.map X P).restrict s) := by
          rw [Measure.restrict_map hX hs]
    _ = Measure.map Y (μ.restrict s) := by rw [hsource.map_eq]

/-- A first-coordinate source event leaves an independent second coordinate
untouched when a deterministic map is applied to the first coordinate.  The
statement is unnormalized and therefore keeps the event mass exactly. -/
private theorem map_pair_restrict_fst_preimage_prod
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α -> γ) (hf : Measurable f) (s : Set α) (hs : MeasurableSet s) :
    Measure.map (fun z : α × β => (f z.1, z.2))
      ((μ.prod ν).restrict (Prod.fst ⁻¹' s)) =
      (Measure.map f (μ.restrict s)).prod ν := by
  let carrier : Set (α × β) := s ×ˢ Set.univ
  have hcarrier : MeasurableSet carrier := hs.prod MeasurableSet.univ
  have hpreimage : Prod.fst ⁻¹' s = carrier := by
    ext z
    simp [carrier]
  calc
    Measure.map (fun z : α × β => (f z.1, z.2))
        ((μ.prod ν).restrict (Prod.fst ⁻¹' s)) =
        Measure.map (Prod.map f id) ((μ.restrict s).prod ν) := by
          rw [hpreimage, ← Measure.restrict_prod_eq_prod_univ]
          rfl
    _ = (Measure.map f (μ.restrict s)).prod ν := by
          rw [← Measure.map_prod_map (μ.restrict s) ν hf measurable_id,
            Measure.map_id]

/-- The literal GN source factors into the complete switch/departing-arrival
external coordinate, the incoming arrival path, and the incoming mark path.
The order exposes the incoming marked path as the input to an external-time
residual calculation; no coordinate is resampled. -/
theorem gn21RawSwitchFirstIncomingArrivalInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (gn21RawSwitchFirstIncomingArrivalInput state)
      (Measure.prod
        (Measure.prod
          (Measure.prod
            (Measure.prod
              (Measure.prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ)
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI))
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state))))
            (AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ state)))
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let currentClock := gn21ArrivalClockIndex state
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let otherClock := gn21ArrivalClockIndex other
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
  let currentArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate currentClock)
  let otherArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate otherClock)
  let currentMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let otherMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let clockInput : GN21RawCycleSeed ->
      (((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) × (Nat -> Real) := fun seed =>
    ((RawTwoStateCTMC.rawSwitchGapPair seed,
        AcceptedArrivalTime.rawClockStream currentClock seed),
      AcceptedArrivalTime.rawClockStream otherClock seed)
  let markInput : GN21RawCycleSeed -> (Nat -> TripLength) × (Nat -> TripLength) := fun seed =>
    (AcceptedArrivalTime.rawTripMarkStream state seed,
      AcceptedArrivalTime.rawTripMarkStream other seed)
  let reassoc : ((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> Real)) ->
      (((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) × (Nat -> Real) :=
    MeasurableEquiv.prodAssoc.symm
  let reorder :
      ((((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) × (Nat -> Real)) ×
        ((Nat -> TripLength) × (Nat -> TripLength)) ->
      (GN21SwitchFirstExternalSeed × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    ((((z.1.1.1, z.1.1.2), z.2.1), z.1.2), z.2.2)
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  have hcurrent_other : currentClock ≠ otherClock := by
    dsimp [currentClock, otherClock, other, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  have hcurrent_two : currentClock ≠ 2 := by
    dsimp [currentClock, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  have hcurrent_three : currentClock ≠ 3 := by
    dsimp [currentClock, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  have hother_two : otherClock ≠ 2 := by
    dsimp [otherClock, other, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  have hother_three : otherClock ≠ 3 := by
    dsimp [otherClock, other, gn21ArrivalClockIndex]
    fin_cases state <;> decide
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
  letI : IsProbabilityMeasure currentArrivalLaw := by
    dsimp [currentArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate currentClock)
  letI : IsProbabilityMeasure otherArrivalLaw := by
    dsimp [otherArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate otherClock)
  letI : IsProbabilityMeasure currentMarkLaw := by
    dsimp [currentMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure otherMarkLaw := by
    dsimp [otherMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hrawClock : HasLaw (fun seed : GN21RawCycleSeed =>
      (RawTwoStateCTMC.rawSwitchGapPair seed,
        (AcceptedArrivalTime.rawClockStream currentClock seed,
          AcceptedArrivalTime.rawClockStream otherClock seed)))
      (switchLaw.prod (currentArrivalLaw.prod otherArrivalLaw)) P := by
    simpa [P, switchLaw, currentArrivalLaw, otherArrivalLaw,
      clockRate, currentClock, otherClock] using
      (RawTwoStateCTMC.rawSwitchGapPair_rawClockPair_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI
        currentClock otherClock hcurrent_other hcurrent_two hcurrent_three
        hother_two hother_three)
  have hassoc : HasLaw reassoc ((switchLaw.prod currentArrivalLaw).prod otherArrivalLaw)
      (switchLaw.prod (currentArrivalLaw.prod otherArrivalLaw)) := by
    exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc switchLaw currentArrivalLaw otherArrivalLaw)).hasLaw
  have hclock : HasLaw clockInput
      ((switchLaw.prod currentArrivalLaw).prod otherArrivalLaw) P := by
    have hcomposed := hassoc.comp hrawClock
    refine hcomposed.congr ?_
    filter_upwards [] with seed
    rfl
  have hmarks : HasLaw markInput (currentMarkLaw.prod otherMarkLaw) P := by
    simpa [markInput, currentMarkLaw, otherMarkLaw, other, P,
      AcceptedArrivalTime.rawTripMarkStream] using
      (RawTwoStateCTMC.rawTripMarkPair_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hclockInputMeas : Measurable clockInput := by
    exact (RawTwoStateCTMC.measurable_rawSwitchGapPair.prodMk
      (AcceptedArrivalTime.measurable_rawClockStream currentClock)).prodMk
        (AcceptedArrivalTime.measurable_rawClockStream otherClock)
  have hmarkInputMeas : Measurable markInput := by
    exact (AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream other)
  have hindep : ProbabilityTheory.IndepFun clockInput markInput P := by
    change ProbabilityTheory.IndepFun
      (fun z : (Fin 4 -> Nat -> Real) × (Fin 2 -> Nat -> TripLength) =>
        (((z.1 2, z.1 3), z.1 currentClock), z.1 otherClock))
      (fun z : (Fin 4 -> Nat -> Real) × (Fin 2 -> Nat -> TripLength) =>
        (z.2 state, z.2 other))
      (clockLaw.prod markLaw)
    exact ProbabilityTheory.indepFun_prod
      (((measurable_pi_apply 2).prodMk (measurable_pi_apply 3)).prodMk
        (measurable_pi_apply currentClock) |>.prodMk
          (measurable_pi_apply otherClock))
      ((measurable_pi_apply state).prodMk (measurable_pi_apply other))
  have hjoined := AppliedModelingLib.Probability.indepFun_hasLaw_prodMk
    hclock hmarks hindep
  have hreorder : Measurable reorder := by
    fun_prop
  have hreorderLaw : HasLaw reorder
      (Measure.prod
        (Measure.prod
          (Measure.prod (switchLaw.prod currentArrivalLaw) currentMarkLaw)
          otherArrivalLaw)
        otherMarkLaw)
      (((switchLaw.prod currentArrivalLaw).prod otherArrivalLaw).prod
        (currentMarkLaw.prod otherMarkLaw)) := by
    refine ⟨hreorder.aemeasurable, ?_⟩
    exact map_reorder_five_product switchLaw currentArrivalLaw otherArrivalLaw
      currentMarkLaw otherMarkLaw
  have hfinal := hreorderLaw.comp hjoined
  change HasLaw (gn21RawSwitchFirstIncomingArrivalInput state)
    (Measure.prod
      (Measure.prod
        (Measure.prod (switchLaw.prod currentArrivalLaw) currentMarkLaw)
        otherArrivalLaw)
      otherMarkLaw) P
  refine hfinal.congr ?_
  filter_upwards [] with seed
  rfl

/-- The complete switch/departing-arrival coordinate has its literal
four-factor raw product law.  This projection is retained separately because
the departing marked residual is stopped by the switch clock, whereas the
incoming residual is handled by a second product factorization. -/
theorem gn21RawSwitchFirstExternalSeed_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (gn21RawSwitchFirstExternalSeed state)
      (Measure.prod
        (Measure.prod
          ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchIJ).prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchJI))
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let currentArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let currentMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let otherArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex other))
  let otherMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let externalLaw : Measure GN21SwitchFirstExternalSeed :=
    (switchLaw.prod currentArrivalLaw).prod currentMarkLaw
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ s : Fin 2, IsProbabilityMeasure (gn21CycleMarkLaw muI muJ s) := by
    intro s
    fin_cases s <;> simp [gn21CycleMarkLaw] <;> infer_instance
  letI : IsProbabilityMeasure otherArrivalLaw := by
    dsimp [otherArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex other))
  letI : IsProbabilityMeasure otherMarkLaw := by
    dsimp [otherMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hinput := gn21RawSwitchFirstIncomingArrivalInput_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state
  have hproj : HasLaw
      (fun z : (GN21SwitchFirstExternalSeed × (Nat -> Real)) ×
        (Nat -> TripLength) => z.1.1)
      externalLaw ((externalLaw.prod otherArrivalLaw).prod otherMarkLaw) := by
    refine ⟨((measurable_fst.comp measurable_fst).aemeasurable), ?_⟩
    calc
      Measure.map (fun z : (GN21SwitchFirstExternalSeed × (Nat -> Real)) ×
          (Nat -> TripLength) => z.1.1)
          ((externalLaw.prod otherArrivalLaw).prod otherMarkLaw) =
          Measure.map Prod.fst
            (Measure.map Prod.fst ((externalLaw.prod otherArrivalLaw).prod otherMarkLaw)) := by
              rw [Measure.map_map measurable_fst measurable_fst]
              rfl
      _ = Measure.map Prod.fst (externalLaw.prod otherArrivalLaw) := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
      _ = externalLaw := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hcomposed := hproj.comp hinput
  change HasLaw (gn21RawSwitchFirstExternalSeed state) externalLaw
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [externalLaw, switchLaw, currentArrivalLaw, currentMarkLaw,
    otherArrivalLaw, otherMarkLaw, clockRate, other] using hcomposed.congr (by
      filter_upwards [] with seed
      rfl)

/-- The full raw input split at the active switch head: literal surviving
switch tails and head, both complete marked arrival streams, and no resampled
coordinate.  This is the source input for the joint switch-first continuation
kernel. -/
abbrev GN21SwitchFirstSplitInput :=
  ((((Nat -> Real) × (Nat -> Real)) × Real) ×
    ((Nat -> Real) × (Nat -> TripLength))) ×
      ((Nat -> Real) × (Nat -> TripLength))

def gn21RawSwitchFirstSplitInput (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstSplitInput := fun seed =>
  ((RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed,
    (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex state) seed,
      AcceptedArrivalTime.rawTripMarkStream state seed)),
    (AcceptedArrivalTime.rawClockStream
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) seed,
      AcceptedArrivalTime.rawTripMarkStream
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state) seed))

theorem measurable_gn21RawSwitchFirstSplitInput (state : Fin 2) :
    Measurable (gn21RawSwitchFirstSplitInput state) := by
  exact ((RawTwoStateCTMC.measurable_rawSwitchTailAndFirstGap state).prodMk
    ((AcceptedArrivalTime.measurable_rawClockStream (gn21ArrivalClockIndex state)).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream state))).prodMk
    ((AcceptedArrivalTime.measurable_rawClockStream
      (gn21ArrivalClockIndex
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))).prodMk
      (AcceptedArrivalTime.measurable_rawTripMarkStream
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))

/-- The switch-first no-hit carrier written directly on the six-factor split
source.  The active switch head is the external clock; only departing request
marks before that clock are inspected. -/
def gn21SwitchFirstSplitNoHitCarrier (sigma : TripPolicy) :
    Set GN21SwitchFirstSplitInput :=
  {z | ∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
      (max 0 z.1.1.2) z.1.2.1 → z.1.2.2 i ∉ sigma}

def gn21RawSwitchFirstSplitNoHit (state : Fin 2) (sigma : TripPolicy) :
    Set GN21RawCycleSeed :=
  (gn21RawSwitchFirstSplitInput state) ⁻¹' gn21SwitchFirstSplitNoHitCarrier sigma

/-- The literal split input has the exact six-factor raw source product law.
The active switch head is separated from the two unconsumed switch tails, but
both marked arrival streams are retained complete for the subsequent stopped
residual construction. -/
theorem gn21RawSwitchFirstSplitInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (gn21RawSwitchFirstSplitInput state)
      (Measure.prod
        (Measure.prod
          (Measure.prod
            ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI))
            (if state = 0 then ProbabilityTheory.expMeasure switchIJ
              else ProbabilityTheory.expMeasure switchJI))
          (Measure.prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state)))
            (AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ state))))
        (Measure.prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex
                (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let tailLaw := switchLaw
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
  let sourceLaw := ((((switchLaw.prod departingArrivalLaw).prod departingMarkLaw).prod
    incomingArrivalLaw).prod incomingMarkLaw)
  let targetLaw := (((tailLaw.prod headLaw).prod
    (departingArrivalLaw.prod departingMarkLaw)).prod
      (incomingArrivalLaw.prod incomingMarkLaw))
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
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
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
  have hinput := gn21RawSwitchFirstIncomingArrivalInput_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state
  have hsource : HasLaw (gn21RawSwitchFirstIncomingArrivalInput state) sourceLaw P := by
    simpa [sourceLaw, switchLaw, departingArrivalLaw, departingMarkLaw,
      incomingArrivalLaw, incomingMarkLaw, P, clockRate, other] using hinput
  let hswitch : MeasurePreserving
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state)
      switchLaw (tailLaw.prod headLaw) := by
    refine ⟨AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead state, ?_⟩
    simpa [switchLaw, tailLaw, headLaw] using
      (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamAfterActiveHead
        state hswitchIJ hswitchJI)
  let p1 := measurePreserving_prodAssoc
    ((switchLaw.prod departingArrivalLaw).prod departingMarkLaw)
    incomingArrivalLaw incomingMarkLaw
  let p2 := MeasurePreserving.prod
    (measurePreserving_prodAssoc switchLaw departingArrivalLaw departingMarkLaw)
    (MeasurePreserving.id (incomingArrivalLaw.prod incomingMarkLaw))
  let p3 := MeasurePreserving.prod
    (MeasurePreserving.prod hswitch
      (MeasurePreserving.id (departingArrivalLaw.prod departingMarkLaw)))
    (MeasurePreserving.id (incomingArrivalLaw.prod incomingMarkLaw))
  let reorder : (((((Nat -> Real) × (Nat -> Real)) × (Nat -> Real)) ×
      (Nat -> TripLength)) × (Nat -> Real)) × (Nat -> TripLength) ->
        GN21SwitchFirstSplitInput := fun z =>
    ((AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state z.1.1.1.1,
      (z.1.1.1.2, z.1.1.2)), (z.1.2, z.2))
  have hreorder : MeasurePreserving reorder sourceLaw targetLaw := by
    dsimp only [reorder]
    simpa [sourceLaw, targetLaw, tailLaw] using (p3.comp (p2.comp p1))
  have hcomposed := hreorder.hasLaw.comp hsource
  change HasLaw (gn21RawSwitchFirstSplitInput state) targetLaw P
  refine hcomposed.congr ?_
  filter_upwards [] with seed
  rfl

/-- Residualize the incoming marked arrival stream at the actual (totalized)
active switch head while retaining that head, the literal switch tails, and
the complete departing marked stream.  This is still an unconditional raw
source observation; the departing no-hit restriction is applied only after
the common clock has been retained. -/
abbrev GN21SwitchFirstIncomingResidualWithCompanion :=
  (Real × ((Nat -> Real) × (Nat -> TripLength))) ×
    (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))

noncomputable def gn21RawSwitchFirstIncomingResidualWithCompanion (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstIncomingResidualWithCompanion := fun seed =>
  let split := gn21RawSwitchFirstSplitInput state seed
  ((split.1.1.2,
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun t : Real => max 0 t) ((split.1.1.2, split.2.1), split.2.2)),
    (split.1.1.1, split.1.2))

theorem measurable_gn21RawSwitchFirstIncomingResidualWithCompanion (state : Fin 2) :
    Measurable (gn21RawSwitchFirstIncomingResidualWithCompanion state) := by
  let split := gn21RawSwitchFirstSplitInput state
  have hsplit := measurable_gn21RawSwitchFirstSplitInput state
  have hhead : Measurable (fun seed : GN21RawCycleSeed => (split seed).1.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hsplit))
  have hincoming : Measurable (fun seed : GN21RawCycleSeed =>
      (((split seed).1.1.2, (split seed).2.1), (split seed).2.2)) :=
    ((hhead.prodMk (measurable_fst.comp (measurable_snd.comp hsplit))).prodMk
      (measurable_snd.comp (measurable_snd.comp hsplit)))
  have hresidual : Measurable (fun seed : GN21RawCycleSeed =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun t : Real => max 0 t)
        (((split seed).1.1.2, (split seed).2.1), (split seed).2.2)) :=
    (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun t : Real => max 0 t)
      (measurable_const.max measurable_id)).comp hincoming
  exact (hhead.prodMk hresidual).prodMk
    ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
      (measurable_snd.comp (measurable_fst.comp hsplit)))

/-- The incoming marked residual has its original joint law while retaining
the active switch clock and every raw coordinate needed for the later
departing no-hit restriction.  This is a product-space identity, not a
conditional restart assertion. -/
theorem gn21RawSwitchFirstIncomingResidualWithCompanion_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (gn21RawSwitchFirstIncomingResidualWithCompanion state)
      (((if state = 0 then ProbabilityTheory.expMeasure switchIJ
          else ProbabilityTheory.expMeasure switchJI).prod
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))).prod
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            switchJI)).prod
          ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))).prod
            (AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ state)))))
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
  let departingLaw := departingArrivalLaw.prod departingMarkLaw
  let incomingArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex other))
  let incomingMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingArrivalLaw.prod incomingMarkLaw
  let splitLaw := ((tailLaw.prod headLaw).prod departingLaw).prod incomingLaw
  let companionLaw := tailLaw.prod departingLaw
  let sourceLaw := ((headLaw.prod companionLaw).prod incomingArrivalLaw).prod incomingMarkLaw
  let targetLaw := (headLaw.prod incomingLaw).prod companionLaw
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
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
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
  letI : IsProbabilityMeasure departingLaw := by
    dsimp [departingLaw]
    infer_instance
  letI : IsProbabilityMeasure incomingArrivalLaw := by
    dsimp [incomingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex other))
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  have hsplit := gn21RawSwitchFirstSplitInput_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state
  have hsplitLaw : HasLaw (gn21RawSwitchFirstSplitInput state) splitLaw P := by
    simpa [splitLaw, tailLaw, headLaw, departingArrivalLaw, departingMarkLaw,
      departingLaw, incomingArrivalLaw, incomingMarkLaw, incomingLaw,
      clockRate, other, P] using hsplit
  let swapHead : MeasurePreserving (Prod.swap : ((Nat -> Real) × (Nat -> Real)) ×
      Real -> Real × ((Nat -> Real) × (Nat -> Real))) (tailLaw.prod headLaw)
      (headLaw.prod tailLaw) := ⟨measurable_swap, Measure.prod_swap⟩
  let reassocHead := measurePreserving_prodAssoc headLaw tailLaw departingLaw
  let p1 := MeasurePreserving.prod (reassocHead.comp
    (MeasurePreserving.prod swapHead (MeasurePreserving.id departingLaw)))
      (MeasurePreserving.id incomingLaw)
  let p2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (headLaw.prod companionLaw)
      incomingArrivalLaw incomingMarkLaw)
  let reorder : GN21SwitchFirstSplitInput ->
      ((Real × (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) ×
        (Nat -> TripLength)))) × (Nat -> Real)) × (Nat -> TripLength) := fun z =>
    (((z.1.1.2, (z.1.1.1, z.1.2)), z.2.1), z.2.2)
  have hreorder : MeasurePreserving reorder splitLaw sourceLaw := by
    dsimp only [reorder]
    simpa [splitLaw, sourceLaw, companionLaw, departingLaw, incomingLaw] using
      (p2.comp p1)
  have hresidual :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_withCompanion_joint_hasLaw
      headLaw companionLaw (gn21CycleMarkLaw muI muJ other)
      (hrate (gn21ArrivalClockIndex other)) (fun t : Real => max 0 t)
      (measurable_const.max measurable_id)
      (fun _ => le_max_left _ _)
  have hcomposed := hresidual.comp (hreorder.hasLaw.comp hsplitLaw)
  change HasLaw (gn21RawSwitchFirstIncomingResidualWithCompanion state) targetLaw P
  simpa [targetLaw, headLaw, incomingLaw, incomingArrivalLaw, incomingMarkLaw,
    companionLaw, tailLaw, departingLaw, departingArrivalLaw, departingMarkLaw,
    gn21RawSwitchFirstIncomingResidualWithCompanion, gn21RawSwitchFirstSplitInput,
    clockRate, other] using hcomposed.congr (by
      filter_upwards [] with seed
      rfl)

/-- The ordered source input for the departing no-hit residual after the
incoming marked stream has been stopped at the same literal switch head. -/
abbrev GN21SwitchFirstJointContinuationInput :=
  ((Real × (((Nat -> Real) × (Nat -> Real)) ×
    ((Nat -> Real) × (Nat -> TripLength)))) × (Nat -> Real)) ×
      (Nat -> TripLength)

/-- The literal source history retained on a switch-first no-hit branch:
the active switch head, both untouched continuation inputs, and the finite
departing arrival prefix exposed before that head. -/
abbrev GN21SwitchFirstJointHistory :=
  (Real × (((Nat -> Real) × (Nat -> Real)) ×
    ((Nat -> Real) × (Nat -> TripLength)))) × (Nat × (Nat -> Real))

/-- Both state-marked arrival streams after a literal switch-first branch,
together with the surviving switch tails.  Every component is a deterministic
tail of the original raw coordinate. -/
abbrev GN21SwitchFirstJointContinuation :=
  ((Nat -> Real) × (Nat -> TripLength)) ×
    (((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))

noncomputable def gn21RawSwitchFirstJointContinuationInput (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstJointContinuationInput := fun seed =>
  let split := gn21RawSwitchFirstSplitInput state seed
  let incoming :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun t : Real => max 0 t) ((split.1.1.2, split.2.1), split.2.2)
  (((split.1.1.2, (split.1.1.1, incoming)), split.1.2.1), split.1.2.2)

theorem measurable_gn21RawSwitchFirstJointContinuationInput (state : Fin 2) :
    Measurable (gn21RawSwitchFirstJointContinuationInput state) := by
  let split := gn21RawSwitchFirstSplitInput state
  have hsplit := measurable_gn21RawSwitchFirstSplitInput state
  have hincoming : Measurable (fun seed : GN21RawCycleSeed =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (fun t : Real => max 0 t)
        (((split seed).1.1.2, (split seed).2.1), (split seed).2.2)) := by
    exact
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
        (α := TripLength) (fun t : Real => max 0 t)
        (measurable_const.max measurable_id)).comp
        (((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
          (measurable_fst.comp (measurable_snd.comp hsplit))).prodMk
          (measurable_snd.comp (measurable_snd.comp hsplit)))
  simpa [split, gn21RawSwitchFirstJointContinuationInput] using
    (((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
      ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
        hincoming)).prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp hsplit)))).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp hsplit)))

/-- The actual switch-first stopped history together with the complete
uninspected departing marked tail.  This is a deterministic raw-source map;
the following restricted-law theorem, rather than this definition, supplies
its regeneration property. -/
noncomputable def gn21RawSwitchFirstJointHistoryAndMarkedTail (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstJointHistory ×
      ((Nat -> TripLength) × (Nat -> Real)) := fun seed =>
  let z := gn21RawSwitchFirstJointContinuationInput state seed
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
    (fun b : Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength))) => max 0 b.1) z.1
  (history,
    (AppliedModelingLib.Probability.IIDStream.externalIndexTail
      (fun h : GN21SwitchFirstJointHistory => h.2.1) (history, z.2),
      AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail
        (fun b : Real × (((Nat -> Real) × (Nat -> Real)) ×
          ((Nat -> Real) × (Nat -> TripLength))) => max 0 b.1) z.1))

theorem measurable_gn21RawSwitchFirstJointHistoryAndMarkedTail (state : Fin 2) :
    Measurable (gn21RawSwitchFirstJointHistoryAndMarkedTail state) := by
  let input := gn21RawSwitchFirstJointContinuationInput state
  let time : Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength))) -> Real := fun b => max 0 b.1
  let history : (Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength)))) × (Nat -> Real) ->
      GN21SwitchFirstJointHistory :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory time
  let index : GN21SwitchFirstJointHistory -> Nat := fun h => h.2.1
  let tail := AppliedModelingLib.Probability.IIDStream.externalIndexTail
    (α := TripLength) index
  let residual := AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail time
  have hinput : Measurable input :=
    measurable_gn21RawSwitchFirstJointContinuationInput state
  have htime : Measurable time := by
    exact measurable_const.max measurable_fst
  have hhistory : Measurable history := by
    simpa [history] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimePastHistory
        time htime)
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have htail : Measurable tail := by
    simpa [tail] using
      (AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail
        (α := TripLength) index hindex)
  have hresidual : Measurable residual := by
    simpa [residual] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeResidualTail
        time htime)
  have houtput : Measurable (fun z : GN21SwitchFirstJointContinuationInput =>
      (history z.1, (tail (history z.1, z.2), residual z.1))) :=
    (hhistory.comp measurable_fst).prodMk
      ((htail.comp ((hhistory.comp measurable_fst).prodMk measurable_snd)).prodMk
        (hresidual.comp measurable_fst))
  exact houtput.comp hinput

/-- The ordered source input for the switch-first continuation has a fully
factored law: active switch head, untouched switch/incoming companion,
departing arrival gaps, and departing marks.  No carrier is imposed here. -/
theorem gn21RawSwitchFirstJointContinuationInput_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    let tailLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let headLaw := if state = 0 then ProbabilityTheory.expMeasure switchIJ
      else ProbabilityTheory.expMeasure switchJI
    let departingArrivalLaw :=
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate (gn21ArrivalClockIndex state))
    let departingMarkLaw :=
      AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    HasLaw (gn21RawSwitchFirstJointContinuationInput state)
      (((headLaw.prod (tailLaw.prod incomingLaw)).prod departingArrivalLaw).prod
        departingMarkLaw)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  dsimp
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let tailLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let headLaw : Measure Real := if state = 0 then ProbabilityTheory.expMeasure switchIJ
    else ProbabilityTheory.expMeasure switchJI
  let departingArrivalLaw :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let departingMarkLaw :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let departingLaw := departingArrivalLaw.prod departingMarkLaw
  let incomingArrivalLaw :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex other))
  let incomingMarkLaw :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingArrivalLaw.prod incomingMarkLaw
  let companionLaw := tailLaw.prod incomingLaw
  let incomingSource := (headLaw.prod incomingLaw).prod (tailLaw.prod departingLaw)
  let sourceLaw := ((headLaw.prod companionLaw).prod departingArrivalLaw).prod departingMarkLaw
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
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
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
  letI : IsProbabilityMeasure departingLaw := by
    dsimp [departingLaw]
    infer_instance
  letI : IsProbabilityMeasure incomingArrivalLaw := by
    dsimp [incomingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex other))
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  have hincoming := gn21RawSwitchFirstIncomingResidualWithCompanion_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state
  have hincomingLaw : HasLaw (gn21RawSwitchFirstIncomingResidualWithCompanion state)
      incomingSource P := by
    simpa [incomingSource, headLaw, incomingLaw, incomingArrivalLaw, incomingMarkLaw,
      tailLaw, departingLaw, departingArrivalLaw, departingMarkLaw, clockRate, other, P] using
      hincoming
  let p1 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (headLaw.prod incomingLaw) tailLaw departingLaw)
  let assocHead := measurePreserving_prodAssoc headLaw incomingLaw tailLaw
  let swapIncomingTail : MeasurePreserving (Prod.swap : ((Nat -> Real) ×
      (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> Real)) ->
        ((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))
      (incomingLaw.prod tailLaw) (tailLaw.prod incomingLaw) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p2 := MeasurePreserving.prod
    ((MeasurePreserving.prod (MeasurePreserving.id headLaw) swapIncomingTail).comp assocHead)
    (MeasurePreserving.id departingLaw)
  let p3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (headLaw.prod companionLaw)
      departingArrivalLaw departingMarkLaw)
  let reorder : GN21SwitchFirstIncomingResidualWithCompanion ->
      GN21SwitchFirstJointContinuationInput := fun z =>
    (((z.1.1, (z.2.1, z.1.2)), z.2.2.1), z.2.2.2)
  have hreorder : MeasurePreserving reorder incomingSource sourceLaw := by
    dsimp only [reorder]
    simpa [incomingSource, sourceLaw, companionLaw, departingLaw, incomingLaw] using
      (p3.comp (p2.comp p1))
  have hcomposed := hreorder.hasLaw.comp hincomingLaw
  change HasLaw (gn21RawSwitchFirstJointContinuationInput state) sourceLaw P
  simpa [gn21RawSwitchFirstJointContinuationInput,
    gn21RawSwitchFirstIncomingResidualWithCompanion] using hcomposed.congr (by
      filter_upwards [] with seed
      rfl)

/-- On the literal totalized switch-first no-hit carrier, retain the actual
stopped source history jointly with the complete uninspected departing marked
tail.  The tail has its original product law; the history marginal remains
unnormalized, as required for a later branchwise regeneration argument. -/
theorem map_gn21RawSwitchFirstJointHistoryAndMarkedTail_restrict_splitNoHit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    let tailLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let headLaw := if state = 0 then ProbabilityTheory.expMeasure switchIJ
      else ProbabilityTheory.expMeasure switchJI
    let departingArrivalLaw :=
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate (gn21ArrivalClockIndex state))
    let departingMarkLaw :=
      AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate (gn21ArrivalClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ
            (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
    let companionLaw := tailLaw.prod incomingLaw
    let time : Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength))) -> Real := fun b => max 0 b.1
    let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory time
    let A := AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
      (fun h : GN21SwitchFirstJointHistory => h.2.1) sigma
    Measure.map (gn21RawSwitchFirstJointHistoryAndMarkedTail state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawSwitchFirstSplitNoHit state sigma)) =
      (Measure.map Prod.fst
        (((Measure.map history ((headLaw.prod companionLaw).prod departingArrivalLaw)).prod
          departingMarkLaw).restrict A)).prod
        (departingMarkLaw.prod departingArrivalLaw) := by
  dsimp
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
  let time : Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength))) -> Real := fun b => max 0 b.1
  let history := AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory time
  let index : GN21SwitchFirstJointHistory -> Nat := fun h => h.2.1
  let A := AppliedModelingLib.Probability.IIDStream.externalIndexNoHit index sigma
  let carrier : Set GN21SwitchFirstJointContinuationInput :=
    {z | (history z.1, z.2) ∈ A}
  let input : GN21RawCycleSeed -> GN21SwitchFirstJointContinuationInput :=
    gn21RawSwitchFirstJointContinuationInput state
  let output : GN21SwitchFirstJointContinuationInput ->
      GN21SwitchFirstJointHistory × ((Nat -> TripLength) × (Nat -> Real)) := fun z =>
    (history z.1,
      (AppliedModelingLib.Probability.IIDStream.externalIndexTail index (history z.1, z.2),
        AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail time z.1))
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
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
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
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  have hinputLaw : HasLaw input sourceLaw P := by
    simpa [input, sourceLaw, companionLaw, incomingLaw, incomingArrivalLaw,
      incomingMarkLaw, tailLaw, headLaw, departingArrivalLaw, departingMarkLaw,
      clockRate, other, P] using
      (gn21RawSwitchFirstJointContinuationInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hinput : Measurable input :=
    measurable_gn21RawSwitchFirstJointContinuationInput state
  have htime : Measurable time := by
    exact measurable_const.max measurable_fst
  have hhistory : Measurable history := by
    simpa [history] using
      (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimePastHistory
        time htime)
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have htail : Measurable (AppliedModelingLib.Probability.IIDStream.externalIndexTail
      (α := TripLength) index) := by
    exact AppliedModelingLib.Probability.IIDStream.measurable_externalIndexTail index hindex
  have hresidual : Measurable
      (AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail time) := by
    exact AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeResidualTail
      time htime
  have houtput : Measurable output := by
    exact (hhistory.comp measurable_fst).prodMk
      ((htail.comp ((hhistory.comp measurable_fst).prodMk measurable_snd)).prodMk
        (hresidual.comp measurable_fst))
  have hA : AppliedModelingLib.Probability.IIDStream.ExternalIndexPrefixEvent index A :=
    AppliedModelingLib.Probability.IIDStream.externalIndexNoHit_prefixEvent index sigma hsigma
  have hcarrier : MeasurableSet carrier := by
    exact (AppliedModelingLib.Probability.IIDStream.measurableSet_externalIndexPrefixEvent
      index hindex A hA).preimage
        ((hhistory.comp measurable_fst).prodMk measurable_snd)
  have htransport := map_restrict_preimage P sourceLaw input output hinput houtput hinputLaw
    carrier hcarrier
  have hfactor :=
    AppliedModelingLib.Probability.PoissonProcess.map_externalTimeMarkedResidualTail_withPastHistory_restrict_eq_prod
      (headLaw.prod companionLaw) (gn21CycleMarkLaw muI muJ state)
      (hrate (gn21ArrivalClockIndex state)) time htime (fun _ => le_max_left _ _)
      A hA
  calc
    Measure.map (gn21RawSwitchFirstJointHistoryAndMarkedTail state)
        (P.restrict (gn21RawSwitchFirstSplitNoHit state sigma)) =
        Measure.map (fun seed => output (input seed))
          (P.restrict (input ⁻¹' carrier)) := by
            rw [show gn21RawSwitchFirstSplitNoHit state sigma = input ⁻¹' carrier by rfl]
            congr 1
    _ = Measure.map output (sourceLaw.restrict carrier) := htransport
    _ = (Measure.map Prod.fst
        (((Measure.map history ((headLaw.prod companionLaw).prod departingArrivalLaw)).prod
          departingMarkLaw).restrict A)).prod
        (departingMarkLaw.prod departingArrivalLaw) := by
          simpa [output, sourceLaw, carrier, history, time, A, index] using hfactor

noncomputable def gn21RawSwitchFirstJointContinuation (state : Fin 2) :
    GN21RawCycleSeed -> GN21SwitchFirstJointContinuation := fun seed =>
  let z := gn21RawSwitchFirstJointContinuationInput state seed
  (AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun t : Real => max 0 t) ((z.1.1.1, z.1.2), z.2), z.1.1.2)

/-- Measurability of the complete literal switch-first continuation.  This is
kept explicit because the continuation will be reassembled into the next raw
calendar seed rather than replaced by an independently drawn proposal. -/
theorem measurable_gn21RawSwitchFirstJointContinuation (state : Fin 2) :
    Measurable (gn21RawSwitchFirstJointContinuation state) := by
  let input := gn21RawSwitchFirstJointContinuationInput state
  have hinput : Measurable input := by
    let split := gn21RawSwitchFirstSplitInput state
    have hsplit := measurable_gn21RawSwitchFirstSplitInput state
    have hincoming : Measurable (fun seed : GN21RawCycleSeed =>
        AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (fun t : Real => max 0 t)
          (((split seed).1.1.2, (split seed).2.1), (split seed).2.2)) := by
      exact
        (AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
          (α := TripLength) (fun t : Real => max 0 t)
          (measurable_const.max measurable_id)).comp
          (((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
            (measurable_fst.comp (measurable_snd.comp hsplit))).prodMk
            (measurable_snd.comp (measurable_snd.comp hsplit)))
    simpa [input, gn21RawSwitchFirstJointContinuationInput, split] using
      (((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
        ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp hsplit))).prodMk
          hincoming)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp hsplit)))).prodMk
          (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp hsplit)))
  have hmarked : Measurable (fun z : GN21SwitchFirstJointContinuationInput =>
      ((z.1.1.1, z.1.2), z.2)) :=
    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  exact
    ((AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (fun t : Real => max 0 t)
      (measurable_const.max measurable_id)).comp hmarked).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)) |>.comp hinput

def gn21SwitchFirstJointNoHitCarrier (sigma : TripPolicy) :
    Set GN21SwitchFirstJointContinuationInput :=
  {z | ∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
      (max 0 z.1.1.1) z.1.2 → z.2 i ∉ sigma}

def gn21RawSwitchFirstJointNoHit (state : Fin 2) (sigma : TripPolicy) :
    Set GN21RawCycleSeed :=
  (gn21RawSwitchFirstJointContinuationInput state) ⁻¹'
    gn21SwitchFirstJointNoHitCarrier sigma

/-- The split-source and existing joint-continuation descriptions inspect the
same switch head, departing arrival prefix, and departing marks. -/
theorem gn21RawSwitchFirstSplitNoHit_eq_jointNoHit
    (state : Fin 2) (sigma : TripPolicy) :
    gn21RawSwitchFirstSplitNoHit state sigma = gn21RawSwitchFirstJointNoHit state sigma := by
  rfl

theorem gn21RawSwitchFirstJointNoHit_eq_externalNoHit
    (state : Fin 2) (sigma : TripPolicy) :
    gn21RawSwitchFirstJointNoHit state sigma =
      gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma := by
  ext seed
  fin_cases state
  · change
      (∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (max 0 (RawTwoStateCTMC.rawSwitchTailAndFirstGap 0 seed).2)
          (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex 0) seed) →
        AcceptedArrivalTime.rawTripMarkStream 0 seed i ∉ sigma) ↔
      ∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (gn21SwitchFirstSwitchTime 0 (RawTwoStateCTMC.rawSwitchGapPair seed))
          (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex 0) seed) →
        AcceptedArrivalTime.rawTripMarkStream 0 seed i ∉ sigma
    rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
    rfl
  · change
      (∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (max 0 (RawTwoStateCTMC.rawSwitchTailAndFirstGap 1 seed).2)
          (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex 1) seed) →
        AcceptedArrivalTime.rawTripMarkStream 1 seed i ∉ sigma) ↔
      ∀ i, i < AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (gn21SwitchFirstSwitchTime 1 (RawTwoStateCTMC.rawSwitchGapPair seed))
          (AcceptedArrivalTime.rawClockStream (gn21ArrivalClockIndex 1) seed) →
        AcceptedArrivalTime.rawTripMarkStream 1 seed i ∉ sigma
    rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
    rfl

/-- On the literal totalized switch-first no-hit carrier, both state-marked
arrival tails and the surviving switch tails factor jointly.  The incoming
tail is stopped first while retaining the common switch clock; the departing
no-hit residual is then applied to those same raw coordinates. -/
theorem map_gn21RawSwitchFirstJointContinuation_restrict_noHit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measure.map (gn21RawSwitchFirstJointContinuation state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawSwitchFirstJointNoHit state sigma)) =
      ((Measure.prod
        (Measure.map
          (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
            (fun t : Real => max 0 t))
          (Measure.prod
            (if state = 0 then ProbabilityTheory.expMeasure switchIJ
              else ProbabilityTheory.expMeasure switchJI)
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state)))))
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma)) •
        (Measure.prod
          (Measure.prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state)))
            (AppliedModelingLib.Probability.IIDStream.measure
              (gn21CycleMarkLaw muI muJ state)))
          (Measure.prod
            ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI))
            (Measure.prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex
                    (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))))
              (AppliedModelingLib.Probability.IIDStream.measure
                (gn21CycleMarkLaw muI muJ
                  (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))))) := by
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
  let departingLaw := departingArrivalLaw.prod departingMarkLaw
  let incomingArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex other))
  let incomingMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ other)
  let incomingLaw := incomingArrivalLaw.prod incomingMarkLaw
  let incomingSource := (headLaw.prod incomingLaw).prod (tailLaw.prod departingLaw)
  let companionLaw := tailLaw.prod incomingLaw
  let sourceLaw := ((headLaw.prod companionLaw).prod departingArrivalLaw).prod departingMarkLaw
  let outputLaw := departingLaw.prod companionLaw
  let input : GN21RawCycleSeed -> GN21SwitchFirstJointContinuationInput :=
    gn21RawSwitchFirstJointContinuationInput state
  let output : GN21SwitchFirstJointContinuationInput ->
      GN21SwitchFirstJointContinuation := fun z =>
    (AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (fun t : Real => max 0 t) ((z.1.1.1, z.1.2), z.2), z.1.1.2)
  let carrier := gn21SwitchFirstJointNoHitCarrier sigma
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
  letI : IsProbabilityMeasure tailLaw := by
    dsimp [tailLaw]
    infer_instance
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
  letI : IsProbabilityMeasure departingLaw := by
    dsimp [departingLaw]
    infer_instance
  letI : IsProbabilityMeasure incomingArrivalLaw := by
    dsimp [incomingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex other))
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure companionLaw := by
    dsimp [companionLaw]
    infer_instance
  have hincoming := gn21RawSwitchFirstIncomingResidualWithCompanion_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state
  have hincomingLaw : HasLaw (gn21RawSwitchFirstIncomingResidualWithCompanion state)
      incomingSource P := by
    simpa [incomingSource, headLaw, incomingLaw, incomingArrivalLaw, incomingMarkLaw,
      tailLaw, departingLaw, departingArrivalLaw, departingMarkLaw, clockRate, other, P] using
      hincoming
  let p1 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (headLaw.prod incomingLaw) tailLaw departingLaw)
  let assocHead := measurePreserving_prodAssoc headLaw incomingLaw tailLaw
  let swapIncomingTail : MeasurePreserving (Prod.swap : ((Nat -> Real) ×
      (Nat -> TripLength)) × ((Nat -> Real) × (Nat -> Real)) ->
        ((Nat -> Real) × (Nat -> Real)) × ((Nat -> Real) × (Nat -> TripLength)))
      (incomingLaw.prod tailLaw) (tailLaw.prod incomingLaw) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p2 := MeasurePreserving.prod
    ((MeasurePreserving.prod (MeasurePreserving.id headLaw) swapIncomingTail).comp assocHead)
    (MeasurePreserving.id departingLaw)
  let p3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (headLaw.prod companionLaw)
      departingArrivalLaw departingMarkLaw)
  let reorder : GN21SwitchFirstIncomingResidualWithCompanion ->
      GN21SwitchFirstJointContinuationInput := fun z =>
    (((z.1.1, (z.2.1, z.1.2)), z.2.2.1), z.2.2.2)
  have hreorder : MeasurePreserving reorder incomingSource sourceLaw := by
    dsimp only [reorder]
    simpa [incomingSource, sourceLaw, companionLaw, departingLaw, incomingLaw] using
      (p3.comp (p2.comp p1))
  have hinputLaw : HasLaw input sourceLaw P := by
    have hcomposed := hreorder.hasLaw.comp hincomingLaw
    simpa [input, gn21RawSwitchFirstJointContinuationInput,
      gn21RawSwitchFirstIncomingResidualWithCompanion] using hcomposed.congr (by
        filter_upwards [] with seed
        rfl)
  have hinput : Measurable input := by
    have hinput_eq : input = reorder ∘
        gn21RawSwitchFirstIncomingResidualWithCompanion state := by
      funext seed
      rfl
    rw [hinput_eq]
    exact hreorder.measurable.comp
      (measurable_gn21RawSwitchFirstIncomingResidualWithCompanion state)
  have hmarkedInput : Measurable (fun z : GN21SwitchFirstJointContinuationInput =>
      ((z.1.1.1, z.1.2), z.2)) :=
    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have houtput : Measurable output := by
    exact ((AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
        (α := TripLength)
        (fun t : Real => max 0 t) (measurable_const.max measurable_id)).comp hmarkedInput).prodMk
          (measurable_snd.comp (measurable_fst.comp measurable_fst))
  let index : (Real × (((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> Real) × (Nat -> TripLength))) ) × (Nat -> Real) -> Nat := fun h =>
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount (max 0 h.1.1) h.2
  have hindex : Measurable index := by
    exact AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount_joint.comp
      (((measurable_const.max measurable_id).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd)
  have hcarrier : MeasurableSet carrier := by
    change MeasurableSet (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit index sigma)
    exact AppliedModelingLib.Probability.IIDStream.measurableSet_externalIndexPrefixEvent
      index hindex (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit index sigma)
      (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit_prefixEvent index sigma hsigma)
  have htransport := map_restrict_preimage P sourceLaw input output hinput houtput hinputLaw
    carrier hcarrier
  have hfactor :=
    AppliedModelingLib.Probability.PoissonProcess.map_externalTimeMarkedResidualTail_withCompanion_restrict_eq_smul_of_noHit
        headLaw companionLaw (gn21CycleMarkLaw muI muJ state)
        (hrate (gn21ArrivalClockIndex state)) (fun t : Real => max 0 t)
        (measurable_const.max measurable_id) (fun _ => le_max_left _ _) sigma hsigma
  calc
    Measure.map (gn21RawSwitchFirstJointContinuation state)
        (P.restrict (gn21RawSwitchFirstJointNoHit state sigma)) =
        Measure.map (fun seed => output (input seed))
          (P.restrict (input ⁻¹' carrier)) := by
          rw [show gn21RawSwitchFirstJointNoHit state sigma = input ⁻¹' carrier by
            rfl]
          congr 1
    _ = Measure.map output (sourceLaw.restrict carrier) := htransport
    _ = ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (fun t : Real => max 0 t)) (headLaw.prod departingArrivalLaw)).prod
        departingMarkLaw
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma)) • outputLaw := by
          simpa [sourceLaw, carrier, index, outputLaw, companionLaw, departingLaw] using hfactor
    _ = ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (fun t : Real => max 0 t))
        (headLaw.prod departingArrivalLaw)).prod departingMarkLaw
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma)) •
        (departingLaw.prod companionLaw) := by rfl
    _ = ((Measure.map
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
          (fun h : Real × (Nat × (Nat -> Real)) => h.2.1) sigma)) •
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
                (gn21ArrivalClockIndex other))).prod
              (AppliedModelingLib.Probability.IIDStream.measure
                (gn21CycleMarkLaw muI muJ other))))) := by
          rfl

/-- The joint continuation is stated on the paper's literal strict
switch-first event.  The transport uses only the pre-existing source-a.e.
totalization/no-hit and strict/no-hit carrier equalities; the continuation
coordinates themselves are not changed. -/
theorem map_gn21RawSwitchFirstJointContinuation_restrict_switchesFirst_eq_noHit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawSwitchFirstJointContinuation state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      Measure.map (gn21RawSwitchFirstJointContinuation state)
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
          (gn21RawSwitchFirstJointNoHit state sigma)) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have htotal_raw :=
    ae_gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch_iff_noAcceptedBeforeSwitch
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma
  have hstrict_raw := ae_gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hjoint_strict : gn21RawSwitchFirstJointNoHit state sigma =ᵐ[P]
      gn21RawPostThinningRaceSwitchesFirst state sigma := by
    filter_upwards [htotal_raw, hstrict_raw] with seed htotal hstrict
    rw [gn21RawSwitchFirstJointNoHit_eq_externalNoHit]
    exact propext (htotal.trans hstrict.symm)
  have hrestrict : P.restrict (gn21RawSwitchFirstJointNoHit state sigma) =
      P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma) :=
    Measure.restrict_congr_set hjoint_strict
  rw [hrestrict]

/-- Under the literal raw source law, conditioning on no accepted departing
request before the (totalized) active switch time leaves the *actual*
departing arrival and mark tails fresh.  The stopped tail is a deterministic
suffix of the original source coordinate, and the final a.e. bridge returns
the totalized carrier to the paper's raw switch-time event. -/
theorem map_gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measure.map (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma)) =
      ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (gn21SwitchFirstSwitchTime state))
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : ((Nat -> Real) × (Nat -> Real)) × (Nat × (Nat -> Real)) => h.2.1) sigma) •
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let currentArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let currentBaseMarkLaw : Measure TripLength := gn21CycleMarkLaw muI muJ state
  let currentMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure currentBaseMarkLaw
  let externalLaw : Measure GN21SwitchFirstExternalSeed :=
    (switchLaw.prod currentArrivalLaw).prod currentMarkLaw
  let residualExternal : GN21SwitchFirstExternalSeed ->
      (Nat -> Real) × (Nat -> TripLength) :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
      (gn21SwitchFirstSwitchTime state)
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
  letI : IsProbabilityMeasure switchLaw := by
    dsimp [switchLaw]
    infer_instance
  letI : IsProbabilityMeasure currentArrivalLaw := by
    dsimp [currentArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex state))
  letI : IsProbabilityMeasure currentBaseMarkLaw := by
    dsimp [currentBaseMarkLaw]
    infer_instance
  letI : IsProbabilityMeasure currentMarkLaw := by
    dsimp [currentMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure externalLaw := by
    dsimp [externalLaw]
    infer_instance
  have hsource : HasLaw (gn21RawSwitchFirstExternalSeed state) externalLaw P := by
    simpa [P, externalLaw, switchLaw, currentArrivalLaw, currentMarkLaw,
      currentBaseMarkLaw, clockRate] using
      (gn21RawSwitchFirstExternalSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hresidual : Measurable residualExternal := by
    exact AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (gn21SwitchFirstSwitchTime state)
      (measurable_gn21SwitchFirstSwitchTime state)
  have hcarrier : MeasurableSet
      (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma) :=
    measurableSet_gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma hsigma
  have htransport := map_restrict_preimage P externalLaw
    (gn21RawSwitchFirstExternalSeed state) residualExternal
    (measurable_gn21RawSwitchFirstExternalSeed state) hresidual hsource
    (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma) hcarrier
  have hfactor :=
    AppliedModelingLib.Probability.PoissonProcess.map_externalTimeMarkedResidualTail_restrict_eq_smul_of_noHit
      switchLaw currentBaseMarkLaw (hrate (gn21ArrivalClockIndex state))
      (gn21SwitchFirstSwitchTime state)
      (measurable_gn21SwitchFirstSwitchTime state)
      (gn21SwitchFirstSwitchTime_nonnegative state) sigma hsigma
  calc
    Measure.map (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state)
        (P.restrict (gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma)) =
        Measure.map residualExternal
          (externalLaw.restrict
            (gn21SwitchFirstDepartingNoAcceptedExternalCarrier state sigma)) := by
          simpa [P, residualExternal,
            gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual,
            gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch] using htransport
    _ = ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (gn21SwitchFirstSwitchTime state))
        (switchLaw.prod currentArrivalLaw)).prod currentMarkLaw)
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : ((Nat -> Real) × (Nat -> Real)) × (Nat × (Nat -> Real)) => h.2.1) sigma) •
        (currentArrivalLaw.prod currentMarkLaw) := by
          simpa [residualExternal, externalLaw, currentMarkLaw,
            currentBaseMarkLaw, gn21SwitchFirstDepartingNoAcceptedExternalCarrier,
            gn21SwitchFirstDepartingExternalArrivalCount,
            AppliedModelingLib.Probability.IIDStream.externalIndexNoHit] using hfactor
    _ = ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (gn21SwitchFirstSwitchTime state))
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : ((Nat -> Real) × (Nat -> Real)) × (Nat × (Nat -> Real)) => h.2.1) sigma) •
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))) := by
          rfl

/-- The departing residual factorization stated on the paper's literal strict
switch-first event.  The only transport from the globally defined external
carrier is the explicit source-a.e. equality of events proved above. -/
theorem map_gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual_restrict_switchesFirst
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (gn21SwitchFirstSwitchTime state))
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : ((Nat -> Real) × (Nat -> Real)) × (Nat × (Nat -> Real)) => h.2.1) sigma) •
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have htotal_raw :=
    ae_gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch_iff_noAcceptedBeforeSwitch
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma
  have hstrict_raw := ae_gn21RawPostThinningRaceSwitchesFirst_iff_noAcceptedBeforeSwitch
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have htotal_strict :
      gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma =ᵐ[P]
        gn21RawPostThinningRaceSwitchesFirst state sigma := by
    filter_upwards [htotal_raw, hstrict_raw] with seed htotal hstrict
    exact propext (htotal.trans hstrict.symm)
  have hrestrict : P.restrict
      (gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma) =
      P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma) :=
    Measure.restrict_congr_set htotal_strict
  calc
    Measure.map (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state)
        (P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
        Measure.map (gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual state)
          (P.restrict (gn21RawPostThinningRaceNoAcceptedBeforeExternalSwitch state sigma)) := by
            rw [hrestrict]
    _ = ((Measure.map
        (AppliedModelingLib.Probability.PoissonProcess.externalTimePastHistory
          (gn21SwitchFirstSwitchTime state))
        (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state))))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state)))
        (AppliedModelingLib.Probability.IIDStream.externalIndexNoHit
          (fun h : ((Nat -> Real) × (Nat -> Real)) × (Nat × (Nat -> Real)) => h.2.1) sigma) •
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))).prod
          (AppliedModelingLib.Probability.IIDStream.measure
            (gn21CycleMarkLaw muI muJ state))) := by
          simpa [P] using
            (map_gn21RawPostThinningRaceSwitchFirstDepartingMarkedResidual_restrict
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma)

/-- The event-bearing observation of the switch/departing-state coordinate.
It is the literal race datum with the unconsumed switch tails, expressed as a
map of `GN21SwitchFirstExternalSeed`. -/
noncomputable def gn21SwitchFirstExternalObservation
    (state : Fin 2) (sigma : TripPolicy) :
    GN21SwitchFirstExternalSeed -> GN21PostThinningRaceWithSwitchTailSeed := fun b =>
  (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state b.1.1,
    ((AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma (b.2, b.1.2)).1.2,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma (b.2, b.1.2))))

theorem measurable_gn21SwitchFirstExternalObservation
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21SwitchFirstExternalObservation state sigma) := by
  let firstPair : (Nat -> TripLength) × (Nat -> Real) -> Real × TripLength := fun paths =>
    ((AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma paths).1.2,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma paths))
  have hfirstPair : Measurable firstPair := by
    let history := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
    have hhistory : Measurable history := by
      simpa [history] using
        AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
    exact ((measurable_snd.comp measurable_fst).comp hhistory).prodMk
      (AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryTripLength.comp hhistory)
  have hpaths : Measurable (fun b : GN21SwitchFirstExternalSeed => (b.2, b.1.2)) := by
    exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  simpa [gn21SwitchFirstExternalObservation, firstPair] using
    ((AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead state).comp
      (measurable_fst.comp measurable_fst)).prodMk (hfirstPair.comp hpaths)

theorem gn21SwitchFirstExternalObservation_raw_eq
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed) :
    gn21SwitchFirstExternalObservation state sigma
      (gn21RawSwitchFirstExternalSeed state seed) =
      gn21RawPostThinningRaceWithSwitchTailSeed state sigma seed := by
  rfl

/-- The carrier of the literal strict switch winner on the external race
observation. -/
def gn21SwitchFirstExternalCarrier (state : Fin 2) (sigma : TripPolicy) :
    Set GN21PostThinningRaceWithSwitchTailSeed :=
  {z | z.1.2 < z.2.1}

theorem measurableSet_gn21SwitchFirstExternalCarrier
    (state : Fin 2) (sigma : TripPolicy) :
    MeasurableSet (gn21SwitchFirstExternalCarrier state sigma) := by
  exact measurableSet_lt (measurable_snd.comp measurable_fst)
    (measurable_fst.comp measurable_snd)

theorem gn21RawPostThinningRaceSwitchesFirst_eq_externalCarrier_preimage
    (state : Fin 2) (sigma : TripPolicy) :
    gn21RawPostThinningRaceSwitchesFirst state sigma =
      (gn21RawSwitchFirstExternalSeed state) ⁻¹'
        ((gn21SwitchFirstExternalObservation state sigma) ⁻¹'
          gn21SwitchFirstExternalCarrier state sigma) := by
  ext seed
  change
    (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
        (gn21RawPostThinningRaceSeed state sigma seed).1 ↔
      (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2 <
        (gn21RawPostThinningRaceSeed state sigma seed).1
  rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
  change
    (RawTwoStateCTMC.rawSwitchGaps seed state 0 <
      (gn21RawPostThinningRaceSeed state sigma seed).1) ↔
      (RawTwoStateCTMC.rawSwitchGaps seed state 0 <
        (gn21RawPostThinningRaceSeed state sigma seed).1)
  rfl

/-- The literal incoming arrival/mark residual at the switch time, retained
jointly with the switch-first external race observation. -/
noncomputable def gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed ->
      GN21PostThinningRaceWithSwitchTailSeed × ((Nat -> Real) × (Nat -> TripLength)) :=
  fun seed =>
    (gn21RawPostThinningRaceWithSwitchTailSeed state sigma seed,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (gn21SwitchFirstExternalTime state)
        (gn21RawSwitchFirstIncomingArrivalInput state seed))

/-- The same literal incoming marked residual evaluated at the un-totalized
active switch time.  It agrees a.e. with the totalized observable used for
the law theorem below. -/
noncomputable def gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidualAtRawTime
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed ->
      GN21PostThinningRaceWithSwitchTailSeed × ((Nat -> Real) × (Nat -> TripLength)) :=
  fun seed =>
    (gn21RawPostThinningRaceWithSwitchTailSeed state sigma seed,
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (gn21SwitchFirstRawTime state)
        (gn21RawSwitchFirstIncomingArrivalInput state seed))

theorem measurable_gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual state sigma) := by
  exact ((measurable_gn21SwitchFirstExternalObservation state sigma hsigma).comp
    (measurable_gn21RawSwitchFirstExternalSeed state)).prodMk
    ((AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (gn21SwitchFirstExternalTime state)
      (measurable_gn21SwitchFirstExternalTime state)).comp
      (measurable_gn21RawSwitchFirstIncomingArrivalInput state))

theorem ae_gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual_eq_rawTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual state sigma seed =
        gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidualAtRawTime state sigma seed := by
  filter_upwards [ae_gn21SwitchFirstExternalTime_eq_rawTime
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state] with seed htime
  have htime' : gn21SwitchFirstExternalTime state
      (gn21RawSwitchFirstIncomingArrivalInput state seed).1.1 =
        gn21SwitchFirstRawTime state
          (gn21RawSwitchFirstIncomingArrivalInput state seed).1.1 := by
    simpa [gn21RawSwitchFirstIncomingArrivalInput] using htime
  simp only [gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual,
    gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidualAtRawTime,
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail,
    AppliedModelingLib.Probability.PoissonProcess.externalTimeResidualTail]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rw [htime']
  · funext i
    unfold AppliedModelingLib.Probability.IIDStream.externalIndexTail
    change (gn21RawSwitchFirstIncomingArrivalInput state seed).2
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (gn21SwitchFirstExternalTime state
            (gn21RawSwitchFirstIncomingArrivalInput state seed).1.1)
          (gn21RawSwitchFirstIncomingArrivalInput state seed).1.2 + i) =
      (gn21RawSwitchFirstIncomingArrivalInput state seed).2
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount
          (gn21SwitchFirstRawTime state
            (gn21RawSwitchFirstIncomingArrivalInput state seed).1.1)
          (gn21RawSwitchFirstIncomingArrivalInput state seed).1.2 + i)
    rw [htime']

/-- On the literal strict switch-winner branch, the observed race/tail datum
factors from the incoming state's residual exponential arrival path and its
uninspected IID mark suffix.  The external factor remains restricted to the
actual source carrier; this is an unnormalized source-law identity, not a
conditional resampling or strong-Markov assumption. -/
theorem map_gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
    let externalLaw :=
      Measure.prod
        (Measure.prod
          ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchIJ).prod
            (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
              switchJI))
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate (gn21ArrivalClockIndex state))))
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ state))
    let incomingLaw :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate (gn21ArrivalClockIndex other))).prod
        (AppliedModelingLib.Probability.IIDStream.measure
          (gn21CycleMarkLaw muI muJ other))
    Measure.map (gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      ((Measure.map (gn21SwitchFirstExternalObservation state sigma) externalLaw).restrict
        (gn21SwitchFirstExternalCarrier state sigma)).prod incomingLaw := by
  dsimp
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let other := AppliedModelingLib.Probability.TwoStateSwitching.otherState state
  let otherClock := gn21ArrivalClockIndex other
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchLaw : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let currentArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate (gn21ArrivalClockIndex state))
  let currentMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let externalLaw : Measure GN21SwitchFirstExternalSeed :=
    (switchLaw.prod currentArrivalLaw).prod currentMarkLaw
  let incomingArrivalLaw : Measure (Nat -> Real) :=
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate otherClock)
  let incomingBaseMarkLaw : Measure TripLength := gn21CycleMarkLaw muI muJ other
  let incomingMarkLaw : Measure (Nat -> TripLength) :=
    AppliedModelingLib.Probability.IIDStream.measure incomingBaseMarkLaw
  let incomingLaw := incomingArrivalLaw.prod incomingMarkLaw
  have hrate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate c)
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
  letI : IsProbabilityMeasure currentArrivalLaw := by
    dsimp [currentArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate (gn21ArrivalClockIndex state))
  letI : IsProbabilityMeasure currentMarkLaw := by
    dsimp [currentMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure externalLaw := by
    dsimp [externalLaw]
    infer_instance
  letI : IsProbabilityMeasure incomingArrivalLaw := by
    dsimp [incomingArrivalLaw]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hrate otherClock)
  letI : IsProbabilityMeasure incomingMarkLaw := by
    dsimp [incomingMarkLaw, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure incomingLaw := by
    dsimp [incomingLaw]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hinput : HasLaw (gn21RawSwitchFirstIncomingArrivalInput state)
      ((externalLaw.prod incomingArrivalLaw).prod incomingMarkLaw) P := by
    simpa [P, externalLaw, incomingArrivalLaw, incomingMarkLaw,
      currentArrivalLaw, currentMarkLaw, switchLaw, clockRate, otherClock, other] using
      (gn21RawSwitchFirstIncomingArrivalInput_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have htime : Measurable (gn21SwitchFirstExternalTime state) :=
    measurable_gn21SwitchFirstExternalTime state
  have hobs : Measurable (gn21SwitchFirstExternalObservation state sigma) :=
    measurable_gn21SwitchFirstExternalObservation state sigma hsigma
  have hmarked :=
    AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail_joint_hasLaw
      externalLaw incomingBaseMarkLaw (hrate otherClock)
      (gn21SwitchFirstExternalTime state) htime
      (gn21SwitchFirstExternalTime_nonnegative state)
      (gn21SwitchFirstExternalObservation state sigma) hobs
  have hcomposed := hmarked.comp hinput
  have hfull : HasLaw
      (gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual state sigma)
      ((Measure.map (gn21SwitchFirstExternalObservation state sigma) externalLaw).prod
        incomingLaw) P := by
    change HasLaw (gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual state sigma)
      ((Measure.map (gn21SwitchFirstExternalObservation state sigma) externalLaw).prod
        (incomingArrivalLaw.prod incomingMarkLaw)) P
    refine hcomposed.congr ?_
    filter_upwards [] with seed
    change
      (gn21RawPostThinningRaceWithSwitchTailSeed state sigma seed,
        AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
          (gn21SwitchFirstExternalTime state)
          (gn21RawSwitchFirstIncomingArrivalInput state seed)) =
        (gn21SwitchFirstExternalObservation state sigma
          (gn21RawSwitchFirstExternalSeed state seed),
          AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
            (gn21SwitchFirstExternalTime state)
            (gn21RawSwitchFirstIncomingArrivalInput state seed))
    rw [gn21SwitchFirstExternalObservation_raw_eq]
  letI : IsProbabilityMeasure
      (Measure.map (gn21SwitchFirstExternalObservation state sigma) externalLaw) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hevent : gn21RawPostThinningRaceSwitchesFirst state sigma =
      (gn21RawPostThinningRaceWithSwitchTailSeed state sigma) ⁻¹'
        (gn21SwitchFirstExternalCarrier state sigma) := by
    ext seed
    rw [gn21RawPostThinningRaceSwitchesFirst_eq_externalCarrier_preimage]
    change
      seed ∈ (gn21RawSwitchFirstExternalSeed state) ⁻¹'
        ((gn21SwitchFirstExternalObservation state sigma) ⁻¹'
          gn21SwitchFirstExternalCarrier state sigma) ↔
        gn21RawPostThinningRaceWithSwitchTailSeed state sigma seed ∈
          gn21SwitchFirstExternalCarrier state sigma
    rw [← gn21SwitchFirstExternalObservation_raw_eq state sigma seed]
    rfl
  have hrestrict := map_pair_restrict_preimage_prod P
    (Measure.map (gn21SwitchFirstExternalObservation state sigma) externalLaw)
    incomingLaw
    (gn21RawPostThinningRaceWithSwitchTailSeed state sigma)
    (fun seed =>
      AppliedModelingLib.Probability.PoissonProcess.externalTimeMarkedResidualTail
        (gn21SwitchFirstExternalTime state)
        (gn21RawSwitchFirstIncomingArrivalInput state seed))
    ((hobs.comp (measurable_gn21RawSwitchFirstExternalSeed state)))
    ((AppliedModelingLib.Probability.PoissonProcess.measurable_externalTimeMarkedResidualTail
      (α := TripLength) (gn21SwitchFirstExternalTime state) htime).comp
        (measurable_gn21RawSwitchFirstIncomingArrivalInput state))
    hfull (gn21SwitchFirstExternalCarrier state sigma)
    (measurableSet_gn21SwitchFirstExternalCarrier state sigma)
  simpa [P, externalLaw, incomingLaw, incomingArrivalLaw, incomingMarkLaw,
    gn21RawPostThinningRaceSwitchFirstIncomingMarkedResidual, hevent] using hrestrict

theorem measurable_gn21RawPostThinningRaceWithSwitchTailSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceWithSwitchTailSeed state sigma) := by
  exact (RawTwoStateCTMC.measurable_rawSwitchTailAndFirstGap state).prodMk
    ((AcceptedArrivalTime.measurable_gn21RawFirstAcceptedArrivalTime
      (gn21ArrivalClockIndex state) state sigma hsigma).prodMk
      ((AcceptedTripSelection.measurable_firstAcceptedTripMark sigma hsigma).comp
        (AcceptedArrivalTime.measurable_rawTripMarkStream state)))

/-- The source-derived post-race data after an accepted winner: elapsed time,
fresh active-switch residual, unconsumed state-indexed switch streams, and
the selected accepted trip mark. -/
def gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> ℝ × (ℝ × (((Nat -> Real) × (Nat -> Real)) × TripLength)) :=
  AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux ∘
    gn21RawPostThinningRaceWithSwitchTailSeed state sigma

theorem measurable_gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma) := by
  exact
    (AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidualWithLeadingAux).comp
      (measurable_gn21RawPostThinningRaceWithSwitchTailSeed state sigma hsigma)

/-- The literal race inputs, including the unconsumed state-indexed switch
tails, have their exact raw-source product law.  This is the input bridge for
the accepted-winner residual path; it does not yet assert a CTMC endpoint or
a regenerative cycle. -/
theorem gn21RawPostThinningRaceWithSwitchTailSeed_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawPostThinningRaceWithSwitchTailSeed state sigma)
      ((((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)).prod
        (ProbabilityTheory.expMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state)))).prod
        ((ProbabilityTheory.expMeasure
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).prod
          (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let arrClock := gn21ArrivalClockIndex state
  let switchClock := RawTwoStateCTMC.switchClockIndex state
  let M := AppliedModelingLib.Probability.IIDStream.measure (gn21CycleMarkLaw muI muJ state)
  let A := AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
    (clockRate arrClock)
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let S := ProbabilityTheory.expMeasure (clockRate switchClock)
  let T := ProbabilityTheory.expMeasure
    (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let input : GN21RawCycleSeed -> (Nat -> TripLength) × (Nat -> Real) := fun seed =>
    (AcceptedArrivalTime.rawTripMarkStream state seed,
      AcceptedArrivalTime.rawClockStream arrClock seed)
  let firstPair : (Nat -> TripLength) × (Nat -> Real) -> Real × TripLength := fun paths =>
    ((AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma paths).1.2,
      AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength
        (AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma paths))
  let sourceInput : GN21RawCycleSeed ->
      ((Nat -> Real) × (Nat -> Real)) × ((Nat -> TripLength) × (Nat -> Real)) := fun seed =>
    (RawTwoStateCTMC.rawSwitchGapPair seed, input seed)
  let factor : ((Nat -> Real) × (Nat -> Real)) ×
      ((Nat -> TripLength) × (Nat -> Real)) -> GN21PostThinningRaceWithSwitchTailSeed := fun z =>
    (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state z.1,
      firstPair z.2)
  have harrivalRate : 0 < clockRate arrClock := by
    dsimp [clockRate, arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < clockRate switchClock := by
    dsimp [clockRate, switchClock, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < clockRate arrClock *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
    exact mul_pos harrivalRate hmass
  have harrNotTwo : arrClock ≠ 2 := by
    dsimp [arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  have harrNotThree : arrClock ≠ 3 := by
    dsimp [arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> decide
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := by
    dsimp [M, AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    exact AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      harrivalRate
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
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hinputMeas : Measurable input := by
    exact (AcceptedArrivalTime.measurable_rawTripMarkStream state).prodMk
      (AcceptedArrivalTime.measurable_rawClockStream arrClock)
  have hfirstPairMeas : Measurable firstPair := by
    let history := AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams sigma
    have hhistory : Measurable history := by
      simpa [history] using
        AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryOfStreams sigma hsigma
    exact ((measurable_snd.comp measurable_fst).comp hhistory).prodMk
      (AcceptedArrivalTime.measurable_firstAcceptedArrivalHistoryTripLength.comp hhistory)
  have hinput : HasLaw input (M.prod A) P := by
    simpa [input, M, A, P, clockRate, arrClock,
      AppliedModelingLib.Probability.IIDStream.measure,
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure] using
      (AcceptedArrivalTime.rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI arrClock state)
  have hfirstRaw : HasLaw (fun seed : GN21RawCycleSeed =>
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
        AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))
      (T.prod Q) P := by
    simpa [T, Q, P, clockRate, arrClock] using
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime_firstAcceptedTripMark_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI arrClock state sigma hsigma hmass)
  have hfirstPair : Measure.map firstPair (M.prod A) = T.prod Q := by
    calc
      Measure.map firstPair (M.prod A) = Measure.map firstPair (Measure.map input P) := by
        rw [hinput.map_eq]
      _ = Measure.map (firstPair ∘ input) P := by
        rw [Measure.map_map hfirstPairMeas hinputMeas]
      _ = Measure.map (fun seed : GN21RawCycleSeed =>
          (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)) P := by
            rfl
      _ = T.prod Q := hfirstRaw.map_eq
  have hsourceInput : HasLaw sourceInput (tails.prod (M.prod A)) P := by
    simpa [sourceInput, input, tails, P, arrClock] using
      (RawTwoStateCTMC.rawSwitchGapPair_rawTripMarkStream_rawClockStream_hasLaw_prod
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI arrClock state harrNotTwo harrNotThree)
  have hswitchFactor : Measure.map
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state) tails =
      tails.prod S := by
    fin_cases state
    · simpa [tails, S, switchClock, clockRate, RawTwoStateCTMC.switchClockIndex,
        gn21CycleClockRate] using
        (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamAfterActiveHead
          0 hswitchIJ hswitchJI)
    · simpa [tails, S, switchClock, clockRate, RawTwoStateCTMC.switchClockIndex,
        gn21CycleClockRate] using
        (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamAfterActiveHead
          1 hswitchIJ hswitchJI)
  have hfactorMeas : Measurable factor := by
    exact ((AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead
      state).comp measurable_fst).prodMk (hfirstPairMeas.comp measurable_snd)
  have hfactor : HasLaw factor ((tails.prod S).prod (T.prod Q)) (tails.prod (M.prod A)) := by
    refine ⟨hfactorMeas.aemeasurable, ?_⟩
    change Measure.map factor (tails.prod (M.prod A)) = (tails.prod S).prod (T.prod Q)
    rw [show factor = Prod.map
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead state)
      firstPair by rfl,
      ← Measure.map_prod_map tails (M.prod A)
        (AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamAfterActiveHead state)
        hfirstPairMeas,
      hswitchFactor, hfirstPair]
  have hfinal := hfactor.comp hsourceInput
  simpa [gn21RawPostThinningRaceWithSwitchTailSeed, sourceInput, input, factor,
    RawTwoStateCTMC.rawSwitchTailAndFirstGap, firstPair,
    AcceptedArrivalTime.firstAcceptedArrivalHistoryOfStreams,
    AcceptedArrivalTime.firstAcceptedArrivalHistoryTripLength, P, tails, S, T, Q,
    clockRate, arrClock, switchClock,
    AppliedModelingLib.Probability.PoissonProcess.twoStreamAfterActiveHead,
    AcceptedArrivalTime.rawTripMarkStream, AcceptedArrivalTime.rawClockStream,
    gn21RawCycleClock, gn21RawCycleMark] using hfinal

/-- On the literal branch where the open-state switch wins the competing
race, the unconsumed state-indexed switch streams retain their original
product law.  The equality is deliberately unnormalized by the branch mass:
it is a source-coordinate factorization, not a claim that the arrival or
mark streams have restarted. -/
theorem map_gn21RawPostThinningRaceSwitchTailPair_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (RawTwoStateCTMC.rawSwitchTailPair state)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) =
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceSwitchesFirst state sigma)) •
        ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
          (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let arrClock := gn21ArrivalClockIndex state
  let switchClock := RawTwoStateCTMC.switchClockIndex state
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let S := ProbabilityTheory.expMeasure (clockRate switchClock)
  let T := ProbabilityTheory.expMeasure
    (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let joint : GN21RawCycleSeed ->
      ((Nat -> Real) × (Nat -> Real)) × (Real × (Real × TripLength)) := fun seed =>
    (RawTwoStateCTMC.rawSwitchTailPair state seed,
      ((RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2,
        (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
          AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)))
  let tail : GN21RawCycleSeed -> (Nat -> Real) × (Nat -> Real) :=
    fun seed => (joint seed).1
  let race : GN21RawCycleSeed -> Real × (Real × TripLength) :=
    fun seed => (joint seed).2
  let switchCarrier : Set (Real × (Real × TripLength)) := {z | z.1 < z.2.1}
  have harrivalRate : 0 < clockRate arrClock := by
    dsimp [clockRate, arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < clockRate switchClock := by
    dsimp [clockRate, switchClock, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < clockRate arrClock *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
    exact mul_pos harrivalRate hmass
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
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
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hsource : HasLaw (gn21RawPostThinningRaceWithSwitchTailSeed state sigma)
      ((tails.prod S).prod (T.prod Q)) P := by
    simpa [tails, S, T, Q, P, clockRate, arrClock, switchClock] using
      (gn21RawPostThinningRaceWithSwitchTailSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hjoint_eq : joint = MeasurableEquiv.prodAssoc ∘
      gn21RawPostThinningRaceWithSwitchTailSeed state sigma := by
    funext seed
    change (RawTwoStateCTMC.rawSwitchTailPair state seed,
        ((RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2,
          (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed))) =
      ((RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).1,
        ((RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2,
          (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed,
            AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)))
    rw [RawTwoStateCTMC.rawSwitchTailPair_eq_factorTail]
  have hjointMeas : Measurable joint := by
    rw [hjoint_eq]
    exact MeasurableEquiv.prodAssoc.measurable.comp
      (measurable_gn21RawPostThinningRaceWithSwitchTailSeed state sigma hsigma)
  have hjointLaw : HasLaw joint (tails.prod (S.prod (T.prod Q))) P := by
    have hassoc : HasLaw (MeasurableEquiv.prodAssoc :
        (((Nat -> Real) × (Nat -> Real)) × Real) × (Real × TripLength) ≃ᵐ
          ((Nat -> Real) × (Nat -> Real)) × (Real × (Real × TripLength)))
        (tails.prod (S.prod (T.prod Q))) ((tails.prod S).prod (T.prod Q)) := by
      refine ⟨MeasurableEquiv.prodAssoc.measurable.aemeasurable, ?_⟩
      exact Measure.prodAssoc_prod
    rw [hjoint_eq]
    exact hassoc.fun_comp hsource
  have htailMeas : Measurable tail := measurable_fst.comp hjointMeas
  have hraceMeas : Measurable race := measurable_snd.comp hjointMeas
  have htailLaw : HasLaw tail tails P := by
    have hfst : HasLaw (Prod.fst : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × (Real × TripLength)) -> (Nat -> Real) × (Nat -> Real))
        tails (tails.prod (S.prod (T.prod Q))) := by
      refine ⟨measurable_fst.aemeasurable, ?_⟩
      rw [Measure.map_fst_prod]
      simp
    simpa [tail] using hfst.fun_comp hjointLaw
  have hraceLaw : HasLaw race (S.prod (T.prod Q)) P := by
    have hsnd : HasLaw (Prod.snd : ((Nat -> Real) × (Nat -> Real)) ×
        (Real × (Real × TripLength)) -> Real × (Real × TripLength))
        (S.prod (T.prod Q)) (tails.prod (S.prod (T.prod Q))) := by
      refine ⟨measurable_snd.aemeasurable, ?_⟩
      rw [Measure.map_snd_prod]
      simp
    simpa [race] using hsnd.fun_comp hjointLaw
  have hindep : tail ⟂ᵢ[P] race := by
    refine (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      htailMeas.aemeasurable hraceMeas.aemeasurable).mpr ?_
    change Measure.map joint P = (Measure.map tail P).prod (Measure.map race P)
    rw [hjointLaw.map_eq, htailLaw.map_eq, hraceLaw.map_eq]
  have hcarrier : MeasurableSet switchCarrier := by
    exact measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)
  have hswitch : race ⁻¹' switchCarrier =
      gn21RawPostThinningRaceSwitchesFirst state sigma := by
    ext seed
    change (RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed).2 <
        AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime arrClock state sigma seed ↔
      (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
        (gn21RawPostThinningRaceSeed state sigma seed).1
    rw [RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd]
    rfl
  ext B hB
  have htailB : MeasurableSet (tail ⁻¹' B) := hB.preimage htailMeas
  calc
    Measure.map (RawTwoStateCTMC.rawSwitchTailPair state)
        (P.restrict (gn21RawPostThinningRaceSwitchesFirst state sigma)) B =
        P (tail ⁻¹' B ∩ race ⁻¹' switchCarrier) := by
          rw [show RawTwoStateCTMC.rawSwitchTailPair state = tail by
            funext seed
            simp [tail, joint],
            Measure.map_apply htailMeas hB, Measure.restrict_apply htailB, hswitch]
    _ = P (tail ⁻¹' B) * P (race ⁻¹' switchCarrier) :=
      hindep.measure_inter_preimage_eq_mul B switchCarrier hB hcarrier
    _ = tails B * P (gn21RawPostThinningRaceSwitchesFirst state sigma) := by
      rw [← Measure.map_apply htailMeas hB, htailLaw.map_eq, hswitch]
    _ = (P (gn21RawPostThinningRaceSwitchesFirst state sigma) • tails) B := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_comm _ _

/-- On the literal accepted-winner event, the source retains a fresh active
switch residual jointly with both unconsumed switch streams and the selected
trip mark.  The equality is an unnormalized restricted law, whose scalar is
the accepted-winner probability. -/
theorem map_gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma)
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
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let arrClock := gn21ArrivalClockIndex state
  let switchClock := RawTwoStateCTMC.switchClockIndex state
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let S := ProbabilityTheory.expMeasure (clockRate switchClock)
  let T := ProbabilityTheory.expMeasure
    (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let carrier := AppliedModelingLib.Probability.exponentialRaceLeftWinnerLeadingAuxCarrier
    (α := (Nat -> Real) × (Nat -> Real)) (β := TripLength)
  have harrivalRate : 0 < clockRate arrClock := by
    dsimp [clockRate, arrClock, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < clockRate switchClock := by
    dsimp [clockRate, switchClock, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < clockRate arrClock *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
    exact mul_pos harrivalRate hmass
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
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
  letI : IsProbabilityMeasure S := by
    dsimp [S]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure T := by
    dsimp [T]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hsource : HasLaw (gn21RawPostThinningRaceWithSwitchTailSeed state sigma)
      ((tails.prod S).prod (T.prod Q)) P := by
    simpa [tails, S, T, Q, P, clockRate, arrClock, switchClock] using
      (gn21RawPostThinningRaceWithSwitchTailSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hpreimage : (gn21RawPostThinningRaceWithSwitchTailSeed state sigma) ⁻¹' carrier =
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
        (α := (Nat -> Real) × (Nat -> Real)) (β := TripLength))
  calc
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map
          (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
          (Measure.map (gn21RawPostThinningRaceWithSwitchTailSeed state sigma)
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [show gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma =
                AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux ∘
                  gn21RawPostThinningRaceWithSwitchTailSeed state sigma by rfl,
                Measure.map_map
                  AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidualWithLeadingAux
                  (measurable_gn21RawPostThinningRaceWithSwitchTailSeed state sigma hsigma)]
    _ = Measure.map
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
        ((Measure.map (gn21RawPostThinningRaceWithSwitchTailSeed state sigma) P).restrict
          carrier) := by
            rw [← hpreimage, Measure.restrict_map
              (measurable_gn21RawPostThinningRaceWithSwitchTailSeed state sigma hsigma) hcarrier]
    _ = Measure.map
        (AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux)
        (((tails.prod S).prod (T.prod Q)).restrict carrier) := by rw [hsource.map_eq]
    _ = ENNReal.ofReal (clockRate arrClock *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma /
        (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          clockRate switchClock)) •
        ((ProbabilityTheory.expMeasure
          (clockRate arrClock * singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            clockRate switchClock)).prod
          ((ProbabilityTheory.expMeasure (clockRate switchClock)).prod (tails.prod Q))) := by
            simpa [carrier, tails, S, T, Q] using
              (AppliedModelingLib.Probability.map_exponentialRaceLeftWinnerResidualWithLeadingAux_expMeasure_prod_restrict
                (ν := tails) (ξ := Q) hacceptedRate hswitchRate)
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))) := by
                rfl

theorem gn21RawPostThinningRaceMinimum_hasLaw_expMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawPostThinningRaceMinimum state sigma)
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let acceptedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let T := ProbabilityTheory.expMeasure (arrivalRate * mass)
  let S := ProbabilityTheory.expMeasure switchRate
  let Q := acceptedLaw
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < arrivalRate * mass := by
    exact mul_pos harrivalRate (by simpa [mass] using hmass)
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := by
    simpa [T] using ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    simpa [Q, acceptedLaw] using
      gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let project : GN21PostThinningRaceSeed -> Real × Real := fun z => (z.1, z.2.1)
  have hproject : Measurable project := by
    exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hprojectLaw : HasLaw project (T.prod S) (T.prod (S.prod Q)) := by
    refine ⟨hproject.aemeasurable, ?_⟩
    change Measure.map project (T.prod (S.prod Q)) = T.prod S
    rw [show project = Prod.map id Prod.fst by rfl,
      ← Measure.map_prod_map T (S.prod Q) measurable_id measurable_fst,
      Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul]
  have hminimumLaw : HasLaw
      AppliedModelingLib.Probability.exponentialRaceMinimum
      (ProbabilityTheory.expMeasure (arrivalRate * mass + switchRate)) (T.prod S) := by
    simpa [T, S] using
      (AppliedModelingLib.Probability.exponentialRaceMinimum_hasLaw_expMeasure
        hacceptedRate hswitchRate)
  have hpost : HasLaw (gn21RawPostThinningRaceSeed state sigma)
      (T.prod (S.prod Q)) P := by
    simpa [T, S, Q, P, arrivalRate, switchRate, mass, acceptedLaw] using
      (gn21RawPostThinningRaceSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hminimum : HasLaw
      (AppliedModelingLib.Probability.exponentialRaceMinimum ∘ project)
      (ProbabilityTheory.expMeasure (arrivalRate * mass + switchRate))
      (T.prod (S.prod Q)) := hminimumLaw.fun_comp hprojectLaw
  simpa [gn21RawPostThinningRaceMinimum, project, P, arrivalRate, switchRate, mass]
    using hminimum.fun_comp hpost

/-- The literal raw open-state holding time is integrable. -/
theorem integrable_gn21RawPostThinningRaceMinimum
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Integrable (gn21RawPostThinningRaceMinimum state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let rate := arrivalRate * mass + switchRate
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hrate : 0 < rate := by
    exact add_pos (mul_pos harrivalRate (by simpa [mass] using hmass)) hswitchRate
  have hLaw : HasLaw (gn21RawPostThinningRaceMinimum state sigma)
      (ProbabilityTheory.expMeasure rate) P := by
    simpa [P, rate, arrivalRate, switchRate, mass] using
      (gn21RawPostThinningRaceMinimum_hasLaw_expMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hmapInt : Integrable (fun x : Real => x)
      (Measure.map (gn21RawPostThinningRaceMinimum state sigma) P) := by
    rw [hLaw.map_eq]
    exact AppliedModelingLib.Probability.integrable_id_expMeasure hrate
  simpa [P, Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id hLaw.aemeasurable).mp hmapInt

/-- The expected literal raw open-state holding time is the reciprocal of the
accepted-arrival plus switching rate. -/
theorem integral_gn21RawPostThinningRaceMinimum_eq_inv_rate
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (∫ seed, gn21RawPostThinningRaceMinimum state sigma seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        1 /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state)) := by
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let rate := arrivalRate * mass + switchRate
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hrate : 0 < rate := by
    exact add_pos (mul_pos harrivalRate (by simpa [mass] using hmass)) hswitchRate
  have hLaw : HasLaw (gn21RawPostThinningRaceMinimum state sigma)
      (ProbabilityTheory.expMeasure rate) P := by
    simpa [P, rate, arrivalRate, switchRate, mass] using
      (gn21RawPostThinningRaceMinimum_hasLaw_expMeasure
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  calc
    (∫ seed, gn21RawPostThinningRaceMinimum state sigma seed ∂P) =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate := hLaw.integral_eq
    _ = 1 / rate := AppliedModelingLib.Probability.integral_id_expMeasure hrate
    _ = 1 /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state)) := by rfl

/-- The literal raw probability that the open-state switching clock wins its
race against the accepted-arrival clock is the usual normalized rate. -/
theorem measure_gn21RawPostThinningRaceSwitchesFirst
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceSwitchesFirst state sigma) =
        ENNReal.ofReal
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state) /
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))) := by
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let acceptedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let T := ProbabilityTheory.expMeasure (arrivalRate * mass)
  let S := ProbabilityTheory.expMeasure switchRate
  let Q := acceptedLaw
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < arrivalRate * mass := by
    exact mul_pos harrivalRate (by simpa [mass] using hmass)
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := by
    simpa [T] using ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    simpa [Q, acceptedLaw] using
      gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let project : GN21PostThinningRaceSeed -> Real × Real := fun z => (z.1, z.2.1)
  have hproject : Measurable project := by
    exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hprojectLaw : HasLaw project (T.prod S) (T.prod (S.prod Q)) := by
    refine ⟨hproject.aemeasurable, ?_⟩
    change Measure.map project (T.prod (S.prod Q)) = T.prod S
    rw [show project = Prod.map id Prod.fst by rfl,
      ← Measure.map_prod_map T (S.prod Q) measurable_id measurable_fst,
      Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul]
  have hpost : HasLaw (gn21RawPostThinningRaceSeed state sigma)
      (T.prod (S.prod Q)) P := by
    simpa [T, S, Q, P, arrivalRate, switchRate, mass, acceptedLaw] using
      (gn21RawPostThinningRaceSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hpairs : HasLaw (project ∘ gn21RawPostThinningRaceSeed state sigma)
      (T.prod S) P := hprojectLaw.fun_comp hpost
  have hcarrier : MeasurableSet
      AppliedModelingLib.Probability.exponentialDifferencePositiveCarrier :=
    AppliedModelingLib.Probability.measurableSet_exponentialDifferencePositiveCarrier
  calc
    P (gn21RawPostThinningRaceSwitchesFirst state sigma) =
        P ((project ∘ gn21RawPostThinningRaceSeed state sigma) ⁻¹'
          AppliedModelingLib.Probability.exponentialDifferencePositiveCarrier) := by rfl
    _ = Measure.map (project ∘ gn21RawPostThinningRaceSeed state sigma) P
        AppliedModelingLib.Probability.exponentialDifferencePositiveCarrier := by
          rw [Measure.map_apply_of_aemeasurable hpairs.aemeasurable hcarrier]
    _ = (T.prod S) AppliedModelingLib.Probability.exponentialDifferencePositiveCarrier := by
          rw [hpairs.map_eq]
    _ = ENNReal.ofReal (switchRate / (arrivalRate * mass + switchRate)) := by
          simpa [T, S] using
            (AppliedModelingLib.Probability.expMeasure_prod_measure_exponentialDifferencePositiveCarrier
              hacceptedRate hswitchRate)
    _ = ENNReal.ofReal
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))) := by rfl

/-- Conditional on an accepted request winning the literal open-state race,
the elapsed race time has the sum-rate exponential law and the active switch
clock has a fresh exponential residual.  This is an unnormalized restricted
law, so its scalar is exactly the accepted-winner probability. -/
theorem map_gn21RawPostThinningRaceAcceptedWinnerResidualSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma)
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
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
            (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let acceptedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let T := ProbabilityTheory.expMeasure (arrivalRate * mass)
  let S := ProbabilityTheory.expMeasure switchRate
  let Q := acceptedLaw
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < arrivalRate * mass := by
    exact mul_pos harrivalRate (by simpa [mass] using hmass)
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := by
    simpa [T] using ProbabilityTheory.isProbabilityMeasure_expMeasure hacceptedRate
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    simpa [Q, acceptedLaw] using
      gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  let residual := AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidual
    (α := TripLength)
  let carrier := AppliedModelingLib.Probability.exponentialRaceLeftWinnerCarrier TripLength
  have hpost : HasLaw (gn21RawPostThinningRaceSeed state sigma)
      (T.prod (S.prod Q)) P := by
    simpa [T, S, Q, P, arrivalRate, switchRate, mass, acceptedLaw] using
      (gn21RawPostThinningRaceSeed_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hpreimage : (gn21RawPostThinningRaceSeed state sigma) ⁻¹' carrier =
      gn21RawPostThinningRaceAcceptedFirst state sigma := by
    ext seed
    simp [carrier,
      AppliedModelingLib.Probability.exponentialRaceLeftWinnerCarrier,
      gn21RawPostThinningRaceAcceptedFirst,
      gn21RawPostThinningRaceSwitchesFirst, not_lt]
  have hcarrier : MeasurableSet carrier := by
    simpa [carrier] using
      (AppliedModelingLib.Probability.measurableSet_exponentialRaceLeftWinnerCarrier
        (α := TripLength))
  calc
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map residual
          (Measure.map (gn21RawPostThinningRaceSeed state sigma)
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [show gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma =
                residual ∘ gn21RawPostThinningRaceSeed state sigma by rfl,
                Measure.map_map
                  (AppliedModelingLib.Probability.measurable_exponentialRaceLeftWinnerResidual)
                  (measurable_gn21RawPostThinningRaceSeed state sigma hsigma)]
    _ = Measure.map residual ((Measure.map (gn21RawPostThinningRaceSeed state sigma) P).restrict
        carrier) := by
          rw [← hpreimage, Measure.restrict_map
            (measurable_gn21RawPostThinningRaceSeed state sigma hsigma) hcarrier]
    _ = Measure.map residual ((T.prod (S.prod Q)).restrict carrier) := by
          rw [hpost.map_eq]
    _ = ENNReal.ofReal (arrivalRate * mass / (arrivalRate * mass + switchRate)) •
        ((ProbabilityTheory.expMeasure (arrivalRate * mass + switchRate)).prod
          ((ProbabilityTheory.expMeasure switchRate).prod Q)) := by
            simpa [residual, carrier, T, S] using
              (AppliedModelingLib.Probability.map_exponentialRaceLeftWinnerResidual_expMeasure_prod_restrict
                (ν := Q) hacceptedRate hswitchRate)
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
            (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
              rfl

/-- The source data retained after an accepted race winner, with the active
switch residual reattached to its unconsumed state-indexed tail.  The second
coordinate is therefore a literal two-switch-stream continuation together
with the selected accepted trip length. -/
abbrev GN21PostThinningRaceAcceptedWinnerRestartSeed :=
  Real × (((Nat -> Real) × (Nat -> Real)) × TripLength)

def gn21PostThinningRaceAcceptedWinnerRestartFactor (state : Fin 2) :
    ℝ × (ℝ × (((Nat -> Real) × (Nat -> Real)) × TripLength)) ->
      GN21PostThinningRaceAcceptedWinnerRestartSeed :=
  fun z =>
    (z.1,
      (AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
        state (z.2.1, z.2.2.1), z.2.2.2))

theorem measurable_gn21PostThinningRaceAcceptedWinnerRestartFactor (state : Fin 2) :
    Measurable (gn21PostThinningRaceAcceptedWinnerRestartFactor state) := by
  exact measurable_fst.prodMk
    (((AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamPrependActiveHeadFromHeadTail
      state).comp
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

/-- The literal accepted-winner source continuation: elapsed open-state time,
the reassembled two switch streams, and the selected accepted trip length. -/
def gn21RawPostThinningRaceAcceptedWinnerRestartSeed
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> GN21PostThinningRaceAcceptedWinnerRestartSeed :=
  gn21PostThinningRaceAcceptedWinnerRestartFactor state ∘
    gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma

theorem measurable_gn21RawPostThinningRaceAcceptedWinnerRestartSeed
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma) := by
  exact (measurable_gn21PostThinningRaceAcceptedWinnerRestartFactor state).comp
    (measurable_gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma hsigma)

/-- The actual raw CTMC endpoint at the completion of the first accepted trip
after the state-specific competing race.  Unlike the earlier fixed-time
selected-mark observable, this uses the accepted-arrival calendar time before
adding the selected trip duration. -/
noncomputable def gn21RawPostThinningRaceCalendarCompletionState
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Fin 2 :=
  fun seed => RawTwoStateCTMC.stateAt state seed
    ((gn21RawPostThinningRaceSeed state sigma seed).1 +
      (gn21RawPostThinningRaceSeed state sigma seed).2.2)

/-- The completion endpoint read from the reassembled accepted-winner restart
seed.  Its switch streams are literal source tails with the active residual
reattached, not a fresh path postulated at the arrival time. -/
noncomputable def gn21PostThinningRaceAcceptedWinnerRestartCompletionState
    (state : Fin 2) : GN21PostThinningRaceAcceptedWinnerRestartSeed -> Fin 2 :=
  fun restart => AppliedModelingLib.Probability.TwoStateSwitching.stateAt state
    (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair restart.2.1)
    restart.2.2

/-- The literal state-indexed switch streams remaining at the actual
calendar-time completion of the selected accepted trip.  This uses the
accepted-arrival clock before adding the trip duration. -/
noncomputable def gn21RawPostThinningRaceCalendarCompletionSwitchGaps
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Fin 2 -> Nat -> Real :=
  fun seed => AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed state
    (RawTwoStateCTMC.rawSwitchGaps seed)
    ((gn21RawPostThinningRaceSeed state sigma seed).1 +
      (gn21RawPostThinningRaceSeed state sigma seed).2.2)

/-- The future switch streams read after the selected trip duration from the
literal accepted-winner continuation. -/
noncomputable def gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps
    (state : Fin 2) : GN21PostThinningRaceAcceptedWinnerRestartSeed -> Fin 2 -> Nat -> Real :=
  fun restart => AppliedModelingLib.Probability.TwoStateSwitching.switchGapsAfterElapsed state
    (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair restart.2.1)
    restart.2.2

/-- The actual calendar-completion endpoint together with the literal future
switch path.  Bundling the two makes the later endpoint/future factorization
claim explicitly joint. -/
noncomputable def gn21RawPostThinningRaceCalendarCompletionEndpointFuture
    (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> (Fin 2) × (Fin 2 -> Nat -> Real) := fun seed =>
  (gn21RawPostThinningRaceCalendarCompletionState state sigma seed,
    gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed)

/-- The same joint endpoint/future observation read from the reassembled
accepted-winner continuation. -/
noncomputable def gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture
    (state : Fin 2) : GN21PostThinningRaceAcceptedWinnerRestartSeed ->
      (Fin 2) × (Fin 2 -> Nat -> Real) := fun restart =>
  (gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart,
    gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state restart)

theorem measurable_gn21RawPostThinningRaceCalendarCompletionState
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceCalendarCompletionState state sigma) := by
  let race := gn21RawPostThinningRaceSeed state sigma
  have hrace : Measurable race :=
    measurable_gn21RawPostThinningRaceSeed state sigma hsigma
  have htime : Measurable (fun seed : GN21RawCycleSeed =>
      (race seed).1 + (race seed).2.2) := by
    exact (measurable_fst.comp hrace).add
      (measurable_snd.comp (measurable_snd.comp hrace))
  simpa [gn21RawPostThinningRaceCalendarCompletionState, race] using
    (RawTwoStateCTMC.measurable_stateAt state).comp (measurable_id.prodMk htime)

theorem measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionState
    (state : Fin 2) :
    Measurable (gn21PostThinningRaceAcceptedWinnerRestartCompletionState state) := by
  simpa [gn21PostThinningRaceAcceptedWinnerRestartCompletionState,
    AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).comp
      measurable_snd

theorem measurable_gn21RawPostThinningRaceCalendarCompletionSwitchGaps
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma) := by
  let race := gn21RawPostThinningRaceSeed state sigma
  have hrace : Measurable race :=
    measurable_gn21RawPostThinningRaceSeed state sigma hsigma
  have htime : Measurable (fun seed : GN21RawCycleSeed =>
      (race seed).1 + (race seed).2.2) := by
    exact (measurable_fst.comp hrace).add
      (measurable_snd.comp (measurable_snd.comp hrace))
  have hinput : Measurable (fun seed : GN21RawCycleSeed =>
      (RawTwoStateCTMC.rawSwitchGaps seed,
        (race seed).1 + (race seed).2.2)) :=
    RawTwoStateCTMC.measurable_rawSwitchGaps.prodMk htime
  simpa [gn21RawPostThinningRaceCalendarCompletionSwitchGaps, race] using
    (AppliedModelingLib.Probability.TwoStateSwitching.measurable_switchGapsAfterElapsed
      state).comp hinput

theorem measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps
    (state : Fin 2) :
    Measurable (gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) := by
  simpa [gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps,
    RawTwoStateCTMC.switchGapsAfterPairAtTime] using
    (RawTwoStateCTMC.measurable_switchGapsAfterPairAtTime state).comp measurable_snd

theorem measurable_gn21RawPostThinningRaceCalendarCompletionEndpointFuture
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma) := by
  simpa [gn21RawPostThinningRaceCalendarCompletionEndpointFuture] using
    (measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma).prodMk
      (measurable_gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma hsigma)

theorem measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture
    (state : Fin 2) :
    Measurable (gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state) := by
  simpa [gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture] using
    (measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionState state).prodMk
      (measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state)

/-- On the strict accepted-arrival branch, the calendar-time raw endpoint at
selected-trip completion is pathwise the endpoint of the reassembled literal
switch continuation.  The strict inequality is intentional here: replacing
the paper's weak tie convention by this carrier requires the separate
zero-probability tie bridge. -/
theorem gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (htripDuration : 0 ≤ (gn21RawPostThinningRaceSeed state sigma seed).2.2)
    (hacceptedStrict : (gn21RawPostThinningRaceSeed state sigma seed).1 <
      (gn21RawPostThinningRaceSeed state sigma seed).2.1)
    (hdiv : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps state
          (RawTwoStateCTMC.rawSwitchGaps seed))) atTop atTop) :
    gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
      gn21PostThinningRaceAcceptedWinnerRestartCompletionState state
        (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  have hfactor : RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed =
      (RawTwoStateCTMC.rawSwitchTailPair state seed,
        RawTwoStateCTMC.rawSwitchGaps seed state 0) := by
    apply Prod.ext
    · exact (RawTwoStateCTMC.rawSwitchTailPair_eq_factorTail state seed).symm
    · exact RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd state seed
  simp only [gn21RawPostThinningRaceCalendarCompletionState,
    gn21PostThinningRaceAcceptedWinnerRestartCompletionState,
    gn21RawPostThinningRaceAcceptedWinnerRestartSeed,
    gn21PostThinningRaceAcceptedWinnerRestartFactor,
    gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed,
    gn21RawPostThinningRaceWithSwitchTailSeed,
    gn21RawPostThinningRaceSeed, Function.comp_apply, Function.comp_def,
    AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux]
  rw [hfactor]
  exact RawTwoStateCTMC.stateAt_add_eq_stateAt_prepend_activeResidual_rawSwitchTailPair
    state seed
    (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime (gn21ArrivalClockIndex state)
      state sigma seed)
    (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
    htripDuration hacceptedStrict hdiv

/-- On the strict accepted-arrival branch, the literal future switch streams
at actual calendar completion agree pathwise with the future streams read
from the reassembled accepted-winner continuation. -/
theorem gn21RawPostThinningRaceCalendarCompletionSwitchGaps_eq_acceptedWinnerRestartCompletionSwitchGaps
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (htripDuration : 0 ≤ (gn21RawPostThinningRaceSeed state sigma seed).2.2)
    (hacceptedStrict : (gn21RawPostThinningRaceSeed state sigma seed).1 <
      (gn21RawPostThinningRaceSeed state sigma seed).2.1)
    (hdiv : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps state
          (RawTwoStateCTMC.rawSwitchGaps seed))) atTop atTop) :
    gn21RawPostThinningRaceCalendarCompletionSwitchGaps state sigma seed =
      gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state
        (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  have hfactor : RawTwoStateCTMC.rawSwitchTailAndFirstGap state seed =
      (RawTwoStateCTMC.rawSwitchTailPair state seed,
        RawTwoStateCTMC.rawSwitchGaps seed state 0) := by
    apply Prod.ext
    · exact (RawTwoStateCTMC.rawSwitchTailPair_eq_factorTail state seed).symm
    · exact RawTwoStateCTMC.rawSwitchTailAndFirstGap_snd state seed
  simp only [gn21RawPostThinningRaceCalendarCompletionSwitchGaps,
    gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps,
    gn21RawPostThinningRaceAcceptedWinnerRestartSeed,
    gn21PostThinningRaceAcceptedWinnerRestartFactor,
    gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed,
    gn21RawPostThinningRaceWithSwitchTailSeed,
    gn21RawPostThinningRaceSeed, Function.comp_apply, Function.comp_def,
    AppliedModelingLib.Probability.exponentialRaceLeftWinnerResidualWithLeadingAux]
  rw [hfactor]
  exact RawTwoStateCTMC.switchGapsAfterElapsed_add_eq_switchGapsAfterElapsed_prepend_activeResidual_rawSwitchTailPair
      state seed
      (AcceptedArrivalTime.gn21RawFirstAcceptedArrivalTime (gn21ArrivalClockIndex state)
        state sigma seed)
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed)
      htripDuration hacceptedStrict hdiv

/-- The source weak accepted-winner event is almost surely strict.  This is
the reusable transport of the paper's no-earlier-switch convention through
the already-proved continuous raw race law. -/
theorem ae_gn21RawPostThinningRaceAcceptedStrict_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)),
      (gn21RawPostThinningRaceSeed state sigma seed).1 <
        (gn21RawPostThinningRaceSeed state sigma seed).2.1 := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let strictAccepted : Set GN21RawCycleSeed :=
    {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 <
      (gn21RawPostThinningRaceSeed state sigma seed).2.1}
  let tie : Set GN21RawCycleSeed :=
    {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 =
      (gn21RawPostThinningRaceSeed state sigma seed).2.1}
  have hstrictMeas : MeasurableSet strictAccepted := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt (measurable_fst.comp raceMeas)
      ((measurable_fst.comp measurable_snd).comp raceMeas)
  have hbadEq : Set.inter (gn21RawPostThinningRaceAcceptedFirst state sigma)
      strictAcceptedᶜ = tie := by
    ext seed
    simp only [gn21RawPostThinningRaceAcceptedFirst,
      gn21RawPostThinningRaceSwitchesFirst]
    change (¬ (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
        (gn21RawPostThinningRaceSeed state sigma seed).1 ∧
      ¬ (gn21RawPostThinningRaceSeed state sigma seed).1 <
        (gn21RawPostThinningRaceSeed state sigma seed).2.1) ↔
      (gn21RawPostThinningRaceSeed state sigma seed).1 =
        (gn21RawPostThinningRaceSeed state sigma seed).2.1
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt h.1) (le_of_not_gt h.2)
    · intro h
      rw [h]
      exact ⟨lt_irrefl _, lt_irrefl _⟩
  have hbadZero : (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))
      strictAcceptedᶜ = 0 := by
    calc
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))
          strictAcceptedᶜ = P (strictAcceptedᶜ ∩
            gn21RawPostThinningRaceAcceptedFirst state sigma) := by
              rw [Measure.restrict_apply hstrictMeas.compl]
      _ = P (gn21RawPostThinningRaceAcceptedFirst state sigma ∩ strictAcceptedᶜ) := by
            rw [Set.inter_comm]
      _ = P tie := by
            change P ((gn21RawPostThinningRaceAcceptedFirst state sigma).inter
              strictAcceptedᶜ) = P tie
            exact congrArg P hbadEq
      _ = 0 := by
            simpa [P, tie] using measure_gn21RawPostThinningRaceTie_eq_zero
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hstrictAccepted : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma), seed ∈ strictAccepted := by
    rw [MeasureTheory.ae_iff]
    simpa using hbadZero
  filter_upwards [hstrictAccepted] with seed hstrict
  simpa [strictAccepted] using hstrict

/-- On the strict accepted-arrival carrier, the actual calendar-completion
endpoint and future switch path jointly equal their literal reassembled
continuation counterparts. -/
theorem gn21RawPostThinningRaceCalendarCompletionEndpointFuture_eq_acceptedWinnerRestartCompletionEndpointFuture
    (state : Fin 2) (sigma : TripPolicy) (seed : GN21RawCycleSeed)
    (htripDuration : 0 ≤ (gn21RawPostThinningRaceSeed state sigma seed).2.2)
    (hacceptedStrict : (gn21RawPostThinningRaceSeed state sigma seed).1 <
      (gn21RawPostThinningRaceSeed state sigma seed).2.1)
    (hdiv : Tendsto (fun n : Nat =>
      AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
        (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps state
          (RawTwoStateCTMC.rawSwitchGaps seed))) atTop atTop) :
    gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma seed =
      gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
        (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  apply Prod.ext
  · exact gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion
      state sigma seed htripDuration hacceptedStrict hdiv
  · exact gn21RawPostThinningRaceCalendarCompletionSwitchGaps_eq_acceptedWinnerRestartCompletionSwitchGaps
      state sigma seed htripDuration hacceptedStrict hdiv

/-- Under the source feasibility domain, the actual calendar-completion
endpoint and the literal reassembled-continuation endpoint agree almost
everywhere on the paper's weak accepted-winner event.  The only excluded
boundary is a simultaneous accepted arrival and switch, proved null from the
raw continuous race law above. -/
theorem ae_gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion_restrict
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
        gn21PostThinningRaceAcceptedWinnerRestartCompletionState state
          (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let strictAccepted : Set GN21RawCycleSeed :=
    {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 <
      (gn21RawPostThinningRaceSeed state sigma seed).2.1}
  let tie : Set GN21RawCycleSeed :=
    {seed | (gn21RawPostThinningRaceSeed state sigma seed).1 =
      (gn21RawPostThinningRaceSeed state sigma seed).2.1}
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hselected : HasLaw
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      selectedLaw P := by
    simpa [selectedLaw, P] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ tripDuration ∂selectedLaw, 0 ≤ tripDuration := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun tripDuration hmem => by
        have hpositive : 0 < tripDuration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hrawNonneg : ∀ᵐ seed ∂P,
      0 ≤ (gn21RawPostThinningRaceSeed state sigma seed).2.2 := by
    have hraw : ∀ᵐ seed ∂P,
        0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
      (hselected.ae_iff (p := fun tripDuration : TripLength => 0 ≤ tripDuration)
        (by fun_prop)).mpr hselectedNonneg
    simpa [gn21RawPostThinningRaceSeed] using hraw
  have hrawDiverges : ∀ᵐ seed ∂P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps state
            (RawTwoStateCTMC.rawSwitchGaps seed))) atTop atTop := by
    simpa [P] using RawTwoStateCTMC.ae_tendsto_arrivalTime_rawSwitchGaps
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state
  have hstrictMeas : MeasurableSet strictAccepted := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt (measurable_fst.comp raceMeas)
      ((measurable_fst.comp measurable_snd).comp raceMeas)
  have hbadEq : Set.inter (gn21RawPostThinningRaceAcceptedFirst state sigma)
      strictAcceptedᶜ = tie := by
    ext seed
    simp only [gn21RawPostThinningRaceAcceptedFirst,
      gn21RawPostThinningRaceSwitchesFirst]
    change (¬ (gn21RawPostThinningRaceSeed state sigma seed).2.1 <
        (gn21RawPostThinningRaceSeed state sigma seed).1 ∧
      ¬ (gn21RawPostThinningRaceSeed state sigma seed).1 <
        (gn21RawPostThinningRaceSeed state sigma seed).2.1) ↔
      (gn21RawPostThinningRaceSeed state sigma seed).1 =
        (gn21RawPostThinningRaceSeed state sigma seed).2.1
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt h.1) (le_of_not_gt h.2)
    · intro h
      rw [h]
      exact ⟨lt_irrefl _, lt_irrefl _⟩
  have hbadZero : (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))
      strictAcceptedᶜ = 0 := by
    calc
      (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))
          strictAcceptedᶜ = P (strictAcceptedᶜ ∩
            gn21RawPostThinningRaceAcceptedFirst state sigma) := by
              rw [Measure.restrict_apply hstrictMeas.compl]
      _ = P (gn21RawPostThinningRaceAcceptedFirst state sigma ∩ strictAcceptedᶜ) := by
            rw [Set.inter_comm]
      _ = P tie := by
            change P ((gn21RawPostThinningRaceAcceptedFirst state sigma).inter
              strictAcceptedᶜ) = P tie
            exact congrArg P hbadEq
      _ = 0 := by
            simpa [P, tie] using measure_gn21RawPostThinningRaceTie_eq_zero
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hstrictAccepted : ∀ᵐ seed ∂P.restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma), seed ∈ strictAccepted := by
    rw [MeasureTheory.ae_iff]
    simpa using hbadZero
  filter_upwards [MeasureTheory.ae_restrict_of_ae hrawNonneg,
    MeasureTheory.ae_restrict_of_ae hrawDiverges, hstrictAccepted] with
      seed hnonneg hdiv hstrict
  exact gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion
    state sigma seed hnonneg (by simpa [strictAccepted] using hstrict) hdiv

/-- The actual calendar-completion endpoint and future switch path jointly
agree almost everywhere, on the paper's weak accepted-winner event, with the
corresponding literal reassembled continuation observation. -/
theorem ae_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_eq_acceptedWinnerRestartCompletionEndpointFuture_restrict
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
      gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma seed =
        gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
          (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma seed) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hselected : HasLaw
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma)
      selectedLaw P := by
    simpa [selectedLaw, P] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hselectedNonneg : ∀ᵐ tripDuration ∂selectedLaw, 0 ≤ tripDuration := by
    simpa [selectedLaw] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun tripDuration hmem => by
        have hpositive : 0 < tripDuration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hrawNonneg : ∀ᵐ seed ∂P,
      0 ≤ (gn21RawPostThinningRaceSeed state sigma seed).2.2 := by
    have hraw : ∀ᵐ seed ∂P,
        0 ≤ AcceptedTripSelection.gn21RawFirstAcceptedTripMark state sigma seed :=
      (hselected.ae_iff (p := fun tripDuration : TripLength => 0 ≤ tripDuration)
        (by fun_prop)).mpr hselectedNonneg
    simpa [gn21RawPostThinningRaceSeed] using hraw
  have hrawDiverges : ∀ᵐ seed ∂P,
      Tendsto (fun n : Nat =>
        AppliedModelingLib.Probability.PoissonProcess.arrivalTime n
          (AppliedModelingLib.Probability.TwoStateSwitching.alternatingGaps state
            (RawTwoStateCTMC.rawSwitchGaps seed))) atTop atTop := by
    simpa [P] using RawTwoStateCTMC.ae_tendsto_arrivalTime_rawSwitchGaps
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state
  have hstrict := ae_gn21RawPostThinningRaceAcceptedStrict_restrict
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  filter_upwards [MeasureTheory.ae_restrict_of_ae hrawNonneg,
    MeasureTheory.ae_restrict_of_ae hrawDiverges, hstrict] with
      seed hnonneg hdiv hstrict
  exact gn21RawPostThinningRaceCalendarCompletionEndpointFuture_eq_acceptedWinnerRestartCompletionEndpointFuture
    state sigma seed hnonneg hstrict hdiv

/-- Pushing the actual weak-event completion endpoint/future observation
through the raw source is the same as first taking the literal
accepted-winner restart seed and then reading that observation.  The equality
is a transport through the preceding a.e. path identity, not a conditional
Markov assertion. -/
theorem map_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_restrict_eq_map_restart
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      Measure.map (gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state)
        (Measure.map (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma)
          ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
            (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let restartSeed := gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma
  let restartObservation :=
    gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  have hcalendar :=
    ae_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_eq_acceptedWinnerRestartCompletionEndpointFuture_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  calc
    Measure.map (gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (restartObservation ∘ restartSeed)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) := by
            apply Measure.map_congr
            filter_upwards [hcalendar] with seed hseed
            simpa [restartObservation, restartSeed, Function.comp_def] using hseed
    _ = Measure.map restartObservation
        (Measure.map restartSeed
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
            rw [Measure.map_map
              (measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state)
              (measurable_gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma hsigma)]

/-- Under any independent probability law for the elapsed race time, the
reassembled continuation's completion endpoint and its future switch path
factor exactly.  This is the existing deterministic-time product-space
factorization with the unused elapsed coordinate marginalized out. -/
theorem measure_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture_prod_factor
    (eta : Measure Real) [IsProbabilityMeasure eta]
    (muI muJ : Measure TripLength) (switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (target : Fin 2) (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let tails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    let L := eta.prod (tails.prod Q)
    L (Set.inter
      {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target}
      ((gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) ⁻¹' B)) =
      L {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target} *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let tails : Measure ((Nat -> Real) × (Nat -> Real)) :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let L := eta.prod (tails.prod Q)
  let observation :=
    gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  let pairObservation : ((Nat -> Real) × (Nat -> Real)) × TripLength ->
      (Fin 2) × (Fin 2 -> Nat -> Real) := fun z =>
    (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state (z.1, z.2),
      RawTwoStateCTMC.switchGapsAfterPairAtTime state (z.1, z.2))
  let outputStateEvent : Set ((Fin 2) × (Fin 2 -> Nat -> Real)) :=
    {z | z.1 = target}
  let outputJointEvent : Set ((Fin 2) × (Fin 2 -> Nat -> Real)) :=
    Set.inter outputStateEvent {z | z.2 ∈ B}
  let pairStateEvent : Set (((Nat -> Real) × (Nat -> Real)) × TripLength) :=
    {z | AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state
      (z.1, z.2) = target}
  let pairFuture : ((Nat -> Real) × (Nat -> Real)) × TripLength ->
      Fin 2 -> Nat -> Real := fun z =>
    RawTwoStateCTMC.switchGapsAfterPairAtTime state (z.1, z.2)
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
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
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hQnonneg : ∀ᵐ tripDuration ∂Q, 0 ≤ tripDuration := by
    simpa [Q] using
      (ProbabilityTheory.ae_cond_of_forall_mem hsigma (fun tripDuration hmem => by
        have hpositive : 0 < tripDuration := by
          simpa [acceptAllPolicy, positiveTripLengths,
            AppliedModelingLib.positiveRealAcceptAll] using hsigma_subset hmem
        exact hpositive.le))
  have hpairObservation : Measurable pairObservation := by
    exact
      (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime state).prodMk
        (RawTwoStateCTMC.measurable_switchGapsAfterPairAtTime state)
  have hObservation : Measurable observation :=
    measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  have hOutputStateEvent : MeasurableSet outputStateEvent :=
    measurable_fst (measurableSet_singleton target)
  have hOutputJointEvent : MeasurableSet outputJointEvent :=
    hOutputStateEvent.inter (measurable_snd hB)
  have hObservationComp : observation = pairObservation ∘ Prod.snd := by
    rfl
  have hMapObservation : Measure.map observation L =
      Measure.map pairObservation (tails.prod Q) := by
    calc
      Measure.map observation L = Measure.map (pairObservation ∘ Prod.snd) L := by
        rw [hObservationComp]
      _ = Measure.map pairObservation (Measure.map Prod.snd L) := by
        rw [Measure.map_map hpairObservation measurable_snd]
      _ = Measure.map pairObservation (tails.prod Q) := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hObservationStatePreimage : observation ⁻¹' outputStateEvent =
      {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target} := by
    rfl
  have hObservationJointPreimage : observation ⁻¹' outputJointEvent = Set.inter
      {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target}
      ((gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) ⁻¹' B) := by
    rfl
  have hPairStatePreimage : pairObservation ⁻¹' outputStateEvent = pairStateEvent := by
    rfl
  have hPairJointPreimage : pairObservation ⁻¹' outputJointEvent =
      Set.inter pairStateEvent (pairFuture ⁻¹' B) := by
    rfl
  have hEndpoint : L
      {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target} =
      (tails.prod Q) pairStateEvent := by
    calc
      L {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target} =
          L (observation ⁻¹' outputStateEvent) := by rw [hObservationStatePreimage]
      _ = (Measure.map observation L) outputStateEvent := by
          exact (Measure.map_apply hObservation hOutputStateEvent).symm
      _ = (Measure.map pairObservation (tails.prod Q)) outputStateEvent := by
          rw [hMapObservation]
      _ = (tails.prod Q) (pairObservation ⁻¹' outputStateEvent) := by
          exact Measure.map_apply hpairObservation hOutputStateEvent
      _ = (tails.prod Q) pairStateEvent := by rw [hPairStatePreimage]
  have hJoint : L (Set.inter
      {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target}
      ((gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) ⁻¹' B)) =
      (tails.prod Q) (Set.inter pairStateEvent (pairFuture ⁻¹' B)) := by
    calc
      L (Set.inter
          {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target}
          ((gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) ⁻¹' B)) =
          L (observation ⁻¹' outputJointEvent) := by rw [hObservationJointPreimage]
      _ = (Measure.map observation L) outputJointEvent := by
          exact (Measure.map_apply hObservation hOutputJointEvent).symm
      _ = (Measure.map pairObservation (tails.prod Q)) outputJointEvent := by
          rw [hMapObservation]
      _ = (tails.prod Q) (pairObservation ⁻¹' outputJointEvent) := by
          exact Measure.map_apply hpairObservation hOutputJointEvent
      _ = (tails.prod Q) (Set.inter pairStateEvent (pairFuture ⁻¹' B)) := by
          rw [hPairJointPreimage]
  have hFactor := RawTwoStateCTMC.measure_stateAtPairAtTime_switchGapsAfter_prod_factor
    switchIJ switchJI hswitchIJ hswitchJI Q id measurable_id hQnonneg state target B hB
  calc
    L (Set.inter
        {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target}
        ((gn21PostThinningRaceAcceptedWinnerRestartCompletionSwitchGaps state) ⁻¹' B)) =
        (tails.prod Q) (Set.inter pairStateEvent (pairFuture ⁻¹' B)) := hJoint
    _ = (tails.prod Q) pairStateEvent *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          simpa [tails, Q, pairStateEvent, pairFuture,
            RawTwoStateCTMC.switchGapsAfterPairAtTime] using hFactor
    _ = L {restart | gn21PostThinningRaceAcceptedWinnerRestartCompletionState state restart = target} *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [← hEndpoint]

/-- On the accepted-winner branch, reattaching the active switch residual to
its literal tail restores the original two-switch-stream law.  The elapsed
open-state holding time remains independent of that continuation and of the
selected conditional trip length.  This is an unnormalized restricted law,
with exactly the accepted-winner probability as its scalar. -/
theorem map_gn21RawPostThinningRaceAcceptedWinnerRestartSeed_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma)
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
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI)).prod
            (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let switchClock := RawTwoStateCTMC.switchClockIndex state
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let elapsed := ProbabilityTheory.expMeasure
    (clockRate (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma + clockRate switchClock)
  let residual := ProbabilityTheory.expMeasure (clockRate switchClock)
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have harrivalRate : 0 < clockRate (gn21ArrivalClockIndex state) := by
    dsimp [clockRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < clockRate switchClock := by
    dsimp [clockRate, switchClock, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < clockRate (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma := by
    exact mul_pos harrivalRate hmass
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
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
  letI : IsProbabilityMeasure elapsed := by
    dsimp [elapsed]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure
      (add_pos hacceptedRate hswitchRate)
  letI : IsProbabilityMeasure residual := by
    dsimp [residual]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gn21AcceptedTripLaw_isProbability (gn21CycleMarkLaw muI muJ state) sigma hmass
  let join := AppliedModelingLib.Probability.PoissonProcess.twoStreamPrependActiveHeadFromHeadTail
    state
  let inner : Real × (((Nat -> Real) × (Nat -> Real)) × TripLength) ->
      ((Nat -> Real) × (Nat -> Real)) × TripLength := fun z =>
    (join (z.1, z.2.1), z.2.2)
  have hjoin : Measure.map join (residual.prod tails) = tails := by
    fin_cases state
    · simpa [join, residual, tails, clockRate, switchClock,
        RawTwoStateCTMC.switchClockIndex, gn21CycleClockRate] using
        (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamPrependActiveHeadFromHeadTail
          0 hswitchIJ hswitchJI)
    · simpa [join, residual, tails, clockRate, switchClock,
        RawTwoStateCTMC.switchClockIndex, gn21CycleClockRate] using
        (AppliedModelingLib.Probability.PoissonProcess.map_twoStreamPrependActiveHeadFromHeadTail
          1 hswitchIJ hswitchJI)
  have hinnerMeas : Measurable inner := by
    exact ((AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamPrependActiveHeadFromHeadTail
      state).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hinner : Measure.map inner (residual.prod (tails.prod Q)) = tails.prod Q := by
    have hassoc := (measurePreserving_prodAssoc residual tails Q).symm.hasLaw
    have hjoinMeas := AppliedModelingLib.Probability.PoissonProcess.measurable_twoStreamPrependActiveHeadFromHeadTail
      state
    rw [show inner = (Prod.map join id) ∘ MeasurableEquiv.prodAssoc.symm by rfl,
      ← Measure.map_map (hjoinMeas.prodMap measurable_id)
        MeasurableEquiv.prodAssoc.symm.measurable,
      hassoc.map_eq,
      ← Measure.map_prod_map (residual.prod tails) Q hjoinMeas measurable_id,
      hjoin, Measure.map_id]
  have hfactor : Measure.map (gn21PostThinningRaceAcceptedWinnerRestartFactor state)
      (elapsed.prod (residual.prod (tails.prod Q))) = elapsed.prod (tails.prod Q) := by
    rw [show gn21PostThinningRaceAcceptedWinnerRestartFactor state = Prod.map id inner by rfl,
      ← Measure.map_prod_map elapsed (residual.prod (tails.prod Q)) measurable_id hinnerMeas,
      Measure.map_id, hinner]
  calc
    Measure.map (gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (gn21PostThinningRaceAcceptedWinnerRestartFactor state)
          (Measure.map (gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma)
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [show gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma =
                gn21PostThinningRaceAcceptedWinnerRestartFactor state ∘
                  gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed state sigma by rfl,
                Measure.map_map
                  (measurable_gn21PostThinningRaceAcceptedWinnerRestartFactor state)
                  (measurable_gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed
                    state sigma hsigma)]
    _ = Measure.map (gn21PostThinningRaceAcceptedWinnerRestartFactor state)
        (ENNReal.ofReal
          (clockRate (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma /
            (clockRate (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              clockRate switchClock)) •
          (elapsed.prod (residual.prod (tails.prod Q)))) := by
            rw [map_gn21RawPostThinningRaceAcceptedWinnerTailResidualSeed_restrict
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass]
    _ = ENNReal.ofReal
          (clockRate (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma /
            (clockRate (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              clockRate switchClock)) •
        (elapsed.prod (tails.prod Q)) := by
          rw [Measure.map_smul, hfactor]
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        ((ProbabilityTheory.expMeasure
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))).prod
          (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchIJ).prod
              (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
              rfl

/-- The actual raw calendar endpoint at accepted-trip completion has the
source-derived accepted-winner product law.  This transports the literal
reassembled continuation law through the a.e. calendar-path identification;
the weak tie convention has already been discharged by the preceding
tie-null bridge. -/
theorem map_gn21RawPostThinningRaceCalendarCompletionState_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceCalendarCompletionState state sigma)
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
        Measure.map (gn21PostThinningRaceAcceptedWinnerRestartCompletionState state)
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let restartSeed := gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma
  let restartCompletion := gn21PostThinningRaceAcceptedWinnerRestartCompletionState state
  have hcalendar :=
    ae_gn21RawPostThinningRaceCalendarCompletion_eq_acceptedWinnerRestartCompletion_restrict
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hrestart := map_gn21RawPostThinningRaceAcceptedWinnerRestartSeed_restrict
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  calc
    Measure.map (gn21RawPostThinningRaceCalendarCompletionState state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map (restartCompletion ∘ restartSeed)
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) := by
            apply Measure.map_congr
            filter_upwards [hcalendar] with seed hseed
            simpa [restartCompletion, restartSeed, Function.comp_def] using hseed
    _ = Measure.map restartCompletion
        (Measure.map restartSeed
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
            rw [Measure.map_map
              (measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionState state)
              (measurable_gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma hsigma)]
    _ = Measure.map restartCompletion
        (ENNReal.ofReal
          ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))) •
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))) := by
            simpa [P, restartSeed] using congrArg (Measure.map restartCompletion) hrestart
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        Measure.map restartCompletion
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
            rw [Measure.map_smul]
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        Measure.map (gn21PostThinningRaceAcceptedWinnerRestartCompletionState state)
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
              rfl

/-- On the accepted-winner branch, the literal calendar-completion endpoint
has the same normalized law as the raw alternating path at the selected trip
duration.  The elapsed race coordinate is irrelevant after the residual
switch path has been reassembled. -/
theorem map_gn21RawPostThinningRaceCalendarCompletionState_restrict_eq_rawTripCompletion
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (gn21RawPostThinningRaceCalendarCompletionState state sigma)
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
        Measure.map (RawTwoStateCTMC.stateAtFirstAcceptedTripCompletion state state sigma)
          (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let acceptedRate :=
    clockRate (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
  let elapsed := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let restartCompletion := gn21PostThinningRaceAcceptedWinnerRestartCompletionState state
  let rawCompletion := RawTwoStateCTMC.stateAtFirstAcceptedTripCompletion state state sigma
  have harrivalRate : 0 < clockRate (gn21ArrivalClockIndex state) := by
    dsimp [clockRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [clockRate, switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos harrivalRate hmass
  letI : IsProbabilityMeasure elapsed := by
    dsimp [elapsed]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure
      (add_pos hacceptedRate hswitchRate)
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
  letI : IsProbabilityMeasure tails := by
    dsimp [tails]
    infer_instance
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact gn21AcceptedTripLaw_isProbability _ _ hmass
  have hcalendar := map_gn21RawPostThinningRaceCalendarCompletionState_restrict
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hrestart :
      Measure.map restartCompletion (elapsed.prod (tails.prod selectedLaw)) =
        Measure.map rawCompletion P := by
    calc
      Measure.map restartCompletion (elapsed.prod (tails.prod selectedLaw)) =
          Measure.map
            (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state)
            (Measure.map Prod.snd (elapsed.prod (tails.prod selectedLaw))) := by
              rw [Measure.map_map
                (AppliedModelingLib.Probability.TwoStateSwitching.measurable_stateAtPairAtTime
                  state)
                measurable_snd]
              rfl
      _ = Measure.map
          (AppliedModelingLib.Probability.TwoStateSwitching.stateAtPairAtTime state)
          (tails.prod selectedLaw) := by
            rw [Measure.map_snd_prod]
            simp
      _ = Measure.map rawCompletion P := by
            have hraw := RawTwoStateCTMC.stateAtFirstAcceptedTripCompletion_hasLaw_raw_product
              muI muJ arrivalI arrivalJ switchIJ switchJI
              harrivalI harrivalJ hswitchIJ hswitchJI state state sigma hsigma hmass
            simpa [tails, selectedLaw, rawCompletion, P] using hraw.map_eq.symm
  calc
    Measure.map (gn21RawPostThinningRaceCalendarCompletionState state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
          Measure.map restartCompletion (elapsed.prod (tails.prod selectedLaw)) := by
            simpa [P, clockRate, acceptedRate, switchRate, elapsed, tails,
              selectedLaw, restartCompletion] using hcalendar
    _ = ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        Measure.map rawCompletion P := by rw [hrestart]
    _ = _ := by rfl

/-- The accepted-winner calendar-completion endpoint has the source CTMC
transition kernel, multiplied by the accepted-winner probability. -/
theorem measure_gn21RawPostThinningRaceCalendarCompletionState_restrict_toReal_eq_kernel
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state target : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)
      {seed | gn21RawPostThinningRaceCalendarCompletionState state sigma seed = target}).toReal =
      ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) *
        ∫ t, AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t state target
          ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let acceptedRate :=
    clockRate (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
  let calendarCompletion := gn21RawPostThinningRaceCalendarCompletionState state sigma
  let rawCompletion := RawTwoStateCTMC.stateAtFirstAcceptedTripCompletion state state sigma
  have harrivalRate : 0 < clockRate (gn21ArrivalClockIndex state) := by
    dsimp [clockRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos harrivalRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [clockRate, switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hratio_nonneg : 0 ≤ acceptedRate / (acceptedRate + switchRate) :=
    le_of_lt (div_pos hacceptedRate (add_pos hacceptedRate hswitchRate))
  have hcalendar :=
    map_gn21RawPostThinningRaceCalendarCompletionState_restrict_eq_rawTripCompletion
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hcalendarMeas : Measurable calendarCompletion :=
    measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma
  have hrawMeas : Measurable rawCompletion :=
    RawTwoStateCTMC.measurable_stateAtFirstAcceptedTripCompletion state state sigma hsigma
  have hrawKernel :=
    RawTwoStateCTMC.measure_stateAtFirstAcceptedTripCompletion_toReal_eq_integral_kernel
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state state target sigma hsigma hsigma_subset hmass
  calc
    ((P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)
        {seed | calendarCompletion seed = target}).toReal) =
        ((Measure.map calendarCompletion
          (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) {target}).toReal := by
            congr 1
            rw [Measure.map_apply hcalendarMeas (measurableSet_singleton _)]
            rfl
    _ = (ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) *
        P {seed | rawCompletion seed = target}).toReal := by
          rw [hcalendar, Measure.smul_apply,
            Measure.map_apply hrawMeas (measurableSet_singleton _)]
          rfl
    _ = (acceptedRate / (acceptedRate + switchRate)) *
        (P {seed | rawCompletion seed = target}).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hratio_nonneg]
    _ = (acceptedRate / (acceptedRate + switchRate)) *
        ∫ t, AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t state target
          ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
            rw [hrawKernel]
    _ = _ := by rfl

/-- The accepted-winner probability of exiting the current state is the
accepted-winner probability times the paper's conditional switch integral. -/
theorem measure_gn21RawPostThinningRaceCalendarCompletionOther_restrict_toReal
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
      (gn21RawPostThinningRaceAcceptedFirst state sigma)
      {seed | gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState state}).toReal =
      ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) *
        ∫ t, gn21SwitchProb
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))) t
          ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  have hkernel : (fun t =>
      AppliedModelingLib.twoStateCtmcTransitionProb switchIJ switchJI t state
        (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)) =
      (fun t => gn21SwitchProb
        (clockRate (RawTwoStateCTMC.switchClockIndex state))
        (clockRate (RawTwoStateCTMC.switchClockIndex
          (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))) t) := by
    funext t
    fin_cases state <;>
      simp [clockRate, gn21CycleClockRate, RawTwoStateCTMC.switchClockIndex,
        AppliedModelingLib.Probability.TwoStateSwitching.otherState, gn21SwitchProb,
        AppliedModelingLib.twoStateCtmcTransitionProb]
  have hcalendar :=
    measure_gn21RawPostThinningRaceCalendarCompletionState_restrict_toReal_eq_kernel
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state
      (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)
      sigma hsigma hsigma_subset hmass
  rw [hkernel] at hcalendar
  simpa [clockRate] using hcalendar

/-- The literal event that one open-state subcycle exits its current state:
either the open-state switch wins the race, or an accepted trip completes in
the other state. -/
def gn21RawPostThinningRaceExitState
    (state : Fin 2) (sigma : TripPolicy) : Set GN21RawCycleSeed :=
  gn21RawPostThinningRaceSwitchesFirst state sigma ∪
    (gn21RawPostThinningRaceAcceptedFirst state sigma ∩
      {seed | gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState state})

/-- The literal raw subcycle-exit event is measurable.  This exposes the
event as a valid IID first-hit target for the finite-horizon renewal layer;
it does not yet assert a restarted global source path. -/
theorem measurableSet_gn21RawPostThinningRaceExitState
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21RawPostThinningRaceExitState state sigma) := by
  have hswitch : MeasurableSet (gn21RawPostThinningRaceSwitchesFirst state sigma) := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have haccepted : MeasurableSet (gn21RawPostThinningRaceAcceptedFirst state sigma) := by
    simpa [gn21RawPostThinningRaceAcceptedFirst,
      gn21RawPostThinningRaceSwitchesFirst] using hswitch.compl
  have hcompletion : MeasurableSet
      {seed | gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
        AppliedModelingLib.Probability.TwoStateSwitching.otherState state} :=
    (measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma)
      (measurableSet_singleton _)
  exact hswitch.union (haccepted.inter hcompletion)

/-- The literal raw exit event has the competing-race plus conditional-CTMC
probability used in the source subcycle calculation. -/
theorem measure_gn21RawPostThinningRaceExitState_toReal
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState state sigma)).toReal =
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) +
      ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) *
        ∫ t, gn21SwitchProb
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))) t
          ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let switchEvent := gn21RawPostThinningRaceSwitchesFirst state sigma
  let acceptedEvent := gn21RawPostThinningRaceAcceptedFirst state sigma
  let completionEvent : Set GN21RawCycleSeed :=
    {seed | gn21RawPostThinningRaceCalendarCompletionState state sigma seed =
      AppliedModelingLib.Probability.TwoStateSwitching.otherState state}
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let acceptedRate := clockRate (gn21ArrivalClockIndex state) *
    singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have harrivalRate : 0 < clockRate (gn21ArrivalClockIndex state) := by
    dsimp [clockRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos harrivalRate hmass
  have hswitchRate : 0 < switchRate := by
    dsimp [clockRate, switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hswitchRatio_nonneg : 0 ≤ switchRate / (acceptedRate + switchRate) :=
    le_of_lt (div_pos hswitchRate (add_pos hacceptedRate hswitchRate))
  have hswitchMeas : MeasurableSet switchEvent := by
    let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    exact measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)
  have hcompletion : MeasurableSet completionEvent := by
    exact (measurable_gn21RawPostThinningRaceCalendarCompletionState state sigma hsigma)
      (measurableSet_singleton _)
  have hacceptedCompletion : MeasurableSet (acceptedEvent ∩ completionEvent) := by
    simpa [acceptedEvent, gn21RawPostThinningRaceAcceptedFirst] using
      hswitchMeas.compl.inter hcompletion
  have hdisjoint : Disjoint switchEvent (acceptedEvent ∩ completionEvent) := by
    refine Set.disjoint_left.2 ?_
    intro seed hswitch haccepted
    exact haccepted.1 (by simpa [acceptedEvent,
      gn21RawPostThinningRaceAcceptedFirst] using hswitch)
  have hunion :
      P (gn21RawPostThinningRaceExitState state sigma) =
        P switchEvent + P (acceptedEvent ∩ completionEvent) := by
    simpa [gn21RawPostThinningRaceExitState, switchEvent, acceptedEvent,
      completionEvent] using (measure_union hdisjoint hacceptedCompletion)
  have haccepted :
      (P (acceptedEvent ∩ completionEvent)).toReal =
        (acceptedRate / (acceptedRate + switchRate)) *
          ∫ t, gn21SwitchProb
            (clockRate (RawTwoStateCTMC.switchClockIndex state))
            (clockRate (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state))) t
            ∂(gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
    have hrestrict : P (acceptedEvent ∩ completionEvent) =
        (P.restrict acceptedEvent) completionEvent := by
          rw [Measure.restrict_apply hcompletion]
          simp only [Set.inter_comm]
    rw [hrestrict]
    simpa [P, acceptedEvent, completionEvent, clockRate, acceptedRate, switchRate] using
      (measure_gn21RawPostThinningRaceCalendarCompletionOther_restrict_toReal
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hswitch : (P switchEvent).toReal = switchRate / (acceptedRate + switchRate) := by
    calc
      (P switchEvent).toReal =
          (ENNReal.ofReal (switchRate / (acceptedRate + switchRate))).toReal := by
            simpa [P, switchEvent, clockRate, switchRate, acceptedRate] using
              congrArg ENNReal.toReal
                (measure_gn21RawPostThinningRaceSwitchesFirst
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
      _ = switchRate / (acceptedRate + switchRate) :=
        ENNReal.toReal_ofReal hswitchRatio_nonneg
  calc
    (P (gn21RawPostThinningRaceExitState state sigma)).toReal =
        (P switchEvent + P (acceptedEvent ∩ completionEvent)).toReal := by rw [hunion]
    _ = (P switchEvent).toReal + (P (acceptedEvent ∩ completionEvent)).toReal := by
          rw [ENNReal.toReal_add (measure_ne_top P switchEvent)
            (measure_ne_top P (acceptedEvent ∩ completionEvent))]
    _ = _ := by rw [hswitch, haccepted]

/-- For state `0`, the literal raw subcycle exit event is exactly the
Appendix-D cross-subcycle probability. -/
theorem measure_gn21RawPostThinningRaceExitState_zero_toReal_eq_crossSubcycleProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass muI sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState 0 sigma)).toReal =
      gn21CrossSubcycleProb arrivalI (singleStateTripMass muI sigma) switchIJ
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigma) := by
  have hden : arrivalI * singleStateTripMass muI sigma + switchIJ ≠ 0 :=
    ne_of_gt (add_pos (mul_pos harrivalI hmass) hswitchIJ)
  calc
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState 0 sigma)).toReal =
        switchIJ / (arrivalI * singleStateTripMass muI sigma + switchIJ) +
          (arrivalI * singleStateTripMass muI sigma /
            (arrivalI * singleStateTripMass muI sigma + switchIJ)) *
            ∫ t, gn21SwitchProb switchIJ switchJI t
              ∂(gn21AcceptedTripLaw muI sigma) := by
              simpa [gn21CycleMarkLaw, gn21CycleClockRate, gn21ArrivalClockIndex,
                RawTwoStateCTMC.switchClockIndex,
                AppliedModelingLib.Probability.TwoStateSwitching.otherState] using
                (measure_gn21RawPostThinningRaceExitState_toReal
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI 0 sigma hsigma hsigma_subset
                  (by simpa [gn21CycleMarkLaw] using hmass))
    _ = gn21CrossSubcycleProb arrivalI (singleStateTripMass muI sigma) switchIJ
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigma) := by
          exact gn21_cross_subcycle_probability_from_post_thinning_components
            muI arrivalI switchIJ switchJI sigma hmass hden

/-- For state `1`, the literal raw subcycle exit event is exactly the
Appendix-D cross-subcycle probability with the two state labels exchanged. -/
theorem measure_gn21RawPostThinningRaceExitState_one_toReal_eq_crossSubcycleProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass muJ sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState 1 sigma)).toReal =
      gn21CrossSubcycleProb arrivalJ (singleStateTripMass muJ sigma) switchJI
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigma) := by
  have hden : arrivalJ * singleStateTripMass muJ sigma + switchJI ≠ 0 :=
    ne_of_gt (add_pos (mul_pos harrivalJ hmass) hswitchJI)
  calc
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState 1 sigma)).toReal =
        switchJI / (arrivalJ * singleStateTripMass muJ sigma + switchJI) +
          (arrivalJ * singleStateTripMass muJ sigma /
            (arrivalJ * singleStateTripMass muJ sigma + switchJI)) *
            ∫ t, gn21SwitchProb switchJI switchIJ t
              ∂(gn21AcceptedTripLaw muJ sigma) := by
              simpa [gn21CycleMarkLaw, gn21CycleClockRate, gn21ArrivalClockIndex,
                RawTwoStateCTMC.switchClockIndex,
                AppliedModelingLib.Probability.TwoStateSwitching.otherState] using
                (measure_gn21RawPostThinningRaceExitState_toReal
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI 1 sigma hsigma hsigma_subset
                  (by simpa [gn21CycleMarkLaw] using hmass))
    _ = gn21CrossSubcycleProb arrivalJ (singleStateTripMass muJ sigma) switchJI
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigma) := by
          exact gn21_cross_subcycle_probability_from_post_thinning_components
            muJ arrivalJ switchJI switchIJ sigma hmass hden

/-- The actual raw calendar-completion endpoint and the literal future
alternating switch path have the accepted-winner continuation law.  This
transports the reassembled residual/tail law through the almost-everywhere
calendar-path identity; it is an equality of the unnormalized restricted
source law, not a conditional Markov assertion. -/
theorem map_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    let acceptedRate :=
      clockRate (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
    let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
    let elapsed := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
    let tails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
    Measure.map (gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma)
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI).restrict
        (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
      ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate)) •
        Measure.map (gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state)
          (elapsed.prod (tails.prod selectedLaw)) := by
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let restartSeed := gn21RawPostThinningRaceAcceptedWinnerRestartSeed state sigma
  let restartObservation :=
    gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  have hcalendar :=
    map_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_restrict_eq_map_restart
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have hrestart := map_gn21RawPostThinningRaceAcceptedWinnerRestartSeed_restrict
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  calc
    Measure.map (gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma)
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map restartObservation
          (Measure.map restartSeed
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              simpa [P, restartSeed, restartObservation] using hcalendar
    _ = Measure.map restartObservation
        (ENNReal.ofReal
          ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))) •
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)))) := by
                simpa [P, restartSeed] using congrArg (Measure.map restartObservation) hrestart
    _ = ENNReal.ofReal
          ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
            (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (gn21ArrivalClockIndex state) *
              singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
              gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                (RawTwoStateCTMC.switchClockIndex state))) •
        Measure.map restartObservation
          ((ProbabilityTheory.expMeasure
              (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (gn21ArrivalClockIndex state) *
                singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
                gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
                  (RawTwoStateCTMC.switchClockIndex state))).prod
            (((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchIJ).prod
                (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
                  switchJI)).prod
              (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma))) := by
                rw [Measure.map_smul]
    _ = _ := by rfl

/-- On the actual raw accepted-winner branch, the calendar-completion state and
the literal future alternating switch path factor exactly.  The first factor
is the raw completion-state mass and the second is the original two-stream
switch-path law. -/
theorem measure_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_prod_factor
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (target : Fin 2) (B : Set (Fin 2 -> Nat -> Real)) (hB : MeasurableSet B) :
    let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
    let restrictedLaw := P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)
    let observation := gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma
    let stateEvent : Set (Fin 2 × (Fin 2 -> Nat -> Real)) :=
      {outcome | outcome.1 = target}
    let jointEvent : Set (Fin 2 × (Fin 2 -> Nat -> Real)) :=
      Set.inter stateEvent {outcome | outcome.2 ∈ B}
    let tails :=
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
        (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
    restrictedLaw (observation ⁻¹' jointEvent) =
      restrictedLaw (observation ⁻¹' stateEvent) *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
  classical
  dsimp
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let restrictedLaw := P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)
  let rawObservation := gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma
  let restartObservation :=
    gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  let stateEvent : Set (Fin 2 × (Fin 2 -> Nat -> Real)) :=
    {outcome | outcome.1 = target}
  let jointEvent : Set (Fin 2 × (Fin 2 -> Nat -> Real)) :=
    Set.inter stateEvent {outcome | outcome.2 ∈ B}
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let acceptedRate :=
    clockRate (gn21ArrivalClockIndex state) *
      singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let switchRate := clockRate (RawTwoStateCTMC.switchClockIndex state)
  let elapsed := ProbabilityTheory.expMeasure (acceptedRate + switchRate)
  let tails :=
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchIJ).prod
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure switchJI)
  let selectedLaw := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  let continuationLaw := elapsed.prod (tails.prod selectedLaw)
  let acceptedMass : ENNReal := ENNReal.ofReal (acceptedRate / (acceptedRate + switchRate))
  have harrivalRate : 0 < clockRate (gn21ArrivalClockIndex state) := by
    dsimp [clockRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [clockRate, switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hacceptedRate : 0 < acceptedRate := by
    exact mul_pos harrivalRate hmass
  letI : IsProbabilityMeasure elapsed := by
    dsimp [elapsed]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure
      (add_pos hacceptedRate hswitchRate)
  have hstateEvent : MeasurableSet stateEvent := by
    change MeasurableSet (Prod.fst ⁻¹' ({target} : Set (Fin 2)))
    exact (measurableSet_singleton _).preimage measurable_fst
  have hfutureEvent : MeasurableSet {outcome : Fin 2 × (Fin 2 -> Nat -> Real) | outcome.2 ∈ B} := by
    change MeasurableSet (Prod.snd ⁻¹' B)
    exact hB.preimage measurable_snd
  have hjointEvent : MeasurableSet jointEvent := hstateEvent.inter hfutureEvent
  have hrawObservation : Measurable rawObservation :=
    measurable_gn21RawPostThinningRaceCalendarCompletionEndpointFuture state sigma hsigma
  have hrestartObservation : Measurable restartObservation :=
    measurable_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture state
  have hrawMap : Measure.map rawObservation restrictedLaw =
      acceptedMass • Measure.map restartObservation continuationLaw := by
    simpa [P, restrictedLaw, rawObservation, restartObservation, acceptedMass,
      continuationLaw, selectedLaw, tails, elapsed, acceptedRate, switchRate, clockRate] using
      (map_gn21RawPostThinningRaceCalendarCompletionEndpointFuture_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  have hrestartFactor :
      continuationLaw (restartObservation ⁻¹' jointEvent) =
        continuationLaw (restartObservation ⁻¹' stateEvent) *
          tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
    simpa [continuationLaw, selectedLaw, tails, elapsed, restartObservation,
      jointEvent, stateEvent] using
      (measure_gn21PostThinningRaceAcceptedWinnerRestartCompletionEndpointFuture_prod_factor
        elapsed muI muJ switchIJ switchJI hswitchIJ hswitchJI state sigma hsigma
        hsigma_subset hmass target B hB)
  calc
    restrictedLaw (rawObservation ⁻¹' jointEvent) =
        (Measure.map rawObservation restrictedLaw) jointEvent := by
          exact (Measure.map_apply hrawObservation hjointEvent).symm
    _ = (acceptedMass • Measure.map restartObservation continuationLaw) jointEvent := by
          rw [hrawMap]
    _ = acceptedMass * (Measure.map restartObservation continuationLaw) jointEvent := by
          rw [Measure.smul_apply, smul_eq_mul]
    _ = acceptedMass * continuationLaw (restartObservation ⁻¹' jointEvent) := by
          rw [Measure.map_apply hrestartObservation hjointEvent]
    _ = acceptedMass *
        (continuationLaw (restartObservation ⁻¹' stateEvent) *
          tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B)) := by
          rw [hrestartFactor]
    _ = (acceptedMass * continuationLaw (restartObservation ⁻¹' stateEvent)) *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [mul_assoc]
    _ = (acceptedMass • Measure.map restartObservation continuationLaw) stateEvent *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [Measure.smul_apply, smul_eq_mul,
            Measure.map_apply hrestartObservation hstateEvent]
    _ = (Measure.map rawObservation restrictedLaw) stateEvent *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [hrawMap]
    _ = restrictedLaw (rawObservation ⁻¹' stateEvent) *
        tails (AppliedModelingLib.Probability.TwoStateSwitching.twoStateGapsOfPair ⁻¹' B) := by
          rw [Measure.map_apply hrawObservation hstateEvent]

/-- The literal raw accepted-winner carrier is measurable.  It is the event
on which a selected trip contributes time and earnings to one open-state
subcycle. -/
theorem measurableSet_gn21RawPostThinningRaceAcceptedFirst
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet (gn21RawPostThinningRaceAcceptedFirst state sigma) := by
  let raceMeas := measurable_gn21RawPostThinningRaceSeed state sigma hsigma
  simpa [gn21RawPostThinningRaceAcceptedFirst,
    gn21RawPostThinningRaceSwitchesFirst] using
    (measurableSet_lt ((measurable_fst.comp measurable_snd).comp raceMeas)
      (measurable_fst.comp raceMeas)).compl

/-- The realized contribution of a selected trip to one literal subcycle:
it is paid only when the accepted request wins the open-state race. -/
noncomputable def gn21RawPostThinningRaceAcceptedContribution
    (state : Fin 2) (sigma : TripPolicy) (f : TripLength -> Real) :
    GN21RawCycleSeed -> Real :=
  (gn21RawPostThinningRaceAcceptedFirst state sigma).indicator
    (fun seed => f ((gn21RawPostThinningRaceSeed state sigma seed).2.2))

theorem measurable_gn21RawPostThinningRaceAcceptedContribution
    (state : Fin 2) (sigma : TripPolicy) (f : TripLength -> Real)
    (hsigma : MeasurableSet sigma) (hf : Measurable f) :
    Measurable (gn21RawPostThinningRaceAcceptedContribution state sigma f) := by
  let selected : GN21RawCycleSeed -> TripLength := fun seed =>
    (gn21RawPostThinningRaceSeed state sigma seed).2.2
  have hselected : Measurable selected :=
    (measurable_snd.comp (measurable_snd.comp
      (measurable_gn21RawPostThinningRaceSeed state sigma hsigma)))
  have haccepted : MeasurableSet (gn21RawPostThinningRaceAcceptedFirst state sigma) :=
    measurableSet_gn21RawPostThinningRaceAcceptedFirst state sigma hsigma
  simpa [gn21RawPostThinningRaceAcceptedContribution, selected] using
    (hf.comp hselected).indicator haccepted

/-- Under the literal accepted-winner restriction, the selected-trip mark has
the accepted conditional law, multiplied by the literal accepted-winner
probability.  This is an unnormalized event-law identity, not a new
conditioning assumption. -/
theorem map_gn21RawPostThinningRaceSelectedTripMark_restrict
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Measure.map (fun seed => (gn21RawPostThinningRaceSeed state sigma seed).2.2)
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
        gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let residual := gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma
  let selected : GN21RawCycleSeed -> TripLength := fun seed =>
    (gn21RawPostThinningRaceSeed state sigma seed).2.2
  let project : GN21PostThinningRaceSeed -> TripLength := fun z => z.2.2
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let T := ProbabilityTheory.expMeasure (arrivalRate * mass + switchRate)
  let S := ProbabilityTheory.expMeasure switchRate
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  letI : IsProbabilityMeasure (gn21CycleMarkLaw muI muJ state) := by
    dsimp [gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure T := by
    simpa [T] using ProbabilityTheory.isProbabilityMeasure_expMeasure
      (add_pos (mul_pos harrivalRate (by simpa [mass] using hmass)) hswitchRate)
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitchRate
  letI : IsProbabilityMeasure Q := by
    simpa [Q] using gn21AcceptedTripLaw_isProbability
      (gn21CycleMarkLaw muI muJ state) sigma hmass
  have hresidual : Measurable residual :=
    measurable_gn21RawPostThinningRaceAcceptedWinnerResidualSeed state sigma hsigma
  have hproject : Measurable project :=
    measurable_snd.comp measurable_snd
  have hlaw := map_gn21RawPostThinningRaceAcceptedWinnerResidualSeed_restrict
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hprojectLaw : Measure.map project (T.prod (S.prod Q)) = Q := by
    calc
      Measure.map project (T.prod (S.prod Q)) =
          Measure.map Prod.snd (Measure.map Prod.snd (T.prod (S.prod Q))) := by
            rw [Measure.map_map measurable_snd measurable_snd]
            rfl
      _ = Q := by
        rw [Measure.map_snd_prod, measure_univ, one_smul,
          Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map selected
        (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma)) =
        Measure.map project
          (Measure.map residual
            (P.restrict (gn21RawPostThinningRaceAcceptedFirst state sigma))) := by
              rw [Measure.map_map hproject hresidual]
              rfl
    _ = Measure.map project
        (ENNReal.ofReal (arrivalRate * mass / (arrivalRate * mass + switchRate)) •
          (T.prod (S.prod Q))) := by
            simpa [P, residual, arrivalRate, switchRate, mass, T, S, Q] using
              congrArg (Measure.map project) hlaw
    _ = ENNReal.ofReal (arrivalRate * mass / (arrivalRate * mass + switchRate)) • Q := by
      rw [Measure.map_smul, hprojectLaw]
    _ = ENNReal.ofReal
        ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (gn21ArrivalClockIndex state) *
            singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
            gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
              (RawTwoStateCTMC.switchClockIndex state))) •
        gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma := by
          rfl

/-- The expectation of any integrable trip statistic realized in one literal
open-state subcycle is the accepted-winner probability times its accepted-mark
mean.  The zero contribution on the switch-first branch is part of the
observable, so this does not condition away a source event. -/
theorem integral_gn21RawPostThinningRaceAcceptedContribution_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (f : TripLength -> Real)
    (hintegrable : Integrable f
      (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)) :
    (∫ seed, gn21RawPostThinningRaceAcceptedContribution state sigma f seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) *
        (∫ tau, f tau ∂gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawPostThinningRaceAcceptedFirst state sigma
  let selected : GN21RawCycleSeed -> TripLength := fun seed =>
    (gn21RawPostThinningRaceSeed state sigma seed).2.2
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  let mass := singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  have hA : MeasurableSet A :=
    measurableSet_gn21RawPostThinningRaceAcceptedFirst state sigma hsigma
  have hselected : Measurable selected :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_gn21RawPostThinningRaceSeed state sigma hsigma))
  have hmap : Measure.map selected (P.restrict A) =
      ENNReal.ofReal (arrivalRate * mass / (arrivalRate * mass + switchRate)) • Q := by
    simpa [P, A, selected, arrivalRate, switchRate, mass, Q] using
      (map_gn21RawPostThinningRaceSelectedTripMark_restrict
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hratio : 0 ≤ arrivalRate * mass / (arrivalRate * mass + switchRate) := by
    exact le_of_lt (div_pos (mul_pos harrivalRate (by simpa [mass] using hmass))
      (add_pos (mul_pos harrivalRate (by simpa [mass] using hmass)) hswitchRate))
  have hfmap : AEStronglyMeasurable f (Measure.map selected (P.restrict A)) := by
    rw [hmap]
    exact AEStronglyMeasurable.smul_measure hintegrable.aestronglyMeasurable
      (ENNReal.ofReal (arrivalRate * mass / (arrivalRate * mass + switchRate)))
  calc
    (∫ seed, gn21RawPostThinningRaceAcceptedContribution state sigma f seed ∂P) =
        ∫ seed, A.indicator (fun seed => f (selected seed)) seed ∂P := by
          rfl
    _ = ∫ seed in A, f (selected seed) ∂P := by
          rw [integral_indicator hA]
    _ = ∫ tau, f tau ∂Measure.map selected (P.restrict A) := by
          exact (integral_map hselected.aemeasurable hfmap).symm
    _ = ∫ tau, f tau ∂(ENNReal.ofReal
        (arrivalRate * mass / (arrivalRate * mass + switchRate)) • Q) := by
          rw [hmap]
    _ = (arrivalRate * mass / (arrivalRate * mass + switchRate) : Real) *
        (∫ tau, f tau ∂Q) := by
          simp [integral_smul_measure, hratio]
    _ = ((gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (gn21ArrivalClockIndex state) *
        singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) /
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state) *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma +
          gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))) *
        (∫ tau, f tau ∂gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma) := by
          rfl

/-- Integrability of an accepted-trip statistic transfers to its literal
zero-on-switch-first contribution in a raw subcycle. -/
theorem integrable_gn21RawPostThinningRaceAcceptedContribution
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (f : TripLength -> Real)
    (hintegrable : Integrable f
      (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)) :
    Integrable (gn21RawPostThinningRaceAcceptedContribution state sigma f)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let A := gn21RawPostThinningRaceAcceptedFirst state sigma
  let selected : GN21RawCycleSeed -> TripLength := fun seed =>
    (gn21RawPostThinningRaceSeed state sigma seed).2.2
  let Q := gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma
  have hselectedLaw : HasLaw selected Q P := by
    simpa [selected, Q, P] using
      (AcceptedTripSelection.gn21RawFirstAcceptedTripMark_hasLaw
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass)
  have hmapIntegrable : Integrable f (Measure.map selected P) := by
    rw [hselectedLaw.map_eq]
    exact hintegrable
  have hselectedIntegrable : Integrable (fun seed => f (selected seed)) P := by
    simpa [Function.comp_def] using
      hmapIntegrable.comp_aemeasurable hselectedLaw.aemeasurable
  have hA : MeasurableSet A :=
    measurableSet_gn21RawPostThinningRaceAcceptedFirst state sigma hsigma
  simpa [gn21RawPostThinningRaceAcceptedContribution, A, selected] using
    hselectedIntegrable.indicator hA

/-- The elapsed time of one literal open-state subcycle: the competing-race
holding time plus the selected trip length exactly on an accepted winner. -/
noncomputable def gn21RawPostThinningRaceSubcycleTime
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Real := fun seed =>
  gn21RawPostThinningRaceMinimum state sigma seed +
    gn21RawPostThinningRaceAcceptedContribution state sigma (fun tau => tau) seed

/-- The literal earnings of one open-state subcycle.  A switch-first subcycle
earns zero; an accepted subcycle earns the selected trip's payout. -/
noncomputable def gn21RawPostThinningRaceSubcycleEarning
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Real :=
  gn21RawPostThinningRaceAcceptedContribution state sigma w

theorem integrable_gn21RawPostThinningRaceSubcycleTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    Integrable (gn21RawPostThinningRaceSubcycleTime state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  have hminimum := integrable_gn21RawPostThinningRaceMinimum
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have htrip := integrable_gn21AcceptedTripLength
    (gn21CycleMarkLaw muI muJ state) sigma hmass htime
  have hcontribution := integrable_gn21RawPostThinningRaceAcceptedContribution
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
    (fun tau : TripLength => tau) htrip
  simpa [gn21RawPostThinningRaceSubcycleTime] using hminimum.add hcontribution

theorem integrable_gn21RawPostThinningRaceSubcycleEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    Integrable (gn21RawPostThinningRaceSubcycleEarning state w sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  have htrip := integrable_gn21AcceptedTripPayment
    (gn21CycleMarkLaw muI muJ state) w sigma hmass hpayment
  simpa [gn21RawPostThinningRaceSubcycleEarning] using
    (integrable_gn21RawPostThinningRaceAcceptedContribution
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass w htrip)

/-- The expected time of one literal raw subcycle is exactly the Appendix D.1
subcycle-length expression. -/
theorem integral_gn21RawPostThinningRaceSubcycleTime_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    (∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21SubcycleLength
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state)) sigma) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  have harrivalRate : 0 < arrivalRate := by
    dsimp [arrivalRate, gn21ArrivalClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, harrivalI, harrivalJ]
  have hswitchRate : 0 < switchRate := by
    dsimp [switchRate, RawTwoStateCTMC.switchClockIndex]
    fin_cases state <;> simp [gn21CycleClockRate, hswitchIJ, hswitchJI]
  have hminimum := integrable_gn21RawPostThinningRaceMinimum
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have htrip := integrable_gn21AcceptedTripLength M sigma (by simpa [M] using hmass)
    (by simpa [M] using htime)
  have hcontribution := integrable_gn21RawPostThinningRaceAcceptedContribution
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
    (fun tau : TripLength => tau) htrip
  calc
    (∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed ∂P) =
        (∫ seed, gn21RawPostThinningRaceMinimum state sigma seed ∂P) +
          (∫ seed, gn21RawPostThinningRaceAcceptedContribution state sigma
            (fun tau : TripLength => tau) seed ∂P) := by
              change (∫ seed, gn21RawPostThinningRaceMinimum state sigma seed +
                gn21RawPostThinningRaceAcceptedContribution state sigma
                  (fun tau : TripLength => tau) seed ∂P) = _
              rw [integral_add hminimum hcontribution]
    _ = 1 / (arrivalRate * singleStateTripMass M sigma + switchRate) +
          (arrivalRate * singleStateTripMass M sigma /
            (arrivalRate * singleStateTripMass M sigma + switchRate)) *
            (∫ tau, tau ∂gn21AcceptedTripLaw M sigma) := by
              rw [integral_gn21RawPostThinningRaceMinimum_eq_inv_rate
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass,
                integral_gn21RawPostThinningRaceAcceptedContribution_eq
                  muI muJ arrivalI arrivalJ switchIJ switchJI
                  harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
                  (fun tau : TripLength => tau) htrip]
    _ = gn21SubcycleLength arrivalRate (singleStateTripMass M sigma) switchRate
          (gn21StateCycleTime M arrivalRate sigma) := by
            exact gn21_expected_subcycle_time_from_post_thinning_components
              M arrivalRate switchRate sigma harrivalRate (le_of_lt hswitchRate)
              (by simpa [M] using hmass)
    _ = gn21SubcycleLength
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state)) sigma) := by rfl

/-- The expected earnings of one literal raw subcycle are exactly the
Appendix D.1 subcycle-earning expression. -/
theorem integral_gn21RawPostThinningRaceSubcycleEarning_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    (∫ seed, gn21RawPostThinningRaceSubcycleEarning state w sigma seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21SubcycleEarning
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ state) w sigma) := by
  let M := gn21CycleMarkLaw muI muJ state
  letI : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  let arrivalRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (gn21ArrivalClockIndex state)
  let switchRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
    (RawTwoStateCTMC.switchClockIndex state)
  have htrip := integrable_gn21AcceptedTripPayment M w sigma (by simpa [M] using hmass)
    (by simpa [M] using hpayment)
  calc
    (∫ seed, gn21RawPostThinningRaceSubcycleEarning state w sigma seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        (arrivalRate * singleStateTripMass M sigma /
          (arrivalRate * singleStateTripMass M sigma + switchRate)) *
          (∫ tau, w tau ∂gn21AcceptedTripLaw M sigma) := by
            simpa [gn21RawPostThinningRaceSubcycleEarning, M, arrivalRate, switchRate] using
              (integral_gn21RawPostThinningRaceAcceptedContribution_eq
                muI muJ arrivalI arrivalJ switchIJ switchJI
                harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass w htrip)
    _ = gn21SubcycleEarning arrivalRate (singleStateTripMass M sigma) switchRate
          (gn21StateMeanEarning M w sigma) := by
            exact gn21_expected_subcycle_earning_from_post_thinning_components
              M arrivalRate switchRate w sigma (by simpa [M] using hmass)
    _ = gn21SubcycleEarning
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ state) w sigma) := by rfl

end

end GN21DriverSurgePricing
