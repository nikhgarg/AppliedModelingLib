import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalLedger
import AppliedModelingLib.Queueing.StationaryPriorityInput
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkload
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkConservation
import AppliedModelingLib.Queueing.NonpreemptivePriorityServiceAccounting
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceRegeneration
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceReflection
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceMeasurability
import AppliedModelingLib.Foundations.Probability.EventuallyStableFiniteReplay
import AppliedModelingLib.Foundations.Probability.MeasurableCountableEvaluation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sigma.Order

/-!
# Finite stationary-input traces for nonpreemptive-priority queues

This module instantiates the deterministic priority trace with the literal
finite windows of the stationary marked-Poisson input.  Starting a window from
an empty state is the finite precursor of the remote-past construction: a
later stability argument will show that sufficiently remote starts give the
same state at the observation epoch.
-/

namespace AppliedModelingLib
namespace Queueing

open ProbabilityTheory

noncomputable section

/-- The empty priority-queue state at a prescribed physical time. -/
def emptyNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*} (time : ℝ) :
    NonpreemptivePriorityWorkState n JobId where
  currentTime := time
  active := none
  waiting := fun _ => []
  completed := []

/-- An empty state has class-consistent waiting lists. -/
theorem hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*} (time : ℝ) :
    hasClassConsistentWaiting (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) time) := by
  intro i job hmember
  simp [emptyNonpreemptivePriorityWorkState] at hmember

/-- The empty state is work-conserving. -/
theorem nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*} (time : ℝ) :
    nonpreemptivePriorityWorkConserving
      (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) time) := by
  intro _ hwaiting
  simp [hasPriorityWaitingJob, emptyNonpreemptivePriorityWorkState] at hwaiting

/-- A positive-work finite trace whose residual workload is zero has the same
live queue as the literal empty state at its current physical time.  Its
completion ledger may still record the finite history that led to that reset. -/
theorem liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (htotal : totalNonpreemptivePriorityResidualWork state = 0) :
    liveEquivalentNonpreemptivePriorityWorkState state
      (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) state.currentTime) := by
  rcases active_eq_none_and_waiting_eq_nil_of_totalResidualWork_eq_zero
    state hpositive htotal with ⟨hactive, hwaiting⟩
  refine ⟨rfl, ?_, ?_⟩
  · simpa [emptyNonpreemptivePriorityWorkState] using hactive
  · funext i
    simp [emptyNonpreemptivePriorityWorkState, hwaiting i]

/-- A finite service evolution with zero residual work at its target is live
equivalent to the literal empty state at that physical epoch. -/
theorem liveEquivalent_advanceNonpreemptivePriorityWorkState_empty_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (htotal : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) = 0) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState fuel target state)
      (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) target) := by
  have hadvancePositive : positiveNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) :=
    positiveNonpreemptivePriorityResidualWork_advance fuel target state hpositive
  have htime : (advanceNonpreemptivePriorityWorkState fuel target state).currentTime = target :=
    advanceNonpreemptivePriorityWorkState_currentTime_eq_target fuel target state hcurrent hfuel
  have hempty := liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
    (advanceNonpreemptivePriorityWorkState fuel target state) hadvancePositive htotal
  rw [htime] at hempty
  exact hempty

/-- If a service-only evolution is empty at a cutoff, then advancing the
same state to a later epoch is live-equivalent to an empty state there. -/
theorem liveEquivalent_advanceNonpreemptivePriorityWorkState_empty_of_empty_at_cutoff
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (cutoff target : ℝ)
    (hcurrentCutoff : state.currentTime ≤ cutoff)
    (hcutoffTarget : cutoff ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel cutoff state) = 0) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState fuel target state)
      (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) target) := by
  apply liveEquivalent_advanceNonpreemptivePriorityWorkState_empty_of_totalResidualWork_eq_zero
  · exact hcurrentCutoff.trans hcutoffTarget
  · exact hpositive
  · exact hfuel
  · exact totalNonpreemptivePriorityResidualWork_advance_eq_zero_of_advance_eq_zero
      fuel state cutoff target hcurrentCutoff hcutoffTarget hpositive hwork hfuel hcutoffZero

/-- Advancing a literal empty state through an arrival-free interval changes
only its physical clock. -/
theorem advanceNonpreemptivePriorityWorkState_empty_eq_empty
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (start target : ℝ) (horizon : start ≤ target) :
    advanceNonpreemptivePriorityWorkState fuel target
      (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) start) =
      emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) target := by
  rcases horizon.eq_or_lt with rfl | hstrict
  · cases fuel <;> simp [advanceNonpreemptivePriorityWorkState,
      emptyNonpreemptivePriorityWorkState]
  · have hnot : ¬ target ≤ start := not_le_of_gt hstrict
    cases fuel <;> simp [advanceNonpreemptivePriorityWorkState,
      emptyNonpreemptivePriorityWorkState, hnot]

/-- Splitting a finite arrival trace at an arrival-free epoch where its
incoming state has emptied does not change the live queue at any later
terminal epoch.  The first later arrival is treated explicitly; after it,
both traces have equal clocks and the standard common-arrivals congruence
applies. -/
theorem liveEquivalent_advance_run_from_empty_at_cutoff
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (cutoff terminal : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (hcurrentCutoff : state.currentTime ≤ cutoff)
    (hcutoffTerminal : cutoff ≤ terminal)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤
      totalNonpreemptivePriorityWorkJobs state)
    (hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) cutoff state) = 0)
    (hjobs : ∀ job ∈ jobs, cutoff ≤ job.arrivalTime) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace state jobs))
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) jobs)) := by
  cases jobs with
  | nil =>
      simp only [runNonpreemptivePriorityArrivalTrace, List.foldl_nil]
      have hemptyCount : totalNonpreemptivePriorityWorkJobs
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) = 0 := by
        simp [emptyNonpreemptivePriorityWorkState,
          totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
      rw [hemptyCount]
      rw [advanceNonpreemptivePriorityWorkState_empty_eq_empty
        0 cutoff terminal hcutoffTerminal]
      exact liveEquivalent_advanceNonpreemptivePriorityWorkState_empty_of_empty_at_cutoff
        (totalNonpreemptivePriorityWorkJobs state) state cutoff terminal
        hcurrentCutoff hcutoffTerminal hpositive hwork hfuel hcutoffZero
  | cons job jobs =>
      have hjobCutoff : cutoff ≤ job.arrivalTime := hjobs job (by simp)
      have hleftAdvance : liveEquivalentNonpreemptivePriorityWorkState
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) job.arrivalTime state)
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId)
            job.arrivalTime) :=
        liveEquivalent_advanceNonpreemptivePriorityWorkState_empty_of_empty_at_cutoff
          (totalNonpreemptivePriorityWorkJobs state) state cutoff job.arrivalTime
          hcurrentCutoff hjobCutoff hpositive hwork hfuel hcutoffZero
      have hrightAdvance : advanceNonpreemptivePriorityWorkState 0 job.arrivalTime
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) =
          emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId)
            job.arrivalTime :=
        advanceNonpreemptivePriorityWorkState_empty_eq_empty 0 cutoff job.arrivalTime hjobCutoff
      have hadvance : liveEquivalentNonpreemptivePriorityWorkState
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) job.arrivalTime state)
          (advanceNonpreemptivePriorityWorkState 0 job.arrivalTime
            (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff)) := by
        rw [hrightAdvance]
        exact hleftAdvance
      let leftFirst := advanceThenAdmitNonpreemptivePriorityJob
        (totalNonpreemptivePriorityWorkJobs state) state job
      let rightFirst := advanceThenAdmitNonpreemptivePriorityJob 0
        (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) job
      have hadmit : liveEquivalentNonpreemptivePriorityWorkState leftFirst rightFirst := by
        dsimp [leftFirst, rightFirst, advanceThenAdmitNonpreemptivePriorityJob]
        exact liveEquivalentNonpreemptivePriorityWorkState_admit _ _ job hadvance
      have htail := liveEquivalentNonpreemptivePriorityWorkState_runThenAdvance
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace leftFirst jobs))
        terminal leftFirst rightFirst jobs hadmit
      have htailCount : totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace leftFirst jobs) =
          totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace rightFirst jobs) :=
        totalNonpreemptivePriorityWorkJobs_eq_of_liveEquivalent
          (liveEquivalentNonpreemptivePriorityWorkState_run leftFirst rightFirst jobs hadmit)
      have hleftRun : runNonpreemptivePriorityArrivalTrace state (job :: jobs) =
          runNonpreemptivePriorityArrivalTrace leftFirst jobs := by
        simp [runNonpreemptivePriorityArrivalTrace, leftFirst]
      have hrightRun : runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) cutoff) (job :: jobs) =
          runNonpreemptivePriorityArrivalTrace rightFirst jobs := by
        simp [runNonpreemptivePriorityArrivalTrace, rightFirst,
          emptyNonpreemptivePriorityWorkState, totalNonpreemptivePriorityWorkJobs,
          totalPriorityWaitingJobs]
      rw [hleftRun, hrightRun, ← htailCount]
      exact htail

/-- Once a positive-work trace has emptied at a physical epoch, every common
finite continuation has the same live queue as a new trace begun empty at
that epoch.  Completion records may differ, but cannot affect later service
or admissions. -/
theorem liveEquivalent_continuation_from_empty_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (terminalFuel : ℕ) (terminalTime : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (suffix : List (NonpreemptivePriorityJob n JobId))
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (htotal : totalNonpreemptivePriorityResidualWork state = 0) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState terminalFuel terminalTime
        (runNonpreemptivePriorityArrivalTrace state suffix))
      (advanceNonpreemptivePriorityWorkState terminalFuel terminalTime
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState (n := n) (JobId := JobId) state.currentTime)
          suffix)) := by
  apply liveEquivalentNonpreemptivePriorityWorkState_runThenAdvance
  exact liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
    state hpositive htotal

/-- The finite labelled arrival indices of the literal stationary input in a
half-open physical interval. -/
def stationaryPriorityArrivalWindowIndices
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) : Fin n → Finset ℤ :=
  fun i => Probability.PoissonProcess.suspensionBaseArrivalIndices a b (omega i).1

/-- The physical epoch of any fixed labelled stationary arrival is a
measurable coordinate of the joint input path. -/
theorem measurable_stationaryPriorityArrivalTime
    {n : ℕ} (q : NonpreemptivePriorityArrivalIndex n) :
    Measurable (fun omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2) := by
  exact (Probability.PoissonProcess.measurable_suspensionBaseArrival q.2).comp
    (measurable_fst.comp (measurable_pi_apply q.1))

/-- Membership of a fixed labelled arrival in a literal finite window is a
Borel event. -/
theorem measurableSet_mem_stationaryPriorityArrivalWindowIndices
    {n : ℕ} (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      q.2 ∈ stationaryPriorityArrivalWindowIndices omega a b q.1} := by
  change MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      q.2 ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b (omega q.1).1}
  apply measurableSet_setOf.mpr
  simpa only [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff] using
    ((measurable_const.le' (measurable_stationaryPriorityArrivalTime q)).and
      ((measurable_stationaryPriorityArrivalTime q).lt measurable_const))

/-- A deterministic total key for stationary labelled arrivals: physical
arrival time first, followed by the class-index label to resolve exact ties. -/
def stationaryPriorityArrivalIndexKey
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (q : NonpreemptivePriorityArrivalIndex n) :
    ℝ ×ₗ (Σₗ i : Fin n, ℤ) :=
  toLex
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2,
      (toLex q : Σₗ i : Fin n, ℤ))

/-- The stationary arrival key retains the labelled index, hence is injective. -/
theorem Function.Injective.stationaryPriorityArrivalIndexKey
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) :
    Function.Injective (stationaryPriorityArrivalIndexKey omega) := by
  intro first second hkey
  have hindex : (toLex first : Σₗ i : Fin n, ℤ) = toLex second := by
    exact congrArg (fun key => (ofLex key).2) hkey
  exact toLex_inj.mp hindex

/-- The total order induced by the physical-time-and-label stationary arrival
key. -/
def stationaryPriorityArrivalIndexLE
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (first second : NonpreemptivePriorityArrivalIndex n) : Prop :=
  stationaryPriorityArrivalIndexKey omega first ≤ stationaryPriorityArrivalIndexKey omega second

/-- The canonical-order comparison of two fixed labelled arrivals is a Borel
event.  The physical epochs are the only random coordinates; the label
tie-breaker is fixed in advance. -/
theorem measurableSet_stationaryPriorityArrivalIndexLE
    {n : ℕ} (first second : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      stationaryPriorityArrivalIndexLE omega first second} := by
  classical
  unfold stationaryPriorityArrivalIndexLE stationaryPriorityArrivalIndexKey
  simp only [Prod.Lex.toLex_le_toLex]
  let firstTime : (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ :=
    fun omega => Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      first.1 omega first.2
  let secondTime : (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ :=
    fun omega => Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      second.1 omega second.2
  have hfirst : Measurable firstTime := by
    simpa [firstTime] using measurable_stationaryPriorityArrivalTime first
  have hsecond : Measurable secondTime := by
    simpa [secondTime] using measurable_stationaryPriorityArrivalTime second
  by_cases hlabel : (toLex first : Σₗ i : Fin n, ℤ) ≤ toLex second
  · simpa [firstTime, secondTime, hlabel] using
      (hfirst.lt hsecond).or (hfirst.eq hsecond)
  · simpa [firstTime, secondTime, hlabel] using hfirst.lt hsecond

/-- Pairwise canonical ordering of one fixed finite labelled ledger is a
Borel condition.  The list itself is static; only its finitely many physical
arrival-time comparisons vary with the stationary input path. -/
theorem measurableSet_stationaryPriorityArrivalIndexList_pairwise
    {n : ℕ} (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      labels.Pairwise (stationaryPriorityArrivalIndexLE omega)} := by
  induction labels with
  | nil => simp
  | cons first labels ih =>
      have hhead : MeasurableSet {omega : Fin n →
          (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
          ∀ later ∈ labels, stationaryPriorityArrivalIndexLE omega first later} := by
        rw [show {omega : Fin n →
            (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
            ∀ later ∈ labels, stationaryPriorityArrivalIndexLE omega first later} =
              ⋂ later ∈ labels.toFinset, {omega |
                stationaryPriorityArrivalIndexLE omega first later} by
          ext omega
          simp]
        exact labels.toFinset.measurableSet_biInter fun later _ =>
          measurableSet_stationaryPriorityArrivalIndexLE first later
      simpa only [List.pairwise_cons] using hhead.inter ih

theorem stationaryPriorityArrivalIndexLE_trans
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    {first second third : NonpreemptivePriorityArrivalIndex n}
    (hfirst : stationaryPriorityArrivalIndexLE omega first second)
    (hsecond : stationaryPriorityArrivalIndexLE omega second third) :
    stationaryPriorityArrivalIndexLE omega first third := by
  exact hfirst.trans hsecond

theorem stationaryPriorityArrivalIndexLE_total
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (first second : NonpreemptivePriorityArrivalIndex n) :
    stationaryPriorityArrivalIndexLE omega first second ∨
      stationaryPriorityArrivalIndexLE omega second first := by
  exact le_total _ _

theorem stationaryPriorityArrivalIndexLE_antisymm
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    {first second : NonpreemptivePriorityArrivalIndex n}
    (hfirst : stationaryPriorityArrivalIndexLE omega first second)
    (hsecond : stationaryPriorityArrivalIndexLE omega second first) :
    first = second := by
  apply Function.Injective.stationaryPriorityArrivalIndexKey omega
  exact le_antisymm hfirst hsecond

/-- The canonical labelled-index ledger in a stationary finite window.  It
uses physical time as its primary order and the fixed class-index label only
to make simultaneous arrivals deterministic. -/
noncomputable def canonicalStationaryPriorityArrivalWindowIndices
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) : List (NonpreemptivePriorityArrivalIndex n) := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  exact (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega a b)).sort
      (stationaryPriorityArrivalIndexLE omega)

/-- The canonical stationary index ledger is sorted by its deterministic
physical-time-and-label order. -/
theorem pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    (canonicalStationaryPriorityArrivalWindowIndices omega a b).Pairwise
      (stationaryPriorityArrivalIndexLE omega) := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  exact Finset.pairwise_sort _ _

/-- Membership in a canonical stationary index ledger is exactly membership
in the corresponding finite half-open arrival window. -/
theorem mem_canonicalStationaryPriorityArrivalWindowIndices_iff
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    q ∈ canonicalStationaryPriorityArrivalWindowIndices omega a b ↔
      q.2 ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b (omega q.1).1 := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  simp [canonicalStationaryPriorityArrivalWindowIndices,
    nonpreemptivePriorityArrivalWindowIndices, stationaryPriorityArrivalWindowIndices]

/-- Each fixed finite labelled-index set is a Borel fiber of the literal
stationary arrival ledger.  This is the countable discrete part of the
finite-trace measurability argument. -/
theorem measurableSet_stationaryPriorityArrivalWindowLedger_eq
    {n : ℕ} (a b : ℝ) (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a b) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {omega : Fin n →
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b)} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityArrivalWindowIndices a b q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {omega : Fin n →
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega a b) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {omega : Fin n →
          (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices omega a b)} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a b) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {omega |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b) ↔ q ∈ labels} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The canonical sorted ledger has a Borel fiber at every fixed finite list.
Besides selecting the fixed finite index set, the fiber records the finite
collection of physical-time comparisons that determines its canonical order. -/
theorem measurableSet_canonicalStationaryPriorityArrivalWindowIndices_eq
    {n : ℕ} (a b : ℝ) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      canonicalStationaryPriorityArrivalWindowIndices omega a b = labels} := by
  classical
  have hledger := measurableSet_stationaryPriorityArrivalWindowLedger_eq a b labels.toFinset
  have hpairwise := measurableSet_stationaryPriorityArrivalIndexList_pairwise labels
  have hnodup : MeasurableSet {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
      canonicalStationaryPriorityArrivalWindowIndices omega a b = labels} =
      ({omega | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a b) = labels.toFinset} ∩
        {omega | labels.Pairwise (stationaryPriorityArrivalIndexLE omega)}) ∩
          {omega | labels.Nodup} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityArrivalIndexLE omega) :=
        ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
      letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
        ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
      letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
        ⟨stationaryPriorityArrivalIndexLE_total omega⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityArrivalWindowIndices omega a b).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityArrivalWindowIndices omega a b) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices omega a b
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityArrivalIndexLE omega) :=
        ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
      letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
        ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
      letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
        ⟨stationaryPriorityArrivalIndexLE_total omega⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a b)).sort
          (stationaryPriorityArrivalIndexLE omega) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityArrivalIndexLE omega) hnodup).mpr
        hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- Every canonical stationary index in a half-open window occurs before the
window's right endpoint. -/
theorem canonicalStationaryPriorityArrivalIndex_lt_right
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityArrivalWindowIndices omega a b) :
    Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2 < b := by
  have hindex :=
    (mem_canonicalStationaryPriorityArrivalWindowIndices_iff omega a b q).mp hq
  have hwindow :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (omega q.1).1 q.2).mp hindex
  simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
    Probability.Queueing.stationaryPoissonWorkArrival,
    Probability.Queueing.timedEmbeddedArrival] using hwindow.2

/-- Every canonical stationary index in a half-open window occurs at or after
the window's left endpoint. -/
theorem canonicalStationaryPriorityArrivalIndex_left_le
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityArrivalWindowIndices omega a b) :
    a ≤ Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2 := by
  have hindex :=
    (mem_canonicalStationaryPriorityArrivalWindowIndices_iff omega a b q).mp hq
  have hwindow :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (omega q.1).1 q.2).mp hindex
  simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
    Probability.Queueing.stationaryPoissonWorkArrival,
    Probability.Queueing.timedEmbeddedArrival] using hwindow.1

/-- Every labelled arrival in the left adjacent canonical ledger precedes
every labelled arrival in the right ledger in the deterministic total order. -/
theorem stationaryPriorityArrivalIndexLE_of_mem_adjacentCanonicalWindows
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (q r : NonpreemptivePriorityArrivalIndex n)
    (hq : q ∈ canonicalStationaryPriorityArrivalWindowIndices omega a c)
    (hr : r ∈ canonicalStationaryPriorityArrivalWindowIndices omega c b) :
    stationaryPriorityArrivalIndexLE omega q r := by
  unfold stationaryPriorityArrivalIndexLE stationaryPriorityArrivalIndexKey
  apply Prod.Lex.toLex_le_toLex.mpr
  left
  exact lt_of_lt_of_le
    (canonicalStationaryPriorityArrivalIndex_lt_right omega a c q hq)
    (canonicalStationaryPriorityArrivalIndex_left_le omega c b r hr)

/-- Adjacent half-open stationary arrival windows partition the corresponding
larger half-open window exactly, class by class. -/
theorem stationaryPriorityArrivalWindowIndices_union
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (fun i => stationaryPriorityArrivalWindowIndices omega a c i ∪
      stationaryPriorityArrivalWindowIndices omega c b i) =
      stationaryPriorityArrivalWindowIndices omega a b := by
  funext i
  ext k
  simp only [stationaryPriorityArrivalWindowIndices, Finset.mem_union]
  rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff,
    Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff,
    Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff]
  constructor
  · rintro (hleft | hright)
    · exact ⟨hleft.1, lt_of_lt_of_le hleft.2 hcb⟩
    · exact ⟨le_trans hac hright.1, hright.2⟩
  · intro hwindow
    rcases lt_or_ge (Probability.PoissonProcess.suspensionBaseArrival (omega i).1 k) c
      with hbefore | hafter
    · exact Or.inl ⟨hwindow.1, hbefore⟩
    · exact Or.inr ⟨hafter, hwindow.2⟩

/-- Adjacent half-open stationary windows select disjoint labelled arrival
indices.  An arrival at the shared endpoint belongs only to the right window. -/
theorem disjoint_stationaryPriorityArrivalWindowIndexLedgers
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    Disjoint
      (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a c))
      (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega c b)) := by
  rw [Finset.disjoint_left]
  rintro ⟨i, k⟩ hleft hright
  have hleftIndex :
      k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a c (omega i).1 := by
    simpa [nonpreemptivePriorityArrivalWindowIndices,
      stationaryPriorityArrivalWindowIndices] using hleft
  have hrightIndex :
      k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices c b (omega i).1 := by
    simpa [nonpreemptivePriorityArrivalWindowIndices,
      stationaryPriorityArrivalWindowIndices] using hright
  have hleft' :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a c (omega i).1 k).mp hleftIndex
  have hright' :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      c b (omega i).1 k).mp hrightIndex
  exact (not_le_of_gt hleft'.2) hright'.1

/-- The raw labelled-index ledger of a larger stationary interval is a
permutation of its two adjacent half-open ledgers concatenated in time order. -/
theorem perm_stationaryPriorityArrivalWindowIndexLedger_append
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices omega a b)).toList.Perm
      ((nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a c)).toList ++
        (nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega c b)).toList) := by
  rw [← stationaryPriorityArrivalWindowIndices_union omega a c b hac hcb]
  rw [nonpreemptivePriorityArrivalWindowIndices_union]
  exact Finset.toList_union_perm_append_of_disjoint _ _
    (disjoint_stationaryPriorityArrivalWindowIndexLedgers omega a c b hac hcb)

/-- The raw marked-job ledger of a larger stationary interval is a
permutation of the raw ledgers from its two adjacent half-open pieces. -/
theorem perm_stationaryPriorityArrivalWindowRawJobs_append
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (nonpreemptivePriorityArrivalWindowJobs
      (stationaryPriorityArrivalWindowIndices omega a b)
      (fun i k => Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k)
      (fun i k => stationaryPriorityWorkRequirement meanService i omega k)).Perm
      (nonpreemptivePriorityArrivalWindowJobs
        (stationaryPriorityArrivalWindowIndices omega a c)
        (fun i k => Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k)
        (fun i k => stationaryPriorityWorkRequirement meanService i omega k) ++
      nonpreemptivePriorityArrivalWindowJobs
        (stationaryPriorityArrivalWindowIndices omega c b)
        (fun i k => Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k)
        (fun i k => stationaryPriorityWorkRequirement meanService i omega k)) := by
  simpa [nonpreemptivePriorityArrivalWindowJobs] using
    (perm_stationaryPriorityArrivalWindowIndexLedger_append omega a c b hac hcb).map
      (fun q : NonpreemptivePriorityArrivalIndex n =>
        ({ identifier := q
           priority := q.1
           arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2
           serviceWork := stationaryPriorityWorkRequirement meanService q.1 omega q.2 } :
          NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))

/-- Canonically ordered stationary index ledgers concatenate exactly across
adjacent half-open physical windows. -/
theorem canonicalStationaryPriorityArrivalWindowIndices_append
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    canonicalStationaryPriorityArrivalWindowIndices omega a b =
      canonicalStationaryPriorityArrivalWindowIndices omega a c ++
        canonicalStationaryPriorityArrivalWindowIndices omega c b := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  let left := canonicalStationaryPriorityArrivalWindowIndices omega a c
  let right := canonicalStationaryPriorityArrivalWindowIndices omega c b
  have hdisjoint : List.Disjoint left right := by
    rw [List.disjoint_iff_ne]
    intro q hq r hr heq
    subst r
    exact (not_le_of_gt
      (canonicalStationaryPriorityArrivalIndex_lt_right omega a c q hq))
      (canonicalStationaryPriorityArrivalIndex_left_le omega c b q hr)
  have hnodup : (left ++ right).Nodup := by
    apply List.Nodup.append
    · exact Finset.sort_nodup _ _
    · exact Finset.sort_nodup _ _
    · exact hdisjoint
  have hpairwise : (left ++ right).Pairwise
      (stationaryPriorityArrivalIndexLE omega) := by
    rw [List.pairwise_append]
    refine ⟨pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices omega a c,
      pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices omega c b, ?_⟩
    intro q hq r hr
    exact stationaryPriorityArrivalIndexLE_of_mem_adjacentCanonicalWindows
      omega a c b q r hq hr
  have hsorted : ((left ++ right).toFinset).sort
      (stationaryPriorityArrivalIndexLE omega) = left ++ right := by
    exact (List.toFinset_sort (r := stationaryPriorityArrivalIndexLE omega) hnodup).mpr hpairwise
  have hledger : (left ++ right).toFinset =
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega a b) := by
    rw [List.toFinset_append]
    change (canonicalStationaryPriorityArrivalWindowIndices omega a c).toFinset ∪
        (canonicalStationaryPriorityArrivalWindowIndices omega c b).toFinset = _
    rw [show (canonicalStationaryPriorityArrivalWindowIndices omega a c).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega a c) by
      exact Finset.sort_toFinset _ _]
    rw [show (canonicalStationaryPriorityArrivalWindowIndices omega c b).toFinset =
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega c b) by
      exact Finset.sort_toFinset _ _]
    rw [← nonpreemptivePriorityArrivalWindowIndices_union]
    exact congrArg nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices_union omega a c b hac hcb)
  change (nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega a b)).sort
      (stationaryPriorityArrivalIndexLE omega) = left ++ right
  rw [← hledger]
  exact hsorted

/-- The key order of two labelled stationary arrivals implies the same weak
order of their physical arrival times. -/
theorem stationaryPriorityArrivalTime_le_of_indexLE
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    {q r : NonpreemptivePriorityArrivalIndex n}
    (horder : stationaryPriorityArrivalIndexLE omega q r) :
    Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2 ≤
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival r.1 omega r.2 := by
  unfold stationaryPriorityArrivalIndexLE stationaryPriorityArrivalIndexKey at horder
  exact Prod.Lex.monotone_fst _ _ horder

/-- The canonical chronological job ledger carried by a stationary marked
input window.  Simultaneous arrivals are ordered by their fixed labels, while
the workload itself remains invariant to that convention. -/
def canonicalStationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (canonicalStationaryPriorityArrivalWindowIndices omega a b).map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2
      serviceWork := stationaryPriorityWorkRequirement meanService q.1 omega q.2 }

/-- The real coordinates attached to one fixed labelled stationary arrival.
Keeping the identifier and priority static makes this the exact input shape
required by the fixed-finite-trace measurability recursion. -/
def stationaryPriorityArrivalJobCoordinate
    {n : ℕ} (meanService : Fin n → ℝ) (q : NonpreemptivePriorityArrivalIndex n)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) :
    NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) :=
  { identifier := q
    priority := q.1
    arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 omega q.2
    serviceWork := stationaryPriorityWorkRequirement meanService q.1 omega q.2 }

/-- The physical arrival epoch and scaled exponential work mark of a fixed
label are measurable coordinates of the stationary input path. -/
theorem stationaryPriorityArrivalJobCoordinate_coordinatesMeasurable
    {n : ℕ} (meanService : Fin n → ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    NonpreemptivePriorityJob.CoordinatesMeasurable
      (stationaryPriorityArrivalJobCoordinate meanService q) := by
  constructor
  · exact measurable_stationaryPriorityArrivalTime q
  · change Measurable (fun omega : Fin n →
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        meanService q.1 * (omega q.1).2 q.2)
    exact measurable_const.mul
      ((measurable_pi_apply q.2).comp
        (measurable_snd.comp (measurable_pi_apply q.1)))

/-- Canonical stationary job ledgers concatenate exactly over adjacent
half-open physical windows. -/
theorem canonicalStationaryPriorityArrivalWindowJobs_append
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    canonicalStationaryPriorityArrivalWindowJobs meanService omega a b =
      canonicalStationaryPriorityArrivalWindowJobs meanService omega a c ++
        canonicalStationaryPriorityArrivalWindowJobs meanService omega c b := by
  unfold canonicalStationaryPriorityArrivalWindowJobs
  rw [canonicalStationaryPriorityArrivalWindowIndices_append omega a c b hac hcb,
    List.map_append]

/-- Canonical stationary job ledgers are nondecreasing in physical arrival
time. -/
theorem pairwise_arrivalTime_le_canonicalStationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    (canonicalStationaryPriorityArrivalWindowJobs meanService omega a b).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
  unfold canonicalStationaryPriorityArrivalWindowJobs
  rw [List.pairwise_map]
  exact (pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices omega a b).imp
    (fun horder => stationaryPriorityArrivalTime_le_of_indexLE omega horder)

/-- Total marked work in one literal stationary half-open arrival window. -/
def stationaryPriorityArrivalWindowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) : ℝ :=
  ∑ i, (stationaryPriorityArrivalWindowIndices omega a b i).sum
    (stationaryPriorityWorkRequirement meanService i omega)

/-- The scalar service sum of the canonical stationary job ledger is exactly
the finite marked-work aggregate of its selected arrival indices. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    nonpreemptivePriorityArrivalTraceServiceWork
      (canonicalStationaryPriorityArrivalWindowJobs meanService omega a b) =
      stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega a b)
  unfold nonpreemptivePriorityArrivalTraceServiceWork
    canonicalStationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowIndices
    stationaryPriorityArrivalWindowTotalWork
  simp only [List.map_map]
  change (ledger.sort
      (stationaryPriorityArrivalIndexLE omega) |>.map
        (fun q => stationaryPriorityWorkRequirement meanService q.1 omega q.2)).sum = _
  calc
    (ledger.sort (stationaryPriorityArrivalIndexLE omega) |>.map
        (fun q => stationaryPriorityWorkRequirement meanService q.1 omega q.2)).sum =
        (ledger.toList.map fun q =>
          stationaryPriorityWorkRequirement meanService q.1 omega q.2).sum :=
      ((Finset.sort_perm_toList ledger (stationaryPriorityArrivalIndexLE omega)).map _).sum_eq
    _ = ∑ q ∈ ledger, stationaryPriorityWorkRequirement meanService q.1 omega q.2 := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => stationaryPriorityWorkRequirement meanService q.1 omega q.2)
          ledger.nodup_toList).symm
    _ = stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
        stationaryPriorityArrivalWindowTotalWork
      rw [Finset.sum_sigma]

/-- Total squared service reward in one literal stationary half-open arrival
window.  This is an input ledger, independent of the service discipline. -/
def stationaryPriorityArrivalWindowTotalSquareWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) : ℝ :=
  ∑ i, (stationaryPriorityArrivalWindowIndices omega a b i).sum
    (fun k => (stationaryPriorityWorkRequirement meanService i omega k) ^ 2)

/-- The squared service sum of the canonical stationary job ledger is exactly
the input's finite squared-mark aggregate. -/
theorem stationaryPriorityArrivalWindowJobs_squareServiceWork_eq
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    ((canonicalStationaryPriorityArrivalWindowJobs meanService omega a b).map
      (fun job => job.serviceWork ^ 2)).sum =
      stationaryPriorityArrivalWindowTotalSquareWork meanService omega a b := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega a b)
  unfold canonicalStationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowIndices
    stationaryPriorityArrivalWindowTotalSquareWork
  simp only [List.map_map]
  change (ledger.sort
      (stationaryPriorityArrivalIndexLE omega) |>.map
        (fun q => (stationaryPriorityWorkRequirement meanService q.1 omega q.2) ^ 2)).sum = _
  calc
    (ledger.sort (stationaryPriorityArrivalIndexLE omega) |>.map
        (fun q => (stationaryPriorityWorkRequirement meanService q.1 omega q.2) ^ 2)).sum =
        (ledger.toList.map fun q =>
          (stationaryPriorityWorkRequirement meanService q.1 omega q.2) ^ 2).sum :=
      ((Finset.sort_perm_toList ledger (stationaryPriorityArrivalIndexLE omega)).map _).sum_eq
    _ = ∑ q ∈ ledger, (stationaryPriorityWorkRequirement meanService q.1 omega q.2) ^ 2 := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => (stationaryPriorityWorkRequirement meanService q.1 omega q.2) ^ 2)
          ledger.nodup_toList).symm
    _ = stationaryPriorityArrivalWindowTotalSquareWork meanService omega a b := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
        stationaryPriorityArrivalWindowTotalSquareWork
      rw [Finset.sum_sigma]

/-- On a past window ending at the observation epoch, the finite square-mark
input ledger is exactly the stationary priority input's total past square
aggregate. -/
theorem stationaryPriorityArrivalWindowTotalSquareWork_neg_to_zero
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) :
    stationaryPriorityArrivalWindowTotalSquareWork meanService omega (-t) 0 =
      stationaryPriorityTotalPastSquareWorkAggregate meanService omega t := by
  rfl

/-- On a past window ending at the observation epoch, the finite event-ledger
work aggregate is exactly the stationary input's total past work. -/
theorem stationaryPriorityArrivalWindowTotalWork_neg_to_zero
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) :
    stationaryPriorityArrivalWindowTotalWork meanService omega (-t) 0 =
      stationaryPriorityTotalPastWorkAggregate meanService omega t := by
  rfl

/-- The chronological finite priority-job list carried by the stationary
marked input in the half-open window `[a,b)`. -/
def stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  canonicalStationaryPriorityArrivalWindowJobs meanService omega a b

/-- The literal chronological stationary job ledger has the total past
squared service reward on a strict-past window. -/
theorem stationaryPriorityArrivalWindowJobs_squareServiceWork_neg_to_zero
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) :
    ((stationaryPriorityArrivalWindowJobs meanService omega (-t) 0).map
      (fun job => job.serviceWork ^ 2)).sum =
      stationaryPriorityTotalPastSquareWorkAggregate meanService omega t := by
  calc
    ((stationaryPriorityArrivalWindowJobs meanService omega (-t) 0).map
        (fun job => job.serviceWork ^ 2)).sum =
        stationaryPriorityArrivalWindowTotalSquareWork meanService omega (-t) 0 := by
          simpa [stationaryPriorityArrivalWindowJobs] using
            stationaryPriorityArrivalWindowJobs_squareServiceWork_eq
              meanService omega (-t) 0
    _ = stationaryPriorityTotalPastSquareWorkAggregate meanService omega t :=
      stationaryPriorityArrivalWindowTotalSquareWork_neg_to_zero meanService omega t

/-- The expected squared service reward of the literal stationary job ledger
over `[-t,0)` is the finite-class exponential second-moment rate. -/
theorem integral_stationaryPriorityArrivalWindowJobs_squareServiceWork_neg_to_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ omega, ((stationaryPriorityArrivalWindowJobs meanService omega (-t) 0).map
      (fun job => job.serviceWork ^ 2)).sum
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      2 * (∑ i, arrivalRate i * meanService i ^ 2) * t := by
  calc
    ∫ omega, ((stationaryPriorityArrivalWindowJobs meanService omega (-t) 0).map
        (fun job => job.serviceWork ^ 2)).sum
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
        ∫ omega, stationaryPriorityTotalPastSquareWorkAggregate meanService omega t
          ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with omega
            exact stationaryPriorityArrivalWindowJobs_squareServiceWork_neg_to_zero
              meanService omega t
    _ = 2 * (∑ i, arrivalRate i * meanService i ^ 2) * t :=
      integral_stationaryPriorityTotalPastSquareWorkAggregate
        arrivalRate meanService harrivalRate t ht

/-- The scalar terminal workload of the literal finite trace, defined directly
from the chronological stationary arrival ledger.  Unlike the full queue
state, this real-valued observable admits a clean countable-fiber Borel proof. -/
def stationaryPriorityFiniteWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) : ℝ :=
  nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
    (stationaryPriorityArrivalWindowJobs meanService omega a b) b

/-- The literal terminal workload of every finite stationary arrival window
is Borel.  The proof glues the fixed finite-trace recursion along the
countably many canonical labelled-index ledgers. -/
theorem measurable_stationaryPriorityFiniteWindowTerminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (a b : ℝ) :
    Measurable (fun omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega a b) := by
  refine Probability.measurable_of_countable_measurable_cover
    (fun labels : List (NonpreemptivePriorityArrivalIndex n) =>
      {omega | canonicalStationaryPriorityArrivalWindowIndices omega a b = labels})
    (fun labels => measurableSet_canonicalStationaryPriorityArrivalWindowIndices_eq a b labels)
    ?_ (fun omega =>
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega a b)
    (fun labels omega => nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
      (evaluateNonpreemptivePriorityJobList
        (labels.map (stationaryPriorityArrivalJobCoordinate meanService)) omega) b)
    ?_ ?_
  · ext omega
    constructor
    · intro _
      simp
    · intro _
      exact Set.mem_iUnion.mpr
        ⟨canonicalStationaryPriorityArrivalWindowIndices omega a b, rfl⟩
  · intro labels
    apply measurable_nonpreemptivePriorityArrivalTraceTerminalResidualWork_eval
      (fun _ => a) (fun _ => 0) (fun _ => b) measurable_const measurable_const
      measurable_const
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
    exact stationaryPriorityArrivalJobCoordinate_coordinatesMeasurable meanService q
  · intro labels omega hlabels
    simp only [stationaryPriorityFiniteWindowTerminalResidualWork,
      stationaryPriorityArrivalWindowJobs,
      canonicalStationaryPriorityArrivalWindowJobs,
      stationaryPriorityArrivalJobCoordinate,
      evaluateNonpreemptivePriorityJobList, List.map_map]
    rw [hlabels]
    rfl

/-- Jobs in a literal stationary-input window are presented to the finite
trace in nondecreasing physical arrival-time order. -/
theorem pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    (stationaryPriorityArrivalWindowJobs meanService omega a b).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
  exact pairwise_arrivalTime_le_canonicalStationaryPriorityArrivalWindowJobs
    meanService omega a b

/-- The deterministic labelled-arrival order lifted to the concrete jobs in a
stationary ledger.  The equality clause makes this a genuine antisymmetric
order on arbitrary job records while agreeing with the index order on the
canonical ledger. -/
def stationaryPriorityArrivalJobLE
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (first second : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) : Prop :=
  stationaryPriorityArrivalIndexLE omega first.identifier second.identifier ∧
    (first.identifier = second.identifier → first = second)

/-- The lifted deterministic labelled-arrival order is antisymmetric. -/
theorem stationaryPriorityArrivalJobLE_antisymm
    {n : ℕ} (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    {first second : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)}
    (hfirst : stationaryPriorityArrivalJobLE omega first second)
    (hsecond : stationaryPriorityArrivalJobLE omega second first) :
    first = second := by
  exact hfirst.2 (stationaryPriorityArrivalIndexLE_antisymm omega hfirst.1 hsecond.1)

/-- Canonical stationary job ledgers are ordered by their labelled-arrival
keys, including a deterministic convention at simultaneous epochs. -/
theorem pairwise_stationaryPriorityArrivalJobLE_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    (stationaryPriorityArrivalWindowJobs meanService omega a b).Pairwise
      (stationaryPriorityArrivalJobLE omega) := by
  unfold stationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowJobs stationaryPriorityArrivalJobLE
  rw [List.pairwise_map]
  apply (pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices omega a b).imp
  intro first second horder
  refine ⟨horder, ?_⟩
  intro hidentifier
  have hindex : first = second := by
    simpa using hidentifier
  subst second
  rfl

/-- A literal stationary job ledger contains each labelled arrival at most
once. -/
theorem nodup_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    (stationaryPriorityArrivalWindowJobs meanService omega a b).Nodup := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  unfold stationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowJobs
  apply List.Nodup.map
  · intro first second hjob
    simpa using congrArg NonpreemptivePriorityJob.identifier hjob
  · exact Finset.sort_nodup _ _

/-- The public stationary job ledger has an exact physical-time append law
across adjacent half-open windows. -/
theorem stationaryPriorityArrivalWindowJobs_append
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    stationaryPriorityArrivalWindowJobs meanService omega a b =
      stationaryPriorityArrivalWindowJobs meanService omega a c ++
        stationaryPriorityArrivalWindowJobs meanService omega c b := by
  exact canonicalStationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb

/-- Total marked work is additive across adjacent literal stationary arrival
windows. -/
theorem stationaryPriorityArrivalWindowTotalWork_append
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    stationaryPriorityArrivalWindowTotalWork meanService omega a b =
      stationaryPriorityArrivalWindowTotalWork meanService omega a c +
        stationaryPriorityArrivalWindowTotalWork meanService omega c b := by
  have hwork : ∀ x y,
      nonpreemptivePriorityArrivalTraceServiceWork
        (stationaryPriorityArrivalWindowJobs meanService omega x y) =
        stationaryPriorityArrivalWindowTotalWork meanService omega x y := by
    intro x y
    simpa [stationaryPriorityArrivalWindowJobs] using
      nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
        meanService omega x y
  calc
    stationaryPriorityArrivalWindowTotalWork meanService omega a b =
        nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega a b) :=
      (hwork a b).symm
    _ = nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega a c ++
            stationaryPriorityArrivalWindowJobs meanService omega c b) := by
          rw [stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb]
    _ = nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega a c) +
        nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega c b) := by
          simp [nonpreemptivePriorityArrivalTraceServiceWork]
    _ = stationaryPriorityArrivalWindowTotalWork meanService omega a c +
        stationaryPriorityArrivalWindowTotalWork meanService omega c b := by
          rw [hwork a c, hwork c b]

/-- The marked work in a past subwindow is the difference of the two nested
past-work aggregates. -/
theorem stationaryPriorityArrivalWindowTotalWork_neg_to_neg
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (older newer : ℝ) (hnewer : 0 ≤ newer) (horizon : newer ≤ older) :
    stationaryPriorityArrivalWindowTotalWork meanService omega (-older) (-newer) =
      stationaryPriorityTotalPastWorkAggregate meanService omega older -
        stationaryPriorityTotalPastWorkAggregate meanService omega newer := by
  have happend := stationaryPriorityArrivalWindowTotalWork_append
    meanService omega (-older) (-newer) 0 (neg_le_neg horizon) (neg_nonpos.mpr hnewer)
  rw [stationaryPriorityArrivalWindowTotalWork_neg_to_zero meanService omega older,
    stationaryPriorityArrivalWindowTotalWork_neg_to_zero meanService omega newer] at happend
  linarith

/-- A backward time horizon is a net-input cutoff when the cumulative marked
work minus elapsed service capacity never exceeds its value at that horizon. -/
def stationaryPriorityNetPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff : ℝ) : Prop :=
  ∀ horizon, cutoff ≤ horizon →
    stationaryPriorityNetPastInput meanService omega horizon ≤
      stationaryPriorityNetPastInput meanService omega cutoff

/-- A backward net-input cutoff bounds the total marked work in every older
past interval ending at that cutoff by its available elapsed service. -/
theorem stationaryPriorityArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff older : ℝ) (hcutoff : stationaryPriorityNetPastCutoff meanService omega cutoff)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older) :
    stationaryPriorityArrivalWindowTotalWork meanService omega (-older) (-cutoff) ≤
      older - cutoff := by
  have hmax := hcutoff older horizon
  unfold stationaryPriorityNetPastCutoff stationaryPriorityNetPastInput at hmax
  rw [stationaryPriorityArrivalWindowTotalWork_neg_to_neg
    meanService omega older cutoff hcutoffNonneg horizon]
  linarith

/-- The stationary-input trace contains exactly the marked arrivals whose
literal epochs lie in its half-open window. -/
theorem mem_stationaryPriorityArrivalWindowJobs_iff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b ↔
      ∃ (i : Fin n) (k : ℤ),
        k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b (omega i).1 ∧
        job =
          { identifier := Sigma.mk i k
            priority := i
            arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k
            serviceWork := stationaryPriorityWorkRequirement meanService i omega k } := by
  unfold stationaryPriorityArrivalWindowJobs canonicalStationaryPriorityArrivalWindowJobs
  simp only [List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, q.2,
      (mem_canonicalStationaryPriorityArrivalWindowIndices_iff omega a b q).mp hq, rfl⟩
  · rintro ⟨i, k, hindex, rfl⟩
    exact ⟨Sigma.mk i k,
      (mem_canonicalStationaryPriorityArrivalWindowIndices_iff omega a b (Sigma.mk i k)).mpr hindex,
      rfl⟩

/-- Every job admitted from a literal stationary-input window occurs before
the window's right endpoint. -/
theorem arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b) :
    job.arrivalTime < b := by
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, hindex, hjob⟩
  subst job
  have harrival :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (omega i).1 k).mp hindex
  simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
    Probability.Queueing.stationaryPoissonWorkArrival,
    Probability.Queueing.timedEmbeddedArrival] using harrival.2

/-- Every job admitted from a literal stationary-input window occurs at or
after the window's left endpoint. -/
theorem left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b) :
    a ≤ job.arrivalTime := by
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, hindex, hjob⟩
  subst job
  have harrival :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (omega i).1 k).mp hindex
  simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
    Probability.Queueing.stationaryPoissonWorkArrival,
    Probability.Queueing.timedEmbeddedArrival] using harrival.1

/-- The literal finite stationary-window workload is exactly the reflected
maximum of its genuine arrival-suffix net-work candidates.  This is a
pathwise identity; proving integrability of the growing remote-past maximum
remains a separate stationary-input argument. -/
theorem stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b) :
    stationaryPriorityFiniteWindowTerminalResidualWork meanService omega a b =
      nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum b
        (stationaryPriorityArrivalWindowJobs meanService omega a b) := by
  unfold stationaryPriorityFiniteWindowTerminalResidualWork
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_empty_eq_suffixMaximum
  · exact hab
  · intro job hjob
    exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega a b job hjob
  · exact pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a b
  · intro job hjob
    exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega a b job hjob).le

/-- Starting a literal stationary trace farther in the past can only increase
its terminal workload.  Equivalently, each larger physical window contributes
additional reflected suffix candidates while retaining all later ones. -/
theorem stationaryPriorityFiniteWindowTerminalResidualWork_mono_left
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    stationaryPriorityFiniteWindowTerminalResidualWork meanService omega c b ≤
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega a b := by
  calc
    stationaryPriorityFiniteWindowTerminalResidualWork meanService omega c b =
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum b
          (stationaryPriorityArrivalWindowJobs meanService omega c b) :=
      stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega c b hcb
    _ ≤ nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum b
          (stationaryPriorityArrivalWindowJobs meanService omega a b) := by
      rw [stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb]
      exact nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_le_append b
        (stationaryPriorityArrivalWindowJobs meanService omega a c)
        (stationaryPriorityArrivalWindowJobs meanService omega c b)
    _ = stationaryPriorityFiniteWindowTerminalResidualWork meanService omega a b :=
      (stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega a b (hac.trans hcb)).symm

/-- A tail beginning at an actual arrival in a literal stationary ledger has
no more marked work than the whole literal window beginning at that arrival.
This retains the physical epochs of simultaneous arrivals while allowing the
backward net-input bound to be applied to every arrival suffix. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_stationaryPriorityArrivalWindowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (older cutoff : ℝ)
    (front suffix : List (NonpreemptivePriorityJob n
      (NonpreemptivePriorityArrivalIndex n)))
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hpositive : ∀ other ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff), 0 < other.serviceWork)
    (hsplit : stationaryPriorityArrivalWindowJobs meanService omega (-older) (-cutoff) =
      front ++ job :: suffix) :
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
      stationaryPriorityArrivalWindowTotalWork meanService omega job.arrivalTime (-cutoff) := by
  let full := stationaryPriorityArrivalWindowJobs meanService omega (-older) (-cutoff)
  let tailWindow := stationaryPriorityArrivalWindowJobs meanService omega job.arrivalTime (-cutoff)
  have hjobFull : job ∈ full := by
    rw [show full = front ++ job :: suffix by exact hsplit]
    simp
  have htimeSorted : full.Pairwise (fun first second =>
      first.arrivalTime ≤ second.arrivalTime) := by
    exact pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff)
  have htailTime : ∀ other ∈ job :: suffix, job.arrivalTime ≤ other.arrivalTime := by
    have hsplitSorted : (front ++ job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) := by
      rw [show full = front ++ job :: suffix by exact hsplit] at htimeSorted
      exact htimeSorted
    have htailSorted : (job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) :=
      (List.pairwise_append.mp hsplitSorted).2.1
    rcases List.pairwise_cons.mp htailSorted with ⟨hhead, _⟩
    intro other hother
    rcases List.mem_cons.mp hother with rfl | hother
    · exact le_rfl
    · exact hhead other hother
  have htailSubset : (job :: suffix) ⊆ tailWindow := by
    intro other hother
    have hotherFull : other ∈ full := by
      rw [show full = front ++ job :: suffix by exact hsplit]
      exact List.mem_append_right _ hother
    have htime := htailTime other hother
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-older) (-cutoff) other).mp hotherFull with
      ⟨i, k, hindex, hother⟩
    subst other
    apply (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega job.arrivalTime (-cutoff)
      { identifier := Sigma.mk i k
        priority := i
        arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k
        serviceWork := stationaryPriorityWorkRequirement meanService i omega k }).mpr
    refine ⟨i, k, ?_, rfl⟩
    have hfullBounds := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      (-older) (-cutoff) (omega i).1 k).mp hindex
    apply (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      job.arrivalTime (-cutoff) (omega i).1 k).mpr
    constructor
    · simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
        Probability.Queueing.stationaryPoissonWorkArrival,
        Probability.Queueing.timedEmbeddedArrival] using htime
    · exact hfullBounds.2
  have hjobLeft : -older ≤ job.arrivalTime := by
    apply left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff) job
    exact hjobFull
  have htailWindowSubset : tailWindow ⊆ full := by
    intro other hother
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega job.arrivalTime (-cutoff) other).mp hother with
      ⟨i, k, hindex, hother⟩
    subst other
    apply (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-older) (-cutoff)
      { identifier := Sigma.mk i k
        priority := i
        arrivalTime := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i omega k
        serviceWork := stationaryPriorityWorkRequirement meanService i omega k }).mpr
    refine ⟨i, k, ?_, rfl⟩
    have htailBounds := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      job.arrivalTime (-cutoff) (omega i).1 k).mp hindex
    apply (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      (-older) (-cutoff) (omega i).1 k).mpr
    exact ⟨hjobLeft.trans htailBounds.1, htailBounds.2⟩
  have htailNodup : (job :: suffix).Nodup := by
    have hfullNodup := nodup_stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff)
    change full.Nodup at hfullNodup
    rw [show full = front ++ job :: suffix by exact hsplit] at hfullNodup
    exact List.Nodup.of_append_right hfullNodup
  have htailOrder : (job :: suffix).Pairwise (stationaryPriorityArrivalJobLE omega) := by
    have hfullOrder :=
      pairwise_stationaryPriorityArrivalJobLE_stationaryPriorityArrivalWindowJobs
        meanService omega (-older) (-cutoff)
    change full.Pairwise (stationaryPriorityArrivalJobLE omega) at hfullOrder
    rw [show full = front ++ job :: suffix by exact hsplit] at hfullOrder
    exact (List.pairwise_append.mp hfullOrder).2.1
  have htailWindowOrder : tailWindow.Pairwise (stationaryPriorityArrivalJobLE omega) := by
    exact pairwise_stationaryPriorityArrivalJobLE_stationaryPriorityArrivalWindowJobs
      meanService omega job.arrivalTime (-cutoff)
  letI : Std.Antisymm (stationaryPriorityArrivalJobLE omega) :=
    ⟨fun _ _ hfirst hsecond => stationaryPriorityArrivalJobLE_antisymm omega hfirst hsecond⟩
  have htailSublist : List.Sublist (job :: suffix) tailWindow := by
    apply List.sublist_of_subperm_of_pairwise (r := stationaryPriorityArrivalJobLE omega)
    · exact htailNodup.subperm htailSubset
    · exact htailOrder
    · exact htailWindowOrder
  calc
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) =
        ((job :: suffix).map fun other => other.serviceWork).sum := rfl
    _ ≤ (tailWindow.map fun other => other.serviceWork).sum := by
      apply List.Sublist.sum_le_sum (htailSublist.map fun other => other.serviceWork)
      intro work hwork
      rcases List.mem_map.mp hwork with ⟨other, hother, rfl⟩
      exact (hpositive other (htailWindowSubset hother)).le
    _ = stationaryPriorityArrivalWindowTotalWork
        meanService omega job.arrivalTime (-cutoff) := by
      simpa [tailWindow, stationaryPriorityArrivalWindowJobs] using
        (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
          meanService omega job.arrivalTime (-cutoff))

/-- A global backward net-input cutoff empties the literal reflected workload
at that cutoff, for every finite start no later than the cutoff.  The proof
uses the exact arrival suffixes, so no artificial batch discretization is
introduced. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_stationaryPriorityNetPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityNetPastCutoff meanService omega cutoff)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff), 0 < job.serviceWork) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-older) 0
      (stationaryPriorityArrivalWindowJobs meanService omega (-older) (-cutoff))
      (-cutoff) = 0 := by
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_all_suffixes_le
  · rw [show nonpreemptivePriorityArrivalTraceServiceWork
        (stationaryPriorityArrivalWindowJobs meanService omega (-older) (-cutoff)) =
        stationaryPriorityArrivalWindowTotalWork meanService omega (-older) (-cutoff) by
      simpa [stationaryPriorityArrivalWindowJobs] using
        (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
          meanService omega (-older) (-cutoff))]
    have hbound := stationaryPriorityArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
      meanService omega cutoff older hcutoff hcutoffNonneg horizon
    linarith
  · intro front suffix job hsplit
    have hjobMem : job ∈ stationaryPriorityArrivalWindowJobs
        meanService omega (-older) (-cutoff) := by
      rw [hsplit]
      simp
    have hjobBeforeCutoff : job.arrivalTime ≤ -cutoff :=
      (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega (-older) (-cutoff) job hjobMem).le
    have hjobHorizon : cutoff ≤ -job.arrivalTime := by
      linarith
    calc
      nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
          stationaryPriorityArrivalWindowTotalWork
            meanService omega job.arrivalTime (-cutoff) :=
        nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_stationaryPriorityArrivalWindowTotalWork
          meanService omega older cutoff front suffix job hpositive hsplit
      _ ≤ -job.arrivalTime - cutoff := by
        simpa using stationaryPriorityArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
          meanService omega cutoff (-job.arrivalTime) hcutoff hcutoffNonneg hjobHorizon
      _ = -cutoff - job.arrivalTime := by ring

/-- If a nonempty past-window ledger is written from its first physical
arrival onward, no literal stationary arrival lies strictly between the
window's left endpoint and that first epoch. -/
theorem stationaryPriorityArrivalWindowJobs_left_of_head_eq_nil
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ)
    (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hledger : stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = head :: tail) :
    stationaryPriorityArrivalWindowJobs meanService omega (-t) head.arrivalTime = [] := by
  have hheadMem : head ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 := by
    rw [hledger]
    simp
  have hleft : -t ≤ head.arrivalTime :=
    left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0 head hheadMem
  have hright : head.arrivalTime ≤ 0 :=
    (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega (-t) 0 head hheadMem).le
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro job hjob
  have hfull : job ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 := by
    rw [stationaryPriorityArrivalWindowJobs_append
      meanService omega (-t) head.arrivalTime 0 hleft hright]
    exact List.mem_append_left _ hjob
  have hfull' : job ∈ head :: tail := by
    rwa [hledger] at hfull
  have hleftRight : job.arrivalTime < head.arrivalTime :=
    arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega (-t) head.arrivalTime job hjob
  have hnothead : job ≠ head := by
    intro heq
    subst job
    exact (lt_irrefl _ hleftRight).elim
  have htail : job ∈ tail := (List.mem_cons.mp hfull').resolve_left hnothead
  have hsorted := pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs
    meanService omega (-t) 0
  rw [hledger] at hsorted
  have hheadLe : head.arrivalTime ≤ job.arrivalTime :=
    (List.pairwise_cons.mp hsorted).1 job htail
  exact (not_le_of_gt hleftRight) hheadLe

/-- On a nonempty past window, the backward net input at the window horizon
is no larger than its value at the age of the window's first physical arrival.
Between those two horizons no new marked work is encountered. -/
theorem stationaryPriorityNetPastInput_le_at_firstArrivalAge
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ)
    (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hledger : stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = head :: tail) :
    stationaryPriorityNetPastInput meanService omega t ≤
      stationaryPriorityNetPastInput meanService omega (-head.arrivalTime) := by
  have hheadMem : head ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 := by
    rw [hledger]
    simp
  have hleft : -t ≤ head.arrivalTime :=
    left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0 head hheadMem
  have hright : head.arrivalTime ≤ 0 :=
    (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega (-t) 0 head hheadMem).le
  have hempty := stationaryPriorityArrivalWindowJobs_left_of_head_eq_nil
    meanService omega t head tail hledger
  have hleftWork : stationaryPriorityArrivalWindowTotalWork
      meanService omega (-t) head.arrivalTime = 0 := by
    calc
      stationaryPriorityArrivalWindowTotalWork meanService omega (-t) head.arrivalTime =
          nonpreemptivePriorityArrivalTraceServiceWork
            (stationaryPriorityArrivalWindowJobs meanService omega (-t) head.arrivalTime) := by
              simpa [stationaryPriorityArrivalWindowJobs] using
                (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
                  meanService omega (-t) head.arrivalTime).symm
      _ = 0 := by simp [hempty, nonpreemptivePriorityArrivalTraceServiceWork]
  have happend := stationaryPriorityArrivalWindowTotalWork_append
    meanService omega (-t) head.arrivalTime 0 hleft hright
  have hfull : stationaryPriorityArrivalWindowTotalWork meanService omega (-t) 0 =
      stationaryPriorityTotalPastWorkAggregate meanService omega t :=
    stationaryPriorityArrivalWindowTotalWork_neg_to_zero meanService omega t
  have htail : stationaryPriorityArrivalWindowTotalWork meanService omega
      head.arrivalTime 0 =
      stationaryPriorityTotalPastWorkAggregate meanService omega (-head.arrivalTime) := by
    simpa using
      (stationaryPriorityArrivalWindowTotalWork_neg_to_zero
        meanService omega (-head.arrivalTime))
  rw [hfull, htail, hleftWork] at happend
  have hage : -head.arrivalTime ≤ t := by linarith
  unfold stationaryPriorityNetPastInput
  linarith

/-- At every nonnegative backward horizon, the net input is bounded either by
the origin value or by its value at the age of one of the finitely many
literal arrivals in that past window. -/
theorem stationaryPriorityNetPastInput_le_zero_or_firstArrivalAge
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    stationaryPriorityNetPastInput meanService omega t ≤ 0 ∨
      ∃ (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
        (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))),
        stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = head :: tail ∧
          0 ≤ -head.arrivalTime ∧ -head.arrivalTime ≤ t ∧
          stationaryPriorityNetPastInput meanService omega t ≤
            stationaryPriorityNetPastInput meanService omega (-head.arrivalTime) := by
  cases hledger : stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 with
  | nil =>
      left
      have hwork : stationaryPriorityTotalPastWorkAggregate meanService omega t = 0 := by
        calc
          stationaryPriorityTotalPastWorkAggregate meanService omega t =
              stationaryPriorityArrivalWindowTotalWork meanService omega (-t) 0 :=
            (stationaryPriorityArrivalWindowTotalWork_neg_to_zero meanService omega t).symm
          _ = nonpreemptivePriorityArrivalTraceServiceWork
                (stationaryPriorityArrivalWindowJobs meanService omega (-t) 0) := by
              simpa [stationaryPriorityArrivalWindowJobs] using
                (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
                  meanService omega (-t) 0).symm
          _ = 0 := by simp [hledger, nonpreemptivePriorityArrivalTraceServiceWork]
      unfold stationaryPriorityNetPastInput
      linarith
  | cons head tail =>
      right
      have hheadMem : head ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 := by
        rw [hledger]
        simp
      have hleft := left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
        meanService omega (-t) 0 head hheadMem
      have hright := arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega (-t) 0 head hheadMem
      refine ⟨head, tail, rfl, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · exact stationaryPriorityNetPastInput_le_at_firstArrivalAge
          meanService omega t head tail hledger

/-- On every bounded nonnegative backward-time interval, the literal
stationary net-input path attains a maximum at the origin or at the age of a
finite-window arrival. -/
theorem exists_stationaryPriorityNetPastInput_max_on_compact
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (radius : ℝ) (hradius : 0 ≤ radius) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧ cutoff ≤ radius ∧
      ∀ horizon, 0 ≤ horizon → horizon ≤ radius →
        stationaryPriorityNetPastInput meanService omega horizon ≤
          stationaryPriorityNetPastInput meanService omega cutoff := by
  let ledger := stationaryPriorityArrivalWindowJobs meanService omega (-radius) 0
  let candidateValues : List ℝ := 0 :: ledger.map fun job =>
    stationaryPriorityNetPastInput meanService omega (-job.arrivalTime)
  have hlength : 0 < candidateValues.length := by
    simp [candidateValues]
  let maximum : ℝ := candidateValues.maximum_of_length_pos hlength
  have hmaximumMem : maximum ∈ candidateValues :=
    candidateValues.maximum_of_length_pos_mem hlength
  have hleMaximum : ∀ value ∈ candidateValues, value ≤ maximum := by
    intro value hvalue
    exact candidateValues.le_maximum_of_length_pos_of_mem hvalue hlength
  have hzeroMem : (0 : ℝ) ∈ candidateValues := by
    simp [candidateValues]
  have hzeroLe : 0 ≤ maximum := hleMaximum 0 hzeroMem
  have hsplitMaximum : maximum = 0 ∨
      ∃ job ∈ ledger,
        stationaryPriorityNetPastInput meanService omega (-job.arrivalTime) = maximum := by
    simpa only [candidateValues, List.mem_cons, List.mem_map] using hmaximumMem
  rcases hsplitMaximum with hzero | ⟨cutoffJob, hcutoffMem, hcutoffValue⟩
  · refine ⟨0, le_rfl, hradius, ?_⟩
    intro horizon hnonneg hbound
    rcases stationaryPriorityNetPastInput_le_zero_or_firstArrivalAge
      meanService omega horizon hnonneg with hinput | ⟨head, tail, hhead, _, _, hheadInput⟩
    · have hnetZero : stationaryPriorityNetPastInput meanService omega 0 = 0 := by
        simp [stationaryPriorityNetPastInput,
          stationaryPriorityTotalPastWorkAggregate_zero]
      exact hinput.trans_eq hnetZero.symm
    · have hheadMem : head ∈ ledger := by
        have hfull : head ∈ stationaryPriorityArrivalWindowJobs
            meanService omega (-radius) 0 := by
          rw [stationaryPriorityArrivalWindowJobs_append
            meanService omega (-radius) (-horizon) 0
            (neg_le_neg hbound) (neg_nonpos.mpr hnonneg)]
          apply List.mem_append_right
          rw [hhead]
          simp
        simpa [ledger] using hfull
      have hheadValue : stationaryPriorityNetPastInput meanService omega
          (-head.arrivalTime) ∈ candidateValues := by
        apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨head, hheadMem, rfl⟩
      have hboundHead := hleMaximum _ hheadValue
      rw [hzero] at hboundHead
      have hnetZero : stationaryPriorityNetPastInput meanService omega 0 = 0 := by
        simp [stationaryPriorityNetPastInput,
          stationaryPriorityTotalPastWorkAggregate_zero]
      exact hheadInput.trans (by simpa [hnetZero] using hboundHead)
  · have hcutoffLeft : -radius ≤ cutoffJob.arrivalTime := by
      simpa [ledger] using
        left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
          meanService omega (-radius) 0 cutoffJob hcutoffMem
    have hcutoffRight : cutoffJob.arrivalTime < 0 := by
      simpa [ledger] using
        arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
          meanService omega (-radius) 0 cutoffJob hcutoffMem
    refine ⟨-cutoffJob.arrivalTime, by linarith, by linarith, ?_⟩
    intro horizon hnonneg hbound
    rcases stationaryPriorityNetPastInput_le_zero_or_firstArrivalAge
      meanService omega horizon hnonneg with hinput | ⟨head, tail, hhead, _, _, hheadInput⟩
    · calc
        stationaryPriorityNetPastInput meanService omega horizon ≤ 0 := hinput
        _ ≤ maximum := hzeroLe
        _ = stationaryPriorityNetPastInput meanService omega (-cutoffJob.arrivalTime) :=
          hcutoffValue.symm
    · have hheadMem : head ∈ ledger := by
        have hfull : head ∈ stationaryPriorityArrivalWindowJobs
            meanService omega (-radius) 0 := by
          rw [stationaryPriorityArrivalWindowJobs_append
            meanService omega (-radius) (-horizon) 0
            (neg_le_neg hbound) (neg_nonpos.mpr hnonneg)]
          apply List.mem_append_right
          rw [hhead]
          simp
        simpa [ledger] using hfull
      have hheadValue : stationaryPriorityNetPastInput meanService omega
          (-head.arrivalTime) ∈ candidateValues := by
        apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨head, hheadMem, rfl⟩
      have hboundHead := hleMaximum _ hheadValue
      rw [← hcutoffValue] at hboundHead
      exact hheadInput.trans hboundHead

/-- A literal backward net-input path that tends to `-∞` has a nonnegative
global maximizing horizon.  Its maximum is attained at the origin or at an
actual arrival age, rather than at an artificial time bin. -/
theorem exists_stationaryPriorityNetPastCutoff_of_tendsto_atBot
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (hlimit : Filter.Tendsto
      (stationaryPriorityNetPastInput meanService omega)
      Filter.atTop Filter.atBot) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff := by
  have htail : ∀ᶠ horizon : ℝ in Filter.atTop,
      stationaryPriorityNetPastInput meanService omega horizon ≤ 0 :=
    Filter.tendsto_atBot.1 hlimit 0
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  let radius : ℝ := max bound 0
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    exact le_max_right _ _
  have hboundRadius : bound ≤ radius := by
    dsimp [radius]
    exact le_max_left _ _
  rcases exists_stationaryPriorityNetPastInput_max_on_compact
    meanService omega radius hradius with
    ⟨cutoff, hcutoffNonneg, hcutoffRadius, hmaximum⟩
  refine ⟨cutoff, hcutoffNonneg, ?_⟩
  intro horizon _
  by_cases hwithin : horizon ≤ radius
  · exact hmaximum horizon (le_trans hcutoffNonneg (by linarith)) hwithin
  · have htailHorizon : stationaryPriorityNetPastInput meanService omega horizon ≤ 0 :=
      hbound horizon (le_trans hboundRadius (le_of_not_ge hwithin))
    have hzero : stationaryPriorityNetPastInput meanService omega 0 = 0 := by
      simp [stationaryPriorityNetPastInput,
        stationaryPriorityTotalPastWorkAggregate_zero]
    have hcutoffNonnegative : 0 ≤ stationaryPriorityNetPastInput meanService omega cutoff := by
      simpa [hzero] using hmaximum 0 le_rfl hradius
    exact htailHorizon.trans hcutoffNonnegative

/-- Strict total load gives an almost-sure nonnegative global maximum horizon
for the literal continuous-time stationary net-input path. -/
theorem ae_exists_stationaryPriorityNetPastCutoff
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService omega cutoff := by
  filter_upwards [ae_tendsto_stationaryPriorityNetPastInput_atBot
    arrivalRate meanService harrivalRate hstable] with omega hlimit
  exact exists_stationaryPriorityNetPastCutoff_of_tendsto_atBot meanService omega hlimit

/-- If a literal past window has strictly less marked work than its elapsed
service capacity, its chronological physical trace has an actual empty epoch
strictly inside that window (or at the observation epoch). -/
theorem exists_stationaryPriorityArrivalWindow_terminalReset_of_totalPastWork_lt
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0,
      0 < job.serviceWork)
    (hnet : stationaryPriorityTotalPastWorkAggregate meanService omega t < t) :
    ∃ (front suffix : List (NonpreemptivePriorityJob n
      (NonpreemptivePriorityArrivalIndex n))) (resetTime : ℝ),
      stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = front ++ suffix ∧
        -t < resetTime ∧ resetTime ≤ 0 ∧
          (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
          (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
          nonpreemptivePriorityArrivalTraceTerminalResidualWork
            (-t) 0 front resetTime = 0 := by
  apply exists_nonpreemptivePriorityArrivalTrace_terminalReset_of_serviceWork_lt
  · intro job hjob
    exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0 job hjob
  · exact pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0
  · intro job hjob
    exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega (-t) 0 job hjob).le
  · exact hpositive
  · rw [show nonpreemptivePriorityArrivalTraceServiceWork
        (stationaryPriorityArrivalWindowJobs meanService omega (-t) 0) =
        stationaryPriorityTotalPastWorkAggregate meanService omega t by
      simpa [stationaryPriorityArrivalWindowJobs] using
        (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
          meanService omega (-t) 0).trans
          (stationaryPriorityArrivalWindowTotalWork_neg_to_zero meanService omega t)]
    simpa using hnet

/-- The scalar reset supplied by a strict-slack stationary past window is a
genuine live-state reset of the literal nonpreemptive-priority execution. -/
theorem exists_stationaryPriorityArrivalWindow_liveReset_of_totalPastWork_lt
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0,
      0 < job.serviceWork)
    (hnet : stationaryPriorityTotalPastWorkAggregate meanService omega t < t) :
    ∃ (front suffix : List (NonpreemptivePriorityJob n
      (NonpreemptivePriorityArrivalIndex n))) (resetTime : ℝ),
      stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = front ++ suffix ∧
        -t < resetTime ∧ resetTime ≤ 0 ∧
          (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
          (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
          liveEquivalentNonpreemptivePriorityWorkState
            (advanceNonpreemptivePriorityWorkState
              (totalNonpreemptivePriorityWorkJobs
                (runNonpreemptivePriorityArrivalTrace
                  (emptyNonpreemptivePriorityWorkState
                    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t)) front))
              resetTime
              (runNonpreemptivePriorityArrivalTrace
                (emptyNonpreemptivePriorityWorkState
                  (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t)) front))
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) resetTime) := by
  rcases exists_stationaryPriorityArrivalWindow_terminalReset_of_totalPastWork_lt
    meanService omega t hpositive hnet with
    ⟨front, suffix, resetTime, hsplit, hleft, hright, hfrontCut, hsuffix, hscalar⟩
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t)
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  let resetState := advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterFront) resetTime afterFront
  have hinPositive : positiveNonpreemptivePriorityResidualWork initial := by
    constructor
    · intro active hactive
      simp [initial, emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [initial, emptyNonpreemptivePriorityWorkState] at hmember
  have hinWork : nonpreemptivePriorityWorkConserving initial := by
    simpa [initial] using
      (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t))
  have hinTotal : totalNonpreemptivePriorityResidualWork initial = 0 := by
    simp [initial, emptyNonpreemptivePriorityWorkState,
      totalNonpreemptivePriorityResidualWork,
      activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork]
  have hfrontStart : ∀ job ∈ front, initial.currentTime ≤ job.arrivalTime := by
    intro job hjob
    rw [show initial.currentTime = -t by rfl]
    apply left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0 job
    rw [hsplit]
    exact List.mem_append_left _ hjob
  have hfrontSorted : front.Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
    have hsorted := pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs
      meanService omega (-t) 0
    rw [hsplit] at hsorted
    exact (List.pairwise_append.mp hsorted).1
  have hfrontPositive : ∀ job ∈ front, 0 < job.serviceWork := by
    intro job hjob
    apply hpositive job
    rw [hsplit]
    exact List.mem_append_left _ hjob
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterFront := by
    dsimp [afterFront]
    exact positiveNonpreemptivePriorityResidualWork_run initial front
      hinPositive hfrontPositive
  have hafterTime : afterFront.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime initial.currentTime front := by
    dsimp [afterFront]
    exact runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
      initial front hfrontStart hfrontSorted
  have hafterCut : afterFront.currentTime ≤ resetTime := by
    rw [hafterTime]
    exact nonpreemptivePriorityArrivalTraceEndTime_le initial.currentTime resetTime front
      hleft.le hfrontCut
  have hresetPositive : positiveNonpreemptivePriorityResidualWork resetState := by
    dsimp [resetState]
    exact positiveNonpreemptivePriorityResidualWork_advance
      (totalNonpreemptivePriorityWorkJobs afterFront) resetTime afterFront hafterPositive
  have hresetTotal : totalNonpreemptivePriorityResidualWork resetState = 0 := by
    calc
      totalNonpreemptivePriorityResidualWork resetState =
          nonpreemptivePriorityArrivalTraceTerminalResidualWork initial.currentTime
            (totalNonpreemptivePriorityResidualWork initial) front resetTime := by
              dsimp [resetState, afterFront]
              apply totalNonpreemptivePriorityResidualWork_advance_run_eq_terminalResidualWork
              · exact hinPositive
              · exact hinWork
              · exact hleft.le
              · exact hfrontStart
              · exact hfrontSorted
              · exact hfrontCut
              · exact hfrontPositive
      _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork (-t) 0
          front resetTime := by rw [show initial.currentTime = -t by rfl, hinTotal]
      _ = 0 := hscalar
  have hresetTime : resetState.currentTime = resetTime := by
    dsimp [resetState]
    exact advanceNonpreemptivePriorityWorkState_currentTime_eq_target
      (totalNonpreemptivePriorityWorkJobs afterFront) resetTime afterFront hafterCut le_rfl
  refine ⟨front, suffix, resetTime, hsplit, hleft, hright, hfrontCut, hsuffix, ?_⟩
  have hempty : emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) resetTime =
      emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) resetState.currentTime := by
    rw [hresetTime]
  rw [hempty]
  simpa only [resetState, afterFront, initial] using
    (liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
      resetState hresetPositive hresetTotal)

/-- A literal past window has a live reset when its finite physical trace can
be split at an epoch where the execution has no active or waiting job. -/
def stationaryPriorityArrivalWindowHasLiveReset
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) : Prop :=
  ∃ (front suffix : List (NonpreemptivePriorityJob n
    (NonpreemptivePriorityArrivalIndex n))) (resetTime : ℝ),
    stationaryPriorityArrivalWindowJobs meanService omega (-t) 0 = front ++ suffix ∧
      -t < resetTime ∧ resetTime ≤ 0 ∧
        (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
        (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
        liveEquivalentNonpreemptivePriorityWorkState
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace
                (emptyNonpreemptivePriorityWorkState
                  (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t)) front))
            resetTime
            (runNonpreemptivePriorityArrivalTrace
              (emptyNonpreemptivePriorityWorkState
                (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-t)) front))
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) resetTime)

/-- Under strict total load, the stationary marked input almost surely has a
finite positive past horizon whose literal physical trace contains a live
queue reset. -/
theorem ae_exists_stationaryPriorityArrivalWindow_liveReset
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∃ t : ℝ, 0 < t ∧
        stationaryPriorityArrivalWindowHasLiveReset meanService omega t := by
  filter_upwards [
    ae_tendsto_stationaryPriorityNetPastInput_atBot
      arrivalRate meanService harrivalRate hstable,
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hlimit hpositive
  have heventually : ∀ᶠ t : ℝ in Filter.atTop,
      stationaryPriorityNetPastInput meanService omega t < 0 :=
    (Filter.tendsto_atBot.1 hlimit (-1)).mono fun _ hbound => by linarith
  rcases Filter.eventually_atTop.1 heventually with ⟨bound, hbound⟩
  let t : ℝ := max bound 1
  have htpositive : 0 < t := by
    dsimp [t]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have htbound : bound ≤ t := by
    dsimp [t]
    exact le_max_left _ _
  have hnet : stationaryPriorityTotalPastWorkAggregate meanService omega t < t := by
    have hnegative := hbound t htbound
    unfold stationaryPriorityNetPastInput at hnegative
    linarith
  refine ⟨t, htpositive, ?_⟩
  unfold stationaryPriorityArrivalWindowHasLiveReset
  apply exists_stationaryPriorityArrivalWindow_liveReset_of_totalPastWork_lt
    meanService omega t
  · intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-t) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  · exact hnet

/-- Run the finite priority queue over a stationary-input window, beginning
empty at the left endpoint and then serving through the right endpoint. -/
def stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (stationaryPriorityArrivalWindowJobs meanService omega a b)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) b afterArrivals

/-- Away from an arrival exactly at the observation time, a chronological
replay over a larger stationary-input window agrees at that time with the
state built from the corresponding shorter window. -/
theorem stationaryPriorityArrivalTraceStateAt_eq_finiteWindowState_of_noArrivalAt
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (hno : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega t b,
      job.arrivalTime ≠ t) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
    nonpreemptivePriorityArrivalTraceStateAt initial jobs t =
      stationaryPriorityFiniteWindowState meanService omega a t := by
  dsimp only
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let front := stationaryPriorityArrivalWindowJobs meanService omega a t
  let tail := stationaryPriorityArrivalWindowJobs meanService omega t b
  have hjobs : stationaryPriorityArrivalWindowJobs meanService omega a b =
      front ++ tail := by
    exact stationaryPriorityArrivalWindowJobs_append meanService omega a t b hat htb
  rw [hjobs]
  have hfront : ∀ job ∈ front, job.arrivalTime ≤ t := by
    intro job hjob
    exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega a t job hjob).le
  have htail : ∀ job ∈ tail, t < job.arrivalTime := by
    intro job hjob
    exact lt_of_le_of_ne
      (left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
        meanService omega t b job hjob)
      (Ne.symm (hno job hjob))
  rw [nonpreemptivePriorityArrivalTraceStateAt_append_of_target_lt
    initial front tail t hfront htail]
  have hterminal := nonpreemptivePriorityArrivalTraceStateAt_terminal_eq_advance_run
    initial front t
    (fun job hjob => left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega a t job hjob)
    (pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a t)
    (fun job hjob =>
      (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a t job hjob).le)
  rw [hterminal]
  simp [stationaryPriorityFiniteWindowState, initial, front]

/-- The active-residual occupation of a finite stationary-input replay is the
time integral of its literal finite-window states.  Arrival instants are
handled by the generic finite-trace almost-everywhere no-arrival fact. -/
theorem intervalIntegrable_and_integral_active_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
    IntervalIntegrable
        (fun t => activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a t))
        MeasureTheory.volume a b ∧
      (∫ t in a..b, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a t)) =
        nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough initial jobs b := by
  dsimp only
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    constructor
    · intro active hactive
      simp [initial, emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [initial, emptyNonpreemptivePriorityWorkState] at hmember
  have htrace := intervalIntegrable_and_integral_activeNonpreemptivePriorityArrivalTraceStateAt
    initial jobs b hab
    (fun job hjob => left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega a b job hjob)
    (pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a b)
    (fun job hjob =>
      (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a b job hjob).le)
    hinitialPositive
    (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a)
    hjobs
  have hnoAE : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      ∀ job ∈ jobs, job.arrivalTime ≠ t :=
    ae_forall_mem_nonpreemptivePriorityArrivalTrace_arrivalTime_ne jobs
  have hstateAEInterval : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      t ∈ Set.uIoc a b →
        activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt initial jobs t) =
          activeNonpreemptivePriorityResidualWork
            (stationaryPriorityFiniteWindowState meanService omega a t) := by
    filter_upwards [hnoAE] with t hno ht
    rw [Set.uIoc_of_le hab] at ht
    apply congrArg activeNonpreemptivePriorityResidualWork
    apply stationaryPriorityArrivalTraceStateAt_eq_finiteWindowState_of_noArrivalAt
      meanService omega a t b ht.1.le ht.2
    intro job hmember
    apply hno job
    change job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b
    rw [stationaryPriorityArrivalWindowJobs_append meanService omega a t b ht.1.le ht.2]
    exact List.mem_append_right _ hmember
  have hstateAERestrict :
      (fun t => activeNonpreemptivePriorityResidualWork
        (nonpreemptivePriorityArrivalTraceStateAt initial jobs t)) =ᵐ[
          MeasureTheory.volume.restrict (Set.uIoc a b)]
        fun t => activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
      MeasureTheory.ae_restrict_of_ae hstateAEInterval] with t ht hstate
    exact hstate ht
  constructor
  · exact htrace.1.congr_ae hstateAERestrict
  · calc
      (∫ t in a..b, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a t)) =
          ∫ t in a..b, activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt initial jobs t) := by
              symm
              exact intervalIntegral.integral_congr_ae hstateAEInterval
      _ = nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough initial jobs b :=
        htrace.2

/-- The finite stationary-input replay satisfies the deterministic
squared-residual energy slab identity.  Each literal arrival in `[a,b)` adds
the square of its service requirement, and the remaining term is exactly the
active-residual occupation assembled by the generic chronological trace. -/
theorem stationaryPriorityFiniteWindow_squaredResidualWork_energy
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
    totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) +
      2 * nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough initial jobs b =
        (jobs.map (fun job => job.serviceWork ^ 2)).sum := by
  dsimp only
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    constructor
    · intro active hactive
      simp [initial, emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [initial, emptyNonpreemptivePriorityWorkState] at hmember
  have hinitialSquared : totalNonpreemptivePrioritySquaredResidualWork initial = 0 := by
    simp [initial, emptyNonpreemptivePriorityWorkState,
      totalNonpreemptivePrioritySquaredResidualWork,
      activeNonpreemptivePriorityResidualWork]
  have henergy := nonpreemptivePriorityArrivalTrace_squaredResidualWork_energy_through
    initial jobs b hab
    (fun job hjob => left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega a b job hjob)
    (pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a b)
    (fun job hjob =>
      (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a b job hjob).le)
    hinitialPositive
    (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a)
    hjobs
  rw [hinitialSquared] at henergy
  simpa [stationaryPriorityFiniteWindowState, initial, jobs] using henergy

/-- The finite stationary-input squared-residual energy slab written directly
as an occupation integral of the literal finite-window queue state. -/
theorem stationaryPriorityFiniteWindow_squaredResidualWork_energy_integral
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) +
      2 * (∫ t in a..b, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a t)) =
        ((stationaryPriorityArrivalWindowJobs meanService omega a b).map
          (fun job => job.serviceWork ^ 2)).sum := by
  have hintegral := intervalIntegrable_and_integral_active_stationaryPriorityFiniteWindowState
    meanService omega a b hab hjobs
  have henergy := stationaryPriorityFiniteWindow_squaredResidualWork_energy
    meanService omega a b hab hjobs
  rw [hintegral.2]
  exact henergy

/-- On a strict-past stationary input window, the deterministic finite energy
slab has the literal total squared service reward as its arrival-side term. -/
theorem stationaryPriorityFiniteWindow_squaredResidualWork_energy_integral_neg_to_zero
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (t : ℝ) (ht : 0 ≤ t)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega (-t) 0,
      0 < job.serviceWork) :
    totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-t) 0) +
      2 * (∫ u in (-t)..0, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-t) u)) =
        stationaryPriorityTotalPastSquareWorkAggregate meanService omega t := by
  calc
    totalNonpreemptivePrioritySquaredResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-t) 0) +
        2 * (∫ u in (-t)..0, activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-t) u)) =
        ((stationaryPriorityArrivalWindowJobs meanService omega (-t) 0).map
          (fun job => job.serviceWork ^ 2)).sum := by
            exact stationaryPriorityFiniteWindow_squaredResidualWork_energy_integral
              meanService omega (-t) 0 (neg_nonpos.mpr ht) hjobs
    _ = stationaryPriorityTotalPastSquareWorkAggregate meanService omega t :=
      stationaryPriorityArrivalWindowJobs_squareServiceWork_neg_to_zero meanService omega t

/-- The finite state obtained from a stationary-input window has only
class-consistent FIFO waiting lists. -/
theorem hasClassConsistentWaiting_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    hasClassConsistentWaiting (stationaryPriorityFiniteWindowState meanService omega a b) := by
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
  apply hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
  exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState a

/-- Every literal finite stationary-input execution is non-idling: if its
server is idle, then no marked job in the executed window remains waiting. -/
theorem nonpreemptivePriorityWorkConserving_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) :
    nonpreemptivePriorityWorkConserving
      (stationaryPriorityFiniteWindowState meanService omega a b) := by
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply nonpreemptivePriorityWorkConserving_advance
  apply nonpreemptivePriorityWorkConserving_run
  exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a

/-- Conditional on positive marks, the concrete stationary window trace has
the exact physical-arrival scalar workload recursion. -/
theorem totalResidualWork_run_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
    totalNonpreemptivePriorityResidualWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
  dsimp only
  have htrace := totalNonpreemptivePriorityResidualWork_run_eq_arrivalTraceResidualWork
    (emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a)
    (stationaryPriorityArrivalWindowJobs meanService omega a b)
    (by
      constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember)
    (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a)
    (by
      intro job hjob
      exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
        meanService omega a b job hjob)
    (pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a b)
    hjobs
  simpa [emptyNonpreemptivePriorityWorkState,
    totalNonpreemptivePriorityResidualWork,
    activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork] using htrace

/-- Positive class mean requirements make the exact physical-arrival workload
recursion for every finite stationary window hold almost surely. -/
theorem ae_totalResidualWork_run_stationaryPriorityArrivalWindowJobs
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      let initial := emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
      let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
      totalNonpreemptivePriorityResidualWork
          (runNonpreemptivePriorityArrivalTrace initial jobs) =
        nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
  filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService] with omega homega
  apply totalResidualWork_run_stationaryPriorityArrivalWindowJobs meanService omega a b
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, _, hjob⟩
  subst job
  exact homega i k

/-- Conditional on positive marks, the final service segment of a finite
stationary-input window has the exact reflected workload accounting law. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_terminal
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
      (stationaryPriorityArrivalWindowJobs meanService omega a b)
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) =
      max 0 (totalNonpreemptivePriorityResidualWork afterArrivals -
        (b - afterArrivals.currentTime)) := by
  dsimp only
  apply totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [emptyNonpreemptivePriorityWorkState] using hab
    · intro job hjob
      exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a b job hjob).le
  · apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  · apply nonpreemptivePriorityWorkConserving_run
    exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a
  · exact le_rfl

/-- Conditional on positive marks, the concrete finite stationary execution
has exactly the terminal physical-time scalar workload of its literal arrival
ledger. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
        (stationaryPriorityArrivalWindowJobs meanService omega a b) b := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let jobs := stationaryPriorityArrivalWindowJobs meanService omega a b
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hrun : totalNonpreemptivePriorityResidualWork afterArrivals =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
    simpa [initial, jobs, afterArrivals] using
      totalResidualWork_run_stationaryPriorityArrivalWindowJobs meanService omega a b hjobs
  have htime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime a jobs := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
    · intro job hjob
      simpa [initial, jobs] using
        left_le_arrivalTime_stationaryPriorityArrivalWindowJobs meanService omega a b job hjob
    · simpa [jobs] using
        pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega a b
  have hterminal := totalResidualWork_stationaryPriorityFiniteWindowState_terminal
    meanService omega a b hab hjobs
  change totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega a b) = _
  rw [hterminal, show totalNonpreemptivePriorityResidualWork afterArrivals =
    nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs from hrun, htime]
  rfl

/-- The literal finite stationary-window execution is clocked at its right
physical endpoint. -/
theorem stationaryPriorityFiniteWindowState_currentTime_eq_right
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b) :
    (stationaryPriorityFiniteWindowState meanService omega a b).currentTime = b := by
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply advanceNonpreemptivePriorityWorkState_currentTime_eq_target
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [emptyNonpreemptivePriorityWorkState] using hab
    · intro job hjob
      exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a b job hjob).le
  · exact le_rfl

/-- A finite stationary trace begun before a global backward net-input cutoff
has zero literal residual workload when it reaches that cutoff. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_eq_zero_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityNetPastCutoff meanService omega cutoff)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff), 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-older) (-cutoff)) = 0 := by
  rw [totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
    meanService omega (-older) (-cutoff) (neg_le_neg horizon) hpositive]
  exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_stationaryPriorityNetPastCutoff
    meanService omega cutoff older hcutoff hcutoffNonneg horizon hpositive

/-- At a global backward net-input cutoff, every sufficiently remote literal
finite start has the same live queue as an empty state at the cutoff epoch. -/
theorem liveEquivalent_stationaryPriorityFiniteWindowState_empty_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityNetPastCutoff meanService omega cutoff)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-older) (-cutoff), 0 < job.serviceWork) :
    liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService omega (-older) (-cutoff))
      (emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) := by
  have hpositiveState : positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-older) (-cutoff)) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hpositive
  have htotal := totalResidualWork_stationaryPriorityFiniteWindowState_eq_zero_of_netPastCutoff
    meanService omega cutoff older hcutoff hcutoffNonneg horizon hpositive
  have htime := stationaryPriorityFiniteWindowState_currentTime_eq_right
    meanService omega (-older) (-cutoff) (neg_le_neg horizon)
  have hempty := liveEquivalent_emptyNonpreemptivePriorityWorkState_of_totalResidualWork_eq_zero
    (stationaryPriorityFiniteWindowState meanService omega (-older) (-cutoff))
    hpositiveState htotal
  rw [htime] at hempty
  exact hempty

/-- Every finite stationary trace whose start lies before a global backward
net-input cutoff has the same live queue at the observation epoch as the
trace freshly begun at that cutoff. -/
theorem liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityNetPastCutoff meanService omega cutoff)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-older) 0, 0 < job.serviceWork) :
    liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService omega (-older) 0)
      (stationaryPriorityFiniteWindowState meanService omega (-cutoff) 0) := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older)
  let front := stationaryPriorityArrivalWindowJobs meanService omega (-older) (-cutoff)
  let suffix := stationaryPriorityArrivalWindowJobs meanService omega (-cutoff) 0
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  have hleftCut : -older ≤ -cutoff := neg_le_neg horizon
  have hcutRight : -cutoff ≤ 0 := neg_nonpos.mpr hcutoffNonneg
  have hwholeAppend : stationaryPriorityArrivalWindowJobs meanService omega (-older) 0 =
      front ++ suffix := by
    exact stationaryPriorityArrivalWindowJobs_append
      meanService omega (-older) (-cutoff) 0 hleftCut hcutRight
  have hfrontPositive : ∀ job ∈ front, 0 < job.serviceWork := by
    intro job hjob
    apply hpositive job
    rw [hwholeAppend]
    exact List.mem_append_left _ hjob
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterFront := by
    dsimp [afterFront]
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [initial, emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [initial, emptyNonpreemptivePriorityWorkState] at hmember
    · exact hfrontPositive
  have hafterWork : nonpreemptivePriorityWorkConserving afterFront := by
    dsimp [afterFront]
    apply nonpreemptivePriorityWorkConserving_run
    exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState (-older)
  have hafterCutoff : afterFront.currentTime ≤ -cutoff := by
    dsimp [afterFront]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [initial, emptyNonpreemptivePriorityWorkState] using hleftCut
    · intro job hjob
      exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega (-older) (-cutoff) job hjob).le
  have hfrontReset : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-older) (-cutoff)) = 0 := by
    apply totalResidualWork_stationaryPriorityFiniteWindowState_eq_zero_of_netPastCutoff
      meanService omega cutoff older hcutoff hcutoffNonneg horizon
    exact hfrontPositive
  have hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterFront) (-cutoff) afterFront) = 0 := by
    simpa [stationaryPriorityFiniteWindowState, initial, front, afterFront] using hfrontReset
  have hsuffixCutoff : ∀ job ∈ suffix, -cutoff ≤ job.arrivalTime := by
    intro job hjob
    exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega (-cutoff) 0 job hjob
  have hcontinuation := liveEquivalent_advance_run_from_empty_at_cutoff
    afterFront (-cutoff) 0 suffix hafterCutoff hcutRight hafterPositive hafterWork le_rfl
    hcutoffZero hsuffixCutoff
  have hleftState : stationaryPriorityFiniteWindowState meanService omega (-older) 0 =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace afterFront suffix)) 0
        (runNonpreemptivePriorityArrivalTrace afterFront suffix) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    rw [hwholeAppend, runNonpreemptivePriorityArrivalTrace_append]
  have hrightState : stationaryPriorityFiniteWindowState meanService omega (-cutoff) 0 =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) suffix)) 0
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-cutoff)) suffix) := by
    rfl
  rw [hleftState, hrightState]
  exact hcontinuation

/-- Under strict total load, the literal stationary priority traces begun at
all sufficiently remote past epochs almost surely coalesce to one live queue
at the observation epoch. -/
theorem ae_exists_stationaryPriorityFiniteWindowState_remotePastLiveCoalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService omega (-older) 0)
          (stationaryPriorityFiniteWindowState meanService omega (-cutoff) 0) := by
  filter_upwards [
    ae_exists_stationaryPriorityNetPastCutoff arrivalRate meanService harrivalRate hstable,
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hcutoff hpositive
  rcases hcutoff with ⟨cutoff, hcutoffNonneg, hmaximum⟩
  refine ⟨cutoff, hcutoffNonneg, ?_⟩
  intro older horizon
  apply liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
    meanService omega cutoff older hmaximum hcutoffNonneg horizon
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff
    meanService omega (-older) 0 job).mp hjob with ⟨i, k, _, hjob⟩
  subst job
  exact hpositive i k

/-- The pathwise remote-past priority state selected from a global net-input
cutoff when one exists, and empty otherwise.  This definition records the
causal state selected by literal finite traces; measurability and its Palm
performance law are separate stochastic obligations. -/
noncomputable def stationaryPriorityRemotePastState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) := by
  classical
  exact if hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff then
    stationaryPriorityFiniteWindowState meanService omega (-hcutoff.choose) 0
  else
    emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) 0

/-- On a path with a global net-input cutoff, the selected remote-past state
is exactly the finite literal trace begun at the selected cutoff. -/
theorem stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff) :
    stationaryPriorityRemotePastState meanService omega =
      stationaryPriorityFiniteWindowState meanService omega (-hcutoff.choose) 0 := by
  simp [stationaryPriorityRemotePastState, hcutoff]

/-- Strict total load gives an almost-sure pathwise remote-past state to
which all older literal finite starts coalesce at the observation epoch. -/
theorem ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService omega (-older) 0)
          (stationaryPriorityRemotePastState meanService omega) := by
  filter_upwards [
    ae_exists_stationaryPriorityNetPastCutoff arrivalRate meanService harrivalRate hstable,
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hcutoff hpositive
  refine ⟨hcutoff.choose, hcutoff.choose_spec.1, ?_⟩
  intro older horizon
  rw [stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
    meanService omega hcutoff]
  apply liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
    meanService omega hcutoff.choose older hcutoff.choose_spec.2
    hcutoff.choose_spec.1 horizon
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff
    meanService omega (-older) 0 job).mp hjob with ⟨i, k, _, hjob⟩
  subst job
  exact hpositive i k

/-- Aggregate unfinished work in the causal state selected from the remote
past.  This is a pathwise workload definition; its measurable Palm response
construction is supplied separately. -/
noncomputable def stationaryPriorityRemotePastResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) : ℝ :=
  totalNonpreemptivePriorityResidualWork
    (stationaryPriorityRemotePastState meanService omega)

/-- Under strict load, every sufficiently remote finite trace has exactly the
same aggregate unfinished work as the causal remote-past state. -/
theorem ae_exists_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-older) 0) =
        stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonneg, hcoalesces⟩
  refine ⟨cutoff, hnonneg, ?_⟩
  intro older holder
  exact totalNonpreemptivePriorityResidualWork_eq_of_liveEquivalent
    (hcoalesces older holder)

/-- The natural-horizon finite workloads eventually equal the causal
remote-past workload almost surely.  This is the pathwise stabilization input
for the generic measurable finite-replay construction. -/
theorem ae_eventually_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
        stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_exists_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  exact hcoalesces (horizon : ℝ) (hceil.trans hcast)

/-- The causal stationary workload is eventually the exact reflected maximum
of the literal arrival-suffix net-work candidates in a remote finite window.
This identifies the remaining integrability question with an honest maximum
over physical marked-input intervals; it does not yet supply a tail bound for
that maximum. -/
theorem ae_eventually_stationaryPriorityFiniteWindowSuffixMaximum_eq_remotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
          (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) =
        stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_eventually_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive hcoalesces
  filter_upwards [hcoalesces] with horizon hresidual
  have hterminal : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
        (-(horizon : ℝ)) 0 := by
    simpa [stationaryPriorityFiniteWindowTerminalResidualWork] using
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) (by
            intro job hjob
            rcases (mem_stationaryPriorityArrivalWindowJobs_iff
              meanService omega (-(horizon : ℝ)) 0 job).mp hjob with
                ⟨i, k, _, hjob⟩
            subst job
            exact hpositive i k)
  calc
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
        (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) =
        stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
          (-(horizon : ℝ)) 0 :=
      (stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega (-(horizon : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg horizon))).symm
    _ = totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) :=
      hterminal.symm
    _ = stationaryPriorityRemotePastResidualWork meanService omega := hresidual

/-- Almost surely, every finite remote-past suffix maximum lies below the
causal stationary workload.  Together with eventual equality, this shows that
the remote-past workload is the increasing exhaustion of actual finite marked
input intervals, not merely a limsup selected by an opaque cutoff. -/
theorem ae_forall_stationaryPriorityFiniteWindowSuffixMaximum_le_remotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
          (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) ≤
        stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_eventually_stationaryPriorityFiniteWindowSuffixMaximum_eq_remotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
  rcases Filter.eventually_atTop.1 heventual with ⟨threshold, hthreshold⟩
  intro horizon
  let later : ℕ := max threshold horizon
  have hhorizon : horizon ≤ later := le_max_right _ _
  have hlater : threshold ≤ later := le_max_left _ _
  calc
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
        (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) =
        stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
          (-(horizon : ℝ)) 0 :=
      (stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega (-(horizon : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg horizon))).symm
    _ ≤ stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
        (-(later : ℝ)) 0 := by
      apply stationaryPriorityFiniteWindowTerminalResidualWork_mono_left
        meanService omega (-(later : ℝ)) (-(horizon : ℝ)) 0
      · exact neg_le_neg (by exact_mod_cast hhorizon)
      · exact neg_nonpos.mpr (Nat.cast_nonneg horizon)
    _ = nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
        (stationaryPriorityArrivalWindowJobs meanService omega (-(later : ℝ)) 0) :=
      stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega (-(later : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg later))
    _ = stationaryPriorityRemotePastResidualWork meanService omega :=
      hthreshold later hlater

/-- Every empty-start finite replay over a remote past window has total
unfinished work bounded by the literal causal stationary workload. -/
theorem ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) ≤
          stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_forall_stationaryPriorityFiniteWindowSuffixMaximum_le_remotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive hsuffix
  intro horizon
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-(horizon : ℝ)) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  calc
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
        nonpreemptivePriorityArrivalTraceTerminalResidualWork (-(horizon : ℝ)) 0
          (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) 0 :=
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) hjobs
    _ = nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum 0
        (stationaryPriorityArrivalWindowJobs meanService omega (-(horizon : ℝ)) 0) :=
      stationaryPriorityFiniteWindowTerminalResidualWork_eq_suffixMaximum
        meanService omega (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon))
    _ ≤ stationaryPriorityRemotePastResidualWork meanService omega := hsuffix horizon

/-- The active residual in every empty-start remote finite replay is bounded
by the literal causal stationary workload.  This gives an integrable envelope
for the finite active-residual exhaustion under strict load. -/
theorem ae_forall_activeResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) ≤
          stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive htotal
  intro horizon
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-(horizon : ℝ)) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hstate : positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  exact (activeNonpreemptivePriorityResidualWork_le_total _ hstate.nonnegative).trans
    (htotal horizon)

/-- Priority-filtered waiting work in every empty-start remote finite replay
is bounded by the literal causal stationary workload.  This supplies the
integrable envelope needed to exhaust finite waiting occupations. -/
theorem ae_forall_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_le_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (priority : Fin n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) priority ≤
          stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive htotal
  intro horizon
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-(horizon : ℝ)) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hstate : positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  exact (priorityWaitingResidualWorkAtLeastAsUrgent_le_total _ hstate.nonnegative priority).trans
    (htotal horizon)

/-- The active residual of any empty-start replay with a nonnegative real
past horizon is bounded by the literal causal stationary workload.  This
continuous-horizon form supports reindexing finite time occupations. -/
theorem ae_forall_activeResidualWork_stationaryPriorityFiniteWindowState_real_le_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℝ, 0 ≤ horizon →
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) ≤
          stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive htotal
  intro horizon hhorizon
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-horizon) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-horizon) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hstate : positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  let later : ℕ := Nat.ceil horizon
  have hceil : horizon ≤ (later : ℝ) := by
    dsimp [later]
    exact Nat.le_ceil horizon
  calc
    activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) ≤
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) :=
      activeNonpreemptivePriorityResidualWork_le_total _ hstate.nonnegative
    _ = stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0 :=
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-horizon) 0 (by linarith) hjobs
    _ ≤ stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-(later : ℝ)) 0 := by
      apply stationaryPriorityFiniteWindowTerminalResidualWork_mono_left
        meanService omega (-(later : ℝ)) (-horizon) 0
      · linarith
      · linarith
    _ = totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(later : ℝ)) 0) := by
      symm
      exact totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(later : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg later)) (by
            intro job hjob
            rcases (mem_stationaryPriorityArrivalWindowJobs_iff
              meanService omega (-(later : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
            subst job
            exact hpositive i k)
    _ ≤ stationaryPriorityRemotePastResidualWork meanService omega := htotal later

/-- Priority-filtered waiting work of any empty-start replay with a
nonnegative real past horizon is bounded by the literal causal stationary
workload.  This is the continuous-horizon form used by stationary waiting
occupations. -/
theorem ae_forall_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_real_le_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (priority : Fin n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℝ, 0 ≤ horizon →
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) priority ≤
          stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive htotal
  intro horizon hhorizon
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-horizon) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-horizon) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hstate : positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) := by
    unfold stationaryPriorityFiniteWindowState
    dsimp only
    apply positiveNonpreemptivePriorityResidualWork_advance
    apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro i job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  let later : ℕ := Nat.ceil horizon
  have hceil : horizon ≤ (later : ℝ) := by
    dsimp [later]
    exact Nat.le_ceil horizon
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) priority ≤
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) :=
      priorityWaitingResidualWorkAtLeastAsUrgent_le_total _ hstate.nonnegative priority
    _ = stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-horizon) 0 :=
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-horizon) 0 (by linarith) hjobs
    _ ≤ stationaryPriorityFiniteWindowTerminalResidualWork meanService omega (-(later : ℝ)) 0 := by
      apply stationaryPriorityFiniteWindowTerminalResidualWork_mono_left
        meanService omega (-(later : ℝ)) (-horizon) 0
      · linarith
      · linarith
    _ = totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(later : ℝ)) 0) := by
      symm
      exact totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(later : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg later)) (by
            intro job hjob
            rcases (mem_stationaryPriorityArrivalWindowJobs_iff
              meanService omega (-(later : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
            subst job
            exact hpositive i k)
    _ ≤ stationaryPriorityRemotePastResidualWork meanService omega := htotal later

/-- Once each literal finite-window workload is known to be measurable, the
causal remote-past workload is almost-everywhere measurable.  The premise is
precisely the finite-replay Borel obligation; no reset-time selector or
stationarity certificate is hidden in this transport step. -/
theorem aemeasurable_stationaryPriorityRemotePastResidualWork_of_measurable_finiteWindows
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hfinite : ∀ horizon : ℕ, Measurable (fun omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0))) :
    AEMeasurable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  exact Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun horizon omega => totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0))
    (stationaryPriorityRemotePastResidualWork meanService)
    hfinite
    (ae_eventually_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable)

/-- Under positive class means and strict total load, the causal workload
obtained from the stationary marked-Poisson queue is almost-everywhere
measurable.  Its measurable finite approximants are the literal terminal
workloads, not an assumed measurable queue-state encoding. -/
theorem aemeasurable_stationaryPriorityRemotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    AEMeasurable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  refine Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun horizon omega => stationaryPriorityFiniteWindowTerminalResidualWork
      meanService omega (-(horizon : ℝ)) 0)
    (stationaryPriorityRemotePastResidualWork meanService)
    (fun horizon => measurable_stationaryPriorityFiniteWindowTerminalResidualWork
      meanService (-(horizon : ℝ)) 0) ?_
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_eventually_stationaryPriorityFiniteWindowState_remotePastResidualWork_eq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive hcoalesces
  filter_upwards [hcoalesces] with horizon hhorizon
  have hfinite : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
        (-(horizon : ℝ)) 0 := by
    simpa [stationaryPriorityFiniteWindowTerminalResidualWork] using
      totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
        meanService omega (-(horizon : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg horizon)) (by
            intro job hjob
            rcases (mem_stationaryPriorityArrivalWindowJobs_iff
              meanService omega (-(horizon : ℝ)) 0 job).mp hjob with
                ⟨i, k, _, hjob⟩
            subst job
            exact hpositive i k)
  exact hfinite.symm.trans hhorizon

/-- The causal remote-past workload is nonnegative almost surely under the
positive exponential-work input model. -/
theorem ae_nonnegative_stationaryPriorityRemotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      0 ≤ stationaryPriorityRemotePastResidualWork meanService omega := by
  filter_upwards [
    ae_exists_stationaryPriorityNetPastCutoff
      arrivalRate meanService harrivalRate hstable,
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hcutoff hpositive
  rw [stationaryPriorityRemotePastResidualWork,
    stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService omega hcutoff]
  apply totalNonpreemptivePriorityResidualWork_nonneg
  apply positiveNonpreemptivePriorityResidualWork.nonnegative
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-hcutoff.choose) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k

/-- The exact finite stationary workload composes across an adjacent physical
cut: the right-window trace starts from the left-window terminal workload. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_append
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork c
        (totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a c))
        (stationaryPriorityArrivalWindowJobs meanService omega c b) b := by
  have hleftJobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a c,
      0 < job.serviceWork := by
    intro job hjob
    apply hjobs job
    rw [stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb]
    exact List.mem_append_left _ hjob
  have hrightJobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega c b,
      0 < job.serviceWork := by
    intro job hjob
    apply hjobs job
    rw [stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb]
    exact List.mem_append_right _ hjob
  have hfront : nonpreemptivePriorityArrivalTraceEndTime a
      (stationaryPriorityArrivalWindowJobs meanService omega a c) ≤ c := by
    apply nonpreemptivePriorityArrivalTraceEndTime_le a c
    · exact hac
    · intro job hjob
      exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
        meanService omega a c job hjob).le
  have hsuffix : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega c b,
      c ≤ job.arrivalTime := by
    intro job hjob
    exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega c b job hjob
  rw [totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
    meanService omega a b (le_trans hac hcb) hjobs,
    stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb,
    nonpreemptivePriorityArrivalTraceTerminalResidualWork_append a c b 0
      (stationaryPriorityArrivalWindowJobs meanService omega a c)
      (stationaryPriorityArrivalWindowJobs meanService omega c b) hfront hcb hsuffix,
    ← totalResidualWork_stationaryPriorityFiniteWindowState_eq_terminalResidualWork
      meanService omega a c hac hleftJobs]

/-- Under positive class means, the finite physical workload composition law
holds almost surely for every fixed adjacent pair of stationary windows. -/
theorem ae_totalResidualWork_stationaryPriorityFiniteWindowState_append
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a b) =
        nonpreemptivePriorityArrivalTraceTerminalResidualWork c
          (totalNonpreemptivePriorityResidualWork
            (stationaryPriorityFiniteWindowState meanService omega a c))
          (stationaryPriorityArrivalWindowJobs meanService omega c b) b := by
  filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService] with omega homega
  apply totalResidualWork_stationaryPriorityFiniteWindowState_append
    meanService omega a c b hac hcb
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, _, hjob⟩
  subst job
  exact homega i k

/-- Across a finite stationary interval, the literal physical trace is no
larger than the conservative recursion that delays every right-window arrival
to the interval endpoint. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_le_virtualEndBatch
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) ≤
      max 0 (totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a c) - (b - c)) +
        nonpreemptivePriorityArrivalTraceServiceWork
          (stationaryPriorityArrivalWindowJobs meanService omega c b) := by
  have hrightJobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega c b,
      0 ≤ job.serviceWork := by
    intro job hjob
    apply (hjobs job ?_).le
    rw [stationaryPriorityArrivalWindowJobs_append meanService omega a c b hac hcb]
    exact List.mem_append_right _ hjob
  rw [totalResidualWork_stationaryPriorityFiniteWindowState_append
    meanService omega a c b hac hcb hjobs]
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_virtualEndBatch
  · intro job hjob
    exact left_le_arrivalTime_stationaryPriorityArrivalWindowJobs
      meanService omega c b job hjob
  · exact pairwise_arrivalTime_le_stationaryPriorityArrivalWindowJobs meanService omega c b
  · intro job hjob
    exact (arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
      meanService omega c b job hjob).le
  · exact hrightJobs

/-- An empty-start finite stationary replay leaves no more residual work than
the total marked work admitted in its window. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_le_windowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ) (hab : a ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) ≤
      stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
  have hbound := totalResidualWork_stationaryPriorityFiniteWindowState_le_virtualEndBatch
    meanService omega a a b le_rfl hab hjobs
  have hindices : stationaryPriorityArrivalWindowIndices omega a a = fun _ => ∅ := by
    funext i
    ext k
    constructor
    · intro hk
      have htime := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a a (omega i).1 k).mp hk
      exact False.elim (lt_irrefl a (htime.1.trans_lt htime.2))
    · intro hk
      simpa using hk
  have hledger : nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices omega a a) = ∅ := by
    unfold nonpreemptivePriorityArrivalWindowIndices
    rw [hindices]
    simp
  have hcanonical : canonicalStationaryPriorityArrivalWindowIndices omega a a = [] := by
    unfold canonicalStationaryPriorityArrivalWindowIndices
    rw [hledger]
    simp
  have hwindow : stationaryPriorityArrivalWindowJobs meanService omega a a = [] := by
    simp [stationaryPriorityArrivalWindowJobs,
      canonicalStationaryPriorityArrivalWindowJobs, hcanonical]
  have hemptyState : stationaryPriorityFiniteWindowState meanService omega a a =
      emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a := by
    simpa [stationaryPriorityFiniteWindowState, hwindow,
      runNonpreemptivePriorityArrivalTrace, totalNonpreemptivePriorityWorkJobs,
      totalPriorityWaitingJobs, emptyNonpreemptivePriorityWorkState] using
      (advanceNonpreemptivePriorityWorkState_empty_eq_empty
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) 0 a a le_rfl)
  have hempty : totalNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega a a) = 0 := by
    rw [hemptyState]
    simp [emptyNonpreemptivePriorityWorkState, totalNonpreemptivePriorityResidualWork,
      activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork]
  calc
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) ≤
        max 0 (totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a a) - (b - a)) +
          nonpreemptivePriorityArrivalTraceServiceWork
            (stationaryPriorityArrivalWindowJobs meanService omega a b) := hbound
    _ = stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
          rw [hempty]
          rw [max_eq_left (by linarith [hab])]
          simpa [stationaryPriorityArrivalWindowJobs] using
            (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
              meanService omega a b)

/-- At every intermediate epoch, an empty-start finite stationary replay is
bounded by the total marked work of any containing arrival window. -/
theorem totalResidualWork_stationaryPriorityFiniteWindowState_le_windowTotalWork_of_le
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a t) ≤
      stationaryPriorityArrivalWindowTotalWork meanService omega a b := by
  have happend := stationaryPriorityArrivalWindowJobs_append meanService omega a t b hat htb
  have hprefix : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a t,
      0 < job.serviceWork := by
    intro job hjob
    apply hjobs job
    rw [happend]
    exact List.mem_append_left _ hjob
  have htail : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega t b,
      0 ≤ job.serviceWork := by
    intro job hjob
    exact (hjobs job (by
      rw [happend]
      exact List.mem_append_right _ hjob)).le
  have htailNonnegative : 0 ≤ stationaryPriorityArrivalWindowTotalWork meanService omega t b := by
    rw [← nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityArrivalWindowJobs
      meanService omega t b]
    change 0 ≤ ((stationaryPriorityArrivalWindowJobs meanService omega t b).map
      fun job => job.serviceWork).sum
    apply List.sum_nonneg
    intro work hwork
    rcases List.mem_map.mp hwork with ⟨job, hjob, rfl⟩
    exact htail job hjob
  have hprefixBound := totalResidualWork_stationaryPriorityFiniteWindowState_le_windowTotalWork
    meanService omega a t hat hprefix
  have hworkAppend := stationaryPriorityArrivalWindowTotalWork_append
    meanService omega a t b hat htb
  rw [hworkAppend]
  linarith

/-- With positive class mean requirements, the terminal reflected-accounting
law for each literal stationary-input window holds almost surely. -/
theorem ae_totalResidualWork_stationaryPriorityFiniteWindowState_terminal
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      let initial := emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
      let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
        (stationaryPriorityArrivalWindowJobs meanService omega a b)
      totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a b) =
        max 0 (totalNonpreemptivePriorityResidualWork afterArrivals -
          (b - afterArrivals.currentTime)) := by
  filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService] with omega homega
  apply totalResidualWork_stationaryPriorityFiniteWindowState_terminal
    meanService omega a b hab
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, _, hjob⟩
  subst job
  exact homega i k

/-- If the stationary jobs in a finite window have nonnegative service work,
then the entire finite execution has nonnegative stored residual work. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 ≤ job.serviceWork) :
    nonnegativeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega a b) := by
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply nonnegativeNonpreemptivePriorityResidualWork_advance
  apply nonnegativeNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · exact hjobs

/-- Under positive class mean service requirements, the literal stationary
marked input produces finite window states with nonnegative residual work
almost surely. -/
theorem ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      nonnegativeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService] with omega homega
  apply nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, _, hjob⟩
  subst job
  exact (homega i k).le

/-- Consequently, total unfinished work in every finite stationary-input
window state is nonnegative almost surely. -/
theorem ae_totalNonpreemptivePriorityResidualWork_nonneg_stationaryPriorityFiniteWindowState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      0 ≤ totalNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  filter_upwards [
    ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      arrivalRate meanService harrivalRate hmeanService a b] with omega homega
  exact totalNonpreemptivePriorityResidualWork_nonneg _ homega

/-- Strictly positive jobs in a finite stationary-input window leave only
strictly positive residual jobs in its final state. -/
theorem positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (a b : ℝ)
    (hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService omega a b,
      0 < job.serviceWork) :
    positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega a b) := by
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro i job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · exact hjobs

/-- Positive class mean service requirements make every finite stationary
window execution a strictly positive-residual state almost surely. -/
theorem ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      positiveNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega a b) := by
  filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService] with omega homega
  apply positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
  intro job hjob
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega a b job).mp hjob
    with ⟨i, k, _, hjob⟩
  subst job
  exact homega i k

/-- On the full-measure positive-mark event, zero total residual work of a
finite stationary window means the concrete priority queue is genuinely
empty, not just empty in aggregate. -/
theorem ae_totalResidualWork_eq_zero_stationaryPriorityFiniteWindowState_implies_empty
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (a b : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      totalNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega a b) = 0 →
        (stationaryPriorityFiniteWindowState meanService omega a b).active = none ∧
          ∀ i, (stationaryPriorityFiniteWindowState meanService omega a b).waiting i = [] := by
  filter_upwards [
    ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      arrivalRate meanService harrivalRate hmeanService a b] with omega homega
  exact active_eq_none_and_waiting_eq_nil_of_totalResidualWork_eq_zero
    _ homega

end

end Queueing
end AppliedModelingLib
