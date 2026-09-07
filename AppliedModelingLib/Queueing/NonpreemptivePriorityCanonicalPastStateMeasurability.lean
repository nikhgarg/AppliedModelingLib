import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastReplay
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceSkeleton
import Mathlib.Tactic

/-!
# Borel state observables for canonical priority replays

This module equips the finite replay of a canonical strict-past marked input
with the same countable fixed-skeleton measurability argument used by literal
priority traces.  It is deliberately a finite replay construction: it does
not assert a stationary occupation formula.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

variable {n : ℕ}

/-- A fixed canonical-past job coordinate has a static label and priority,
with its physical arrival time and work requirement supplied by the canonical
past sample. -/
def canonicalNonpreemptivePriorityPastFixedJobCoordinate
    (meanService : Fin n → ℝ) (q : NonpreemptivePriorityCanonicalPastIndex n) :
    NonpreemptivePriorityFixedJobCoordinate
      (Fin n → StationaryPoissonWorkPastCanonicalSample)
      n (NonpreemptivePriorityCanonicalPastIndex n) :=
  { identifier := q
    priority := q.1
    arrivalTime := fun past => nonpreemptivePriorityCanonicalPastArrivalTime past q
    serviceWork := fun past => nonpreemptivePriorityCanonicalPastServiceWork meanService past q }

/-- The fixed coordinate jobs attached to one static canonical-past ledger. -/
def canonicalNonpreemptivePriorityPastFixedJobs
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityCanonicalPastIndex n)) :
    List (NonpreemptivePriorityFixedJobCoordinate
      (Fin n → StationaryPoissonWorkPastCanonicalSample)
      n (NonpreemptivePriorityCanonicalPastIndex n)) :=
  labels.map (canonicalNonpreemptivePriorityPastFixedJobCoordinate meanService)

/-- A countable service skeleton for one finite canonical-past replay. -/
structure CanonicalNonpreemptivePriorityPastFixedReplaySkeleton where
  arrivalSlots : List NonpreemptivePriorityFixedArrivalTraceSlot
  terminalCompletionCount : ℕ
  terminal : NonpreemptivePriorityFixedAdvanceTerminal
  deriving Countable

/-- The fixed empty state at the left endpoint of a canonical past window. -/
def canonicalNonpreemptivePriorityPastFixedInitial (horizon : ℝ) :
    NonpreemptivePriorityFixedStateCoordinate
      (Fin n → StationaryPoissonWorkPastCanonicalSample)
      n (NonpreemptivePriorityCanonicalPastIndex n) :=
  emptyNonpreemptivePriorityFixedStateCoordinate (fun _ => -horizon)

/-- The static state after applying one fixed canonical-past arrival skeleton. -/
noncomputable def canonicalNonpreemptivePriorityPastFixedAfterArrivals
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (canonicalNonpreemptivePriorityPastFixedInitial horizon)
    (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
    skeleton.arrivalSlots

/-- The static terminal state of one finite canonical-past replay. -/
noncomputable def canonicalNonpreemptivePriorityPastFixedState
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch (fun _ => 0)
    (canonicalNonpreemptivePriorityPastFixedAfterArrivals meanService horizon labels skeleton)
    skeleton.terminalCompletionCount skeleton.terminal

/-- A fixed canonical-past coordinate has Borel arrival and work components. -/
theorem canonicalNonpreemptivePriorityPastFixedJobCoordinate_coordinatesMeasurable
    (meanService : Fin n → ℝ) (q : NonpreemptivePriorityCanonicalPastIndex n) :
    (canonicalNonpreemptivePriorityPastFixedJobCoordinate meanService q).CoordinatesMeasurable := by
  constructor
  · exact measurable_nonpreemptivePriorityCanonicalPastArrivalTime q
  · change Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      meanService q.1 * (past q.1).2 q.2)
    exact measurable_const.mul
      ((measurable_pi_apply q.2).comp (measurable_snd.comp (measurable_pi_apply q.1)))

/-- Every fixed canonical-past job ledger has Borel real coordinates. -/
theorem canonicalNonpreemptivePriorityPastFixedJobs_coordinatesMeasurable
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityCanonicalPastIndex n)) :
    ∀ job ∈ canonicalNonpreemptivePriorityPastFixedJobs meanService labels,
      job.CoordinatesMeasurable := by
  intro job hjob
  rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
  exact canonicalNonpreemptivePriorityPastFixedJobCoordinate_coordinatesMeasurable meanService q

/-- Evaluating a fixed canonical-past job ledger gives its literal finite
job coordinates in the same static list order. -/
theorem eval_canonicalNonpreemptivePriorityPastFixedJobs
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample) :
    ((canonicalNonpreemptivePriorityPastFixedJobs meanService labels).map fun job => job.eval past) =
      labels.map (nonpreemptivePriorityCanonicalPastJob meanService past) := by
  simp [canonicalNonpreemptivePriorityPastFixedJobs,
    canonicalNonpreemptivePriorityPastFixedJobCoordinate,
    NonpreemptivePriorityFixedJobCoordinate.eval,
    nonpreemptivePriorityCanonicalPastJob,
    nonpreemptivePriorityCanonicalPastServiceWork]

/-- The static canonical-past replay state has Borel real coordinates. -/
theorem canonicalNonpreemptivePriorityPastFixedState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton) :
    (canonicalNonpreemptivePriorityPastFixedState meanService horizon labels skeleton).CoordinatesMeasurable := by
  have hinitial : (canonicalNonpreemptivePriorityPastFixedInitial (n := n) horizon).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hjobs := canonicalNonpreemptivePriorityPastFixedJobs_coordinatesMeasurable meanService labels
  have hafter : (canonicalNonpreemptivePriorityPastFixedAfterArrivals
      meanService horizon labels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (canonicalNonpreemptivePriorityPastFixedInitial horizon) hinitial
      (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs
  exact coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
    _ hafter skeleton.terminalCompletionCount skeleton.terminal

/-- The Borel branch predicate for one fixed canonical-past finite replay. -/
def canonicalNonpreemptivePriorityPastFixedBranchMatches
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (canonicalNonpreemptivePriorityPastFixedInitial horizon)
      (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
      skeleton.arrivalSlots past ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (canonicalNonpreemptivePriorityPastFixedAfterArrivals
          meanService horizon labels skeleton))
      (fun _ => 0)
      (canonicalNonpreemptivePriorityPastFixedAfterArrivals
        meanService horizon labels skeleton)
      skeleton.terminalCompletionCount skeleton.terminal past

/-- Each fixed canonical-past replay branch is Borel. -/
theorem measurableSet_canonicalNonpreemptivePriorityPastFixedBranchMatches
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton) :
    MeasurableSet {past |
      canonicalNonpreemptivePriorityPastFixedBranchMatches
        meanService horizon labels skeleton past} := by
  have hinitial : (canonicalNonpreemptivePriorityPastFixedInitial (n := n) horizon).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hjobs := canonicalNonpreemptivePriorityPastFixedJobs_coordinatesMeasurable meanService labels
  have hafter : (canonicalNonpreemptivePriorityPastFixedAfterArrivals
      meanService horizon labels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (canonicalNonpreemptivePriorityPastFixedInitial horizon) hinitial
      (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs
  convert (measurableSet_fixedPriorityArrivalTraceBranchMatches
      (canonicalNonpreemptivePriorityPastFixedInitial horizon) hinitial
      (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (canonicalNonpreemptivePriorityPastFixedAfterArrivals
            meanService horizon labels skeleton))
        (fun _ => 0) measurable_const
        _ hafter skeleton.terminalCompletionCount skeleton.terminal) using 1

/-- The executable finite state of a canonical strict-past replay. -/
def canonicalNonpreemptivePriorityPastWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityCanonicalPastIndex n) :=
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon)
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) 0 afterArrivals

/-- Replay a canonical finite ledger after sorting it with a target identifier
tie-breaker.  The stored identifiers remain canonical; relabelling is applied
only after the deterministic priority trace has been run. -/
def nonpreemptivePriorityReindexedPastWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (horizon : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityCanonicalPastIndex n) :=
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon)
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (nonpreemptivePriorityReindexedPastWindowJobs meanService past reindex hreindex
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon))
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) 0 afterArrivals

/-- Without simultaneous physical arrivals, changing only the secondary
identifier sorting key cannot change the complete finite priority state. -/
theorem nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (reindex : NonpreemptivePriorityCanonicalPastIndex n →
      NonpreemptivePriorityArrivalIndex n)
    (hreindex : Function.Injective reindex)
    (horizon : ℝ)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime past first =
        nonpreemptivePriorityCanonicalPastArrivalTime past second → first = second) :
    nonpreemptivePriorityReindexedPastWindowState meanService past reindex hreindex horizon =
      canonicalNonpreemptivePriorityPastWindowState meanService past horizon := by
  unfold nonpreemptivePriorityReindexedPastWindowState
    canonicalNonpreemptivePriorityPastWindowState
    nonpreemptivePriorityReindexedPastWindowJobs
    canonicalNonpreemptivePriorityPastWindowJobs
  rw [nonpreemptivePriorityReindexedPastWindowIndices_eq_canonical_of_noArrivalTies
    past reindex hreindex horizon hnoTies]

/-- Mapping identifiers after the reindexed stationary past replay produces
the literal stationary finite arrival trace. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowRun_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    nonpreemptivePriorityWorkStateMapIdentifier
        (nonpreemptivePriorityStationaryPastReindex (n := n))
        (runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon))
          (nonpreemptivePriorityReindexedPastWindowJobs meanService
            (multiclassStationaryPoissonWorkPastCanonicalInput omega)
            (nonpreemptivePriorityStationaryPastReindex (n := n))
            Function.Injective.nonpreemptivePriorityStationaryPastReindex
            (nonpreemptivePriorityCanonicalPastWindowIndexLedger
              (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon))) =
      runNonpreemptivePriorityArrivalTrace
        (emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-horizon))
    (canonicalStationaryPriorityArrivalWindowJobs meanService omega (-horizon) 0) := by
  rw [nonpreemptivePriorityWorkStateMapIdentifier_run]
  have hempty : nonpreemptivePriorityWorkStateMapIdentifier
      (nonpreemptivePriorityStationaryPastReindex (n := n))
      (emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon)) =
      emptyNonpreemptivePriorityWorkState
        (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-horizon) := by
    rfl
  rw [hempty]
  rw [nonpreemptivePriorityStationaryPastReindex_windowJobs_eq_canonical
    meanService omega horizon hindices]

/-- Relabelling the complete reindexed stationary finite replay produces the
literal stationary finite state, including the active job, all waiting lists,
and the completion ledger. -/
theorem nonpreemptivePriorityStationaryPastReindex_windowState_eq_canonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1) :
    nonpreemptivePriorityWorkStateMapIdentifier
        (nonpreemptivePriorityStationaryPastReindex (n := n))
        (nonpreemptivePriorityReindexedPastWindowState meanService
          (multiclassStationaryPoissonWorkPastCanonicalInput omega)
          (nonpreemptivePriorityStationaryPastReindex (n := n))
          Function.Injective.nonpreemptivePriorityStationaryPastReindex horizon) =
      stationaryPriorityFiniteWindowState meanService omega (-horizon) 0 := by
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let initial : NonpreemptivePriorityWorkState n
      (NonpreemptivePriorityCanonicalPastIndex n) :=
    emptyNonpreemptivePriorityWorkState (-horizon)
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (nonpreemptivePriorityReindexedPastWindowJobs meanService past reindex
      Function.Injective.nonpreemptivePriorityStationaryPastReindex
      (nonpreemptivePriorityCanonicalPastWindowIndexLedger past horizon))
  let literalInitial : NonpreemptivePriorityWorkState n
      (NonpreemptivePriorityArrivalIndex n) :=
    emptyNonpreemptivePriorityWorkState (-horizon)
  let literalAfterArrivals := runNonpreemptivePriorityArrivalTrace literalInitial
    (canonicalStationaryPriorityArrivalWindowJobs meanService omega (-horizon) 0)
  have hrun : nonpreemptivePriorityWorkStateMapIdentifier reindex afterArrivals =
      literalAfterArrivals := by
    dsimp [afterArrivals, initial, literalAfterArrivals, literalInitial, past, reindex]
    exact nonpreemptivePriorityStationaryPastReindex_windowRun_eq_canonical
      meanService omega horizon hindices
  have hcount : totalNonpreemptivePriorityWorkJobs afterArrivals =
      totalNonpreemptivePriorityWorkJobs literalAfterArrivals := by
    rw [← hrun]
    exact (totalNonpreemptivePriorityWorkJobs_mapIdentifier reindex afterArrivals).symm
  unfold nonpreemptivePriorityReindexedPastWindowState
    stationaryPriorityFiniteWindowState
  dsimp only
  change nonpreemptivePriorityWorkStateMapIdentifier reindex
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) 0 afterArrivals) =
    advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs literalAfterArrivals) 0 literalAfterArrivals
  rw [nonpreemptivePriorityWorkStateMapIdentifier_advance, hcount, hrun]

/-- The existing selected-arrival full-state transport written through the
shared reindexed-past state abbreviation. -/
theorem nonpreemptivePriorityClassTaggedPastReindex_windowState_eq_canonicalState
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1) :
    nonpreemptivePriorityWorkStateMapIdentifier
        (nonpreemptivePriorityClassTaggedPastReindex selected)
        (nonpreemptivePriorityReindexedPastWindowState meanService
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z)
          (nonpreemptivePriorityClassTaggedPastReindex selected)
          (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) horizon) =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0 := by
  simpa [nonpreemptivePriorityReindexedPastWindowState] using
    (nonpreemptivePriorityClassTaggedPastReindex_windowState_eq_canonical
      meanService selected z hgood horizon hpassive)

/-- On a collision-free finite stationary window, the active residual agrees
with the common canonical strict-past replay. -/
theorem stationaryPriorityFiniteWindowActiveResidualWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) second → first = second) :
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
      activeNonpreemptivePriorityResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let reindexedState := nonpreemptivePriorityReindexedPastWindowState
    meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex horizon
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState =
      stationaryPriorityFiniteWindowState meanService omega (-horizon) 0 := by
    simpa [past, reindex, reindexedState] using
      (nonpreemptivePriorityStationaryPastReindex_windowState_eq_canonical
        meanService omega horizon hindices)
  have hstate : reindexedState = canonicalNonpreemptivePriorityPastWindowState
      meanService past horizon := by
    exact nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
      meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex
      horizon hnoTies
  calc
    activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
        activeNonpreemptivePriorityResidualWork
          (nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState) := by
          rw [htransport]
    _ = activeNonpreemptivePriorityResidualWork reindexedState := by
          rw [activeNonpreemptivePriorityResidualWork_mapIdentifier]
    _ = activeNonpreemptivePriorityResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) := by
          rw [hstate]

/-- On a collision-free finite stationary window, the full squared residual
ledger agrees with the common canonical strict-past replay. -/
theorem stationaryPriorityFiniteWindowSquaredResidualWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ i : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) second → first = second) :
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
      totalNonpreemptivePrioritySquaredResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let reindexedState := nonpreemptivePriorityReindexedPastWindowState
    meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex horizon
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState =
      stationaryPriorityFiniteWindowState meanService omega (-horizon) 0 := by
    simpa [past, reindex, reindexedState] using
      (nonpreemptivePriorityStationaryPastReindex_windowState_eq_canonical
        meanService omega horizon hindices)
  have hstate : reindexedState = canonicalNonpreemptivePriorityPastWindowState
      meanService past horizon := by
    exact nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
      meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex
      horizon hnoTies
  calc
    totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
        totalNonpreemptivePrioritySquaredResidualWork
          (nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState) := by
            rw [htransport]
    _ = totalNonpreemptivePrioritySquaredResidualWork reindexedState := by
          rw [totalNonpreemptivePrioritySquaredResidualWork_mapIdentifier]
    _ = totalNonpreemptivePrioritySquaredResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) := by
          rw [hstate]

/-- On a collision-free finite selected-arrival window, the active residual
agrees with the common canonical strict-past replay. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) second → first = second) :
    activeNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0) =
      activeNonpreemptivePriorityResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon) := by
  let past := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z
  let reindex := nonpreemptivePriorityClassTaggedPastReindex selected
  let reindexedState := nonpreemptivePriorityReindexedPastWindowState
    meanService past reindex
      (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) horizon
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0 := by
    simpa [past, reindex, reindexedState] using
      (nonpreemptivePriorityClassTaggedPastReindex_windowState_eq_canonicalState
        meanService selected z hgood horizon hpassive)
  have hstate : reindexedState = canonicalNonpreemptivePriorityPastWindowState
      meanService past horizon := by
    exact nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
      meanService past reindex
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
      horizon hnoTies
  calc
    activeNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) =
        activeNonpreemptivePriorityResidualWork
          (nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState) := by
          rw [htransport]
    _ = activeNonpreemptivePriorityResidualWork reindexedState := by
          rw [activeNonpreemptivePriorityResidualWork_mapIdentifier]
    _ = activeNonpreemptivePriorityResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) := by
          rw [hstate]

/-- On a collision-free finite stationary window, waiting work in all classes
at least as urgent as `i` agrees with the common canonical replay. -/
theorem stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath)
    (horizon : ℝ)
    (hindices : ∀ j : Fin n,
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega j).1 =
        Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
          (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega j)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) second → first = second) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) i =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalNonpreemptivePriorityPastWindowState meanService
          (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) i := by
  let past := multiclassStationaryPoissonWorkPastCanonicalInput omega
  let reindex := nonpreemptivePriorityStationaryPastReindex (n := n)
  let reindexedState := nonpreemptivePriorityReindexedPastWindowState
    meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex horizon
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState =
      stationaryPriorityFiniteWindowState meanService omega (-horizon) 0 := by
    simpa [past, reindex, reindexedState] using
      (nonpreemptivePriorityStationaryPastReindex_windowState_eq_canonical
        meanService omega horizon hindices)
  have hstate : reindexedState = canonicalNonpreemptivePriorityPastWindowState
      meanService past horizon := by
    exact nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
      meanService past reindex Function.Injective.nonpreemptivePriorityStationaryPastReindex
      horizon hnoTies
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) i =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState) i := by
          rw [htransport]
    _ = priorityWaitingResidualWorkAtLeastAsUrgent reindexedState i := by
          rw [priorityWaitingResidualWorkAtLeastAsUrgent_mapIdentifier]
    _ = priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) i := by
          rw [hstate]

/-- On a collision-free selected-arrival finite window, waiting work in all
classes at least as urgent as the selected class agrees with the common
canonical replay. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast_of_noArrivalTies
    {n : ℕ} (meanService : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (horizon : ℝ)
    (hpassive : ∀ (j : Fin n) (hji : j ≠ selected),
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0
        (z.2 ⟨j, hji⟩).1 =
      Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
        (Probability.Queueing.stationaryPoissonWorkToEquilibrium
          (z.2 ⟨j, hji⟩)).1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      ∀ second ∈ nonpreemptivePriorityCanonicalPastWindowIndexLedger
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon,
      nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) first =
        nonpreemptivePriorityCanonicalPastArrivalTime
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) second → first = second) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0) selected =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalNonpreemptivePriorityPastWindowState meanService
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon) selected := by
  let past := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z
  let reindex := nonpreemptivePriorityClassTaggedPastReindex selected
  let reindexedState := nonpreemptivePriorityReindexedPastWindowState
    meanService past reindex
      (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected) horizon
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-horizon) 0 := by
    simpa [past, reindex, reindexedState] using
      (nonpreemptivePriorityClassTaggedPastReindex_windowState_eq_canonicalState
        meanService selected z hgood horizon hpassive)
  have hstate : reindexedState = canonicalNonpreemptivePriorityPastWindowState
      meanService past horizon := by
    exact nonpreemptivePriorityReindexedPastWindowState_eq_canonical_of_noArrivalTies
      meanService past reindex
        (Function.Injective.nonpreemptivePriorityClassTaggedPastReindex selected)
      horizon hnoTies
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) selected =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (nonpreemptivePriorityWorkStateMapIdentifier reindex reindexedState) selected := by
          rw [htransport]
    _ = priorityWaitingResidualWorkAtLeastAsUrgent reindexedState selected := by
          rw [priorityWaitingResidualWorkAtLeastAsUrgent_mapIdentifier]
    _ = priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) selected := by
          rw [hstate]

/-- At every finite horizon, the literal stationary active residual agrees
almost surely with the canonical strict-past state observable. -/
theorem ae_stationaryPriorityFiniteWindowActiveResidualWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
        activeNonpreemptivePriorityResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService
            (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
  have hpastIndices : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ i : Fin n,
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1 := by
    let μ : Fin n → Measure StationaryPoissonWorkPath := fun i =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
    letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
      Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
        (harrivalRate i)
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun z : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 z.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium z).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          arrivalRate harrivalRate i).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate i) horizon
  filter_upwards [
    hpastIndices,
    ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate] with omega hindices hcollision
  apply stationaryPriorityFiniteWindowActiveResidualWork_eq_canonicalPast_of_noArrivalTies
    meanService omega horizon hindices
  intro first _ second _ heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  have htime : Probability.PoissonProcess.arrivalTime firstIndex
      (multiclassStationaryPoissonWorkPastCanonicalInput omega firstClass).1 =
      Probability.PoissonProcess.arrivalTime secondIndex
        (multiclassStationaryPoissonWorkPastCanonicalInput omega secondClass).1 := by
    exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
  rcases hcollision firstClass secondClass firstIndex secondIndex htime with
    ⟨hclasses, hindices⟩
  subst secondClass
  subst secondIndex
  rfl

/-- At every finite horizon, the literal stationary squared residual ledger
agrees almost surely with the canonical strict-past state observable. -/
theorem ae_stationaryPriorityFiniteWindowSquaredResidualWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
        totalNonpreemptivePrioritySquaredResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService
            (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) := by
  have hpastIndices : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ i : Fin n,
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega i).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega i)).1 := by
    let μ : Fin n → Measure StationaryPoissonWorkPath := fun i =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
    letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
      Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
        (harrivalRate i)
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun z : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 z.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium z).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          arrivalRate harrivalRate i).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate i) horizon
  filter_upwards [
    hpastIndices,
    ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate] with omega hindices hcollision
  apply stationaryPriorityFiniteWindowSquaredResidualWork_eq_canonicalPast_of_noArrivalTies
    meanService omega horizon hindices
  intro first _ second _ heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  have htime : Probability.PoissonProcess.arrivalTime firstIndex
      (multiclassStationaryPoissonWorkPastCanonicalInput omega firstClass).1 =
      Probability.PoissonProcess.arrivalTime secondIndex
        (multiclassStationaryPoissonWorkPastCanonicalInput omega secondClass).1 := by
    exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
  rcases hcollision firstClass secondClass firstIndex secondIndex htime with
    ⟨hclasses, hindices⟩
  subst secondClass
  subst secondIndex
  rfl

/-- At every finite horizon, the selected-arrival active residual agrees
almost surely with the canonical strict-past state observable. -/
theorem ae_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      activeNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) =
        activeNonpreemptivePriorityResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon) := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood
      arrivalRate harrivalRate selected horizon,
    ae_multiclassStationaryPoissonWorkClassTaggedPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate selected] with z hgood hpassive hcollision
  apply canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_canonicalPast_of_noArrivalTies
    meanService selected z hgood horizon
  · intro i hiselected
    exact hpassive ⟨i, hiselected⟩
  · intro first _ second _ heq
    rcases first with ⟨firstClass, firstIndex⟩
    rcases second with ⟨secondClass, secondIndex⟩
    have htime : Probability.PoissonProcess.arrivalTime firstIndex
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
          selected z firstClass).1 =
        Probability.PoissonProcess.arrivalTime secondIndex
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
            selected z secondClass).1 := by
      exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
    rcases hcollision firstClass secondClass firstIndex secondIndex htime with
      ⟨hclasses, hindices⟩
    subst secondClass
    subst secondIndex
    rfl

/-- At every finite horizon, the literal stationary urgent-waiting component
agrees almost surely with the canonical strict-past state observable. -/
theorem ae_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (i : Fin n) (horizon : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
      arrivalRate,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) i =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (canonicalNonpreemptivePriorityPastWindowState meanService
            (multiclassStationaryPoissonWorkPastCanonicalInput omega) horizon) i := by
  have hpastIndices : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ j : Fin n,
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 (omega j).1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium (omega j)).1 := by
    let μ : Fin n → Measure StationaryPoissonWorkPath := fun j =>
      Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j)
    letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
      Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
        (harrivalRate j)
    rw [ae_all_iff]
    intro j
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval j)
      (p := fun z : StationaryPoissonWorkPath =>
        Probability.PoissonProcess.suspensionBaseArrivalIndices (-horizon) 0 z.1 =
          Probability.PoissonProcess.equilibriumBackwardArrivalIndices horizon
            (Probability.Queueing.stationaryPoissonWorkToEquilibrium z).1)
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate j).measurable.aemeasurable ?_
    have hmap : Measure.map (Function.eval j) (Measure.pi μ) =
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j) := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure, μ] using
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          arrivalRate harrivalRate j).map_eq
    rw [hmap]
    exact
      Probability.Queueing.ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
        (harrivalRate j) horizon
  filter_upwards [
    hpastIndices,
    ae_multiclassStationaryPoissonWorkPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate] with omega hindices hcollision
  apply stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast_of_noArrivalTies
    meanService i omega horizon hindices
  intro first _ second _ heq
  rcases first with ⟨firstClass, firstIndex⟩
  rcases second with ⟨secondClass, secondIndex⟩
  have htime : Probability.PoissonProcess.arrivalTime firstIndex
      (multiclassStationaryPoissonWorkPastCanonicalInput omega firstClass).1 =
      Probability.PoissonProcess.arrivalTime secondIndex
        (multiclassStationaryPoissonWorkPastCanonicalInput omega secondClass).1 := by
    exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
  rcases hcollision firstClass secondClass firstIndex secondIndex htime with
    ⟨hclasses, hindices⟩
  subst secondClass
  subst secondIndex
  rfl

/-- At every finite horizon, the selected-arrival urgent-waiting component
agrees almost surely with the canonical strict-past state observable. -/
theorem ae_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) selected =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (canonicalNonpreemptivePriorityPastWindowState meanService
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) horizon)
          selected := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_multiclassStationaryPoissonWorkClassTaggedPassivePastIndicesGood
      arrivalRate harrivalRate selected horizon,
    ae_multiclassStationaryPoissonWorkClassTaggedPastCanonicalArrivalTime_eq_iff
      arrivalRate harrivalRate selected] with z hgood hpassive hcollision
  apply canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast_of_noArrivalTies
    meanService selected z hgood horizon
  · intro j hjselected
    exact hpassive ⟨j, hjselected⟩
  · intro first _ second _ heq
    rcases first with ⟨firstClass, firstIndex⟩
    rcases second with ⟨secondClass, secondIndex⟩
    have htime : Probability.PoissonProcess.arrivalTime firstIndex
        (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
          selected z firstClass).1 =
        Probability.PoissonProcess.arrivalTime secondIndex
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput
            selected z secondClass).1 := by
      exact neg_injective (by simpa [nonpreemptivePriorityCanonicalPastArrivalTime] using heq)
    rcases hcollision firstClass secondClass firstIndex secondIndex htime with
      ⟨hclasses, hindices⟩
    subst secondClass
    subst secondIndex
    rfl

/-- On a matching finite fixed replay branch, the static state evaluates to
the executable canonical-past finite state. -/
theorem canonicalNonpreemptivePriorityPastFixedState_eval_eq_windowState_of_matches
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (labels : List (NonpreemptivePriorityCanonicalPastIndex n))
    (skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (hledger : canonicalNonpreemptivePriorityPastWindowIndices past horizon = labels)
    (hmatches : canonicalNonpreemptivePriorityPastFixedBranchMatches
      meanService horizon labels skeleton past) :
    (canonicalNonpreemptivePriorityPastFixedState meanService horizon labels skeleton).eval past =
      canonicalNonpreemptivePriorityPastWindowState meanService past horizon := by
  rcases hmatches with ⟨harrivals, hterminal⟩
  have hafter :
      (canonicalNonpreemptivePriorityPastFixedAfterArrivals
        meanService horizon labels skeleton).eval past =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon))
          (canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon) := by
    calc
      (canonicalNonpreemptivePriorityPastFixedAfterArrivals
          meanService horizon labels skeleton).eval past =
          runNonpreemptivePriorityArrivalTrace
            ((canonicalNonpreemptivePriorityPastFixedInitial horizon).eval past)
            ((canonicalNonpreemptivePriorityPastFixedJobs meanService labels).map
              fun job => job.eval past) := by
            simpa [canonicalNonpreemptivePriorityPastFixedAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (canonicalNonpreemptivePriorityPastFixedInitial horizon)
                (canonicalNonpreemptivePriorityPastFixedJobs meanService labels)
                skeleton.arrivalSlots past harrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityCanonicalPastIndex n) (-horizon))
            (canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon) := by
            rw [eval_canonicalNonpreemptivePriorityPastFixedJobs]
            simp only [canonicalNonpreemptivePriorityPastFixedInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              canonicalNonpreemptivePriorityPastWindowJobs]
            rw [hledger]
            rfl
  calc
    (canonicalNonpreemptivePriorityPastFixedState
        meanService horizon labels skeleton).eval past =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (canonicalNonpreemptivePriorityPastFixedAfterArrivals
              meanService horizon labels skeleton))
          0
          ((canonicalNonpreemptivePriorityPastFixedAfterArrivals
            meanService horizon labels skeleton).eval past) := by
          simpa [canonicalNonpreemptivePriorityPastFixedState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (canonicalNonpreemptivePriorityPastFixedAfterArrivals
                  meanService horizon labels skeleton))
              (fun _ => 0)
              (canonicalNonpreemptivePriorityPastFixedAfterArrivals
                meanService horizon labels skeleton)
              skeleton.terminalCompletionCount skeleton.terminal past hterminal)
    _ = canonicalNonpreemptivePriorityPastWindowState meanService past horizon := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hafter]
          rfl

/-- A real observable of a finite canonical strict-past state is Borel when
it is Borel on every fixed-shape state coordinate. -/
theorem measurable_canonicalNonpreemptivePriorityPastWindowState_component
    (meanService : Fin n → ℝ) (horizon : ℝ)
    (F : NonpreemptivePriorityWorkState n (NonpreemptivePriorityCanonicalPastIndex n) → ℝ)
    (hF : ∀ state : NonpreemptivePriorityFixedStateCoordinate
        (Fin n → StationaryPoissonWorkPastCanonicalSample)
        n (NonpreemptivePriorityCanonicalPastIndex n),
        state.CoordinatesMeasurable → Measurable (fun past => F (state.eval past))) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      F (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)) := by
  let Piece := List (NonpreemptivePriorityCanonicalPastIndex n) ×
    CanonicalNonpreemptivePriorityPastFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      {past | canonicalNonpreemptivePriorityPastWindowIndices past horizon = q.1} ∩
        {past | canonicalNonpreemptivePriorityPastFixedBranchMatches
          meanService horizon q.1 q.2 past})
    ?_ ?_
    (fun past => F (canonicalNonpreemptivePriorityPastWindowState meanService past horizon))
    (fun q past => F ((canonicalNonpreemptivePriorityPastFixedState
      meanService horizon q.1 q.2).eval past))
    ?_ ?_
  · intro q
    exact (measurableSet_canonicalNonpreemptivePriorityPastWindowIndices_eq horizon q.1).inter
      (measurableSet_canonicalNonpreemptivePriorityPastFixedBranchMatches
        meanService horizon q.1 q.2)
  · ext past
    constructor
    · intro _
      simp
    · intro _
      let labels := canonicalNonpreemptivePriorityPastWindowIndices past horizon
      let initial := canonicalNonpreemptivePriorityPastFixedInitial (n := n) horizon
      let jobs := canonicalNonpreemptivePriorityPastFixedJobs meanService labels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial jobs past with
        ⟨arrivalSlots, harrivals⟩
      let afterArrivals := runFixedPriorityArrivalTraceBranch initial jobs arrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs afterArrivals) (fun _ => 0) afterArrivals past with
        ⟨terminalCompletionCount, terminal, hterminal⟩
      let skeleton : CanonicalNonpreemptivePriorityPastFixedReplaySkeleton :=
        { arrivalSlots := arrivalSlots
          terminalCompletionCount := terminalCompletionCount
          terminal := terminal }
      refine Set.mem_iUnion.mpr ⟨(labels, skeleton), ?_⟩
      exact ⟨rfl, ⟨harrivals, hterminal⟩⟩
  · intro q
    exact hF (canonicalNonpreemptivePriorityPastFixedState meanService horizon q.1 q.2)
      (canonicalNonpreemptivePriorityPastFixedState_coordinatesMeasurable
        meanService horizon q.1 q.2)
  · intro q past hz
    rcases hz with ⟨hledger, hmatches⟩
    exact congrArg F
      (canonicalNonpreemptivePriorityPastFixedState_eval_eq_windowState_of_matches
        meanService horizon q.1 q.2 past hledger hmatches).symm

/-- The active residual of a finite canonical strict-past state is Borel. -/
theorem measurable_canonicalNonpreemptivePriorityPastWindowActiveResidualWork
    (meanService : Fin n → ℝ) (horizon : ℝ) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      activeNonpreemptivePriorityResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)) := by
  apply measurable_canonicalNonpreemptivePriorityPastWindowState_component
    meanService horizon activeNonpreemptivePriorityResidualWork
  intro state hstate
  exact measurable_activeNonpreemptivePriorityResidualWork_fixedState_eval state hstate

/-- The squared residual-work ledger of a finite canonical strict-past state
is Borel. -/
theorem measurable_canonicalNonpreemptivePriorityPastWindowSquaredResidualWork
    (meanService : Fin n → ℝ) (horizon : ℝ) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      totalNonpreemptivePrioritySquaredResidualWork
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)) := by
  apply measurable_canonicalNonpreemptivePriorityPastWindowState_component
    meanService horizon totalNonpreemptivePrioritySquaredResidualWork
  intro state hstate
  exact measurable_totalNonpreemptivePrioritySquaredResidualWork_fixedState_eval state hstate

/-- The waiting work in classes at least as urgent as `i` of a finite
canonical strict-past state is Borel. -/
theorem measurable_canonicalNonpreemptivePriorityPastWindowAtLeastAsUrgentWaitingWork
    (meanService : Fin n → ℝ) (horizon : ℝ) (i : Fin n) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) i) := by
  apply measurable_canonicalNonpreemptivePriorityPastWindowState_component
    meanService horizon (fun state => priorityWaitingResidualWorkAtLeastAsUrgent state i)
  intro state hstate
  exact measurable_priorityWaitingResidualWorkAtLeastAsUrgent_fixedState_eval state hstate i

/-- The finite stationary active residual has the law of its measurable
canonical strict-past state replay. -/
theorem stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    HasLaw
      (fun omega => activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0))
      (Measure.map
        (fun past => activeNonpreemptivePriorityResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService past horizon))
        (Measure.pi fun i =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    activeNonpreemptivePriorityResidualWork
      (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun i =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowActiveResidualWork
      meanService horizon).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_stationaryPriorityFiniteWindowActiveResidualWork_eq_canonicalPast
      arrivalRate meanService harrivalRate horizon] with omega heq
  exact heq

/-- The finite stationary squared residual ledger has the law of its
measurable canonical strict-past state replay. -/
theorem stationaryPriorityFiniteWindowSquaredResidualWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (horizon : ℝ) :
    HasLaw
      (fun omega => totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0))
      (Measure.map
        (fun past => totalNonpreemptivePrioritySquaredResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService past horizon))
        (Measure.pi fun i =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    totalNonpreemptivePrioritySquaredResidualWork
      (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun i =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowSquaredResidualWork
      meanService horizon).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_stationaryPriorityFiniteWindowSquaredResidualWork_eq_canonicalPast
      arrivalRate meanService harrivalRate horizon] with omega heq
  exact heq

/-- The finite selected-arrival active residual has the law of the same
measurable canonical strict-past state replay. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => activeNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0))
      (Measure.map
        (fun past => activeNonpreemptivePriorityResidualWork
          (canonicalNonpreemptivePriorityPastWindowState meanService past horizon))
        (Measure.pi fun i =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let canonical := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    activeNonpreemptivePriorityResidualWork
      (canonicalNonpreemptivePriorityPastWindowState meanService past horizon)
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun i =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate selected)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowActiveResidualWork
      meanService horizon).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_canonicalPast
      arrivalRate meanService harrivalRate selected horizon] with z heq
  exact heq

/-- At each finite past horizon, the selected-arrival and stationary active
residuals have identical laws. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => activeNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0))
      (Measure.map
        (fun omega => activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0))
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  have hstationary := stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
    arrivalRate meanService harrivalRate horizon
  have hselected :=
    canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate selected horizon
  refine ⟨hselected.aemeasurable, ?_⟩
  exact hselected.map_eq.trans hstationary.map_eq.symm

/-- The finite stationary urgent-waiting component has the law of its
measurable canonical strict-past state replay. -/
theorem stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n) (horizon : ℝ) :
    HasLaw
      (fun omega => priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) i)
      (Measure.map
        (fun past => priorityWaitingResidualWorkAtLeastAsUrgent
          (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) i)
        (Measure.pi fun j =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) i
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowAtLeastAsUrgentWaitingWork
      meanService horizon i).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast
      arrivalRate meanService harrivalRate i horizon] with omega heq
  exact heq

/-- The finite selected-arrival urgent-waiting component has the law of the
same measurable canonical strict-past state replay. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) selected)
      (Measure.map
        (fun past => priorityWaitingResidualWorkAtLeastAsUrgent
          (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) selected)
        (Measure.pi fun j =>
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let canonical := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected
  let F : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalNonpreemptivePriorityPastWindowState meanService past horizon) selected
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j)).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hinput : MeasurePreserving canonical
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
      (Measure.pi ν) := by
    simpa [canonical, ν] using
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate selected)
  have hcanonical : HasLaw F (Measure.map F (Measure.pi ν)) (Measure.pi ν) :=
    ⟨(measurable_canonicalNonpreemptivePriorityPastWindowAtLeastAsUrgentWaitingWork
      meanService horizon selected).aemeasurable, rfl⟩
  refine hcanonical.comp hinput.hasLaw |>.congr ?_
  filter_upwards [
    ae_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_canonicalPast
      arrivalRate meanService harrivalRate selected horizon] with z heq
  exact heq

/-- At each finite past horizon, selected-arrival and stationary urgent
waiting work have identical laws. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (selected : Fin n) (horizon : ℝ) :
    HasLaw
      (fun z => priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
          (-horizon) 0) selected)
      (Measure.map
        (fun omega => priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) selected)
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  have hstationary :=
    stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate selected horizon
  have hselected :=
    canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate selected horizon
  refine ⟨hselected.aemeasurable, ?_⟩
  exact hselected.map_eq.trans hstationary.map_eq.symm

end

end AppliedModelingLib.Queueing
