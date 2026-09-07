import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedCanonicalTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceSkeleton
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTimeTranslation
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import Mathlib.Tactic

/-!
# Borel fixed replays for selected nonpreemptive-priority queues

This module connects the generic fixed-event priority trace skeleton with the
selected/Palm finite replay construction.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Fixed labelled selected/Palm job coordinates for one finite ledger. -/
def stationaryPriorityClassTaggedFixedJobs
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    List (NonpreemptivePriorityFixedJobCoordinate
      (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
      n (NonpreemptivePriorityArrivalIndex n)) :=
  labels.map (stationaryPriorityClassTaggedFixedJobCoordinate meanService i)

/-- One countable static skeleton for a finite two-sided selected/Palm replay. -/
structure StationaryPriorityClassTaggedFixedReplaySkeleton where
  pastArrivalSlots : List NonpreemptivePriorityFixedArrivalTraceSlot
  pastTerminalCompletionCount : ℕ
  pastTerminal : NonpreemptivePriorityFixedAdvanceTerminal
  futureArrivalSlots : List NonpreemptivePriorityFixedArrivalTraceSlot
  futureTerminalCompletionCount : ℕ
  futureTerminal : NonpreemptivePriorityFixedAdvanceTerminal
  deriving Countable

/-- The fixed empty coordinate state at the left endpoint of a finite past
window. -/
def stationaryPriorityClassTaggedFixedPastInitial
    (i : Fin n) (older : ℝ) :
    NonpreemptivePriorityFixedStateCoordinate
      (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
      n (NonpreemptivePriorityArrivalIndex n) :=
  emptyNonpreemptivePriorityFixedStateCoordinate (fun _ => -older)

/-- The static state after executing the labelled past-arrival slots. -/
noncomputable def stationaryPriorityClassTaggedFixedPastAfterArrivals
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (stationaryPriorityClassTaggedFixedPastInitial i older)
    (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
    skeleton.pastArrivalSlots

/-- The static finite past state served through the tag epoch. -/
noncomputable def stationaryPriorityClassTaggedFixedPastState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch (fun _ => 0)
    (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older pastLabels skeleton)
    skeleton.pastTerminalCompletionCount skeleton.pastTerminal

/-- The static selected state after clearing historical observations and
admitting the Palm-tagged customer. -/
noncomputable def stationaryPriorityClassTaggedFixedPostTagState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  NonpreemptivePriorityFixedStateCoordinate.admit
    (NonpreemptivePriorityFixedStateCoordinate.clearCompleted
      (stationaryPriorityClassTaggedFixedPastState meanService i older pastLabels skeleton))
    (stationaryPriorityClassTaggedFixedJobCoordinate meanService i (Sigma.mk i 0))

/-- The static state after the fixed future-arrival ledger. -/
noncomputable def stationaryPriorityClassTaggedFixedPostFutureState
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (stationaryPriorityClassTaggedFixedPostTagState meanService i older pastLabels skeleton)
    (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
    skeleton.futureArrivalSlots

/-- The static completed finite two-sided replay state. -/
noncomputable def stationaryPriorityClassTaggedFixedReplayState
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch (fun _ => t)
    (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton)
    skeleton.futureTerminalCompletionCount skeleton.futureTerminal

/-- The static completed replay state at a Borel sample-dependent right
horizon.  The finite ledger and every service branch remain static; only the
final advance clock is a carrier coordinate. -/
noncomputable def stationaryPriorityClassTaggedFixedReplayStateAt
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch target
    (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton)
    skeleton.futureTerminalCompletionCount skeleton.futureTerminal

/-- Evaluating a static replay at a random horizon agrees pointwise with
freezing that horizon at its value on the evaluated carrier point. -/
theorem stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_fixed
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    (stationaryPriorityClassTaggedFixedReplayStateAt meanService i older target
      pastLabels futureLabels skeleton).eval z =
      (stationaryPriorityClassTaggedFixedReplayState meanService i older (target z)
        pastLabels futureLabels skeleton).eval z := by
  cases hterminal : skeleton.futureTerminal with
  | hold =>
      simp [stationaryPriorityClassTaggedFixedReplayStateAt,
        stationaryPriorityClassTaggedFixedReplayState, runFixedPriorityAdvanceBranch,
        hterminal]
  | advance =>
      cases hactive : (iterateFixedPriorityCompletions
          skeleton.futureTerminalCompletionCount
          (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
            pastLabels futureLabels skeleton)).active <;>
        simp [stationaryPriorityClassTaggedFixedReplayStateAt,
          stationaryPriorityClassTaggedFixedReplayState, runFixedPriorityAdvanceBranch,
          hterminal, hactive,
          NonpreemptivePriorityFixedStateCoordinate.advanceWithoutCompletion,
          NonpreemptivePriorityFixedStateCoordinate.withCurrentTime,
          NonpreemptivePriorityFixedStateCoordinate.eval]

/-- All fixed selected/Palm labelled jobs carry Borel arrival and service
coordinates. -/
theorem stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    ∀ job ∈ stationaryPriorityClassTaggedFixedJobs meanService i labels,
      job.CoordinatesMeasurable := by
  intro job hjob
  rcases List.mem_map.mp hjob with ⟨label, _, rfl⟩
  exact stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable meanService i label

/-- Evaluating a fixed selected/Palm label ledger produces its literal job
coordinates in the same static list order. -/
theorem eval_stationaryPriorityClassTaggedFixedJobs
    (meanService : Fin n → ℝ) (i : Fin n)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    ((stationaryPriorityClassTaggedFixedJobs meanService i labels).map fun job => job.eval z) =
      labels.map fun q =>
        { identifier := q
          priority := q.1
          arrivalTime := stationaryPriorityClassTaggedArrival i z q.1 q.2
          serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 } := by
  simp [stationaryPriorityClassTaggedFixedJobs,
    stationaryPriorityClassTaggedFixedJobCoordinate,
    NonpreemptivePriorityFixedJobCoordinate.eval]

/-- Every static finite two-sided replay state has Borel real coordinates. -/
theorem stationaryPriorityClassTaggedFixedReplayState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedFixedReplayState meanService i older t
      pastLabels futureLabels skeleton).CoordinatesMeasurable := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  have hpast : (stationaryPriorityClassTaggedFixedPastState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal
  have htag := stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    meanService i (Sigma.mk i 0)
  have hpostTag : (stationaryPriorityClassTaggedFixedPostTagState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.admit
      _ _
      (NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.clearCompleted _ hpast)
      htag
  have hfutureJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i futureLabels
  have hfuture : (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs
  exact coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => t) measurable_const
    _ hfuture skeleton.futureTerminalCompletionCount skeleton.futureTerminal

/-- The fixed coordinate state at the selected arrival's pre-arrival epoch has
Borel real coordinates.  This is the past-only part of a fixed two-sided
replay and is useful for stationary state observables. -/
theorem stationaryPriorityClassTaggedFixedPastState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedFixedPastState meanService i older
      pastLabels skeleton).CoordinatesMeasurable := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  exact coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
    _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal

/-- The Borel branch predicate for the past-only part of a fixed selected/Palm
replay. -/
def stationaryPriorityClassTaggedFixedPastBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older)
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots z ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
          pastLabels skeleton))
      (fun _ => 0)
      (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
        pastLabels skeleton)
      skeleton.pastTerminalCompletionCount skeleton.pastTerminal z

/-- Every fixed past-only selected/Palm replay branch is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFixedPastBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MeasurableSet {z |
      stationaryPriorityClassTaggedFixedPastBranchMatches
        meanService i older pastLabels skeleton z} := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  convert (measurableSet_fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
            pastLabels skeleton)) (fun _ => 0) measurable_const
        _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal) using 1

/-- On a fixed past-ledger fiber and a matching service skeleton, the static
past state evaluates to the executable finite pre-arrival state. -/
theorem stationaryPriorityClassTaggedFixedPastState_eval_eq_finiteWindowState_of_matches
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (pastLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hledger : canonicalStationaryPriorityClassTaggedArrivalWindowIndices
      i z (-older) 0 = pastLabels)
    (hmatches : stationaryPriorityClassTaggedFixedPastBranchMatches
      meanService i older pastLabels skeleton z) :
    (stationaryPriorityClassTaggedFixedPastState meanService i older
      pastLabels skeleton).eval z =
      canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-older) 0 := by
  rcases hmatches with ⟨hpastArrivals, hpastTerminal⟩
  have hpastAfter :
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
        meanService i older pastLabels skeleton).eval z =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-older) 0) := by
    calc
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
          meanService i older pastLabels skeleton).eval z =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedFixedPastInitial i older).eval z)
            ((stationaryPriorityClassTaggedFixedJobs meanService i pastLabels).map
              fun job => job.eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPastAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedFixedPastInitial i older)
                (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
                skeleton.pastArrivalSlots z hpastArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
            (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
              meanService i z (-older) 0) := by
            rw [eval_stationaryPriorityClassTaggedFixedJobs]
            simp only [stationaryPriorityClassTaggedFixedPastInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              canonicalStationaryPriorityClassTaggedArrivalWindowJobs]
            rw [hledger]
            rfl
  calc
    (stationaryPriorityClassTaggedFixedPastState meanService i older
        pastLabels skeleton).eval z =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (stationaryPriorityClassTaggedFixedPastAfterArrivals
              meanService i older pastLabels skeleton))
          0
          ((stationaryPriorityClassTaggedFixedPastAfterArrivals
            meanService i older pastLabels skeleton).eval z) := by
          simpa [stationaryPriorityClassTaggedFixedPastState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (stationaryPriorityClassTaggedFixedPastAfterArrivals
                  meanService i older pastLabels skeleton))
              (fun _ => 0)
              (stationaryPriorityClassTaggedFixedPastAfterArrivals
                meanService i older pastLabels skeleton)
              skeleton.pastTerminalCompletionCount skeleton.pastTerminal z hpastTerminal)
    _ = canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i z (-older) 0 := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hpastAfter]
          rfl

/-- A real observable of a finite selected/Palm pre-arrival state is Borel
whenever it is Borel on every fixed-shape state coordinate.  The proof uses
the literal countable cover of finite arrival ledgers and service choices. -/
theorem measurable_canonicalStationaryPriorityClassTaggedFiniteWindowState_component
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (F : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) → ℝ)
    (hF : ∀ state : NonpreemptivePriorityFixedStateCoordinate
        (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
        n (NonpreemptivePriorityArrivalIndex n),
        state.CoordinatesMeasurable →
          Measurable (fun z => F (state.eval z))) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      F (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-older) 0)) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      {z | canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0 = q.1} ∩
        {z | stationaryPriorityClassTaggedFixedPastBranchMatches
          meanService i older q.1 q.2 z})
    ?_ ?_
    (fun z => F (canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-older) 0))
    (fun q z => F ((stationaryPriorityClassTaggedFixedPastState
      meanService i older q.1 q.2).eval z))
    ?_ ?_
  · intro q
    exact (measurableSet_canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq
      i (-older) 0 q.1).inter
      (measurableSet_stationaryPriorityClassTaggedFixedPastBranchMatches
        meanService i older q.1 q.2)
  · ext z
    constructor
    · intro _
      simp
    · intro _
      let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0
      let initial := stationaryPriorityClassTaggedFixedPastInitial i older
      let pastJobs := stationaryPriorityClassTaggedFixedJobs meanService i pastLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs z with
        ⟨pastArrivalSlots, hpastArrivals⟩
      let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter z with
        ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
      let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := []
          futureTerminalCompletionCount := 0
          futureTerminal := .hold }
      refine Set.mem_iUnion.mpr ⟨(pastLabels, skeleton), ?_⟩
      exact ⟨rfl, ⟨hpastArrivals, hpastTerminal⟩⟩
  · intro q
    exact hF (stationaryPriorityClassTaggedFixedPastState
      meanService i older q.1 q.2)
      (stationaryPriorityClassTaggedFixedPastState_coordinatesMeasurable
        meanService i older q.1 q.2)
  · intro q z hz
    rcases hz with ⟨hledger, hmatches⟩
    exact congrArg F
      (stationaryPriorityClassTaggedFixedPastState_eval_eq_finiteWindowState_of_matches
        meanService i older q.1 q.2 z hledger hmatches).symm

/-- The active residual in a finite selected/Palm pre-arrival state is Borel. -/
theorem measurable_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      activeNonpreemptivePriorityResidualWork
        (canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i z (-older) 0)) := by
  apply measurable_canonicalStationaryPriorityClassTaggedFiniteWindowState_component
    meanService i older activeNonpreemptivePriorityResidualWork
  intro state hstate
  exact measurable_activeNonpreemptivePriorityResidualWork_fixedState_eval state hstate

/-- Waiting work at least as urgent as the selected class in a finite
selected/Palm pre-arrival state is Borel. -/
theorem measurable_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      priorityWaitingResidualWorkAtLeastAsUrgent
        (canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i z (-older) 0) i) := by
  apply measurable_canonicalStationaryPriorityClassTaggedFiniteWindowState_component
    meanService i older (fun state => priorityWaitingResidualWorkAtLeastAsUrgent state i)
  intro state hstate
  exact measurable_priorityWaitingResidualWorkAtLeastAsUrgent_fixedState_eval state hstate i

/-- Every static two-sided replay state at a Borel random horizon has Borel
real coordinates. -/
theorem stationaryPriorityClassTaggedFixedReplayStateAt_coordinatesMeasurable
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    (stationaryPriorityClassTaggedFixedReplayStateAt meanService i older target
      pastLabels futureLabels skeleton).CoordinatesMeasurable := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  have hpast : (stationaryPriorityClassTaggedFixedPastState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal
  have htag := stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    meanService i (Sigma.mk i 0)
  have hpostTag : (stationaryPriorityClassTaggedFixedPostTagState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.admit
      _ _
      (NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.clearCompleted _ hpast)
      htag
  have hfutureJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i futureLabels
  have hfuture : (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs
  exact coordinatesMeasurable_runFixedPriorityAdvanceBranch target htarget
    _ hfuture skeleton.futureTerminalCompletionCount skeleton.futureTerminal

/-- The Borel completion response of a fixed selected/Palm replay skeleton. -/
def stationaryPriorityClassTaggedFixedReplayResponse
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
  fixedPriorityCompletionResponse (Sigma.mk i 0)
    (stationaryPriorityClassTaggedFixedReplayState meanService i older t
      pastLabels futureLabels skeleton)

/-- The Borel completion response of a fixed replay at a Borel random
horizon. -/
def stationaryPriorityClassTaggedFixedReplayResponseAt
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ :=
  fixedPriorityCompletionResponse (Sigma.mk i 0)
    (stationaryPriorityClassTaggedFixedReplayStateAt meanService i older target
      pastLabels futureLabels skeleton)

/-- Every fixed selected/Palm replay response is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFixedReplayResponse
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    Measurable (stationaryPriorityClassTaggedFixedReplayResponse meanService i older t
      pastLabels futureLabels skeleton) := by
  apply measurable_fixedPriorityCompletionResponse
  exact stationaryPriorityClassTaggedFixedReplayState_coordinatesMeasurable
    meanService i older t pastLabels futureLabels skeleton

/-- Every fixed selected/Palm replay response at a Borel random horizon is
Borel. -/
theorem measurable_stationaryPriorityClassTaggedFixedReplayResponseAt
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    Measurable (stationaryPriorityClassTaggedFixedReplayResponseAt meanService i older target
      pastLabels futureLabels skeleton) := by
  apply measurable_fixedPriorityCompletionResponse
  exact stationaryPriorityClassTaggedFixedReplayStateAt_coordinatesMeasurable
    meanService i older target htarget pastLabels futureLabels skeleton

/-- The Borel branch predicate for a fully fixed two-sided selected/Palm replay. -/
def stationaryPriorityClassTaggedFixedReplayBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older)
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots z ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
          pastLabels skeleton))
      (fun _ => 0)
      (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
        pastLabels skeleton)
      skeleton.pastTerminalCompletionCount skeleton.pastTerminal z ∧
    fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPostTagState meanService i older pastLabels skeleton)
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots z ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
          pastLabels futureLabels skeleton))
      (fun _ => t)
      (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal z

/-- The Borel branch predicate for a static two-sided replay whose final
advance target is a carrier coordinate. -/
def stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older)
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots z ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
          pastLabels skeleton))
      (fun _ => 0)
      (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
        pastLabels skeleton)
      skeleton.pastTerminalCompletionCount skeleton.pastTerminal z ∧
    fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPostTagState meanService i older pastLabels skeleton)
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots z ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
          pastLabels futureLabels skeleton))
      target
      (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal z

/-- Every fixed two-sided selected/Palm replay branch is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatches
    (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MeasurableSet {z |
      stationaryPriorityClassTaggedFixedReplayBranchMatches meanService i older t
        pastLabels futureLabels skeleton z} := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  have hpast : (stationaryPriorityClassTaggedFixedPastState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal
  have htag := stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    meanService i (Sigma.mk i 0)
  have hpostTag : (stationaryPriorityClassTaggedFixedPostTagState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.admit
      _ _
      (NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.clearCompleted _ hpast)
      htag
  have hfutureJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i futureLabels
  have hfuture : (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs
  convert ((measurableSet_fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs).inter
    (measurableSet_fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
          pastLabels skeleton)) (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal)).inter
    ((measurableSet_fixedPriorityArrivalTraceBranchMatches _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
            pastLabels futureLabels skeleton)) (fun _ => t) measurable_const
        _ hfuture skeleton.futureTerminalCompletionCount skeleton.futureTerminal))
    using 1
  ext z
  simp [stationaryPriorityClassTaggedFixedReplayBranchMatches]
  aesop

/-- Every fixed two-sided selected/Palm replay branch at a Borel random
horizon is Borel. -/
theorem measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
    (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton) :
    MeasurableSet {z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i |
      stationaryPriorityClassTaggedFixedReplayBranchMatchesAt meanService i older target
        pastLabels futureLabels skeleton z} := by
  have hinitial : (stationaryPriorityClassTaggedFixedPastInitial i older).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hpastJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i pastLabels
  have hpastAfter : (stationaryPriorityClassTaggedFixedPastAfterArrivals
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs
  have hpast : (stationaryPriorityClassTaggedFixedPastState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal
  have htag := stationaryPriorityClassTaggedFixedJobCoordinate_coordinatesMeasurable
    meanService i (Sigma.mk i 0)
  have hpostTag : (stationaryPriorityClassTaggedFixedPostTagState
      meanService i older pastLabels skeleton).CoordinatesMeasurable :=
    NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.admit
      _ _
      (NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.clearCompleted _ hpast)
      htag
  have hfutureJobs := stationaryPriorityClassTaggedFixedJobs_coordinatesMeasurable
    meanService i futureLabels
  have hfuture : (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
      pastLabels futureLabels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs
  convert ((measurableSet_fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityClassTaggedFixedPastInitial i older) hinitial
      (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
      skeleton.pastArrivalSlots hpastJobs).inter
    (measurableSet_fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPastAfterArrivals meanService i older
          pastLabels skeleton)) (fun _ => 0) measurable_const
      _ hpastAfter skeleton.pastTerminalCompletionCount skeleton.pastTerminal)).inter
    ((measurableSet_fixedPriorityArrivalTraceBranchMatches _ hpostTag
      (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
      skeleton.futureArrivalSlots hfutureJobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
            pastLabels futureLabels skeleton)) target htarget
        _ hfuture skeleton.futureTerminalCompletionCount skeleton.futureTerminal))
    using 1
  ext z
  simp [stationaryPriorityClassTaggedFixedReplayBranchMatchesAt]
  aesop

/-- Reading a static completion ledger agrees with the selected/Palm literal
completion observation after coordinate evaluation. -/
theorem fixedPriorityCompletionResponse_eq_recordedCompletionTime_getD
    {i : Fin n}
    (state : NonpreemptivePriorityFixedStateCoordinate
      (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
      n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) :
    fixedPriorityCompletionResponse identifier state = fun z =>
      (nonpreemptivePriorityRecordedCompletionTime (state.eval z) identifier).getD 0 := by
  funext z
  unfold fixedPriorityCompletionResponse nonpreemptivePriorityRecordedCompletionTime
  change fixedPriorityCompletionResponseFromLedger identifier state.completed.reverse z =
    (Option.map Prod.snd
      (List.find? (fun entry => decide (entry.1.identifier = identifier))
        ((state.completed.map fun entry => (entry.1.eval z, entry.2 z)).reverse))).getD 0
  rw [← List.map_reverse]
  induction state.completed.reverse with
  | nil => simp [fixedPriorityCompletionResponseFromLedger]
  | cons entry entries ih =>
      by_cases hidentifier : entry.1.identifier = identifier
      · simp [fixedPriorityCompletionResponseFromLedger, hidentifier,
          NonpreemptivePriorityFixedJobCoordinate.eval]
      · simpa [fixedPriorityCompletionResponseFromLedger, hidentifier,
          NonpreemptivePriorityFixedJobCoordinate.eval] using ih

/-- On a fixed ledger fiber and a matching finite service skeleton, evaluating
the static replay is exactly the literal two-sided selected/Palm replay.  This
is the pathwise connection needed to glue the Borel skeleton responses into
the observable produced by the executable queue dynamics. -/
theorem stationaryPriorityClassTaggedFixedReplayState_eval_eq_finiteReplayState_of_matches
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hledger : stationaryPriorityClassTaggedFiniteReplayLedgerFiber
      i older t pastLabels futureLabels z)
    (hmatches : stationaryPriorityClassTaggedFixedReplayBranchMatches
      meanService i older t pastLabels futureLabels skeleton z) :
    (stationaryPriorityClassTaggedFixedReplayState meanService i older t
      pastLabels futureLabels skeleton).eval z =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older t := by
  rcases hledger with ⟨hpastLabels, hfutureLabels⟩
  rcases hmatches with ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  have hpastAfter :
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
        meanService i older pastLabels skeleton).eval z =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-older) 0) := by
    calc
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
          meanService i older pastLabels skeleton).eval z =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedFixedPastInitial i older).eval z)
            ((stationaryPriorityClassTaggedFixedJobs meanService i pastLabels).map
              fun job => job.eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPastAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedFixedPastInitial i older)
                (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
                skeleton.pastArrivalSlots z hpastArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
            (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
              meanService i z (-older) 0) := by
            rw [eval_stationaryPriorityClassTaggedFixedJobs]
            simp only [stationaryPriorityClassTaggedFixedPastInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              canonicalStationaryPriorityClassTaggedArrivalWindowJobs]
            rw [hpastLabels]
            rfl
  have hpast :
      (stationaryPriorityClassTaggedFixedPastState
        meanService i older pastLabels skeleton).eval z =
        canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i z (-older) 0 := by
    calc
      (stationaryPriorityClassTaggedFixedPastState
          meanService i older pastLabels skeleton).eval z =
          advanceNonpreemptivePriorityWorkState
            (totalFixedNonpreemptivePriorityWorkJobs
              (stationaryPriorityClassTaggedFixedPastAfterArrivals
                meanService i older pastLabels skeleton))
            0
            ((stationaryPriorityClassTaggedFixedPastAfterArrivals
              meanService i older pastLabels skeleton).eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPastState] using
              (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
                (totalFixedNonpreemptivePriorityWorkJobs
                  (stationaryPriorityClassTaggedFixedPastAfterArrivals
                    meanService i older pastLabels skeleton))
                (fun _ => 0)
                (stationaryPriorityClassTaggedFixedPastAfterArrivals
                  meanService i older pastLabels skeleton)
                skeleton.pastTerminalCompletionCount skeleton.pastTerminal z hpastTerminal)
      _ = canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-older) 0 := by
            rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval]
            rw [hpastAfter]
            rfl
  have hpostTag :
      (stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton).eval z =
        admitNonpreemptivePriorityJob
          (clearNonpreemptivePriorityCompletionLedger
            (canonicalStationaryPriorityClassTaggedFiniteWindowState
              meanService i z (-older) 0))
          (stationaryPriorityClassTaggedJob meanService i z) := by
    simp only [stationaryPriorityClassTaggedFixedPostTagState,
      NonpreemptivePriorityFixedStateCoordinate.eval_admit,
      NonpreemptivePriorityFixedStateCoordinate.eval_clearCompleted]
    rw [hpast]
    rfl
  have hfuture :
      (stationaryPriorityClassTaggedFixedPostFutureState
        meanService i older pastLabels futureLabels skeleton).eval z =
        runNonpreemptivePriorityArrivalTrace
          (admitNonpreemptivePriorityJob
            (clearNonpreemptivePriorityCompletionLedger
              (canonicalStationaryPriorityClassTaggedFiniteWindowState
                meanService i z (-older) 0))
            (stationaryPriorityClassTaggedJob meanService i z))
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) := by
    calc
      (stationaryPriorityClassTaggedFixedPostFutureState
          meanService i older pastLabels futureLabels skeleton).eval z =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedFixedPostTagState
              meanService i older pastLabels skeleton).eval z)
            ((stationaryPriorityClassTaggedFixedJobs meanService i futureLabels).map
              fun job => job.eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPostFutureState] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedFixedPostTagState
                  meanService i older pastLabels skeleton)
                (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
                skeleton.futureArrivalSlots z hfutureArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (admitNonpreemptivePriorityJob
              (clearNonpreemptivePriorityCompletionLedger
                (canonicalStationaryPriorityClassTaggedFiniteWindowState
                  meanService i z (-older) 0))
              (stationaryPriorityClassTaggedJob meanService i z))
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) := by
            rw [hpostTag, eval_stationaryPriorityClassTaggedFixedJobs]
            simp only [canonicalStationaryPriorityClassTaggedFutureArrivalJobs]
            rw [hfutureLabels]
  calc
    (stationaryPriorityClassTaggedFixedReplayState meanService i older t
        pastLabels futureLabels skeleton).eval z =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (stationaryPriorityClassTaggedFixedPostFutureState
              meanService i older pastLabels futureLabels skeleton))
          t
          ((stationaryPriorityClassTaggedFixedPostFutureState
            meanService i older pastLabels futureLabels skeleton).eval z) := by
          simpa [stationaryPriorityClassTaggedFixedReplayState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (stationaryPriorityClassTaggedFixedPostFutureState
                  meanService i older pastLabels futureLabels skeleton))
              (fun _ => t)
              (stationaryPriorityClassTaggedFixedPostFutureState
                meanService i older pastLabels futureLabels skeleton)
              skeleton.futureTerminalCompletionCount skeleton.futureTerminal z hfutureTerminal)
    _ = stationaryPriorityClassTaggedFiniteReplayPostArrivalState
          meanService i z older t := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hfuture]
          rfl

/-- On a fixed ledger fiber and matching service skeleton at a Borel random
horizon, evaluating the static replay is exactly the corresponding literal
selected/Palm finite replay. -/
theorem stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_finiteReplayState_of_matches
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hledger : stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
      i older target pastLabels futureLabels z)
    (hmatches : stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
      meanService i older target pastLabels futureLabels skeleton z) :
    (stationaryPriorityClassTaggedFixedReplayStateAt meanService i older target
      pastLabels futureLabels skeleton).eval z =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older (target z) := by
  have hledgerFixed : stationaryPriorityClassTaggedFiniteReplayLedgerFiber
      i older (target z) pastLabels futureLabels z := by
    simpa [stationaryPriorityClassTaggedFiniteReplayLedgerFiber,
      stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt] using hledger
  have hmatchesFixed : stationaryPriorityClassTaggedFixedReplayBranchMatches
      meanService i older (target z) pastLabels futureLabels skeleton z := by
    rcases hmatches with ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
    refine ⟨hpastArrivals, hpastTerminal, hfutureArrivals, ?_⟩
    exact (fixedPriorityAdvanceBranchMatches_congr_target
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
          pastLabels futureLabels skeleton))
      target (fun _ => target z)
      (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal z rfl).mp
        hfutureTerminal
  rw [stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_fixed]
  exact stationaryPriorityClassTaggedFixedReplayState_eval_eq_finiteReplayState_of_matches
    meanService i older (target z) pastLabels futureLabels skeleton z hledgerFixed hmatchesFixed

/-- A finite selected replay that omits every arrival at its right endpoint.
It is the literal strict-past counterpart of the right-closed finite replay. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (admitNonpreemptivePriorityJob
      (clearNonpreemptivePriorityCompletionLedger preArrival)
      (stationaryPriorityClassTaggedJob meanService i z))
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals

/-- When the Palm tag is isolated at time zero, the full canonical finite
replay through a positive horizon and the strict post-tag replay have the
same live queue.  The strict replay deliberately clears only historical
completion observations, which do not affect its active or waiting jobs. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_zero_to_strictReplay
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hzero : ∀ q : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityClassTaggedArrival i z q.1 q.2 = 0 → q = Sigma.mk i 0) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) t)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older t) := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older)
  let past := canonicalStationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z (-older) 0
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let future := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  have hwhole : canonicalStationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) t = past ++ tag :: future := by
    rw [canonicalStationaryPriorityClassTaggedArrivalWindowJobs_append
      meanService i z (-older) 0 t hgood (neg_nonpos.mpr holder) ht.le,
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs_zero_to_eq_tag_cons_future
        meanService i z t ht hgood hzero]
  have hrun : runNonpreemptivePriorityArrivalTrace initial (past ++ tag :: future) =
      runNonpreemptivePriorityArrivalTrace
        (admitNonpreemptivePriorityJob preArrival tag) future := by
    rw [runNonpreemptivePriorityArrivalTrace_append]
    change runNonpreemptivePriorityArrivalTrace
        (advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial past))
          (runNonpreemptivePriorityArrivalTrace initial past) tag) future = _
    unfold advanceThenAdmitNonpreemptivePriorityJob
    rw [show tag.arrivalTime = 0 by
      simpa [tag] using stationaryPriorityClassTaggedJob_arrivalTime meanService i z]
    rfl
  have hinitial : liveEquivalentNonpreemptivePriorityWorkState
      (admitNonpreemptivePriorityJob
        (clearNonpreemptivePriorityCompletionLedger preArrival) tag)
      (admitNonpreemptivePriorityJob preArrival tag) := by
    apply liveEquivalentNonpreemptivePriorityWorkState_admit
    exact liveEquivalent_clearNonpreemptivePriorityCompletionLedger preArrival
  have hafter := liveEquivalentNonpreemptivePriorityWorkState_run
    _ _ future hinitial
  have hcount : totalNonpreemptivePriorityWorkJobs
      (runNonpreemptivePriorityArrivalTrace
        (admitNonpreemptivePriorityJob
          (clearNonpreemptivePriorityCompletionLedger preArrival) tag) future) =
      totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace
          (admitNonpreemptivePriorityJob preArrival tag) future) :=
    totalNonpreemptivePriorityWorkJobs_eq_of_liveEquivalent hafter
  have hcontinuation := liveEquivalentNonpreemptivePriorityWorkState_runThenAdvance
    (totalNonpreemptivePriorityWorkJobs
      (runNonpreemptivePriorityArrivalTrace
        (admitNonpreemptivePriorityJob preArrival tag) future)) t
    (admitNonpreemptivePriorityJob preArrival tag)
    (admitNonpreemptivePriorityJob
      (clearNonpreemptivePriorityCompletionLedger preArrival) tag)
    future (liveEquivalentNonpreemptivePriorityWorkState_symm hinitial)
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  dsimp only
  rw [hwhole, hrun, hcount]
  exact hcontinuation

/-- The preceding finite replay comparison only needs isolation of the tag
within the queried endpoint window.  This local form is the one supplied by
the finite stationary no-simultaneous-arrivals event after Campbell
recentring. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_zero_to_strictReplay_of_unique_zero_in_window
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hzero : ∀ q : NonpreemptivePriorityArrivalIndex n,
      0 ≤ stationaryPriorityClassTaggedArrival i z q.1 q.2 →
      stationaryPriorityClassTaggedArrival i z q.1 q.2 < t →
      stationaryPriorityClassTaggedArrival i z q.1 q.2 = 0 → q = Sigma.mk i 0) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) t)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older t) := by
  apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_zero_to_strictReplay
    meanService i z older t holder ht hgood
  intro q hq
  apply hzero q
  · rw [hq]
  · rw [hq]
    exact ht
  · exact hq

/-- After a Campbell-selected arrival is recentered, collision-freedom of the
literal finite global window isolates the distinguished zero-time customer in
the selected replay window.  Thus the deterministic finite-replay comparison
can use the stationary no-simultaneous-arrivals event without requiring an
unnecessarily global condition on the Palm sample. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay_of_noArrivalTies
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k).1.1)
    (hnoTies : ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x))
          (-older) t),
      ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x))
          (-older) t),
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x))
            first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x))
            second.2 → first = second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) t)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) := by
  let omega := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
    (Probability.Queueing.timedEmbeddedArrival x.1 k)
    (multiclassStationaryPoissonWorkClassAssemble i x)
  let z := (multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i).recenterAt x k
  have hphase : (omega i).1.1.2 = 0 := by
    exact multiclassStationaryPoissonWorkClassFlow_at_baseArrival_phase_zero
      arrivalRate harrivalRate i x k
  have hrecenter : z =
      multiclassStationaryPoissonWorkClassTaggedView i omega := by
    exact multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
      arrivalRate harrivalRate i x k
  apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_zero_to_strictReplay_of_unique_zero_in_window
    meanService i z older t holder ht (by simpa [z] using hgood)
  intro q hnonneg hbefore hqzero
  have hqtime : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      q.1 omega q.2 = 0 := by
    rw [← multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
      i q.1 omega q.2 hphase]
    rw [← hrecenter]
    exact hqzero
  have htagtime : Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      i omega 0 = 0 := by
    rw [← multiclassStationaryPoissonWorkClassTaggedArrival_view_eq_multiclassArrival
      i i omega 0 hphase]
    exact stationaryPriorityClassTaggedArrival_tag_zero i
      (multiclassStationaryPoissonWorkClassTaggedView i omega)
  have hqmem : q ∈ nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityArrivalWindowIndices omega (-older) t) := by
    have hqbase : Probability.PoissonProcess.suspensionBaseArrival
        (omega q.1).1 q.2 = 0 := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
        Probability.Queueing.stationaryPoissonWorkArrival] using hqtime
    simpa [nonpreemptivePriorityArrivalWindowIndices, stationaryPriorityArrivalWindowIndices] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        (-older) t (omega q.1).1 q.2).mpr
        ⟨by rw [hqbase]; exact neg_nonpos.mpr holder, by rw [hqbase]; exact ht⟩
  have htagmem : (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n) ∈
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices omega (-older) t) := by
    have htagbase : Probability.PoissonProcess.suspensionBaseArrival (omega i).1 0 = 0 := by
      simpa [Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
        Probability.Queueing.stationaryPoissonWorkArrival] using htagtime
    simpa [nonpreemptivePriorityArrivalWindowIndices, stationaryPriorityArrivalWindowIndices] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        (-older) t (omega i).1 0).mpr
        ⟨by rw [htagbase]; exact neg_nonpos.mpr holder, by rw [htagbase]; exact ht⟩
  apply hnoTies q (by simpa [omega] using hqmem) (Sigma.mk i 0)
    (by simpa [omega] using htagmem)
  exact hqtime.trans htagtime.symm

/-- The recentered finite replay comparison can use a collision-free global
input directly; the required finite-window premise is then immediate. -/
theorem liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay_of_noArrivalTies_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k).1.1)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x)) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x)) second.2 → first = second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) t)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) := by
  apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay_of_noArrivalTies
    arrivalRate meanService harrivalRate i x k older t holder ht hgood
  intro first _ second _ heq
  exact hnoTies first second heq

/-- Under the selected-class Campbell base law, the assembled literal global
input has no simultaneous labelled arrivals almost surely. -/
theorem ae_stationaryPriorityArrival_noArrivalTies_all_campbellBase
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
            (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
            (multiclassStationaryPoissonWorkClassAssemble i x) second.2 →
          first = second := by
  let Pbase := (Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
    arrivalRate
  let assemble := multiclassStationaryPoissonWorkClassAssemble i
  have hassemble : MeasurePreserving assemble Pbase Pstationary := by
    simpa [Pbase, Pstationary, assemble] using
      measurePreserving_multiclassStationaryPoissonWorkClassAssemble
        arrivalRate harrivalRate i
  have hbase : ∀ᵐ x ∂Pbase,
      ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1 (assemble x) first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 (assemble x) second.2 → first = second := by
    refine MeasureTheory.ae_of_ae_map (μ := Pbase) (f := assemble)
      (p := fun omega => ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second)
      hassemble.measurable.aemeasurable ?_
    rw [hassemble.map_eq]
    exact ae_stationaryPriorityArrival_noArrivalTies_all arrivalRate harrivalRate
  simpa [Pbase, assemble] using hbase

/-- Under strict total load, almost every split stationary input has a
nonnegative global net-input cutoff after every deterministic time shift.
This uniform form is the one needed when a Campbell arrival is followed by a
further elapsed waiting-time coordinate. -/
theorem ae_all_exists_stationaryPriorityNetPastCutoff_campbellBaseFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ offset : ℝ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            offset
            (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff := by
  let Pbase := (Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
    arrivalRate
  let assemble := multiclassStationaryPoissonWorkClassAssemble i
  have hassemble : MeasurePreserving assemble Pbase Pstationary := by
    simpa [Pbase, Pstationary, assemble] using
      measurePreserving_multiclassStationaryPoissonWorkClassAssemble
        arrivalRate harrivalRate i
  have hbase : ∀ᵐ x ∂Pbase, ∀ offset : ℝ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          offset (assemble x)) cutoff := by
    refine MeasureTheory.ae_of_ae_map (μ := Pbase) (f := assemble)
      (p := fun omega => ∀ offset : ℝ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset omega) cutoff)
      hassemble.measurable.aemeasurable ?_
    rw [hassemble.map_eq]
    exact ae_all_exists_stationaryPriorityNetPastCutoff_flow
      arrivalRate meanService harrivalRate hstable
  simpa [Pbase, assemble] using hbase

/-- Under strict total load, almost every split stationary input has a
nonnegative global net-input cutoff after recentering at each labelled
arrival of the distinguished class. -/
theorem ae_all_exists_stationaryPriorityNetPastCutoff_campbellFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff := by
  filter_upwards [ae_all_exists_stationaryPriorityNetPastCutoff_campbellBaseFlow
    arrivalRate meanService harrivalRate hstable i] with x hx
  intro k
  exact hx (Probability.Queueing.timedEmbeddedArrival x.1 k)

/-- Positive class means make every class-labelled service mark of the
assembled stationary input positive almost surely under the Campbell base
law. -/
theorem ae_all_stationaryPriorityWorkRequirement_positive_campbellBase
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ j : Fin n, ∀ k : ℤ,
        0 < stationaryPriorityWorkRequirement meanService j
          (multiclassStationaryPoissonWorkClassAssemble i x) k := by
  let Pbase := (Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
    arrivalRate
  let assemble := multiclassStationaryPoissonWorkClassAssemble i
  have hassemble : MeasurePreserving assemble Pbase Pstationary := by
    simpa [Pbase, Pstationary, assemble] using
      measurePreserving_multiclassStationaryPoissonWorkClassAssemble
        arrivalRate harrivalRate i
  refine MeasureTheory.ae_of_ae_map (μ := Pbase) (f := assemble)
    (p := fun omega => ∀ j : Fin n, ∀ k : ℤ,
      0 < stationaryPriorityWorkRequirement meanService j omega k)
    hassemble.measurable.aemeasurable ?_
  rw [hassemble.map_eq]
  exact ae_all_stationaryPriorityWorkRequirement_positive
    arrivalRate meanService harrivalRate hmeanService

/-- The corresponding selected/Palm input also has a cutoff after every
labelled recentering.  This is the selected-coordinate form of the global
time-shift statement. -/
theorem ae_all_exists_stationaryPriorityClassTaggedNetPastCutoff_campbellRecenter
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityClassTaggedNetPastCutoff meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) cutoff := by
  filter_upwards [ae_all_exists_stationaryPriorityNetPastCutoff_campbellFlow
    arrivalRate meanService harrivalRate hstable i] with x hx
  intro k
  rcases hx k with ⟨cutoff, hcutoffNonneg, hcutoff⟩
  exact ⟨cutoff, hcutoffNonneg,
    (stationaryPriorityClassTaggedNetPastCutoff_campbellRecenter_iff_globalFlow
      arrivalRate meanService harrivalRate i x k cutoff).mpr hcutoff⟩

/-- Under the Campbell base law, the literal global input remains
collision-free after flowing it to any labelled selected-class arrival.  This
uses only stationary-input law preservation and the deterministic restoration
of shifted labels, not a queue-state argument. -/
theorem ae_stationaryPriorityArrival_noArrivalTies_all_campbellFlow
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ, ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x)) first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x)) second.2 →
          first = second := by
  filter_upwards [ae_stationaryPriorityArrival_noArrivalTies_all_campbellBase
    arrivalRate harrivalRate i] with x hbase
  intro k
  exact stationaryPriorityArrival_noArrivalTies_all_flow
    (multiclassStationaryPoissonWorkClassAssemble i x)
    (Probability.Queueing.timedEmbeddedArrival x.1 k) hbase

/-- For every fixed finite recentered window, the canonical global replay
and strict selected replay have the same live queue almost surely under the
Campbell base law, simultaneously for all selected arrival labels. -/
theorem ae_forall_liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ,
        liveEquivalentNonpreemptivePriorityWorkState
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) (-older) t)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) older t) := by
  filter_upwards [ae_stationaryPriorityArrival_noArrivalTies_all_campbellFlow
    arrivalRate harrivalRate i] with x hnoTies
  intro k
  exact liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay_of_noArrivalTies_all
    arrivalRate meanService harrivalRate i x k older t holder ht
    (multiclassStationaryPoissonWorkClassCampbellRecenter_gapPath_good
      arrivalRate harrivalRate i x k)
    (hnoTies k)

/-- The distinguished customer's FIFO waiting indicator in its strict
recentered replay equals the indicator of the same zero-labelled customer in
the literal flowed global finite replay, almost surely under the Campbell
base law.  This is the pointwise state/customer comparison needed before any
integration or receding-window argument. -/
theorem ae_forall_stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_globalFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ,
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) older t) =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
            (stationaryPriorityFiniteWindowState meanService
              (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
                (Probability.Queueing.timedEmbeddedArrival x.1 k)
                (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
  filter_upwards [
    ae_forall_liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay
      arrivalRate meanService harrivalRate i older t holder ht] with x hequivalent
  intro k
  have hindicator :=
    nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent
      (Sigma.mk i 0) (hequivalent k)
  calc
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) older t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) (-older) t) :=
          hindicator.symm
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
          rw [canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_eq_globalFlow
            arrivalRate meanService harrivalRate i x k (-older) t]

/-- The finite selected-to-global waiting-indicator bridge is deterministic
once the assembled input is globally collision-free.  In particular, the
same event supports every finite choice of replay horizons. -/
theorem stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_globalFiniteWindow_of_noArrivalTies_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second) :
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityFiniteWindowState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.Queueing.timedEmbeddedArrival x.1 k)
            (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
  have hequivalent :=
    liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_zero_to_strictReplay_of_noArrivalTies_all
      arrivalRate meanService harrivalRate i x k older t holder ht
      (multiclassStationaryPoissonWorkClassCampbellRecenter_gapPath_good
        arrivalRate harrivalRate i x k)
      (stationaryPriorityArrival_noArrivalTies_all_flow
        (multiclassStationaryPoissonWorkClassAssemble i x)
        (Probability.Queueing.timedEmbeddedArrival x.1 k) hnoTies)
  have hindicator :=
    nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent
      (Sigma.mk i 0) hequivalent
  calc
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) older t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) (-older) t) :=
          hindicator.symm
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
          rw [canonicalStationaryPriorityClassTaggedFiniteWindowState_campbellRecenter_eq_globalFlow
            arrivalRate meanService harrivalRate i x k (-older) t]

/-- At a selected-class arrival epoch, restoring the zero label of the
recentered input gives precisely the original selected arrival label. -/
theorem stationaryPriorityFlowRestoreIndex_campbellSelectedTag_eq
    {n : ℕ} (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) :
    stationaryPriorityFlowRestoreIndex
      (multiclassStationaryPoissonWorkClassAssemble i x)
      (Probability.Queueing.timedEmbeddedArrival x.1 k)
      (Sigma.mk i 0) = Sigma.mk i k := by
  simp [stationaryPriorityFlowRestoreIndex,
    Probability.Queueing.suspensionCrossingIndexPastClosed_suspensionBaseArrival]

/-- The selected Palm service mark after Campbell recentering is the service
mark of the same restored customer in the original stationary input. -/
theorem stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) :
    stationaryPriorityClassTaggedWorkRequirement meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) =
      stationaryPriorityWorkRequirement meanService i
        (multiclassStationaryPoissonWorkClassAssemble i x) k := by
  let omega := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
    (Probability.Queueing.timedEmbeddedArrival x.1 k)
    (multiclassStationaryPoissonWorkClassAssemble i x)
  calc
    stationaryPriorityClassTaggedWorkRequirement meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) i 0 :=
          stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate meanService i _
    _ = stationaryPriorityWorkRequirement meanService i omega 0 := by
          rw [multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
            arrivalRate harrivalRate i x k]
          simp [stationaryPriorityClassTaggedWorkRequirementAt,
            multiclassStationaryPoissonWorkClassTaggedRequirementAt,
            stationaryPriorityWorkRequirement,
            Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
            Probability.Queueing.stationaryPoissonWorkRequirement]
          left
          rfl
    _ = stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k := by
          change stationaryPriorityWorkRequirement meanService i
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              (Probability.Queueing.timedEmbeddedArrival x.1 k)
              (multiclassStationaryPoissonWorkClassAssemble i x)) 0 = _
          simpa [stationaryPriorityFlowRestoreIndex,
            Probability.Queueing.suspensionCrossingIndexPastClosed_suspensionBaseArrival] using
            stationaryPriorityWorkRequirement_flow_restore meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k) (Sigma.mk i 0)

/-- Every selected/Palm work-mark coordinate after a Campbell recentering is
the corresponding coordinate of the literal global input at that arrival
epoch.  This includes nonselected classes and nonzero labels, so it transports
the simultaneous positive-mark event used by remote-past coalescence. -/
theorem stationaryPriorityClassTaggedWorkRequirementAt_campbellRecenter_eq_globalFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (selectedIndex : ℤ) (j : Fin n) (k : ℤ) :
    stationaryPriorityClassTaggedWorkRequirementAt meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x selectedIndex) j k =
      stationaryPriorityWorkRequirement meanService j
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 selectedIndex)
          (multiclassStationaryPoissonWorkClassAssemble i x)) k := by
  rw [multiclassStationaryPoissonWorkClassCampbellRecenter_eq_taggedView_flow_at_baseArrival
    arrivalRate harrivalRate i x selectedIndex]
  unfold stationaryPriorityClassTaggedWorkRequirementAt stationaryPriorityWorkRequirement
  rw [multiclassStationaryPoissonWorkClassTaggedRequirementAt_view_eq_multiclassRequirement]

/-- In a finite original-time window around a selected Campbell arrival, the
selected customer's waiting indicator is exactly the zero-tag indicator in
the corresponding recentered strict replay.  This is a local finite-window
identity; no long-time or stationary limit is used here. -/
theorem ae_forall_stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ,
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) older t) =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityFiniteWindowState meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
              (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  filter_upwards [
    ae_forall_stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_globalFiniteWindow
      arrivalRate meanService harrivalRate i older t holder ht,
    ae_stationaryPriorityArrival_noArrivalTies_all_campbellBase
      arrivalRate harrivalRate i] with x hshift hnoTies
  intro k
  let offset := Probability.Queueing.timedEmbeddedArrival x.1 k
  have hfiniteNoTies : ∀ first ∈
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices
          (multiclassStationaryPoissonWorkClassAssemble i x) (offset - older) (offset + t)),
      ∀ second ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices
            (multiclassStationaryPoissonWorkClassAssemble i x) (offset - older) (offset + t)),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second := by
    intro first _ second _ heq
    exact hnoTies first second heq
  have htransport :
      nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) ↔
        nonpreemptivePriorityWaitingIdentifier (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := by
    convert nonpreemptivePriorityWaitingIdentifier_stationaryPriorityFiniteWindow_flow_restore_iff
      meanService (multiclassStationaryPoissonWorkClassAssemble i x) offset
      (offset - older) (offset + t) hfiniteNoTies (Sigma.mk i 0) using 1
    · ring_nf
    · rw [show stationaryPriorityFlowRestoreIndex
          (multiclassStationaryPoissonWorkClassAssemble i x) offset (Sigma.mk i 0) =
          Sigma.mk i k by
          simpa [offset] using stationaryPriorityFlowRestoreIndex_campbellSelectedTag_eq i x k]
  have hindicator :
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := by
    unfold nonpreemptivePriorityWaitingIdentifierIndicator
    rw [htransport]
  calc
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) older t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
          simpa [offset] using hshift k
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := hindicator
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
            (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
          rw [show offset = Probability.Queueing.timedEmbeddedArrival x.1 k from rfl]

/-- The original-time selected-customer finite bridge is deterministic on a
globally collision-free assembled input, and hence may be used uniformly over
finite observation horizons. -/
theorem stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_of_noArrivalTies_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second) :
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityFiniteWindowState meanService
          (multiclassStationaryPoissonWorkClassAssemble i x)
          (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  let offset := Probability.Queueing.timedEmbeddedArrival x.1 k
  have hshift :=
    stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_globalFiniteWindow_of_noArrivalTies_all
      arrivalRate meanService harrivalRate i x k older t holder ht hnoTies
  have hfiniteNoTies : ∀ first ∈
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices
          (multiclassStationaryPoissonWorkClassAssemble i x) (offset - older) (offset + t)),
      ∀ second ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices
            (multiclassStationaryPoissonWorkClassAssemble i x) (offset - older) (offset + t)),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second := by
    intro first _ second _ heq
    exact hnoTies first second heq
  have htransport :
      nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) ↔
        nonpreemptivePriorityWaitingIdentifier (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := by
    convert nonpreemptivePriorityWaitingIdentifier_stationaryPriorityFiniteWindow_flow_restore_iff
      meanService (multiclassStationaryPoissonWorkClassAssemble i x) offset
      (offset - older) (offset + t) hfiniteNoTies (Sigma.mk i 0) using 1
    · ring_nf
    · rw [show stationaryPriorityFlowRestoreIndex
          (multiclassStationaryPoissonWorkClassAssemble i x) offset (Sigma.mk i 0) =
          Sigma.mk i k by
          simpa [offset] using stationaryPriorityFlowRestoreIndex_campbellSelectedTag_eq i x k]
  have hindicator :
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := by
    unfold nonpreemptivePriorityWaitingIdentifierIndicator
    rw [htransport]
  calc
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) older t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
              (multiclassStationaryPoissonWorkClassAssemble i x)) (-older) t) := by
          simpa [offset] using hshift
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (offset - older) (offset + t)) := hindicator
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
            (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
          rw [show offset = Probability.Queueing.timedEmbeddedArrival x.1 k from rfl]

/-- A single Campbell-base null set supports the original-time finite bridge
simultaneously for every selected label and every finite observation window. -/
theorem ae_forall_stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ, ∀ older t : ℝ, 0 ≤ older → 0 < t →
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) older t) =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityFiniteWindowState meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
              (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  filter_upwards [ae_stationaryPriorityArrival_noArrivalTies_all_campbellBase
    arrivalRate harrivalRate i] with x hnoTies
  intro k older t holder ht
  exact stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_of_noArrivalTies_all
    arrivalRate meanService harrivalRate i x k older t holder ht hnoTies

/-- The original-time finite bridge also preserves the selected customer's
work-weighted waiting contribution. -/
theorem ae_forall_stationaryPriorityClassTaggedStrictReplayWorkWaitingIndicator_eq_originalFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ,
        stationaryPriorityClassTaggedWorkRequirement meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
            (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
              meanService i
              ((multiclassStationaryPoissonWorkClassCampbellCertificate
                arrivalRate harrivalRate i).recenterAt x k) older t) =
          stationaryPriorityWorkRequirement meanService i
            (multiclassStationaryPoissonWorkClassAssemble i x) k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityFiniteWindowState meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k - older)
              (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  filter_upwards [
    ae_forall_stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow
      arrivalRate meanService harrivalRate i older t holder ht] with x hwaiting
  intro k
  rw [stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
    arrivalRate meanService harrivalRate i x k, hwaiting k]

/-- In a strict finite replay whose historical ledger is cleared at the Palm
origin, every subsequently recorded completion lies strictly after time zero.
This is a deterministic queue-semantic fact; it prevents the Borel numerical
default used for an absent completion observation from being confused with a
physical completion epoch. -/
theorem nonpreemptivePriorityCompletionTimesAfter_zero_finiteReplayBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    nonpreemptivePriorityCompletionTimesAfter 0
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older t) := by
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let cleared := clearNonpreemptivePriorityCompletionLedger preArrival
  let initial := admitNonpreemptivePriorityJob cleared
    (stationaryPriorityClassTaggedJob meanService i z)
  let future := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial future
  have hpreClock : preArrival.currentTime = 0 := by
    exact canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
      meanService i z (-older) 0 (neg_nonpos.mpr holder) hgood
  have hprePositive : positiveNonpreemptivePriorityResidualWork preArrival := by
    apply positiveNonpreemptivePriorityResidualWork_canonicalStationaryPriorityClassTaggedFiniteWindowState
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-older) 0 job).mp hjob with ⟨j, k, _, hcoordinate⟩
    subst job
    exact hpositive j k
  have hclearedPositive : positiveNonpreemptivePriorityResidualWork cleared := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hprePositive
  have hclearedTimes : nonpreemptivePriorityCompletionTimesAfter 0 cleared := by
    apply nonpreemptivePriorityCompletionTimesAfter_clear 0 preArrival
    simpa [hpreClock]
  have htagPositive : 0 < (stationaryPriorityClassTaggedJob meanService i z).serviceWork := by
    rw [stationaryPriorityClassTaggedJob_serviceWork]
    simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hpositive i 0
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    simpa [initial] using positiveNonpreemptivePriorityResidualWork_admit
      cleared (stationaryPriorityClassTaggedJob meanService i z) hclearedPositive htagPositive
  have hinitialTimes : nonpreemptivePriorityCompletionTimesAfter 0 initial := by
    simpa [initial] using nonpreemptivePriorityCompletionTimesAfter_admit
      0 cleared (stationaryPriorityClassTaggedJob meanService i z) hclearedTimes
  have hfuturePositive : ∀ job ∈ future, 0 < job.serviceWork := by
    intro job hjob
    unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon at hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
    exact hpositive q.1 q.2
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    exact positiveNonpreemptivePriorityResidualWork_run initial future
      hinitialPositive hfuturePositive
  have hafterTimes : nonpreemptivePriorityCompletionTimesAfter 0 afterArrivals := by
    exact nonpreemptivePriorityCompletionTimesAfter_run 0 initial future
      hinitialPositive hinitialTimes hfuturePositive
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  dsimp only
  exact nonpreemptivePriorityCompletionTimesAfter_advance
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t 0 afterArrivals
    hafterPositive hafterTimes

/-- The selected customer's completion observation in the strict-past finite
replay. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) : Option ℝ :=
  nonpreemptivePriorityRecordedCompletionTime
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t)
    (Sigma.mk i 0)

/-- On the positive-work good carrier, the Borel numerical representation of
the strict finite completion observation is zero exactly when the observation
is absent. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_eq_zero_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older t).getD 0 = 0 ↔
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older t = none := by
  let state := stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
    meanService i z older t
  have htimes : nonpreemptivePriorityCompletionTimesAfter 0 state := by
    simpa [state] using
      nonpreemptivePriorityCompletionTimesAfter_zero_finiteReplayBeforeHorizon
        meanService i z older t holder ht hgood hpositive
  constructor
  · intro hzero
    cases hresponse : stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older t with
    | none => rfl
    | some completedAt =>
        have hpos : 0 < completedAt := by
          apply nonpreemptivePriorityRecordedCompletionTime_pos_of_eq_some 0 state (Sigma.mk i 0)
          · exact htimes
          · simpa [state,
              stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon] using hresponse
        simp [hresponse] at hzero
        linarith
  · intro hnone
    simp [hnone]

/-- Equivalently, the numerical strict-replay observation is nonzero exactly
when the selected completion has already been physically recorded. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_ne_zero_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older t).getD 0 ≠ 0 ↔
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older t ≠ none := by
  exact not_congr
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_eq_zero_iff
      meanService i z older t holder ht hgood hpositive)

/-- In a finite two-sided replay, arrivals exactly at the queried endpoint do
not alter the selected customer's recorded completion observation. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_beforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) (holder : 0 ≤ older) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime meanService i z older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older t := by
  apply nonpreemptivePriorityRecordedCompletionTime_congr_completed
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let initial := admitNonpreemptivePriorityJob
    (clearNonpreemptivePriorityCompletionLedger preArrival)
    (stationaryPriorityClassTaggedJob meanService i z)
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z t
  have hpreClock : preArrival.currentTime = 0 := by
    exact canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
      meanService i z (-older) 0 (neg_nonpos.mpr holder) hgood
  have hclock : initial.currentTime ≤ t := by
    dsimp only [initial]
    rw [admitNonpreemptivePriorityJob_currentTime]
    change preArrival.currentTime ≤ t
    rw [hpreClock]
    exact ht
  have htail : ∀ job ∈ tail, job.arrivalTime = t := by
    intro job hjob
    exact arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
      meanService i z t hgood job (by simpa [tail] using hjob)
  have hfrontClock :
      (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ t := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · exact hclock
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t job (by simpa [front] using hjob)).le
  have hsplit := canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    meanService i z t hgood
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalState
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  dsimp only
  rw [hsplit]
  simpa [preArrival, initial, front, tail] using
    (completed_advance_run_append_of_all_arrivalTime_eq_target initial front tail t hfrontClock htail)

/-- Under strict total load, diagonal two-sided replays have recorded the
selected completion before the `(N+1)`st arrival of any fixed passive class
for all sufficiently large `N`, almost surely.  The proof combines remote
past coalescence, eventual causal completion, and stationary-renewal
nonexplosion. -/
theorem ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_ne_none_at_passiveArrival
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ N : ℕ in Filter.atTop,
        stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
          meanService i z (N : ℝ)
          (stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))) ≠ none := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_eventually_stationaryPriorityClassTaggedFinitePostArrivalResponseTime_ne_none
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hcoalesces hpost hgood
  rcases hcoalesces with ⟨cutoff, hcutoff, hcoalesces⟩
  let arrival : ℕ → ℝ := fun N =>
    stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))
  have harrivalTendsto : Filter.Tendsto arrival Filter.atTop Filter.atTop := by
    simpa [arrival, stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2,
      Probability.Queueing.stationaryPoissonWorkArrival,
      Probability.Queueing.timedEmbeddedArrival] using
      Probability.PoissonProcess.tendsto_suspensionBaseArrival_ofNat_succ_atTop
        (z.2 j).1
  have hpostArrival : ∀ᶠ N : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z
        (arrival N) ≠ none :=
    harrivalTendsto.eventually hpost
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil cutoff), hpostArrival] with N hN hresponse
  have hcutoffN : cutoff ≤ (N : ℝ) := by
    calc
      cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
      _ ≤ (N : ℝ) := by exact_mod_cast hN
  have hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-(N : ℝ)) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z) :=
    hcoalesces (N : ℝ) hcutoffN
  have hfull : stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z (N : ℝ) (arrival N) =
      stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z (arrival N) :=
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_liveEquivalent
      meanService i z (N : ℝ) (arrival N) hequivalent
  have harrivalNonneg : 0 ≤ arrival N := by
    dsimp [arrival, stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival]
    rw [dif_neg j.2]
    exact (Probability.PoissonProcess.zero_lt_suspensionBaseArrival_ofNat_succ
      (z.2 j).1 N).le
  have hstrict : stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z (N : ℝ) (arrival N) =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z (N : ℝ) (arrival N) :=
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_beforeHorizon
      meanService i z (N : ℝ) (arrival N) (Nat.cast_nonneg N) harrivalNonneg hgood
  intro hnone
  apply hresponse
  rw [← hfull, hstrict]
  exact hnone

/-- On a fixed strict-ledger fiber and matching service skeleton, evaluating
the static replay is exactly the finite replay that omits endpoint arrivals. -/
theorem stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_finiteReplayStateBeforeHorizon_of_matches
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (pastLabels futureLabels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hledger : stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
      i older target pastLabels futureLabels z)
    (hmatches : stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
      meanService i older target pastLabels futureLabels skeleton z) :
    (stationaryPriorityClassTaggedFixedReplayStateAt meanService i older target
      pastLabels futureLabels skeleton).eval z =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older (target z) := by
  rcases hledger with ⟨hpastLabels, hfutureLabels⟩
  rcases hmatches with ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  have hmatchesFixed : fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
          pastLabels futureLabels skeleton))
      (fun _ => target z)
      (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal z :=
    (fixedPriorityAdvanceBranchMatches_congr_target
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
          pastLabels futureLabels skeleton))
      target (fun _ => target z)
      (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
        pastLabels futureLabels skeleton)
      skeleton.futureTerminalCompletionCount skeleton.futureTerminal z rfl).mp hfutureTerminal
  rw [stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_fixed]
  have hpastAfter :
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
        meanService i older pastLabels skeleton).eval z =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
          (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-older) 0) := by
    calc
      (stationaryPriorityClassTaggedFixedPastAfterArrivals
          meanService i older pastLabels skeleton).eval z =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedFixedPastInitial i older).eval z)
            ((stationaryPriorityClassTaggedFixedJobs meanService i pastLabels).map
              fun job => job.eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPastAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedFixedPastInitial i older)
                (stationaryPriorityClassTaggedFixedJobs meanService i pastLabels)
                skeleton.pastArrivalSlots z hpastArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) (-older))
            (canonicalStationaryPriorityClassTaggedArrivalWindowJobs
              meanService i z (-older) 0) := by
            rw [eval_stationaryPriorityClassTaggedFixedJobs]
            simp only [stationaryPriorityClassTaggedFixedPastInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              canonicalStationaryPriorityClassTaggedArrivalWindowJobs]
            rw [hpastLabels]
            rfl
  have hpast :
      (stationaryPriorityClassTaggedFixedPastState
        meanService i older pastLabels skeleton).eval z =
        canonicalStationaryPriorityClassTaggedFiniteWindowState
          meanService i z (-older) 0 := by
    calc
      (stationaryPriorityClassTaggedFixedPastState
          meanService i older pastLabels skeleton).eval z =
          advanceNonpreemptivePriorityWorkState
            (totalFixedNonpreemptivePriorityWorkJobs
              (stationaryPriorityClassTaggedFixedPastAfterArrivals
                meanService i older pastLabels skeleton))
            0
            ((stationaryPriorityClassTaggedFixedPastAfterArrivals
              meanService i older pastLabels skeleton).eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPastState] using
              (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
                (totalFixedNonpreemptivePriorityWorkJobs
                  (stationaryPriorityClassTaggedFixedPastAfterArrivals
                    meanService i older pastLabels skeleton))
                (fun _ => 0)
                (stationaryPriorityClassTaggedFixedPastAfterArrivals
                  meanService i older pastLabels skeleton)
                skeleton.pastTerminalCompletionCount skeleton.pastTerminal z hpastTerminal)
      _ = canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-older) 0 := by
            rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval]
            rw [hpastAfter]
            rfl
  have hpostTag :
      (stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton).eval z =
        admitNonpreemptivePriorityJob
          (clearNonpreemptivePriorityCompletionLedger
            (canonicalStationaryPriorityClassTaggedFiniteWindowState
              meanService i z (-older) 0))
          (stationaryPriorityClassTaggedJob meanService i z) := by
    simp only [stationaryPriorityClassTaggedFixedPostTagState,
      NonpreemptivePriorityFixedStateCoordinate.eval_admit,
      NonpreemptivePriorityFixedStateCoordinate.eval_clearCompleted]
    rw [hpast]
    rfl
  have hfuture :
      (stationaryPriorityClassTaggedFixedPostFutureState
        meanService i older pastLabels futureLabels skeleton).eval z =
        runNonpreemptivePriorityArrivalTrace
          (admitNonpreemptivePriorityJob
            (clearNonpreemptivePriorityCompletionLedger
              (canonicalStationaryPriorityClassTaggedFiniteWindowState
                meanService i z (-older) 0))
            (stationaryPriorityClassTaggedJob meanService i z))
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
            meanService i z (target z)) := by
    calc
      (stationaryPriorityClassTaggedFixedPostFutureState
          meanService i older pastLabels futureLabels skeleton).eval z =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityClassTaggedFixedPostTagState
              meanService i older pastLabels skeleton).eval z)
            ((stationaryPriorityClassTaggedFixedJobs meanService i futureLabels).map
              fun job => job.eval z) := by
            simpa [stationaryPriorityClassTaggedFixedPostFutureState] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityClassTaggedFixedPostTagState
                  meanService i older pastLabels skeleton)
                (stationaryPriorityClassTaggedFixedJobs meanService i futureLabels)
                skeleton.futureArrivalSlots z hfutureArrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (admitNonpreemptivePriorityJob
              (clearNonpreemptivePriorityCompletionLedger
                (canonicalStationaryPriorityClassTaggedFiniteWindowState
                  meanService i z (-older) 0))
              (stationaryPriorityClassTaggedJob meanService i z))
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z (target z)) := by
            rw [hpostTag, eval_stationaryPriorityClassTaggedFixedJobs]
            simp only [canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon]
            rw [hfutureLabels]
  calc
    (stationaryPriorityClassTaggedFixedReplayState meanService i older (target z)
        pastLabels futureLabels skeleton).eval z =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (stationaryPriorityClassTaggedFixedPostFutureState
              meanService i older pastLabels futureLabels skeleton))
          (target z)
          ((stationaryPriorityClassTaggedFixedPostFutureState
            meanService i older pastLabels futureLabels skeleton).eval z) := by
          simpa [stationaryPriorityClassTaggedFixedReplayState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (stationaryPriorityClassTaggedFixedPostFutureState
                  meanService i older pastLabels futureLabels skeleton))
              (fun _ => target z)
              (stationaryPriorityClassTaggedFixedPostFutureState meanService i older
                pastLabels futureLabels skeleton)
              skeleton.futureTerminalCompletionCount skeleton.futureTerminal z hmatchesFixed)
    _ = stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i z older (target z) := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hfuture]
          rfl

/-- The literal finite two-sided selected/Palm completion observation is
Borel.  Its random finite ledgers and service decisions are partitioned into
countably many fixed, Borel skeleton branches, each of which evaluates to the
same executable replay. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older t : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z older t).getD 0) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    List (NonpreemptivePriorityArrivalIndex n) ×
      StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      stationaryPriorityClassTaggedFiniteReplayLedgerFiber i older t q.1 q.2.1 ∩
        {z | stationaryPriorityClassTaggedFixedReplayBranchMatches
          meanService i older t q.1 q.2.1 q.2.2 z})
    ?_ ?_
    (fun z => (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z older t).getD 0)
    (fun q => stationaryPriorityClassTaggedFixedReplayResponse
      meanService i older t q.1 q.2.1 q.2.2)
    ?_ ?_
  · intro q
    exact (measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiber
      i older t q.1 q.2.1).inter
      (measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatches
        meanService i older t q.1 q.2.1 q.2.2)
  · ext z
    constructor
    · intro _
      simp
    · intro _
      let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0
      let futureLabels := canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z t
      let initial := stationaryPriorityClassTaggedFixedPastInitial i older
      let pastJobs := stationaryPriorityClassTaggedFixedJobs meanService i pastLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs z with
        ⟨pastArrivalSlots, hpastArrivals⟩
      let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter z with
        ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
      let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := []
          futureTerminalCompletionCount := 0
          futureTerminal := .hold }
      let postTag := stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton
      let futureJobs := stationaryPriorityClassTaggedFixedJobs meanService i futureLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches postTag futureJobs z with
        ⟨futureArrivalSlots, hfutureArrivals⟩
      let postFuture := runFixedPriorityArrivalTraceBranch postTag futureJobs futureArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs postFuture) (fun _ => t) postFuture z with
        ⟨futureTerminalCompletionCount, futureTerminal, hfutureTerminal⟩
      let finalSkeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := futureArrivalSlots
          futureTerminalCompletionCount := futureTerminalCompletionCount
          futureTerminal := futureTerminal }
      refine Set.mem_iUnion.mpr ⟨(pastLabels, futureLabels, finalSkeleton), ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  · intro q
    exact measurable_stationaryPriorityClassTaggedFixedReplayResponse
      meanService i older t q.1 q.2.1 q.2.2
  · intro q z hz
    rcases hz with ⟨hledger, hmatches⟩
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older t) (Sigma.mk i 0)).getD 0 =
      fixedPriorityCompletionResponse (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFixedReplayState
          meanService i older t q.1 q.2.1 q.2.2) z
    rw [fixedPriorityCompletionResponse_eq_recordedCompletionTime_getD]
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older t) (Sigma.mk i 0)).getD 0 =
      (nonpreemptivePriorityRecordedCompletionTime
        ((stationaryPriorityClassTaggedFixedReplayState
          meanService i older t q.1 q.2.1 q.2.2).eval z) (Sigma.mk i 0)).getD 0
    rw [stationaryPriorityClassTaggedFixedReplayState_eval_eq_finiteReplayState_of_matches
      meanService i older t q.1 q.2.1 q.2.2 z hledger hmatches]

/-- The literal finite selected/Palm completion observation is Borel when it
is queried at any Borel carrier-dependent right horizon. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD_at
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
        meanService i z older (target z)).getD 0) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    List (NonpreemptivePriorityArrivalIndex n) ×
      StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt i older target q.1 q.2.1 ∩
        {z | stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
          meanService i older target q.1 q.2.1 q.2.2 z})
    ?_ ?_
    (fun z => (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z older (target z)).getD 0)
    (fun q => stationaryPriorityClassTaggedFixedReplayResponseAt
      meanService i older target q.1 q.2.1 q.2.2)
    ?_ ?_
  · intro q
    exact (measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiberAt
      i older target htarget q.1 q.2.1).inter
      (measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
        meanService i older target htarget q.1 q.2.1 q.2.2)
  · ext z
    constructor
    · intro _
      simp
    · intro _
      let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0
      let futureLabels := canonicalStationaryPriorityClassTaggedFutureArrivalIndices i z (target z)
      let initial := stationaryPriorityClassTaggedFixedPastInitial i older
      let pastJobs := stationaryPriorityClassTaggedFixedJobs meanService i pastLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs z with
        ⟨pastArrivalSlots, hpastArrivals⟩
      let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter z with
        ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
      let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := []
          futureTerminalCompletionCount := 0
          futureTerminal := .hold }
      let postTag := stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton
      let futureJobs := stationaryPriorityClassTaggedFixedJobs meanService i futureLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches postTag futureJobs z with
        ⟨futureArrivalSlots, hfutureArrivals⟩
      let postFuture := runFixedPriorityArrivalTraceBranch postTag futureJobs futureArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs postFuture) target postFuture z with
        ⟨futureTerminalCompletionCount, futureTerminal, hfutureTerminal⟩
      let finalSkeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := futureArrivalSlots
          futureTerminalCompletionCount := futureTerminalCompletionCount
          futureTerminal := futureTerminal }
      refine Set.mem_iUnion.mpr ⟨(pastLabels, futureLabels, finalSkeleton), ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  · intro q
    exact measurable_stationaryPriorityClassTaggedFixedReplayResponseAt
      meanService i older target htarget q.1 q.2.1 q.2.2
  · intro q z hz
    rcases hz with ⟨hledger, hmatches⟩
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older (target z)) (Sigma.mk i 0)).getD 0 =
      fixedPriorityCompletionResponse (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFixedReplayStateAt
          meanService i older target q.1 q.2.1 q.2.2) z
    rw [fixedPriorityCompletionResponse_eq_recordedCompletionTime_getD]
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState
        meanService i z older (target z)) (Sigma.mk i 0)).getD 0 =
      (nonpreemptivePriorityRecordedCompletionTime
        ((stationaryPriorityClassTaggedFixedReplayStateAt
          meanService i older target q.1 q.2.1 q.2.2).eval z) (Sigma.mk i 0)).getD 0
    rw [stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_finiteReplayState_of_matches
      meanService i older target q.1 q.2.1 q.2.2 z hledger hmatches]

/-- The strict-past finite selected replay has a Borel completion observation
at every Borel sample-dependent right horizon. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_at
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older (target z)).getD 0) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    List (NonpreemptivePriorityArrivalIndex n) ×
      StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
        i older target q.1 q.2.1 ∩
        {z | stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
          meanService i older target q.1 q.2.1 q.2.2 z})
    ?_ ?_
    (fun z => (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older (target z)).getD 0)
    (fun q => stationaryPriorityClassTaggedFixedReplayResponseAt
      meanService i older target q.1 q.2.1 q.2.2)
    ?_ ?_
  · intro q
    exact (measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
      i older target htarget q.1 q.2.1).inter
      (measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
        meanService i older target htarget q.1 q.2.1 q.2.2)
  · ext z
    constructor
    · intro _
      simp
    · intro _
      let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0
      let futureLabels := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (target z)
      let initial := stationaryPriorityClassTaggedFixedPastInitial i older
      let pastJobs := stationaryPriorityClassTaggedFixedJobs meanService i pastLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs z with
        ⟨pastArrivalSlots, hpastArrivals⟩
      let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter z with
        ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
      let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := []
          futureTerminalCompletionCount := 0
          futureTerminal := .hold }
      let postTag := stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton
      let futureJobs := stationaryPriorityClassTaggedFixedJobs meanService i futureLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches postTag futureJobs z with
        ⟨futureArrivalSlots, hfutureArrivals⟩
      let postFuture := runFixedPriorityArrivalTraceBranch postTag futureJobs futureArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs postFuture) target postFuture z with
        ⟨futureTerminalCompletionCount, futureTerminal, hfutureTerminal⟩
      let finalSkeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := futureArrivalSlots
          futureTerminalCompletionCount := futureTerminalCompletionCount
          futureTerminal := futureTerminal }
      refine Set.mem_iUnion.mpr ⟨(pastLabels, futureLabels, finalSkeleton), ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  · intro q
    exact measurable_stationaryPriorityClassTaggedFixedReplayResponseAt
      meanService i older target htarget q.1 q.2.1 q.2.2
  · intro q z hz
    rcases hz with ⟨hledger, hmatches⟩
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older (target z)) (Sigma.mk i 0)).getD 0 =
      fixedPriorityCompletionResponse (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFixedReplayStateAt
          meanService i older target q.1 q.2.1 q.2.2) z
    rw [fixedPriorityCompletionResponse_eq_recordedCompletionTime_getD]
    change (nonpreemptivePriorityRecordedCompletionTime
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older (target z)) (Sigma.mk i 0)).getD 0 =
      (nonpreemptivePriorityRecordedCompletionTime
        ((stationaryPriorityClassTaggedFixedReplayStateAt
          meanService i older target q.1 q.2.1 q.2.2).eval z) (Sigma.mk i 0)).getD 0
    rw [stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_finiteReplayStateBeforeHorizon_of_matches
      meanService i older target q.1 q.2.1 q.2.2 z hledger hmatches]

/-- A finite selected-customer completion observation at any fixed labelled
arrival epoch is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD_atArrival
    {n : ℕ} (meanService : Fin n → ℝ) (i j : Fin n) (k : ℤ) (older : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime meanService i z older
        (stationaryPriorityClassTaggedArrival i z j k)).getD 0) := by
  apply measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD_at
    meanService i older
  exact measurable_stationaryPriorityClassTaggedArrival i j k

/-- The strict-past finite replay has a Borel completion observation at every
fixed labelled arrival epoch. -/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_atArrival
    {n : ℕ} (meanService : Fin n → ℝ) (i j : Fin n) (k : ℤ) (older : ℝ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z older (stationaryPriorityClassTaggedArrival i z j k)).getD 0) := by
  apply measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_at
    meanService i older
  exact measurable_stationaryPriorityClassTaggedArrival i j k

/-- Under strict total load, the canonical selected-customer stationary
response is almost everywhere measurable under its concrete multiclass Palm
law.  This no longer needs a finite-replay measurability certificate. -/
theorem aemeasurable_stationaryPriorityClassTaggedResponseTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  apply aemeasurable_stationaryPriorityClassTaggedResponseTime_of_measurable_finiteReplays
    arrivalRate meanService harrivalRate hmeanService hstable i
  intro horizon
  exact measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD
    meanService i (horizon : ℝ) (horizon : ℝ)

/-- The canonical selected response is Borel: it is the pointwise limsup of
the total Borel finite replay responses used in its definition.  Almost-sure
stabilization supplies its queueing semantics, but is not needed for this
measurability fact. -/
theorem measurable_stationaryPriorityClassTaggedResponseTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedResponseTime meanService i) := by
  unfold stationaryPriorityClassTaggedResponseTime
  apply Probability.measurable_stabilizedFiniteReplayResponse
  intro horizon
  exact measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD
    meanService i (horizon : ℝ) (horizon : ℝ)

/-- The literal tagged queue-wait observable is almost everywhere measurable
under the selected Palm law.  Its service-mark term has a concrete
exponential-law construction, while its response term is supplied by the
finite-replay Borel argument above. -/
theorem aemeasurable_stationaryPriorityClassTaggedQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedQueueWait meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  exact (aemeasurable_stationaryPriorityClassTaggedResponseTime
    arrivalRate meanService harrivalRate hmeanService hstable i).sub
      (stationaryPriorityClassTaggedWorkRequirement_hasLaw
        arrivalRate meanService harrivalRate hmeanService i).aemeasurable

/-- The literal selected queue-wait observable is Borel as the difference
between its canonical Borel response and its Borel service requirement. -/
theorem measurable_stationaryPriorityClassTaggedQueueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedQueueWait meanService i) := by
  exact (measurable_stationaryPriorityClassTaggedResponseTime meanService i).sub
    (measurable_stationaryPriorityClassTaggedWorkRequirement meanService i)

/-- For a passive class, its literal work arriving before the selected
customer's completion time is almost-everywhere measurable under the
concrete Palm input law.  This records only the random-horizon input ledger;
identifying which arrivals are served before that completion is a separate
pathwise priority argument. -/
theorem aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_at_response
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i j : Fin n) (hji : j ≠ i) :
    AEMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j
        (stationaryPriorityClassTaggedResponseTime meanService i z))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  apply aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_comp
    meanService i j hji
  exact aemeasurable_stationaryPriorityClassTaggedResponseTime
    arrivalRate meanService harrivalRate hmeanService hstable i

/-- The passive future-work ledger is likewise almost-everywhere measurable
at the selected customer's queue-wait horizon.  This is the input observable
whose pathwise priority identification is needed for the strictly
higher-priority overtaking term. -/
theorem aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_at_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i j : Fin n) (hji : j ≠ i) :
    AEMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j
        (stationaryPriorityClassTaggedQueueWait meanService i z))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  apply aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_comp
    meanService i j hji
  exact aemeasurable_stationaryPriorityClassTaggedQueueWait
    arrivalRate meanService harrivalRate hmeanService hstable i

/-- Total literal work of strictly higher-priority passive classes in the
right-closed interval from the Palm origin through the tagged customer's
queue-wait horizon.  This is an input-ledger observable; a separate
pathwise service-accounting proof identifies its role in the priority
workload decomposition. -/
noncomputable def stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j < i),
    stationaryPriorityTaggedFutureWorkAggregate meanService i z j
      (stationaryPriorityClassTaggedQueueWait meanService i z)

/-- The finite strict-priority future-work aggregate at the tagged queue-wait
horizon is Palm almost-everywhere measurable. -/
theorem aemeasurable_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  unfold stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
  apply Finset.aemeasurable_fun_sum
  intro j hj
  exact aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_at_queueWait
    arrivalRate meanService harrivalRate hmeanService hstable i j
      (ne_of_lt (Finset.mem_filter.mp hj).2)

/-- Under the concrete positive exponential-mark law, the strict-priority
future-work aggregate at the tagged queue-wait horizon is nonnegative almost
everywhere.  This supplies the nonnegative side of the extended-expectation
formulation before its finiteness is proved. -/
theorem ae_nonneg_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 ≤ stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hpositive
  unfold stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
  apply Finset.sum_nonneg
  intro j hj
  exact stationaryPriorityTaggedFutureWorkAggregate_nonneg meanService i z j
    (stationaryPriorityClassTaggedQueueWait meanService i z)
    (fun k => (hpositive j k).le)

/-- Integrability of the literal tagged response immediately yields
integrability of its queue-wait observable, since the tagged service mark has
the concrete exponential integrability proof. -/
theorem integrable_stationaryPriorityClassTaggedQueueWait_of_response
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n)
    (hresponse : Integrable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) :
    Integrable (stationaryPriorityClassTaggedQueueWait meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  exact hresponse.sub (integrable_stationaryPriorityClassTaggedWorkRequirement
    arrivalRate meanService harrivalRate hmeanService i)

/-- Once the concrete tagged response has been proved integrable, the Palm
mean queue wait is its mean response minus the prescribed mean service time. -/
theorem integral_stationaryPriorityClassTaggedQueueWait_of_response
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n)
    (hresponse : Integrable (stationaryPriorityClassTaggedResponseTime meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) :
    ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, stationaryPriorityClassTaggedResponseTime meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) - meanService i := by
  unfold stationaryPriorityClassTaggedQueueWait
  rw [integral_sub hresponse
    (integrable_stationaryPriorityClassTaggedWorkRequirement
      arrivalRate meanService harrivalRate hmeanService i),
    integral_stationaryPriorityClassTaggedWorkRequirement
      arrivalRate meanService harrivalRate hmeanService i]

end

end AppliedModelingLib.Queueing
