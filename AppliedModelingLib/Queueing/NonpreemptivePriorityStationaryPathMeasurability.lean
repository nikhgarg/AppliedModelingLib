import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceSkeleton
import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting
import Mathlib.Tactic

/-!
# Joint measurability of finite stationary priority paths

This module begins the product-time measurable-cover construction for literal
finite nonpreemptive-priority replays.  The terminal time is a coordinate of
the sample rather than a fixed parameter, so its countable ledger fibers can
later support Fubini and stationary-occupation arguments.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

variable {n : ℕ}

/-- A fixed labelled stationary arrival, viewed as a coordinate job over the
product of a physical observation time and the marked input path. -/
def stationaryPriorityTimePathFixedJobCoordinate
    (meanService : Fin n → ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    NonpreemptivePriorityFixedJobCoordinate
      (ℝ × (Fin n → StationaryPoissonWorkPath))
      n (NonpreemptivePriorityArrivalIndex n) :=
  { identifier := q
    priority := q.1
    arrivalTime := fun p =>
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 p.2 q.2
    serviceWork := fun p => stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 }

/-- Static coordinate jobs associated with one fixed chronological stationary
arrival ledger. -/
def stationaryPriorityTimePathFixedJobs
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    List (NonpreemptivePriorityFixedJobCoordinate
      (ℝ × (Fin n → StationaryPoissonWorkPath))
      n (NonpreemptivePriorityArrivalIndex n)) :=
  labels.map (stationaryPriorityTimePathFixedJobCoordinate meanService)

/-- A countable terminal skeleton for a finite replay with a variable
physical observation time. -/
structure StationaryPriorityTimePathFixedReplaySkeleton where
  arrivalSlots : List NonpreemptivePriorityFixedArrivalTraceSlot
  terminalCompletionCount : ℕ
  terminal : NonpreemptivePriorityFixedAdvanceTerminal
  deriving Countable

/-- The empty coordinate state at a fixed left endpoint. -/
def stationaryPriorityTimePathFixedInitial (a : ℝ) :
    NonpreemptivePriorityFixedStateCoordinate
      (ℝ × (Fin n → StationaryPoissonWorkPath))
      n (NonpreemptivePriorityArrivalIndex n) :=
  emptyNonpreemptivePriorityFixedStateCoordinate (fun _ => a)

/-- The static state obtained after replaying one fixed arrival skeleton. -/
noncomputable def stationaryPriorityTimePathFixedAfterArrivals
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton) :=
  runFixedPriorityArrivalTraceBranch
    (stationaryPriorityTimePathFixedInitial a)
    (stationaryPriorityTimePathFixedJobs meanService labels)
    skeleton.arrivalSlots

/-- The static terminal state obtained by advancing a fixed finite replay to
the product-time coordinate. -/
noncomputable def stationaryPriorityTimePathFixedState
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton) :=
  runFixedPriorityAdvanceBranch (fun p => p.1)
    (stationaryPriorityTimePathFixedAfterArrivals meanService a labels skeleton)
    skeleton.terminalCompletionCount skeleton.terminal

/-- Fixed labelled stationary arrivals have Borel coordinates on the
time-path product. -/
theorem stationaryPriorityTimePathFixedJobCoordinate_coordinatesMeasurable
    (meanService : Fin n → ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    (stationaryPriorityTimePathFixedJobCoordinate meanService q).CoordinatesMeasurable := by
  constructor
  · exact (measurable_stationaryPriorityArrivalTime q).comp measurable_snd
  · change Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      meanService q.1 * (p.2 q.1).2 q.2)
    exact measurable_const.mul
      ((measurable_pi_apply q.2).comp
        (measurable_snd.comp
          ((measurable_pi_apply q.1).comp measurable_snd)))

/-- Every static stationary time-path job ledger has Borel coordinates. -/
theorem stationaryPriorityTimePathFixedJobs_coordinatesMeasurable
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    ∀ job ∈ stationaryPriorityTimePathFixedJobs meanService labels,
      job.CoordinatesMeasurable := by
  intro job hjob
  rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
  exact stationaryPriorityTimePathFixedJobCoordinate_coordinatesMeasurable meanService q

/-- Evaluating a static time-path job ledger yields the literal stationary
job coordinates in the prescribed list order. -/
theorem eval_stationaryPriorityTimePathFixedJobs
    (meanService : Fin n → ℝ) (labels : List (NonpreemptivePriorityArrivalIndex n))
    (p : ℝ × (Fin n → StationaryPoissonWorkPath)) :
    ((stationaryPriorityTimePathFixedJobs meanService labels).map fun job => job.eval p) =
      labels.map (fun q => stationaryPriorityArrivalJobCoordinate meanService q p.2) := by
  simp [stationaryPriorityTimePathFixedJobs,
    stationaryPriorityTimePathFixedJobCoordinate,
    NonpreemptivePriorityFixedJobCoordinate.eval,
    stationaryPriorityArrivalJobCoordinate,
    stationaryPriorityWorkRequirement]

/-- Fixed time-path replay states have Borel real coordinates. -/
theorem stationaryPriorityTimePathFixedState_coordinatesMeasurable
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton) :
    (stationaryPriorityTimePathFixedState meanService a labels skeleton).CoordinatesMeasurable := by
  have hinitial : (stationaryPriorityTimePathFixedInitial (n := n) a).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hjobs := stationaryPriorityTimePathFixedJobs_coordinatesMeasurable meanService labels
  have hafter : (stationaryPriorityTimePathFixedAfterArrivals
      meanService a labels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityTimePathFixedInitial a) hinitial
      (stationaryPriorityTimePathFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs
  exact coordinatesMeasurable_runFixedPriorityAdvanceBranch (fun p => p.1) measurable_fst
    _ hafter skeleton.terminalCompletionCount skeleton.terminal

/-- The Borel predicate selecting one fixed finite replay branch on the
time-path product. -/
def stationaryPriorityTimePathFixedBranchMatches
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton)
    (p : ℝ × (Fin n → StationaryPoissonWorkPath)) : Prop :=
  fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityTimePathFixedInitial a)
      (stationaryPriorityTimePathFixedJobs meanService labels)
      skeleton.arrivalSlots p ∧
    fixedPriorityAdvanceBranchMatches
      (totalFixedNonpreemptivePriorityWorkJobs
        (stationaryPriorityTimePathFixedAfterArrivals meanService a labels skeleton))
      (fun p => p.1)
      (stationaryPriorityTimePathFixedAfterArrivals meanService a labels skeleton)
      skeleton.terminalCompletionCount skeleton.terminal p

/-- Each fixed finite time-path replay branch is Borel. -/
theorem measurableSet_stationaryPriorityTimePathFixedBranchMatches
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton) :
    MeasurableSet {p |
      stationaryPriorityTimePathFixedBranchMatches meanService a labels skeleton p} := by
  have hinitial : (stationaryPriorityTimePathFixedInitial (n := n) a).CoordinatesMeasurable :=
    emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable _ measurable_const
  have hjobs := stationaryPriorityTimePathFixedJobs_coordinatesMeasurable meanService labels
  have hafter : (stationaryPriorityTimePathFixedAfterArrivals
      meanService a labels skeleton).CoordinatesMeasurable :=
    coordinatesMeasurable_runFixedPriorityArrivalTraceBranch
      (stationaryPriorityTimePathFixedInitial a) hinitial
      (stationaryPriorityTimePathFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs
  convert (measurableSet_fixedPriorityArrivalTraceBranchMatches
      (stationaryPriorityTimePathFixedInitial a) hinitial
      (stationaryPriorityTimePathFixedJobs meanService labels)
      skeleton.arrivalSlots hjobs).inter
      (measurableSet_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs
          (stationaryPriorityTimePathFixedAfterArrivals meanService a labels skeleton))
        (fun p => p.1) measurable_fst
        _ hafter skeleton.terminalCompletionCount skeleton.terminal) using 1

/-- On a matching fixed branch, the coordinate replay evaluates to the
literal finite stationary-input state at the product-time observation epoch. -/
theorem stationaryPriorityTimePathFixedState_eval_eq_windowState_of_matches
    (meanService : Fin n → ℝ) (a : ℝ)
    (labels : List (NonpreemptivePriorityArrivalIndex n))
    (skeleton : StationaryPriorityTimePathFixedReplaySkeleton)
    (p : ℝ × (Fin n → StationaryPoissonWorkPath))
    (hledger : canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1 = labels)
    (hmatches : stationaryPriorityTimePathFixedBranchMatches
      meanService a labels skeleton p) :
    (stationaryPriorityTimePathFixedState meanService a labels skeleton).eval p =
      stationaryPriorityFiniteWindowState meanService p.2 a p.1 := by
  rcases hmatches with ⟨harrivals, hterminal⟩
  have hafter :
      (stationaryPriorityTimePathFixedAfterArrivals
        meanService a labels skeleton).eval p =
        runNonpreemptivePriorityArrivalTrace
          (emptyNonpreemptivePriorityWorkState
            (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a)
          (stationaryPriorityArrivalWindowJobs meanService p.2 a p.1) := by
    calc
      (stationaryPriorityTimePathFixedAfterArrivals
          meanService a labels skeleton).eval p =
          runNonpreemptivePriorityArrivalTrace
            ((stationaryPriorityTimePathFixedInitial a).eval p)
            ((stationaryPriorityTimePathFixedJobs meanService labels).map
              fun job => job.eval p) := by
            simpa [stationaryPriorityTimePathFixedAfterArrivals] using
              (eval_runFixedPriorityArrivalTraceBranch_eq_run_of_matches
                (stationaryPriorityTimePathFixedInitial a)
                (stationaryPriorityTimePathFixedJobs meanService labels)
                skeleton.arrivalSlots p harrivals)
      _ = runNonpreemptivePriorityArrivalTrace
            (emptyNonpreemptivePriorityWorkState
              (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a)
            (stationaryPriorityArrivalWindowJobs meanService p.2 a p.1) := by
            rw [eval_stationaryPriorityTimePathFixedJobs]
            simp only [stationaryPriorityTimePathFixedInitial,
              emptyNonpreemptivePriorityFixedStateCoordinate_eval,
              stationaryPriorityArrivalWindowJobs,
              canonicalStationaryPriorityArrivalWindowJobs]
            rw [hledger]
            rfl
  calc
    (stationaryPriorityTimePathFixedState meanService a labels skeleton).eval p =
        advanceNonpreemptivePriorityWorkState
          (totalFixedNonpreemptivePriorityWorkJobs
            (stationaryPriorityTimePathFixedAfterArrivals
              meanService a labels skeleton))
          p.1
          ((stationaryPriorityTimePathFixedAfterArrivals
            meanService a labels skeleton).eval p) := by
          simpa [stationaryPriorityTimePathFixedState] using
            (eval_runFixedPriorityAdvanceBranch_eq_advance_of_matches
              (totalFixedNonpreemptivePriorityWorkJobs
                (stationaryPriorityTimePathFixedAfterArrivals
                  meanService a labels skeleton))
              (fun p => p.1)
              (stationaryPriorityTimePathFixedAfterArrivals
                meanService a labels skeleton)
              skeleton.terminalCompletionCount skeleton.terminal p hterminal)
    _ = stationaryPriorityFiniteWindowState meanService p.2 a p.1 := by
          rw [← totalNonpreemptivePriorityWorkJobs_fixedState_eval, hafter]
          rfl

/-- Membership of a fixed stationary arrival label in the half-open window
with a fixed left endpoint and sample-dependent right endpoint is Borel on
the product of physical time and the marked input path. -/
theorem measurableSet_mem_stationaryPriorityArrivalWindowIndices_uncurry
    {n : ℕ} (a : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      q.2 ∈ stationaryPriorityArrivalWindowIndices p.2 a p.1 q.1} := by
  change MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      q.2 ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a p.1 (p.2 q.1).1}
  apply measurableSet_setOf.mpr
  have harrival : Measurable (fun p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) =>
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival q.1 p.2 q.2) := by
    exact (measurable_stationaryPriorityArrivalTime q).comp measurable_snd
  simpa only [Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff] using
    ((measurable_const.le' harrival).and (harrival.lt measurable_fst))

/-- Every finite labelled stationary arrival set is a Borel fiber when the
window's right endpoint is the physical-time coordinate. -/
theorem measurableSet_stationaryPriorityArrivalWindowLedger_eq_uncurry
    {n : ℕ} (a : ℝ) (labels : Finset (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices p.2 a p.1) = labels} := by
  classical
  have hmem : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {p : ℝ × (Fin n →
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices p.2 a p.1)} := by
    intro q
    simpa [nonpreemptivePriorityArrivalWindowIndices] using
      measurableSet_mem_stationaryPriorityArrivalWindowIndices_uncurry a q
  have hfiber : ∀ q : NonpreemptivePriorityArrivalIndex n,
      MeasurableSet {p : ℝ × (Fin n →
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices p.2 a p.1) ↔ q ∈ labels} := by
    intro q
    by_cases hq : q ∈ labels
    · simpa [hq] using hmem q
    · have hnot : MeasurableSet {p : ℝ × (Fin n →
          (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
          q ∉ nonpreemptivePriorityArrivalWindowIndices
            (stationaryPriorityArrivalWindowIndices p.2 a p.1)} := by
          convert (hmem q).compl using 1
      simpa [hq] using hnot
  have heq : {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices p.2 a p.1) = labels} =
      ⋂ q : NonpreemptivePriorityArrivalIndex n, {p |
        q ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices p.2 a p.1) ↔ q ∈ labels} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hledger q
      simpa [hledger]
    · intro hledger
      ext q
      exact hledger q
  rw [heq]
  exact MeasurableSet.iInter hfiber

/-- The canonical chronological ledger has a Borel fiber when its right
endpoint is the physical-time coordinate.  In addition to the finite ledger
membership, the fiber records the finitely many arrival-time comparisons that
fix its deterministic canonical order. -/
theorem measurableSet_canonicalStationaryPriorityArrivalWindowIndices_eq_uncurry
    {n : ℕ} (a : ℝ) (labels : List (NonpreemptivePriorityArrivalIndex n)) :
    MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1 = labels} := by
  classical
  have hledger := measurableSet_stationaryPriorityArrivalWindowLedger_eq_uncurry
    a labels.toFinset
  have hpairwise : MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      labels.Pairwise (stationaryPriorityArrivalIndexLE p.2)} := by
    exact (measurableSet_stationaryPriorityArrivalIndexList_pairwise labels).preimage
      measurable_snd
  have hnodup : MeasurableSet {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) | labels.Nodup} := by
    by_cases hlabels : labels.Nodup <;> simp [hlabels]
  have heq : {p : ℝ × (Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) |
      canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1 = labels} =
      ({p | nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices p.2 a p.1) = labels.toFinset} ∩
        {p | labels.Pairwise (stationaryPriorityArrivalIndexLE p.2)}) ∩
          {p | labels.Nodup} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hcanonical
      letI : DecidableRel (stationaryPriorityArrivalIndexLE p.2) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans p.2⟩
      letI : Std.Antisymm (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm p.2⟩
      letI : Std.Total (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨stationaryPriorityArrivalIndexLE_total p.2⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have htoFinset :
          (canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1).toFinset =
            nonpreemptivePriorityArrivalWindowIndices
              (stationaryPriorityArrivalWindowIndices p.2 a p.1) := by
            exact Finset.sort_toFinset _ _
        rw [hcanonical] at htoFinset
        exact htoFinset.symm
      · rw [← hcanonical]
        exact pairwise_stationaryPriorityArrivalIndexLE_canonicalWindowIndices p.2 a p.1
      · rw [← hcanonical]
        exact Finset.sort_nodup _ _
    · rintro ⟨⟨hledger, hpairwise⟩, hnodup⟩
      letI : DecidableRel (stationaryPriorityArrivalIndexLE p.2) := Classical.decRel _
      letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
          (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans p.2⟩
      letI : Std.Antisymm (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm p.2⟩
      letI : Std.Total (stationaryPriorityArrivalIndexLE p.2) :=
        ⟨stationaryPriorityArrivalIndexLE_total p.2⟩
      change (nonpreemptivePriorityArrivalWindowIndices
        (stationaryPriorityArrivalWindowIndices p.2 a p.1)).sort
          (stationaryPriorityArrivalIndexLE p.2) = labels
      rw [hledger]
      exact (List.toFinset_sort (r := stationaryPriorityArrivalIndexLE p.2) hnodup).mpr
        hpairwise
  rw [heq]
  exact (hledger.inter hpairwise).inter hnodup

/-- A real observable of a literal stationary finite replay is Borel on the
time-path product whenever it is Borel on every fixed replay coordinate. -/
theorem measurable_uncurry_stationaryPriorityFiniteWindowState_component
    (meanService : Fin n → ℝ) (a : ℝ)
    (F : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) → ℝ)
    (hF : ∀ state : NonpreemptivePriorityFixedStateCoordinate
        (ℝ × (Fin n → StationaryPoissonWorkPath))
        n (NonpreemptivePriorityArrivalIndex n),
        state.CoordinatesMeasurable → Measurable (fun p => F (state.eval p))) :
    Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      F (stationaryPriorityFiniteWindowState meanService p.2 a p.1)) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    StationaryPriorityTimePathFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      {p | canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1 = q.1} ∩
        {p | stationaryPriorityTimePathFixedBranchMatches
          meanService a q.1 q.2 p})
    ?_ ?_
    (fun p => F (stationaryPriorityFiniteWindowState meanService p.2 a p.1))
    (fun q p => F ((stationaryPriorityTimePathFixedState
      meanService a q.1 q.2).eval p))
    ?_ ?_
  · intro q
    exact (measurableSet_canonicalStationaryPriorityArrivalWindowIndices_eq_uncurry a q.1).inter
      (measurableSet_stationaryPriorityTimePathFixedBranchMatches
        meanService a q.1 q.2)
  · ext p
    constructor
    · intro _
      simp
    · intro _
      let labels := canonicalStationaryPriorityArrivalWindowIndices p.2 a p.1
      let initial := stationaryPriorityTimePathFixedInitial (n := n) a
      let jobs := stationaryPriorityTimePathFixedJobs meanService labels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial jobs p with
        ⟨arrivalSlots, harrivals⟩
      let afterArrivals := runFixedPriorityArrivalTraceBranch initial jobs arrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs afterArrivals) (fun p => p.1) afterArrivals p with
        ⟨terminalCompletionCount, terminal, hterminal⟩
      let skeleton : StationaryPriorityTimePathFixedReplaySkeleton :=
        { arrivalSlots := arrivalSlots
          terminalCompletionCount := terminalCompletionCount
          terminal := terminal }
      refine Set.mem_iUnion.mpr ⟨(labels, skeleton), ?_⟩
      exact ⟨rfl, ⟨harrivals, hterminal⟩⟩
  · intro q
    exact hF (stationaryPriorityTimePathFixedState meanService a q.1 q.2)
      (stationaryPriorityTimePathFixedState_coordinatesMeasurable
        meanService a q.1 q.2)
  · intro q p hz
    rcases hz with ⟨hledger, hmatches⟩
    exact congrArg F
      (stationaryPriorityTimePathFixedState_eval_eq_windowState_of_matches
        meanService a q.1 q.2 p hledger hmatches).symm

/-- The active residual work in a literal stationary finite replay is jointly
Borel in physical time and the marked input path. -/
theorem measurable_uncurry_stationaryPriorityFiniteWindowActiveResidualWork
    (meanService : Fin n → ℝ) (a : ℝ) :
    Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService p.2 a p.1)) := by
  apply measurable_uncurry_stationaryPriorityFiniteWindowState_component
    meanService a activeNonpreemptivePriorityResidualWork
  intro state hstate
  exact measurable_activeNonpreemptivePriorityResidualWork_fixedState_eval state hstate

/-- The squared residual-work ledger in a literal stationary finite replay is
jointly Borel in physical time and the marked input path. -/
theorem measurable_uncurry_stationaryPriorityFiniteWindowSquaredResidualWork
    (meanService : Fin n → ℝ) (a : ℝ) :
    Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService p.2 a p.1)) := by
  apply measurable_uncurry_stationaryPriorityFiniteWindowState_component
    meanService a totalNonpreemptivePrioritySquaredResidualWork
  intro state hstate
  exact measurable_totalNonpreemptivePrioritySquaredResidualWork_fixedState_eval state hstate

/-- The waiting work in classes at least as urgent as `i` of a literal
stationary finite replay is jointly Borel in time and input. -/
theorem measurable_uncurry_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork
    (meanService : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService p.2 a p.1) i) := by
  apply measurable_uncurry_stationaryPriorityFiniteWindowState_component
    meanService a (fun state => priorityWaitingResidualWorkAtLeastAsUrgent state i)
  intro state hstate
  exact measurable_priorityWaitingResidualWorkAtLeastAsUrgent_fixedState_eval state hstate i

/-- The work-weighted FIFO contribution of one fixed labelled customer is
jointly Borel in the physical observation time and the stationary marked
input.  This is the customer-level measurable surface needed to integrate a
finite waiting ledger term by term. -/
theorem measurable_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution
    (meanService : Fin n → ℝ) (a : ℝ)
    (q : NonpreemptivePriorityArrivalIndex n) :
    Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityFiniteWindowState meanService p.2 a p.1)) := by
  apply Measurable.mul
  · change Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      meanService q.1 * (p.2 q.1).2 q.2)
    exact measurable_const.mul
      ((measurable_pi_apply q.2).comp
        (measurable_snd.comp ((measurable_pi_apply q.1).comp measurable_snd)))
  · apply measurable_uncurry_stationaryPriorityFiniteWindowState_component
      meanService a
      (fun state => nonpreemptivePriorityWaitingIdentifierIndicator q state)
    intro state hstate
    convert measurable_fixedNonpreemptivePriorityWaitingIdentifierIndicator q state using 1
    funext p
    exact (fixedNonpreemptivePriorityWaitingIdentifierIndicator_eval q state p).symm

/-- On every bounded physical interval, one fixed customer's work-weighted
FIFO contribution to a finite stationary replay is integrable. -/
theorem intervalIntegrable_stationaryPriorityFiniteWindowWaitingIdentifierContribution
    (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left a b : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    IntervalIntegrable (fun time =>
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityFiniteWindowState meanService omega left time))
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  let contribution : ℝ → ℝ := fun time =>
    stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityFiniteWindowState meanService omega left time)
  let work : ℝ := stationaryPriorityWorkRequirement meanService q.1 omega q.2
  have hmeasurable : Measurable contribution := by
    simpa [contribution] using
      (measurable_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution
        meanService left q).comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => omega)))
  have hmeas : AEStronglyMeasurable contribution
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    hmeasurable.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ time ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      ‖contribution time‖ ≤ ‖work‖ := by
    filter_upwards with time
    unfold contribution nonpreemptivePriorityWaitingIdentifierIndicator
    split_ifs <;> simp [work]
  have hconst : Integrable (fun _ : ℝ => ‖work‖)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    exact (MeasureTheory.integrableOn_const
      (s := Set.uIoc a b) (by
        rw [Real.volume_uIoc]
        exact ENNReal.ofReal_ne_top)).integrable
  exact MeasureTheory.Integrable.mono' hconst hmeas hbound

end

end AppliedModelingLib.Queueing
