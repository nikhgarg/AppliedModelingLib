import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateCompression
import Mathlib.Tactic

/-!
# Semantic projection of a GPS segment trace to one selected class

An executable GPS trace has endpoints that are irrelevant as arrivals for a
chosen class: internal depletion endpoints and external endpoints carrying
only other classes' work.  They cannot be discarded, because their durations
are real service intervals.  This file gives a source-agnostic projection
interface that groups each such zero-batch block with the next retained
selected-class endpoint, while retaining a final zero-batch block as a
service-only suffix.

The API does not inspect event names, source labels, or scheduler booleans.
An application supplies a semantic partition of a concrete segment list and
then identifies each retained endpoint and each block duration from its own
source model.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- One retained selected-class endpoint together with every preceding
consecutive segment whose selected endpoint batch is zero.  The retained
segment's own duration remains before its endpoint batch, as required by the
service-before-endpoint convention. -/
structure FiniteGPSConstantRateProjectionBlock (Class : Type*) where
  zeroPrefix : List (FiniteGPSExecutionSegment Class)
  retained : FiniteGPSExecutionSegment Class

/-- The original concrete segment sublist represented by one projected
endpoint block. -/
def finiteGPSConstantRateProjectionBlockSegments
    (block : FiniteGPSConstantRateProjectionBlock Class) :
    List (FiniteGPSExecutionSegment Class) :=
  block.zeroPrefix ++ [block.retained]

/-- The total elapsed time before the retained endpoint in a projected
block.  It includes the retained segment itself. -/
def finiteGPSConstantRateProjectionBlockDuration
    (block : FiniteGPSConstantRateProjectionBlock Class) : Real :=
  finiteGPSExecutionSegmentsTotalDuration block.zeroPrefix +
    block.retained.duration

/-- Expand projected retained endpoints back to their concrete segment
blocks, and append the final selected-class-zero service suffix.  The suffix
is deliberately a list of concrete segments rather than a fabricated source
endpoint. -/
def finiteGPSConstantRateProjectionSegments
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class)) :
    List (FiniteGPSExecutionSegment Class) :=
  blocks.flatMap finiteGPSConstantRateProjectionBlockSegments ++ terminalZero

/-- The scalar service-before-endpoint recursion after semantic projection.
The terminal zero block is retained as one final reflected service update,
not deleted and not converted into an external batch. -/
def finiteGPSConstantRateProjectionComparatorFrom
    (initial rate : Real) (i : Class) :
    List (FiniteGPSConstantRateProjectionBlock Class) ->
      List (FiniteGPSExecutionSegment Class) -> Real
  | [], terminalZero =>
      lateBatchUpdate initial
        (rate * finiteGPSExecutionSegmentsTotalDuration terminalZero) 0
  | block :: blocks, terminalZero =>
      finiteGPSConstantRateProjectionComparatorFrom
        (lateBatchUpdate initial
          (rate * finiteGPSConstantRateProjectionBlockDuration block)
          (block.retained.endpointBatch i))
        rate i blocks terminalZero

/-- One source-agnostic scalar service-before-batch event.  This is the
semantic interface between a projected GPS ledger and a Lindley-style finite
replay: an application can identify these events with any chronological
arrival sequence without exposing source event constructors to the generic
algebra. -/
structure LateBatchReplayStep where
  service : Real
  batch : Real

/-- Replay a finite chronological scalar service-before-batch ledger. -/
def lateBatchReplayFrom (initial : Real) : List LateBatchReplayStep -> Real
  | [] => initial
  | step :: steps =>
      lateBatchReplayFrom
        (lateBatchUpdate initial step.service step.batch) steps

/-- The retained-endpoint portion of a semantic GPS projection as a scalar
service-before-batch ledger.  Each projection block contributes its complete
elapsed duration before its retained endpoint batch. -/
def finiteGPSConstantRateProjectionRetainedReplaySteps
    (rate : Real) (i : Class)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class)) :
    List LateBatchReplayStep :=
  blocks.map fun block =>
    { service := rate * finiteGPSConstantRateProjectionBlockDuration block
      batch := block.retained.endpointBatch i }

/-- The final selected-class-zero segment suffix as a final scalar reflected
service event.  It is an endpoint-free computational/service suffix rather
than a fabricated source arrival. -/
def finiteGPSConstantRateProjectionTerminalReplayStep
    (rate : Real)
    (terminalZero : List (FiniteGPSExecutionSegment Class)) : LateBatchReplayStep :=
  { service := rate * finiteGPSExecutionSegmentsTotalDuration terminalZero
    batch := 0 }

/-- The complete finite scalar replay represented by a semantic projection.
The last event records the terminal zero-batch service suffix explicitly. -/
def finiteGPSConstantRateProjectionReplaySteps
    (rate : Real) (i : Class)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class)) :
    List LateBatchReplayStep :=
  finiteGPSConstantRateProjectionRetainedReplaySteps rate i blocks ++
    [finiteGPSConstantRateProjectionTerminalReplayStep rate terminalZero]

/-- A finite scalar replay composes across a chronological append. -/
theorem lateBatchReplayFrom_append
    (initial : Real) (left right : List LateBatchReplayStep) :
    lateBatchReplayFrom initial (left ++ right) =
      lateBatchReplayFrom (lateBatchReplayFrom initial left) right := by
  induction left generalizing initial with
  | nil =>
      simp [lateBatchReplayFrom]
  | cons step left ih =>
      simp only [List.cons_append, lateBatchReplayFrom]
      exact ih (initial := lateBatchUpdate initial step.service step.batch)

/-- The projected comparator is exactly the finite scalar replay of its
retained endpoint batches followed by its explicit terminal zero-batch
service suffix.  This is an identity of ordered folds; it needs no
nonnegativity, source-process, or scheduler hypotheses. -/
theorem finiteGPSConstantRateProjectionComparatorFrom_eq_replayFrom
    (initial rate : Real) (i : Class)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSConstantRateProjectionComparatorFrom initial rate i blocks terminalZero =
      lateBatchReplayFrom initial
        (finiteGPSConstantRateProjectionReplaySteps rate i blocks terminalZero) := by
  induction blocks generalizing initial with
  | nil =>
      simp [finiteGPSConstantRateProjectionComparatorFrom,
        finiteGPSConstantRateProjectionReplaySteps,
        finiteGPSConstantRateProjectionRetainedReplaySteps,
        lateBatchReplayFrom,
        finiteGPSConstantRateProjectionTerminalReplayStep]
  | cons block blocks ih =>
      simp only [finiteGPSConstantRateProjectionComparatorFrom,
        finiteGPSConstantRateProjectionReplaySteps,
        finiteGPSConstantRateProjectionRetainedReplaySteps, List.map_cons,
        List.cons_append, lateBatchReplayFrom]
      exact ih (initial := lateBatchUpdate initial
        (rate * finiteGPSConstantRateProjectionBlockDuration block)
        (block.retained.endpointBatch i))

/-- Equivalent form that keeps the terminal zero-batch suffix visibly
separate from the retained source endpoints. -/
theorem finiteGPSConstantRateProjectionComparatorFrom_eq_retainedReplay_then_terminal
    (initial rate : Real) (i : Class)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSConstantRateProjectionComparatorFrom initial rate i blocks terminalZero =
      lateBatchUpdate
        (lateBatchReplayFrom initial
          (finiteGPSConstantRateProjectionRetainedReplaySteps rate i blocks))
        (rate * finiteGPSExecutionSegmentsTotalDuration terminalZero) 0 := by
  rw [finiteGPSConstantRateProjectionComparatorFrom_eq_replayFrom]
  rw [show finiteGPSConstantRateProjectionReplaySteps rate i blocks terminalZero =
      finiteGPSConstantRateProjectionRetainedReplaySteps rate i blocks ++
        [finiteGPSConstantRateProjectionTerminalReplayStep rate terminalZero] by rfl]
  rw [lateBatchReplayFrom_append]
  simp [lateBatchReplayFrom, finiteGPSConstantRateProjectionTerminalReplayStep]

/-- A finite functional form of the scalar replay.  Source adapters that
index retained blocks by `Fin N` can use this without rebuilding a recursive
list fold by hand. -/
def lateBatchReplayOfFn {N : Nat}
    (initial : Real) (steps : Fin N -> LateBatchReplayStep) : Real :=
  lateBatchReplayFrom initial (List.ofFn steps)

/-- Pointwise equal finite replay steps give the same scalar replay.  This is
the extensional bridge for source adapters whose retained-block certificate
is naturally a `Fin N` function. -/
theorem lateBatchReplayOfFn_congr {N : Nat}
    (initial : Real) (left right : Fin N -> LateBatchReplayStep)
    (hstep : ∀ j, left j = right j) :
    lateBatchReplayOfFn initial left = lateBatchReplayOfFn initial right := by
  unfold lateBatchReplayOfFn
  congr 2
  funext j
  exact hstep j

/-- Mapping finite projection blocks to scalar replay steps commutes with
`List.ofFn`.  This is a source-agnostic list equality: it merely exposes the
block function's chronological finite order. -/
theorem finiteGPSConstantRateProjectionRetainedReplaySteps_ofFn
    {N : Nat} (rate : Real) (i : Class)
    (blocks : Fin N -> FiniteGPSConstantRateProjectionBlock Class) :
    finiteGPSConstantRateProjectionRetainedReplaySteps rate i (List.ofFn blocks) =
      List.ofFn (fun j =>
        { service := rate * finiteGPSConstantRateProjectionBlockDuration (blocks j)
          batch := (blocks j).retained.endpointBatch i }) := by
  simp [finiteGPSConstantRateProjectionRetainedReplaySteps,
    List.map_ofFn, Function.comp_def]

/-- The service elapsed before the first retained endpoint has no effect on
an empty selected-class scalar queue.  This permits a projection to begin at
an arbitrary physical reset boundary, including a boundary belonging to a
different class. -/
theorem lateBatchUpdate_zero_initial_eq_batch
    (service batch : Real) (hservice_nonneg : 0 <= service) :
    lateBatchUpdate 0 service batch = batch := by
  unfold lateBatchUpdate
  rw [max_eq_right (sub_nonpos.mpr hservice_nonneg)]
  ring

/-- The chronological scalar replay of exactly `N` retained batches.  The
first batch may be preceded by an arbitrary physical-reset service interval;
because the scalar state begins at zero, only its nonnegativity matters.  A
later retained batch `j + 1` is preceded by service coordinate `j`.

The definition deliberately has no entry when `N = 0`.  In that case the
terminal zero-batch suffix is still retained separately by the projection
comparator and can be shown inert from its nonnegative service amount. -/
def lateBatchChronologicalReplaySteps
    (firstService : Real) (batch service : Nat -> Real) : Nat -> List LateBatchReplayStep
  | 0 => []
  | n + 1 =>
      { service := firstService, batch := batch 0 } ::
        List.ofFn (fun j : Fin n =>
          { service := service j, batch := batch (j + 1) })

/-- The chronological finite replay grows by the next ordinary
service-before-batch event.  This form is useful for source adapters working
with `List.ofFn`-indexed retained blocks. -/
theorem lateBatchChronologicalReplaySteps_succ
    (firstService : Real) (batch service : Nat -> Real) (n : Nat) :
    lateBatchChronologicalReplaySteps firstService batch service (n + 2) =
      lateBatchChronologicalReplaySteps firstService batch service (n + 1) ++
        [{ service := service n, batch := batch (n + 1) }] := by
  change
    ({ service := firstService, batch := batch 0 } : LateBatchReplayStep) ::
        List.ofFn (fun j : Fin (n + 1) =>
          ({ service := service j, batch := batch (j + 1) } : LateBatchReplayStep)) =
      (({ service := firstService, batch := batch 0 } : LateBatchReplayStep) ::
        List.ofFn (fun j : Fin n =>
          ({ service := service j, batch := batch (j + 1) } : LateBatchReplayStep)) ++
        [({ service := service n, batch := batch (n + 1) } : LateBatchReplayStep)])
  rw [List.ofFn_succ']
  simp

/-- Replaying a nonempty chronological finite target history from the empty
scalar state gives the usual post-batch workload at its final retained
batch.  The first physical-reset service is harmless provided it is
nonnegative. -/
theorem lateBatchReplayFrom_chronological_succ_eq_lateBatchPostWorkload
    (firstService : Real) (batch service : Nat -> Real)
    (hfirstService_nonneg : 0 <= firstService) (n : Nat) :
    lateBatchReplayFrom 0
      (lateBatchChronologicalReplaySteps firstService batch service (n + 1)) =
      lateBatchPostWorkload batch service n := by
  induction n with
  | zero =>
      simp only [lateBatchChronologicalReplaySteps, lateBatchReplayFrom]
      rw [lateBatchUpdate_zero_initial_eq_batch
        firstService (batch 0) hfirstService_nonneg]
      rfl
  | succ n ih =>
      rw [lateBatchChronologicalReplaySteps_succ]
      rw [lateBatchReplayFrom_append]
      rw [ih]
      simp [lateBatchReplayFrom, lateBatchPostWorkload]

/-- A chronological replay of `N` retained batches followed by a terminal
zero-batch service event is exactly `lateBatchPreWorkload` at epoch `N`.
For a nonempty history the terminal service must be the final service
coordinate; for an empty history it need only be nonnegative, as no target
batch has occurred.  This keeps the physical reset-to-tag suffix explicit
without fabricating a retained target event. -/
theorem lateBatchReplayFrom_chronological_then_terminal_eq_lateBatchPreWorkload
    (firstService terminalService : Real) (batch service : Nat -> Real) (N : Nat)
    (hfirstService_nonneg : 0 <= firstService)
    (hterminalService_nonneg_of_zero : N = 0 -> 0 <= terminalService)
    (hterminalService_eq_final_of_succ : ∀ n, N = n + 1 ->
      terminalService = service n) :
    lateBatchUpdate
      (lateBatchReplayFrom 0
        (lateBatchChronologicalReplaySteps firstService batch service N))
      terminalService 0 =
      lateBatchPreWorkload batch service N := by
  cases N with
  | zero =>
      simp only [lateBatchChronologicalReplaySteps, lateBatchReplayFrom,
        lateBatchPreWorkload]
      rw [lateBatchUpdate_zero_initial_eq_batch terminalService 0
        (hterminalService_nonneg_of_zero rfl)]
  | succ n =>
      rw [hterminalService_eq_final_of_succ n rfl]
      rw [lateBatchReplayFrom_chronological_succ_eq_lateBatchPostWorkload
        firstService batch service hfirstService_nonneg n]
      simp [lateBatchUpdate, lateBatchPreWorkload]

/-- Generic finite-block bridge from a semantic GPS projection to the usual
finite Lindley/late-batch pre-workload.  A source adapter supplies only a
chronological equality of retained scalar events and the physical terminal
service identification; no source event names or scheduler branches appear
in this theorem. -/
theorem finiteGPSConstantRateProjectionComparatorFrom_eq_lateBatchPreWorkload_of_retainedReplay_eq
    {N : Nat} (rate : Real) (i : Class)
    (blocks : Fin N -> FiniteGPSConstantRateProjectionBlock Class)
    (terminalZero : List (FiniteGPSExecutionSegment Class))
    (firstService : Real) (batch service : Nat -> Real)
    (hretainedReplay :
      finiteGPSConstantRateProjectionRetainedReplaySteps rate i (List.ofFn blocks) =
        lateBatchChronologicalReplaySteps firstService batch service N)
    (hfirstService_nonneg : 0 <= firstService)
    (hterminalService_nonneg_of_zero : N = 0 ->
      0 <= rate * finiteGPSExecutionSegmentsTotalDuration terminalZero)
    (hterminalService_eq_final_of_succ : ∀ n, N = n + 1 ->
      rate * finiteGPSExecutionSegmentsTotalDuration terminalZero = service n) :
    finiteGPSConstantRateProjectionComparatorFrom 0 rate i
      (List.ofFn blocks) terminalZero =
      lateBatchPreWorkload batch service N := by
  rw [finiteGPSConstantRateProjectionComparatorFrom_eq_retainedReplay_then_terminal]
  rw [hretainedReplay]
  exact lateBatchReplayFrom_chronological_then_terminal_eq_lateBatchPreWorkload
    firstService (rate * finiteGPSExecutionSegmentsTotalDuration terminalZero)
    batch service N hfirstService_nonneg hterminalService_nonneg_of_zero
    hterminalService_eq_final_of_succ

/-- A projection block's declared duration is exactly the sum of the
durations in its concrete expansion. -/
theorem finiteGPSConstantRateProjectionBlockDuration_eq_totalDuration
    (block : FiniteGPSConstantRateProjectionBlock Class) :
    finiteGPSConstantRateProjectionBlockDuration block =
      finiteGPSExecutionSegmentsTotalDuration
        (finiteGPSConstantRateProjectionBlockSegments block) := by
  simp [finiteGPSConstantRateProjectionBlockDuration,
    finiteGPSConstantRateProjectionBlockSegments,
    finiteGPSExecutionSegmentsTotalDuration]

/-- Every interval emitted by one bounded executable GPS gap has nonnegative
duration under the ordinary finite-runner hypotheses.  This is independent of
the selected class and is useful when a later semantic projection groups
several emitted intervals into one source-to-source gap. -/
theorem finiteGPSRunGapSegments_duration_nonneg
    (fuel : Nat) {capacity nextBatchDelay : Real}
    {weight work batchWork : Class -> Real} {currentTime : Real}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : ∀ j, 0 <= work j)
    (hnextBatchDelay_nonneg : 0 <= nextBatchDelay) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      0 <= segment.duration := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hexternal : duration = nextBatchDelay
      · intro segment hsegment
        have hsegment_eq :
            segment = finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hexternal] using hsegment
        subst segment
        exact finiteGPSBuildExecutionSegment_duration_nonneg
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hnextBatchDelay_nonneg
      · have hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
            nextBatchDelay := by
          simpa [duration] using hexternal
        have hnext_work_nonneg : ∀ j, 0 <=
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hremaining_delay_nonneg : 0 <= nextBatchDelay - duration := by
          rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
              nextBatchDelay)
        have hlist :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
              currentTime nextBatchDelay =
              finiteGPSBuildExecutionSegment capacity weight work batchWork
                currentTime nextBatchDelay ::
                finiteGPSRunGapSegments fuel capacity weight
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                  batchWork (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hexternal]
        intro segment hsegment
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_duration_nonneg
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            hnextBatchDelay_nonneg
        · exact ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_work_nonneg hremaining_delay_nonneg segment htail

/-- Every interval emitted by a complete chronological GPS batch trace has
nonnegative duration.  The theorem follows the executable trace recursion;
it does not infer time positivity from an event name or from a caller-made
segmentation. -/
theorem finiteGPSRunBatchTraceSegments_duration_nonneg
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : ∀ j, 0 <= work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      0 <= segment.duration := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 <= batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j, 0 <= batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true := by
        simpa [gap, gapFuel] using
          (finiteGPSRunGap_terminates_of_activeCard_lt
            gapFuel (capacity := capacity) (weight := weight) (work := work)
            (batchWork := batchWork eventTime)
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            (sub_nonneg.mpr hdelay) (Nat.lt_succ_self _)).1
      have hgap_work_nonneg : ∀ j, 0 <= gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have hgap_duration := finiteGPSRunGapSegments_duration_nonneg
        gapFuel (capacity := capacity) (weight := weight) (work := work)
        (batchWork := batchWork eventTime) (currentTime := currentTime)
        (nextBatchDelay := eventTime - currentTime)
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        (sub_nonneg.mpr hdelay)
      have htail_duration := ih (currentTime := eventTime) (work := gap.workload)
        hgap_work_nonneg hchronological_tail hbatch_tail
      have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
          currentTime work (eventTime :: times) =
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
        simpa [gap, gapFuel] using
          (finiteGPSRunBatchTraceSegments_cons_of_batchApplied capacity weight
            batchWork currentTime work eventTime times hgap_terminates)
      intro segment hsegment
      rw [htrace] at hsegment
      rcases List.mem_append.mp hsegment with hgap | htail
      · exact hgap_duration segment hgap
      · exact htail_duration segment htail

/-- For any literal chain of concrete segments, elapsed duration telescopes
to the final endpoint clock minus the initial clock.  This is independent of
GPS rate or source provenance, and is the time bridge used to turn projected
blocks into physical interarrival gaps. -/
theorem finiteGPSExecutionSegmentsTotalDuration_eq_finalTime_sub_start
    (initialTime : Real) (initialWorkload : Class -> Real)
    (segments : List (FiniteGPSExecutionSegment Class))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload segments) :
    finiteGPSExecutionSegmentsTotalDuration segments =
      finiteGPSExecutionSegmentsFinalTime initialTime segments - initialTime := by
  induction segments generalizing initialTime initialWorkload with
  | nil =>
      simp [finiteGPSExecutionSegmentsTotalDuration,
        finiteGPSExecutionSegmentsFinalTime]
  | cons segment segments ih =>
      rcases hchain with ⟨hstart, hwork, htail⟩
      have htail_duration := ih
        (initialTime := finiteGPSExecutionSegmentEndTime segment)
        (initialWorkload := segment.endpointWorkload) htail
      change segment.duration + finiteGPSExecutionSegmentsTotalDuration segments =
        finiteGPSExecutionSegmentsFinalTime
          (finiteGPSExecutionSegmentEndTime segment) segments - initialTime
      rw [htail_duration]
      change segment.duration +
          (finiteGPSExecutionSegmentsFinalTime
            (segment.startTime + segment.duration) segments -
              (segment.startTime + segment.duration)) =
        finiteGPSExecutionSegmentsFinalTime
          (segment.startTime + segment.duration) segments - initialTime
      rw [hstart]
      ring

/-- A concrete chain through an appended segment ledger decomposes exactly
into a chain through its prefix and a chain from that prefix's actual final
endpoint.  This is the structural bridge used to obtain a local chain for
each caller-supplied projection block from one executable full-trace chain. -/
theorem finiteGPSExecutionSegmentsChainFrom_append_iff
    (initialTime : Real) (initialWorkload : Class -> Real)
    (left right : List (FiniteGPSExecutionSegment Class)) :
    FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload (left ++ right) ↔
      FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload left ∧
        FiniteGPSExecutionSegmentsChainFrom
          (finiteGPSExecutionSegmentsFinalTime initialTime left)
          (finiteGPSExecutionSegmentsFinalWorkload initialWorkload left) right := by
  induction left generalizing initialTime initialWorkload with
  | nil =>
      simp [FiniteGPSExecutionSegmentsChainFrom,
        finiteGPSExecutionSegmentsFinalTime,
        finiteGPSExecutionSegmentsFinalWorkload]
  | cons segment left ih =>
      simp only [List.cons_append, FiniteGPSExecutionSegmentsChainFrom,
        finiteGPSExecutionSegmentsFinalTime,
        finiteGPSExecutionSegmentsFinalWorkload]
      rw [ih]
      constructor
      · rintro ⟨hstart, hwork, hleft, hright⟩
        exact ⟨⟨hstart, hwork, hleft⟩, hright⟩
      · rintro ⟨⟨hstart, hwork, hleft⟩, hright⟩
        exact ⟨hstart, hwork, hleft, hright⟩

/-- A projected block's duration is the physical elapsed time between the
block's literal start and its final concrete endpoint.  Source adapters can
instantiate the final endpoint with a retained target-arrival epoch. -/
theorem finiteGPSConstantRateProjectionBlockDuration_eq_finalTime_sub_start
    (initialTime : Real) (initialWorkload : Class -> Real)
    (block : FiniteGPSConstantRateProjectionBlock Class)
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionBlockSegments block)) :
    finiteGPSConstantRateProjectionBlockDuration block =
      finiteGPSExecutionSegmentsFinalTime initialTime
        (finiteGPSConstantRateProjectionBlockSegments block) - initialTime := by
  rw [finiteGPSConstantRateProjectionBlockDuration_eq_totalDuration]
  exact finiteGPSExecutionSegmentsTotalDuration_eq_finalTime_sub_start
    initialTime initialWorkload
    (finiteGPSConstantRateProjectionBlockSegments block) hchain

/-- A block embedded in a larger semantic projection inherits its physical
elapsed duration from the one concrete execution chain.  The result is
purely list-structural: it does not inspect source labels, batch sizes, or
scheduler event names. -/
theorem finiteGPSConstantRateProjectionBlockDuration_eq_finalTime_sub_prefix
    (initialTime : Real) (initialWorkload : Class -> Real)
    (earlier suffix : List (FiniteGPSConstantRateProjectionBlock Class))
    (block : FiniteGPSConstantRateProjectionBlock Class)
    (terminalZero : List (FiniteGPSExecutionSegment Class))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments (earlier ++ block :: suffix)
        terminalZero)) :
    finiteGPSConstantRateProjectionBlockDuration block =
      finiteGPSExecutionSegmentsFinalTime initialTime
        (finiteGPSConstantRateProjectionSegments (earlier ++ [block]) []) -
      finiteGPSExecutionSegmentsFinalTime initialTime
        (finiteGPSConstantRateProjectionSegments earlier []) := by
  let earlierSegments := earlier.flatMap finiteGPSConstantRateProjectionBlockSegments
  let blockSegments := finiteGPSConstantRateProjectionBlockSegments block
  let suffixSegments := suffix.flatMap finiteGPSConstantRateProjectionBlockSegments ++
    terminalZero
  have hsegments : finiteGPSConstantRateProjectionSegments
      (earlier ++ block :: suffix) terminalZero =
      earlierSegments ++ blockSegments ++ suffixSegments := by
    simp [finiteGPSConstantRateProjectionSegments, earlierSegments,
      blockSegments, suffixSegments, List.append_assoc]
  have hchain' : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (earlierSegments ++ blockSegments ++ suffixSegments) := by
    rw [← hsegments]
    exact hchain
  have hchain_assoc : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (earlierSegments ++ (blockSegments ++ suffixSegments)) := by
    simpa only [List.append_assoc] using hchain'
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      initialTime initialWorkload earlierSegments
      (blockSegments ++ suffixSegments)).mp hchain_assoc with ⟨hprefix, htail⟩
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      (finiteGPSExecutionSegmentsFinalTime initialTime earlierSegments)
      (finiteGPSExecutionSegmentsFinalWorkload initialWorkload earlierSegments)
      blockSegments suffixSegments).mp htail with ⟨hblock, _⟩
  calc
    finiteGPSConstantRateProjectionBlockDuration block =
        finiteGPSExecutionSegmentsFinalTime
          (finiteGPSExecutionSegmentsFinalTime initialTime earlierSegments)
          blockSegments -
        finiteGPSExecutionSegmentsFinalTime initialTime earlierSegments :=
      finiteGPSConstantRateProjectionBlockDuration_eq_finalTime_sub_start
        (finiteGPSExecutionSegmentsFinalTime initialTime earlierSegments)
        (finiteGPSExecutionSegmentsFinalWorkload initialWorkload earlierSegments)
        block hblock
    _ = finiteGPSExecutionSegmentsFinalTime initialTime
          (earlierSegments ++ blockSegments) -
        finiteGPSExecutionSegmentsFinalTime initialTime earlierSegments := by
      rw [finiteGPSExecutionSegmentsFinalTime_append]
    _ = finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments (earlier ++ [block]) []) -
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments earlier []) := by
      simp [finiteGPSConstantRateProjectionSegments, earlierSegments,
        blockSegments, List.append_assoc]

/-- The final source-empty/service-only suffix of a semantic projection has
the physical elapsed duration between the final retained endpoint and the
full ledger's final clock.  It remains a real suffix rather than a synthetic
arrival. -/
theorem finiteGPSConstantRateProjectionTerminalDuration_eq_finalTime_sub_blocks
    (initialTime : Real) (initialWorkload : Class -> Real)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments blocks terminalZero)) :
    finiteGPSExecutionSegmentsTotalDuration terminalZero =
      finiteGPSExecutionSegmentsFinalTime initialTime
        (finiteGPSConstantRateProjectionSegments blocks terminalZero) -
      finiteGPSExecutionSegmentsFinalTime initialTime
        (finiteGPSConstantRateProjectionSegments blocks []) := by
  let blockSegments := blocks.flatMap finiteGPSConstantRateProjectionBlockSegments
  have hsegments : finiteGPSConstantRateProjectionSegments blocks terminalZero =
      blockSegments ++ terminalZero := by
    simp [finiteGPSConstantRateProjectionSegments, blockSegments]
  have hchain' : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (blockSegments ++ terminalZero) := by
    rw [← hsegments]
    exact hchain
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      initialTime initialWorkload blockSegments terminalZero).mp hchain' with
      ⟨_, hterminal⟩
  calc
    finiteGPSExecutionSegmentsTotalDuration terminalZero =
        finiteGPSExecutionSegmentsFinalTime
          (finiteGPSExecutionSegmentsFinalTime initialTime blockSegments)
          terminalZero -
        finiteGPSExecutionSegmentsFinalTime initialTime blockSegments :=
      finiteGPSExecutionSegmentsTotalDuration_eq_finalTime_sub_start
        (finiteGPSExecutionSegmentsFinalTime initialTime blockSegments)
        (finiteGPSExecutionSegmentsFinalWorkload initialWorkload blockSegments)
        terminalZero hterminal
    _ = finiteGPSExecutionSegmentsFinalTime initialTime
          (blockSegments ++ terminalZero) -
        finiteGPSExecutionSegmentsFinalTime initialTime blockSegments := by
      rw [finiteGPSExecutionSegmentsFinalTime_append]
    _ = finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments blocks terminalZero) -
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments blocks []) := by
      simp [finiteGPSConstantRateProjectionSegments, blockSegments]

/-- Semantic projection is an exact scalar-recursion identity.  Every
selected-class-zero prefix is compressed into the service interval before its
retained endpoint; every final zero block remains as the final reflected
service interval.  The hypotheses are entirely semantic: selected endpoint
batches, elapsed durations, and scalar nonnegativity. -/
theorem finiteGPSConstantRateSegmentComparatorFrom_eq_projectionComparatorFrom
    (initial rate : Real) (i : Class)
    (blocks : List (FiniteGPSConstantRateProjectionBlock Class))
    (terminalZero : List (FiniteGPSExecutionSegment Class))
    (hinitial_nonneg : 0 <= initial)
    (hrate_nonneg : 0 <= rate)
    (hprefix_duration_nonneg : ∀ block ∈ blocks, ∀ segment ∈ block.zeroPrefix,
      0 <= segment.duration)
    (hretained_duration_nonneg : ∀ block ∈ blocks, 0 <= block.retained.duration)
    (hterminal_duration_nonneg : ∀ segment ∈ terminalZero, 0 <= segment.duration)
    (hprefix_zero_batch : ∀ block ∈ blocks, ∀ segment ∈ block.zeroPrefix,
      segment.endpointBatch i = 0)
    (hterminal_zero_batch : ∀ segment ∈ terminalZero,
      segment.endpointBatch i = 0)
    (hretained_batch_nonneg : ∀ block ∈ blocks,
      0 <= block.retained.endpointBatch i) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i
      (finiteGPSConstantRateProjectionSegments blocks terminalZero) =
      finiteGPSConstantRateProjectionComparatorFrom initial rate i
        blocks terminalZero := by
  induction blocks generalizing initial with
  | nil =>
      simpa [finiteGPSConstantRateProjectionSegments,
        finiteGPSConstantRateProjectionComparatorFrom] using
        (finiteGPSConstantRateSegmentComparatorFrom_eq_combinedZeroBatchService
          initial rate i terminalZero hinitial_nonneg hrate_nonneg
          hterminal_duration_nonneg hterminal_zero_batch)
  | cons block blocks ih =>
      have hblock_prefix_duration : ∀ segment ∈ block.zeroPrefix,
          0 <= segment.duration := by
        intro segment hsegment
        exact hprefix_duration_nonneg block (by simp) segment hsegment
      have hblock_retained_duration : 0 <= block.retained.duration :=
        hretained_duration_nonneg block (by simp)
      have hblock_prefix_zero : ∀ segment ∈ block.zeroPrefix,
          segment.endpointBatch i = 0 := by
        intro segment hsegment
        exact hprefix_zero_batch block (by simp) segment hsegment
      have hnext_nonneg : 0 <= lateBatchUpdate initial
          (rate * finiteGPSConstantRateProjectionBlockDuration block)
          (block.retained.endpointBatch i) := by
        unfold lateBatchUpdate
        exact add_nonneg (le_max_right _ _)
          (hretained_batch_nonneg block (by simp))
      have htail_prefix_duration : ∀ later ∈ blocks,
          ∀ segment ∈ later.zeroPrefix, 0 <= segment.duration := by
        intro later hlater segment hsegment
        exact hprefix_duration_nonneg later (by simp [hlater]) segment hsegment
      have htail_retained_duration : ∀ later ∈ blocks,
          0 <= later.retained.duration := by
        intro later hlater
        exact hretained_duration_nonneg later (by simp [hlater])
      have htail_prefix_zero : ∀ later ∈ blocks,
          ∀ segment ∈ later.zeroPrefix, segment.endpointBatch i = 0 := by
        intro later hlater segment hsegment
        exact hprefix_zero_batch later (by simp [hlater]) segment hsegment
      have htail_retained_batch_nonneg : ∀ later ∈ blocks,
          0 <= later.retained.endpointBatch i := by
        intro later hlater
        exact hretained_batch_nonneg later (by simp [hlater])
      have hhead := finiteGPSConstantRateSegmentComparatorFrom_zeroBatchPrefix_then
        initial rate i block.zeroPrefix block.retained
        (finiteGPSConstantRateProjectionSegments blocks terminalZero)
        hinitial_nonneg hrate_nonneg hblock_prefix_duration
        hblock_retained_duration hblock_prefix_zero
      have htail := ih
        (initial := lateBatchUpdate initial
          (rate * finiteGPSConstantRateProjectionBlockDuration block)
          (block.retained.endpointBatch i))
        hnext_nonneg htail_prefix_duration htail_retained_duration
        htail_prefix_zero htail_retained_batch_nonneg
      have hsegments : finiteGPSConstantRateProjectionSegments
          (block :: blocks) terminalZero =
          block.zeroPrefix ++ block.retained ::
            finiteGPSConstantRateProjectionSegments blocks terminalZero := by
        simp [finiteGPSConstantRateProjectionSegments,
          finiteGPSConstantRateProjectionBlockSegments, List.append_assoc]
      rw [hsegments]
      rw [hhead]
      simpa [finiteGPSConstantRateProjectionComparatorFrom,
        finiteGPSConstantRateProjectionBlockDuration] using htail

end

end AppliedModelingLib.Probability.Queueing
