import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSMeasurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentMeasurability
import Mathlib.Tactic

/-!
# Fixed-skeleton Borel FCFS replay

This module gives the generic second half of a finite GPS/FCFS measurability
argument.  A preceding GPS layer may expose a bounded, totalized family of
segment slots.  Here a *fixed discrete skeleton* declares which such slots are
active, gives a fixed queue shape before each active slot, and records whether
that slot contains the first keyed completion.  Its real coordinates remain
Borel functions; only the branch and queue-shape data are stratified.

The executable FCFS fold is not replaced.  `Matches` below recursively checks
the actual generated step list and its actual pre-step ledger.  On a matching
fiber, the skeleton response is proved equal to the literal completion-trace
scan.  Establishing that all generated GPS/FCFS executions admit countably
many Borel `Matches` fibers is deliberately a separate bridge.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId Omega : Type*} [Fintype Class] [DecidableEq Class]
  [MeasurableSpace Omega]

/-- One position in a fixed, padded GPS/FCFS replay layout.  `active` is
fixed skeleton data: inactive positions consume no actual FCFS step.  For an
active position, `preQueue` describes the tracked class's queue immediately
before its concrete segment and `keyCompletes` records whether that segment
contains a keyed completion. -/
structure FiniteGPSFCFSPaddedReplaySlot (Class JobId Omega : Type*) where
  segment : Omega → FiniteGPSExecutionSegment Class
  preQueue : List (Omega → FiniteGPSFCFSJob JobId)
  active : Bool
  keyCompletes : Bool

/-- The local first-key response for one replay slot.  It is the existing
FCFS scalar selector applied to the slot's concrete segment and fixed queue
coordinates. -/
def FiniteGPSFCFSPaddedReplaySlot.firstKeyResponse
    (key : JobId → Bool) (trackedClass : Class)
    (slot : FiniteGPSFCFSPaddedReplaySlot Class JobId Omega) (omega : Omega) : ℝ :=
  finiteGPSFCFSFirstKeyCompletionResponse key
    (slot.segment omega).startTime
    ((slot.segment omega).classRate trackedClass)
    0
    ((slot.segment omega).serviceIncrement trackedClass)
    (slot.preQueue.map fun job => job omega)

/-- Borel coordinate requirements for one static replay slot.  Identifier
values need not themselves be measurable: the fixed queue-key condition is
the only discrete requirement used by the scalar selector. -/
def FiniteGPSFCFSPaddedReplaySlot.CoordinatesMeasurable
    (key : JobId → Bool) (trackedClass : Class)
    (slot : FiniteGPSFCFSPaddedReplaySlot Class JobId Omega) : Prop :=
  FiniteGPSExecutionSegmentCoordinatesMeasurable slot.segment ∧
    FiniteGPSFCFSFixedQueueCoordinatesMeasurable slot.preQueue ∧
      FiniteGPSFCFSFixedQueueKeyShape key slot.preQueue

/-- A slot's exact local response is Borel from its segment and fixed queue
coordinates. -/
theorem FiniteGPSFCFSPaddedReplaySlot.measurable_firstKeyResponse
    (key : JobId → Bool) (trackedClass : Class)
    (slot : FiniteGPSFCFSPaddedReplaySlot Class JobId Omega)
    (hcoordinates : slot.CoordinatesMeasurable key trackedClass) :
    Measurable (slot.firstKeyResponse key trackedClass) := by
  rcases hcoordinates with ⟨hsegment, hqueue, hkeyShape⟩
  simpa [FiniteGPSFCFSPaddedReplaySlot.firstKeyResponse] using
    (measurable_finiteGPSFCFSFirstKeyCompletionResponse_apply key
      (fun omega => (slot.segment omega).startTime)
      (fun omega => (slot.segment omega).classRate trackedClass)
      (fun _ : Omega => 0)
      (fun omega => (slot.segment omega).serviceIncrement trackedClass)
      hsegment.1 (hsegment.2.2.2.1 trackedClass) measurable_const
      (hsegment.2.2.2.2.1 trackedClass)
      slot.preQueue hqueue hkeyShape)

/-- Scan a fixed padded skeleton in its declared order.  Inactive slots and
active slots without a keyed completion are skipped; the first active slot
whose fixed `keyCompletes` flag is true supplies the literal local FCFS
response. -/
def finiteGPSFCFSPaddedReplayResponse
    (key : JobId → Bool) (trackedClass : Class) :
    List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega) → Omega → ℝ
  | [], _ => 0
  | slot :: slots, omega =>
      if slot.active = true then
        if slot.keyCompletes = true then
          slot.firstKeyResponse key trackedClass omega
        else finiteGPSFCFSPaddedReplayResponse key trackedClass slots omega
      else finiteGPSFCFSPaddedReplayResponse key trackedClass slots omega

/-- A fixed padded replay response is Borel whenever each static slot has
Borel real coordinates.  The active/completion flags are skeleton data, so
the proof does not introduce a random branch selector. -/
theorem measurable_finiteGPSFCFSPaddedReplayResponse
    (key : JobId → Bool) (trackedClass : Class)
    (slots : List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega))
    (hcoordinates : ∀ slot ∈ slots,
      slot.CoordinatesMeasurable key trackedClass) :
    Measurable (finiteGPSFCFSPaddedReplayResponse key trackedClass slots) := by
  induction slots with
  | nil =>
      simp [finiteGPSFCFSPaddedReplayResponse]
  | cons slot slots ih =>
      have hslot : slot.CoordinatesMeasurable key trackedClass :=
        hcoordinates slot (by simp)
      have htail : ∀ later ∈ slots,
          later.CoordinatesMeasurable key trackedClass := by
        intro later hlater
        exact hcoordinates later (by simp [hlater])
      have hresponse := slot.measurable_firstKeyResponse key trackedClass hslot
      have htailResponse := ih htail
      by_cases hactive : slot.active = true
      · by_cases hkey : slot.keyCompletes = true
        · simpa [finiteGPSFCFSPaddedReplayResponse, hactive, hkey] using hresponse
        · simpa [finiteGPSFCFSPaddedReplayResponse, hactive, hkey] using htailResponse
      · simpa [finiteGPSFCFSPaddedReplayResponse, hactive] using htailResponse

/-- The fixed skeleton condition for one active concrete FCFS step.  It
checks the actual segment, the actual tracked pre-step queue, and whether the
existing local completion scan contains a keyed record. -/
def FiniteGPSFCFSPaddedReplaySlot.Matches
    (key : JobId → Bool) (trackedClass : Class)
    (slot : FiniteGPSFCFSPaddedReplaySlot Class JobId Omega)
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (actual : FiniteGPSFCFSSegmentJobStep Class JobId) (omega : Omega) : Prop :=
  actual.segment = slot.segment omega ∧
    ledger.residualJobs trackedClass = slot.preQueue.map (fun job => job omega) ∧
      (slot.keyCompletes = true ↔
        finiteGPSFCFSFirstKeyCompletion? key
          (finiteGPSFCFSCompletedJobsInSegment actual.segment trackedClass
            (ledger.residualJobs trackedClass)) ≠ none)

/-- Recursively compare a literal FCFS step list with a fixed padded replay
skeleton.  An active skeleton slot consumes exactly one literal step and
advances the literal ledger; an inactive slot consumes neither.  Thus this
is an exact shape certificate for the executable fold, not a second FCFS
transition relation. -/
def finiteGPSFCFSPaddedReplayMatchesFrom
    (key : JobId → Bool) (trackedClass : Class) (omega : Omega) :
    FiniteGPSFCFSJobLedger Class JobId →
      List (FiniteGPSFCFSSegmentJobStep Class JobId) →
        List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega) → Prop
  | _ledger, actualSteps, [] => actualSteps = []
  | ledger, [], slot :: slots =>
      match slot.active with
      | true => False
      | false => finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
          ledger [] slots
  | ledger, actual :: actualSteps, slot :: slots =>
      match slot.active with
      | true =>
          slot.Matches key trackedClass ledger actual omega ∧
            finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
              (finiteGPSFCFSApplySegment ledger actual.segment actual.endpointJobs)
              actualSteps slots
      | false => finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
          ledger (actual :: actualSteps) slots

/-- Wrapper for a literal finite FCFS trace and a fixed padded replay
skeleton. -/
def finiteGPSFCFSPaddedReplayMatches
    (key : JobId → Bool) (trackedClass : Class)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (actualSteps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (slots : List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega))
    (omega : Omega) : Prop :=
  finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega initial actualSteps slots

/-- Scanning a completion list after a prefix with no keyed record is the
same as scanning the suffix. -/
theorem finiteGPSFCFSFirstKeyCompletion?_append_of_eq_none
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (hleft : finiteGPSFCFSFirstKeyCompletion? key left = none) :
    finiteGPSFCFSFirstKeyCompletion? key (left ++ right) =
      finiteGPSFCFSFirstKeyCompletion? key right := by
  induction left with
  | nil => simp
  | cons completion left ih =>
      by_cases hkey : key completion.identifier = true
      · simp [finiteGPSFCFSFirstKeyCompletion?, hkey] at hleft
      · simp only [finiteGPSFCFSFirstKeyCompletion?, hkey] at hleft ⊢
        simpa [finiteGPSFCFSFirstKeyCompletion?, hkey] using ih hleft

/-- A keyed record selected in a completion prefix remains the selected
record after appending any suffix. -/
theorem finiteGPSFCFSFirstKeyCompletion?_append_of_eq_some
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (selected : FiniteGPSFCFSCompletion JobId)
    (hleft : finiteGPSFCFSFirstKeyCompletion? key left = some selected) :
    finiteGPSFCFSFirstKeyCompletion? key (left ++ right) = some selected := by
  induction left with
  | nil =>
      simp [finiteGPSFCFSFirstKeyCompletion?] at hleft
  | cons completion left ih =>
      by_cases hkey : key completion.identifier = true
      · simp [finiteGPSFCFSFirstKeyCompletion?, hkey] at hleft ⊢
        exact hleft
      · simp only [finiteGPSFCFSFirstKeyCompletion?, hkey] at hleft ⊢
        simpa [finiteGPSFCFSFirstKeyCompletion?, hkey] using ih hleft

/-- The scalar trace response also ignores a prefix without a keyed
completion. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_append_of_eq_none
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (hleft : finiteGPSFCFSFirstKeyCompletion? key left = none) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key (left ++ right) =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace key right := by
  unfold finiteGPSFCFSFirstKeyCompletionResponseFromTrace
  rw [finiteGPSFCFSFirstKeyCompletion?_append_of_eq_none key left right hleft]

/-- The scalar trace response is fixed by any prefix in which a keyed record
is selected. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_append_of_ne_none
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (hleft : finiteGPSFCFSFirstKeyCompletion? key left ≠ none) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key (left ++ right) =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace key left := by
  cases hscan : finiteGPSFCFSFirstKeyCompletion? key left with
  | none => exact (hleft hscan).elim
  | some selected =>
      unfold finiteGPSFCFSFirstKeyCompletionResponseFromTrace
      rw [finiteGPSFCFSFirstKeyCompletion?_append_of_eq_some
        key left right selected hscan, hscan]

/-- On a matching padded execution skeleton, the fixed Borel replay response
is exactly the literal first-key response obtained by scanning the actual
class-wise FCFS completion trace. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_paddedReplayResponse_of_matches
    (key : JobId → Bool) (trackedClass : Class)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (actualSteps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (slots : List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega))
    (omega : Omega)
    (hmatches : finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
      initial actualSteps slots) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial trackedClass actualSteps) =
      finiteGPSFCFSPaddedReplayResponse key trackedClass slots omega := by
  induction slots generalizing initial actualSteps with
  | nil =>
      change actualSteps = [] at hmatches
      subst actualSteps
      simp [finiteGPSFCFSRunSegmentStepsClassCompletions,
        finiteGPSFCFSPaddedReplayResponse,
        finiteGPSFCFSFirstKeyCompletionResponseFromTrace,
        finiteGPSFCFSFirstKeyCompletion?]
  | cons slot slots ih =>
      cases hactive : slot.active with
      | false =>
          cases actualSteps with
          | nil =>
              have htail : finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
                  initial [] slots := by
                simpa [finiteGPSFCFSPaddedReplayMatchesFrom, hactive] using hmatches
              simpa [finiteGPSFCFSPaddedReplayMatchesFrom, hactive,
                finiteGPSFCFSPaddedReplayResponse] using
                (ih (initial := initial) (actualSteps := []) htail)
          | cons actual actualSteps =>
              have htail : finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
                  initial (actual :: actualSteps) slots := by
                simpa [finiteGPSFCFSPaddedReplayMatchesFrom, hactive] using hmatches
              simpa [finiteGPSFCFSPaddedReplayResponse, hactive] using
                (ih (initial := initial) (actualSteps := actual :: actualSteps) htail)
      | true =>
          cases actualSteps with
          | nil =>
              simp [finiteGPSFCFSPaddedReplayMatchesFrom, hactive] at hmatches
          | cons actual actualSteps =>
              have hmatchActive : slot.Matches key trackedClass initial actual omega ∧
                  finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega
                    (finiteGPSFCFSApplySegment initial actual.segment actual.endpointJobs)
                    actualSteps slots := by
                simpa [finiteGPSFCFSPaddedReplayMatchesFrom, hactive] using hmatches
              rcases hmatchActive with ⟨hslot, htail⟩
              have hlocalResponse :
                  finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
                    (finiteGPSFCFSCompletedJobsInSegment actual.segment trackedClass
                      (initial.residualJobs trackedClass)) =
                    slot.firstKeyResponse key trackedClass omega := by
                rcases hslot with ⟨hsegment, hqueue, _hkey⟩
                rw [hsegment, hqueue]
                simpa [FiniteGPSFCFSPaddedReplaySlot.firstKeyResponse,
                  finiteGPSFCFSCompletedJobsInSegment,
                  finiteGPSFCFSCompletedJobs] using
                  (finiteGPSFCFSFirstKeyCompletionResponse_eq_completionTraceScan
                  key (slot.segment omega).startTime
                  ((slot.segment omega).classRate trackedClass) 0
                  ((slot.segment omega).serviceIncrement trackedClass)
                  (slot.preQueue.map fun job => job omega)).symm
              have htailResponse := ih
                (initial := finiteGPSFCFSApplySegment initial actual.segment actual.endpointJobs)
                (actualSteps := actualSteps) htail
              change finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
                  (finiteGPSFCFSCompletedJobsInSegment actual.segment trackedClass
                    (initial.residualJobs trackedClass) ++
                    finiteGPSFCFSRunSegmentStepsClassCompletions
                      (finiteGPSFCFSApplySegment initial actual.segment actual.endpointJobs)
                      trackedClass actualSteps) =
                finiteGPSFCFSPaddedReplayResponse key trackedClass
                  (slot :: slots) omega
              cases hkey : slot.keyCompletes with
              | false =>
                  have hnone : finiteGPSFCFSFirstKeyCompletion? key
                      (finiteGPSFCFSCompletedJobsInSegment actual.segment trackedClass
                        (initial.residualJobs trackedClass)) = none := by
                    rcases hslot with ⟨_hsegment, _hqueue, hcompletion⟩
                    by_contra hnot
                    have htrue : slot.keyCompletes = true :=
                      hcompletion.mpr hnot
                    simp [hkey] at htrue
                  rw [finiteGPSFCFSFirstKeyCompletionResponseFromTrace_append_of_eq_none
                    key _ _ hnone]
                  simpa [finiteGPSFCFSPaddedReplayResponse, hactive, hkey] using
                    htailResponse
              | true =>
                  have hsome : finiteGPSFCFSFirstKeyCompletion? key
                      (finiteGPSFCFSCompletedJobsInSegment actual.segment trackedClass
                        (initial.residualJobs trackedClass)) ≠ none := by
                    rcases hslot with ⟨_hsegment, _hqueue, hcompletion⟩
                    exact hcompletion.mp (by simpa [hkey])
                  rw [finiteGPSFCFSFirstKeyCompletionResponseFromTrace_append_of_ne_none
                    key _ _ hsome, hlocalResponse]
                  simp [finiteGPSFCFSPaddedReplayResponse, hactive, hkey]

end

end AppliedModelingLib.Probability.Queueing
