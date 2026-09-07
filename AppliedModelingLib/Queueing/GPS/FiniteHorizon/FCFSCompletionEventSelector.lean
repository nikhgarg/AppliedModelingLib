import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSMeasurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSServiceSplit
import Mathlib.Tactic

/-!
# Event-level selectors for finite FCFS completion traces

Exact refinements of a GPS service interval can change the segment-local
fields of a `FiniteGPSFCFSCompletion` record.  They nevertheless preserve the
source identifier, source arrival time, and absolute completion time.  This
module exposes selectors on that stable event representation and relates them
to the existing concrete completion-trace selector.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {JobId : Type*}

/-- Scan completion events for the first event whose source identifier has a
fixed Boolean key.  The event representation contains exactly the fields
stable under service-interval refinement. -/
def finiteGPSFCFSFirstKeyCompletionEvent?
    (key : JobId → Bool) :
    List (JobId × ℝ × ℝ) → Option (JobId × ℝ × ℝ)
  | [] => none
  | event :: events =>
      if key event.1 = true then some event
      else finiteGPSFCFSFirstKeyCompletionEvent? key events

/-- The response duration selected from the first keyed completion event,
with the same zero fallback as the concrete completion-trace selector. -/
def finiteGPSFCFSFirstKeyCompletionEventResponse
    (key : JobId → Bool) (events : List (JobId × ℝ × ℝ)) : ℝ :=
  match finiteGPSFCFSFirstKeyCompletionEvent? key events with
  | some event => event.2.2 - event.2.1
  | none => 0

/-- The absolute completion time selected from the first keyed completion
event, with a zero fallback when no keyed completion is present. -/
def finiteGPSFCFSFirstKeyCompletionEventTime
    (key : JobId → Bool) (events : List (JobId × ℝ × ℝ)) : ℝ :=
  match finiteGPSFCFSFirstKeyCompletionEvent? key events with
  | some event => event.2.2
  | none => 0

/-- Scanning the event projection of a concrete completion trace is exactly
the event projection of its concrete first-key scan. -/
theorem finiteGPSFCFSFirstKeyCompletionEvent?_eq_map_firstKeyCompletion?
    (key : JobId → Bool)
    (completions : List (FiniteGPSFCFSCompletion JobId)) :
    finiteGPSFCFSFirstKeyCompletionEvent? key
        (finiteGPSFCFSCompletionEvents completions) =
      Option.map finiteGPSFCFSCompletionEvent
        (finiteGPSFCFSFirstKeyCompletion? key completions) := by
  induction completions with
  | nil =>
      rfl
  | cons completion completions ih =>
      by_cases hkey : key completion.identifier = true
      · simp [finiteGPSFCFSFirstKeyCompletionEvent?,
          finiteGPSFCFSCompletionEvents, finiteGPSFCFSCompletionEvent,
          finiteGPSFCFSFirstKeyCompletion?, hkey]
      · simp [finiteGPSFCFSFirstKeyCompletionEvent?,
          finiteGPSFCFSCompletionEvents, finiteGPSFCFSCompletionEvent,
          finiteGPSFCFSFirstKeyCompletion?, hkey]
        simpa [finiteGPSFCFSCompletionEvents] using ih

/-- The stable event-level duration selector agrees exactly with the existing
concrete completion-trace response selector. -/
theorem finiteGPSFCFSFirstKeyCompletionEventResponse_eq_completionTraceResponse
    (key : JobId → Bool)
    (completions : List (FiniteGPSFCFSCompletion JobId)) :
    finiteGPSFCFSFirstKeyCompletionEventResponse key
        (finiteGPSFCFSCompletionEvents completions) =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace key completions := by
  unfold finiteGPSFCFSFirstKeyCompletionEventResponse
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace
  rw [finiteGPSFCFSFirstKeyCompletionEvent?_eq_map_firstKeyCompletion?
    key completions]
  cases hselected : finiteGPSFCFSFirstKeyCompletion? key completions with
  | none =>
      simp
  | some selected =>
      simp [finiteGPSFCFSCompletionEvent]

/-- The stable event-level absolute-time selector agrees with a scan of the
concrete first-key completion record. -/
theorem finiteGPSFCFSFirstKeyCompletionEventTime_eq_completionTraceTime
    (key : JobId → Bool)
    (completions : List (FiniteGPSFCFSCompletion JobId)) :
    finiteGPSFCFSFirstKeyCompletionEventTime key
        (finiteGPSFCFSCompletionEvents completions) =
      match finiteGPSFCFSFirstKeyCompletion? key completions with
      | some completion => completion.completionTime
      | none => 0 := by
  unfold finiteGPSFCFSFirstKeyCompletionEventTime
  rw [finiteGPSFCFSFirstKeyCompletionEvent?_eq_map_firstKeyCompletion?
    key completions]
  cases hselected : finiteGPSFCFSFirstKeyCompletion? key completions with
  | none =>
      simp
  | some selected =>
      simp [finiteGPSFCFSCompletionEvent]

/-- Equality of the stable completion-event lists preserves the existing
first-key response scalar.  No equality of segment-local completion records
is assumed. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_of_completionEvents_eq
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (hevents : finiteGPSFCFSCompletionEvents left =
      finiteGPSFCFSCompletionEvents right) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key left =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace key right := by
  rw [← finiteGPSFCFSFirstKeyCompletionEventResponse_eq_completionTraceResponse
    key left,
    ← finiteGPSFCFSFirstKeyCompletionEventResponse_eq_completionTraceResponse
      key right,
    hevents]

/-- Equality of the stable completion-event lists preserves the selected
absolute completion-time scalar. -/
theorem finiteGPSFCFSFirstKeyCompletionTimeFromTrace_eq_of_completionEvents_eq
    (key : JobId → Bool)
    (left right : List (FiniteGPSFCFSCompletion JobId))
    (hevents : finiteGPSFCFSCompletionEvents left =
      finiteGPSFCFSCompletionEvents right) :
    (match finiteGPSFCFSFirstKeyCompletion? key left with
      | some completion => completion.completionTime
      | none => 0) =
      (match finiteGPSFCFSFirstKeyCompletion? key right with
      | some completion => completion.completionTime
      | none => 0) := by
  rw [← finiteGPSFCFSFirstKeyCompletionEventTime_eq_completionTraceTime key left,
    ← finiteGPSFCFSFirstKeyCompletionEventTime_eq_completionTraceTime key right,
    hevents]

end

end AppliedModelingLib.Probability.Queueing
