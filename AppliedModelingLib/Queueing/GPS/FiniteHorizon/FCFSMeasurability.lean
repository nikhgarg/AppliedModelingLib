import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletion
import Mathlib.Tactic

/-!
# Fixed-shape Borel FCFS completion selectors

This module supplies a deliberately narrow Borel interface for the concrete
FCFS consumer.  It does not give a measurable-space instance to variable
lists and does not claim that a random FCFS fold is measurable.  Instead, it
uses a fixed finite list of job-coordinate functions and proves Borel
measurability for the first completed job satisfying a fixed Boolean key.

The scalar selector below is proved equal to a scan of the existing concrete
completion trace.  Consequently it is an exact fixed-shape view of the
executable FCFS completion semantics, not a surrogate queue transition.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Omega JobId : Type*} [MeasurableSpace Omega]

/-- Scan an existing concrete completion list for the first record whose
identifier has the requested fixed key. -/
def finiteGPSFCFSFirstKeyCompletion?
    (key : JobId → Bool) :
    List (FiniteGPSFCFSCompletion JobId) → Option (FiniteGPSFCFSCompletion JobId)
  | [] => none
  | completion :: completions =>
      if key completion.identifier = true then some completion
      else finiteGPSFCFSFirstKeyCompletion? key completions

/-- The response represented by the first keyed record of an existing
concrete completion list, with the literal zero fallback for an empty key
match. -/
def finiteGPSFCFSFirstKeyCompletionResponseFromTrace
    (key : JobId → Bool)
    (completions : List (FiniteGPSFCFSCompletion JobId)) : ℝ :=
  match finiteGPSFCFSFirstKeyCompletion? key completions with
  | some completion => completion.completionTime - completion.arrivalTime
  | none => 0

/-- A scalar first-key completion response computed directly while FCFS walks
a fixed input queue.  Its recursion exactly mirrors
`finiteGPSFCFSCompletedJobsFrom`: a partial head terminates the scan, a
completed keyed head is selected, and every other completed head is removed
before the scan continues. -/
def finiteGPSFCFSFirstKeyCompletionResponse
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore availableService : ℝ) :
    List (FiniteGPSFCFSJob JobId) → ℝ
  | [] => 0
  | job :: jobs =>
      if availableService < job.residualWork then 0
      else if key job.identifier = true then
        segmentStart + (serviceBefore + job.residualWork) / classRate - job.arrivalTime
      else
        finiteGPSFCFSFirstKeyCompletionResponse key segmentStart classRate
          (serviceBefore + job.residualWork)
          (availableService - job.residualWork) jobs

/-- The direct scalar selector is exactly the response obtained by scanning
the existing finite FCFS completion list. -/
theorem finiteGPSFCFSFirstKeyCompletionResponse_eq_completionTraceScan
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    finiteGPSFCFSFirstKeyCompletionResponse key segmentStart classRate
      serviceBefore availableService jobs =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
        (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
          availableService jobs) := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      rfl
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSFirstKeyCompletionResponse,
          finiteGPSFCFSCompletedJobsFrom, hpartial,
          finiteGPSFCFSFirstKeyCompletion?,
          finiteGPSFCFSFirstKeyCompletionResponseFromTrace]
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial]
        by_cases hkey : key job.identifier = true
        · simp [finiteGPSFCFSFirstKeyCompletionResponse, hpartial, hkey,
            finiteGPSFCFSFirstKeyCompletion?,
            finiteGPSFCFSFirstKeyCompletionResponseFromTrace,
            finiteGPSFCFSCompletionOf]
        · simp only [finiteGPSFCFSFirstKeyCompletionResponse, hpartial,
            if_false, hkey]
          simp [finiteGPSFCFSFirstKeyCompletion?,
            finiteGPSFCFSFirstKeyCompletionResponseFromTrace, hkey, ih]

/-- The real-valued coordinates of one fixed queue slot are Borel.  Its
identifier is intentionally not given a measurable-space assumption: only a
fixed Boolean key value is required to select the appropriate scalar branch. -/
def FiniteGPSFCFSFixedQueueCoordinatesMeasurable
    (jobs : List (Omega → FiniteGPSFCFSJob JobId)) : Prop :=
  (∀ job ∈ jobs, Measurable fun omega => (job omega).arrivalTime) ∧
    ∀ job ∈ jobs, Measurable fun omega => (job omega).residualWork

/-- A static queue slot has a source-fixed key value when its identifier may
be read without inspecting the random real coordinates.  This is the
fixed-shape condition used by the Borel induction below. -/
def FiniteGPSFCFSFixedQueueKeyShape
    (key : JobId → Bool)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId)) : Prop :=
  ∀ job ∈ jobs, ∃ keyValue : Bool, ∀ omega, key (job omega).identifier = keyValue

/-- On a fixed finite queue shape, the exact first-key FCFS response selector
is Borel in the segment coordinates and job arrival/work coordinates.  The
list shape and each key branch are static; no measurable list-valued random
object or random full FCFS selector is assumed. -/
theorem measurable_finiteGPSFCFSFirstKeyCompletionResponse_apply
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore availableService : Omega → ℝ)
    (hsegmentStart : Measurable segmentStart)
    (hclassRate : Measurable classRate)
    (hserviceBefore : Measurable serviceBefore)
    (havailableService : Measurable availableService)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId))
    (hcoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs)
    (hkeyShape : FiniteGPSFCFSFixedQueueKeyShape key jobs) :
    Measurable fun omega =>
      finiteGPSFCFSFirstKeyCompletionResponse key
        (segmentStart omega) (classRate omega) (serviceBefore omega)
        (availableService omega) (jobs.map fun job => job omega) := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSFirstKeyCompletionResponse]
  | cons job jobs ih =>
      have harrival : Measurable fun omega => (job omega).arrivalTime :=
        hcoordinates.1 job (by simp)
      have hwork : Measurable fun omega => (job omega).residualWork :=
        hcoordinates.2 job (by simp)
      have hcoordinates_tail : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs := by
        constructor
        · intro later hlater
          exact hcoordinates.1 later (by simp [hlater])
        · intro later hlater
          exact hcoordinates.2 later (by simp [hlater])
      have hkeyShape_tail : FiniteGPSFCFSFixedQueueKeyShape key jobs := by
        intro later hlater
        exact hkeyShape later (by simp [hlater])
      rcases hkeyShape job (by simp) with ⟨keyValue, hkeyValue⟩
      have hpartial : MeasurableSet {omega |
          availableService omega < (job omega).residualWork} :=
        measurableSet_lt havailableService hwork
      have htail := ih
        (serviceBefore := fun omega => serviceBefore omega + (job omega).residualWork)
        (availableService := fun omega =>
          availableService omega - (job omega).residualWork)
        (hserviceBefore := hserviceBefore.add hwork)
        (havailableService := havailableService.sub hwork)
        (hcoordinates := hcoordinates_tail)
        (hkeyShape := hkeyShape_tail)
      have hformula : (fun omega =>
          finiteGPSFCFSFirstKeyCompletionResponse key
            (segmentStart omega) (classRate omega) (serviceBefore omega)
            (availableService omega) ((job :: jobs).map fun slot => slot omega)) =
          fun omega => if availableService omega < (job omega).residualWork then 0
            else if keyValue = true then
              segmentStart omega +
                (serviceBefore omega + (job omega).residualWork) / classRate omega -
                  (job omega).arrivalTime
            else
              finiteGPSFCFSFirstKeyCompletionResponse key
                (segmentStart omega) (classRate omega)
                (serviceBefore omega + (job omega).residualWork)
                (availableService omega - (job omega).residualWork)
                (jobs.map fun slot => slot omega) := by
        funext omega
        simp [finiteGPSFCFSFirstKeyCompletionResponse, hkeyValue omega]
      rw [hformula]
      by_cases hkey : keyValue = true
      · simp only [hkey, ↓reduceIte]
        exact Measurable.ite hpartial measurable_const
          ((hsegmentStart.add ((hserviceBefore.add hwork).div hclassRate)).sub harrival)
      · simp only [hkey]
        exact Measurable.ite hpartial measurable_const htail

end

end AppliedModelingLib.Probability.Queueing
