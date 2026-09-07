import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSMeasurability
import Mathlib.Tactic

/-!
# Fixed-count FCFS consumption skeletons

For a finite ordered FCFS queue, a consumption branch is determined by the
number of heads completed before the one possible partially served head.  This
module makes that finite discrete datum explicit.  It supplies Borel fibers,
fixed-shape coordinate residual queues, and an exact equality to the existing
`finiteGPSFCFSConsume` function.  No alternate FCFS transition is introduced.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Omega JobId : Type*} [MeasurableSpace Omega]

/-- The residual queue obtained when exactly `completedCount` heads are
fully consumed.  When a head remains, it is the unique partially served head;
when all heads are consumed, the result is empty.  This total function is used
only together with the matching branch predicate below. -/
def finiteGPSFCFSConsumeByCount
    (availableService : ℝ) : Nat →
      List (FiniteGPSFCFSJob JobId) → List (FiniteGPSFCFSJob JobId)
  | 0, [] => []
  | 0, job :: jobs =>
      { job with residualWork := job.residualWork - availableService } :: jobs
  | completedCount + 1, [] => []
  | completedCount + 1, job :: jobs =>
      finiteGPSFCFSConsumeByCount (availableService - job.residualWork)
        completedCount jobs

/-- The exact comparison branch conditions for a fixed completed-head count.
This permits zero-work jobs: a zero-work head belongs to the completed prefix,
matching the existing FCFS consumer's non-strict completion branch. -/
def FiniteGPSFCFSConsumeByCountMatches
    (availableService : ℝ) : Nat → List (FiniteGPSFCFSJob JobId) → Prop
  | 0, [] => True
  | 0, job :: _jobs => availableService < job.residualWork
  | completedCount + 1, [] => False
  | completedCount + 1, job :: jobs =>
      ¬ availableService < job.residualWork ∧
        FiniteGPSFCFSConsumeByCountMatches
          (availableService - job.residualWork) completedCount jobs

/-- On the fixed-count branch fiber, the count-based residual queue is
exactly the existing executable FCFS residual queue. -/
theorem finiteGPSFCFSConsume_eq_consumeByCount_of_matches
    (availableService : ℝ) (completedCount : Nat)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hmatches : FiniteGPSFCFSConsumeByCountMatches availableService
      completedCount jobs) :
    finiteGPSFCFSConsume availableService jobs =
      finiteGPSFCFSConsumeByCount availableService completedCount jobs := by
  induction completedCount generalizing availableService jobs with
  | zero =>
      cases jobs with
      | nil => rfl
      | cons job jobs =>
          exact finiteGPSFCFSConsume_eq_partial_head availableService job jobs hmatches
  | succ completedCount ih =>
      cases jobs with
      | nil => simp [FiniteGPSFCFSConsumeByCountMatches] at hmatches
      | cons job jobs =>
          rw [finiteGPSFCFSConsume_eq_after_complete_head availableService job jobs
            hmatches.1]
          exact ih (availableService - job.residualWork) jobs hmatches.2

/-- Every finite FCFS queue lies on at least one completed-count branch.
This is a pointwise finite cover; the accompanying Borel theorem below makes
each fixed branch suitable for later countable gluing. -/
theorem exists_finiteGPSFCFSConsumeByCountMatches
    (availableService : ℝ) (jobs : List (FiniteGPSFCFSJob JobId)) :
    ∃ completedCount,
      FiniteGPSFCFSConsumeByCountMatches availableService completedCount jobs := by
  induction jobs generalizing availableService with
  | nil => exact ⟨0, trivial⟩
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · exact ⟨0, hpartial⟩
      · rcases ih (availableService - job.residualWork) with
          ⟨completedCount, hmatches⟩
        exact ⟨completedCount + 1, hpartial, hmatches⟩

/-- Coordinate-level counterpart of `finiteGPSFCFSConsumeByCount`.  Its list
shape depends only on the fixed count and the fixed input list, while its real
residual coordinates are formed by Borel subtraction. -/
def finiteGPSFCFSConsumeByCountCoordinates
    (availableService : Omega → ℝ) : Nat →
      List (Omega → FiniteGPSFCFSJob JobId) →
        List (Omega → FiniteGPSFCFSJob JobId)
  | 0, [] => []
  | 0, job :: jobs =>
      (fun omega => { job omega with
        residualWork := (job omega).residualWork - availableService omega }) :: jobs
  | completedCount + 1, [] => []
  | completedCount + 1, job :: jobs =>
      finiteGPSFCFSConsumeByCountCoordinates
        (fun omega => availableService omega - (job omega).residualWork)
        completedCount jobs

/-- Evaluating a fixed-count coordinate queue commutes exactly with the
value-level count-based consumer. -/
theorem finiteGPSFCFSConsumeByCountCoordinates_eval
    (availableService : Omega → ℝ) (completedCount : Nat)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId)) (omega : Omega) :
    (finiteGPSFCFSConsumeByCountCoordinates availableService completedCount jobs).map
        (fun job => job omega) =
      finiteGPSFCFSConsumeByCount (availableService omega) completedCount
        (jobs.map fun job => job omega) := by
  induction completedCount generalizing availableService jobs with
  | zero =>
      cases jobs with
      | nil => rfl
      | cons job jobs =>
          simp [finiteGPSFCFSConsumeByCountCoordinates,
            finiteGPSFCFSConsumeByCount]
  | succ completedCount ih =>
      cases jobs with
      | nil => rfl
      | cons job jobs =>
          simpa [finiteGPSFCFSConsumeByCountCoordinates,
            finiteGPSFCFSConsumeByCount] using
            ih (availableService := fun omega =>
              availableService omega - (job omega).residualWork) (jobs := jobs)

/-- The coordinate queue is Borel whenever the input service and fixed queue
coordinates are Borel. -/
theorem finiteGPSFCFSConsumeByCountCoordinates_measurable
    (availableService : Omega → ℝ) (havailableService : Measurable availableService)
    (completedCount : Nat)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId))
    (hcoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs) :
    FiniteGPSFCFSFixedQueueCoordinatesMeasurable
      (finiteGPSFCFSConsumeByCountCoordinates availableService completedCount jobs) := by
  induction completedCount generalizing availableService jobs with
  | zero =>
      cases jobs with
      | nil => simp [finiteGPSFCFSConsumeByCountCoordinates,
          FiniteGPSFCFSFixedQueueCoordinatesMeasurable]
      | cons job jobs =>
          constructor
          · intro outputJob houtputJob
            simp only [finiteGPSFCFSConsumeByCountCoordinates] at houtputJob
            rcases List.mem_cons.mp houtputJob with hhead | htail
            · subst outputJob
              simpa using hcoordinates.1 job (by simp)
            · exact hcoordinates.1 outputJob (by simp [htail])
          · intro outputJob houtputJob
            simp only [finiteGPSFCFSConsumeByCountCoordinates] at houtputJob
            rcases List.mem_cons.mp houtputJob with hhead | htail
            · subst outputJob
              simpa using (hcoordinates.2 job (by simp)).sub havailableService
            · exact hcoordinates.2 outputJob (by simp [htail])
  | succ completedCount ih =>
      cases jobs with
      | nil => simp [finiteGPSFCFSConsumeByCountCoordinates,
          FiniteGPSFCFSFixedQueueCoordinatesMeasurable]
      | cons job jobs =>
          have htailCoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs := by
            constructor
            · intro outputJob houtputJob
              exact hcoordinates.1 outputJob (by simp [houtputJob])
            · intro outputJob houtputJob
              exact hcoordinates.2 outputJob (by simp [houtputJob])
          exact ih
            (availableService := fun omega =>
              availableService omega - (job omega).residualWork)
            ((havailableService.sub (hcoordinates.2 job (by simp))))
            (jobs := jobs) htailCoordinates

/-- Every fixed completed-count branch is a Borel fiber of the real-valued
service and fixed queue coordinates. -/
theorem measurableSet_finiteGPSFCFSConsumeByCountMatches
    (availableService : Omega → ℝ) (havailableService : Measurable availableService)
    (completedCount : Nat)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId))
    (hcoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs) :
    MeasurableSet {omega |
      FiniteGPSFCFSConsumeByCountMatches (availableService omega) completedCount
        (jobs.map fun job => job omega)} := by
  induction completedCount generalizing availableService jobs with
  | zero =>
      cases jobs with
      | nil => simp [FiniteGPSFCFSConsumeByCountMatches]
      | cons job jobs =>
          simpa [FiniteGPSFCFSConsumeByCountMatches] using
            (measurableSet_lt havailableService (hcoordinates.2 job (by simp)))
  | succ completedCount ih =>
      cases jobs with
      | nil => simp [FiniteGPSFCFSConsumeByCountMatches]
      | cons job jobs =>
          have htailCoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs := by
            constructor
            · intro outputJob houtputJob
              exact hcoordinates.1 outputJob (by simp [houtputJob])
            · intro outputJob houtputJob
              exact hcoordinates.2 outputJob (by simp [houtputJob])
          have hcomplete : MeasurableSet {omega |
              ¬ availableService omega < (job omega).residualWork} :=
            (measurableSet_lt havailableService
              (hcoordinates.2 job (by simp))).compl
          have htail := ih
            (availableService := fun omega =>
              availableService omega - (job omega).residualWork)
            (havailableService.sub (hcoordinates.2 job (by simp)))
            (jobs := jobs) htailCoordinates
          have hset : {omega |
              FiniteGPSFCFSConsumeByCountMatches (availableService omega)
                (completedCount + 1) ((job :: jobs).map fun slot => slot omega)} =
              {omega | ¬ availableService omega < (job omega).residualWork} ∩
                {omega | FiniteGPSFCFSConsumeByCountMatches
                  (availableService omega - (job omega).residualWork)
                  completedCount (jobs.map fun slot => slot omega)} := by
            ext omega
            simp [FiniteGPSFCFSConsumeByCountMatches]
          rw [hset]
          exact hcomplete.inter htail

/-- On the fixed Borel branch fiber, evaluating the coordinate residual queue
gives exactly the existing executable FCFS consumer. -/
theorem finiteGPSFCFSConsumeByCountCoordinates_eval_eq_consume_of_matches
    (availableService : Omega → ℝ) (completedCount : Nat)
    (jobs : List (Omega → FiniteGPSFCFSJob JobId)) (omega : Omega)
    (hmatches : FiniteGPSFCFSConsumeByCountMatches (availableService omega)
      completedCount (jobs.map fun job => job omega)) :
    (finiteGPSFCFSConsumeByCountCoordinates availableService completedCount jobs).map
        (fun job => job omega) =
      finiteGPSFCFSConsume (availableService omega)
        (jobs.map fun job => job omega) := by
  rw [finiteGPSFCFSConsumeByCountCoordinates_eval]
  exact (finiteGPSFCFSConsume_eq_consumeByCount_of_matches
    (availableService omega) completedCount (jobs.map fun job => job omega)
    hmatches).symm

end

end AppliedModelingLib.Probability.Queueing
