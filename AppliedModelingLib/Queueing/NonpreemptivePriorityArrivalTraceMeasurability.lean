import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload

/-!
# Borel fixed finite priority traces

This module proves the continuous-coordinate part of finite priority-trace
measurability.  A later stationary-input layer supplies a countable partition
of random arrival ledgers into fixed lists; on each such list, these theorems
show that the literal physical-time workload recursion is Borel.
-/

namespace AppliedModelingLib
namespace Queueing

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ} {JobId : Type*}

/-- Borel real-coordinate requirements for one job in a fixed finite trace.
Identifiers and class labels are static data in this interface, so no
measurable-space structure on them is required. -/
def NonpreemptivePriorityJob.CoordinatesMeasurable
    (job : Ω → NonpreemptivePriorityJob n JobId) : Prop :=
  Measurable (fun omega => (job omega).arrivalTime) ∧
    Measurable (fun omega => (job omega).serviceWork)

/-- Evaluate a fixed list of job-coordinate maps at one sample. -/
def evaluateNonpreemptivePriorityJobList
    (jobs : List (Ω → NonpreemptivePriorityJob n JobId)) (omega : Ω) :
    List (NonpreemptivePriorityJob n JobId) :=
  jobs.map fun job => job omega

/-- The physical epoch after a fixed finite coordinate trace is measurable. -/
theorem measurable_nonpreemptivePriorityArrivalTraceEndTime_eval
    (time : Ω → ℝ) (htime : Measurable time)
    (jobs : List (Ω → NonpreemptivePriorityJob n JobId))
    (hjobs : ∀ job ∈ jobs, NonpreemptivePriorityJob.CoordinatesMeasurable job) :
    Measurable (fun omega => nonpreemptivePriorityArrivalTraceEndTime
      (time omega) (evaluateNonpreemptivePriorityJobList jobs omega)) := by
  induction jobs generalizing time with
  | nil =>
      simpa [evaluateNonpreemptivePriorityJobList,
        nonpreemptivePriorityArrivalTraceEndTime] using htime
  | cons job jobs ih =>
      have hhead : NonpreemptivePriorityJob.CoordinatesMeasurable job := hjobs job (by simp)
      have htail : ∀ later ∈ jobs, NonpreemptivePriorityJob.CoordinatesMeasurable later := by
        intro later hlater
        exact hjobs later (by simp [hlater])
      simpa [evaluateNonpreemptivePriorityJobList,
        nonpreemptivePriorityArrivalTraceEndTime] using
        ih (fun omega => (job omega).arrivalTime) hhead.1 htail

/-- The scalar workload after a fixed finite coordinate trace is measurable.
This is the literal reflected recursion, with no discrete-time batching or
queue-state measurability assumption. -/
theorem measurable_nonpreemptivePriorityArrivalTraceResidualWork_eval
    (time workload : Ω → ℝ) (htime : Measurable time)
    (hworkload : Measurable workload)
    (jobs : List (Ω → NonpreemptivePriorityJob n JobId))
    (hjobs : ∀ job ∈ jobs, NonpreemptivePriorityJob.CoordinatesMeasurable job) :
    Measurable (fun omega => nonpreemptivePriorityArrivalTraceResidualWork
      (time omega) (workload omega)
      (evaluateNonpreemptivePriorityJobList jobs omega)) := by
  induction jobs generalizing time workload with
  | nil =>
      simpa [evaluateNonpreemptivePriorityJobList,
        nonpreemptivePriorityArrivalTraceResidualWork] using hworkload
  | cons job jobs ih =>
      have hhead : NonpreemptivePriorityJob.CoordinatesMeasurable job := hjobs job (by simp)
      have htail : ∀ later ∈ jobs, NonpreemptivePriorityJob.CoordinatesMeasurable later := by
        intro later hlater
        exact hjobs later (by simp [hlater])
      have hnext : Measurable (fun omega =>
          max 0 (workload omega - ((job omega).arrivalTime - time omega)) +
            (job omega).serviceWork) :=
        (measurable_const.max (hworkload.sub (hhead.1.sub htime))).add hhead.2
      simpa [evaluateNonpreemptivePriorityJobList,
        nonpreemptivePriorityArrivalTraceResidualWork] using
        ih (fun omega => (job omega).arrivalTime) (fun omega =>
          max 0 (workload omega - ((job omega).arrivalTime - time omega)) +
            (job omega).serviceWork)
          hhead.1 hnext htail

/-- The terminal workload of a fixed finite coordinate trace is measurable. -/
theorem measurable_nonpreemptivePriorityArrivalTraceTerminalResidualWork_eval
    (time workload terminalTime : Ω → ℝ)
    (htime : Measurable time) (hworkload : Measurable workload)
    (hterminalTime : Measurable terminalTime)
    (jobs : List (Ω → NonpreemptivePriorityJob n JobId))
    (hjobs : ∀ job ∈ jobs, NonpreemptivePriorityJob.CoordinatesMeasurable job) :
    Measurable (fun omega => nonpreemptivePriorityArrivalTraceTerminalResidualWork
      (time omega) (workload omega)
      (evaluateNonpreemptivePriorityJobList jobs omega) (terminalTime omega)) := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  exact measurable_const.max
    ((measurable_nonpreemptivePriorityArrivalTraceResidualWork_eval
      time workload htime hworkload jobs hjobs).sub
      (hterminalTime.sub
        (measurable_nonpreemptivePriorityArrivalTraceEndTime_eval
          time htime jobs hjobs)))

end

end Queueing
end AppliedModelingLib
