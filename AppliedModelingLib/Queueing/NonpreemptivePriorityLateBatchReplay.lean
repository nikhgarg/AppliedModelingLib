import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload
import AppliedModelingLib.Queueing.Lindley.RemotePastInitialCoupling

/-!
# Finite late-batch replays as physical arrival traces

This module realizes a finite scalar late-batch recurrence as a chronological
arrival trace with literal interarrival durations.  It is deterministic and
does not assume a probability law or a queueing discipline beyond
work-conserving scalar workload accounting.
-/

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability.Queueing
open scoped BigOperators

noncomputable section

/-- The first `N` marked arrivals of a late-batch input, with their physical
epochs obtained by accumulating the intervening service durations. -/
def lateBatchArrivalTraceJobs
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) (N : ℕ) :
    List (NonpreemptivePriorityJob n ℕ) :=
  (List.range N).map fun index =>
    { identifier := index
      priority := priority
      arrivalTime := ∑ j ∈ Finset.range index, service j
      serviceWork := batch index }

/-- The terminal epoch just before the next late-batch arrival. -/
def lateBatchArrivalTraceTerminalTime (service : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, service j

/-- Translate the physical epoch of one arrival while retaining all workload
data and its queueing label. -/
def nonpreemptivePriorityJobTranslateArrivalTime
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) : NonpreemptivePriorityJob n JobId :=
  { identifier := job.identifier
    priority := job.priority
    arrivalTime := job.arrivalTime + offset
    serviceWork := job.serviceWork }

theorem nonpreemptivePriorityArrivalTraceResidualWork_map_translateArrivalTime
    {n : ℕ} {JobId : Type*} (offset time workload : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceResidualWork (time + offset) workload
      (jobs.map (nonpreemptivePriorityJobTranslateArrivalTime offset)) =
      nonpreemptivePriorityArrivalTraceResidualWork time workload jobs := by
  induction jobs generalizing time workload with
  | nil => rfl
  | cons job jobs ih =>
      simp only [List.map_cons, nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityJobTranslateArrivalTime]
      rw [show job.arrivalTime + offset - (time + offset) = job.arrivalTime - time by ring]
      exact ih job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)

theorem nonpreemptivePriorityArrivalTraceEndTime_map_translateArrivalTime
    {n : ℕ} {JobId : Type*} (offset time : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceEndTime (time + offset)
      (jobs.map (nonpreemptivePriorityJobTranslateArrivalTime offset)) =
      nonpreemptivePriorityArrivalTraceEndTime time jobs + offset := by
  induction jobs generalizing time with
  | nil => rfl
  | cons job jobs ih =>
      simp only [List.map_cons, nonpreemptivePriorityArrivalTraceEndTime,
        nonpreemptivePriorityJobTranslateArrivalTime]
      exact ih job.arrivalTime

theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_map_translateArrivalTime
    {n : ℕ} {JobId : Type*} (offset time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (time + offset) workload
      (jobs.map (nonpreemptivePriorityJobTranslateArrivalTime offset))
      (terminalTime + offset) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs terminalTime := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  rw [nonpreemptivePriorityArrivalTraceResidualWork_map_translateArrivalTime,
    nonpreemptivePriorityArrivalTraceEndTime_map_translateArrivalTime]
  congr 2
  ring

theorem lateBatchArrivalTraceJobs_succ
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) (N : ℕ) :
    lateBatchArrivalTraceJobs priority batch service (N + 1) =
      lateBatchArrivalTraceJobs priority batch service N ++
        [{ identifier := N
           priority := priority
           arrivalTime := lateBatchArrivalTraceTerminalTime service N
           serviceWork := batch N }] := by
  simp [lateBatchArrivalTraceJobs, lateBatchArrivalTraceTerminalTime,
    List.range_succ]

theorem lateBatchArrivalTraceTerminalTime_succ
    (service : ℕ → ℝ) (N : ℕ) :
    lateBatchArrivalTraceTerminalTime service (N + 1) =
      lateBatchArrivalTraceTerminalTime service N + service N := by
  simp [lateBatchArrivalTraceTerminalTime, Finset.sum_range_succ]

/-- Appending one arrival evaluates the preceding trace at that arrival epoch,
then adds the new work and serves until the stated terminal time. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_append_singleton
    {n : ℕ} {JobId : Type*} (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
      (jobs ++ [job]) terminalTime =
      max 0
        (nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs
          job.arrivalTime + job.serviceWork - (terminalTime - job.arrivalTime)) := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  rw [nonpreemptivePriorityArrivalTraceResidualWork_append,
    nonpreemptivePriorityArrivalTraceEndTime_append]
  simp only [nonpreemptivePriorityArrivalTraceResidualWork,
    nonpreemptivePriorityArrivalTraceEndTime]

/-- With no initial work, moving the start time forward to the first arrival
does not alter the terminal workload. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_zero_start_eq_firstArrival
    {n : ℕ} {JobId : Type*} (time terminalTime : ℝ)
    (job : NonpreemptivePriorityJob n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hstart : time ≤ job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0
      (job :: jobs) terminalTime =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork job.arrivalTime 0
        (job :: jobs) terminalTime := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  change max 0
      (nonpreemptivePriorityArrivalTraceResidualWork job.arrivalTime
        (max 0 (0 - (job.arrivalTime - time)) + job.serviceWork) jobs -
        (terminalTime - nonpreemptivePriorityArrivalTraceEndTime job.arrivalTime jobs)) = _
  rw [max_eq_left (by linarith : 0 - (job.arrivalTime - time) ≤ 0)]
  simp [nonpreemptivePriorityArrivalTraceResidualWork,
    nonpreemptivePriorityArrivalTraceEndTime]

/-- A finite chronological physical replay has exactly the late-batch
pre-arrival workload at its terminal epoch. -/
theorem lateBatchArrivalTraceTerminalResidualWork_eq_lateBatchPreWorkload
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) : ∀ N : ℕ,
    nonpreemptivePriorityArrivalTraceTerminalResidualWork 0 0
      (lateBatchArrivalTraceJobs priority batch service N)
      (lateBatchArrivalTraceTerminalTime service N) =
      lateBatchPreWorkload batch service N := by
  intro N
  induction N with
  | zero =>
      simp [lateBatchArrivalTraceJobs, lateBatchArrivalTraceTerminalTime,
        nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime, lateBatchPreWorkload]
  | succ N ih =>
      rw [lateBatchArrivalTraceJobs_succ,
        lateBatchArrivalTraceTerminalTime_succ,
        nonpreemptivePriorityArrivalTraceTerminalResidualWork_append_singleton]
      simp only
      rw [show lateBatchArrivalTraceTerminalTime service N + service N -
          lateBatchArrivalTraceTerminalTime service N = service N by ring]
      rw [ih, ← lateBatchPostWorkload_eq_pre_add_batch]
      rw [max_comm]
      exact (lateBatchPreWorkload_succ batch service N).symm

/-- The same late-batch replay identity holds at any translated physical-time
origin. -/
theorem lateBatchArrivalTraceTerminalResidualWork_translate_eq_lateBatchPreWorkload
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ)
    (offset : ℝ) (N : ℕ) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork offset 0
      ((lateBatchArrivalTraceJobs priority batch service N).map
        (nonpreemptivePriorityJobTranslateArrivalTime offset))
      (lateBatchArrivalTraceTerminalTime service N + offset) =
      lateBatchPreWorkload batch service N := by
  calc
    nonpreemptivePriorityArrivalTraceTerminalResidualWork offset 0
        ((lateBatchArrivalTraceJobs priority batch service N).map
          (nonpreemptivePriorityJobTranslateArrivalTime offset))
        (lateBatchArrivalTraceTerminalTime service N + offset) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork 0 0
        (lateBatchArrivalTraceJobs priority batch service N)
        (lateBatchArrivalTraceTerminalTime service N) := by
          simpa using
            (nonpreemptivePriorityArrivalTraceTerminalResidualWork_map_translateArrivalTime
              offset 0 0 (lateBatchArrivalTraceTerminalTime service N)
              (lateBatchArrivalTraceJobs priority batch service N))
    _ = lateBatchPreWorkload batch service N :=
      lateBatchArrivalTraceTerminalResidualWork_eq_lateBatchPreWorkload
        priority batch service N

/-- The literal physical trace generated by a finite block of an input indexed
outward from the observation epoch.  Its first list entry is the oldest input
point and its terminal epoch is zero. -/
def reverseRemotePastArrivalTraceJobs
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) (N : ℕ) :
    List (NonpreemptivePriorityJob n ℕ) :=
  (lateBatchArrivalTraceJobs priority
    (reverseRemotePastIncrement batch N)
    (reverseRemotePastIncrement service N) N).map fun job =>
      { identifier := job.identifier
        priority := job.priority
        arrivalTime := job.arrivalTime -
          lateBatchArrivalTraceTerminalTime
            (reverseRemotePastIncrement service N) N
        serviceWork := job.serviceWork }

/-- The duration of a reversed finite block is its outward cumulative input
duration. -/
theorem lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement
    (service : ℕ → ℝ) (N : ℕ) :
    lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N =
      remotePastCumulativeNetInput service N := by
  unfold lateBatchArrivalTraceTerminalTime
  simpa [remotePastCumulativeNetInput] using
    (sum_range_reverseRemotePastIncrement_eq_cumulative_sub service 0 N (zero_le N))

/-- The reverse remote-past physical trace has exactly the actual backwards
arrival epochs and marks of its finite input block. -/
theorem reverseRemotePastArrivalTraceJobs_eq_reverseRange
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) (N : ℕ) :
    reverseRemotePastArrivalTraceJobs priority batch service N =
      (List.range N).reverse.map fun index =>
        { identifier := N - (index + 1)
          priority := priority
          arrivalTime := -remotePastCumulativeNetInput service (index + 1)
          serviceWork := batch index } := by
  unfold reverseRemotePastArrivalTraceJobs lateBatchArrivalTraceJobs
  rw [List.range_eq_range', List.reverse_range']
  simp only [List.map_map]
  rw [← List.range_eq_range']
  apply List.map_congr_left
  intro index hindex
  have hindex_lt : index < N := by
    simpa only [List.mem_range] using hindex
  have hprefix :
      Finset.sum (Finset.range index) (reverseRemotePastIncrement service N) =
        remotePastCumulativeNetInput service N -
          remotePastCumulativeNetInput service (N - index) := by
    have hsum := sum_range_reverseRemotePastIncrement_eq_cumulative_sub service
      (N - index) N (Nat.sub_le _ _)
    have hlength : N - (N - index) = index := by omega
    simpa [hlength] using hsum
  have hterminal :
      lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N =
        remotePastCumulativeNetInput service N :=
    lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement service N
  have harrival :
      Finset.sum (Finset.range index) (reverseRemotePastIncrement service N) -
        lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N =
          -remotePastCumulativeNetInput service (N - index) := by
    rw [hprefix, hterminal]
    ring
  simp only [Function.comp_apply]
  rw [harrival]
  have hshift : 0 + N - 1 - index + 1 = N - index := by omega
  congr 1
  · rw [hshift]
    omega
  · congr 1
    rw [hshift]
  · unfold reverseRemotePastIncrement
    congr 1
    omega

/-- The terminal workload of a literal reverse remote-past trace is its
finite late-batch pre-arrival workload. -/
theorem reverseRemotePastArrivalTraceTerminalResidualWork_eq_lateBatchPreWorkload
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ) (N : ℕ) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      (-lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N) 0
      (reverseRemotePastArrivalTraceJobs priority batch service N) 0 =
      lateBatchPreWorkload
        (reverseRemotePastIncrement batch N)
        (reverseRemotePastIncrement service N) N := by
  unfold reverseRemotePastArrivalTraceJobs
  let terminalTime := lateBatchArrivalTraceTerminalTime
    (reverseRemotePastIncrement service N) N
  have htranslate :=
    lateBatchArrivalTraceTerminalResidualWork_translate_eq_lateBatchPreWorkload
      priority (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N) (-terminalTime) N
  change nonpreemptivePriorityArrivalTraceTerminalResidualWork (-terminalTime) 0
    ((lateBatchArrivalTraceJobs priority
      (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N) N).map _) 0 = _
  have hjobs :
      (lateBatchArrivalTraceJobs priority
        (reverseRemotePastIncrement batch N)
        (reverseRemotePastIncrement service N) N).map (fun job =>
          { identifier := job.identifier
            priority := job.priority
            arrivalTime := job.arrivalTime - terminalTime
            serviceWork := job.serviceWork }) =
        (lateBatchArrivalTraceJobs priority
          (reverseRemotePastIncrement batch N)
          (reverseRemotePastIncrement service N) N).map
          (nonpreemptivePriorityJobTranslateArrivalTime (-terminalTime)) := by
        apply List.map_congr_left
        intro job _
        rfl
  rw [hjobs]
  simpa [terminalTime] using htranslate

/-- An empty trace begun before the oldest arrival of a nonempty reverse
remote-past block has the same terminal workload as one begun at that arrival. -/
theorem reverseRemotePastArrivalTraceTerminalResidualWork_zero_start_eq_oldest
    {n : ℕ} (priority : Fin n) (batch service : ℕ → ℝ)
    (time : ℝ) (N : ℕ) (hN : 0 < N)
    (hstart : time ≤
      -lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0
      (reverseRemotePastArrivalTraceJobs priority batch service N) 0 =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-lateBatchArrivalTraceTerminalTime (reverseRemotePastIncrement service N) N) 0
        (reverseRemotePastArrivalTraceJobs priority batch service N) 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN) with ⟨M, rfl⟩
  rw [reverseRemotePastArrivalTraceJobs_eq_reverseRange]
  have hterminal := lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement
    service (M + 1)
  rw [show (List.range (M + 1)).reverse = M :: (List.range M).reverse by
    simp [List.range_succ]]
  change nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0
      ({ identifier := M + 1 - (M + 1)
         priority := priority
         arrivalTime := -remotePastCumulativeNetInput service (M + 1)
         serviceWork := batch M } :: _) 0 = _
  have hhead : time ≤ -remotePastCumulativeNetInput service (M + 1) := by
    calc
      time ≤ -lateBatchArrivalTraceTerminalTime
          (reverseRemotePastIncrement service (M + 1)) (M + 1) := by
            simpa using hstart
      _ = -remotePastCumulativeNetInput service (M + 1) := by rw [hterminal]
  rw [hterminal]
  simp only [List.map_cons]
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_zero_start_eq_firstArrival
  exact hhead

end

end AppliedModelingLib.Queueing
