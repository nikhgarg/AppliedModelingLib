import AppliedModelingLib.Queueing.NonpreemptivePriorityServiceAccounting

/-!
# Physical-time workload recursion for finite priority traces

This module records the scalar workload recursion at the literal epochs of a
finite arrival list.  It does not batch arrivals into artificial time bins:
between consecutive arrivals the work-conserving server supplies precisely the
elapsed service capacity, and the next job then contributes its marked work.
-/

namespace AppliedModelingLib
namespace Queueing

/-- Scalar unfinished work after processing a chronological finite arrival
trace from a specified physical time and workload. -/
def nonpreemptivePriorityArrivalTraceResidualWork
    {n : ℕ} {JobId : Type*} :
    ℝ → ℝ → List (NonpreemptivePriorityJob n JobId) → ℝ
  | _, workload, [] => workload
  | time, workload, job :: jobs =>
      nonpreemptivePriorityArrivalTraceResidualWork job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork) jobs

/-- The physical epoch immediately after processing a finite arrival list. -/
def nonpreemptivePriorityArrivalTraceEndTime
    {n : ℕ} {JobId : Type*} :
    ℝ → List (NonpreemptivePriorityJob n JobId) → ℝ
  | time, [] => time
  | _, job :: jobs => nonpreemptivePriorityArrivalTraceEndTime job.arrivalTime jobs

/-- Residual work at a prescribed terminal physical time after a finite
arrival trace and the intervening work-conserving service. -/
def nonpreemptivePriorityArrivalTraceTerminalResidualWork
    {n : ℕ} {JobId : Type*}
    (time workload : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminalTime : ℝ) : ℝ :=
  max 0 (nonpreemptivePriorityArrivalTraceResidualWork time workload jobs -
    (terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs))

/-- Relabel a finite priority-trace job without changing its class, physical
arrival time, or service requirement.  Scalar workload observables depend on
those latter three coordinates only. -/
def nonpreemptivePriorityJobMapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (job : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityJob n JobId' :=
  { identifier := f job.identifier
    priority := job.priority
    arrivalTime := job.arrivalTime
    serviceWork := job.serviceWork }

/-- Relabelling the identifiers in a finite trace leaves its scalar workload
recursion unchanged.  This separates the physical workload calculation from
the particular stream labels used to enumerate an input path. -/
theorem nonpreemptivePriorityArrivalTraceResidualWork_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (time workload : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceResidualWork time workload
        (jobs.map (nonpreemptivePriorityJobMapIdentifier f)) =
      nonpreemptivePriorityArrivalTraceResidualWork time workload jobs := by
  induction jobs generalizing time workload with
  | nil => rfl
  | cons job jobs ih =>
      simp only [List.map_cons, nonpreemptivePriorityArrivalTraceResidualWork]
      exact ih job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)

/-- Relabelling a finite trace preserves the physical epoch of its last
arrival. -/
theorem nonpreemptivePriorityArrivalTraceEndTime_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (time : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceEndTime time
        (jobs.map (nonpreemptivePriorityJobMapIdentifier f)) =
      nonpreemptivePriorityArrivalTraceEndTime time jobs := by
  induction jobs generalizing time with
  | nil => rfl
  | cons job jobs ih =>
      simpa [nonpreemptivePriorityArrivalTraceEndTime] using ih job.arrivalTime

/-- Consequently, relabelling leaves the terminal scalar workload of a
finite physical trace unchanged. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
        (jobs.map (nonpreemptivePriorityJobMapIdentifier f)) terminalTime =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs terminalTime := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  rw [nonpreemptivePriorityArrivalTraceResidualWork_mapIdentifier,
    nonpreemptivePriorityArrivalTraceEndTime_mapIdentifier]

/-- Splitting a nonnegative elapsed service interval at an intermediate time
does not change the reflected scalar workload. -/
theorem max_zero_sub_split_elapsed_time
    (workload startTime splitTime terminalTime : ℝ)
    (hstart : startTime ≤ splitTime) (hsplit : splitTime ≤ terminalTime) :
    max 0 (max 0 (workload - (splitTime - startTime)) -
      (terminalTime - splitTime)) =
      max 0 (workload - (terminalTime - startTime)) := by
  have hrewrite : workload - (terminalTime - startTime) =
      (workload - (splitTime - startTime)) - (terminalTime - splitTime) := by
    ring
  rw [hrewrite]
  by_cases hwork : 0 ≤ workload - (splitTime - startTime)
  · rw [max_eq_right hwork]
  · have hwork' : workload - (splitTime - startTime) ≤ 0 := le_of_not_ge hwork
    rw [max_eq_left hwork']
    have hterminal : workload - (splitTime - startTime) -
        (terminalTime - splitTime) ≤ 0 := by
      linarith
    rw [max_eq_left (by linarith : 0 - (terminalTime - splitTime) ≤ 0),
      max_eq_left hterminal]

/-- The physical epoch after a concatenated arrival trace is the epoch after
the prefix, continued through the suffix. -/
theorem nonpreemptivePriorityArrivalTraceEndTime_append
    {n : ℕ} {JobId : Type*}
    (time : ℝ) (front suffix : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceEndTime time (front ++ suffix) =
      nonpreemptivePriorityArrivalTraceEndTime
        (nonpreemptivePriorityArrivalTraceEndTime time front) suffix := by
  induction front generalizing time with
  | nil =>
      simp [nonpreemptivePriorityArrivalTraceEndTime]
  | cons job front ih =>
      simpa [nonpreemptivePriorityArrivalTraceEndTime] using ih job.arrivalTime

/-- The terminal epoch of a finite trace remains below any common upper bound
on its initial epoch and all arrival epochs. -/
theorem nonpreemptivePriorityArrivalTraceEndTime_le
    {n : ℕ} {JobId : Type*}
    (time bound : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time ≤ bound)
    (hjobs : ∀ job ∈ jobs, job.arrivalTime ≤ bound) :
    nonpreemptivePriorityArrivalTraceEndTime time jobs ≤ bound := by
  induction jobs generalizing time with
  | nil =>
      simpa [nonpreemptivePriorityArrivalTraceEndTime] using htime
  | cons job jobs ih =>
      apply ih job.arrivalTime
      · exact hjobs job (by simp)
      · intro other hother
        exact hjobs other (by simp [hother])

/-- A chronologically executed finite trace records the physical epoch of its
last arrival (or its initial epoch for an empty trace). -/
theorem runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime)) :
    (runNonpreemptivePriorityArrivalTrace initial jobs).currentTime =
      nonpreemptivePriorityArrivalTraceEndTime initial.currentTime jobs := by
  induction jobs generalizing initial with
  | nil =>
      simp [runNonpreemptivePriorityArrivalTrace,
        nonpreemptivePriorityArrivalTraceEndTime]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmittedTime : admitted.currentTime = job.arrivalTime := by
        simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using
          advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
            (totalNonpreemptivePriorityWorkJobs initial) initial job
            (hstart job (by simp)) le_rfl
      have hadmittedStart : ∀ other ∈ jobs, admitted.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hadmittedTime]
        exact hhead other hother
      calc
        (runNonpreemptivePriorityArrivalTrace initial (job :: jobs)).currentTime =
            (runNonpreemptivePriorityArrivalTrace admitted jobs).currentTime := by
              simp [runNonpreemptivePriorityArrivalTrace, advanced, admitted,
                advanceThenAdmitNonpreemptivePriorityJob]
        _ = nonpreemptivePriorityArrivalTraceEndTime admitted.currentTime jobs :=
              ih admitted hadmittedStart htail
        _ = nonpreemptivePriorityArrivalTraceEndTime job.arrivalTime jobs := by
              rw [hadmittedTime]
        _ = nonpreemptivePriorityArrivalTraceEndTime initial.currentTime (job :: jobs) := by
              rfl

/-- Processing a concatenated physical arrival trace is exactly processing its
prefix and then continuing the suffix from the prefix's terminal epoch and
residual workload. -/
theorem nonpreemptivePriorityArrivalTraceResidualWork_append
    {n : ℕ} {JobId : Type*}
    (time workload : ℝ) (front suffix : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceResidualWork time workload (front ++ suffix) =
      nonpreemptivePriorityArrivalTraceResidualWork
        (nonpreemptivePriorityArrivalTraceEndTime time front)
        (nonpreemptivePriorityArrivalTraceResidualWork time workload front) suffix := by
  induction front generalizing time workload with
  | nil =>
      simp [nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime]
  | cons job tail ih =>
      simpa [nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime] using
        ih job.arrivalTime
          (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)

/-- A literal empty state at the end of a finite arrival prefix is a genuine
restart point for every following physical arrival suffix. -/
theorem nonpreemptivePriorityArrivalTraceResidualWork_restart_of_prefix_eq_zero
    {n : ℕ} {JobId : Type*}
    (time workload : ℝ) (front suffix : List (NonpreemptivePriorityJob n JobId))
    (hreset : nonpreemptivePriorityArrivalTraceResidualWork time workload front = 0) :
    nonpreemptivePriorityArrivalTraceResidualWork time workload (front ++ suffix) =
      nonpreemptivePriorityArrivalTraceResidualWork
        (nonpreemptivePriorityArrivalTraceEndTime time front) 0 suffix := by
  rw [nonpreemptivePriorityArrivalTraceResidualWork_append, hreset]

/-- Moving the start of a terminal physical-time computation forward through
an arrival-free interval gives the same final workload, provided every
remaining arrival lies at or after the new start. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_shift_start
    {n : ℕ} {JobId : Type*}
    (time splitTime terminalTime workload : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time ≤ splitTime) (hsplit : splitTime ≤ terminalTime)
    (hjobs : ∀ job ∈ jobs, splitTime ≤ job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      time workload jobs terminalTime =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork splitTime
        (max 0 (workload - (splitTime - time))) jobs terminalTime := by
  cases jobs with
  | nil =>
      simpa [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime] using
        (max_zero_sub_split_elapsed_time workload time splitTime terminalTime htime hsplit).symm
  | cons job jobs =>
      have hjob : splitTime ≤ job.arrivalTime := hjobs job (by simp)
      simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime]
      rw [max_zero_sub_split_elapsed_time workload time splitTime job.arrivalTime htime hjob]

/-- Terminal physical workload composes exactly across an arrival-free cut
between a finite prefix and a suffix whose arrivals occur after that cut. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_append
    {n : ℕ} {JobId : Type*}
    (time splitTime terminalTime workload : ℝ)
    (front suffix : List (NonpreemptivePriorityJob n JobId))
    (hfront : nonpreemptivePriorityArrivalTraceEndTime time front ≤ splitTime)
    (hsplit : splitTime ≤ terminalTime)
    (hsuffix : ∀ job ∈ suffix, splitTime ≤ job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      time workload (front ++ suffix) terminalTime =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork splitTime
        (nonpreemptivePriorityArrivalTraceTerminalResidualWork
          time workload front splitTime) suffix terminalTime := by
  unfold nonpreemptivePriorityArrivalTraceTerminalResidualWork
  rw [nonpreemptivePriorityArrivalTraceResidualWork_append,
    nonpreemptivePriorityArrivalTraceEndTime_append]
  exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_shift_start
    (nonpreemptivePriorityArrivalTraceEndTime time front) splitTime terminalTime
    (nonpreemptivePriorityArrivalTraceResidualWork time workload front)
    suffix hfront hsplit hsuffix

/-- Delaying a nonnegative batch of work to the end of two consecutive
service intervals can only increase the reflected scalar workload. -/
theorem max_zero_sub_add_le_virtual_end_batch
    (workload firstElapsed secondElapsed batchWork : ℝ)
    (hfirst : 0 ≤ firstElapsed) (hsecond : 0 ≤ secondElapsed)
    (hbatch : 0 ≤ batchWork) :
    max 0 (max 0 (workload - firstElapsed) + batchWork - secondElapsed) ≤
      max 0 (workload - (firstElapsed + secondElapsed)) + batchWork := by
  apply max_le
  · linarith [le_max_left 0 (workload - (firstElapsed + secondElapsed))]
  · have hinner : max 0 (workload - firstElapsed) - secondElapsed ≤
        max 0 (workload - firstElapsed - secondElapsed) := by
      by_cases hwork : 0 ≤ workload - firstElapsed
      · rw [max_eq_right hwork]
        exact le_max_right _ _
      · rw [max_eq_left (le_of_not_ge hwork)]
        exact le_trans (by linarith) (le_max_left _ _)
    calc
      max 0 (workload - firstElapsed) + batchWork - secondElapsed =
          (max 0 (workload - firstElapsed) - secondElapsed) + batchWork := by
            ring
      _ ≤ max 0 (workload - firstElapsed - secondElapsed) + batchWork := by
            linarith
      _ = max 0 (workload - (firstElapsed + secondElapsed)) + batchWork := by
            congr 2
            ring

/-- Total marked service work in a finite arrival ledger. -/
def nonpreemptivePriorityArrivalTraceServiceWork
    {n : ℕ} {JobId : Type*}
    (jobs : List (NonpreemptivePriorityJob n JobId)) : ℝ :=
  (jobs.map fun job => job.serviceWork).sum

/-- A finite physical arrival trace is bounded above by the workload obtained
by delaying all of its nonnegative marked work to its terminal epoch. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_virtualEndBatch
    {n : ℕ} {JobId : Type*}
    (time terminalTime workload : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime)
    (hservice : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs terminalTime ≤
      max 0 (workload - (terminalTime - time)) +
        nonpreemptivePriorityArrivalTraceServiceWork jobs := by
  induction jobs generalizing time workload with
  | nil =>
      simp [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime,
        nonpreemptivePriorityArrivalTraceServiceWork]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      have hjobStart : time ≤ job.arrivalTime := hstart job (by simp)
      have hjobEnd : job.arrivalTime ≤ terminalTime := hend job (by simp)
      have htailStart : ∀ other ∈ jobs, job.arrivalTime ≤ other.arrivalTime := by
        intro other hother
        exact hhead other hother
      have htailEnd : ∀ other ∈ jobs, other.arrivalTime ≤ terminalTime := by
        intro other hother
        exact hend other (by simp [hother])
      have htailService : ∀ other ∈ jobs, 0 ≤ other.serviceWork := by
        intro other hother
        exact hservice other (by simp [hother])
      have hrec := ih job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)
        htailStart htail htailEnd htailService
      calc
        nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
            (job :: jobs) terminalTime =
            nonpreemptivePriorityArrivalTraceTerminalResidualWork job.arrivalTime
              (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)
              jobs terminalTime := by
                rfl
        _ ≤ max 0 ((max 0 (workload - (job.arrivalTime - time)) + job.serviceWork) -
              (terminalTime - job.arrivalTime)) +
              nonpreemptivePriorityArrivalTraceServiceWork jobs := hrec
        _ ≤ max 0 (workload - (terminalTime - time)) + job.serviceWork +
              nonpreemptivePriorityArrivalTraceServiceWork jobs := by
                gcongr
                have hbound := max_zero_sub_add_le_virtual_end_batch workload
                  (job.arrivalTime - time) (terminalTime - job.arrivalTime)
                  job.serviceWork (by linarith) (by linarith)
                  (hservice job (by simp))
                have helapsed : job.arrivalTime - time +
                    (terminalTime - job.arrivalTime) = terminalTime - time := by
                  ring
                simpa [helapsed] using hbound
        _ = max 0 (workload - (terminalTime - time)) +
              nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) := by
                simp [nonpreemptivePriorityArrivalTraceServiceWork]
                ring

/-- The scalar physical-time workload is unchanged by swapping two jobs that
arrive at the same epoch.  Thus its interval decomposition does not depend on
the priority trace's deterministic convention for simultaneous arrivals. -/
theorem nonpreemptivePriorityArrivalTraceResidualWork_swap_equal_arrivalTime
    {n : ℕ} {JobId : Type*}
    (time workload : ℝ)
    (first second : NonpreemptivePriorityJob n JobId)
    (suffix : List (NonpreemptivePriorityJob n JobId))
    (htime : first.arrivalTime = second.arrivalTime)
    (hfirst : 0 ≤ first.serviceWork) (hsecond : 0 ≤ second.serviceWork) :
    nonpreemptivePriorityArrivalTraceResidualWork time workload (first :: second :: suffix) =
      nonpreemptivePriorityArrivalTraceResidualWork time workload (second :: first :: suffix) := by
  simp only [nonpreemptivePriorityArrivalTraceResidualWork]
  rw [htime]
  simp only [sub_self, sub_zero]
  have hbase : 0 ≤ max 0 (workload - (second.arrivalTime - time)) := le_max_left _ _
  have hfirstNonneg : 0 ≤
      max 0 (workload - (second.arrivalTime - time)) + first.serviceWork :=
    add_nonneg hbase hfirst
  have hsecondNonneg : 0 ≤
      max 0 (workload - (second.arrivalTime - time)) + second.serviceWork :=
    add_nonneg hbase hsecond
  rw [max_eq_right hfirstNonneg, max_eq_right hsecondNonneg]
  congr 1
  ring

/-- The deterministic finite priority execution has exactly the scalar
physical-time workload recursion whenever the supplied arrivals are
chronological and carry positive service work. -/
theorem totalNonpreemptivePriorityResidualWork_run_eq_arrivalTraceResidualWork
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      nonpreemptivePriorityArrivalTraceResidualWork initial.currentTime
        (totalNonpreemptivePriorityResidualWork initial) jobs := by
  induction jobs generalizing initial with
  | nil =>
      simp [runNonpreemptivePriorityArrivalTrace,
        nonpreemptivePriorityArrivalTraceResidualWork]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadvancedPositive : positiveNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using
          positiveNonpreemptivePriorityResidualWork_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hpositive
      have hadmittedPositive : positiveNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using
          positiveNonpreemptivePriorityResidualWork_admit advanced job hadvancedPositive
            (hjobs job (by simp))
      have hadvancedWork : nonpreemptivePriorityWorkConserving advanced := by
        simpa [advanced] using
          nonpreemptivePriorityWorkConserving_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadmittedWork : nonpreemptivePriorityWorkConserving admitted := by
        simpa [admitted] using nonpreemptivePriorityWorkConserving_admit advanced job
      have hadmittedTime : admitted.currentTime = job.arrivalTime := by
        simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using
          advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
            (totalNonpreemptivePriorityWorkJobs initial) initial job
            (hstart job (by simp)) (le_rfl :
              totalNonpreemptivePriorityWorkJobs initial ≤
                totalNonpreemptivePriorityWorkJobs initial)
      have hadmittedStart : ∀ other ∈ jobs, admitted.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hadmittedTime]
        exact hhead other hother
      have htailPositive : ∀ other ∈ jobs, 0 < other.serviceWork := by
        intro other hother
        exact hjobs other (by simp [hother])
      have hrec := ih admitted hadmittedPositive hadmittedWork
        hadmittedStart htail htailPositive
      have hadmittedWorkload :
          totalNonpreemptivePriorityResidualWork admitted =
            max 0 (totalNonpreemptivePriorityResidualWork initial -
              (job.arrivalTime - initial.currentTime)) + job.serviceWork := by
        simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using
          totalNonpreemptivePriorityResidualWork_advanceThenAdmit
            (totalNonpreemptivePriorityWorkJobs initial) initial job
            (hstart job (by simp)) hpositive hwork le_rfl
      calc
        totalNonpreemptivePriorityResidualWork
            (runNonpreemptivePriorityArrivalTrace initial (job :: jobs)) =
            totalNonpreemptivePriorityResidualWork
              (runNonpreemptivePriorityArrivalTrace admitted jobs) := by
                simp [runNonpreemptivePriorityArrivalTrace, advanced, admitted,
                  advanceThenAdmitNonpreemptivePriorityJob]
        _ = nonpreemptivePriorityArrivalTraceResidualWork admitted.currentTime
              (totalNonpreemptivePriorityResidualWork admitted) jobs := hrec
        _ = nonpreemptivePriorityArrivalTraceResidualWork job.arrivalTime
              (max 0 (totalNonpreemptivePriorityResidualWork initial -
                (job.arrivalTime - initial.currentTime)) + job.serviceWork) jobs := by
              rw [hadmittedTime, hadmittedWorkload]
        _ = nonpreemptivePriorityArrivalTraceResidualWork initial.currentTime
              (totalNonpreemptivePriorityResidualWork initial) (job :: jobs) := by
              rfl

/-- If a finite physical arrival trace stays strictly busy immediately before
each arrival and at its terminal epoch, its scalar workload recursion never
uses the reflection at zero.  Consequently, elapsed service is exactly the
terminal interval length, and the remaining work is initial work plus marked
arrivals minus that elapsed capacity.

The hypotheses are deliberately scalar: a tagged-customer liveness argument
can supply them without committing this reusable accounting lemma to a
particular priority ordering or stochastic input law. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_initial_add_serviceWork_sub_of_positive
    {n : ℕ} {JobId : Type*}
    (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hterminal : 0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork
      time workload jobs terminalTime)
    (hprefix : ∀ (front suffix : List (NonpreemptivePriorityJob n JobId))
      (job : NonpreemptivePriorityJob n JobId),
      jobs = front ++ job :: suffix →
        0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork
          time workload front job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      time workload jobs terminalTime =
      workload + nonpreemptivePriorityArrivalTraceServiceWork jobs -
        (terminalTime - time) := by
  induction jobs generalizing time workload with
  | nil =>
      have hraw : 0 < workload - (terminalTime - time) := by
        by_contra hnot
        have hnonpos : workload - (terminalTime - time) ≤ 0 := le_of_not_gt hnot
        simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
          nonpreemptivePriorityArrivalTraceResidualWork,
          nonpreemptivePriorityArrivalTraceEndTime] at hterminal
        rw [max_eq_left hnonpos] at hterminal
        linarith
      simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime,
        nonpreemptivePriorityArrivalTraceServiceWork, List.map_nil, List.sum_nil]
      rw [max_eq_right hraw.le]
      ring
  | cons job jobs ih =>
      have hbefore : 0 < workload - (job.arrivalTime - time) := by
        have hpositive := hprefix [] jobs job rfl
        simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
          nonpreemptivePriorityArrivalTraceResidualWork,
          nonpreemptivePriorityArrivalTraceEndTime] at hpositive
        by_contra hnot
        have hnonpos : workload - (job.arrivalTime - time) ≤ 0 := le_of_not_gt hnot
        rw [max_eq_left hnonpos] at hpositive
        linarith
      let nextWorkload : ℝ := workload - (job.arrivalTime - time) + job.serviceWork
      have htailTerminal : 0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork
          job.arrivalTime nextWorkload jobs terminalTime := by
        simpa [nextWorkload, nonpreemptivePriorityArrivalTraceTerminalResidualWork,
          nonpreemptivePriorityArrivalTraceResidualWork,
          nonpreemptivePriorityArrivalTraceEndTime, max_eq_right hbefore.le] using hterminal
      have htailPrefix : ∀ (front suffix : List (NonpreemptivePriorityJob n JobId))
          (other : NonpreemptivePriorityJob n JobId),
          jobs = front ++ other :: suffix →
            0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork
              job.arrivalTime nextWorkload front other.arrivalTime := by
        intro front suffix other hsplit
        have hpositive := hprefix (job :: front) suffix other (by simp [hsplit])
        simpa [nextWorkload, nonpreemptivePriorityArrivalTraceTerminalResidualWork,
          nonpreemptivePriorityArrivalTraceResidualWork,
          nonpreemptivePriorityArrivalTraceEndTime, max_eq_right hbefore.le] using hpositive
      have htail := ih job.arrivalTime nextWorkload htailTerminal htailPrefix
      calc
        nonpreemptivePriorityArrivalTraceTerminalResidualWork
            time workload (job :: jobs) terminalTime =
            nonpreemptivePriorityArrivalTraceTerminalResidualWork
              job.arrivalTime nextWorkload jobs terminalTime := by
                simp [nextWorkload, nonpreemptivePriorityArrivalTraceTerminalResidualWork,
                  nonpreemptivePriorityArrivalTraceResidualWork,
                  nonpreemptivePriorityArrivalTraceEndTime, max_eq_right hbefore.le]
        _ = nextWorkload + nonpreemptivePriorityArrivalTraceServiceWork jobs -
              (terminalTime - job.arrivalTime) := htail
        _ = workload + nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
              (terminalTime - time) := by
                simp [nextWorkload, nonpreemptivePriorityArrivalTraceServiceWork]
                ring

end Queueing
end AppliedModelingLib
