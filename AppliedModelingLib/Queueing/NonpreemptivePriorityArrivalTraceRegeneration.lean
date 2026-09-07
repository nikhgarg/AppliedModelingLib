import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload

/-!
# Regeneration in finite physical-time priority traces

This module isolates the deterministic busy-period argument for a finite,
chronologically presented queue trace.  If initial work plus all marked work
is strictly smaller than the service capacity of the enclosing interval, then
the trace has an actual empty epoch after its start.  The assertion is about
the literal arrival epochs; it does not replace them by batched input.
-/

namespace AppliedModelingLib
namespace Queueing

/-- Advancing a concrete chronological finite trace through a terminal epoch
has exactly the scalar physical-time terminal workload. -/
theorem totalNonpreemptivePriorityResidualWork_advance_run_eq_terminalResidualWork
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminalTime : ℝ)
    (hpositiveInitial : positiveNonpreemptivePriorityResidualWork initial)
    (hworkInitial : nonpreemptivePriorityWorkConserving initial)
    (hinitialTerminal : initial.currentTime ≤ terminalTime)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime)
    (hpositive : ∀ job ∈ jobs, 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace initial jobs))
        terminalTime (runNonpreemptivePriorityArrivalTrace initial jobs)) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork initial.currentTime
        (totalNonpreemptivePriorityResidualWork initial) jobs terminalTime := by
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    dsimp [afterArrivals]
    exact positiveNonpreemptivePriorityResidualWork_run initial jobs
      hpositiveInitial hpositive
  have hafterWork : nonpreemptivePriorityWorkConserving afterArrivals := by
    dsimp [afterArrivals]
    exact nonpreemptivePriorityWorkConserving_run initial jobs hworkInitial
  have hafterTime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime initial.currentTime jobs := by
    dsimp [afterArrivals]
    exact runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
      initial jobs hstart hsorted
  have hafterTerminal : afterArrivals.currentTime ≤ terminalTime := by
    rw [hafterTime]
    exact nonpreemptivePriorityArrivalTraceEndTime_le initial.currentTime terminalTime jobs
      hinitialTerminal hend
  have hafterResidual : totalNonpreemptivePriorityResidualWork afterArrivals =
      nonpreemptivePriorityArrivalTraceResidualWork initial.currentTime
        (totalNonpreemptivePriorityResidualWork initial) jobs := by
    dsimp [afterArrivals]
    exact totalNonpreemptivePriorityResidualWork_run_eq_arrivalTraceResidualWork
      initial jobs hpositiveInitial hworkInitial hstart hsorted hpositive
  change totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals)
        terminalTime afterArrivals) = _
  rw [totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
    (totalNonpreemptivePriorityWorkJobs afterArrivals) terminalTime afterArrivals
    hafterTerminal hafterPositive hafterWork le_rfl,
    hafterResidual, hafterTime]
  rfl

/-- If the initial work plus the whole trace fits in the terminal service
interval, and every nonempty arrival suffix also fits after its first
arrival, then the literal physical-time trace is empty at the terminal epoch.
This is the finite reflected-workload form of a backward net-input maximum. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_all_suffixes_le
    {n : ℕ} {JobId : Type*}
    (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hinitial : workload + nonpreemptivePriorityArrivalTraceServiceWork jobs ≤
      terminalTime - time)
    (hsuffix : ∀ (front suffix : List (NonpreemptivePriorityJob n JobId))
      (job : NonpreemptivePriorityJob n JobId),
      jobs = front ++ job :: suffix →
        nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
          terminalTime - job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      time workload jobs terminalTime = 0 := by
  induction jobs generalizing time workload with
  | nil =>
      simp only [nonpreemptivePriorityArrivalTraceServiceWork,
        List.map_nil, List.sum_nil] at hinitial
      simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime]
      rw [max_eq_left]
      linarith
  | cons job jobs ih =>
      have hwhole : nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) ≤
          terminalTime - job.arrivalTime := by
        exact hsuffix [] jobs job rfl
      have htail : ∀ (front suffix : List (NonpreemptivePriorityJob n JobId))
          (other : NonpreemptivePriorityJob n JobId),
          jobs = front ++ other :: suffix →
            nonpreemptivePriorityArrivalTraceServiceWork (other :: suffix) ≤
              terminalTime - other.arrivalTime := by
        intro front suffix other hsplit
        apply hsuffix (job :: front) suffix other
        simp [hsplit]
      let nextWorkload :=
        max 0 (workload - (job.arrivalTime - time)) + job.serviceWork
      have hnext : nextWorkload + nonpreemptivePriorityArrivalTraceServiceWork jobs ≤
          terminalTime - job.arrivalTime := by
        by_cases hclear : workload ≤ job.arrivalTime - time
        · dsimp [nextWorkload]
          rw [max_eq_left (sub_nonpos.mpr hclear)]
          simpa [nonpreemptivePriorityArrivalTraceServiceWork] using hwhole
        · have hpositive : 0 < workload - (job.arrivalTime - time) := by
            exact sub_pos.mpr (lt_of_not_ge hclear)
          have hinitial' := hinitial
          simp only [nonpreemptivePriorityArrivalTraceServiceWork,
            List.map_cons, List.sum_cons] at hinitial'
          dsimp [nextWorkload]
          rw [max_eq_right hpositive.le]
          simp only [nonpreemptivePriorityArrivalTraceServiceWork]
          linarith
      simpa [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime, nextWorkload] using
        (ih job.arrivalTime nextWorkload hnext htail)

/-- A finite chronological trace whose initial work plus all marked work is
strictly below the service capacity of its enclosing interval has an actual
arrival-free reset epoch.  The returned prefix has been served through
`resetTime`, and every remaining job arrives at or after that epoch. -/
theorem exists_nonpreemptivePriorityArrivalTrace_terminalReset_of_initial_add_serviceWork_lt
    {n : ℕ} {JobId : Type*}
    (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hworkload : 0 ≤ workload)
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime)
    (hpositive : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hnet : workload + nonpreemptivePriorityArrivalTraceServiceWork jobs <
      terminalTime - time) :
    ∃ (front suffix : List (NonpreemptivePriorityJob n JobId)) (resetTime : ℝ),
      jobs = front ++ suffix ∧ time < resetTime ∧ resetTime ≤ terminalTime ∧
        (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
        (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
        nonpreemptivePriorityArrivalTraceTerminalResidualWork
          time workload front resetTime = 0 := by
  induction jobs generalizing time workload with
  | nil =>
      have htime : time < terminalTime := by
        simp [nonpreemptivePriorityArrivalTraceServiceWork] at hnet
        linarith
      refine ⟨[], [], terminalTime, by simp, htime, le_rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
          nonpreemptivePriorityArrivalTraceResidualWork,
          nonpreemptivePriorityArrivalTraceEndTime]
        rw [max_eq_left]
        simp [nonpreemptivePriorityArrivalTraceServiceWork] at hnet
        linarith
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      have hjobStart : time ≤ job.arrivalTime := hstart job (by simp)
      have hjobEnd : job.arrivalTime ≤ terminalTime := hend job (by simp)
      have hrestStart : ∀ other ∈ jobs, job.arrivalTime ≤ other.arrivalTime := by
        intro other hother
        exact hhead other hother
      have hrestEnd : ∀ other ∈ jobs, other.arrivalTime ≤ terminalTime := by
        intro other hother
        exact hend other (by simp [hother])
      have hrestPositive : ∀ other ∈ jobs, 0 < other.serviceWork := by
        intro other hother
        exact hpositive other (by simp [hother])
      let nextWorkload :=
        max 0 (workload - (job.arrivalTime - time)) + job.serviceWork
      by_cases hgap : time < job.arrivalTime ∧
          max 0 (workload - (job.arrivalTime - time)) = 0
      · refine ⟨[], job :: jobs, job.arrivalTime, by simp, hgap.1,
          hjobEnd, ?_, ?_, ?_⟩
        · simp
        · intro other hother
          rcases List.mem_cons.mp hother with rfl | hother
          · exact le_rfl
          · exact hhead other hother
        · simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
            nonpreemptivePriorityArrivalTraceResidualWork,
            nonpreemptivePriorityArrivalTraceEndTime]
          simpa using hgap.2
      · have hpre : max 0 (workload - (job.arrivalTime - time)) =
          workload - (job.arrivalTime - time) := by
          rcases hjobStart.lt_or_eq with hstrict | heq
          · have hnotzero : max 0 (workload - (job.arrivalTime - time)) ≠ 0 := by
              intro hzero
              exact hgap ⟨hstrict, hzero⟩
            by_cases hnonneg : 0 ≤ workload - (job.arrivalTime - time)
            · exact max_eq_right hnonneg
            · have hnonpos : workload - (job.arrivalTime - time) ≤ 0 :=
                le_of_not_ge hnonneg
              exact (hnotzero (max_eq_left hnonpos)).elim
          · simpa [heq] using (max_eq_right hworkload)
        have hnextNonneg : 0 ≤ nextWorkload := by
          dsimp [nextWorkload]
          exact add_nonneg (le_max_left _ _) (hpositive job (by simp)).le
        have hnet' : nextWorkload +
            nonpreemptivePriorityArrivalTraceServiceWork jobs <
            terminalTime - job.arrivalTime := by
          have hnet' := hnet
          simp only [nextWorkload, nonpreemptivePriorityArrivalTraceServiceWork,
            List.map_cons, List.sum_cons] at hnet' ⊢
          rw [hpre]
          linarith
        rcases ih job.arrivalTime nextWorkload hnextNonneg
          hrestStart htail hrestEnd hrestPositive hnet' with
          ⟨front, suffix, resetTime, hsplit, htime, hendTime, hfrontCut,
            hsuffix, hreset⟩
        have hfrontStart : ∀ other ∈ front, job.arrivalTime ≤ other.arrivalTime := by
          intro other hother
          apply hhead other
          rw [hsplit]
          exact List.mem_append_left _ hother
        have hfrontEnd : nonpreemptivePriorityArrivalTraceEndTime time [job] ≤
            job.arrivalTime := by
          simp [nonpreemptivePriorityArrivalTraceEndTime]
        have hfrontReset :
            nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
              [job] job.arrivalTime = nextWorkload := by
          simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
            nonpreemptivePriorityArrivalTraceResidualWork,
            nonpreemptivePriorityArrivalTraceEndTime, nextWorkload]
          rw [sub_self, sub_zero,
            max_eq_right (add_nonneg (le_max_left _ _) (hpositive job (by simp)).le)]
        refine ⟨job :: front, suffix, resetTime, ?_,
          lt_of_le_of_lt hjobStart htime, hendTime, ?_, hsuffix, ?_⟩
        · simp [hsplit]
        · intro other hother
          rcases List.mem_cons.mp hother with rfl | hother
          · exact htime.le
          · exact hfrontCut other hother
        · change nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
              ([job] ++ front) resetTime = 0
          rw [nonpreemptivePriorityArrivalTraceTerminalResidualWork_append
            time job.arrivalTime resetTime workload [job] front hfrontEnd htime.le hfrontStart,
            hfrontReset]
          exact hreset

/-- An empty-start finite trace with strictly less total marked work than the
enclosing service capacity has an actual arrival-free reset epoch. -/
theorem exists_nonpreemptivePriorityArrivalTrace_terminalReset_of_serviceWork_lt
    {n : ℕ} {JobId : Type*}
    (time terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime)
    (hpositive : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hnet : nonpreemptivePriorityArrivalTraceServiceWork jobs < terminalTime - time) :
    ∃ (front suffix : List (NonpreemptivePriorityJob n JobId)) (resetTime : ℝ),
      jobs = front ++ suffix ∧ time < resetTime ∧ resetTime ≤ terminalTime ∧
        (∀ job ∈ front, job.arrivalTime ≤ resetTime) ∧
        (∀ job ∈ suffix, resetTime ≤ job.arrivalTime) ∧
        nonpreemptivePriorityArrivalTraceTerminalResidualWork
          time 0 front resetTime = 0 := by
  simpa using
    (exists_nonpreemptivePriorityArrivalTrace_terminalReset_of_initial_add_serviceWork_lt
      time 0 terminalTime jobs (by norm_num) hstart hsorted hend hpositive (by simpa using hnet))

end Queueing
end AppliedModelingLib
