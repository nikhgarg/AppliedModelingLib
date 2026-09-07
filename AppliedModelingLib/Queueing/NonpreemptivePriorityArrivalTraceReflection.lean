import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload

/-!
# Exact reflected workload representation for finite priority traces

The scalar workload of a work-conserving single server is independent of the
service order.  This file gives the exact finite physical-time reflection
formula for a chronological priority-arrival trace.  It retains the literal
arrival epochs: each term is the marked work in an actual arrival suffix less
the service capacity available after that suffix begins.

The result is deliberately deterministic.  Stationary or Palm integrability
requires a separate probabilistic argument for the resulting supremum.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- The maximum net work of a nonempty suffix of a finite chronological
arrival trace, measured at a fixed terminal epoch.  The entry for a suffix
beginning at `job` is its total marked work less the service capacity from
`job.arrivalTime` through the terminal epoch. -/
def nonpreemptivePriorityArrivalTraceSuffixNetWork
    {n : ℕ} {JobId : Type*}
    (terminalTime : ℝ) : List (NonpreemptivePriorityJob n JobId) → List ℝ
  | [] => []
  | job :: jobs =>
      (nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
        (terminalTime - job.arrivalTime)) ::
      nonpreemptivePriorityArrivalTraceSuffixNetWork terminalTime jobs

/-- The maximum terminal net work among all nonempty suffixes, with zero as
the empty-suffix alternative. -/
def nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) : ℝ :=
  (nonpreemptivePriorityArrivalTraceSuffixNetWork terminalTime jobs).foldr max 0

/-- The suffix maximum of the empty trace is zero. -/
@[simp] theorem nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_nil
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ) :
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum
      (n := n) (JobId := JobId) terminalTime [] = 0 := by
  rfl

/-- Peeling the first arrival exposes the net work of the whole suffix and
the maximum over its proper suffixes. -/
theorem nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (job : NonpreemptivePriorityJob n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime (job :: jobs) =
      max
        (nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
          (terminalTime - job.arrivalTime))
        (nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs) := by
  rfl

/-- The one-step algebra behind physical-time workload reflection.  Carrying
initial work to the first arrival either leaves that work positive, or resets
the queue and leaves the first arrival as the new suffix candidate. -/
private theorem max_zero_add_terminal_eq_max_initial_or_arrival
    (initialWork elapsed firstWork laterWork remainingTime tailMaximum : ℝ) :
    max 0
      (max (max 0 (initialWork - elapsed) + firstWork + laterWork - remainingTime)
        tailMaximum) =
      max 0
        (max
          (initialWork + firstWork + laterWork - (elapsed + remainingTime))
          (max (firstWork + laterWork - remainingTime) tailMaximum)) := by
  by_cases h : 0 ≤ initialWork - elapsed
  · rw [max_eq_right h]
    let broad : ℝ := initialWork + firstWork + laterWork - (elapsed + remainingTime)
    let arrival : ℝ := firstWork + laterWork - remainingTime
    have hdominates : arrival ≤ broad := by
      dsimp [broad, arrival]
      linarith
    have hinterior : max broad (max arrival tailMaximum) = max broad tailMaximum := by
      rw [← max_assoc, max_eq_left hdominates]
    calc
      max 0
          (max (initialWork - elapsed + firstWork + laterWork - remainingTime)
            tailMaximum) = max 0 (max broad tailMaximum) := by
              congr 2
              dsimp [broad]
              ring
      _ = max 0 (max broad (max arrival tailMaximum)) := by rw [hinterior]
      _ = max 0
          (max
            (initialWork + firstWork + laterWork - (elapsed + remainingTime))
            (max (firstWork + laterWork - remainingTime) tailMaximum)) := by
              rfl
  · rw [max_eq_left (le_of_not_ge h)]
    let broad : ℝ := initialWork + firstWork + laterWork - (elapsed + remainingTime)
    let arrival : ℝ := firstWork + laterWork - remainingTime
    have hdominated : broad ≤ arrival := by
      dsimp [broad, arrival]
      linarith
    have hinterior : max broad (max arrival tailMaximum) = max arrival tailMaximum := by
      rw [← max_assoc, max_eq_right hdominated]
    calc
      max 0 (max (0 + firstWork + laterWork - remainingTime) tailMaximum) =
          max 0 (max arrival tailMaximum) := by
            congr 2
            dsimp [arrival]
            ring
      _ = max 0 (max broad (max arrival tailMaximum)) := by rw [hinterior]
      _ = max 0
          (max
            (initialWork + firstWork + laterWork - (elapsed + remainingTime))
            (max (firstWork + laterWork - remainingTime) tailMaximum)) := by
              rfl

/-- Every suffix-work maximum includes the zero empty-suffix candidate. -/
theorem nonnegative_nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    0 ≤ nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      exact ih.trans (le_max_right _ _)

/-- Extending a trace by an older prefix cannot lower the maximum net work of
the suffixes that were already present.  This is the deterministic monotonicity
behind remote-past workload limits. -/
theorem nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_le_append
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (front suffix : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime suffix ≤
      nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime
        (front ++ suffix) := by
  induction front with
  | nil => rfl
  | cons job front ih =>
      rw [List.cons_append,
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
      exact ih.trans (le_max_right _ _)

/-- Exact reflected physical workload for a finite chronological trace.  The
first candidate carries the initial work together with the complete trace;
the remaining candidates are the literal nonempty arrival suffixes. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_reflection
    {n : ℕ} {JobId : Type*}
    (time workload terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time ≤ terminalTime)
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs terminalTime =
      max 0
        (max
          (workload + nonpreemptivePriorityArrivalTraceServiceWork jobs -
            (terminalTime - time))
          (nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs)) := by
  induction jobs generalizing time workload with
  | nil =>
      simp only [nonpreemptivePriorityArrivalTraceTerminalResidualWork,
        nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityArrivalTraceEndTime,
        nonpreemptivePriorityArrivalTraceServiceWork,
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum,
        nonpreemptivePriorityArrivalTraceSuffixNetWork,
        List.map_nil, List.sum_nil, List.foldr_nil]
      simp only [add_zero]
      rw [max_comm (workload - (terminalTime - time)) 0]
      rw [max_eq_right (le_max_left _ _)]
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
      rw [show nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload
          (job :: jobs) terminalTime =
          nonpreemptivePriorityArrivalTraceTerminalResidualWork job.arrivalTime
            (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)
            jobs terminalTime by rfl]
      rw [ih job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)
        hjobEnd htailStart htail htailEnd]
      simp only [nonpreemptivePriorityArrivalTraceServiceWork,
        List.map_cons, List.sum_cons]
      have hrewrite : terminalTime - time =
          (job.arrivalTime - time) + (terminalTime - job.arrivalTime) := by
        ring
      have halgebra := max_zero_add_terminal_eq_max_initial_or_arrival
        workload (job.arrivalTime - time) job.serviceWork
        (nonpreemptivePriorityArrivalTraceServiceWork jobs)
        (terminalTime - job.arrivalTime)
        (nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs)
      rw [hrewrite]
      rw [nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
      simpa [add_assoc, add_left_comm, add_comm] using halgebra

/-- From an empty initial state, the terminal workload is exactly the maximum
over the genuine arrival-suffix net-work candidates.  The artificial
empty-start candidate is dominated by the candidate beginning at the first
arrival (and is zero for an empty trace). -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_empty_eq_suffixMaximum
    {n : ℕ} {JobId : Type*}
    (time terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time ≤ terminalTime)
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0 jobs terminalTime =
      nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs := by
  rw [nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_reflection
    time 0 terminalTime jobs htime hstart hsorted hend]
  cases jobs with
  | nil =>
      simp only [nonpreemptivePriorityArrivalTraceServiceWork,
        List.map_nil, List.sum_nil,
        nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum,
        nonpreemptivePriorityArrivalTraceSuffixNetWork, List.foldr_nil, zero_add]
      rw [max_eq_right (by linarith : 0 - (terminalTime - time) ≤ 0)]
      simp
  | cons job jobs =>
      have hjobStart : time ≤ job.arrivalTime := hstart job (by simp)
      rw [nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
      have htailNonnegative : 0 ≤
          nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs :=
        nonnegative_nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs
      have hmaximumNonnegative : 0 ≤ max
          (nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
            (terminalTime - job.arrivalTime))
          (nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs) :=
        htailNonnegative.trans (le_max_right _ _)
      have hfirstLe :
          nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
            (terminalTime - time) ≤
          max
            (nonpreemptivePriorityArrivalTraceServiceWork (job :: jobs) -
              (terminalTime - job.arrivalTime))
            (nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime jobs) := by
        apply le_trans ?_ (le_max_left _ _)
        linarith
      simp only [zero_add]
      rw [max_eq_right hfirstLe, max_eq_right hmaximumNonnegative]

end

end AppliedModelingLib.Queueing
