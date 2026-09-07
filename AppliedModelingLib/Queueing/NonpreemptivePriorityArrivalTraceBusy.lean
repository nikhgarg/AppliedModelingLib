import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedLiveness

/-!
# Busy prefixes of finite nonpreemptive-priority traces

A tracked job that remains uncompleted throughout a chronological literal
arrival trace prevents the scalar workload recursion from reflecting at zero
before any later admission.  This is a deterministic queue fact; consumers
may establish the no-completion premise from a tagged response construction,
without encoding a particular stochastic input law here.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- If a tracked initial job has no completion record after a finite
chronological trace, then every prefix immediately before a later admission
has strictly positive terminal workload.  The conclusion is stated in the
scalar trace language so it can feed unreflected work-conservation arguments.
-/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_pos_of_initialJob_not_completed
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hpositiveInitial : positiveNonpreemptivePriorityResidualWork initial)
    (hworkInitial : nonpreemptivePriorityWorkConserving initial)
    (hcontainsInitial : nonpreemptivePriorityWorkStateContainsJob initial tag)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hpositive : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hsorted : jobs.Pairwise (fun earlier later =>
      earlier.arrivalTime ≤ later.arrivalTime))
    (hnotCompleted : ¬ ∃ completedAt, (tag, completedAt) ∈
      (runNonpreemptivePriorityArrivalTrace initial jobs).completed) :
    ∀ (front suffix : List (NonpreemptivePriorityJob n JobId))
      (job : NonpreemptivePriorityJob n JobId),
      jobs = front ++ job :: suffix →
      0 < nonpreemptivePriorityArrivalTraceTerminalResidualWork
        initial.currentTime (totalNonpreemptivePriorityResidualWork initial)
        front job.arrivalTime := by
  intro front suffix job hsplit
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  let atArrival := advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterFront) job.arrivalTime afterFront
  have hfrontStart : ∀ earlier ∈ front, initial.currentTime ≤ earlier.arrivalTime := by
    intro earlier hearlier
    exact hstart earlier (by rw [hsplit]; exact List.mem_append_left _ hearlier)
  have hfrontPositive : ∀ earlier ∈ front, 0 < earlier.serviceWork := by
    intro earlier hearlier
    exact hpositive earlier (by rw [hsplit]; exact List.mem_append_left _ hearlier)
  have hsortedSplit : (front ++ job :: suffix).Pairwise (fun earlier later =>
      earlier.arrivalTime ≤ later.arrivalTime) := by
    rw [← hsplit]
    exact hsorted
  have hsplitPair := List.pairwise_append.mp hsortedSplit
  have hfrontOrdered : front.Pairwise (fun earlier later =>
      earlier.arrivalTime ≤ later.arrivalTime) := by
    exact hsplitPair.1
  have hfrontEnd : ∀ earlier ∈ front, earlier.arrivalTime ≤ job.arrivalTime := by
    intro earlier hearlier
    exact hsplitPair.2.2 earlier hearlier job (by simp)
  have hcurrent : initial.currentTime ≤ job.arrivalTime := by
    exact hstart job (by rw [hsplit]; simp)
  have hafterFrontPositive : positiveNonpreemptivePriorityResidualWork afterFront := by
    dsimp [afterFront]
    exact positiveNonpreemptivePriorityResidualWork_run initial front
      hpositiveInitial hfrontPositive
  have hcontainsAtArrival : nonpreemptivePriorityWorkStateContainsJob atArrival tag := by
    dsimp [atArrival]
    apply nonpreemptivePriorityWorkStateContainsJob_advance
    dsimp [afterFront]
    exact nonpreemptivePriorityWorkStateContainsJob_run initial front tag hcontainsInitial
  have hnotCompletedAtArrival : ¬ ∃ completedAt, (tag, completedAt) ∈ atArrival.completed := by
    rintro ⟨completedAt, hcompleted⟩
    apply hnotCompleted
    have hadmitted : (tag, completedAt) ∈
        (admitNonpreemptivePriorityJob atArrival job).completed := by
      exact mem_completed_admitNonpreemptivePriorityJob atArrival job tag completedAt hcompleted
    have htail : (tag, completedAt) ∈
        (runNonpreemptivePriorityArrivalTrace (admitNonpreemptivePriorityJob atArrival job)
          suffix).completed := by
      exact mem_completed_runNonpreemptivePriorityArrivalTrace
        (admitNonpreemptivePriorityJob atArrival job) suffix tag completedAt hadmitted
    refine ⟨completedAt, ?_⟩
    rw [hsplit]
    simpa [afterFront, atArrival, runNonpreemptivePriorityArrivalTrace,
      advanceThenAdmitNonpreemptivePriorityJob] using htail
  have hlive : nonpreemptivePriorityWorkStateJobLive atArrival tag := by
    exact nonpreemptivePriorityWorkStateJobLive_of_contains_of_not_completed
      atArrival tag hcontainsAtArrival hnotCompletedAtArrival
  have hpositiveAtArrival : positiveNonpreemptivePriorityResidualWork atArrival := by
    dsimp [atArrival]
    exact positiveNonpreemptivePriorityResidualWork_advance
      (totalNonpreemptivePriorityWorkJobs afterFront) job.arrivalTime afterFront
      hafterFrontPositive
  have hresidualPos : 0 < totalNonpreemptivePriorityResidualWork atArrival := by
    exact totalNonpreemptivePriorityResidualWork_pos_of_jobLive
      atArrival tag hpositiveAtArrival hlive
  have hscalar : totalNonpreemptivePriorityResidualWork atArrival =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork initial.currentTime
        (totalNonpreemptivePriorityResidualWork initial) front job.arrivalTime := by
    dsimp [atArrival, afterFront]
    exact totalNonpreemptivePriorityResidualWork_advance_run_eq_terminalResidualWork
      initial front job.arrivalTime hpositiveInitial hworkInitial hcurrent hfrontStart
      hfrontOrdered hfrontEnd hfrontPositive
  rwa [hscalar] at hresidualPos

end

end AppliedModelingLib.Queueing
