import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedServiceStartPredictability
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryPathMeasurability

/-!
# Waiting-interval occupation for tagged priority customers

This module records the deterministic occupation of a FIFO waiting interval.
It is stated for the generic nonpreemptive-priority construction: a customer
whose service has not started before time `w` contributes one unit to its
waiting indicator on `[0, w)`, and hence contributes its work requirement
times its capped waiting interval.  The later stationary Campbell argument
uses these finite-horizon identities without treating customer rewards as
primitive certificates.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The Lebesgue area of a strict waiting indicator on a nonnegative finite
horizon is the corresponding capped waiting time. -/
theorem intervalIntegral_indicator_lt_eq_min
    (horizon wait : ℝ) (hhorizon : 0 ≤ horizon) (hwait : 0 ≤ wait) :
    (∫ time in 0..horizon, if time < wait then (1 : ℝ) else 0) =
      min horizon wait := by
  have hae : (fun time : ℝ => if time < wait then (1 : ℝ) else 0) =ᵐ[
      MeasureTheory.volume]
      (Set.Iic wait).indicator (fun _ : ℝ => (1 : ℝ)) := by
    have hne : ∀ᵐ time : ℝ ∂MeasureTheory.volume, time ≠ wait := by
      simp [MeasureTheory.ae_iff]
    filter_upwards [hne] with time htime
    by_cases hlt : time < wait
    · rw [Set.indicator_of_mem (show time ∈ Set.Iic wait from hlt.le)]
      simp [hlt]
    · have hnotle : ¬ time ≤ wait := by
        intro hle
        exact hlt (lt_of_le_of_ne hle htime)
      rw [Set.indicator_of_notMem (show time ∉ Set.Iic wait from hnotle)]
      simp [hlt]
  rcases le_total horizon wait with hhw | hwh
  · have hconst : ∀ᵐ time : ℝ ∂MeasureTheory.volume, time ∈ Set.uIoc 0 horizon →
        (if time < wait then (1 : ℝ) else 0) = 1 := by
      have hne : ∀ᵐ time : ℝ ∂MeasureTheory.volume, time ≠ wait := by
        simp [MeasureTheory.ae_iff]
      filter_upwards [hne] with time htime hmember
      rw [Set.uIoc_of_le hhorizon] at hmember
      have hlt : time < wait := lt_of_le_of_ne (hmember.2.trans hhw) htime
      simp [hlt]
    calc
      (∫ time in 0..horizon, if time < wait then (1 : ℝ) else 0) =
          ∫ time in 0..horizon, (1 : ℝ) :=
        intervalIntegral.integral_congr_ae hconst
      _ = min horizon wait := by
        rw [intervalIntegral.integral_const, min_eq_left hhw]
        norm_num
  · calc
      (∫ time in 0..horizon, if time < wait then (1 : ℝ) else 0) =
          ∫ time in 0..horizon,
            (Set.Iic wait).indicator (fun _ : ℝ => (1 : ℝ)) time := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hae] with time htime _
        exact htime
      _ = ∫ time in 0..wait, (1 : ℝ) := by
        exact intervalIntegral.integral_indicator ⟨hwait, hwh⟩
      _ = min horizon wait := by
        rw [intervalIntegral.integral_const, min_eq_right hwh]
        norm_num

/-- A class FIFO's waiting-work ledger is the finite sum of the work of its
literal occupants weighted by their own FIFO-membership indicators.  This is
the state-side form of the customer occupation decomposition; a later trace
telescope will replace the current FIFO list by the corresponding arrival
ledger. -/
theorem priorityWaitingResidualWork_eq_sum_waitingIdentifierIndicator
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (priority : Fin n) :
    priorityWaitingResidualWork state priority =
      ((state.waiting priority).map (fun job => job.serviceWork *
        nonpreemptivePriorityWaitingIdentifierIndicator job.identifier state)).sum := by
  unfold priorityWaitingResidualWork
  rw [List.map_congr_left]
  intro job hmember
  have hwaiting : nonpreemptivePriorityWaitingIdentifier job.identifier state :=
    ⟨priority, job, hmember, rfl⟩
  simp [nonpreemptivePriorityWaitingIdentifierIndicator, hwaiting]

/-- Priority-filtered waiting work is the sum of the same indicator-weighted
customer contributions over the classes at least as urgent as the selected
priority. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_eq_sum_waitingIdentifierIndicator
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent state priority =
      ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
        ((state.waiting level).map (fun job => job.serviceWork *
          nonpreemptivePriorityWaitingIdentifierIndicator job.identifier state)).sum := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_congr rfl
  intro level hlevel
  exact priorityWaitingResidualWork_eq_sum_waitingIdentifierIndicator state level

/-- A finite arrival-trace state at an arbitrary physical time cannot contain
a job other than one already present initially or one in its finite input
ledger.  This is the provenance half of reindexing a changing FIFO population
by a fixed customer list. -/
theorem nonpreemptivePriorityWorkStateContainsJob_arrivalTraceStateAt_reverse
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (nonpreemptivePriorityArrivalTraceStateAt initial jobs target) job) :
    nonpreemptivePriorityWorkStateContainsJob initial job ∨ job ∈ jobs := by
  induction jobs generalizing initial with
  | nil =>
      left
      exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
        (totalNonpreemptivePriorityWorkJobs initial) target initial job
        (by simpa [nonpreemptivePriorityArrivalTraceStateAt] using hcontains)
  | cons newJob jobs ih =>
      by_cases htarget : target < newJob.arrivalTime
      · left
        exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
          (totalNonpreemptivePriorityWorkJobs initial) target initial job
          (by simpa [nonpreemptivePriorityArrivalTraceStateAt, htarget] using hcontains)
      · let advanced := advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
        let admitted := admitNonpreemptivePriorityJob advanced newJob
        have htail : nonpreemptivePriorityWorkStateContainsJob admitted job ∨ job ∈ jobs := by
          apply ih admitted
          simpa [nonpreemptivePriorityArrivalTraceStateAt, htarget,
            advanced, admitted, advanceThenAdmitNonpreemptivePriorityJob] using hcontains
        rcases htail with hadmitted | hmember
        · rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse
            advanced newJob job (by simpa [admitted] using hadmitted) with hadvanced | hnew
          · left
            exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
              (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial job
              (by simpa [advanced] using hadvanced)
          · exact Or.inr (List.mem_cons.mpr (Or.inl hnew))
        · exact Or.inr (List.mem_cons.mpr (Or.inr hmember))

/-- Every job represented by a literal finite stationary window was supplied
by that window's marked-arrival ledger.  In particular, the changing FIFO
population has no hidden source beyond the finite input list. -/
theorem nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_reverse
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityFiniteWindowState meanService omega left right) job) :
    job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right := by
  unfold stationaryPriorityFiniteWindowState at hcontains
  dsimp only at hcontains
  have hrun : nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace
        (emptyNonpreemptivePriorityWorkState
          (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) left)
        (stationaryPriorityArrivalWindowJobs meanService omega left right)) job := by
    exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ right _ _ hcontains
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse _ _ _ hrun with hempty | hledger
  · simp [nonpreemptivePriorityWorkStateContainsJob,
      emptyNonpreemptivePriorityWorkState] at hempty
  · exact hledger

/-- At an intermediate observation time, every finite-window queue occupant
already belongs to the fixed ledger for the enclosing physical window. -/
theorem nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_of_le
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityFiniteWindowState meanService omega left time) job) :
    job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right := by
  rw [stationaryPriorityArrivalWindowJobs_append meanService omega left time right hleft hright]
  exact List.mem_append_left _
    (nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_reverse
      meanService omega left time job hcontains)

/-- Within one literal stationary input window, a job record is determined by
its labelled arrival identifier.  This lets a FIFO-membership indicator be
reindexed by the fixed marked-arrival ledger without conflating two records. -/
theorem eq_stationaryPriorityArrivalWindowJob_of_mem_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ)
    (first second : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hfirst : first ∈ stationaryPriorityArrivalWindowJobs meanService omega left right)
    (hsecond : second ∈ stationaryPriorityArrivalWindowJobs meanService omega left right)
    (hidentifier : first.identifier = second.identifier) :
    first = second := by
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega left right first).mp hfirst
    with ⟨firstClass, firstIndex, _, hfirstEq⟩
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega left right second).mp hsecond
    with ⟨secondClass, secondIndex, _, hsecondEq⟩
  subst first
  subst second
  change (Sigma.mk firstClass firstIndex : NonpreemptivePriorityArrivalIndex n) =
    (Sigma.mk secondClass secondIndex : NonpreemptivePriorityArrivalIndex n) at hidentifier
  cases hidentifier
  rfl

/-- At an intermediate time of a finite stationary replay, membership in a
given FIFO list is exactly membership in the enclosing fixed arrival ledger,
at that priority, together with the job's FIFO-membership indicator. -/
theorem mem_waiting_stationaryPriorityFiniteWindowState_iff_mem_window_and_indicator
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ (stationaryPriorityFiniteWindowState meanService omega left time).waiting priority ↔
      job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right ∧
        job.priority = priority ∧
        nonpreemptivePriorityWaitingIdentifier job.identifier
          (stationaryPriorityFiniteWindowState meanService omega left time) := by
  let state := stationaryPriorityFiniteWindowState meanService omega left time
  let ledger := stationaryPriorityArrivalWindowJobs meanService omega left right
  have hclass : hasClassConsistentWaiting state := by
    simpa [state] using
      hasClassConsistentWaiting_stationaryPriorityFiniteWindowState
        meanService omega left time
  constructor
  · intro hmember
    refine ⟨?_, hclass priority job hmember, ⟨priority, job, hmember, rfl⟩⟩
    exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_of_le
      meanService omega left time right hleft hright job
      (Or.inr (Or.inl ⟨priority, hmember⟩))
  · rintro ⟨hledger, hpriority, hwaiting⟩
    rcases hwaiting with ⟨actualPriority, actual, hactual, hidentifier⟩
    have hactualLedger : actual ∈ ledger := by
      exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_of_le
        meanService omega left time right hleft hright actual
        (Or.inr (Or.inl ⟨actualPriority, hactual⟩))
    have hactualEq : actual = job := by
      exact eq_stationaryPriorityArrivalWindowJob_of_mem_of_identifier_eq
        meanService omega left right actual job
        (by simpa [ledger] using hactualLedger)
        (by simpa [ledger] using hledger) hidentifier
    subst actual
    have hactualPriority : job.priority = actualPriority :=
      hclass actualPriority job hactual
    have hpriorityEq : actualPriority = priority := by
      exact hactualPriority.symm.trans hpriority
    rw [hpriorityEq] at hactual
    exact hactual

/-- A customer from a fixed finite input ledger cannot occupy a FIFO before
its own literal arrival epoch.  This is the support fact used when replacing
a physical-time occupation by per-customer elapsed-time integrals. -/
theorem arrivalTime_lt_of_nonpreemptivePriorityWaitingIdentifier_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right)
    (hwaiting : nonpreemptivePriorityWaitingIdentifier job.identifier
      (stationaryPriorityFiniteWindowState meanService omega left time)) :
    job.arrivalTime < time := by
  rcases hwaiting with ⟨level, actual, hactual, hidentifier⟩
  have hactualWindow : actual ∈ stationaryPriorityArrivalWindowJobs meanService omega left time := by
    exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_reverse
      meanService omega left time actual (Or.inr (Or.inl ⟨level, hactual⟩))
  have hactualExtended : actual ∈ stationaryPriorityArrivalWindowJobs meanService omega left right := by
    exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_of_le
      meanService omega left time right hleft hright actual
      (Or.inr (Or.inl ⟨level, hactual⟩))
  have hactualEq : actual = job := by
    exact eq_stationaryPriorityArrivalWindowJob_of_mem_of_identifier_eq
      meanService omega left right actual job hactualExtended hjob hidentifier
  subst actual
  exact arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right
    meanService omega left time job hactualWindow

/-- The numeric FIFO indicator of a finite-ledger customer vanishes at and
before that customer's arrival epoch. -/
theorem nonpreemptivePriorityWaitingIdentifierIndicator_eq_zero_of_time_le_arrival
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right)
    (htime : time ≤ job.arrivalTime) :
    nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
      (stationaryPriorityFiniteWindowState meanService omega left time) = 0 := by
  unfold nonpreemptivePriorityWaitingIdentifierIndicator
  by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier job.identifier
      (stationaryPriorityFiniteWindowState meanService omega left time)
  · exfalso
    exact (not_lt_of_ge htime)
      (arrivalTime_lt_of_nonpreemptivePriorityWaitingIdentifier_stationaryPriorityFiniteWindowState
        meanService omega left time right hleft hright job hjob hwaiting)
  · simp [hwaiting]

/-- The work coordinate carried by a literal finite arrival ledger is exactly
the corresponding marked-input work requirement. -/
theorem stationaryPriorityArrivalWindowJob_serviceWork_eq_workRequirement
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right) :
    job.serviceWork = stationaryPriorityWorkRequirement meanService job.identifier.1 omega
      job.identifier.2 := by
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega left right job).mp hjob
    with ⟨i, k, _, hcoordinate⟩
  subst job
  rfl

/-- In a finite stationary replay, one ledger customer's work-weighted FIFO
occupation is supported after that customer's literal arrival epoch. -/
theorem intervalIntegral_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_from_arrival
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left right : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right) :
    (∫ time in left..right,
      stationaryPriorityWorkRequirement meanService job.identifier.1 omega job.identifier.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
          (stationaryPriorityFiniteWindowState meanService omega left time)) =
      ∫ time in job.arrivalTime..right,
        stationaryPriorityWorkRequirement meanService job.identifier.1 omega job.identifier.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
            (stationaryPriorityFiniteWindowState meanService omega left time) := by
  let f : ℝ → ℝ := fun time =>
    stationaryPriorityWorkRequirement meanService job.identifier.1 omega job.identifier.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
        (stationaryPriorityFiniteWindowState meanService omega left time)
  have hleft : left ≤ job.arrivalTime :=
    left_le_arrivalTime_stationaryPriorityArrivalWindowJobs meanService omega left right job hjob
  have hright : job.arrivalTime < right :=
    arrivalTime_lt_stationaryPriorityArrivalWindowJobs_right meanService omega left right job hjob
  have hleftIntegrable : IntervalIntegrable f MeasureTheory.volume left job.arrivalTime := by
    simpa [f] using
      intervalIntegrable_stationaryPriorityFiniteWindowWaitingIdentifierContribution
        meanService omega left left job.arrivalTime job.identifier
  have hrightIntegrable : IntervalIntegrable f MeasureTheory.volume job.arrivalTime right := by
    simpa [f] using
      intervalIntegrable_stationaryPriorityFiniteWindowWaitingIdentifierContribution
        meanService omega left job.arrivalTime right job.identifier
  have hzero : (∫ time in left..job.arrivalTime, f time) = 0 := by
    calc
      (∫ time in left..job.arrivalTime, f time) = ∫ time in left..job.arrivalTime, 0 := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with time htime
        rw [Set.uIoc_of_le hleft] at htime
        unfold f
        rw [nonpreemptivePriorityWaitingIdentifierIndicator_eq_zero_of_time_le_arrival
          meanService omega left time right htime.1.le (htime.2.trans hright.le) job hjob
          htime.2]
        ring
      _ = 0 := intervalIntegral.integral_zero
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hleftIntegrable hrightIntegrable
  dsimp [f] at hzero hsplit ⊢
  linarith

/-- A finite stationary replay started empty contains each input job at most
once across its active, waiting, and completed ledgers. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityFiniteWindowState_eq_one_of_mem
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (stationaryPriorityFiniteWindowState meanService omega left right) job = 1 := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) left
  let ledger := stationaryPriorityArrivalWindowJobs meanService omega left right
  have hrun : nonpreemptivePriorityWorkStateJobMultiplicity
      (runNonpreemptivePriorityArrivalTrace initial ledger) job =
        nonpreemptivePriorityWorkStateJobMultiplicity initial job + 1 := by
    exact nonpreemptivePriorityWorkStateJobMultiplicity_run_eq_add_one_of_nodup_mem
      initial ledger job
      (by simpa [ledger] using
        nodup_stationaryPriorityArrivalWindowJobs meanService omega left right)
      (by simpa [ledger] using hjob)
  have hinitial : nonpreemptivePriorityWorkStateJobMultiplicity initial job = 0 := by
    simp [initial, nonpreemptivePriorityWorkStateJobMultiplicity,
      emptyNonpreemptivePriorityWorkState]
  unfold stationaryPriorityFiniteWindowState
  dsimp only
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance, hrun, hinitial]

/-- No finite stationary replay FIFO list contains the same literal arrival
record twice. -/
theorem nodup_waiting_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ) (priority : Fin n) :
    (stationaryPriorityFiniteWindowState meanService omega left right).waiting priority |>.Nodup := by
  classical
  rw [List.nodup_iff_count_le_one]
  intro job
  by_cases hmember : job ∈
      (stationaryPriorityFiniteWindowState meanService omega left right).waiting priority
  · have hledger : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right := by
      exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_reverse
        meanService omega left right job (Or.inr (Or.inl ⟨priority, hmember⟩))
    have hmult :=
      nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityFiniteWindowState_eq_one_of_mem
        meanService omega left right job hledger
    have hsum :
        ((stationaryPriorityFiniteWindowState meanService omega left right).waiting priority).count job ≤
          ∑ level,
            ((stationaryPriorityFiniteWindowState meanService omega left right).waiting level).count job := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun level =>
          ((stationaryPriorityFiniteWindowState meanService omega left right).waiting level).count job)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ priority)
    unfold nonpreemptivePriorityWorkStateJobMultiplicity at hmult
    omega
  · rw [List.count_eq_zero_of_not_mem hmember]
    omega

/-- The fixed arrival ledger restricted to the customers that occupy one FIFO
at an intermediate replay time.  The predicate is expressed through the
literal state indicator so it can later be integrated customer by customer. -/
noncomputable def stationaryPriorityFiniteWindowWaitingJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (priority : Fin n) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) := by
  classical
  exact (stationaryPriorityArrivalWindowJobs meanService omega left right).filter
    (fun job => decide (job.priority = priority ∧
      nonpreemptivePriorityWaitingIdentifier job.identifier
        (stationaryPriorityFiniteWindowState meanService omega left time)))

/-- Membership in the fixed-ledger waiting sublist has its literal
priority-and-FIFO-indicator characterization. -/
theorem mem_stationaryPriorityFiniteWindowWaitingJobs_iff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ stationaryPriorityFiniteWindowWaitingJobs meanService omega left time right priority ↔
      job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right ∧
        job.priority = priority ∧
        nonpreemptivePriorityWaitingIdentifier job.identifier
          (stationaryPriorityFiniteWindowState meanService omega left time) := by
  classical
  unfold stationaryPriorityFiniteWindowWaitingJobs
  simp only [List.mem_filter, decide_eq_true_eq]

/-- The actual FIFO list is a permutation of its indicator-selected fixed
arrival-ledger sublist.  This is the finite pathwise reindexing step that
turns an evolving queue population into a fixed customer index set. -/
theorem perm_waiting_stationaryPriorityFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n) :
    (stationaryPriorityFiniteWindowState meanService omega left time).waiting priority |>.Perm
      (stationaryPriorityFiniteWindowWaitingJobs meanService omega left time right priority) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup_waiting_stationaryPriorityFiniteWindowState
      meanService omega left time priority
  · unfold stationaryPriorityFiniteWindowWaitingJobs
    exact (nodup_stationaryPriorityArrivalWindowJobs meanService omega left right).filter _
  · apply Finset.ext
    intro job
    simp only [List.mem_toFinset]
    exact (mem_waiting_stationaryPriorityFiniteWindowState_iff_mem_window_and_indicator
      meanService omega left time right hleft hright priority job).trans
      (mem_stationaryPriorityFiniteWindowWaitingJobs_iff
        meanService omega left time right priority job).symm

/-- The waiting-work ledger of one class is the sum of the fixed-window
customers currently selected by its FIFO indicator. -/
theorem priorityWaitingResidualWork_stationaryPriorityFiniteWindowState_eq_sum_waitingJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n) :
    priorityWaitingResidualWork
      (stationaryPriorityFiniteWindowState meanService omega left time) priority =
      ((stationaryPriorityFiniteWindowWaitingJobs
        meanService omega left time right priority).map (fun job => job.serviceWork)).sum := by
  have hperm := perm_waiting_stationaryPriorityFiniteWindowState
    meanService omega left time right hleft hright priority
  simpa [priorityWaitingResidualWork] using
    (hperm.map (fun job => job.serviceWork)).sum_eq

/-- The priority-filtered waiting workload is the corresponding finite sum
over fixed-window customer lists. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_sum_waitingJobs
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega left time) priority =
      ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
        ((stationaryPriorityFiniteWindowWaitingJobs
          meanService omega left time right level).map (fun job => job.serviceWork)).sum := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_congr rfl
  intro level hlevel
  exact priorityWaitingResidualWork_stationaryPriorityFiniteWindowState_eq_sum_waitingJobs
    meanService omega left time right hleft hright level

/-- Filtering a finite customer ledger before summing a reward is equivalent
to summing the reward with a zero contribution from unselected customers. -/
theorem sum_map_filter_eq_sum_map_ite
    {α : Type*} (jobs : List α) (predicate : α → Bool) (reward : α → ℝ) :
    ((jobs.filter predicate).map reward).sum =
      (jobs.map (fun job => if predicate job then reward job else 0)).sum := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      by_cases hpredicate : predicate job
      · simp [hpredicate, ih]
      · simp [hpredicate, ih]

/-- The service-work contribution of a fixed-window customer to one FIFO
class at one replay time. -/
noncomputable def stationaryPriorityFiniteWindowWaitingContribution
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) : ℝ := by
  classical
  exact if job.priority = priority ∧
      nonpreemptivePriorityWaitingIdentifier job.identifier
        (stationaryPriorityFiniteWindowState meanService omega left time)
    then job.serviceWork else 0

/-- The all-class priority-filtered contribution of one fixed-window
customer at one replay time. -/
noncomputable def stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) : ℝ := by
  classical
  exact if job.priority ≤ priority then job.serviceWork *
    nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
      (stationaryPriorityFiniteWindowState meanService omega left time) else 0

/-- The fixed-ledger priority-filtered waiting contribution of a customer
vanishes at and before that customer's arrival epoch. -/
theorem stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution_eq_zero_of_time_le_arrival
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right)
    (htime : time ≤ job.arrivalTime) :
    stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
      meanService omega left time priority job = 0 := by
  unfold stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
  rw [nonpreemptivePriorityWaitingIdentifierIndicator_eq_zero_of_time_le_arrival
    meanService omega left time right hleft hright job hjob htime]
  simp

/-- The interval occupation of one fixed priority-filtered ledger customer
starts at that customer's literal arrival time. -/
theorem intervalIntegral_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution_eq_from_arrival
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left right : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left right) :
    (∫ time in left..right,
      stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority job) =
      ∫ time in job.arrivalTime..right,
        stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left time priority job := by
  unfold stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
  by_cases hpriority : job.priority ≤ priority
  · simp only [hpriority, ↓reduceIte]
    rw [stationaryPriorityArrivalWindowJob_serviceWork_eq_workRequirement
      meanService omega left right job hjob]
    exact intervalIntegral_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_from_arrival
      meanService omega left right job hjob
  · simp [hpriority]

/-- Each one-customer contribution in a finite priority ledger is
interval-integrable on every bounded observation interval. -/
theorem intervalIntegrable_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left a b : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega left b) :
    IntervalIntegrable (fun time =>
      stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority job)
      MeasureTheory.volume a b := by
  unfold stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
  by_cases hpriority : job.priority ≤ priority
  · simp only [hpriority, ↓reduceIte]
    rw [stationaryPriorityArrivalWindowJob_serviceWork_eq_workRequirement
      meanService omega left b job hjob]
    exact intervalIntegrable_stationaryPriorityFiniteWindowWaitingIdentifierContribution
      meanService omega left a b job.identifier
  · simp [hpriority]

/-- A finite fixed ledger can be integrated customer by customer over a
bounded observation interval. -/
theorem intervalIntegrable_map_sum_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left a b : ℝ) (priority : Fin n)
    (jobs : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hjobs : ∀ job ∈ jobs,
      job ∈ stationaryPriorityArrivalWindowJobs meanService omega left b) :
    IntervalIntegrable (fun time =>
      (jobs.map (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority)).sum)
      MeasureTheory.volume a b := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply (intervalIntegrable_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left a b priority job (hjobs job (by simp))).add
      exact ih (fun other hother => hjobs other (List.mem_cons_of_mem _ hother))

/-- The finite fixed-ledger waiting occupation is the sum of the individual
customer occupations over the same physical interval. -/
theorem intervalIntegral_map_sum_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution_eq_sum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left a b : ℝ) (priority : Fin n)
    (jobs : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hjobs : ∀ job ∈ jobs,
      job ∈ stationaryPriorityArrivalWindowJobs meanService omega left b) :
    (∫ time in a..b,
      (jobs.map (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority)).sum) =
      (jobs.map fun job => ∫ time in a..b,
        stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left time priority job).sum := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      have hhead :=
        intervalIntegrable_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left a b priority job (hjobs job (by simp))
      have htail :=
        intervalIntegrable_map_sum_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left a b priority jobs
          (fun other hother => hjobs other (List.mem_cons_of_mem _ hother))
      simp only [List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add hhead htail,
        ih (fun other hother => hjobs other (List.mem_cons_of_mem _ hother))]

/-- A classwise customer contribution is zero except at the customer's own
priority, where it is its service work times the literal FIFO indicator. -/
theorem stationaryPriorityFiniteWindowWaitingContribution_eq_ite
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time : ℝ) (level : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    stationaryPriorityFiniteWindowWaitingContribution meanService omega left time level job =
      if level = job.priority then job.serviceWork *
        nonpreemptivePriorityWaitingIdentifierIndicator job.identifier
          (stationaryPriorityFiniteWindowState meanService omega left time) else 0 := by
  classical
  unfold stationaryPriorityFiniteWindowWaitingContribution
    nonpreemptivePriorityWaitingIdentifierIndicator
  by_cases hlevel : level = job.priority
  · subst level
    by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier job.identifier
        (stationaryPriorityFiniteWindowState meanService omega left time) <;>
      simp [hwaiting]
  · have hpriority : job.priority ≠ level := Ne.symm hlevel
    simp [hlevel, hpriority]

/-- Summing the classwise contribution of one customer over all eligible
priority classes gives its single at-least-as-urgent contribution. -/
theorem sum_stationaryPriorityFiniteWindowWaitingContribution_eq_atLeastAsUrgent
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time : ℝ) (priority : Fin n)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
      stationaryPriorityFiniteWindowWaitingContribution meanService omega left time level job =
      stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority job := by
  classical
  let state := stationaryPriorityFiniteWindowState meanService omega left time
  let work := job.serviceWork *
    nonpreemptivePriorityWaitingIdentifierIndicator job.identifier state
  have hclass : ∀ level : Fin n,
      stationaryPriorityFiniteWindowWaitingContribution meanService omega left time level job =
        if level = job.priority then work else 0 := by
    intro level
    simpa [state, work] using
      stationaryPriorityFiniteWindowWaitingContribution_eq_ite
        meanService omega left time level job
  rw [show (fun level : Fin n =>
      stationaryPriorityFiniteWindowWaitingContribution meanService omega left time level job) =
      fun level => if level = job.priority then work else 0 by
        funext level
        exact hclass level]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
  by_cases hpriority : job.priority ≤ priority <;> simp [state, work, hpriority]

/-- A finite ledger's classwise FIFO contributions collapse to one
priority-filtered contribution per customer. -/
theorem sum_map_stationaryPriorityFiniteWindowWaitingContribution_eq_map_atLeastAsUrgent
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time : ℝ) (priority : Fin n)
    (ledger : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))) :
    ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
      (ledger.map (stationaryPriorityFiniteWindowWaitingContribution
        meanService omega left time level)).sum =
      (ledger.map (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
        meanService omega left time priority)).sum := by
  induction ledger with
  | nil => simp
  | cons job ledger ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih,
        sum_stationaryPriorityFiniteWindowWaitingContribution_eq_atLeastAsUrgent
          meanService omega left time priority job]

/-- The priority-filtered waiting workload at an intermediate finite replay
time is a sum over one fixed marked-arrival ledger; each customer contributes
its work exactly when its literal FIFO indicator is on. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerSum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega left time) priority =
      ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
        ((stationaryPriorityArrivalWindowJobs meanService omega left right).map
          (stationaryPriorityFiniteWindowWaitingContribution
            meanService omega left time level)).sum := by
  classical
  rw [priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_sum_waitingJobs
    meanService omega left time right hleft hright priority]
  apply Finset.sum_congr rfl
  intro level hlevel
  unfold stationaryPriorityFiniteWindowWaitingJobs
    stationaryPriorityFiniteWindowWaitingContribution
  simpa only [decide_eq_true_eq] using
    (sum_map_filter_eq_sum_map_ite
      (stationaryPriorityArrivalWindowJobs meanService omega left right)
      (fun job => decide (job.priority = level ∧
        nonpreemptivePriorityWaitingIdentifier job.identifier
          (stationaryPriorityFiniteWindowState meanService omega left time)))
      (fun job => job.serviceWork))

/-- The priority-filtered waiting workload at an intermediate finite replay
time is one fixed-ledger sum, with one contribution per customer. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left time right : ℝ) (hleft : left ≤ time) (hright : time ≤ right)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega left time) priority =
      ((stationaryPriorityArrivalWindowJobs meanService omega left right).map
        (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left time priority)).sum := by
  rw [priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerSum
    meanService omega left time right hleft hright priority,
    sum_map_stationaryPriorityFiniteWindowWaitingContribution_eq_map_atLeastAsUrgent]

/-- Integrating a finite stationary priority replay over its physical window
is exactly the integral of the fixed arrival-ledger customer contributions.
The theorem is pathwise; it makes no stochastic compensation claim. -/
theorem intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerSum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ) (hwindow : left ≤ right)
    (priority : Fin n) :
    (∫ time in left..right,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega left time) priority) =
      ∫ time in left..right,
        ∑ level ∈ Finset.univ.filter (fun level => level ≤ priority),
          ((stationaryPriorityArrivalWindowJobs meanService omega left right).map
            (stationaryPriorityFiniteWindowWaitingContribution
              meanService omega left time level)).sum := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with time hmember
  rw [Set.uIoc_of_le hwindow] at hmember
  exact priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerSum
    meanService omega left time right hmember.1.le hmember.2 priority

/-- Integrating a finite stationary priority replay over its physical window
is the integral of a single fixed-ledger customer sum. -/
theorem intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ) (hwindow : left ≤ right)
    (priority : Fin n) :
    (∫ time in left..right,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega left time) priority) =
      ∫ time in left..right,
        ((stationaryPriorityArrivalWindowJobs meanService omega left right).map
          (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
            meanService omega left time priority)).sum := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with time hmember
  rw [Set.uIoc_of_le hwindow] at hmember
  exact
    priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
      meanService omega left time right hmember.1.le hmember.2 priority

/-- The finite priority-filtered waiting occupation is exactly the sum of
the post-arrival occupations of its fixed marked customer ledger.  This is a
pathwise finite replay identity and makes no Campbell or stationary-limit
assertion. -/
theorem intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_sum_postArrivalCustomerOccupations
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ) (hwindow : left ≤ right)
    (priority : Fin n) :
    (∫ time in left..right,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega left time) priority) =
      ((stationaryPriorityArrivalWindowJobs meanService omega left right).map fun job =>
        ∫ time in job.arrivalTime..right,
          stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
            meanService omega left time priority job).sum := by
  rw [intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
    meanService omega left right hwindow priority]
  calc
    (∫ time in left..right,
      ((stationaryPriorityArrivalWindowJobs meanService omega left right).map
        (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left time priority)).sum) =
        ((stationaryPriorityArrivalWindowJobs meanService omega left right).map fun job =>
          ∫ time in left..right,
            stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
              meanService omega left time priority job).sum := by
          apply intervalIntegral_map_sum_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution_eq_sum
          intro job hjob
          exact hjob
    _ = ((stationaryPriorityArrivalWindowJobs meanService omega left right).map fun job =>
          ∫ time in job.arrivalTime..right,
            stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
              meanService omega left time priority job).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro job hjob
          exact intervalIntegral_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution_eq_from_arrival
            meanService omega left right priority job hjob

/-- Under the literal selected-Palm law, the selected FIFO indicator has
exactly the capped queue-wait occupation on every nonnegative horizon. -/
theorem ae_forall_intervalIntegral_stationaryPriorityClassTaggedWaitingIndicator_eq_min_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ horizon : ℝ, 0 ≤ horizon →
        (∫ time in 0..horizon,
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
            (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
              meanService i z time)) =
          min horizon (stationaryPriorityClassTaggedQueueWait meanService i z) := by
  filter_upwards [
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwaiting hwait
  intro horizon hhorizon
  have heq : ∀ᵐ time : ℝ ∂MeasureTheory.volume, time ∈ Set.uIoc 0 horizon →
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
            meanService i z time) =
        if time < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 := by
    filter_upwards with time hmember
    rw [Set.uIoc_of_le hhorizon] at hmember
    unfold nonpreemptivePriorityWaitingIdentifierIndicator
    rw [hwaiting time hmember.1.le]
  calc
    (∫ time in 0..horizon,
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z time)) =
        ∫ time in 0..horizon,
          if time < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 :=
      intervalIntegral.integral_congr_ae heq
    _ = min horizon (stationaryPriorityClassTaggedQueueWait meanService i z) :=
      intervalIntegral_indicator_lt_eq_min horizon
        (stationaryPriorityClassTaggedQueueWait meanService i z) hhorizon hwait

/-- Multiplying the selected FIFO indicator by its fixed service requirement
turns the capped occupation into the concrete capped work-times-wait reward. -/
theorem ae_forall_intervalIntegral_stationaryPriorityClassTaggedWork_mul_waitingIndicator_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ horizon : ℝ, 0 ≤ horizon →
        (∫ time in 0..horizon,
          stationaryPriorityClassTaggedWorkRequirement meanService i z *
            nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
              (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
                meanService i z time)) =
          stationaryPriorityClassTaggedWorkRequirement meanService i z *
            min horizon (stationaryPriorityClassTaggedQueueWait meanService i z) := by
  filter_upwards [
    ae_forall_intervalIntegral_stationaryPriorityClassTaggedWaitingIndicator_eq_min_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hoccupation
  intro horizon hhorizon
  rw [intervalIntegral.integral_const_mul,
    hoccupation horizon hhorizon]

end

end AppliedModelingLib.Queueing
