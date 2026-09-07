import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceReflection

/-!
# Capacity-split bounds for finite work-conserving traces

This module compares one work-conserving server with a collection of virtual
class servers whose nonnegative capacities sum to the original capacity.
-/

namespace AppliedModelingLib.Queueing

open scoped BigOperators

noncomputable section

def finiteStableCapacityAllocation
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (load : Class → ℝ) : Class → ℝ :=
  fun i => load i + (1 - ∑ j, load j) / Fintype.card Class

theorem sum_finiteStableCapacityAllocation
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (load : Class → ℝ) :
    ∑ i, finiteStableCapacityAllocation load i = 1 := by
  have hcard : (Fintype.card Class : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteStableCapacityAllocation
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  field_simp
  ring

theorem load_lt_finiteStableCapacityAllocation
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (load : Class → ℝ) (htotal : ∑ j, load j < 1) (i : Class) :
    load i < finiteStableCapacityAllocation load i := by
  have hcard : (0 : ℝ) < Fintype.card Class := by
    exact_mod_cast Fintype.card_pos
  unfold finiteStableCapacityAllocation
  have hslack : 0 < 1 - ∑ j, load j := by linarith
  have hshare : 0 < (1 - ∑ j, load j) / Fintype.card Class :=
    div_pos hslack hcard
  linarith

theorem finiteStableCapacityAllocation_pos_of_nonnegativeLoad
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (load : Class → ℝ) (hnonnegative : ∀ i, 0 ≤ load i)
    (htotal : ∑ j, load j < 1) (i : Class) :
    0 < finiteStableCapacityAllocation load i := by
  exact (hnonnegative i).trans_lt
    (load_lt_finiteStableCapacityAllocation load htotal i)

theorem offeredWork_lt_finiteStableCapacityAllocation
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (arrivalRate meanService : Class → ℝ)
    (htotal : ∑ j, arrivalRate j * meanService j < 1) (i : Class) :
    arrivalRate i * meanService i <
      finiteStableCapacityAllocation (fun j => arrivalRate j * meanService j) i := by
  exact load_lt_finiteStableCapacityAllocation
    (fun j => arrivalRate j * meanService j) htotal i

theorem arrivalRate_lt_finiteStableCapacityAllocation_div_meanService
    {Class : Type*} [Fintype Class] [Nonempty Class]
    (arrivalRate meanService : Class → ℝ)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotal : ∑ j, arrivalRate j * meanService j < 1) (i : Class) :
    arrivalRate i <
      finiteStableCapacityAllocation
        (fun j => arrivalRate j * meanService j) i / meanService i := by
  apply (lt_div_iff₀ (hmeanService i)).2
  simpa [mul_comm] using
    offeredWork_lt_finiteStableCapacityAllocation arrivalRate meanService htotal i

def nonpreemptivePriorityCapacitySplitResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → List (NonpreemptivePriorityJob n JobId) → Fin n → ℝ
  | _, workload, [] => workload
  | time, workload, job :: jobs =>
      nonpreemptivePriorityCapacitySplitResidualWork capacity job.arrivalTime
        (fun i =>
          max 0 (workload i - capacity i * (job.arrivalTime - time)) +
            if job.priority = i then job.serviceWork else 0)
        jobs

def nonpreemptivePriorityCapacitySplitEndTime
    {n : ℕ} {JobId : Type*} :
    ℝ → List (NonpreemptivePriorityJob n JobId) → ℝ
  | time, [] => time
  | _, job :: jobs => nonpreemptivePriorityCapacitySplitEndTime job.arrivalTime jobs

theorem nonpreemptivePriorityCapacitySplitEndTime_eq_arrivalTraceEndTime
    {n : ℕ} {JobId : Type*} (time : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityCapacitySplitEndTime time jobs =
      nonpreemptivePriorityArrivalTraceEndTime time jobs := by
  induction jobs generalizing time with
  | nil => rfl
  | cons job jobs ih =>
      exact ih job.arrivalTime

def nonpreemptivePriorityCapacitySplitTerminalResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time : ℝ) (workload : Fin n → ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminalTime : ℝ) : Fin n → ℝ :=
  fun i => max 0
    (nonpreemptivePriorityCapacitySplitResidualWork capacity time workload jobs i -
      capacity i *
        (terminalTime - nonpreemptivePriorityCapacitySplitEndTime time jobs))

def classCapacitySplitResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ) (selected : Fin n) :
    ℝ → ℝ → List (NonpreemptivePriorityJob n JobId) → ℝ
  | _, workload, [] => workload
  | time, workload, job :: jobs =>
      classCapacitySplitResidualWork capacity selected job.arrivalTime
        (max 0 (workload - capacity selected * (job.arrivalTime - time)) +
          if job.priority = selected then job.serviceWork else 0)
        jobs

def classCapacitySplitTerminalResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ) (selected : Fin n)
    (time workload : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminalTime : ℝ) : ℝ :=
  max 0
    (classCapacitySplitResidualWork capacity selected time workload jobs -
      capacity selected *
        (terminalTime - nonpreemptivePriorityCapacitySplitEndTime time jobs))

def nonpreemptivePriorityJobClassMaskScaleServiceWork
    {n : ℕ} {JobId : Type*} (selected : Fin n) (scale : ℝ)
    (job : NonpreemptivePriorityJob n JobId) : NonpreemptivePriorityJob n JobId :=
  { identifier := job.identifier
    priority := job.priority
    arrivalTime := job.arrivalTime
    serviceWork := if job.priority = selected then scale * job.serviceWork else 0 }

theorem nonpreemptivePriorityCapacitySplitResidualWork_apply_eq_classCapacitySplitResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time : ℝ) (workload : Fin n → ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (selected : Fin n) :
    nonpreemptivePriorityCapacitySplitResidualWork capacity time workload jobs selected =
      classCapacitySplitResidualWork capacity selected time (workload selected) jobs := by
  induction jobs generalizing time workload with
  | nil => rfl
  | cons job jobs ih =>
      change nonpreemptivePriorityCapacitySplitResidualWork capacity job.arrivalTime
        (fun i =>
          max 0 (workload i - capacity i * (job.arrivalTime - time)) +
            if job.priority = i then job.serviceWork else 0)
        jobs selected =
        classCapacitySplitResidualWork capacity selected job.arrivalTime
          (max 0 (workload selected - capacity selected * (job.arrivalTime - time)) +
            if job.priority = selected then job.serviceWork else 0)
          jobs
      rw [ih]

theorem nonpreemptivePriorityCapacitySplitTerminalResidualWork_apply_eq_classCapacitySplitTerminalResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time : ℝ) (workload : Fin n → ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminalTime : ℝ) (selected : Fin n) :
    nonpreemptivePriorityCapacitySplitTerminalResidualWork
      capacity time workload jobs terminalTime selected =
      classCapacitySplitTerminalResidualWork capacity selected time
        (workload selected) jobs terminalTime := by
  unfold nonpreemptivePriorityCapacitySplitTerminalResidualWork
    classCapacitySplitTerminalResidualWork
  rw [nonpreemptivePriorityCapacitySplitResidualWork_apply_eq_classCapacitySplitResidualWork]

theorem classCapacitySplitResidualWork_eq_scale_arrivalTraceResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ) (selected : Fin n)
    (hcapacity : 0 < capacity selected)
    (time initial : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId)) :
    classCapacitySplitResidualWork capacity selected time
      (capacity selected * initial) jobs =
      capacity selected * nonpreemptivePriorityArrivalTraceResidualWork time initial
        (jobs.map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
            (capacity selected)⁻¹)) := by
  induction jobs generalizing time initial with
  | nil => simp [classCapacitySplitResidualWork,
      nonpreemptivePriorityArrivalTraceResidualWork]
  | cons job jobs ih =>
      let elapsed : ℝ := job.arrivalTime - time
      let next : ℝ := max 0 (initial - elapsed) +
        if job.priority = selected then (capacity selected)⁻¹ * job.serviceWork else 0
      have hstep :
          max 0 (capacity selected * initial - capacity selected * elapsed) +
            (if job.priority = selected then job.serviceWork else 0) =
          capacity selected * next := by
        dsimp [next]
        have hlinear : capacity selected * (initial - elapsed) =
            capacity selected * initial - capacity selected * elapsed := by ring
        have hmax :
            max 0 (capacity selected * initial - capacity selected * elapsed) =
              capacity selected * max 0 (initial - elapsed) := by
          calc
            max 0 (capacity selected * initial - capacity selected * elapsed) =
                max (capacity selected * 0)
                  (capacity selected * (initial - elapsed)) := by
                    rw [hlinear]
                    simp
            _ = capacity selected * max 0 (initial - elapsed) :=
              (mul_max_of_nonneg _ _ hcapacity.le).symm
        rw [hmax, mul_add]
        split_ifs with hselected
        · rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcapacity), one_mul]
        · ring
      change classCapacitySplitResidualWork capacity selected job.arrivalTime
        (max 0 (capacity selected * initial -
          capacity selected * (job.arrivalTime - time)) +
          if job.priority = selected then job.serviceWork else 0) jobs = _
      rw [show job.arrivalTime - time = elapsed by rfl, hstep]
      simpa [nonpreemptivePriorityJobClassMaskScaleServiceWork] using
        ih job.arrivalTime next

theorem nonpreemptivePriorityArrivalTraceEndTime_map_classMaskScaleServiceWork
    {n : ℕ} {JobId : Type*} (time : ℝ)
    (selected : Fin n) (scale : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceEndTime time
      (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) =
      nonpreemptivePriorityArrivalTraceEndTime time jobs := by
  induction jobs generalizing time with
  | nil => rfl
  | cons job jobs ih =>
      exact ih job.arrivalTime

theorem nonpreemptivePriorityArrivalTraceServiceWork_map_classMaskScaleServiceWork_eq_filter
    {n : ℕ} {JobId : Type*} (selected : Fin n) (scale : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityArrivalTraceServiceWork
      (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) =
      nonpreemptivePriorityArrivalTraceServiceWork
        ((jobs.filter fun job => job.priority = selected).map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      by_cases hselected : job.priority = selected
      · simpa [nonpreemptivePriorityArrivalTraceServiceWork,
          nonpreemptivePriorityJobClassMaskScaleServiceWork, hselected] using
          congrArg (fun x : ℝ => scale * job.serviceWork + x) ih
      · simpa [nonpreemptivePriorityArrivalTraceServiceWork,
          nonpreemptivePriorityJobClassMaskScaleServiceWork, hselected] using ih

private theorem maskedHeadNetWork_le_suffixMaximum_tail
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (head : NonpreemptivePriorityJob n JobId)
    (tail : List (NonpreemptivePriorityJob n JobId))
    (hzero : head.serviceWork = 0)
    (hhead : ∀ other ∈ tail, head.arrivalTime ≤ other.arrivalTime)
    (hend : head.arrivalTime ≤ terminalTime) :
    nonpreemptivePriorityArrivalTraceServiceWork (head :: tail) -
      (terminalTime - head.arrivalTime) ≤
      nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime tail := by
  cases tail with
  | nil =>
      rw [nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_nil]
      simp only [nonpreemptivePriorityArrivalTraceServiceWork,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
      rw [hzero]
      linarith
  | cons next tail =>
      rw [nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
      apply le_trans ?_ (le_max_left _ _)
      simp only [nonpreemptivePriorityArrivalTraceServiceWork, List.map_cons, List.sum_cons]
      rw [hzero]
      have htime : head.arrivalTime ≤ next.arrivalTime := hhead next (by simp)
      linarith

theorem nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_map_classMaskScaleServiceWork_eq_filter
    {n : ℕ} {JobId : Type*} (terminalTime : ℝ)
    (selected : Fin n) (scale : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hsorted : jobs.Pairwise (fun first second => first.arrivalTime ≤ second.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime) :
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime
      (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) =
      nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum terminalTime
        ((jobs.filter fun job => job.priority = selected).map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      have hendTail : ∀ other ∈ jobs, other.arrivalTime ≤ terminalTime := by
        intro other hother
        exact hend other (by simp [hother])
      have htailEq := ih htail hendTail
      by_cases hselected : job.priority = selected
      · have hfilter : (List.filter (fun item => item.priority = selected) (job :: jobs)) =
            job :: List.filter (fun item => item.priority = selected) jobs := by
            simp [hselected]
        rw [hfilter]
        simp only [List.map_cons,
          nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
        rw [htailEq]
        have hservice :=
          nonpreemptivePriorityArrivalTraceServiceWork_map_classMaskScaleServiceWork_eq_filter
            selected scale (job :: jobs)
        rw [hfilter] at hservice
        simp only [List.map_cons] at hservice
        rw [hservice]
      · have hfilter : (List.filter (fun item => item.priority = selected) (job :: jobs)) =
            List.filter (fun item => item.priority = selected) jobs := by
            simp [hselected]
        rw [hfilter, List.map_cons,
          nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_cons]
        have hzero :
            (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale job).serviceWork = 0 := by
          simp [nonpreemptivePriorityJobClassMaskScaleServiceWork, hselected]
        have hheadMap : ∀ other ∈
            jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale),
            (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale job).arrivalTime ≤
              other.arrivalTime := by
          intro other hother
          rcases List.mem_map.mp hother with ⟨original, horiginal, rfl⟩
          simpa [nonpreemptivePriorityJobClassMaskScaleServiceWork] using hhead original horiginal
        have hendHead :
            (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale job).arrivalTime ≤
              terminalTime := by
          simpa [nonpreemptivePriorityJobClassMaskScaleServiceWork] using hend job (by simp)
        rw [max_eq_right
          (maskedHeadNetWork_le_suffixMaximum_tail terminalTime
            (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale job)
            (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale))
            hzero hheadMap hendHead), htailEq]

theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_map_classMaskScaleServiceWork_eq_filter
    {n : ℕ} {JobId : Type*} (time terminalTime : ℝ)
    (selected : Fin n) (scale : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time ≤ terminalTime)
    (hstart : ∀ job ∈ jobs, time ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun first second => first.arrivalTime ≤ second.arrivalTime))
    (hend : ∀ job ∈ jobs, job.arrivalTime ≤ terminalTime) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0
      (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) terminalTime =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0
        ((jobs.filter fun job => job.priority = selected).map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale)) terminalTime := by
  let f : NonpreemptivePriorityJob n JobId → NonpreemptivePriorityJob n JobId :=
    nonpreemptivePriorityJobClassMaskScaleServiceWork selected scale
  have hstartMap : ∀ job ∈ jobs.map f, time ≤ job.arrivalTime := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, rfl⟩
    simpa [f] using hstart original horiginal
  have hsortedMap : (jobs.map f).Pairwise
      (fun first second => first.arrivalTime ≤ second.arrivalTime) := by
    rw [List.pairwise_map]
    simpa [f] using hsorted
  have hendMap : ∀ job ∈ jobs.map f, job.arrivalTime ≤ terminalTime := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, rfl⟩
    simpa [f] using hend original horiginal
  have hstartFilter : ∀ job ∈ (jobs.filter fun job => job.priority = selected).map f,
      time ≤ job.arrivalTime := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, rfl⟩
    exact hstart original ((List.mem_filter.mp horiginal).1)
  have hsortedFilter : ((jobs.filter fun job => job.priority = selected).map f).Pairwise
      (fun first second => first.arrivalTime ≤ second.arrivalTime) := by
    rw [List.pairwise_map]
    simpa [f] using hsorted.filter (fun job => job.priority = selected)
  have hendFilter : ∀ job ∈ (jobs.filter fun job => job.priority = selected).map f,
      job.arrivalTime ≤ terminalTime := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, rfl⟩
    exact hend original ((List.mem_filter.mp horiginal).1)
  rw [nonpreemptivePriorityArrivalTraceTerminalResidualWork_empty_eq_suffixMaximum
    time terminalTime (jobs.map f) htime hstartMap hsortedMap hendMap,
    nonpreemptivePriorityArrivalTraceTerminalResidualWork_empty_eq_suffixMaximum
      time terminalTime ((jobs.filter fun job => job.priority = selected).map f)
      htime hstartFilter hsortedFilter hendFilter]
  simpa [f] using
    nonpreemptivePriorityArrivalTraceSuffixNetWorkMaximum_map_classMaskScaleServiceWork_eq_filter
      terminalTime selected scale jobs hsorted hend

theorem classCapacitySplitTerminalResidualWork_eq_scale_arrivalTraceTerminalResidualWork
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ) (selected : Fin n)
    (hcapacity : 0 < capacity selected)
    (time initial terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    classCapacitySplitTerminalResidualWork capacity selected time
      (capacity selected * initial) jobs terminalTime =
      capacity selected * nonpreemptivePriorityArrivalTraceTerminalResidualWork time initial
        (jobs.map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
            (capacity selected)⁻¹)) terminalTime := by
  unfold classCapacitySplitTerminalResidualWork
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
  rw [classCapacitySplitResidualWork_eq_scale_arrivalTraceResidualWork
    capacity selected hcapacity time initial jobs,
    nonpreemptivePriorityCapacitySplitEndTime_eq_arrivalTraceEndTime,
    nonpreemptivePriorityArrivalTraceEndTime_map_classMaskScaleServiceWork]
  let residual : ℝ := nonpreemptivePriorityArrivalTraceResidualWork time initial
    (jobs.map
      (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
        (capacity selected)⁻¹))
  let elapsed : ℝ := terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs
  have hlinear : capacity selected * residual - capacity selected * elapsed =
      capacity selected * (residual - elapsed) := by ring
  calc
    max 0 (capacity selected * residual - capacity selected * elapsed) =
        max (capacity selected * 0) (capacity selected * (residual - elapsed)) := by
          rw [hlinear]
          simp
    _ = capacity selected * max 0 (residual - elapsed) :=
      (mul_max_of_nonneg _ _ hcapacity.le).symm

private theorem max_sum_sub_elapsed_le_sum_max_sub_capacity_elapsed
    {n : ℕ} (capacity workload : Fin n → ℝ) (elapsed : ℝ)
    (hcapacity : ∑ i, capacity i = 1) :
    max 0 ((∑ i, workload i) - elapsed) ≤
      ∑ i, max 0 (workload i - capacity i * elapsed) := by
  have hrewrite :
      (∑ i, workload i) - elapsed =
        ∑ i, (workload i - capacity i * elapsed) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcapacity]
    ring
  rw [hrewrite]
  apply max_le
  · exact Finset.sum_nonneg fun i _ => le_max_left _ _
  · exact Finset.sum_le_sum fun i _ => le_max_right _ _

private theorem sum_capacitySplitArrivalIncrement
    {n : ℕ} {JobId : Type*} (workload capacity : Fin n → ℝ)
    (elapsed : ℝ) (job : NonpreemptivePriorityJob n JobId) :
    (∑ i, (max 0 (workload i - capacity i * elapsed) +
      if job.priority = i then job.serviceWork else 0)) =
      (∑ i, max 0 (workload i - capacity i * elapsed)) + job.serviceWork := by
  classical
  rw [Finset.sum_add_distrib]
  simp

/-- At every arrival boundary, a unit-capacity work-conserving trace is
dominated by the sum of virtual class traces whose capacities sum to one. -/
theorem nonpreemptivePriorityArrivalTraceResidualWork_le_sum_capacitySplit
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time workload : ℝ) (classWorkload : Fin n → ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hcapacity : ∑ i, capacity i = 1)
    (hworkload : workload ≤ ∑ i, classWorkload i) :
    nonpreemptivePriorityArrivalTraceResidualWork time workload jobs ≤
      ∑ i, nonpreemptivePriorityCapacitySplitResidualWork capacity
        time classWorkload jobs i := by
  induction jobs generalizing time workload classWorkload with
  | nil =>
      simpa [nonpreemptivePriorityArrivalTraceResidualWork,
        nonpreemptivePriorityCapacitySplitResidualWork] using hworkload
  | cons job jobs ih =>
      let elapsed : ℝ := job.arrivalTime - time
      let nextClassWorkload : Fin n → ℝ := fun i =>
        max 0 (classWorkload i - capacity i * elapsed) +
          if job.priority = i then job.serviceWork else 0
      have hsub : workload - elapsed ≤ (∑ i, classWorkload i) - elapsed := by
        linarith
      have hmax : max 0 (workload - elapsed) ≤
          ∑ i, max 0 (classWorkload i - capacity i * elapsed) := by
        calc
          max 0 (workload - elapsed) ≤ max 0 ((∑ i, classWorkload i) - elapsed) :=
            max_le_max_left _ hsub
          _ ≤ ∑ i, max 0 (classWorkload i - capacity i * elapsed) :=
            max_sum_sub_elapsed_le_sum_max_sub_capacity_elapsed
              capacity classWorkload elapsed hcapacity
      have hnext :
          max 0 (workload - elapsed) + job.serviceWork ≤
            ∑ i, nextClassWorkload i := by
        rw [sum_capacitySplitArrivalIncrement]
        linarith
      change nonpreemptivePriorityArrivalTraceResidualWork job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork) jobs ≤ _
      have hnext' :
          max 0 (workload - (job.arrivalTime - time)) + job.serviceWork ≤
            ∑ i, nextClassWorkload i := by
        simpa [elapsed] using hnext
      exact ih job.arrivalTime
        (max 0 (workload - (job.arrivalTime - time)) + job.serviceWork)
        nextClassWorkload hnext'

theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_sum_capacitySplit
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time terminalTime : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hcapacity : ∑ i, capacity i = 1) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time 0 jobs terminalTime ≤
      ∑ i, nonpreemptivePriorityCapacitySplitTerminalResidualWork
        capacity time (fun _ => 0) jobs terminalTime i := by
  let residual : ℝ := nonpreemptivePriorityArrivalTraceResidualWork time 0 jobs
  let split : Fin n → ℝ :=
    nonpreemptivePriorityCapacitySplitResidualWork capacity time (fun _ => 0) jobs
  let elapsed : ℝ := terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs
  have hresidual : residual ≤ ∑ i, split i := by
    exact nonpreemptivePriorityArrivalTraceResidualWork_le_sum_capacitySplit
      capacity time 0 (fun _ => 0)
      jobs hcapacity (by simp)
  have hsub : residual - elapsed ≤ (∑ i, split i) - elapsed := by
    linarith
  have hmax : max 0 (residual - elapsed) ≤
      ∑ i, max 0 (split i - capacity i * elapsed) := by
    calc
      max 0 (residual - elapsed) ≤ max 0 ((∑ i, split i) - elapsed) :=
        max_le_max_left _ hsub
      _ ≤ ∑ i, max 0 (split i - capacity i * elapsed) :=
        max_sum_sub_elapsed_le_sum_max_sub_capacity_elapsed capacity split elapsed hcapacity
  change max 0
      (nonpreemptivePriorityArrivalTraceResidualWork time 0 jobs -
        (terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs)) ≤ _
  rw [show (fun i =>
      nonpreemptivePriorityCapacitySplitTerminalResidualWork
        capacity time (fun _ => 0) jobs terminalTime i) =
      fun i => max 0 (split i - capacity i * elapsed) by
        funext i
        simp only [nonpreemptivePriorityCapacitySplitTerminalResidualWork, split, elapsed,
          nonpreemptivePriorityCapacitySplitEndTime_eq_arrivalTraceEndTime]]
  exact hmax

/-- The capacity-split terminal-work bound also holds from arbitrary initial
work whenever that work is bounded by the sum of the virtual initial loads. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_sum_capacitySplit_of_le
    {n : ℕ} {JobId : Type*} (capacity : Fin n → ℝ)
    (time workload terminalTime : ℝ) (classWorkload : Fin n → ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hcapacity : ∑ i, capacity i = 1)
    (hworkload : workload ≤ ∑ i, classWorkload i) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork time workload jobs terminalTime ≤
      ∑ i, nonpreemptivePriorityCapacitySplitTerminalResidualWork
        capacity time classWorkload jobs terminalTime i := by
  let residual : ℝ := nonpreemptivePriorityArrivalTraceResidualWork time workload jobs
  let split : Fin n → ℝ :=
    nonpreemptivePriorityCapacitySplitResidualWork capacity time classWorkload jobs
  let elapsed : ℝ := terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs
  have hresidual : residual ≤ ∑ i, split i := by
    exact nonpreemptivePriorityArrivalTraceResidualWork_le_sum_capacitySplit
      capacity time workload classWorkload jobs hcapacity hworkload
  have hsub : residual - elapsed ≤ (∑ i, split i) - elapsed := by
    linarith
  have hmax : max 0 (residual - elapsed) ≤
      ∑ i, max 0 (split i - capacity i * elapsed) := by
    calc
      max 0 (residual - elapsed) ≤ max 0 ((∑ i, split i) - elapsed) :=
        max_le_max_left _ hsub
      _ ≤ ∑ i, max 0 (split i - capacity i * elapsed) :=
        max_sum_sub_elapsed_le_sum_max_sub_capacity_elapsed capacity split elapsed hcapacity
  change max 0
      (nonpreemptivePriorityArrivalTraceResidualWork time workload jobs -
        (terminalTime - nonpreemptivePriorityArrivalTraceEndTime time jobs)) ≤ _
  rw [show (fun i =>
      nonpreemptivePriorityCapacitySplitTerminalResidualWork
        capacity time classWorkload jobs terminalTime i) =
      fun i => max 0 (split i - capacity i * elapsed) by
        funext i
        simp only [nonpreemptivePriorityCapacitySplitTerminalResidualWork, split, elapsed,
          nonpreemptivePriorityCapacitySplitEndTime_eq_arrivalTraceEndTime]]
  exact hmax

end

end AppliedModelingLib.Queueing
