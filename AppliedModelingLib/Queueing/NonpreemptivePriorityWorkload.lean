import AppliedModelingLib.Queueing.NonpreemptivePriorityFiniteTrace

/-!
# Residual workload of finite nonpreemptive-priority states

The server discipline changes job order but not aggregate unfinished work.
These definitions expose that aggregate on the concrete finite trace state,
which is the quantity coupled to a reflected stationary workload in later
layers.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-- Residual work held in a single class-FIFO waiting list. -/
def priorityWaitingResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) : ℝ :=
  (state.waiting i).map (fun job => job.serviceWork) |>.sum

/-- Residual waiting work in classes at least as urgent as `i`, with lower
`Fin` indices denoting higher urgency.  This excludes any currently active
job, whose nonpreemptive residual is accounted for separately. -/
def priorityWaitingResidualWorkAtLeastAsUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), priorityWaitingResidualWork state j

/-- Residual waiting work in classes strictly less urgent than `i`.  Together
with `priorityWaitingResidualWorkAtLeastAsUrgent`, this partitions all waiting
work by priority. -/
def priorityWaitingResidualWorkLessUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i < j), priorityWaitingResidualWork state j

/-- Residual work of the active job, with zero contribution from an idle
server. -/
def activeNonpreemptivePriorityResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : ℝ :=
  match state.active with
  | none => 0
  | some (_, residual) => residual

/-- Total unfinished work in the active server and all class-FIFO lists. -/
def totalNonpreemptivePriorityResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : ℝ :=
  activeNonpreemptivePriorityResidualWork state +
    ∑ i, priorityWaitingResidualWork state i

/-- The sum of squared residual requirements held by a finite priority state.
The active coordinate uses its remaining work, while every waiting job has not
yet received service and therefore contributes the square of its full service
requirement.  This ledger is preserved when a waiting job is dispatched and
loses precisely the completed job's square at a service completion. -/
def totalNonpreemptivePrioritySquaredResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : ℝ :=
  activeNonpreemptivePriorityResidualWork state ^ 2 +
    ∑ i, ((state.waiting i).map
      (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum

/-- The squared residual-work ledger is nonnegative for every finite priority
state. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_nonneg
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    0 ≤ totalNonpreemptivePrioritySquaredResidualWork state := by
  unfold totalNonpreemptivePrioritySquaredResidualWork
  apply add_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply List.sum_nonneg
  intro work hmember
  rcases List.mem_map.mp hmember with ⟨job, _, rfl⟩
  exact sq_nonneg _

/-- Updating only the physical clock leaves every live residual requirement,
and hence its squared ledger, unchanged. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (time : ℝ) :
    totalNonpreemptivePrioritySquaredResidualWork { state with currentTime := time } =
      totalNonpreemptivePrioritySquaredResidualWork state := by
  rfl

/-- Live-equivalent states have the same aggregate residual workload.  The
completion ledger is intentionally absent from both notions, because it has no
effect on present or future service work. -/
theorem totalNonpreemptivePriorityResidualWork_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (heq : liveEquivalentNonpreemptivePriorityWorkState first second) :
    totalNonpreemptivePriorityResidualWork first =
      totalNonpreemptivePriorityResidualWork second := by
  rcases heq with ⟨_, hactive, hwaiting⟩
  simp only [totalNonpreemptivePriorityResidualWork,
    activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork,
    hactive, hwaiting]

/-- Live-equivalent states have the same residual work of the active job. -/
theorem activeNonpreemptivePriorityResidualWork_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (heq : liveEquivalentNonpreemptivePriorityWorkState first second) :
    activeNonpreemptivePriorityResidualWork first =
      activeNonpreemptivePriorityResidualWork second := by
  rcases heq with ⟨_, hactive, _⟩
  simp [activeNonpreemptivePriorityResidualWork, hactive]

/-- Live-equivalent states have the same waiting work in each priority class. -/
theorem priorityWaitingResidualWork_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (heq : liveEquivalentNonpreemptivePriorityWorkState first second) (i : Fin n) :
    priorityWaitingResidualWork first i = priorityWaitingResidualWork second i := by
  rcases heq with ⟨_, _, hwaiting⟩
  simp [priorityWaitingResidualWork, hwaiting]

/-- Live-equivalent states have the same waiting work aggregated over every
initial priority segment. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (heq : liveEquivalentNonpreemptivePriorityWorkState first second) (i : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent first i =
      priorityWaitingResidualWorkAtLeastAsUrgent second i := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_congr rfl
  intro j _
  exact priorityWaitingResidualWork_eq_of_liveEquivalent heq j

/-- Live-equivalent states have the same squared-residual ledger. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (heq : liveEquivalentNonpreemptivePriorityWorkState first second) :
    totalNonpreemptivePrioritySquaredResidualWork first =
      totalNonpreemptivePrioritySquaredResidualWork second := by
  rcases heq with ⟨_, hactive, hwaiting⟩
  simp [totalNonpreemptivePrioritySquaredResidualWork,
    activeNonpreemptivePriorityResidualWork, hactive, hwaiting]

/-- All stored residual work is nonnegative.  An active job stores its mutable
residual amount; waiting jobs have not started and therefore contribute their
declared service work. -/
def nonnegativeNonpreemptivePriorityResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  (∀ active, state.active = some active → 0 ≤ active.2) ∧
    ∀ (i : Fin n) (job : NonpreemptivePriorityJob n JobId),
      job ∈ state.waiting i → 0 ≤ job.serviceWork

/-- Every stored residual work amount is strictly positive. -/
def positiveNonpreemptivePriorityResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  (∀ active, state.active = some active → 0 < active.2) ∧
    ∀ (i : Fin n) (job : NonpreemptivePriorityJob n JobId),
      job ∈ state.waiting i → 0 < job.serviceWork

/-- Strictly positive stored work is in particular nonnegative. -/
theorem positiveNonpreemptivePriorityResidualWork.nonnegative
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state) :
    nonnegativeNonpreemptivePriorityResidualWork state := by
  constructor
  · intro active hactive
    exact (hwork.1 active hactive).le
  · intro i job hmember
    exact (hwork.2 i job hmember).le

/-- A finite real list with nonnegative entries and one positive entry has
strictly positive sum. -/
theorem list_sum_pos_of_mem_pos_of_nonneg
    (values : List ℝ) (value : ℝ)
    (hmember : value ∈ values) (hpositive : 0 < value)
    (hnonnegative : ∀ other ∈ values, 0 ≤ other) :
    0 < values.sum := by
  induction values with
  | nil => simp at hmember
  | cons head tail ih =>
      rw [List.sum_cons]
      rw [List.mem_cons] at hmember
      rcases hmember with hmember | hmember
      · subst value
        exact add_pos_of_pos_of_nonneg hpositive
          (List.sum_nonneg fun other hother => hnonnegative other (by simp [hother]))
      · exact add_pos_of_nonneg_of_pos
          (hnonnegative head (by simp))
          (ih hmember
            (fun other hother => hnonnegative other (by simp [hother])))

/-- Any positive-work job in a class queue makes that class's aggregate
waiting work strictly positive. -/
theorem priorityWaitingResidualWork_pos_of_mem
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state)
    (i : Fin n) (job : NonpreemptivePriorityJob n JobId)
    (hmember : job ∈ state.waiting i) :
    0 < priorityWaitingResidualWork state i := by
  unfold priorityWaitingResidualWork
  apply list_sum_pos_of_mem_pos_of_nonneg
    ((state.waiting i).map fun job => job.serviceWork) job.serviceWork
  · exact List.mem_map.mpr ⟨job, hmember, rfl⟩
  · exact hwork.2 i job hmember
  · intro work hworkMember
    rcases List.mem_map.mp hworkMember with ⟨other, hother, rfl⟩
    exact (hwork.2 i other hother).le

/-- In a state whose stored residual work is strictly positive, zero aggregate
work is equivalent to an actually empty server and empty class-FIFO lists. -/
theorem active_eq_none_and_waiting_eq_nil_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (htotal : totalNonpreemptivePriorityResidualWork state = 0) :
    state.active = none ∧ ∀ i, state.waiting i = [] := by
  constructor
  · by_contra hnot
    cases hactive : state.active with
    | none => exact hnot hactive
    | some active =>
        have hactivePos : 0 < active.2 := hpositive.1 active hactive
        have hwaitingNonneg : 0 ≤ ∑ i, priorityWaitingResidualWork state i := by
          apply Finset.sum_nonneg
          intro i _
          unfold priorityWaitingResidualWork
          apply List.sum_nonneg
          intro work hmember
          rcases List.mem_map.mp hmember with ⟨job, hjob, rfl⟩
          exact (hpositive.2 i job hjob).le
        unfold totalNonpreemptivePriorityResidualWork
          activeNonpreemptivePriorityResidualWork at htotal
        simp [hactive] at htotal
        linarith
  · intro i
    by_contra hnot
    rcases List.exists_mem_of_ne_nil (state.waiting i) hnot with ⟨job, hjob⟩
    have hwaitingPos : 0 < priorityWaitingResidualWork state i :=
      priorityWaitingResidualWork_pos_of_mem state hpositive i job hjob
    have hactiveNonneg : 0 ≤ activeNonpreemptivePriorityResidualWork state := by
      unfold activeNonpreemptivePriorityResidualWork
      cases hactive : state.active with
      | none => simp
      | some active => exact (hpositive.1 active hactive).le
    have hsumPos : 0 < ∑ j, priorityWaitingResidualWork state j :=
      Finset.sum_pos'
        (fun j _ => by
          unfold priorityWaitingResidualWork
          apply List.sum_nonneg
          intro work hmember
          rcases List.mem_map.mp hmember with ⟨other, hother, rfl⟩
          exact (hpositive.2 j other hother).le)
        ⟨i, Finset.mem_univ i, hwaitingPos⟩
    unfold totalNonpreemptivePriorityResidualWork at htotal
    linarith

/-- A nonnegative finite state has nonnegative waiting work in each class. -/
theorem priorityWaitingResidualWork_nonneg
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (i : Fin n) :
    0 ≤ priorityWaitingResidualWork state i := by
  unfold priorityWaitingResidualWork
  apply List.sum_nonneg
  intro work hmember
  rcases List.mem_map.mp hmember with ⟨job, hjob, rfl⟩
  exact hwork.2 i job hjob

/-- For a finite list of nonnegative reals, the sum of the squared entries is
bounded by the square of their sum. -/
theorem list_map_sq_sum_le_sq_sum_of_forall_mem_nonneg
    (works : List ℝ) (hwork : ∀ work ∈ works, 0 ≤ work) :
    (works.map (fun work => work ^ 2)).sum ≤ works.sum ^ 2 := by
  induction works with
  | nil => simp
  | cons work works ih =>
      have hhead : 0 ≤ work := hwork work (by simp)
      have htail : ∀ tailWork ∈ works, 0 ≤ tailWork := by
        intro tailWork hmember
        exact hwork tailWork (by simp [hmember])
      have hsum : 0 ≤ works.sum := by
        apply List.sum_nonneg
        intro tailWork hmember
        exact htail tailWork hmember
      calc
        (List.map (fun work => work ^ 2) (work :: works)).sum =
            work ^ 2 + (works.map (fun work => work ^ 2)).sum := by simp
        _ ≤ work ^ 2 + works.sum ^ 2 := by gcongr; exact ih htail
        _ ≤ (work + works.sum) ^ 2 := by
          nlinarith [mul_nonneg hhead hsum]
        _ = (work :: works).sum ^ 2 := by simp

/-- The squared residual-work ledger of a nonnegative finite priority state is
bounded by the square of its total residual work. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_le_sq_totalNonpreemptivePriorityResidualWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    totalNonpreemptivePrioritySquaredResidualWork state ≤
      (totalNonpreemptivePriorityResidualWork state) ^ 2 := by
  have hactive : 0 ≤ activeNonpreemptivePriorityResidualWork state := by
    unfold activeNonpreemptivePriorityResidualWork
    cases hactiveState : state.active with
    | none => simp
    | some active => exact hwork.1 active hactiveState
  have hwaiting : ∀ i : Fin n, 0 ≤ priorityWaitingResidualWork state i := by
    intro i
    exact priorityWaitingResidualWork_nonneg state hwork i
  have hwaitingSq : ∑ i, (priorityWaitingResidualWork state i) ^ 2 ≤
      (∑ i, priorityWaitingResidualWork state i) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hwaiting i
  have hwaitingSum : 0 ≤ ∑ i, priorityWaitingResidualWork state i := by
    exact Finset.sum_nonneg fun i _ => hwaiting i
  have hlist : ∀ i : Fin n,
      ((state.waiting i).map
        (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum ≤
        (priorityWaitingResidualWork state i) ^ 2 := by
    intro i
    have hvalues : ∀ work ∈ (state.waiting i).map
        (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork), 0 ≤ work := by
      intro work hmember
      rcases List.mem_map.mp hmember with ⟨job, hjob, rfl⟩
      exact hwork.2 i job hjob
    simpa only [priorityWaitingResidualWork, List.map_map, Function.comp_apply] using
      (list_map_sq_sum_le_sq_sum_of_forall_mem_nonneg
        ((state.waiting i).map
          (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork)) hvalues)
  unfold totalNonpreemptivePrioritySquaredResidualWork
    totalNonpreemptivePriorityResidualWork
  calc
    activeNonpreemptivePriorityResidualWork state ^ 2 + ∑ i,
        ((state.waiting i).map
          (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum ≤
        activeNonpreemptivePriorityResidualWork state ^ 2 + ∑ i,
          (priorityWaitingResidualWork state i) ^ 2 := by
            exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => hlist i)
    _ ≤ (activeNonpreemptivePriorityResidualWork state +
        ∑ i, priorityWaitingResidualWork state i) ^ 2 := by
          nlinarith [hwaitingSq, mul_nonneg hactive hwaitingSum]

/-- At-least-as-urgent waiting work is nonnegative when every stored residual
work amount is nonnegative. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_nonneg
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (i : Fin n) :
    0 ≤ priorityWaitingResidualWorkAtLeastAsUrgent state i := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_nonneg
  intro j _
  exact priorityWaitingResidualWork_nonneg state hwork j

/-- Strictly-less-urgent waiting work is nonnegative when every stored
residual work amount is nonnegative. -/
theorem priorityWaitingResidualWorkLessUrgent_nonneg
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (i : Fin n) :
    0 ≤ priorityWaitingResidualWorkLessUrgent state i := by
  unfold priorityWaitingResidualWorkLessUrgent
  apply Finset.sum_nonneg
  intro j _
  exact priorityWaitingResidualWork_nonneg state hwork j

/-- The total unfinished work partitions into the active residual, waiting
work at least as urgent as a designated priority, and less-urgent waiting
work. -/
theorem totalNonpreemptivePriorityResidualWork_eq_active_add_waitingAtLeastAsUrgent_add_lessUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    totalNonpreemptivePriorityResidualWork state =
      activeNonpreemptivePriorityResidualWork state +
        priorityWaitingResidualWorkAtLeastAsUrgent state i +
          priorityWaitingResidualWorkLessUrgent state i := by
  classical
  unfold totalNonpreemptivePriorityResidualWork
    priorityWaitingResidualWorkAtLeastAsUrgent
    priorityWaitingResidualWorkLessUrgent
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ≤ i)]
  simp only [not_le]
  ring

/-- Waiting work at least as urgent as `i` is bounded by total unfinished
work whenever all stored residual amounts are nonnegative. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_le_total
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (i : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent state i ≤
      totalNonpreemptivePriorityResidualWork state := by
  have hactive : 0 ≤ activeNonpreemptivePriorityResidualWork state := by
    unfold activeNonpreemptivePriorityResidualWork
    cases hactive : state.active with
    | none => simp
    | some active => exact hwork.1 active hactive
  have hless : 0 ≤ priorityWaitingResidualWorkLessUrgent state i :=
    priorityWaitingResidualWorkLessUrgent_nonneg state hwork i
  rw [totalNonpreemptivePriorityResidualWork_eq_active_add_waitingAtLeastAsUrgent_add_lessUrgent]
  linarith

/-- Active residual work is bounded by total unfinished work whenever all
stored residual amounts are nonnegative. -/
theorem activeNonpreemptivePriorityResidualWork_le_total
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    activeNonpreemptivePriorityResidualWork state ≤
      totalNonpreemptivePriorityResidualWork state := by
  unfold totalNonpreemptivePriorityResidualWork
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j _
  exact priorityWaitingResidualWork_nonneg state hwork j

/-- Tail admission adds exactly the admitted service work to the selected
class's residual-work ledger. -/
theorem priorityWaitingResidualWork_enqueue_selected
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    priorityWaitingResidualWork (enqueueNonpreemptivePriorityJob state job) job.priority =
      priorityWaitingResidualWork state job.priority + job.serviceWork := by
  unfold priorityWaitingResidualWork
  rw [enqueueNonpreemptivePriorityJob_waiting_selected]
  simp

/-- Tail admission leaves every other class's residual-work ledger unchanged. -/
theorem priorityWaitingResidualWork_enqueue_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hi : i ≠ job.priority) :
    priorityWaitingResidualWork (enqueueNonpreemptivePriorityJob state job) i =
      priorityWaitingResidualWork state i := by
  unfold priorityWaitingResidualWork
  rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state job i hi]

/-- A tail admission increases total unfinished work by exactly the admitted
job's service requirement. -/
theorem totalNonpreemptivePriorityResidualWork_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    totalNonpreemptivePriorityResidualWork
      (enqueueNonpreemptivePriorityJob state job) =
      totalNonpreemptivePriorityResidualWork state + job.serviceWork := by
  classical
  have hactive :
      activeNonpreemptivePriorityResidualWork
        (enqueueNonpreemptivePriorityJob state job) =
        activeNonpreemptivePriorityResidualWork state := by
    unfold activeNonpreemptivePriorityResidualWork
    simp [enqueueNonpreemptivePriorityJob]
  have hwaiting :
      (fun i => priorityWaitingResidualWork
          (enqueueNonpreemptivePriorityJob state job) i) =
        Function.update (fun i => priorityWaitingResidualWork state i) job.priority
          (priorityWaitingResidualWork state job.priority + job.serviceWork) := by
    funext i
    by_cases hi : i = job.priority
    · subst i
      simp [priorityWaitingResidualWork_enqueue_selected]
    · simp [Function.update_of_ne hi,
        priorityWaitingResidualWork_enqueue_of_ne state job i hi]
  unfold totalNonpreemptivePriorityResidualWork
  rw [hactive, hwaiting, Finset.sum_update_of_mem (Finset.mem_univ job.priority)]
  rw [← Finset.sum_erase_add _ (fun i => priorityWaitingResidualWork state i)
    (Finset.mem_univ job.priority)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- Tail admission adds the square of the admitted requirement to its selected
class's squared residual ledger. -/
theorem priorityWaitingSquaredResidualWork_enqueue_selected
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (((enqueueNonpreemptivePriorityJob state job).waiting job.priority).map
        (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum =
      ((state.waiting job.priority).map
        (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum +
        job.serviceWork ^ 2 := by
  rw [enqueueNonpreemptivePriorityJob_waiting_selected]
  simp

/-- Tail admission leaves the squared residual ledger of every other class
unchanged. -/
theorem priorityWaitingSquaredResidualWork_enqueue_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hi : i ≠ job.priority) :
    (((enqueueNonpreemptivePriorityJob state job).waiting i).map
        (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum =
      ((state.waiting i).map
        (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum := by
  rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state job i hi]

/-- Appending one waiting job raises the squared-residual ledger by precisely
the square of its declared requirement. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    totalNonpreemptivePrioritySquaredResidualWork
      (enqueueNonpreemptivePriorityJob state job) =
      totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
  classical
  have hactive :
      activeNonpreemptivePriorityResidualWork
        (enqueueNonpreemptivePriorityJob state job) =
        activeNonpreemptivePriorityResidualWork state := by
    unfold activeNonpreemptivePriorityResidualWork
    simp [enqueueNonpreemptivePriorityJob]
  have hwaiting :
      (fun i => ((enqueueNonpreemptivePriorityJob state job).waiting i).map
        (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2) |>.sum) =
        Function.update (fun i => ((state.waiting i).map
          (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum)
          job.priority
          (((state.waiting job.priority).map
            (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum +
            job.serviceWork ^ 2) := by
    funext i
    by_cases hi : i = job.priority
    · subst i
      simp [priorityWaitingSquaredResidualWork_enqueue_selected]
    · simp [Function.update_of_ne hi,
        priorityWaitingSquaredResidualWork_enqueue_of_ne state job i hi]
  unfold totalNonpreemptivePrioritySquaredResidualWork
  rw [hactive, hwaiting, Finset.sum_update_of_mem (Finset.mem_univ job.priority)]
  rw [← Finset.sum_erase_add _ (fun i => ((state.waiting i).map
    (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum)
    (Finset.mem_univ job.priority)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- Starting a waiting job changes its location but preserves total unfinished
work. -/
theorem totalNonpreemptivePriorityResidualWork_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityResidualWork
      (startNextNonpreemptivePriorityJob state) =
      totalNonpreemptivePriorityResidualWork state := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
        | cons head tail =>
            have hactiveWork :
                activeNonpreemptivePriorityResidualWork
                  (startNextNonpreemptivePriorityJob state) = head.serviceWork := by
              simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                activeNonpreemptivePriorityResidualWork]
            have hwaitingWork :
                (fun i => priorityWaitingResidualWork
                    (startNextNonpreemptivePriorityJob state) i) =
                  Function.update (fun i => priorityWaitingResidualWork state i) selected
                    ((tail.map fun job => job.serviceWork).sum) := by
              funext i
              by_cases hi : i = selected
              · subst i
                simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                  priorityWaitingResidualWork]
              · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                  Function.update_of_ne hi, priorityWaitingResidualWork]
            have hselectedWork :
                priorityWaitingResidualWork state selected =
                  head.serviceWork + (tail.map fun job => job.serviceWork).sum := by
              simp [priorityWaitingResidualWork, hhead]
            have hstateActive : activeNonpreemptivePriorityResidualWork state = 0 := by
              simp [activeNonpreemptivePriorityResidualWork, hactive]
            unfold totalNonpreemptivePriorityResidualWork
            rw [hactiveWork, hwaitingWork,
              Finset.sum_update_of_mem (Finset.mem_univ selected)]
            rw [← Finset.sum_erase_add _ (fun i => priorityWaitingResidualWork state i)
              (Finset.mem_univ selected)]
            rw [Finset.sdiff_singleton_eq_erase, hselectedWork, hstateActive]
            ring
      · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Dispatching the next waiting job only moves its residual requirement from
the FIFO ledger to the active coordinate, so the squared-residual ledger is
unchanged. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePrioritySquaredResidualWork
      (startNextNonpreemptivePriorityJob state) =
      totalNonpreemptivePrioritySquaredResidualWork state := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
        | cons head tail =>
            have hactiveWork :
                activeNonpreemptivePriorityResidualWork
                  (startNextNonpreemptivePriorityJob state) = head.serviceWork := by
              simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                activeNonpreemptivePriorityResidualWork]
            have hwaitingWork :
                (fun i => (((startNextNonpreemptivePriorityJob state).waiting i).map
                    (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) =
                  Function.update
                    (fun i => ((state.waiting i).map
                      (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum)
                    selected ((tail.map
                      (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) := by
              funext i
              by_cases hi : i = selected
              · subst i
                simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
              · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                  Function.update_of_ne hi]
            have hselectedWork :
                ((state.waiting selected).map
                  (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum =
                  head.serviceWork ^ 2 + (tail.map
                    (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum := by
              rw [hhead]
              simp
            have hstateActive : activeNonpreemptivePriorityResidualWork state = 0 := by
              simp [activeNonpreemptivePriorityResidualWork, hactive]
            unfold totalNonpreemptivePrioritySquaredResidualWork
            rw [hactiveWork, hwaitingWork,
              Finset.sum_update_of_mem (Finset.mem_univ selected)]
            rw [← Finset.sum_erase_add _
              (fun i => ((state.waiting i).map
                (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum)
              (Finset.mem_univ selected)]
            rw [Finset.sdiff_singleton_eq_erase, hselectedWork, hstateActive]
            ring
      · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Every admission raises total unfinished work by its declared service
requirement, whether it enters service immediately or joins a FIFO list. -/
theorem totalNonpreemptivePriorityResidualWork_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    totalNonpreemptivePriorityResidualWork
      (admitNonpreemptivePriorityJob state job) =
      totalNonpreemptivePriorityResidualWork state + job.serviceWork := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared :
      totalNonpreemptivePriorityResidualWork prepared =
        totalNonpreemptivePriorityResidualWork state := by
    simpa [prepared] using totalNonpreemptivePriorityResidualWork_startNext state
  cases hactive : prepared.active with
  | none =>
      have hnew :
          totalNonpreemptivePriorityResidualWork
            { prepared with active := some (job, job.serviceWork) } =
            totalNonpreemptivePriorityResidualWork prepared + job.serviceWork := by
        have hwaiting :
            (∑ i, priorityWaitingResidualWork
              { prepared with active := some (job, job.serviceWork) } i) =
              ∑ i, priorityWaitingResidualWork prepared i := by
          rfl
        unfold totalNonpreemptivePriorityResidualWork
          activeNonpreemptivePriorityResidualWork
        rw [hwaiting]
        simp [hactive]
        ring
      calc
        totalNonpreemptivePriorityResidualWork
            (admitNonpreemptivePriorityJob state job) =
            totalNonpreemptivePriorityResidualWork prepared + job.serviceWork := by
              simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hnew
        _ = totalNonpreemptivePriorityResidualWork state + job.serviceWork := by
              rw [hprepared]
  | some active =>
      calc
        totalNonpreemptivePriorityResidualWork
            (admitNonpreemptivePriorityJob state job) =
            totalNonpreemptivePriorityResidualWork prepared + job.serviceWork := by
              simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
                totalNonpreemptivePriorityResidualWork_enqueue prepared job
        _ = totalNonpreemptivePriorityResidualWork state + job.serviceWork := by
              rw [hprepared]

/-- Every admission raises the squared-residual ledger by the square of the
declared service requirement, regardless of whether service begins
immediately or the job joins a FIFO list. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    totalNonpreemptivePrioritySquaredResidualWork
      (admitNonpreemptivePriorityJob state job) =
      totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared :
      totalNonpreemptivePrioritySquaredResidualWork prepared =
        totalNonpreemptivePrioritySquaredResidualWork state := by
    simpa [prepared] using totalNonpreemptivePrioritySquaredResidualWork_startNext state
  cases hactive : prepared.active with
  | none =>
      have hnew :
          totalNonpreemptivePrioritySquaredResidualWork
            { prepared with active := some (job, job.serviceWork) } =
              totalNonpreemptivePrioritySquaredResidualWork prepared + job.serviceWork ^ 2 := by
        have hwaiting :
            (∑ i, (({ prepared with active := some (job, job.serviceWork) }.waiting i).map
              (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum) =
              ∑ i, ((prepared.waiting i).map
                (fun (other : NonpreemptivePriorityJob n JobId) => other.serviceWork ^ 2)).sum := by
          rfl
        unfold totalNonpreemptivePrioritySquaredResidualWork
          activeNonpreemptivePriorityResidualWork
        rw [hwaiting]
        simp [hactive]
        ring
      calc
        totalNonpreemptivePrioritySquaredResidualWork
            (admitNonpreemptivePriorityJob state job) =
            totalNonpreemptivePrioritySquaredResidualWork prepared + job.serviceWork ^ 2 := by
              simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hnew
        _ = totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
              rw [hprepared]
  | some active =>
      calc
        totalNonpreemptivePrioritySquaredResidualWork
            (admitNonpreemptivePriorityJob state job) =
            totalNonpreemptivePrioritySquaredResidualWork prepared + job.serviceWork ^ 2 := by
              simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
                totalNonpreemptivePrioritySquaredResidualWork_enqueue prepared job
        _ = totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
              rw [hprepared]

/-- Completing an active job removes exactly its currently stored residual
work; selecting the next waiting job is workload-preserving. -/
theorem totalNonpreemptivePriorityResidualWork_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active) :
    totalNonpreemptivePriorityResidualWork
      (completeNonpreemptivePriorityWorkJob state) =
      totalNonpreemptivePriorityResidualWork state - active.2 := by
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
  have hstart :
      totalNonpreemptivePriorityResidualWork
        (startNextNonpreemptivePriorityJob afterCompletion) =
        totalNonpreemptivePriorityResidualWork afterCompletion :=
    totalNonpreemptivePriorityResidualWork_startNext afterCompletion
  have hafter :
      totalNonpreemptivePriorityResidualWork afterCompletion =
        totalNonpreemptivePriorityResidualWork state - active.2 := by
    have hwaiting :
        (∑ i, priorityWaitingResidualWork afterCompletion i) =
          ∑ i, priorityWaitingResidualWork state i := by
      rfl
    unfold totalNonpreemptivePriorityResidualWork
      activeNonpreemptivePriorityResidualWork
    rw [hwaiting]
    simp [afterCompletion, hactive]
  calc
    totalNonpreemptivePriorityResidualWork
        (completeNonpreemptivePriorityWorkJob state) =
        totalNonpreemptivePriorityResidualWork afterCompletion := by
          simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hstart
    _ = totalNonpreemptivePriorityResidualWork state - active.2 := hafter

/-- Completing an active job removes its squared residual requirement from the
squared-residual ledger; dispatching a replacement leaves that ledger
unchanged. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active) :
    totalNonpreemptivePrioritySquaredResidualWork
      (completeNonpreemptivePriorityWorkJob state) =
      totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
  have hstart :
      totalNonpreemptivePrioritySquaredResidualWork
        (startNextNonpreemptivePriorityJob afterCompletion) =
        totalNonpreemptivePrioritySquaredResidualWork afterCompletion :=
    totalNonpreemptivePrioritySquaredResidualWork_startNext afterCompletion
  have hafter :
      totalNonpreemptivePrioritySquaredResidualWork afterCompletion =
        totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
    have hwaiting :
        (∑ i, ((afterCompletion.waiting i).map
          (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) =
          ∑ i, ((state.waiting i).map
            (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum := by
      rfl
    unfold totalNonpreemptivePrioritySquaredResidualWork
    rw [hwaiting]
    unfold activeNonpreemptivePriorityResidualWork
    simp [afterCompletion, hactive]
  calc
    totalNonpreemptivePrioritySquaredResidualWork
        (completeNonpreemptivePriorityWorkJob state) =
        totalNonpreemptivePrioritySquaredResidualWork afterCompletion := by
          simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hstart
    _ = totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := hafter

/-- In the partial-service branch, the concrete residual-work ledger falls
by exactly the elapsed physical time. -/
theorem totalNonpreemptivePriorityResidualWork_advance_partial
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (htarget : ¬ target ≤ state.currentTime)
    (hactive : state.active = some active)
    (hcomplete : ¬ active.2 ≤ target - state.currentTime) :
    totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
      totalNonpreemptivePriorityResidualWork state -
        (target - state.currentTime) := by
  let partialState : NonpreemptivePriorityWorkState n JobId :=
    { state with
      currentTime := target
      active := some (active.1, active.2 - (target - state.currentTime)) }
  have hwaiting :
      (∑ i, priorityWaitingResidualWork partialState i) =
        ∑ i, priorityWaitingResidualWork state i := by
    rfl
  calc
    totalNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
        totalNonpreemptivePriorityResidualWork partialState := by
          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete, partialState]
    _ = (active.2 - (target - state.currentTime)) +
          ∑ i, priorityWaitingResidualWork state i := by
          unfold totalNonpreemptivePriorityResidualWork
            activeNonpreemptivePriorityResidualWork
          rw [hwaiting]
    _ = totalNonpreemptivePriorityResidualWork state -
          (target - state.currentTime) := by
          unfold totalNonpreemptivePriorityResidualWork
            activeNonpreemptivePriorityResidualWork
          simp [hactive]
          ring

/-- In the same partial-service branch, the active residual itself is the
original residual minus elapsed service.  This component form is used when
integrating residual work over a finite service trace. -/
theorem activeNonpreemptivePriorityResidualWork_advance_partial
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (htarget : ¬ target ≤ state.currentTime)
    (hactive : state.active = some active)
    (hcomplete : ¬ active.2 ≤ target - state.currentTime) :
    activeNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
      active.2 - (target - state.currentTime) := by
  simp [activeNonpreemptivePriorityResidualWork,
    advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]

/-- A nonnegative finite state has nonnegative total unfinished work. -/
theorem totalNonpreemptivePriorityResidualWork_nonneg
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    0 ≤ totalNonpreemptivePriorityResidualWork state := by
  unfold totalNonpreemptivePriorityResidualWork
  apply add_nonneg
  · unfold activeNonpreemptivePriorityResidualWork
    cases hactive : state.active with
    | none => simp
    | some active =>
        simp only
        exact hwork.1 active hactive
  · apply Finset.sum_nonneg
    intro i _
    exact priorityWaitingResidualWork_nonneg state hwork i

/-- Moving a waiting head into service preserves nonnegative stored residual
work. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    nonnegativeNonpreemptivePriorityResidualWork
      (startNextNonpreemptivePriorityJob state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hwork
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
              using hwork
        | cons head tail =>
            constructor
            · intro active houtput
              simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                selected, hhead] at houtput
              injection houtput with heq
              subst active
              exact hwork.2 selected head (by rw [hhead]; simp)
            · intro i other hmember
              by_cases hi : i = selected
              · subst i
                simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                  selected, hhead, Function.update_self] at hmember
                exact hwork.2 selected other (by
                  rw [hhead]
                  exact List.mem_cons_of_mem _ hmember)
              · simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                  selected, hhead, Function.update_of_ne hi] at hmember
                exact hwork.2 i other hmember
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hwork

/-- Appending a nonnegative-work arrival preserves nonnegative stored
residual work. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (hjob : 0 ≤ job.serviceWork) :
    nonnegativeNonpreemptivePriorityResidualWork
      (enqueueNonpreemptivePriorityJob state job) := by
  constructor
  · intro active hactive
    simpa [enqueueNonpreemptivePriorityJob] using hwork.1 active hactive
  · intro i other hmember
    by_cases hi : i = job.priority
    · subst i
      rw [enqueueNonpreemptivePriorityJob_waiting_selected] at hmember
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmember
      rcases hmember with hmember | hmember
      · exact hwork.2 job.priority other hmember
      · subst other
        exact hjob
    · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state job i hi] at hmember
      exact hwork.2 i other hmember

/-- Service completion removes an active residual and then starts a waiting
head without introducing negative stored work. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    nonnegativeNonpreemptivePriorityResidualWork
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hwork
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : nonnegativeNonpreemptivePriorityResidualWork afterCompletion := by
        constructor
        · intro other hother
          simp [afterCompletion] at hother
        · intro i job hmember
          simpa [afterCompletion] using hwork.2 i job hmember
      have hnext := nonnegativeNonpreemptivePriorityResidualWork_startNext
        afterCompletion hafter
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hnext

/-- Admitting a nonnegative-work customer preserves nonnegative stored work. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (hjob : 0 ≤ job.serviceWork) :
    nonnegativeNonpreemptivePriorityResidualWork
      (admitNonpreemptivePriorityJob state job) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonnegativeNonpreemptivePriorityResidualWork prepared := by
    simpa [prepared] using
      nonnegativeNonpreemptivePriorityResidualWork_startNext state hwork
  cases hactive : prepared.active with
  | none =>
      constructor
      · intro active houtput
        simp only [admitNonpreemptivePriorityJob, prepared, hactive] at houtput
        injection houtput with heq
        subst active
        exact hjob
      · intro i other hmember
        have hwaiting :
            (admitNonpreemptivePriorityJob state job).waiting = prepared.waiting := by
          simp [admitNonpreemptivePriorityJob, prepared, hactive]
        rw [hwaiting] at hmember
        exact hprepared.2 i other hmember
  | some active =>
      have henqueued := nonnegativeNonpreemptivePriorityResidualWork_enqueue
        prepared job hprepared hjob
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using henqueued

/-- Bounded service evolution preserves nonnegative residual work.  In the
partial-service branch the strict comparison defining that branch guarantees
that the new active residual is still positive. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    nonnegativeNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            constructor
            · intro active houtput
              simp [advanceNonpreemptivePriorityWorkState, htarget, hactive] at houtput
            · intro i job hmember
              exact hwork.2 i job (by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hmember)
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hwork
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            constructor
            · intro active houtput
              simp [advanceNonpreemptivePriorityWorkState, htarget, hactive] at houtput
            · intro i job hmember
              have hwaiting :
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).waiting =
                    state.waiting := by
                simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
              rw [hwaiting] at hmember
              exact hwork.2 i job hmember
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAt : nonnegativeNonpreemptivePriorityResidualWork completedAt := by
                constructor
                · intro other hother
                  simpa [completedAt] using hwork.1 other hother
                · intro i job hmember
                  simpa [completedAt] using hwork.2 i job hmember
              have hstep := nonnegativeNonpreemptivePriorityResidualWork_complete
                completedAt hcompletedAt
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt) hstep
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedAt] using hind
            · constructor
              · intro other hother
                simp only [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] at hother
                injection hother with heq
                subst other
                exact (sub_pos.mpr (lt_of_not_ge hcomplete)).le
              · intro i job hmember
                have hwaiting :
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).waiting =
                      state.waiting := by
                  simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                rw [hwaiting] at hmember
                exact hwork.2 i job hmember

/-- Executing a finite arrival trace preserves nonnegative stored work when
every presented job has nonnegative service requirement. -/
theorem nonnegativeNonpreemptivePriorityResidualWork_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hinitial : nonnegativeNonpreemptivePriorityResidualWork initial)
    (hjobs : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonnegativeNonpreemptivePriorityResidualWork
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hinitial
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using
          nonnegativeNonpreemptivePriorityResidualWork_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hinitial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using
          nonnegativeNonpreemptivePriorityResidualWork_admit advanced job hadvanced
            (hjobs job (by simp))
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted (fun other hother => hjobs other (by simp [hother]))

/-- Starting the next job preserves strict positivity of all stored residual
work. -/
theorem positiveNonpreemptivePriorityResidualWork_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state) :
    positiveNonpreemptivePriorityResidualWork
      (startNextNonpreemptivePriorityJob state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hwork
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
              using hwork
        | cons head tail =>
            constructor
            · intro active houtput
              simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                selected, hhead] at houtput
              injection houtput with heq
              subst active
              exact hwork.2 selected head (by rw [hhead]; simp)
            · intro i other hmember
              by_cases hi : i = selected
              · subst i
                simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                  selected, hhead, Function.update_self] at hmember
                exact hwork.2 selected other (by
                  rw [hhead]
                  exact List.mem_cons_of_mem _ hmember)
              · simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                  selected, hhead, Function.update_of_ne hi] at hmember
                exact hwork.2 i other hmember
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hwork

/-- Appending a strictly positive-work job preserves strict positivity of all
stored residual work. -/
theorem positiveNonpreemptivePriorityResidualWork_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state)
    (hjob : 0 < job.serviceWork) :
    positiveNonpreemptivePriorityResidualWork
      (enqueueNonpreemptivePriorityJob state job) := by
  constructor
  · intro active hactive
    simpa [enqueueNonpreemptivePriorityJob] using hwork.1 active hactive
  · intro i other hmember
    by_cases hi : i = job.priority
    · subst i
      rw [enqueueNonpreemptivePriorityJob_waiting_selected] at hmember
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmember
      rcases hmember with hmember | hmember
      · exact hwork.2 job.priority other hmember
      · subst other
        exact hjob
    · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state job i hi] at hmember
      exact hwork.2 i other hmember

/-- Completion and reselection preserve strict positivity of the remaining
stored residual work. -/
theorem positiveNonpreemptivePriorityResidualWork_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state) :
    positiveNonpreemptivePriorityResidualWork
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hwork
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : positiveNonpreemptivePriorityResidualWork afterCompletion := by
        constructor
        · intro other hother
          simp [afterCompletion] at hother
        · intro i job hmember
          simpa [afterCompletion] using hwork.2 i job hmember
      have hnext := positiveNonpreemptivePriorityResidualWork_startNext
        afterCompletion hafter
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hnext

/-- Admitting a strictly positive-work customer preserves strict residual
positivity. -/
theorem positiveNonpreemptivePriorityResidualWork_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state)
    (hjob : 0 < job.serviceWork) :
    positiveNonpreemptivePriorityResidualWork
      (admitNonpreemptivePriorityJob state job) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : positiveNonpreemptivePriorityResidualWork prepared := by
    simpa [prepared] using
      positiveNonpreemptivePriorityResidualWork_startNext state hwork
  cases hactive : prepared.active with
  | none =>
      constructor
      · intro active houtput
        simp only [admitNonpreemptivePriorityJob, prepared, hactive] at houtput
        injection houtput with heq
        subst active
        exact hjob
      · intro i other hmember
        have hwaiting :
            (admitNonpreemptivePriorityJob state job).waiting = prepared.waiting := by
          simp [admitNonpreemptivePriorityJob, prepared, hactive]
        rw [hwaiting] at hmember
        exact hprepared.2 i other hmember
  | some active =>
      have henqueued := positiveNonpreemptivePriorityResidualWork_enqueue
        prepared job hprepared hjob
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using henqueued

/-- Bounded service evolution preserves strict positivity of all residual jobs
that remain in the state. -/
theorem positiveNonpreemptivePriorityResidualWork_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state) :
    positiveNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            constructor
            · intro active houtput
              simp [advanceNonpreemptivePriorityWorkState, htarget, hactive] at houtput
            · intro i job hmember
              exact hwork.2 i job (by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hmember)
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hwork
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            constructor
            · intro active houtput
              simp [advanceNonpreemptivePriorityWorkState, htarget, hactive] at houtput
            · intro i job hmember
              have hwaiting :
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).waiting =
                    state.waiting := by
                simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
              rw [hwaiting] at hmember
              exact hwork.2 i job hmember
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAt : positiveNonpreemptivePriorityResidualWork completedAt := by
                constructor
                · intro other hother
                  simpa [completedAt] using hwork.1 other hother
                · intro i job hmember
                  simpa [completedAt] using hwork.2 i job hmember
              have hstep := positiveNonpreemptivePriorityResidualWork_complete
                completedAt hcompletedAt
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt) hstep
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedAt] using hind
            · constructor
              · intro other hother
                simp only [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] at hother
                injection hother with heq
                subst other
                exact sub_pos.mpr (lt_of_not_ge hcomplete)
              · intro i job hmember
                have hwaiting :
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).waiting =
                      state.waiting := by
                  simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                rw [hwaiting] at hmember
                exact hwork.2 i job hmember

/-- A finite trace of strictly positive-work arrivals keeps every unfinished
residual strictly positive. -/
theorem positiveNonpreemptivePriorityResidualWork_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hinitial : positiveNonpreemptivePriorityResidualWork initial)
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    positiveNonpreemptivePriorityResidualWork
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hinitial
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : positiveNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using
          positiveNonpreemptivePriorityResidualWork_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hinitial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : positiveNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using
          positiveNonpreemptivePriorityResidualWork_admit advanced job hadvanced
            (hjobs job (by simp))
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted (fun other hother => hjobs other (by simp [hother]))

/-- In the partial-service branch, the squared-residual ledger changes only
in the active coordinate.  The displayed difference is the elementary
square-law corresponding to the residual work supplied over the elapsed
physical interval. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_advance_partial
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (htarget : ¬ target ≤ state.currentTime)
    (hactive : state.active = some active)
    (hcomplete : ¬ active.2 ≤ target - state.currentTime) :
    totalNonpreemptivePrioritySquaredResidualWork
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
      totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 +
        (active.2 - (target - state.currentTime)) ^ 2 := by
  let partialState : NonpreemptivePriorityWorkState n JobId :=
    { state with
      currentTime := target
      active := some (active.1, active.2 - (target - state.currentTime)) }
  have hwaiting :
      (∑ i, ((partialState.waiting i).map
        (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) =
        ∑ i, ((state.waiting i).map
          (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum := by
    rfl
  calc
    totalNonpreemptivePrioritySquaredResidualWork
        (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
        totalNonpreemptivePrioritySquaredResidualWork partialState := by
          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
            hcomplete, partialState]
    _ = totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 +
          (active.2 - (target - state.currentTime)) ^ 2 := by
            unfold totalNonpreemptivePrioritySquaredResidualWork
              activeNonpreemptivePriorityResidualWork
            rw [hwaiting]
            simp [partialState, hactive]
            ring

end Queueing
end AppliedModelingLib
