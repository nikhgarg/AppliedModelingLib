import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# Deterministic reflected workload

This module contains only the scalar deterministic part of Lindley's
recursion.  In particular, it makes no assertion about a stochastic input,
stationarity, or a queueing discipline.  A future construction may instantiate
`increment` with finite-trace net work and use a negative-prefix certificate to
obtain a reset of an empty-start trajectory.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

/-- The empty-start scalar reflected-workload recursion. -/
def lindleyWorkload (increment : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => max 0 (lindleyWorkload increment n + increment n)

/-- The scalar reflected-workload recursion with an explicit initial state. -/
def lindleyWorkloadFrom (initial : Real) (increment : Nat -> Real) : Nat -> Real
  | 0 => initial
  | n + 1 => max 0 (lindleyWorkloadFrom initial increment n + increment n)

/--
One service-before-arrival update.  `postWork` is the work just after the
current external batch, `service` is the work-conserving capacity available
before the next external batch, and `batch` is that next batch.  The value is
the work just after the next batch.
-/
def lateBatchUpdate (postWork service batch : Real) : Real :=
  max (postWork - service) 0 + batch

/--
Post-batch workload for a service-before-arrival scalar queue.  Batch `n` is
applied at epoch `n`; service `n` is accrued after that batch and before batch
`n + 1`.
-/
def lateBatchPostWorkload (batch service : Nat -> Real) : Nat -> Real
  | 0 => batch 0
  | n + 1 =>
      lateBatchUpdate (lateBatchPostWorkload batch service n) (service n) (batch (n + 1))

/--
Workload immediately before an external batch in the service-before-arrival
recursion.  At a pre-batch reset this value is zero even when the batch itself
is nonzero, so it is the appropriate coalescence state.
-/
def lateBatchPreWorkload (batch service : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => max (lateBatchPostWorkload batch service n - service n) 0

/--
Service-before-arrival scalar workload with an explicit pre-batch initial
state.  This is the convention needed to compare two finite event traces
started at different remote-past epochs: `initial` is the work immediately
before batch zero, not the post-batch work.
-/
def lateBatchPostWorkloadFrom
    (initial : Real) (batch service : Nat -> Real) : Nat -> Real
  | 0 => initial + batch 0
  | n + 1 =>
      lateBatchUpdate
        (lateBatchPostWorkloadFrom initial batch service n)
        (service n) (batch (n + 1))

/-- The corresponding explicit-initial-state workload immediately before each batch. -/
def lateBatchPreWorkloadFrom
    (initial : Real) (batch service : Nat -> Real) : Nat -> Real
  | 0 => initial
  | n + 1 => max (lateBatchPostWorkloadFrom initial batch service n - service n) 0

/-- The post-batch state is the corresponding pre-batch state plus that batch. -/
theorem lateBatchPostWorkload_eq_pre_add_batch
    (batch service : Nat -> Real) (n : Nat) :
    lateBatchPostWorkload batch service n = lateBatchPreWorkload batch service n + batch n := by
  cases n with
  | zero => simp [lateBatchPostWorkload, lateBatchPreWorkload]
  | succ n => rfl

/-- The explicit-initial-state post-batch workload is its pre-batch work plus that batch. -/
theorem lateBatchPostWorkloadFrom_eq_pre_add_batch
    (initial : Real) (batch service : Nat -> Real) (n : Nat) :
    lateBatchPostWorkloadFrom initial batch service n =
      lateBatchPreWorkloadFrom initial batch service n + batch n := by
  cases n with
  | zero => simp [lateBatchPostWorkloadFrom, lateBatchPreWorkloadFrom]
  | succ n => rfl

/-- The pre-batch state obeys the displayed service-before-arrival recursion. -/
theorem lateBatchPreWorkload_succ
    (batch service : Nat -> Real) (n : Nat) :
    lateBatchPreWorkload batch service (n + 1) =
      max (lateBatchPostWorkload batch service n - service n) 0 := by
  rfl

/-- The post-batch state obeys one explicit late-batch update. -/
theorem lateBatchPostWorkload_succ
    (batch service : Nat -> Real) (n : Nat) :
    lateBatchPostWorkload batch service (n + 1) =
      lateBatchUpdate (lateBatchPostWorkload batch service n) (service n) (batch (n + 1)) := by
  rfl

/--
At pre-batch epochs, the late-batch model is exactly the usual reflected
recursion on net increments `batch n - service n`.  This equality does not
identify the post-batch state with a Lindley state.
-/
theorem lateBatchPreWorkload_eq_lindleyWorkload
    (batch service : Nat -> Real) :
    lateBatchPreWorkload batch service =
      lindleyWorkload (fun n => batch n - service n) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        lateBatchPreWorkload batch service (n + 1) =
            max (lateBatchPostWorkload batch service n - service n) 0 := rfl
        _ = max (lateBatchPreWorkload batch service n + batch n - service n) 0 := by
              rw [lateBatchPostWorkload_eq_pre_add_batch]
        _ = max 0 (lateBatchPreWorkload batch service n + (batch n - service n)) := by
              rw [max_comm]
              congr 1
              ring
        _ = max 0 (lindleyWorkload (fun j => batch j - service j) n +
              (batch n - service n)) := by rw [ih]
        _ = lindleyWorkload (fun j => batch j - service j) (n + 1) := by rfl

/--
At pre-batch epochs, the explicit-initial-state late-batch recursion is the
usual reflected recursion from that same initial workload.  This preserves the
GPS runner's service-before-arrival semantics while exposing the scalar state
needed for remote-past coalescence.
-/
theorem lateBatchPreWorkloadFrom_eq_lindleyWorkloadFrom
    (initial : Real) (batch service : Nat -> Real) :
    lateBatchPreWorkloadFrom initial batch service =
      lindleyWorkloadFrom initial (fun n => batch n - service n) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        lateBatchPreWorkloadFrom initial batch service (n + 1) =
            max (lateBatchPostWorkloadFrom initial batch service n - service n) 0 := rfl
        _ = max (lateBatchPreWorkloadFrom initial batch service n + batch n - service n) 0 := by
              rw [lateBatchPostWorkloadFrom_eq_pre_add_batch]
        _ = max 0 (lateBatchPreWorkloadFrom initial batch service n +
              (batch n - service n)) := by
              rw [max_comm]
              congr 1
              ring
        _ = max 0 (lindleyWorkloadFrom initial (fun j => batch j - service j) n +
              (batch n - service n)) := by rw [ih]
        _ = lindleyWorkloadFrom initial (fun j => batch j - service j) (n + 1) := by
              rfl

/-- Every pre-batch late-batch workload is nonnegative. -/
theorem lateBatchPreWorkload_nonneg
    (batch service : Nat -> Real) (n : Nat) :
    0 <= lateBatchPreWorkload batch service n := by
  cases n with
  | zero => simp [lateBatchPreWorkload]
  | succ n =>
      change 0 <= max (lateBatchPostWorkload batch service n - service n) 0
      exact le_max_right _ _

/-- Empty-start and zero-initial-state recursions agree. -/
theorem lindleyWorkload_eq_from_zero (increment : Nat -> Real) :
    lindleyWorkload increment = lindleyWorkloadFrom 0 increment := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [lindleyWorkload, lindleyWorkloadFrom, ih]

/-- Every empty-start reflected workload is nonnegative. -/
theorem lindleyWorkload_nonneg (increment : Nat -> Real) (n : Nat) :
    0 <= lindleyWorkload increment n := by
  cases n with
  | zero => simp [lindleyWorkload]
  | succ n =>
      exact le_max_left _ _

/-- A nonnegative initial state remains nonnegative under the recursion. -/
theorem lindleyWorkloadFrom_nonneg
    {initial : Real} {increment : Nat -> Real} (hinitial : 0 <= initial) :
    forall n, 0 <= lindleyWorkloadFrom initial increment n := by
  intro n
  induction n with
  | zero => simpa [lindleyWorkloadFrom]
  | succ n ih => exact le_max_left _ _

/--
If an empty-start trajectory has no reset through time `N`, reflection never
binds, so its workload is the ordinary cumulative increment.
-/
theorem lindleyWorkload_eq_sum_range_of_no_reset
    (increment : Nat -> Real) (N : Nat)
    (hnoreset : forall m, 0 < m -> m <= N -> lindleyWorkload increment m ≠ 0) :
    lindleyWorkload increment N = Finset.sum (Finset.range N) increment := by
  induction N with
  | zero => simp [lindleyWorkload]
  | succ N ih =>
      have hprior : forall m, 0 < m -> m <= N -> lindleyWorkload increment m ≠ 0 := by
        intro m hm_pos hm_le
        exact hnoreset m hm_pos (le_trans hm_le (Nat.le_succ N))
      have hsum : lindleyWorkload increment N = Finset.sum (Finset.range N) increment :=
        ih hprior
      have hnext_ne : lindleyWorkload increment (N + 1) ≠ 0 :=
        hnoreset (N + 1) (Nat.succ_pos N) (Nat.le_refl _)
      have hinner_nonneg : 0 <= Finset.sum (Finset.range N) increment + increment N := by
        by_contra h
        have hinner_neg : Finset.sum (Finset.range N) increment + increment N < 0 :=
          lt_of_not_ge h
        apply hnext_ne
        calc
          lindleyWorkload increment (N + 1) =
              max 0 (lindleyWorkload increment N + increment N) := by
                rfl
          _ = max 0 (Finset.sum (Finset.range N) increment + increment N) := by rw [hsum]
          _ = 0 := max_eq_left (le_of_lt hinner_neg)
      calc
        lindleyWorkload increment (N + 1) =
            max 0 (lindleyWorkload increment N + increment N) := by
              rfl
        _ = max 0 (Finset.sum (Finset.range N) increment + increment N) := by rw [hsum]
        _ = Finset.sum (Finset.range N) increment + increment N :=
          max_eq_right hinner_nonneg
        _ = Finset.sum (Finset.range (N + 1)) increment := by
          symm
          exact Finset.sum_range_succ increment N

/--
A finite negative cumulative increment forces an empty time strictly after the
empty start.  This is the finite reset certificate consumed by a future
negative-drift argument.
-/
theorem exists_lindley_reset_of_sum_range_neg
    {increment : Nat -> Real} {N : Nat}
    (hneg : Finset.sum (Finset.range N) increment < 0) :
    exists m, 0 < m /\ m <= N /\ lindleyWorkload increment m = 0 := by
  by_contra h
  have hnoreset : forall m, 0 < m -> m <= N -> lindleyWorkload increment m ≠ 0 := by
    intro m hm_pos hm_le hzero
    apply h
    exact ⟨m, hm_pos, hm_le, hzero⟩
  have hsum := lindleyWorkload_eq_sum_range_of_no_reset increment N hnoreset
  rw [<- hsum] at hneg
  exact (not_lt_of_ge (lindleyWorkload_nonneg increment N)) hneg

/--
If a reflected trajectory beginning from a finite initial workload has no
reset through time `N`, reflection never binds and the state is its initial
workload plus the cumulative net increment.  This is the version needed when
comparing finite runs begun at different remote-past times.
-/
theorem lindleyWorkloadFrom_eq_initial_add_sum_range_of_no_reset
    (initial : Real) (increment : Nat -> Real) (N : Nat)
    (hnoreset : forall m, 0 < m -> m <= N ->
      lindleyWorkloadFrom initial increment m ≠ 0) :
    lindleyWorkloadFrom initial increment N =
      initial + Finset.sum (Finset.range N) increment := by
  induction N with
  | zero =>
      simp [lindleyWorkloadFrom]
  | succ N ih =>
      have hprior : forall m, 0 < m -> m <= N ->
          lindleyWorkloadFrom initial increment m ≠ 0 := by
        intro m hm_pos hm_le
        exact hnoreset m hm_pos (le_trans hm_le (Nat.le_succ N))
      have hsum : lindleyWorkloadFrom initial increment N =
          initial + Finset.sum (Finset.range N) increment :=
        ih hprior
      have hnext_ne : lindleyWorkloadFrom initial increment (N + 1) ≠ 0 :=
        hnoreset (N + 1) (Nat.succ_pos N) (Nat.le_refl _)
      have hinner_nonneg : 0 <=
          initial + Finset.sum (Finset.range N) increment + increment N := by
        by_contra h
        have hinner_neg :
            initial + Finset.sum (Finset.range N) increment + increment N < 0 :=
          lt_of_not_ge h
        apply hnext_ne
        calc
          lindleyWorkloadFrom initial increment (N + 1) =
              max 0 (lindleyWorkloadFrom initial increment N + increment N) := by
                rfl
          _ = max 0
              (initial + Finset.sum (Finset.range N) increment + increment N) := by
                rw [hsum]
          _ = 0 := max_eq_left (le_of_lt hinner_neg)
      calc
        lindleyWorkloadFrom initial increment (N + 1) =
            max 0 (lindleyWorkloadFrom initial increment N + increment N) := by
              rfl
        _ = max 0
            (initial + Finset.sum (Finset.range N) increment + increment N) := by
              rw [hsum]
        _ = initial + Finset.sum (Finset.range N) increment + increment N :=
          max_eq_right hinner_nonneg
        _ = initial + Finset.sum (Finset.range (N + 1)) increment := by
          rw [Finset.sum_range_succ]
          ring

/--
For a nonnegative finite initial workload, a sufficiently negative cumulative
net increment forces a reset.  Unlike the empty-start lemma, the negativity
explicitly includes the carried initial work, so it can drive remote-past
coalescence once a stochastic negative-drift argument supplies such an
excursion.
-/
theorem exists_lindleyWorkloadFrom_reset_of_initial_add_sum_neg
    {initial : Real} {increment : Nat -> Real} {N : Nat}
    (hinitial : 0 <= initial)
    (hneg : initial + Finset.sum (Finset.range N) increment < 0) :
    exists m, 0 < m /\ m <= N /\ lindleyWorkloadFrom initial increment m = 0 := by
  by_contra h
  have hnoreset : forall m, 0 < m -> m <= N ->
      lindleyWorkloadFrom initial increment m ≠ 0 := by
    intro m hm_pos hm_le hzero
    apply h
    exact ⟨m, hm_pos, hm_le, hzero⟩
  have hsum :=
    lindleyWorkloadFrom_eq_initial_add_sum_range_of_no_reset initial increment N hnoreset
  rw [<- hsum] at hneg
  exact (not_lt_of_ge (lindleyWorkloadFrom_nonneg hinitial N)) hneg

/--
For the service-before-arrival convention, a negative net-input excursion
that exceeds the finite pre-batch initial workload forces a genuine pre-batch
reset. The endpoint batch is intentionally not declared empty.
-/
theorem exists_lateBatchPreResetFrom_of_initial_add_sum_net_neg
    {initial : Real} {batch service : Nat -> Real} {N : Nat}
    (hinitial : 0 <= initial)
    (hneg : initial + Finset.sum (Finset.range N)
      (fun n => batch n - service n) < 0) :
    exists m, 0 < m /\ m <= N /\
      lateBatchPreWorkloadFrom initial batch service m = 0 := by
  rcases exists_lindleyWorkloadFrom_reset_of_initial_add_sum_neg
    (initial := initial) (increment := fun n => batch n - service n)
    (N := N) hinitial hneg with ⟨m, hm_pos, hm_le, hm_reset⟩
  refine ⟨m, hm_pos, hm_le, ?_⟩
  rw [lateBatchPreWorkloadFrom_eq_lindleyWorkloadFrom]
  exact hm_reset

/--
After an empty time, the suffix of a reflected trajectory is exactly the
empty-start trajectory of the shifted increment sequence.
-/
theorem lindleyWorkloadFrom_restart_after_reset
    (initial : Real) (increment : Nat -> Real) (m : Nat)
    (hreset : lindleyWorkloadFrom initial increment m = 0) :
    forall n,
      lindleyWorkloadFrom initial increment (m + n) =
        lindleyWorkloadFrom 0 (fun j => increment (m + j)) n := by
  intro n
  induction n with
  | zero => simpa [lindleyWorkloadFrom] using hreset
  | succ n ih =>
      calc
        lindleyWorkloadFrom initial increment (m + (n + 1)) =
            lindleyWorkloadFrom initial increment ((m + n) + 1) := by
              congr 1
        _ =
            max 0 (lindleyWorkloadFrom initial increment (m + n) + increment (m + n)) := by
              rfl
        _ = max 0 (lindleyWorkloadFrom 0 (fun j => increment (m + j)) n +
              (fun j => increment (m + j)) n) := by rw [ih]
        _ = lindleyWorkloadFrom 0 (fun j => increment (m + j)) (n + 1) := by
              rfl

/-- The empty-start restart form of `lindleyWorkloadFrom_restart_after_reset`. -/
theorem lindleyWorkload_restart_after_reset
    (increment : Nat -> Real) (m : Nat)
    (hreset : lindleyWorkload increment m = 0) :
    forall n,
      lindleyWorkload increment (m + n) =
        lindleyWorkload (fun j => increment (m + j)) n := by
  intro n
  have hreset' : lindleyWorkloadFrom 0 increment m = 0 := by
    rw [<- lindleyWorkload_eq_from_zero increment]
    exact hreset
  rw [lindleyWorkload_eq_from_zero]
  rw [lindleyWorkload_eq_from_zero]
  exact lindleyWorkloadFrom_restart_after_reset 0 increment m hreset' n

/--
An average increment converging to a strictly negative limit has a finite
negative prefix.  This is deterministic; an SLLN can supply its hypothesis on
each sample path in a later module.
-/
theorem exists_sum_range_neg_of_tendsto_average_neg
    (increment : Nat -> Real) (limit : Real)
    (hlimit : Filter.Tendsto
      (fun n : Nat => Finset.sum (Finset.range n) increment / (n : Real))
      Filter.atTop (nhds limit))
    (hlimit_neg : limit < 0) :
    exists N, Finset.sum (Finset.range N) increment < 0 := by
  have heventually : ∀ᶠ n : Nat in Filter.atTop,
      Finset.sum (Finset.range n) increment / (n : Real) < 0 :=
    hlimit.eventually_lt tendsto_const_nhds hlimit_neg
  rcases Filter.eventually_atTop.mp heventually with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  have hratio : Finset.sum (Finset.range (N + 1)) increment / ((N + 1 : Nat) : Real) < 0 :=
    hN (N + 1) (Nat.le_succ N)
  have hdenom_pos : (0 : Real) < ((N + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_pos N
  have hmul := (div_lt_iff₀ hdenom_pos).mp hratio
  simpa using hmul

/--
A strictly negative limiting average therefore gives a finite reset of the
empty-start scalar reflected workload.
-/
theorem exists_lindley_reset_of_tendsto_average_neg
    (increment : Nat -> Real) (limit : Real)
    (hlimit : Filter.Tendsto
      (fun n : Nat => Finset.sum (Finset.range n) increment / (n : Real))
      Filter.atTop (nhds limit))
    (hlimit_neg : limit < 0) :
    exists m, 0 < m /\ lindleyWorkload increment m = 0 := by
  rcases exists_sum_range_neg_of_tendsto_average_neg increment limit hlimit hlimit_neg with
    ⟨N, hN⟩
  rcases exists_lindley_reset_of_sum_range_neg hN with ⟨m, hm_pos, -, hm_reset⟩
  exact ⟨m, hm_pos, hm_reset⟩

/--
A finite negative sum of late-batch net increments forces a pre-batch reset.
It intentionally does not assert that the post-batch workload is zero: the
arrival batch at that reset can be positive.
-/
theorem exists_lateBatchPreReset_of_sum_range_net_neg
    {batch service : Nat -> Real} {N : Nat}
    (hneg : Finset.sum (Finset.range N) (fun n => batch n - service n) < 0) :
    exists m, 0 < m /\ m <= N /\ lateBatchPreWorkload batch service m = 0 := by
  rcases exists_lindley_reset_of_sum_range_neg hneg with ⟨m, hm_pos, hm_le, hm_reset⟩
  refine ⟨m, hm_pos, hm_le, ?_⟩
  rw [lateBatchPreWorkload_eq_lindleyWorkload]
  exact hm_reset

/--
After a pre-batch reset, the pre-batch late-batch suffix is exactly the
empty-start suffix for the shifted batches and service amounts.
-/
theorem lateBatchPreWorkload_restart_after_reset
    (batch service : Nat -> Real) (m : Nat)
    (hreset : lateBatchPreWorkload batch service m = 0) :
    forall n,
      lateBatchPreWorkload batch service (m + n) =
        lateBatchPreWorkload (fun j => batch (m + j)) (fun j => service (m + j)) n := by
  intro n
  have hreset' : lindleyWorkload (fun j => batch j - service j) m = 0 := by
    rw [← lateBatchPreWorkload_eq_lindleyWorkload batch service]
    exact hreset
  rw [lateBatchPreWorkload_eq_lindleyWorkload batch service]
  rw [lateBatchPreWorkload_eq_lindleyWorkload
    (fun j => batch (m + j)) (fun j => service (m + j))]
  exact lindleyWorkload_restart_after_reset (fun j => batch j - service j) m hreset' n

/--
The post-batch late-batch suffix also restarts after a pre-batch reset.  This
is the coalescence form relevant to a runner whose stored states are after
endpoint batches.
-/
theorem lateBatchPostWorkload_restart_after_preReset
    (batch service : Nat -> Real) (m : Nat)
    (hreset : lateBatchPreWorkload batch service m = 0) :
    forall n,
      lateBatchPostWorkload batch service (m + n) =
        lateBatchPostWorkload (fun j => batch (m + j)) (fun j => service (m + j)) n := by
  intro n
  rw [lateBatchPostWorkload_eq_pre_add_batch]
  rw [lateBatchPostWorkload_eq_pre_add_batch]
  rw [lateBatchPreWorkload_restart_after_reset batch service m hreset n]

/--
After an explicit-initial-state pre-batch reset, the scalar late-batch suffix
is exactly the empty-start suffix. This is the scalar coalescence statement
used when a remote-past run and a later empty-start run have reached the same
computational fence.
-/
theorem lateBatchPreWorkloadFrom_restart_after_preReset
    (initial : Real) (batch service : Nat -> Real) (m : Nat)
    (hreset : lateBatchPreWorkloadFrom initial batch service m = 0) :
    forall n,
      lateBatchPreWorkloadFrom initial batch service (m + n) =
        lateBatchPreWorkload (fun j => batch (m + j)) (fun j => service (m + j)) n := by
  intro n
  have hreset' : lindleyWorkloadFrom initial (fun j => batch j - service j) m = 0 := by
    rw [<- lateBatchPreWorkloadFrom_eq_lindleyWorkloadFrom]
    exact hreset
  rw [lateBatchPreWorkloadFrom_eq_lindleyWorkloadFrom]
  rw [lateBatchPreWorkload_eq_lindleyWorkload]
  rw [lindleyWorkload_eq_from_zero]
  exact lindleyWorkloadFrom_restart_after_reset initial
    (fun j => batch j - service j) m hreset' n

/--
The post-batch scalar workload coalesces after the same explicit-initial-state
pre-batch reset. The arrival batch at the reset remains part of the common
suffix, so this theorem does not misstate it as a post-batch empty state.
-/
theorem lateBatchPostWorkloadFrom_restart_after_preReset
    (initial : Real) (batch service : Nat -> Real) (m : Nat)
    (hreset : lateBatchPreWorkloadFrom initial batch service m = 0) :
    forall n,
      lateBatchPostWorkloadFrom initial batch service (m + n) =
        lateBatchPostWorkload (fun j => batch (m + j)) (fun j => service (m + j)) n := by
  intro n
  rw [lateBatchPostWorkloadFrom_eq_pre_add_batch]
  rw [lateBatchPostWorkload_eq_pre_add_batch]
  rw [lateBatchPreWorkloadFrom_restart_after_preReset initial batch service m hreset n]

/--
A strictly negative limiting average of late-batch net increments gives a
finite pre-batch reset.  A later SLLN may establish the convergence hypothesis
pathwise; no stochastic assertion is made here.
-/
theorem exists_lateBatchPreReset_of_tendsto_average_net_neg
    (batch service : Nat -> Real) (limit : Real)
    (hlimit : Filter.Tendsto
      (fun n : Nat =>
        Finset.sum (Finset.range n) (fun j => batch j - service j) / (n : Real))
      Filter.atTop (nhds limit))
    (hlimit_neg : limit < 0) :
    exists m, 0 < m /\ lateBatchPreWorkload batch service m = 0 := by
  rcases exists_lindley_reset_of_tendsto_average_neg
    (fun j => batch j - service j) limit hlimit hlimit_neg with ⟨m, hm_pos, hm_reset⟩
  refine ⟨m, hm_pos, ?_⟩
  rw [lateBatchPreWorkload_eq_lindleyWorkload]
  exact hm_reset

end

end AppliedModelingLib.Probability.Queueing
