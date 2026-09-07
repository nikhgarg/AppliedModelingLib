import AppliedModelingLib.Queueing.Lindley.Recursion
import Mathlib.Tactic

/-!
# Initial-state comparison for Lindley's recursion

The remote-past construction uses empty-start replays.  This file records the
exact deterministic comparison with a replay started from a finite nonnegative
state.  It is independent of any input law or stationary construction.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

/-- A reflected run from a nonnegative initial workload is the larger of the
empty-start reflected run and the unreﬂected carried initial workload. -/
theorem lindleyWorkloadFrom_eq_max_empty_initial_add_sum_range
    {initial : Real} {increment : Nat -> Real} (hinitial : 0 <= initial) :
    forall n,
      lindleyWorkloadFrom initial increment n =
        max (lindleyWorkload increment n)
          (initial + Finset.sum (Finset.range n) increment) := by
  intro n
  induction n with
  | zero =>
      simp [lindleyWorkload, lindleyWorkloadFrom, hinitial]
  | succ n ih =>
      rw [show lindleyWorkloadFrom initial increment (n + 1) =
        max 0 (lindleyWorkloadFrom initial increment n + increment n) by rfl,
        ih,
        show lindleyWorkload increment (n + 1) =
          max 0 (lindleyWorkload increment n + increment n) by rfl,
        Finset.sum_range_succ]
      have hmax_add :
          max (lindleyWorkload increment n)
              (initial + Finset.sum (Finset.range n) increment) + increment n =
            max (lindleyWorkload increment n + increment n)
              (initial + Finset.sum (Finset.range n) increment + increment n) := by
        rcases le_total (lindleyWorkload increment n)
          (initial + Finset.sum (Finset.range n) increment) with h | h
        · rw [max_eq_right h]
          have hc : lindleyWorkload increment n + increment n <=
              initial + Finset.sum (Finset.range n) increment + increment n := by
            linarith
          exact (max_eq_right hc).symm
        · rw [max_eq_left h]
          have hc : initial + Finset.sum (Finset.range n) increment + increment n <=
              lindleyWorkload increment n + increment n := by
            linarith
          exact (max_eq_left hc).symm
      rw [hmax_add]
      calc
        max 0
            (max (lindleyWorkload increment n + increment n)
              (initial + Finset.sum (Finset.range n) increment + increment n)) =
            max (max 0 (lindleyWorkload increment n + increment n))
              (initial + Finset.sum (Finset.range n) increment + increment n) := by
                ac_rfl
        _ = max (max 0 (lindleyWorkload increment n + increment n))
              (initial + (Finset.sum (Finset.range n) increment + increment n)) := by
                congr 1
                ring

/-- If the empty-start replay is empty at a horizon and the carried initial
load plus the cumulative increment is nonpositive, then the initial-state
replay is empty at that same horizon. -/
theorem lindleyWorkloadFrom_eq_zero_of_empty_eq_zero_of_initial_add_sum_nonpos
    {initial : Real} {increment : Nat -> Real} {n : Nat}
    (hinitial : 0 <= initial)
    (hempty : lindleyWorkload increment n = 0)
    (hcarried : initial + Finset.sum (Finset.range n) increment <= 0) :
    lindleyWorkloadFrom initial increment n = 0 := by
  rw [lindleyWorkloadFrom_eq_max_empty_initial_add_sum_range hinitial n,
    hempty, max_eq_left]
  exact hcarried

end

end AppliedModelingLib.Probability.Queueing
