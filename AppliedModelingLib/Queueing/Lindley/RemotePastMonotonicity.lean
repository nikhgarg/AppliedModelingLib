import AppliedModelingLib.Queueing.Lindley.InitialState
import AppliedModelingLib.Queueing.Lindley.RemotePastCutoff
import Mathlib.Tactic

/-!
# Monotonicity of finite remote-past Lindley replays

An empty-start replay from an older remote-past index contains the same later
increments as a replay from a newer index, but begins with a nonnegative
state at the newer index.  This file records the resulting pathwise
monotonicity.  It is deterministic and does not use a stochastic law.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

/-- A reflected recursion is monotone in a nonnegative initial workload. -/
theorem lindleyWorkload_le_lindleyWorkloadFrom
    {initial : Real} {increment : Nat -> Real} (hinitial : 0 <= initial) (n : Nat) :
    lindleyWorkload increment n <= lindleyWorkloadFrom initial increment n := by
  rw [lindleyWorkloadFrom_eq_max_empty_initial_add_sum_range hinitial n]
  exact le_max_left _ _

/-- Splitting an explicit-initial-state reflected recursion at a finite time
preserves its exact carried state for the remaining suffix. -/
theorem lindleyWorkloadFrom_add
    (initial : Real) (increment : Nat -> Real) (m n : Nat) :
    lindleyWorkloadFrom initial increment (m + n) =
      lindleyWorkloadFrom (lindleyWorkloadFrom initial increment m)
        (fun j => increment (m + j)) n := by
  induction n with
  | zero =>
      simp [lindleyWorkloadFrom]
  | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by omega]
      change max 0 (lindleyWorkloadFrom initial increment (m + n) + increment (m + n)) = _
      rw [ih]
      rfl

/-- An empty remote-past replay from `N` decomposes at the newer remote
index `K` into the exact nonnegative carried state and the replay beginning
at `K`. -/
theorem lindleyWorkload_reverseRemotePast_eq_lindleyWorkloadFrom_suffix
    (d : Nat -> Real) (K N : Nat) (hKN : K <= N) :
    lindleyWorkload (reverseRemotePastIncrement d N) N =
      lindleyWorkloadFrom
        (lindleyWorkload (reverseRemotePastIncrement d N) (N - K))
        (reverseRemotePastIncrement d K) K := by
  have hsplit := lindleyWorkloadFrom_add 0
    (reverseRemotePastIncrement d N) (N - K) K
  have hsum : (N - K) + K = N := by omega
  rw [hsum] at hsplit
  have hsuffix :
      (fun j => reverseRemotePastIncrement d N ((N - K) + j)) =
        reverseRemotePastIncrement d K := by
    funext j
    unfold reverseRemotePastIncrement
    congr 1
    omega
  rw [hsuffix] at hsplit
  calc
    lindleyWorkload (reverseRemotePastIncrement d N) N =
        lindleyWorkloadFrom 0 (reverseRemotePastIncrement d N) N :=
      congrFun (lindleyWorkload_eq_from_zero _) N
    _ = lindleyWorkloadFrom
        (lindleyWorkloadFrom 0 (reverseRemotePastIncrement d N) (N - K))
        (reverseRemotePastIncrement d K) K := hsplit
    _ = lindleyWorkloadFrom
        (lindleyWorkload (reverseRemotePastIncrement d N) (N - K))
        (reverseRemotePastIncrement d K) K := by
      rw [← lindleyWorkload_eq_from_zero (reverseRemotePastIncrement d N)]

/-- Starting the same literal suffix with the carried workload from an older
remote past can only increase its present reflected workload. -/
theorem lindleyWorkload_reverseRemotePast_mono
    (d : Nat -> Real) (K N : Nat) (hKN : K <= N) :
    lindleyWorkload (reverseRemotePastIncrement d K) K <=
      lindleyWorkload (reverseRemotePastIncrement d N) N := by
  rw [lindleyWorkload_reverseRemotePast_eq_lindleyWorkloadFrom_suffix d K N hKN]
  exact lindleyWorkload_le_lindleyWorkloadFrom
    (lindleyWorkload_nonneg (reverseRemotePastIncrement d N) (N - K)) K

/-- The service-before-arrival finite replay has the same remote-past
monotonicity.  No sign restriction is needed: reflection is monotone in the
carried state for every scalar increment sequence. -/
theorem lateBatchPreWorkload_reverseRemotePast_mono
    (batch service : Nat -> Real) (K N : Nat) (hKN : K <= N) :
    lateBatchPreWorkload
      (reverseRemotePastIncrement batch K)
      (reverseRemotePastIncrement service K) K <=
    lateBatchPreWorkload
      (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N) N := by
  rw [lateBatchPreWorkload_eq_lindleyWorkload,
    lateBatchPreWorkload_eq_lindleyWorkload]
  simpa only [reverseRemotePastIncrement] using
    (lindleyWorkload_reverseRemotePast_mono
      (fun i => batch i - service i) K N hKN)

end

end AppliedModelingLib.Probability.Queueing
