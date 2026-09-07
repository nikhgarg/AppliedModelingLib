import AppliedModelingLib.Queueing.Lindley.InitialState
import AppliedModelingLib.Queueing.Lindley.RemotePastCutoff
import Mathlib.Tactic

/-!
# Remote-past coupling from a finite initial state

The empty-start remote-past construction is the canonical causal solution of
Lindley's recursion.  This file proves the deterministic fact needed for
uniqueness: any finite nonnegative state placed sufficiently far in the past
is erased at the same finite cutoff, and then has the same present state as
the empty-start construction.  No probability law is used here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

/-- The sum of a reversed remote-past block is the difference of the outward
cumulative net-input values at its endpoints. -/
theorem sum_range_reverseRemotePastIncrement_eq_cumulative_sub
    (d : Nat -> Real) (K N : Nat) (hKN : K <= N) :
    Finset.sum (Finset.range (N - K)) (reverseRemotePastIncrement d N) =
      remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K := by
  have hNK : N = K + (N - K) := by omega
  calc
    Finset.sum (Finset.range (N - K)) (reverseRemotePastIncrement d N) =
        Finset.sum (Finset.range (N - K))
          (fun j => d (K + ((N - K) - 1 - j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            unfold reverseRemotePastIncrement
            congr 1
            have hjlt : j < N - K := Finset.mem_range.mp hj
            omega
    _ = Finset.sum (Finset.range (N - K)) (fun j => d (K + j)) := by
      exact Finset.sum_range_reflect (fun j => d (K + j)) (N - K)
    _ = remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K := by
      have hcumulative : remotePastCumulativeNetInput d N =
          remotePastCumulativeNetInput d K +
            Finset.sum (Finset.range (N - K)) (fun j => d (K + j)) := by
        rw [hNK, remotePastCumulativeNetInput, Finset.sum_range_add]
        simp [remotePastCumulativeNetInput]
      rw [hcumulative]
      ring

/-- If an empty remote-past run resets at a cutoff and the unreﬂected carried
initial load has been drained by that cutoff, the finite-initial-state run
also resets there. -/
theorem lindleyWorkloadFrom_reverseRemotePast_eq_zero_at_global_cutoff
    {initial : Real} (d : Nat -> Real) (K N : Nat)
    (hinitial : 0 <= initial) (hKN : K <= N)
    (hmax : forall J,
      remotePastCumulativeNetInput d J <= remotePastCumulativeNetInput d K)
    (hcarried : initial +
      (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) <= 0) :
    lindleyWorkloadFrom initial (reverseRemotePastIncrement d N) (N - K) = 0 := by
  apply lindleyWorkloadFrom_eq_zero_of_empty_eq_zero_of_initial_add_sum_nonpos hinitial
  · exact lindleyWorkload_reverseRemotePast_eq_zero_at_global_cutoff d K N hKN hmax
  · rw [sum_range_reverseRemotePastIncrement_eq_cumulative_sub d K N hKN]
    exact hcarried

/-- Once both replays have reset at the same literal remote-past cutoff, the
present state from a finite initial condition is exactly the canonical
empty-start suffix state. -/
theorem lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
    {initial : Real} (d : Nat -> Real) (K N : Nat)
    (hinitial : 0 <= initial) (hKN : K <= N)
    (hmax : forall J,
      remotePastCumulativeNetInput d J <= remotePastCumulativeNetInput d K)
    (hcarried : initial +
      (remotePastCumulativeNetInput d N - remotePastCumulativeNetInput d K) <= 0) :
    lindleyWorkloadFrom initial (reverseRemotePastIncrement d N) N =
      lindleyWorkload (reverseRemotePastIncrement d K) K := by
  have hreset : lindleyWorkloadFrom initial (reverseRemotePastIncrement d N)
      (N - K) = 0 :=
    lindleyWorkloadFrom_reverseRemotePast_eq_zero_at_global_cutoff d K N
      hinitial hKN hmax hcarried
  have hrestart := lindleyWorkloadFrom_restart_after_reset initial
    (reverseRemotePastIncrement d N) (N - K) hreset K
  have htail :
      (fun j => reverseRemotePastIncrement d N ((N - K) + j)) =
        reverseRemotePastIncrement d K := by
    funext j
    unfold reverseRemotePastIncrement
    congr 1
    omega
  rw [show (N - K) + K = N by omega, htail] at hrestart
  simpa [lindleyWorkload_eq_from_zero] using hrestart

/-- Under a remote-past cumulative input tending to `-∞`, every fixed finite
nonnegative initial state is erased by the common cutoff for all sufficiently
remote starts. -/
theorem exists_lindleyWorkloadFrom_reverseRemotePast_coupling_of_tendsto_atBot
    {initial : Real} (d : Nat -> Real) (hinitial : 0 <= initial)
    (hlim : Filter.Tendsto (remotePastCumulativeNetInput d)
      Filter.atTop Filter.atBot) :
    exists K N0, K <= N0 /\ forall N, N0 <= N ->
      lindleyWorkloadFrom initial (reverseRemotePastIncrement d N) N =
        lindleyWorkload (reverseRemotePastIncrement d K) K := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  have htail : ∀ᶠ N : Nat in Filter.atTop,
      remotePastCumulativeNetInput d N <
        remotePastCumulativeNetInput d K - initial := by
    filter_upwards [Filter.tendsto_atBot.1 hlim
      (remotePastCumulativeNetInput d K - initial - 1)] with N hN
    linarith
  rcases Filter.eventually_atTop.mp htail with ⟨N1, hN1⟩
  refine ⟨K, max K N1, le_max_left _ _, ?_⟩
  intro N hN
  have hKN : K <= N :=
    (le_max_left K N1).trans hN
  have hN1N : N1 <= N :=
    (le_max_right K N1).trans hN
  apply lindleyWorkloadFrom_reverseRemotePast_coalesces_at_present_of_global_cutoff
    d K N hinitial hKN hmax
  have hbound := hN1 N hN1N
  linarith

end

end AppliedModelingLib.Probability.Queueing
