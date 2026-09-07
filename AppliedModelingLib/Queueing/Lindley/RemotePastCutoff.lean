import AppliedModelingLib.Queueing.Lindley.Recursion
import Mathlib.Tactic

/-!
# Remote-past cutoffs for deterministic reflected workloads

This module is entirely deterministic.  Its index `0` is the latest
increment and increasing indices point farther into the past.  Thus an
empty-start trajectory begun at remote index `N` processes the increments
`d (N - 1), d (N - 2), ..., d 0` in chronological order.

The only asymptotic premise is that the cumulative remote-past net input
goes to `-∞`.  It yields a finite maximum cutoff of that cumulative path and,
in turn, a genuine pre-batch Lindley reset at that cutoff for every sufficiently
remote empty-start trajectory.  No arrival process, queueing discipline,
stationary construction, or artificial endpoint batch is introduced here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

/-- Cumulative net input in the outward-from-present indexing convention. -/
def remotePastCumulativeNetInput (d : Nat -> Real) (N : Nat) : Real :=
  Finset.sum (Finset.range N) d

/-- The chronological increment at step `j` of an empty run started at remote index `N`. -/
def reverseRemotePastIncrement (d : Nat -> Real) (N j : Nat) : Real :=
  d (N - (j + 1))

@[simp]
theorem remotePastCumulativeNetInput_zero (d : Nat -> Real) :
    remotePastCumulativeNetInput d 0 = 0 := by
  simp [remotePastCumulativeNetInput]

theorem remotePastCumulativeNetInput_succ (d : Nat -> Real) (N : Nat) :
    remotePastCumulativeNetInput d (N + 1) =
      remotePastCumulativeNetInput d N + d N := by
  simp [remotePastCumulativeNetInput, Finset.sum_range_succ]

/-- A sequence whose normalization by the positive index `n + 1` converges
to a strictly negative value itself tends to `-∞`.  This is the deterministic
asymptotic conversion used when a marked-renewal law supplies a negative
mean net input. -/
theorem tendsto_atBot_of_tendsto_div_nat_succ_neg
    (f : Nat -> Real) (limit : Real)
    (hlimit : Filter.Tendsto
      (fun n : Nat => f n / ((n + 1 : Nat) : Real))
      Filter.atTop (nhds limit))
    (hlimit_neg : limit < 0) :
    Filter.Tendsto f Filter.atTop Filter.atBot := by
  have hhalf_neg : limit / 2 < 0 := by linarith
  have hratio : ∀ᶠ n : Nat in Filter.atTop,
      f n / ((n + 1 : Nat) : Real) < limit / 2 :=
    hlimit.eventually_lt tendsto_const_nhds (by linarith)
  refine Filter.tendsto_atBot.2 fun bound => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (bound / (limit / 2))
  filter_upwards [hratio, Filter.eventually_ge_atTop N] with n hratio_n hn
  have hdenom_pos : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hscaled : f n < (limit / 2) * ((n + 1 : Nat) : Real) := by
    exact (div_lt_iff₀ hdenom_pos).mp hratio_n
  have hquotient_lt : bound / (limit / 2) < ((n + 1 : Nat) : Real) := by
    calc
      bound / (limit / 2) < (N : Real) := by exact_mod_cast hN
      _ ≤ (n : Real) := by exact_mod_cast hn
      _ < ((n + 1 : Nat) : Real) := by norm_num
  have hproduct : ((n + 1 : Nat) : Real) * (limit / 2) < bound := by
    exact (div_lt_iff_of_neg hhalf_neg).mp hquotient_lt
  nlinarith

/-- Convergence to `-∞` is unchanged by discarding the initial value of a
natural-indexed sequence. -/
theorem tendsto_atBot_of_tendsto_succ_atBot
    (f : Nat -> Real)
    (hlimit : Filter.Tendsto (fun n : Nat => f (n + 1))
      Filter.atTop Filter.atBot) :
    Filter.Tendsto f Filter.atTop Filter.atBot := by
  refine Filter.tendsto_atBot.2 fun bound => ?_
  rcases Filter.eventually_atTop.mp (Filter.tendsto_atBot.1 hlimit bound) with
    ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N + 1, ?_⟩
  intro n hn
  have hN_le : N ≤ n - 1 := by omega
  have hvalue := hN (n - 1) hN_le
  have hindex : (n - 1) + 1 = n := by omega
  simpa [hindex] using hvalue

/--
If the outward cumulative net input tends to `-∞`, it has a finite global
maximum.  In particular, no remote-past index can exceed the selected cutoff.
-/
theorem exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot
    (d : Nat -> Real)
    (hlim : Filter.Tendsto (remotePastCumulativeNetInput d)
      Filter.atTop Filter.atBot) :
    ∃ K, ∀ J, remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d K := by
  have htail_eventually : ∀ᶠ J : Nat in Filter.atTop,
      remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d 0 :=
    (Filter.tendsto_atBot.1 hlim) _
  rcases Filter.eventually_atTop.mp htail_eventually with ⟨N, hN⟩
  let values : Finset Real := (Finset.range (N + 1)).image (remotePastCumulativeNetInput d)
  have hvalues_nonempty : values.Nonempty := by
    refine ⟨remotePastCumulativeNetInput d 0, ?_⟩
    change remotePastCumulativeNetInput d 0 ∈
      (Finset.range (N + 1)).image (remotePastCumulativeNetInput d)
    exact Finset.mem_image.mpr ⟨0,
      Finset.mem_range.mpr (by simpa [Nat.succ_eq_add_one] using Nat.succ_pos N), rfl⟩
  let M : Real := values.max' hvalues_nonempty
  have hM_mem : M ∈ values := by
    exact Finset.max'_mem values hvalues_nonempty
  rcases Finset.mem_image.mp hM_mem with ⟨K, hK_mem, hK_eq⟩
  refine ⟨K, ?_⟩
  intro J
  by_cases hJ : J ≤ N
  · have hJ_mem : remotePastCumulativeNetInput d J ∈ values := by
      refine Finset.mem_image.mpr ⟨J, ?_, rfl⟩
      simpa using hJ
    have hleM : remotePastCumulativeNetInput d J ≤ M :=
      Finset.le_max' values _ hJ_mem
    simpa [M] using hleM.trans_eq hK_eq.symm
  · have hNJ : N ≤ J := by omega
    have htail : remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d 0 :=
      hN J hNJ
    have hzero_mem : remotePastCumulativeNetInput d 0 ∈ values := by
      refine Finset.mem_image.mpr ⟨0, ?_, rfl⟩
      change 0 ∈ Finset.range (N + 1)
      exact Finset.mem_range.mpr
        (by simpa [Nat.succ_eq_add_one] using Nat.succ_pos N)
    have hzero_le_M : remotePastCumulativeNetInput d 0 ≤ M :=
      Finset.le_max' values _ hzero_mem
    exact htail.trans (by simpa [M] using hzero_le_M.trans_eq hK_eq.symm)

/--
The suffix version of the global-cutoff property.  This is the form consumed
by the reversed Lindley recursion below.
-/
theorem exists_remotePastCumulativeNetInput_cutoff_of_tendsto_atBot
    (d : Nat -> Real)
    (hlim : Filter.Tendsto (remotePastCumulativeNetInput d)
      Filter.atTop Filter.atBot) :
    ∃ K, ∀ J ≥ K,
      remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d K := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hK⟩
  exact ⟨K, fun J _ => hK J⟩

/--
At any finite step before the cutoff, the reversed empty-start Lindley
workload is bounded by the cutoff's cumulative surplus over the current
remote-past cumulative level.
-/
theorem lindleyWorkload_reverseRemotePast_le_cutoff_surplus
    (d : Nat -> Real) (K N : Nat)
    (hKN : K ≤ N)
    (hmax : ∀ J, K ≤ J -> J ≤ N ->
      remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d K) :
    ∀ q, q ≤ N - K ->
      lindleyWorkload (reverseRemotePastIncrement d N) q ≤
        remotePastCumulativeNetInput d K - remotePastCumulativeNetInput d (N - q) := by
  intro q hq
  induction q with
  | zero =>
      have hNK : remotePastCumulativeNetInput d N ≤ remotePastCumulativeNetInput d K :=
        hmax N hKN (le_refl N)
      simpa [lindleyWorkload, remotePastCumulativeNetInput_zero] using sub_nonneg.mpr hNK
  | succ q ih =>
      have hq_prev : q ≤ N - K := by omega
      have hq_le_N : q + 1 ≤ N := by omega
      have hindex_lower : K ≤ N - (q + 1) := by omega
      have hindex_upper : N - (q + 1) ≤ N := Nat.sub_le _ _
      have hcurrent_le : remotePastCumulativeNetInput d (N - (q + 1)) ≤
          remotePastCumulativeNetInput d K :=
        hmax (N - (q + 1)) hindex_lower hindex_upper
      have hcurrent_nonneg : 0 ≤
          remotePastCumulativeNetInput d K - remotePastCumulativeNetInput d (N - (q + 1)) :=
        sub_nonneg.mpr hcurrent_le
      have hsum_step : remotePastCumulativeNetInput d (N - q) =
          remotePastCumulativeNetInput d (N - (q + 1)) + d (N - (q + 1)) := by
        rw [show N - q = (N - (q + 1)) + 1 by omega]
        exact remotePastCumulativeNetInput_succ d _
      calc
        lindleyWorkload (reverseRemotePastIncrement d N) (q + 1) =
            max 0 (lindleyWorkload (reverseRemotePastIncrement d N) q +
              d (N - (q + 1))) := by
                rfl
        _ ≤ max 0 ((remotePastCumulativeNetInput d K -
              remotePastCumulativeNetInput d (N - q)) + d (N - (q + 1))) := by
                apply max_le_max_left
                linarith [ih hq_prev]
        _ = max 0 (remotePastCumulativeNetInput d K -
              remotePastCumulativeNetInput d (N - (q + 1))) := by
                congr 1
                rw [hsum_step]
                ring
        _ = remotePastCumulativeNetInput d K -
              remotePastCumulativeNetInput d (N - (q + 1)) :=
                by exact max_eq_right hcurrent_nonneg

/--
Every empty-start Lindley run begun at remote index `N ≥ K` is genuinely
empty when it reaches a finite global cumulative-net-input maximum `K`.
This is a pre-batch scalar reset; no endpoint batch is added or relabelled.
-/
theorem lindleyWorkload_reverseRemotePast_eq_zero_at_global_cutoff
    (d : Nat -> Real) (K N : Nat)
    (hKN : K ≤ N)
    (hmax : ∀ J, remotePastCumulativeNetInput d J ≤ remotePastCumulativeNetInput d K) :
    lindleyWorkload (reverseRemotePastIncrement d N) (N - K) = 0 := by
  have hle := lindleyWorkload_reverseRemotePast_le_cutoff_surplus d K N hKN
    (fun J _ _ => hmax J) (N - K) (le_refl _)
  have hnonneg := lindleyWorkload_nonneg (reverseRemotePastIncrement d N) (N - K)
  have hendpoint : N - (N - K) = K := Nat.sub_sub_self hKN
  rw [hendpoint] at hle
  linarith

/--
The same remote-past cutoff is a literal pre-batch reset in the
service-before-arrival recursion.  The two reversed coordinate functions are
only a reindexing of the supplied batch and service sequences.
-/
theorem lateBatchPreWorkload_reverseRemotePast_eq_zero_at_global_cutoff
    (batch service : Nat -> Real) (K N : Nat)
    (hKN : K ≤ N)
    (hmax : ∀ J,
      remotePastCumulativeNetInput (fun i => batch i - service i) J ≤
        remotePastCumulativeNetInput (fun i => batch i - service i) K) :
    lateBatchPreWorkload
      (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N)
      (N - K) = 0 := by
  rw [lateBatchPreWorkload_eq_lindleyWorkload]
  exact lindleyWorkload_reverseRemotePast_eq_zero_at_global_cutoff
    (fun i => batch i - service i) K N hKN hmax

/-- Once a remote empty-start trace has reached its genuine cutoff reset, its
pre-batch workload at the present is independent of how much older input was
included.  The right-hand side is the finite suffix beginning at the cutoff;
no endpoint batch is inserted or removed. -/
theorem lateBatchPreWorkload_reverseRemotePast_coalesces_at_present_of_global_cutoff
    (batch service : Nat -> Real) (K N : Nat)
    (hKN : K ≤ N)
    (hmax : ∀ J,
      remotePastCumulativeNetInput (fun i => batch i - service i) J ≤
        remotePastCumulativeNetInput (fun i => batch i - service i) K) :
    lateBatchPreWorkload
      (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N) N =
      lateBatchPreWorkload
        (reverseRemotePastIncrement batch K)
        (reverseRemotePastIncrement service K) K := by
  have hreset : lateBatchPreWorkload
      (reverseRemotePastIncrement batch N)
      (reverseRemotePastIncrement service N) (N - K) = 0 :=
    lateBatchPreWorkload_reverseRemotePast_eq_zero_at_global_cutoff
      batch service K N hKN hmax
  have hrestart := lateBatchPreWorkload_restart_after_reset
    (reverseRemotePastIncrement batch N)
    (reverseRemotePastIncrement service N) (N - K) hreset K
  have hbatch :
      (fun j => reverseRemotePastIncrement batch N (N - K + j)) =
        reverseRemotePastIncrement batch K := by
    funext j
    unfold reverseRemotePastIncrement
    congr 1
    omega
  have hservice :
      (fun j => reverseRemotePastIncrement service N (N - K + j)) =
        reverseRemotePastIncrement service K := by
    funext j
    unfold reverseRemotePastIncrement
    congr 1
    omega
  rw [show (N - K) + K = N by omega, hbatch, hservice] at hrestart
  exact hrestart

/--
Combining the deterministic at-bottom limit and reversed Lindley bridge:
there is one finite cutoff at which all sufficiently remote empty-start
trajectories coalesce at zero.
-/
theorem exists_lindleyWorkload_reverseRemotePast_cutoff_of_tendsto_atBot
    (d : Nat -> Real)
    (hlim : Filter.Tendsto (remotePastCumulativeNetInput d)
      Filter.atTop Filter.atBot) :
    ∃ K, ∀ N ≥ K,
      lindleyWorkload (reverseRemotePastIncrement d N) (N - K) = 0 := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot d hlim with
    ⟨K, hmax⟩
  refine ⟨K, ?_⟩
  intro N hKN
  exact lindleyWorkload_reverseRemotePast_eq_zero_at_global_cutoff d K N hKN hmax

/--
The service-before-arrival form of the common remote-past cutoff.  This
concludes a genuine pre-batch zero state for all sufficiently remote
empty-start finite runs, without introducing a terminal or source fence.
-/
theorem exists_lateBatchPreWorkload_reverseRemotePast_cutoff_of_tendsto_atBot
    (batch service : Nat -> Real)
    (hlim : Filter.Tendsto
      (remotePastCumulativeNetInput (fun i => batch i - service i))
      Filter.atTop Filter.atBot) :
    ∃ K, ∀ N ≥ K,
      lateBatchPreWorkload
        (reverseRemotePastIncrement batch N)
        (reverseRemotePastIncrement service N)
        (N - K) = 0 := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot
    (fun i => batch i - service i) hlim with ⟨K, hmax⟩
  refine ⟨K, ?_⟩
  intro N hKN
  exact lateBatchPreWorkload_reverseRemotePast_eq_zero_at_global_cutoff
    batch service K N hKN hmax

/-- The remote-past present workload has a stable finite-suffix value as soon
as its cumulative net input tends to `-∞`. -/
theorem exists_lateBatchPreWorkload_reverseRemotePast_coalescence_at_present_of_tendsto_atBot
    (batch service : Nat -> Real)
    (hlim : Filter.Tendsto
      (remotePastCumulativeNetInput (fun i => batch i - service i))
      Filter.atTop Filter.atBot) :
    ∃ K, ∀ N ≥ K,
      lateBatchPreWorkload
        (reverseRemotePastIncrement batch N)
        (reverseRemotePastIncrement service N) N =
        lateBatchPreWorkload
          (reverseRemotePastIncrement batch K)
          (reverseRemotePastIncrement service K) K := by
  rcases exists_remotePastCumulativeNetInput_global_max_of_tendsto_atBot
      (fun i => batch i - service i) hlim with ⟨K, hmax⟩
  refine ⟨K, ?_⟩
  intro N hKN
  exact lateBatchPreWorkload_reverseRemotePast_coalesces_at_present_of_global_cutoff
    batch service K N hKN hmax

end

end AppliedModelingLib.Probability.Queueing
