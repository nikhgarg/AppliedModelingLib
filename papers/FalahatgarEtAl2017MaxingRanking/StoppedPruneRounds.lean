import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction

/-!
# Stopped Prune rounds

Algorithm 2 stops before a new round once its active set has size at most
`2 * cutoff`.  These definitions and deterministic lemmas retain that stopping
condition, which is essential for the comparison-cost part of Lemma 15.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- Algorithm 2's finite stopped Prune execution, capped at a supplied round count. -/
noncomputable def stoppedPruneRounds {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) : Finset Arm :=
  match roundCount with
  | 0 => active
  | round + 1 =>
      let current := stoppedPruneRounds round cutoff decision outcome active
      if current.card ≤ 2 * cutoff then current
      else pruneRound current (fun arm => decision round arm outcome)

/-- One additional stopped round either leaves the stopped set unchanged or runs Prune. -/
theorem stoppedPruneRounds_succ {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) :
    stoppedPruneRounds (roundCount + 1) cutoff decision outcome active =
      if (stoppedPruneRounds roundCount cutoff decision outcome active).card ≤ 2 * cutoff then
        stoppedPruneRounds roundCount cutoff decision outcome active
      else pruneRound (stoppedPruneRounds roundCount cutoff decision outcome active)
        (fun arm => decision roundCount arm outcome) := by
  rfl

/-- A stopped Prune execution never introduces a new arm. -/
theorem stoppedPruneRounds_subset {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) :
    stoppedPruneRounds roundCount cutoff decision outcome active ⊆ active := by
  induction roundCount with
  | zero => simp [stoppedPruneRounds]
  | succ round ih =>
      rw [stoppedPruneRounds_succ]
      split
      · exact ih
      · exact (pruneRound_subset _ _).trans ih

/-- Once Algorithm 2 stops, the next capped state is unchanged. -/
theorem stoppedPruneRounds_stays_stopped {Ω Arm : Type*} [DecidableEq Arm]
    (round cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm)
    (hstop : (stoppedPruneRounds round cutoff decision outcome active).card ≤ 2 * cutoff) :
    stoppedPruneRounds (round + 1) cutoff decision outcome active =
      stoppedPruneRounds round cutoff decision outcome active := by
  rw [stoppedPruneRounds_succ, if_pos hstop]

/-- Any running stopped-Prune state has more than `cutoff` bad arms. -/
theorem cutoff_lt_badCard_of_goodAnchor_and_running
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (active : Finset Arm) (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hrunning : ¬ active.card ≤ 2 * cutoff) :
    (cutoff : ℝ) < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := by
  by_contra hnotLarge
  have hbad : (pruneBadArms preferenceGap lower anchor active).card ≤ cutoff := by
    exact (Nat.cast_le (α := ℝ)).mp (le_of_not_gt hnotLarge)
  exact hrunning (by
    calc
      active.card ≤ cutoff + (pruneBadArms preferenceGap lower anchor active).card :=
        active_card_le_cutoff_add_badCard_of_goodAnchor preferenceGap lower cutoff anchor active hanchor
      _ ≤ cutoff + cutoff := Nat.add_le_add_left hbad _
      _ = 2 * cutoff := by omega)

/--
On every actually executed Algorithm-2 round, the no-failure contraction
recurrence bounds the bad population by its geometric source target.
-/
theorem stoppedPruneRounds_badCard_le_geometric_of_running
    {Ω Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (decision : ℕ → Arm → Ω → CompareDecision) (outcome : Ω)
    (active : Finset Arm) (delta : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hdelta : 0 ≤ delta)
    (hcontract : ∀ round current,
      (cutoff : ℝ) < ((pruneBadArms preferenceGap lower anchor current).card : ℝ) →
      ((pruneBadArms preferenceGap lower anchor
        (pruneRound current (fun arm => decision round arm outcome))).card : ℝ) ≤
        delta * ((pruneBadArms preferenceGap lower anchor current).card : ℝ)) :
    ∀ round,
      ¬ (stoppedPruneRounds round cutoff decision outcome active).card ≤ 2 * cutoff →
      ((pruneBadArms preferenceGap lower anchor
        (stoppedPruneRounds round cutoff decision outcome active)).card : ℝ) ≤
        delta ^ round * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := by
  intro round
  induction round with
  | zero =>
      intro _
      simp [stoppedPruneRounds]
  | succ round ih =>
      intro hnextRunning
      let current := stoppedPruneRounds round cutoff decision outcome active
      have hcurrentRunning : ¬ current.card ≤ 2 * cutoff := by
        intro hstop
        have heq := stoppedPruneRounds_stays_stopped round cutoff decision outcome active hstop
        apply hnextRunning
        rw [heq]
        exact hstop
      have hcurrentBound := ih hcurrentRunning
      have hcurrentLarge := cutoff_lt_badCard_of_goodAnchor_and_running
        preferenceGap lower cutoff anchor current hanchor hcurrentRunning
      have hstep := hcontract round current hcurrentLarge
      rw [stoppedPruneRounds_succ, if_neg hcurrentRunning]
      calc
        ((pruneBadArms preferenceGap lower anchor
          (pruneRound current (fun arm => decision round arm outcome))).card : ℝ) ≤
            delta * ((pruneBadArms preferenceGap lower anchor current).card : ℝ) := hstep
        _ ≤ delta * (delta ^ round *
            ((pruneBadArms preferenceGap lower anchor active).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcurrentBound hdelta
        _ = delta ^ (round + 1) *
            ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := by
          rw [pow_succ]
          ring

/-- The number of comparisons issued in one actually executed stopped-Prune round. -/
noncomputable def stoppedPruneRoundComparisonCount {Ω Arm : Type*} [DecidableEq Arm]
    (cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision) (outcome : Ω)
    (active : Finset Arm) (lower upper delta : ℝ) (round : ℕ) : ℕ :=
  if (stoppedPruneRounds round cutoff decision outcome active).card ≤ 2 * cutoff then 0 else
    (stoppedPruneRounds round cutoff decision outcome active).card *
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)

/-- The capped comparison count of Algorithm 2 with its printed stopping rule. -/
noncomputable def stoppedPruneComparisonCount {Ω Arm : Type*} [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision) (outcome : Ω)
    (active : Finset Arm) (lower upper delta : ℝ) : ℕ :=
  ∑ round ∈ Finset.range roundCount,
    stoppedPruneRoundComparisonCount cutoff decision outcome active lower upper delta round

/--
On a path satisfying the source contraction invariant, Algorithm 2's actual
stopped-round comparison count is bounded by its geometric bad-arm envelope
plus the `cutoff` good-arm envelope.  This keeps the source stopping rule in
the resource statement instead of charging padded post-stop rounds.
-/
theorem stoppedPruneComparisonCount_real_le_geometricBudgetSum
    {Ω Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount cutoff : ℕ) (decision : ℕ → Arm → Ω → CompareDecision) (outcome : Ω)
    (active : Finset Arm) (preferenceGap : Arm → Arm → ℝ) (anchor : Arm)
    (lower upper delta : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hdelta : 0 ≤ delta)
    (hcontract : ∀ round current,
      (cutoff : ℝ) < ((pruneBadArms preferenceGap lower anchor current).card : ℝ) →
      ((pruneBadArms preferenceGap lower anchor
        (pruneRound current (fun arm => decision round arm outcome))).card : ℝ) ≤
        delta * ((pruneBadArms preferenceGap lower anchor current).card : ℝ)) :
    (stoppedPruneComparisonCount roundCount cutoff decision outcome active lower upper delta : ℝ) ≤
      ∑ round ∈ Finset.range roundCount,
        ((cutoff : ℝ) + delta ^ round *
          ((pruneBadArms preferenceGap lower anchor active).card : ℝ)) *
          (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) : ℝ) := by
  unfold stoppedPruneComparisonCount
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro round hround
  unfold stoppedPruneRoundComparisonCount
  let current := stoppedPruneRounds round cutoff decision outcome active
  let budget := fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)
  have hbudgetNonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg budget
  have hbadInitNonneg : 0 ≤
      ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := Nat.cast_nonneg _
  have hgeomNonneg : 0 ≤ delta ^ round *
      ((pruneBadArms preferenceGap lower anchor active).card : ℝ) :=
    mul_nonneg (pow_nonneg hdelta _) hbadInitNonneg
  by_cases hstop : current.card ≤ 2 * cutoff
  · change ↑(if current.card ≤ 2 * cutoff then (0 : ℕ) else current.card * budget) ≤
      ((cutoff : ℝ) + delta ^ round *
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ)) * (budget : ℝ)
    rw [if_pos hstop]
    norm_num
    exact mul_nonneg (add_nonneg (Nat.cast_nonneg _) hgeomNonneg) hbudgetNonneg
  · have hbadGeo := stoppedPruneRounds_badCard_le_geometric_of_running
      preferenceGap lower cutoff anchor decision outcome active delta hanchor hdelta hcontract round hstop
    have hactiveNat := active_card_le_cutoff_add_badCard_of_goodAnchor
      preferenceGap lower cutoff anchor current hanchor
    have hactiveReal : (current.card : ℝ) ≤
        (cutoff : ℝ) + delta ^ round *
          ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := by
      calc
        (current.card : ℝ) ≤ (cutoff : ℝ) +
            ((pruneBadArms preferenceGap lower anchor current).card : ℝ) := by
              exact_mod_cast hactiveNat
        _ ≤ (cutoff : ℝ) + delta ^ round *
            ((pruneBadArms preferenceGap lower anchor active).card : ℝ) := by
              gcongr
    change ↑(if current.card ≤ 2 * cutoff then (0 : ℕ) else current.card * budget) ≤
      ((cutoff : ℝ) + delta ^ round *
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ)) * (budget : ℝ)
    rw [if_neg hstop]
    push_cast
    change (current.card : ℝ) * (budget : ℝ) ≤
      ((cutoff : ℝ) + delta ^ round *
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ)) * (budget : ℝ)
    exact mul_le_mul_of_nonneg_right hactiveReal hbudgetNonneg

end FalahatgarEtAl2017MaxingRanking
