import FalahatgarEtAl2017MaxingRanking.CanonicalFreshPruneRounds
import FalahatgarEtAl2017MaxingRanking.StoppedPruneRounds

/-!
# Fresh stopped Prune rounds

Algorithm 2 stops before issuing another round once its active set has size at
most `2 * cutoff`.  This module retains that rule in the finite adaptive PMF:
the failure flag is charged only on rounds that the algorithm actually runs.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- One stopped Algorithm-2 state transition driven by its current fresh outcome. -/
noncomputable def stoppedPruneAdvance
    {Arm Outcome : Type*} [DecidableEq Arm]
    (cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) :
    AdaptiveStateUpdate (Finset Arm) Outcome := fun round active outcome =>
  if active.card ≤ 2 * cutoff then active
  else pruneRound active (decision round active outcome)

/-- A stopped-Prune transition never introduces an arm. -/
theorem stoppedPruneAdvance_subset
    {Arm Outcome : Type*} [DecidableEq Arm]
    (cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome) :
    stoppedPruneAdvance cutoff decision round active outcome ⊆ active := by
  unfold stoppedPruneAdvance
  split
  · exact Finset.Subset.rfl
  · exact pruneRound_subset _ _

/--
The finite law of a stopped Algorithm-2 execution.  Its Boolean flag records
only a contraction failure from an actually executed Prune round.
-/
noncomputable def freshStoppedPruneRoundsStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (Finset Arm × Bool) := by
  classical
  exact adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
    (stoppedPruneAdvance cutoff decision)
    (fun round active outcome =>
      ¬ active.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ))
    roundCount

/--
The Lemma-15 size conclusion for a stopped finite fresh-round execution.  The
state invariant records three no-failure alternatives: Algorithm 2 has
already stopped, the bad population is below its cutoff, or it follows the
source geometric recurrence.
-/
theorem freshStoppedPruneRounds_card_success_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (delta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hdelta : 0 ≤ delta)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ≤
        failureBudget round)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
          decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := by
  classical
  let badCount : Finset Arm → ℝ := fun active =>
    ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := stoppedPruneAdvance cutoff decision
  let bad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    ¬ active.card ≤ 2 * cutoff ∧ cutoff < badCount active ∧
      delta * badCount active < badCount (advance round active outcome)
  let invariant : ℕ → Finset Arm → Bool → Prop := fun round active flag =>
    flag = false → active.card ≤ 2 * cutoff ∨ badCount active ≤ cutoff ∨
      badCount active ≤ delta ^ round * badCount initial
  have hinitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    right; right
    simp [badCount] at hactive ⊢
    subst active
    simp
  have hbadMonotone : ∀ round active outcome,
      badCount (advance round active outcome) ≤ badCount active := by
    intro round active outcome
    dsimp [badCount, advance]
    exact_mod_cast Finset.card_le_card
      (pruneBadArms_subset_of_subset preferenceGap lower anchor
        (stoppedPruneAdvance_subset cutoff decision round active outcome))
  have hadvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round active outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round active outcome := by
      simpa using hbadFalse
    rcases hinvariant hflag with hstopped | hsmall | hgeometric
    · left
      simp [advance, stoppedPruneAdvance, hstopped]
    · right; left
      exact (hbadMonotone round active outcome).trans hsmall
    · by_cases hsmall : badCount active ≤ cutoff
      · right; left
        exact (hbadMonotone round active outcome).trans hsmall
      · by_cases hstopped : active.card ≤ 2 * cutoff
        · left
          simp [advance, stoppedPruneAdvance, hstopped]
        · right; right
          have hcontract : badCount (advance round active outcome) ≤
              delta * badCount active := by
                apply le_of_not_gt
                intro htooMany
                exact hnotBad ⟨hstopped, lt_of_not_ge hsmall, htooMany⟩
          calc
            badCount (advance round active outcome) ≤ delta * badCount active := hcontract
            _ ≤ delta * (delta ^ round * badCount initial) :=
              mul_le_mul_of_nonneg_left hgeometric hdelta
            _ = delta ^ (round + 1) * badCount initial := by
              rw [pow_succ]
              ring
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinitial hadvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure initial) outcomeLaw advance bad failureBudget (by
      intro round active
      simpa [bad, badCount, advance] using hfailure round active) roundCount
  have hsize : ∀ stateFailure ∈
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).support,
      stateFailure.2 = false → stateFailure.1.card ≤ 2 * cutoff := by
    intro stateFailure hsupport hflag
    rcases hinvariantSupport roundCount stateFailure hsupport hflag with hstopped | hsmall | hgeometric
    · exact hstopped
    · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
        preferenceGap lower cutoff anchor stateFailure.1 hanchor
      exact (Nat.cast_le (α := ℝ)).mp (by simpa [badCount] using hsmall)
    · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
        preferenceGap lower cutoff anchor stateFailure.1 hanchor
      exact (Nat.cast_le (α := ℝ)).mp (by
        calc
          ((pruneBadArms preferenceGap lower anchor stateFailure.1).card : ℝ) =
              badCount stateFailure.1 := rfl
          _ ≤ delta ^ roundCount * badCount initial := hgeometric
          _ ≤ cutoff := by simpa [badCount] using htarget)
  have hequal : pmfProb
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
      (fun stateFailure => stateFailure.2 = false) =
      pmfProb
        (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, hsize stateFailure hsupport hflag⟩
    · exact fun h => h.1
  simpa only [freshStoppedPruneRoundsStateLaw, advance, bad, badCount] using hsuccess.trans_eq hequal

/--
The Lemma-15 `n⁻³` contraction tail for one scheduled round that Algorithm 2
actually executes, under the canonical tagged Bernoulli batch law.
-/
theorem canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper scheduleDelta contraction : ℝ)
    (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta scheduleDelta round) ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (hseparation : lower < upper)
    (hschedule : 0 < scheduleDelta) (hscheduleLeOne : scheduleDelta ≤ 1)
    (hcontraction : 0 < contraction) (hscheduleLeContraction : scheduleDelta ≤ contraction)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hcontractionLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ contraction) :
    pmfProb
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper scheduleDelta maxBatch hbudget round active)
      (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff
                (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget)
                round active outcome)).card : ℝ)) ≤
      1 / (Fintype.card Arm : ℝ) ^ 3 := by
  apply (pmfProb_le_of_imp _ _ _ ?_).trans
    (canonicalFreshPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
      preferenceGap hprobability roundCount anchor lower upper scheduleDelta contraction
      maxBatch cutoff hbudget round hround active hseparation hschedule hscheduleLeOne
      hcontraction hscheduleLeContraction hcard hcutoff hcontractionLower)
  intro outcome hbad
  rcases hbad with ⟨hrunning, hlarge, htooMany⟩
  refine ⟨hlarge, ?_⟩
  simpa [stoppedPruneAdvance, hrunning] using htooMany

/-- The strict Supplement Lemma 15 specialization. -/
theorem canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    pmfProb
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper delta maxBatch hbudget round active)
      (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff
                (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                round active outcome)).card : ℝ)) ≤
      1 / (Fintype.card Arm : ℝ) ^ 3 := by
  apply (pmfProb_le_of_imp _ _ _ ?_).trans
    (canonicalFreshPruneRound_contraction_failure_le_card_inv_cube
      preferenceGap hprobability roundCount anchor lower upper delta maxBatch cutoff hbudget
      round hround active hseparation hdelta hdeltaLeOne hcard hcutoff hdeltaLower)
  intro outcome hbad
  rcases hbad with ⟨hrunning, hlarge, htooMany⟩
  refine ⟨hlarge, ?_⟩
  simpa [stoppedPruneAdvance, hrunning] using htooMany

/--
Lemma 15's source `1 - n⁻²` size endpoint on the concrete finite stopped
execution.  Its failure budget is assigned only to scheduled executed rounds.
-/
theorem canonicalFreshStoppedPruneRounds_card_success_probability_ge_one_sub_card_inv_sq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb
        (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := by
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then 1 / (Fintype.card Arm : ℝ) ^ 3 else 1
  have hfailure : ∀ round active,
      pmfProb
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
          lower upper delta maxBatch hbudget round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧
            cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (stoppedPruneAdvance cutoff
                  (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                  round active outcome)).card : ℝ)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · simpa [failureBudget, hround] using
        (canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube
          preferenceGap hprobability roundCount anchor lower upper delta maxBatch cutoff hbudget
          round hround active hseparation hdelta hdeltaLeOne hcard hcutoff hdeltaLower)
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget round active)
          (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧
              cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
              delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                ((pruneBadArms preferenceGap lower anchor
                  (stoppedPruneAdvance cutoff
                    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                    round active outcome)).card : ℝ)))
  have hfresh := freshStoppedPruneRounds_card_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor initial delta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
    failureBudget roundCount hanchor hdelta.le hfailure htarget
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
    calc
      (∑ round ∈ Finset.range roundCount, failureBudget round) =
          ∑ round ∈ Finset.range roundCount, 1 / (Fintype.card Arm : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro round hround
            simp [failureBudget, Finset.mem_range.mp hround]
      _ = (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by simp
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hinvNonneg : 0 ≤ 1 / (Fintype.card Arm : ℝ) ^ 3 := by positivity
  have hsumLe : ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 := by
    rw [hsum]
    calc
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) ≤
          (Fintype.card Arm : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hroundCount
            · exact hinvNonneg
      _ = 1 / (Fintype.card Arm : ℝ) ^ 2 := by
            field_simp [ne_of_gt hcardPos]
  calc
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
          linarith
    _ ≤ pmfProb
        (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := hfresh

/--
Lemma 15's printed `1 - delta / 2` size endpoint on the actual stopped
execution in the source-normalized `delta ≤ 1 / 2` regime.
-/
theorem canonicalFreshStoppedPruneRounds_card_success_probability_ge_one_sub_delta_half_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := by
  have hcutoffPosReal : 0 < (cutoff : ℝ) :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have hcutoffPos : 0 < cutoff := by exact_mod_cast hcutoffPosReal
  have htarget := sourceLemma15_card_round_geometric_target preferenceGap lower anchor initial
    cutoff delta hcutoffPos hdelta.le hdeltaHalf
  have hcore := canonicalFreshStoppedPruneRounds_card_success_probability_ge_one_sub_card_inv_sq
    preferenceGap hprobability (Fintype.card Arm) anchor lower upper delta maxBatch cutoff hbudget
    initial hanchor hseparation hdelta (hdeltaHalf.trans (by norm_num)) hcard (le_refl _)
    hcutoff hdeltaLower htarget
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcutoffOne : 1 ≤ (cutoff : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hcutoffPos
  have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hdeltaTail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 2 := by
    have hscale : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Arm : ℝ))).mpr
      field_simp [ne_of_gt hcardPos]
      nlinarith [hcardTwo, hcutoffOne]
    calc
      1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := hscale
      _ = ((cutoff : ℝ) / (Fintype.card Arm : ℝ)) / 2 := by ring
      _ ≤ delta / 2 := by gcongr
  calc
    1 - delta / 2 ≤ 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 := by linarith
    _ ≤ _ := hcore

end FalahatgarEtAl2017MaxingRanking
