import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction
import FalahatgarEtAl2017MaxingRanking.AdaptiveFreshSeqEliminate

/-!
# Fresh adaptive Prune rounds

Lemma 15 selects its next active set from the preceding Prune history, while
the comparison batches for that round are fresh.  This module gives the
finite-PMF composition argument: uniform conditional contraction bounds can
be union-bounded over those history-selected rounds, and their deterministic
geometric recurrence yields the source size conclusion.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The finite execution law for Prune rounds with fresh, history-selected round
outcomes.  The Boolean coordinate records whether a bad-cardinality
contraction occurred in any completed round.
-/
noncomputable def freshPruneRoundsStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (Finset Arm × Bool) := by
  classical
  exact adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
    (fun round active outcome => pruneRound active (decision round active outcome))
    (fun round active outcome =>
      cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (pruneRound active (decision round active outcome))).card : ℝ))
    roundCount

/--
Finite-PMF event probabilities may be compared using an equivalence only on
the law's support; values outside it have zero mass.
-/
theorem pmfProb_eq_of_support_iff
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    [DecidablePred first] [DecidablePred second]
    (hiff : ∀ outcome ∈ law.support, first outcome ↔ second outcome) :
    pmfProb law first = pmfProb law second := by
  classical
  unfold pmfProb pmfExp
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hsupport : outcome ∈ law.support
  · simp [hiff outcome hsupport]
  · have hzero : law outcome = 0 := by
      by_contra hnonzero
      exact hsupport ((law.mem_support_iff outcome).mpr hnonzero)
    simp [hzero]

/--
The Lemma 15 size conclusion for a finite fresh-round execution.  A
historywise PMF tail bound for each new round is enough: on the event that no
round violates its contraction, the threshold-nonbetter population follows
the deterministic geometric recurrence and the good anchor bounds the final
active set by `2 * cutoff`.
-/
theorem freshPruneRounds_card_success_probability_ge_one_sub_sum
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
        cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active (decision round active outcome))).card : ℝ)) ≤
        failureBudget round)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
          decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := by
  classical
  let badCount : Finset Arm → ℝ := fun active =>
    ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := fun round active outcome =>
    pruneRound active (decision round active outcome)
  let bad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    cutoff < badCount active ∧ delta * badCount active < badCount (advance round active outcome)
  let invariant : ℕ → Finset Arm → Bool → Prop := fun round active flag =>
    flag = false → badCount active ≤ cutoff ∨
      badCount active ≤ delta ^ round * badCount initial
  have hinitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    right
    simp [badCount] at hactive ⊢
    subst active
    simp
  have hbadMonotone : ∀ round active outcome,
      badCount (advance round active outcome) ≤ badCount active := by
    intro round active outcome
    dsimp [badCount, advance]
    exact_mod_cast Finset.card_le_card
      (pruneBadArms_subset_of_subset preferenceGap lower anchor
        (pruneRound_subset active (decision round active outcome)))
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
    rcases hinvariant hflag with hsmall | hgeometric
    · left
      exact (hbadMonotone round active outcome).trans hsmall
    · by_cases hsmall : badCount active ≤ cutoff
      · left
        exact (hbadMonotone round active outcome).trans hsmall
      · right
        have hcontract : badCount (advance round active outcome) ≤
            delta * badCount active := by
              apply le_of_not_gt
              intro htooMany
              exact hnotBad ⟨lt_of_not_ge hsmall, htooMany⟩
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
    rcases hinvariantSupport roundCount stateFailure hsupport hflag with hsmall | hgeometric
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
  simpa only [freshPruneRoundsStateLaw, advance, bad, badCount] using hsuccess.trans_eq hequal

end FalahatgarEtAl2017MaxingRanking
