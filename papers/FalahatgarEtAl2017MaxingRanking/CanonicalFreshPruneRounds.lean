import FalahatgarEtAl2017MaxingRanking.CanonicalFullPruneNumerics
import FalahatgarEtAl2017MaxingRanking.FreshPruneRounds

/-!
# Canonical fresh adaptive Prune rounds

This is the concrete finite coupling behind Lemma 15.  At each history-selected
round it draws fresh Bernoulli comparison batches for all arms, and then Prune
reads only the current active subset.  The unused coordinates make the outcome
type fixed across the varying source batch sizes without changing any sampled
comparison used by the algorithm.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- A tagged full-arm batch, whose tag records the finite batch size in use. -/
abbrev canonicalFreshPruneTaggedOutcome (Arm : Type*) [Fintype Arm] (maxBatch : ℕ) :=
  Σ batchSize : Fin (maxBatch + 1),
    (↑(Finset.univ : Finset Arm) → Fin batchSize.val → Bool)

noncomputable section

noncomputable instance canonicalFreshPruneTaggedOutcomeFintype
    (Arm : Type*) [Fintype Arm] (maxBatch : ℕ) :
    Fintype (canonicalFreshPruneTaggedOutcome Arm maxBatch) :=
  Fintype.ofFinite _

/-- Embed a full-arm batch at its actual finite size into the tagged outcome type. -/
noncomputable def canonicalFreshPruneTaggedEmbed {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (maxBatch batchSize : ℕ) (hbatch : batchSize ≤ maxBatch)
    (table : ↑(Finset.univ : Finset Arm) → Fin batchSize → Bool) :
    canonicalFreshPruneTaggedOutcome Arm maxBatch :=
  ⟨⟨batchSize, Nat.lt_succ_of_le hbatch⟩, table⟩

/-- Read the source Prune decision when a tagged outcome has the expected batch size. -/
noncomputable def canonicalFreshPruneTaggedDecision {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (maxBatch : ℕ) (lower upper eta : ℝ)
    (hbudget : fixedSampleBudget lower upper eta ≤ maxBatch)
    (outcome : canonicalFreshPruneTaggedOutcome Arm maxBatch) (arm : Arm) : CompareDecision :=
  if htag : outcome.1.val = fixedSampleBudget lower upper eta then
    have htagFin : outcome.1 = ⟨fixedSampleBudget lower upper eta, Nat.lt_succ_of_le hbudget⟩ :=
      Fin.ext htag
    let batchTable : ↑(Finset.univ : Finset Arm) →
        Fin (fixedSampleBudget lower upper eta) → Bool :=
      cast (by rw [htagFin]) outcome.2
    canonicalFullPruneRoundDecision lower upper eta batchTable arm
  else .lower

/-- The tagged decision reduces to the ordinary full-arm decision on an embedded batch. -/
theorem canonicalFreshPruneTaggedDecision_embed {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (maxBatch : ℕ) (lower upper eta : ℝ)
    (hbudget : fixedSampleBudget lower upper eta ≤ maxBatch)
    (table : ↑(Finset.univ : Finset Arm) → Fin (fixedSampleBudget lower upper eta) → Bool)
    (arm : Arm) :
    canonicalFreshPruneTaggedDecision maxBatch lower upper eta hbudget
      (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta) hbudget table) arm =
      canonicalFullPruneRoundDecision lower upper eta table arm := by
  simp [canonicalFreshPruneTaggedDecision, canonicalFreshPruneTaggedEmbed]

/-- The fresh source law at a round, with a harmless zero-size default outside the schedule. -/
noncomputable def canonicalFreshPruneOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch) :
    AdaptiveOutcomeKernel (Finset Arm) (canonicalFreshPruneTaggedOutcome Arm maxBatch) :=
  fun round _ => if hround : round < roundCount then
    (canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
      (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))).map
      (canonicalFreshPruneTaggedEmbed maxBatch
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))
        (hbudget round hround))
  else PMF.pure ⟨⟨0, Nat.succ_pos _⟩, fun _ sample => Fin.elim0 sample⟩

/-- The scheduled source decision reads a tagged fresh batch at its round. -/
noncomputable def canonicalFreshPruneDecision {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (roundCount : ℕ) (lower upper delta : ℝ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (round : ℕ) (_active : Finset Arm) (outcome : canonicalFreshPruneTaggedOutcome Arm maxBatch)
    (arm : Arm) : CompareDecision :=
  if hround : round < roundCount then
    canonicalFreshPruneTaggedDecision maxBatch lower upper (adaptivePruneRoundDelta delta round)
      (hbudget round hround) outcome arm
  else .lower

/-- On a scheduled embedded batch, the tagged decision is exactly the source decision. -/
theorem canonicalFreshPruneDecision_embed {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm] (roundCount : ℕ) (lower upper delta : ℝ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (table : ↑(Finset.univ : Finset Arm) →
      Fin (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round)) → Bool)
    (arm : Arm) :
    canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget round active
      (canonicalFreshPruneTaggedEmbed maxBatch
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))
        (hbudget round hround) table) arm =
      canonicalFullPruneRoundDecision lower upper (adaptivePruneRoundDelta delta round)
        table arm := by
  simp [canonicalFreshPruneDecision, hround, canonicalFreshPruneTaggedDecision_embed]

/--
At a scheduled source Prune round, an arm meeting the upper Compare threshold
is removed with probability at most that round's allocated confidence.
The probability is for the tagged fresh law used by the stopped execution.
-/
theorem canonicalFreshPruneRound_upper_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor : Arm) (lower upper delta : ℝ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm) (arm : Arm)
    (hgap : upper ≤ preferenceGap arm anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    pmfProb
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper delta maxBatch hbudget round active)
      (fun outcome =>
        canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget round active
          outcome arm ≠ .upper) ≤ adaptivePruneRoundDelta delta round := by
  let eta : ℝ := adaptivePruneRoundDelta delta round
  have hetaParts := adaptivePruneRoundDelta_pos_le_delta_div_four delta hdelta round
  have heta : 0 < eta := by simpa [eta] using hetaParts.1
  have hetaLeOne : eta ≤ 1 := by
    have hetaBound : eta ≤ delta / 4 := by simpa [eta] using hetaParts.2
    nlinarith
  unfold canonicalFreshPruneOutcomeLaw
  rw [dif_pos hround, pmfProb_map]
  let fullLaw := canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
    (fixedSampleBudget lower upper eta)
  calc
    pmfProb fullLaw (fun table =>
        canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget round active
          (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
            (hbudget round hround) table) arm ≠ .upper) ≤
        pmfProb fullLaw (fun table =>
          canonicalFullPruneRoundDecision lower upper eta table arm ≠ .upper) := by
            apply pmfProb_le_of_imp
            intro table hfailure
            have hdecision := canonicalFreshPruneDecision_embed roundCount lower upper delta
              maxBatch hbudget round hround active table arm
            rw [hdecision] at hfailure
            exact hfailure
    _ = fullLaw.toMeasure.real {table |
        canonicalFullPruneRoundDecision lower upper eta table arm ≠ .upper} := by
          rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
    _ ≤ eta := by
      simpa [fullLaw] using canonicalFullPruneRound_upper_failure_probability
        preferenceGap hprobability anchor arm lower upper eta hgap hseparation heta hetaLeOne
    _ = adaptivePruneRoundDelta delta round := rfl

/--
The inverse-cubic contraction tail when the geometric analysis factor may be
larger than the confidence used by the actual Prune schedule.
-/
theorem canonicalFreshPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
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
      (fun outcome => cutoff <
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (pruneRound active
              (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                hbudget round active outcome))).card : ℝ)) ≤
      1 / (Fintype.card Arm : ℝ) ^ 3 := by
  let eta : ℝ := adaptivePruneRoundDelta scheduleDelta round
  have hetaParts := adaptivePruneRoundDelta_pos_le_delta_div_four scheduleDelta hschedule round
  have heta : 0 < eta := by simpa [eta] using hetaParts.1
  have hetaScheduleBound : eta ≤ scheduleDelta / 4 := by simpa [eta] using hetaParts.2
  have hetaBound : eta ≤ contraction / 4 := by
    exact hetaScheduleBound.trans
      (div_le_div_of_nonneg_right hscheduleLeContraction (by norm_num))
  have hetaLeOne : eta ≤ 1 := by nlinarith
  unfold canonicalFreshPruneOutcomeLaw
  rw [dif_pos hround, pmfProb_map]
  let fullLaw := canonicalPruneRoundBatchLaw preferenceGap hprobability Finset.univ anchor
    (fixedSampleBudget lower upper eta)
  have htail := canonicalFullPruneRound_badSurvivor_contraction_failure_le_exp
    preferenceGap hprobability active anchor lower upper contraction eta hseparation hcontraction
    heta hetaLeOne hetaBound
  have hnumeric := exp_neg_half_mul_le_card_inv_cube_of_sourceLemma5_sqrt
    (Fintype.card Arm) cutoff contraction hcard hcutoff hcontractionLower
  by_cases hlarge : cutoff <
      ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  · calc
      pmfProb fullLaw (fun table => cutoff <
          ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                  hbudget round active
                  (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                    (hbudget round hround) table)))).card : ℝ)) ≤
          pmfProb fullLaw (fun table =>
            contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (pruneRound active
                  (canonicalFullPruneRoundDecision lower upper eta table))).card : ℝ)) := by
            apply pmfProb_le_of_imp
            intro table hbad
            have hdecision :
                canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch hbudget
                  round active
                  (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                    (hbudget round hround) table) =
                  canonicalFullPruneRoundDecision lower upper eta table := by
              funext arm
              exact canonicalFreshPruneDecision_embed roundCount lower upper scheduleDelta maxBatch
                hbudget round hround active table arm
            simpa only [hdecision] using hbad.2
      _ = fullLaw.toMeasure.real {table |
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFullPruneRoundDecision lower upper eta table))).card : ℝ)} := by
            rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
      _ ≤ Real.exp (-((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
            contraction / 2) := by
            simpa [fullLaw, eta, pruneBadArms] using htail
      _ ≤ Real.exp (-(cutoff : ℝ) * contraction / 2) := by
            apply Real.exp_le_exp.mpr
            have hlargeFilter : (cutoff : ℝ) <
                ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) := by
              simpa [pruneBadArms] using hlarge
            nlinarith [hlargeFilter, hcontraction]
      _ ≤ 1 / (Fintype.card Arm : ℝ) ^ 3 := hnumeric
  · have hempty : ∀ table,
        ¬ (cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                  hbudget round active
                  (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                    (hbudget round hround) table)))).card : ℝ)) := by
          intro table hbad
          exact hlarge hbad.1
    change pmfProb fullLaw (fun table => cutoff <
      ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (pruneRound active
              (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                hbudget round active
                (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                  (hbudget round hround) table)))).card : ℝ)) ≤
      1 / (Fintype.card Arm : ℝ) ^ 3
    have hzero : pmfProb fullLaw (fun table => cutoff <
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                  hbudget round active
                  (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                    (hbudget round hround) table)))).card : ℝ)) = 0 := by
      unfold pmfProb pmfExp
      apply Finset.sum_eq_zero
      intro table _
      by_cases hevent : cutoff <
          ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          contraction * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFreshPruneDecision roundCount lower upper scheduleDelta maxBatch
                  hbudget round active
                  (canonicalFreshPruneTaggedEmbed maxBatch (fixedSampleBudget lower upper eta)
                    (hbudget round hround) table)))).card : ℝ)
      · exact (hempty table hevent).elim
      · dsimp
        rw [if_neg hevent]
        ring
    rw [hzero]
    positivity

/-- The strict Supplement Lemma 15 specialization. -/
theorem canonicalFreshPruneRound_contraction_failure_le_card_inv_cube
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
      (fun outcome => cutoff <
        ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (pruneRound active
              (canonicalFreshPruneDecision roundCount lower upper delta maxBatch
                hbudget round active outcome))).card : ℝ)) ≤
      1 / (Fintype.card Arm : ℝ) ^ 3 := by
  exact canonicalFreshPruneRound_contraction_failure_le_card_inv_cube_of_schedule_le
    preferenceGap hprobability roundCount anchor lower upper delta delta maxBatch cutoff hbudget
      round hround active hseparation hdelta hdeltaLeOne hdelta (le_refl _) hcard hcutoff.le
      hdeltaLower

/--
Lemma 15's concrete finite fresh-round size probability, conditional only on
its source geometric round target and an explicit finite cap on scheduled
batch sizes.  The source's `n⁻³` tail is summed over at most `n` rounds.
-/
theorem canonicalFreshPruneRounds_card_success_probability_ge_one_sub_card_inv_sq
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
        (freshPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
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
        (fun outcome => cutoff <
          ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (pruneRound active
                (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                  round active outcome))).card : ℝ)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · simpa [failureBudget, hround] using
        (canonicalFreshPruneRound_contraction_failure_le_card_inv_cube preferenceGap hprobability
          roundCount anchor lower upper delta maxBatch cutoff hbudget round hround active
          hseparation hdelta hdeltaLeOne hcard hcutoff hdeltaLower)
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget round active)
          (fun outcome => cutoff <
            ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (pruneRound active
                  (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                    round active outcome))).card : ℝ)))
  have hfresh := freshPruneRounds_card_success_probability_ge_one_sub_sum
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
        (freshPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff) := hfresh

/--
Lemma 15's multi-round size probability in the source-normalized `delta ≤ 1 / 2`
regime.  The source permits this normalization when its requested confidence
parameter is larger; the remaining Lemma 15 work is its comparison-cost bound.
-/
theorem canonicalFreshPruneRounds_card_success_probability_ge_one_sub_delta_half_of_sourceLemma15
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
        (freshPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
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
  have hcore := canonicalFreshPruneRounds_card_success_probability_ge_one_sub_card_inv_sq
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

end

end FalahatgarEtAl2017MaxingRanking
