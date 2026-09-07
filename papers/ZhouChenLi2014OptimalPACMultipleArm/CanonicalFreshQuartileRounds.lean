import ZhouChenLi2014OptimalPACMultipleArm.FreshQuartileRounds

/-!
# Canonical fresh outcomes for adaptive QE rounds

The abstract fresh-round theorem is instantiated by a tagged outcome type.
Each history-selected active set receives exactly one newly drawn product
batch at that round's scheduled size; the tag embeds varying finite batch
sizes into one fixed finite outcome type.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- A QE outcome tagged with both its finite batch size and its active set. -/
abbrev canonicalFreshQuartileOutcome (Arm : Type*) [Fintype Arm] (maxBatch : ℕ) :=
  Σ batchSize : Fin (maxBatch + 1),
    Σ active : Finset Arm, active → Fin batchSize.val → Bool

noncomputable section

noncomputable instance canonicalFreshQuartileOutcomeFintype
    (Arm : Type*) [Fintype Arm] (maxBatch : ℕ) :
    Fintype (canonicalFreshQuartileOutcome Arm maxBatch) :=
  Fintype.ofFinite _

noncomputable instance canonicalFreshQuartileOutcomeDecidableEq
    (Arm : Type*) [Fintype Arm] (maxBatch : ℕ) :
    DecidableEq (canonicalFreshQuartileOutcome Arm maxBatch) :=
  Classical.decEq _

/-- Embed the active round's exact batch into the fixed tagged outcome type. -/
noncomputable def canonicalFreshQuartileEmbed {Arm : Type*} [Fintype Arm]
    (maxBatch batchSize : ℕ) (hbatch : batchSize ≤ maxBatch) (active : Finset Arm)
    (batchTable : active → Fin batchSize → Bool) :
    canonicalFreshQuartileOutcome Arm maxBatch :=
  ⟨⟨batchSize, Nat.lt_succ_of_le hbatch⟩, ⟨active, batchTable⟩⟩

/--
Read the empirical-score table from a tagged outcome when its size and active
set agree with the scheduled round; a mismatched tag is assigned zero scores.
-/
noncomputable def canonicalFreshQuartileScore {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch)
    (round : ℕ) (active : Finset Arm)
    (outcome : canonicalFreshQuartileOutcome Arm maxBatch) (arm : Arm) : ℝ := by
  classical
  by_cases hround : round < roundCount
  · by_cases hsize : outcome.1.val = sampleCount round
    · have hsizeFin : outcome.1 =
          ⟨sampleCount round, Nat.lt_succ_of_le (hbudget round hround)⟩ := Fin.ext hsize
      let taggedActiveTable : Σ taggedActive : Finset Arm,
          taggedActive → Fin (sampleCount round) → Bool :=
        cast (by rw [hsizeFin]) outcome.2
      by_cases hactive : taggedActiveTable.1 = active
      · let batchTable : active → Fin (sampleCount round) → Bool :=
          cast (by rw [hactive]) taggedActiveTable.2
        exact quartileBernoulliBatchScore active (sampleCount round) batchTable arm
      · exact 0
    · exact 0
  · exact 0

/-- The tagged score reduces to the ordinary batch score on an embedded outcome. -/
theorem canonicalFreshQuartileScore_embed {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (batchTable : active → Fin (sampleCount round) → Bool) (arm : Arm) :
    canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget round active
      (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
        active batchTable) arm =
      quartileBernoulliBatchScore active (sampleCount round) batchTable arm := by
  simp [canonicalFreshQuartileScore, hround, canonicalFreshQuartileEmbed]

/--
The fresh outcome kernel for an adaptive QE execution.  Outside the finite
schedule it returns a harmless empty, zero-size tagged outcome.
-/
noncomputable def canonicalFreshQuartileOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch) :
    AdaptiveOutcomeKernel (Finset Arm) (canonicalFreshQuartileOutcome Arm maxBatch) :=
  fun round active => if hround : round < roundCount then
    (quartileBernoulliBatchLaw mean hmean active (sampleCount round)).map
      (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround) active)
  else PMF.pure ⟨⟨0, Nat.succ_pos _⟩, ⟨∅, fun _ sample => Fin.elim0 sample⟩⟩

end

/--
At a scheduled, nonempty QE round, the concrete tagged outcome kernel has the
same bad-event probability as the fresh product batch used in the one-round
tail theorem.
-/
theorem canonicalFreshQuartileRound_failure_probability_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch)
    (error : ℕ → ℝ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hcount : 0 < sampleCount round) (herror : 0 ≤ error round) (t : ℝ) (ht : 0 ≤ t) :
    pmfProbClassical
        (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
          round active)
        (quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active) ≤
      Real.exp (-((sampleCount round : ℝ) * error round) ^ 2 /
        (2 * (sampleCount round : ℝ) * (1 / 4 : ℝ))) +
      Real.exp (-t * (quartileSurvivorCount active.card : ℝ) +
        (active.card : ℝ) * ((Real.exp t - 1) *
          Real.exp (-((sampleCount round : ℝ) * error round) ^ 2 /
            (2 * (sampleCount round : ℝ) * (1 / 4 : ℝ))))) := by
  classical
  let reference : active := quartileRoundMeanMaximizer mean active hactive
  have hmaximum : ∀ competitor : active, mean competitor.val ≤ mean reference.val := by
    intro competitor
    exact mean_le_quartileRoundMeanMaximizer mean active hactive competitor
  have hevent : ∀ batchTable : active → Fin (sampleCount round) → Bool,
      quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable) ↔
        ¬ ∃ survivor, survivor ∈ quartileEliminationFromBatch active (sampleCount round)
            batchTable ∧ mean reference.val - 2 * error round ≤ mean survivor := by
    intro batchTable
    unfold quartileRoundBad
    rw [dif_pos hactive]
    change (¬ ∃ survivor, survivor ∈ quartileEliminationSurvivors active
        (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable)) ∧
        mean reference.val - 2 * error round ≤ mean survivor) ↔ _
    rw [show canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable) =
          quartileBernoulliBatchScore active (sampleCount round) batchTable by
            funext arm
            exact canonicalFreshQuartileScore_embed roundCount sampleCount maxBatch hbudget
              round hround active batchTable arm]
    rfl
  have heventSet :
      {batchTable | quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable)} =
        {batchTable | ¬ ∃ survivor,
          survivor ∈ quartileEliminationFromBatch active (sampleCount round) batchTable ∧
          mean reference.val - 2 * error round ≤ mean survivor} := by
    ext batchTable
    exact hevent batchTable
  rw [show canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
      round active =
      (quartileBernoulliBatchLaw mean hmean active (sampleCount round)).map
        (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround) active) by
          simp [canonicalFreshQuartileOutcomeLaw, hround]]
  unfold pmfProbClassical
  rw [pmfProb_map]
  rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
  rw [heventSet]
  exact quartileEliminationFromBatch_no_near_maximum_probability mean hmean active reference
    hmaximum (sampleCount round) hcount (error round) t herror ht

/--
The same concrete tagged QE round also satisfies the simpler all-arms
uniform-estimation bound.  This less sharp form is convenient for explicit
finite sample schedules.
-/
theorem canonicalFreshQuartileRound_uniform_failure_probability_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch)
    (error : ℕ → ℝ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hcount : 0 < sampleCount round) (herror : 0 ≤ error round) :
    pmfProbClassical
        (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
          round active)
        (quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active) ≤
      (active.card : ℝ) * 2 *
        Real.exp (-((sampleCount round : ℝ) * error round) ^ 2 /
          (2 * (sampleCount round : ℝ) * (1 / 4 : ℝ))) := by
  classical
  let reference : active := quartileRoundMeanMaximizer mean active hactive
  have hevent : ∀ batchTable : active → Fin (sampleCount round) → Bool,
      quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable) ↔
        ¬ ∃ survivor, survivor ∈ quartileEliminationFromBatch active (sampleCount round)
            batchTable ∧ mean reference.val - 2 * error round ≤ mean survivor := by
    intro batchTable
    unfold quartileRoundBad
    rw [dif_pos hactive]
    change (¬ ∃ survivor, survivor ∈ quartileEliminationSurvivors active
        (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable)) ∧
        mean reference.val - 2 * error round ≤ mean survivor) ↔ _
    rw [show canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable) =
          quartileBernoulliBatchScore active (sampleCount round) batchTable by
            funext arm
            exact canonicalFreshQuartileScore_embed roundCount sampleCount maxBatch hbudget
              round hround active batchTable arm]
    rfl
  have heventSet :
      {batchTable | quartileRoundBad mean error
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround)
            active batchTable)} =
        {batchTable | ¬ ∃ survivor,
          survivor ∈ quartileEliminationFromBatch active (sampleCount round) batchTable ∧
          mean reference.val - 2 * error round ≤ mean survivor} := by
    ext batchTable
    exact hevent batchTable
  rw [show canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
      round active =
      (quartileBernoulliBatchLaw mean hmean active (sampleCount round)).map
        (canonicalFreshQuartileEmbed maxBatch (sampleCount round) (hbudget round hround) active) by
          simp [canonicalFreshQuartileOutcomeLaw, hround]]
  unfold pmfProbClassical
  rw [pmfProb_map]
  rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
  rw [heventSet]
  exact quartileEliminationFromBatch_no_near_reference_probability_of_uniformEstimate
    mean hmean active reference (sampleCount round) hcount (error round) herror

/-- The explicit source-shaped upper bound for one concrete QE round. -/
noncomputable def canonicalFreshQuartileRoundFailureBound
    {Arm : Type*} (sampleCount : ℕ → ℕ) (error t : ℕ → ℝ)
    (round : ℕ) (active : Finset Arm) : ℝ :=
  Real.exp (-((sampleCount round : ℝ) * error round) ^ 2 /
    (2 * (sampleCount round : ℝ) * (1 / 4 : ℝ))) +
  Real.exp (-t round * (quartileSurvivorCount active.card : ℝ) +
    (active.card : ℝ) * ((Real.exp (t round) - 1) *
      Real.exp (-((sampleCount round : ℝ) * error round) ^ 2 /
        (2 * (sampleCount round : ℝ) * (1 / 4 : ℝ)))))

/--
The concrete tagged-batch kernel satisfies the abstract fresh-round theorem
whenever a scheduled per-round budget dominates its explicit product-batch
tail bound.  The condition is needed only for nonempty active sets: the QE
bad event is definitionally false on an empty state.
-/
theorem canonicalFreshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (error t : ℕ → ℝ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (roundCount : ℕ) (sampleCount : ℕ → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, sampleCount round ≤ maxBatch)
    (hcount : ∀ round < roundCount, 0 < sampleCount round)
    (herror : ∀ round < roundCount, 0 ≤ error round)
    (ht : ∀ round < roundCount, 0 ≤ t round)
    (failureBudget : ℕ → ℝ) (hfailureBudgetNonneg : ∀ round < roundCount,
      0 ≤ failureBudget round)
    (hfailureBudget : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty →
      canonicalFreshQuartileRoundFailureBound sampleCount error t round active ≤
        failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget)
          (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  have hgeneric := freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum
    mean error initial hinitial
    (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget)
    (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget)
    (fun round => if round < roundCount then failureBudget round else 1) roundCount (by
      intro round active
      by_cases hround : round < roundCount
      · change pmfProbClassical
            (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch
              hbudget round active)
            (quartileRoundBad mean error
              (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget)
              round active) ≤
            (if round < roundCount then failureBudget round else 1)
        rw [if_pos hround]
        by_cases hactive : active.Nonempty
        · calc
            pmfProbClassical
                (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch
                  hbudget round active)
                (quartileRoundBad mean error
                  (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget)
                  round active) ≤
                canonicalFreshQuartileRoundFailureBound sampleCount error t round active := by
                  exact canonicalFreshQuartileRound_failure_probability_le mean hmean roundCount
                    sampleCount maxBatch hbudget error round hround active hactive
                    (hcount round hround) (herror round hround) (t round) (ht round hround)
            _ ≤ failureBudget round := hfailureBudget round hround active hactive
        · simpa [pmfProbClassical, pmfProb, quartileRoundBad, hactive] using
            hfailureBudgetNonneg round hround
      · change pmfProbClassical
            (canonicalFreshQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch
              hbudget round active)
            (quartileRoundBad mean error
              (canonicalFreshQuartileScore roundCount sampleCount maxBatch hbudget)
              round active) ≤
            (if round < roundCount then failureBudget round else 1)
        rw [if_neg hround]
        unfold pmfProbClassical
        exact pmfProb_le_one _ _)
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      ∑ round ∈ Finset.range roundCount,
        (if round < roundCount then failureBudget round else 1) := by
    apply Finset.sum_congr rfl
    intro round hround
    rw [if_pos (Finset.mem_range.mp hround)]
  calc
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round =
        1 - ∑ round ∈ Finset.range roundCount,
          (if round < roundCount then failureBudget round else 1) := by rw [hsum]
    _ ≤ _ := hgeneric

end ZhouChenLi2014OptimalPACMultipleArm
