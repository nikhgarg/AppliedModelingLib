import ZhouChenLi2014OptimalPACMultipleArm.CanonicalFreshQuartileRounds

/-!
# State-dependent fresh QE batches

Algorithm 1 divides a round budget by the current active-set cardinality.
This extension of the tagged carrier therefore lets the fresh batch size
depend on the history-selected active set, while retaining one fixed finite
outcome type for adaptive-query composition.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

noncomputable section

/-- Read a state-dependent QE batch from the tagged adaptive outcome. -/
noncomputable def adaptiveBatchQuartileScore {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (sampleCount : ℕ → Finset Arm → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, ∀ active, sampleCount round active ≤ maxBatch)
    (round : ℕ) (active : Finset Arm)
    (outcome : canonicalFreshQuartileOutcome Arm maxBatch) (arm : Arm) : ℝ := by
  classical
  by_cases hround : round < roundCount
  · by_cases hsize : outcome.1.val = sampleCount round active
    · have hsizeFin : outcome.1 =
          ⟨sampleCount round active, Nat.lt_succ_of_le (hbudget round hround active)⟩ :=
        Fin.ext hsize
      let taggedActiveTable : Σ taggedActive : Finset Arm,
          taggedActive → Fin (sampleCount round active) → Bool :=
        cast (by rw [hsizeFin]) outcome.2
      by_cases hactive : taggedActiveTable.1 = active
      · let batchTable : active → Fin (sampleCount round active) → Bool :=
          cast (by rw [hactive]) taggedActiveTable.2
        exact quartileBernoulliBatchScore active (sampleCount round active) batchTable arm
      · exact 0
    · exact 0
  · exact 0

/-- State-dependent tagged scores agree with the active round's batch scores. -/
theorem adaptiveBatchQuartileScore_embed {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (sampleCount : ℕ → Finset Arm → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, ∀ active, sampleCount round active ≤ maxBatch)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (batchTable : active → Fin (sampleCount round active) → Bool) (arm : Arm) :
    adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget round active
      (canonicalFreshQuartileEmbed maxBatch (sampleCount round active) (hbudget round hround active)
        active batchTable) arm =
      quartileBernoulliBatchScore active (sampleCount round active) batchTable arm := by
  simp [adaptiveBatchQuartileScore, hround, canonicalFreshQuartileEmbed]

/-- The fresh state-dependent batch law used by a QE round of Algorithm 1. -/
noncomputable def adaptiveBatchQuartileOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (sampleCount : ℕ → Finset Arm → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, ∀ active, sampleCount round active ≤ maxBatch) :
    AdaptiveOutcomeKernel (Finset Arm) (canonicalFreshQuartileOutcome Arm maxBatch) :=
  fun round active => if hround : round < roundCount then
    (quartileBernoulliBatchLaw mean hmean active (sampleCount round active)).map
      (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
        (hbudget round hround active) active)
  else PMF.pure ⟨⟨0, Nat.succ_pos _⟩, ⟨∅, fun _ sample => Fin.elim0 sample⟩⟩

/--
The source-shaped one-round QE tail bound remains valid when the batch size is
selected from the current active state before the fresh batch is drawn.
-/
theorem adaptiveBatchQuartileRound_failure_probability_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (sampleCount : ℕ → Finset Arm → ℕ) (maxBatch : ℕ)
    (hbudget : ∀ round < roundCount, ∀ active, sampleCount round active ≤ maxBatch)
    (error : ℕ → ℝ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hcount : 0 < sampleCount round active) (herror : 0 ≤ error round) (t : ℝ) (ht : 0 ≤ t) :
    pmfProbClassical
        (adaptiveBatchQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
          round active)
        (quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget) round active) ≤
      Real.exp (-((sampleCount round active : ℝ) * error round) ^ 2 /
        (2 * (sampleCount round active : ℝ) * (1 / 4 : ℝ))) +
      Real.exp (-t * (quartileSurvivorCount active.card : ℝ) +
        (active.card : ℝ) * ((Real.exp t - 1) *
          Real.exp (-((sampleCount round active : ℝ) * error round) ^ 2 /
            (2 * (sampleCount round active : ℝ) * (1 / 4 : ℝ))))) := by
  classical
  let reference : active := quartileRoundMeanMaximizer mean active hactive
  have hmaximum : ∀ competitor : active, mean competitor.val ≤ mean reference.val := by
    intro competitor
    exact mean_le_quartileRoundMeanMaximizer mean active hactive competitor
  have hevent : ∀ batchTable : active → Fin (sampleCount round active) → Bool,
      quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
            (hbudget round hround active) active batchTable) ↔
        ¬ ∃ survivor, survivor ∈ quartileEliminationFromBatch active (sampleCount round active)
            batchTable ∧ mean reference.val - 2 * error round ≤ mean survivor := by
    intro batchTable
    unfold quartileRoundBad
    rw [dif_pos hactive]
    change (¬ ∃ survivor, survivor ∈ quartileEliminationSurvivors active
        (adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
            (hbudget round hround active) active batchTable)) ∧
        mean reference.val - 2 * error round ≤ mean survivor) ↔ _
    rw [show adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
            (hbudget round hround active) active batchTable) =
          quartileBernoulliBatchScore active (sampleCount round active) batchTable by
            funext arm
            exact adaptiveBatchQuartileScore_embed roundCount sampleCount maxBatch hbudget
              round hround active batchTable arm]
    rfl
  have heventSet :
      {batchTable | quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount sampleCount maxBatch hbudget) round active
          (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
            (hbudget round hround active) active batchTable)} =
        {batchTable | ¬ ∃ survivor,
          survivor ∈ quartileEliminationFromBatch active (sampleCount round active) batchTable ∧
          mean reference.val - 2 * error round ≤ mean survivor} := by
    ext batchTable
    exact hevent batchTable
  rw [show adaptiveBatchQuartileOutcomeLaw mean hmean roundCount sampleCount maxBatch hbudget
      round active =
      (quartileBernoulliBatchLaw mean hmean active (sampleCount round active)).map
        (canonicalFreshQuartileEmbed maxBatch (sampleCount round active)
          (hbudget round hround active) active) by
          simp [adaptiveBatchQuartileOutcomeLaw, hround]]
  unfold pmfProbClassical
  rw [pmfProb_map]
  rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
  rw [heventSet]
  exact quartileEliminationFromBatch_no_near_maximum_probability mean hmean active reference
    hmaximum (sampleCount round active) hcount (error round) t herror ht

end

end ZhouChenLi2014OptimalPACMultipleArm
