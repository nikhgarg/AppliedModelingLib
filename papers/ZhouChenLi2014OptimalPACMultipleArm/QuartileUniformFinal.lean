import ZhouChenLi2014OptimalPACMultipleArm.QuartileFinalComposition
import ZhouChenLi2014OptimalPACMultipleArm.UniformBudget
import ZhouChenLi2014OptimalPACMultipleArm.UniformBatchPolicy

/-!
# Concrete uniform final stage after Quartile-Elimination

The final uniform batch is tagged with the history-selected active set.  This
gives one fixed finite outcome carrier while retaining the exact conditional
Bernoulli product law on the active subtype.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The source supplement's ceiling final-batch count for a particular active set. -/
noncomputable def quartileUniformFinalSampleCount
    {Arm : Type*} [Fintype Arm] (epsilon delta : ℝ) (active : Finset Arm) : ℕ :=
  uniformBernoulliBatchSampleBudget (Fintype.card active) epsilon delta

/-- A fixed finite cap for the number of final-stage pulls over every possible
survivor set.  It is a finite maximum, not an asymptotic replacement of the
history-selected final allocation. -/
noncomputable def quartileUniformFinalMaxPullBudget
    (Arm : Type*) [Fintype Arm] (epsilon delta : ℝ) : ℕ :=
  (Finset.univ : Finset (Finset Arm)).sup
    (fun active => Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)))

/-- The final-batch cap over the source's reachable terminal sets only.  QE
stops with at most three surviving arms, so this is the resource cap relevant
to the source algorithm; `quartileUniformFinalMaxPullBudget` above remains
the separate fixed-horizon cap needed by the generic replay interface. -/
noncomputable def quartileUniformFinalTerminalMaxPullBudget
    (Arm : Type*) [Fintype Arm] (epsilon delta : ℝ) : ℕ :=
  ((Finset.univ : Finset (Finset Arm)).filter (fun active => active.card ≤ 3)).sup
    (fun active => Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)))

/-- A cardinality-only cap for the source final batch.  It is the maximum of
the four possible costs for terminal set sizes zero through three and therefore
does not grow with the original number of arms. -/
noncomputable def quartileUniformFinalThreeArmPullBudget
    (epsilon delta : ℝ) : ℕ :=
  (Finset.range 4).sup
    (fun armCount => armCount * uniformBernoulliBatchSampleBudget armCount epsilon delta)

/-- Every survivor-specific final replay fits within the finite global cap. -/
theorem quartileUniformFinalPullBudget_le_max
    {Arm : Type*} [Fintype Arm] (epsilon delta : ℝ) (active : Finset Arm) :
    Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) ≤
      quartileUniformFinalMaxPullBudget Arm epsilon delta := by
  unfold quartileUniformFinalMaxPullBudget
  exact Finset.le_sup (s := (Finset.univ : Finset (Finset Arm)))
    (f := fun candidate : Finset Arm =>
      Fintype.card (UniformBatchCoordinate candidate
        (quartileUniformFinalSampleCount epsilon delta candidate)))
    (Finset.mem_univ active)

/-- Every source-terminal final batch fits in the maximum taken only over
sets of at most three arms. -/
theorem quartileUniformFinalPullBudget_le_terminalMax
    {Arm : Type*} [Fintype Arm] (epsilon delta : ℝ) (active : Finset Arm)
    (hterminal : active.card ≤ 3) :
    Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) ≤
      quartileUniformFinalTerminalMaxPullBudget Arm epsilon delta := by
  unfold quartileUniformFinalTerminalMaxPullBudget
  exact Finset.le_sup
    (s := ((Finset.univ : Finset (Finset Arm)).filter (fun candidate => candidate.card ≤ 3)))
    (f := fun candidate : Finset Arm => Fintype.card (UniformBatchCoordinate candidate
      (quartileUniformFinalSampleCount epsilon delta candidate)))
    (b := active)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ active, hterminal⟩)

/-- The number of coordinates in a survivor-specific uniform final batch
depends only on its finite cardinality. -/
theorem quartileUniformFinalPullBudget_eq_card
    {Arm : Type*} [Fintype Arm] (epsilon delta : ℝ) (active : Finset Arm) :
    Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) =
      active.card * uniformBernoulliBatchSampleBudget active.card epsilon delta := by
  simp [UniformBatchCoordinate, quartileUniformFinalSampleCount]

/-- Every terminal survivor-specific final batch is bounded by the explicit
four-case cardinality cap. -/
theorem quartileUniformFinalPullBudget_le_threeArmBudget
    {Arm : Type*} [Fintype Arm] (epsilon delta : ℝ) (active : Finset Arm)
    (hterminal : active.card ≤ 3) :
    Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) ≤
      quartileUniformFinalThreeArmPullBudget epsilon delta := by
  rw [quartileUniformFinalPullBudget_eq_card]
  unfold quartileUniformFinalThreeArmPullBudget
  exact Finset.le_sup
    (s := Finset.range 4)
    (f := fun armCount => armCount * uniformBernoulliBatchSampleBudget armCount epsilon delta)
    (b := active.card)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hterminal))

/-- The four terminal cardinalities are bounded by three copies of the
three-arm per-arm ceiling budget.  The zero-arm branch is cost-free, while
the positive branches use monotonicity of the Hoeffding target in the arm
count. -/
theorem quartileUniformFinalThreeArmPullBudget_le_three_mul_sampleBudget
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) :
    quartileUniformFinalThreeArmPullBudget epsilon delta ≤
      3 * uniformBernoulliBatchSampleBudget 3 epsilon delta := by
  unfold quartileUniformFinalThreeArmPullBudget
  apply Finset.sup_le
  intro armCount hmem
  have hleThree : armCount ≤ 3 := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem)
  by_cases hzero : armCount = 0
  · simp [hzero]
  · have hcard : 0 < armCount := Nat.pos_of_ne_zero hzero
    have hsourcePos : 0 < 2 * (armCount : ℝ) / delta := by positivity
    have hratioLe : 2 * (armCount : ℝ) / delta ≤ 2 * (3 : ℝ) / delta := by
      apply (div_le_div_iff_of_pos_right hdelta).mpr
      gcongr
      exact_mod_cast hleThree
    have htargetLe :
        2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) ≤
          2 / epsilon ^ 2 * Real.log (2 * (3 : ℝ) / delta) := by
      apply mul_le_mul_of_nonneg_left
        (Real.log_le_log hsourcePos hratioLe)
      exact le_of_lt (div_pos (by norm_num) (sq_pos_of_pos hepsilon))
    have hsampleLe : uniformBernoulliBatchSampleBudget armCount epsilon delta ≤
        uniformBernoulliBatchSampleBudget 3 epsilon delta := by
      unfold uniformBernoulliBatchSampleBudget
      exact Nat.ceil_le_ceil htargetLe
    calc
      armCount * uniformBernoulliBatchSampleBudget armCount epsilon delta ≤
          3 * uniformBernoulliBatchSampleBudget armCount epsilon delta := by
        exact Nat.mul_le_mul_right _ hleThree
      _ ≤ 3 * uniformBernoulliBatchSampleBudget 3 epsilon delta := by
        exact Nat.mul_le_mul_left _ hsampleLe

/-- An explicit real resource bound for the source terminal uniform batch.
It retains the exact `log (6 / delta)` cost of the three-arm worst case and
one ceiling pull per surviving arm. -/
theorem quartileUniformFinalThreeArmPullBudget_real_le
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (quartileUniformFinalThreeArmPullBudget epsilon delta : ℝ) ≤
      3 * (2 / epsilon ^ 2 * Real.log (6 / delta) + 1) := by
  have hcap := quartileUniformFinalThreeArmPullBudget_le_three_mul_sampleBudget
    epsilon delta hepsilon hdelta
  have hsample := uniformBernoulliBatchSampleBudget_real_le_target_add_one
    3 epsilon delta (by norm_num) hepsilon hdelta hdeltaLeOne
  calc
    (quartileUniformFinalThreeArmPullBudget epsilon delta : ℝ) ≤
        (3 * uniformBernoulliBatchSampleBudget 3 epsilon delta : ℕ) := by
      exact_mod_cast hcap
    _ = 3 * (uniformBernoulliBatchSampleBudget 3 epsilon delta : ℝ) := by
      norm_num
    _ ≤ 3 * (2 / epsilon ^ 2 * Real.log (6 / delta) + 1) := by
      have hnormalized :
          (uniformBernoulliBatchSampleBudget 3 epsilon delta : ℝ) ≤
            2 / epsilon ^ 2 * Real.log (6 / delta) + 1 := by
        norm_num at hsample ⊢
        exact hsample
      exact mul_le_mul_of_nonneg_left hnormalized (by norm_num : (0 : ℝ) ≤ 3)

/-- At the Corollary-4.4 half-accuracy and half-confidence split, the
three-arm terminal batch has the same positive-log resource form as the QE
prefix.  The constant is intentionally explicit: it accounts for all three
per-arm ceilings and the source's `delta / 2` final-stage allocation. -/
theorem quartileUniformFinalThreeArmEnvelope_real_le_sourceRateForm
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) ≤
      27 * (1 + Real.log 6) * (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
  let logFactor : ℝ := Real.log (1 / (delta / 2))
  let confidenceFactor : ℝ := 1 + Real.log 6
  let envelope : ℝ := confidenceFactor * (1 + logFactor)
  have hdeltaHalf : 0 < delta / 2 := by linarith
  have hdeltaHalfLeOne : delta / 2 ≤ 1 := by linarith
  have hlogSixNonneg : 0 ≤ Real.log 6 := by
    apply Real.log_nonneg
    norm_num
  have hlogFactorNonneg : 0 ≤ logFactor := by
    dsimp [logFactor]
    apply Real.log_nonneg
    apply (le_div_iff₀ hdeltaHalf).mpr
    linarith
  have hlogSplit : Real.log (6 / (delta / 2)) = Real.log 6 + logFactor := by
    dsimp [logFactor]
    rw [show 6 / (delta / 2) = 6 * (1 / (delta / 2)) by field_simp]
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (one_div_ne_zero hdeltaHalf.ne')]
  have hlogLeEnvelope : Real.log (6 / (delta / 2)) ≤ envelope := by
    rw [hlogSplit]
    dsimp [envelope, confidenceFactor]
    nlinarith [mul_nonneg hlogSixNonneg hlogFactorNonneg]
  have henvelopeGeOne : 1 ≤ envelope := by
    dsimp [envelope, confidenceFactor]
    nlinarith [mul_nonneg hlogSixNonneg hlogFactorNonneg]
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilonSqLeOne : epsilon ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hepsilon.le (by norm_num)).mpr hepsilonLeOne
  have hinvEpsilonSqGeOne : 1 ≤ 1 / epsilon ^ 2 := by
    apply (le_div_iff₀ hepsilonSqPos).mpr
    simpa using hepsilonSqLeOne
  have henvelopeOverEpsilonSqGeOne : 1 ≤ envelope / epsilon ^ 2 := by
    calc
      1 ≤ 1 / epsilon ^ 2 := hinvEpsilonSqGeOne
      _ ≤ envelope / epsilon ^ 2 := by
        exact div_le_div_of_nonneg_right henvelopeGeOne hepsilonSqPos.le
  have hlogOverEpsilonSq :
      Real.log (6 / (delta / 2)) / epsilon ^ 2 ≤ envelope / epsilon ^ 2 := by
    exact div_le_div_of_nonneg_right hlogLeEnvelope hepsilonSqPos.le
  have hhalfScale : 2 / (epsilon / 2) ^ 2 = 8 / epsilon ^ 2 := by
    field_simp [hepsilonSqPos.ne']
    ring
  calc
    3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) =
        3 * (8 * (Real.log (6 / (delta / 2)) / epsilon ^ 2) + 1) := by
      rw [hhalfScale]
      ring
    _ ≤ 3 * (8 * (envelope / epsilon ^ 2) + envelope / epsilon ^ 2) := by
      gcongr
    _ = 27 * (1 + Real.log 6) * (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
      dsimp [envelope, confidenceFactor, logFactor]
      ring

/-- The actual three-arm terminal-batch maximum inherits the positive-log
source rate from its explicit ceiling envelope. -/
theorem quartileUniformFinalThreeArmPullBudget_real_le_sourceRateForm
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (quartileUniformFinalThreeArmPullBudget (epsilon / 2) (delta / 2) : ℝ) ≤
      27 * (1 + Real.log 6) * (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
  exact (quartileUniformFinalThreeArmPullBudget_real_le
    (epsilon / 2) (delta / 2) (by linarith) (by linarith) (by linarith)).trans
    (quartileUniformFinalThreeArmEnvelope_real_le_sourceRateForm epsilon delta
      hepsilon hepsilonLeOne hdelta hdeltaLeOne)

/-- A tagged uniform final-batch outcome, with its active subtype made explicit. -/
abbrev canonicalQuartileUniformFinalOutcome (Arm : Type*) [Fintype Arm]
    (epsilon delta : ℝ) :=
  Σ active : Finset Arm,
    UniformBatchCoordinate active (quartileUniformFinalSampleCount epsilon delta active) → Bool

noncomputable section

noncomputable instance canonicalQuartileUniformFinalOutcomeFintype
    (Arm : Type*) [Fintype Arm] (epsilon delta : ℝ) :
    Fintype (canonicalQuartileUniformFinalOutcome Arm epsilon delta) :=
  Fintype.ofFinite _

noncomputable instance canonicalQuartileUniformFinalOutcomeDecidableEq
    (Arm : Type*) [Fintype Arm] (epsilon delta : ℝ) :
    DecidableEq (canonicalQuartileUniformFinalOutcome Arm epsilon delta) :=
  Classical.decEq _

/-- The actual conditional product law for the uniform final batch. -/
noncomputable def canonicalQuartileUniformFinalOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ) :
    Finset Arm → PMF (canonicalQuartileUniformFinalOutcome Arm epsilon delta) :=
  fun active =>
    (uniformBernoulliBatchLaw (fun arm : active => mean arm.val)
      (fun arm => hmean arm.val)
      (quartileUniformFinalSampleCount epsilon delta active)).map
      (fun labels => ⟨active, labels⟩)

/-- For a fixed nonempty survivor set, the tagged final-batch kernel is
exactly the reward law of the corresponding finite sequential policy, followed
by the coordinate reindexing used by the static batch. -/
theorem canonicalQuartileUniformFinalOutcomeLaw_eq_sequentialReplay
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) [Nonempty active] :
    canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active =
      (adaptiveBernoulliRewardLaw (fun arm : active => mean arm.val)
        (fun arm => hmean arm.val)
        (uniformBernoulliBatchProcedure (Arm := active)
          (quartileUniformFinalSampleCount epsilon delta active))).map
        (fun rewards => ⟨active,
          uniformBatchTraceLabels
            (quartileUniformFinalSampleCount epsilon delta active) rewards⟩) := by
  classical
  let activeMean : active → ℝ := fun arm => mean arm.val
  let activeMeansValid : ValidBernoulliMeans activeMean := fun arm => hmean arm.val
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  rw [canonicalQuartileUniformFinalOutcomeLaw]
  rw [← adaptiveUniformBernoulliBatchProcedureRewardLaw_map_eq_uniformBernoulliBatchLaw
    activeMean activeMeansValid sampleCount]
  rw [PMF.map_comp]
  rfl

/--
The same fixed final batch, stated as a procedure over the original arm type
rather than over the survivor subtype.  The nonempty survivor instance makes
the empirical-maximizer output total; its pull schedule still visits exactly
the survivor/sample coordinates once.
-/
noncomputable def canonicalQuartileUniformFinalArmProcedure
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ) (active : Finset Arm) [Nonempty active] :
    FiniteAdaptiveBernoulliBestArmProcedure Arm
      (Fintype.card (UniformBatchCoordinate active
        (quartileUniformFinalSampleCount epsilon delta active))) :=
  fixedBernoulliProcedure
    (fun round =>
      ((uniformBatchCoordinateEquiv active
        (quartileUniformFinalSampleCount epsilon delta active)).symm round).1.val)
    (fun rewards =>
      (uniformBernoulliBatchBestArm
        (quartileUniformFinalSampleCount epsilon delta active)
        (uniformBatchTraceLabels
          (quartileUniformFinalSampleCount epsilon delta active) rewards)).val)

/--
For every nonempty survivor set, the tagged final kernel is also the exact
reward-law pushforward of an original-arm-valued finite procedure.  This
removes the subtype-only seam before composing it after a history-dependent
QE prefix.
-/
theorem canonicalQuartileUniformFinalOutcomeLaw_eq_armSequentialReplay
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) [Nonempty active] :
    canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active =
      (adaptiveBernoulliRewardLaw mean hmean
        (canonicalQuartileUniformFinalArmProcedure epsilon delta active)).map
        (fun rewards => ⟨active,
          uniformBatchTraceLabels
            (quartileUniformFinalSampleCount epsilon delta active) rewards⟩) := by
  let activeMean : active → ℝ := fun arm => mean arm.val
  let activeMeansValid : ValidBernoulliMeans activeMean := fun arm => hmean arm.val
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  rw [canonicalQuartileUniformFinalOutcomeLaw]
  rw [← uniformBatchTraceProductLaw_map_eq_uniformBernoulliBatchLaw
    activeMean activeMeansValid sampleCount]
  rw [canonicalQuartileUniformFinalArmProcedure,
    adaptiveFixedBernoulliRewardLaw_eq_pmfPi]
  rw [PMF.map_comp]
  congr 1

/-- A fixed-horizon version of the original-arm final replay.  Once every
usable survivor/sample coordinate has been queried, any remaining pulls use a
fixed harmless arm; the outcome map below discards those padded responses. -/
noncomputable def canonicalQuartileUniformFinalPaddedArmProcedure
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ) (active : Finset Arm) [Nonempty active]
    (pullBudget : ℕ)
    (hbudget : Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) ≤ pullBudget) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm pullBudget where
  pull := fun round _history =>
    if hround : round.val < Fintype.card (UniformBatchCoordinate active
        (quartileUniformFinalSampleCount epsilon delta active)) then
      ((uniformBatchCoordinateEquiv active
        (quartileUniformFinalSampleCount epsilon delta active)).symm
        ⟨round.val, hround⟩).1.val
    else Classical.choice (inferInstance : Nonempty Arm)
  output := fun _ => Classical.choice (inferInstance : Nonempty Arm)

/-- Discarding the inert suffix of a fixed-horizon final replay recovers the
exact tagged uniform-final kernel. -/
theorem canonicalQuartileUniformFinalOutcomeLaw_eq_paddedArmSequentialReplay
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) [Nonempty active]
    (pullBudget : ℕ)
    (hbudget : Fintype.card (UniformBatchCoordinate active
      (quartileUniformFinalSampleCount epsilon delta active)) ≤ pullBudget) :
    canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active =
      (adaptiveBernoulliRewardLaw mean hmean
        (canonicalQuartileUniformFinalPaddedArmProcedure epsilon delta active
          pullBudget hbudget)).map
        (fun rewards => ⟨active,
          uniformBatchTraceLabels
            (quartileUniformFinalSampleCount epsilon delta active)
            (rewardTracePrefixLE
              (Fintype.card (UniformBatchCoordinate active
                (quartileUniformFinalSampleCount epsilon delta active)))
              pullBudget hbudget rewards)⟩) := by
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  let padded := canonicalQuartileUniformFinalPaddedArmProcedure epsilon delta active
    pullBudget hbudget
  let replay := canonicalQuartileUniformFinalArmProcedure epsilon delta active
  have hlocalCard : localBudget = active.card * sampleCount := by
    simpa [localBudget] using
      (uniformBernoulliBatchProcedure_pullBudget (Arm := active) sampleCount)
  have hpulls : ∀ (round : Fin localBudget) (history : Fin round.val → Bool),
      padded.pull ⟨round.val, Nat.lt_of_lt_of_le round.isLt hbudget⟩ history =
        replay.pull round history := by
    intro round history
    have hround : round.val < active.card * sampleCount := by
      simpa [hlocalCard] using round.isLt
    simp [padded, replay, canonicalQuartileUniformFinalPaddedArmProcedure,
      canonicalQuartileUniformFinalArmProcedure, fixedBernoulliProcedure,
      sampleCount, localBudget, hlocalCard, hround]
  have hlocalLaw :
      adaptiveBernoulliRewardPrefixLaw mean hmean padded localBudget hbudget =
      adaptiveBernoulliRewardLaw mean hmean replay := by
    simpa using
      (adaptiveBernoulliRewardPrefixLaw_congr_pulls_prefix mean hmean padded replay
        localBudget hbudget (Nat.le_refl _) hpulls)
  have hprefixLaw :
      (adaptiveBernoulliRewardLaw mean hmean padded).map
        (rewardTracePrefixLE localBudget pullBudget hbudget) =
      adaptiveBernoulliRewardPrefixLaw mean hmean padded localBudget hbudget := by
    simpa [adaptiveBernoulliRewardLaw] using
      (adaptiveBernoulliRewardPrefixLaw_map_rewardTracePrefixLE mean hmean padded
        localBudget pullBudget hbudget (Nat.le_refl _))
  calc
    canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active =
        (adaptiveBernoulliRewardLaw mean hmean replay).map
          (fun rewards => ⟨active,
            uniformBatchTraceLabels sampleCount rewards⟩) :=
      canonicalQuartileUniformFinalOutcomeLaw_eq_armSequentialReplay
        mean hmean epsilon delta active
    _ = (adaptiveBernoulliRewardPrefixLaw mean hmean padded localBudget hbudget).map
          (fun rewards => ⟨active,
            uniformBatchTraceLabels sampleCount rewards⟩) := by rw [hlocalLaw]
    _ = ((adaptiveBernoulliRewardLaw mean hmean padded).map
          (rewardTracePrefixLE localBudget pullBudget hbudget)).map
          (fun rewards => ⟨active,
            uniformBatchTraceLabels sampleCount rewards⟩) := by rw [hprefixLaw]
    _ = _ := by
      rw [PMF.map_comp]
      rfl

/-- The full padded reward-trace law used by the final stage.  On an empty
active set it is a harmless point mass; the source QE invariant gives a
nonempty active set on every realized continuation. -/
noncomputable def quartileUniformFinalPaddedTraceLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) :
    PMF (Fin (quartileUniformFinalMaxPullBudget Arm epsilon delta) → Bool) :=
  if hactive : active.Nonempty then
    letI : Nonempty active := hactive.to_subtype
    let pullBudget := quartileUniformFinalMaxPullBudget Arm epsilon delta
    let sampleCount := quartileUniformFinalSampleCount epsilon delta active
    let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
    let hbudget : localBudget ≤ pullBudget := by
      simpa [localBudget] using
        (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon delta active)
    adaptiveBernoulliRewardLaw mean hmean
      (canonicalQuartileUniformFinalPaddedArmProcedure epsilon delta active
        pullBudget hbudget)
  else PMF.pure (fun _ => false)

/-- On every nonempty survivor set, mapping the fixed padded trace to its
usable uniform-batch coordinates recovers the exact tagged final kernel. -/
theorem quartileUniformFinalPaddedTraceLaw_map_eq_outcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) (hactive : active.Nonempty) :
    (quartileUniformFinalPaddedTraceLaw mean hmean epsilon delta active).map
      (fun rewards =>
        let pullBudget := quartileUniformFinalMaxPullBudget Arm epsilon delta
        let sampleCount := quartileUniformFinalSampleCount epsilon delta active
        let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
        let hbudget : localBudget ≤ pullBudget := by
          simpa [localBudget] using
            (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon delta active)
        ⟨active, uniformBatchTraceLabels sampleCount
          (rewardTracePrefixLE localBudget pullBudget hbudget rewards)⟩) =
      canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active := by
  letI : Nonempty active := hactive.to_subtype
  let pullBudget := quartileUniformFinalMaxPullBudget Arm epsilon delta
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  have hbudget : localBudget ≤ pullBudget := by
    simpa [localBudget] using
      (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon delta active)
  rw [quartileUniformFinalPaddedTraceLaw, dif_pos hactive]
  dsimp
  symm
  exact canonicalQuartileUniformFinalOutcomeLaw_eq_paddedArmSequentialReplay
    mean hmean epsilon delta active pullBudget hbudget

/--
Read the empirical maximizer from a tagged final batch.  On a zero-cardinality
tag the value is a harmless total-function fallback; all success statements
are restricted to nonempty active sets.
-/
noncomputable def canonicalQuartileUniformFinalOutput
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ) (active : Finset Arm)
    (outcome : canonicalQuartileUniformFinalOutcome Arm epsilon delta) : Arm :=
  if htag : outcome.1.Nonempty then
    letI : Nonempty outcome.1 := htag.to_subtype
    (uniformBernoulliBatchBestArm
      (quartileUniformFinalSampleCount epsilon delta outcome.1) outcome.2).val
  else Classical.choice (inferInstance : Nonempty Arm)

/-- The source final-stage decision read from a fixed padded trace.  Only the
prefix allocated to the particular survivor set is used; the remaining
coordinates are intentionally inert. -/
noncomputable def quartileUniformFinalPaddedTraceOutput
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ) (active : Finset Arm)
    (rewards : Fin (quartileUniformFinalMaxPullBudget Arm epsilon delta) → Bool) : Arm := by
  let pullBudget := quartileUniformFinalMaxPullBudget Arm epsilon delta
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  let localBudget := Fintype.card (UniformBatchCoordinate active sampleCount)
  let hbudget : localBudget ≤ pullBudget := by
    simpa [localBudget] using
      (quartileUniformFinalPullBudget_le_max (Arm := Arm) epsilon delta active)
  exact canonicalQuartileUniformFinalOutput epsilon delta active
    ⟨active, uniformBatchTraceLabels sampleCount
      (rewardTracePrefixLE localBudget pullBudget hbudget rewards)⟩

end

/--
Conditionally on any nonempty active set, the tagged final uniform batch is
`epsilon`-PAC within that set with its literal `1 - delta` guarantee.
-/
theorem canonicalQuartileUniformFinal_activePAC_probability_ge_one_sub
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (active : Finset Arm) (hactive : active.Nonempty) :
    1 - delta ≤ pmfProbClassical
      (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active)
      (finalActiveEpsilonPAC mean epsilon
        (canonicalQuartileUniformFinalOutput epsilon delta) active) := by
  classical
  letI : Nonempty active := hactive.to_subtype
  let activeMean : active → ℝ := fun arm => mean arm.val
  let activeMeansValid : ValidBernoulliMeans activeMean := fun arm => hmean arm.val
  let sampleCount := quartileUniformFinalSampleCount epsilon delta active
  let batchLaw : PMF (UniformBatchCoordinate active sampleCount → Bool) :=
    uniformBernoulliBatchLaw activeMean activeMeansValid sampleCount
  let selected : (UniformBatchCoordinate active sampleCount → Bool) → active :=
    uniformBernoulliBatchBestArm sampleCount
  have hfailureMeasure : batchLaw.toMeasure.real
      {labels | ¬ EpsilonPACBestArm activeMean epsilon (selected labels)} ≤ delta := by
    simpa [batchLaw, activeMean, sampleCount, selected,
      quartileUniformFinalSampleCount] using
      (uniformBernoulliBatchBestArm_failure_probability_of_budget activeMean activeMeansValid
        epsilon delta hepsilon hdelta hdeltaLeOne)
  have hfailure : pmfProbClassical batchLaw
      (fun labels => ¬ EpsilonPACBestArm activeMean epsilon (selected labels)) ≤ delta := by
    rw [pmfProbClassical_eq_pmfProb, AppliedModelingLib.pmfProb_eq_toMeasure_real]
    exact hfailureMeasure
  have hsuccess : 1 - delta ≤ pmfProbClassical batchLaw
      (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) := by
    have hcomplement : pmfProbClassical batchLaw
        (fun labels => ¬ EpsilonPACBestArm activeMean epsilon (selected labels)) =
        1 - pmfProbClassical batchLaw
          (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) := by
      calc
        pmfProbClassical batchLaw
            (fun labels => ¬ EpsilonPACBestArm activeMean epsilon (selected labels)) =
            pmfProb batchLaw
              (fun labels => ¬ EpsilonPACBestArm activeMean epsilon (selected labels)) :=
          pmfProbClassical_eq_pmfProb _ _
        _ = 1 - pmfProb batchLaw
            (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) :=
          pmfProb_compl _ _
        _ = 1 - pmfProbClassical batchLaw
            (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) := by
          rw [pmfProbClassical_eq_pmfProb]
    linarith
  rw [show canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active =
      batchLaw.map (fun labels => ⟨active, labels⟩) by
        simp [canonicalQuartileUniformFinalOutcomeLaw, batchLaw, activeMean, sampleCount]]
  rw [pmfProbClassical_eq_pmfProb, pmfProb_map]
  have hevent : ∀ labels,
      finalActiveEpsilonPAC mean epsilon (canonicalQuartileUniformFinalOutput epsilon delta)
        active ⟨active, labels⟩ ↔
        EpsilonPACBestArm activeMean epsilon (selected labels) := by
    intro labels
    constructor
    · rintro ⟨_, hlabels⟩ arm
      simpa [canonicalQuartileUniformFinalOutput, hactive, activeMean, sampleCount, selected]
        using hlabels arm.val arm.property
    · intro hpac
      refine ⟨?_, ?_⟩
      · simp [canonicalQuartileUniformFinalOutput, hactive]
      · intro competitor hcompetitor
        simpa [canonicalQuartileUniformFinalOutput, hactive, activeMean, sampleCount, selected]
          using hpac ⟨competitor, hcompetitor⟩
  have hsuccess' : 1 - delta ≤ pmfProb batchLaw
      (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) := by
    rw [← pmfProbClassical_eq_pmfProb]
    exact hsuccess
  calc
    1 - delta ≤ pmfProb batchLaw
        (fun labels => EpsilonPACBestArm activeMean epsilon (selected labels)) := hsuccess'
    _ = pmfProb batchLaw (fun labels =>
        finalActiveEpsilonPAC mean epsilon (canonicalQuartileUniformFinalOutput epsilon delta)
          active ⟨active, labels⟩) := by
      apply pmfProb_congr
      intro labels
      exact (hevent labels).symm

/-- The padded trace itself is PAC on every nonempty active set.  This is the
conditional final-stage guarantee in a fixed, history-independent carrier. -/
theorem quartileUniformFinalPaddedTraceLaw_activePAC_probability_ge_one_sub
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (active : Finset Arm) (hactive : active.Nonempty) :
    1 - delta ≤ pmfProbClassical
      (quartileUniformFinalPaddedTraceLaw mean hmean epsilon delta active)
      (fun rewards => finalActiveEpsilonPAC mean epsilon
        (quartileUniformFinalPaddedTraceOutput epsilon delta) active rewards) := by
  classical
  have hcanonical := canonicalQuartileUniformFinal_activePAC_probability_ge_one_sub
    mean hmean epsilon delta hepsilon hdelta hdeltaLeOne active hactive
  rw [← quartileUniformFinalPaddedTraceLaw_map_eq_outcomeLaw
    mean hmean epsilon delta active hactive] at hcanonical
  rw [pmfProbClassical_eq_pmfProb] at hcanonical ⊢
  rw [pmfProb_map] at hcanonical
  simpa [quartileUniformFinalPaddedTraceOutput] using hcanonical

/-- Discarding the inert padded coordinates gives exactly the same selected-arm
law as the tagged source final kernel on a fixed nonempty survivor set. -/
theorem quartileUniformFinalPaddedTraceLaw_map_output_eq_outcomeLaw_map_output
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (epsilon delta : ℝ)
    (active : Finset Arm) (hactive : active.Nonempty) :
    (quartileUniformFinalPaddedTraceLaw mean hmean epsilon delta active).map
      (quartileUniformFinalPaddedTraceOutput epsilon delta active) =
      (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon delta active).map
        (canonicalQuartileUniformFinalOutput epsilon delta active) := by
  rw [← quartileUniformFinalPaddedTraceLaw_map_eq_outcomeLaw
    mean hmean epsilon delta active hactive]
  rw [PMF.map_comp]
  rfl

/--
QE followed by the concrete tagged uniform final batch is globally PAC on the
joint finite PMF whenever the QE state has the displayed near-maximum bound.
-/
theorem quartileUniformFinalJoint_epsilonPAC_probability_ge_one_sub
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (initial : Finset Arm) (hinitial : initial.Nonempty)
    (hinitialAll : ∀ arm, arm ∈ initial) (loss epsilon deltaQE deltaFinal : ℝ)
    (qeStateLaw : PMF (Finset Arm × Bool))
    (hdeltaQE : 0 ≤ deltaQE) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1) (hepsilon : 0 < epsilon)
    (hqe : 1 - deltaQE ≤ pmfProbClassical qeStateLaw
      (quartileStateNearInitialMaximum mean initial hinitial loss)) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (qeStateLaw.bind fun stateFailure =>
          (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
            (fun outcome => (stateFailure, outcome)))
        (fun stateOutcome => EpsilonPACBestArm mean (loss + epsilon)
          (canonicalQuartileUniformFinalOutput epsilon deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  classical
  apply quartileFinalJoint_epsilonPAC_probability_ge_one_sub
    mean initial hinitial hinitialAll loss epsilon deltaQE deltaFinal qeStateLaw
    (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal)
    (canonicalQuartileUniformFinalOutput epsilon deltaFinal)
    hdeltaQE hdeltaFinal.le hdeltaFinalLeOne hqe
  intro stateFailure hstate
  rcases hstate with ⟨_, survivor, hsurvivor, _⟩
  exact canonicalQuartileUniformFinal_activePAC_probability_ge_one_sub
    mean hmean epsilon deltaFinal hepsilon hdeltaFinal hdeltaFinalLeOne stateFailure.1
    ⟨survivor, hsurvivor⟩

end ZhouChenLi2014OptimalPACMultipleArm
