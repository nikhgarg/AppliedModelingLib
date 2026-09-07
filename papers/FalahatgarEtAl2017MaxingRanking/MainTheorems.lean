import FalahatgarEtAl2017MaxingRanking.SequentialElimination
import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare
import FalahatgarEtAl2017MaxingRanking.AdaptiveCompare
import FalahatgarEtAl2017MaxingRanking.AdaptiveCompareProbability
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminate
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateProbability
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateCost
import FalahatgarEtAl2017MaxingRanking.AdaptiveFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches
import FalahatgarEtAl2017MaxingRanking.FiniteBatchConcentration
import FalahatgarEtAl2017MaxingRanking.FiniteBatchAdaptiveCompareProbability
import FalahatgarEtAl2017MaxingRanking.FiniteBatchFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.PickAnchorFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.CanonicalFreshPickAnchor
import FalahatgarEtAl2017MaxingRanking.CanonicalUniformSeqEliminate
import FalahatgarEtAl2017MaxingRanking.PickAnchorRankedTop
import FalahatgarEtAl2017MaxingRanking.PickAnchorCost
import FalahatgarEtAl2017MaxingRanking.FiniteBatchPruneProbability
import FalahatgarEtAl2017MaxingRanking.CanonicalPruneBatches
import FalahatgarEtAl2017MaxingRanking.CanonicalPruneSize
import FalahatgarEtAl2017MaxingRanking.CanonicalPruneRounds
import FalahatgarEtAl2017MaxingRanking.PruneMultiplicative
import FalahatgarEtAl2017MaxingRanking.CanonicalPruneChernoff
import FalahatgarEtAl2017MaxingRanking.CanonicalFullPruneBatches
import FalahatgarEtAl2017MaxingRanking.CanonicalFullPruneNumerics
import FalahatgarEtAl2017MaxingRanking.CanonicalFreshPruneRounds
import FalahatgarEtAl2017MaxingRanking.PruneSourceNumerics
import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction
import FalahatgarEtAl2017MaxingRanking.FreshPruneRounds
import FalahatgarEtAl2017MaxingRanking.StoppedPruneRounds
import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRounds
import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRetention
import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneTrace
import FalahatgarEtAl2017MaxingRanking.PruneSourceSchedule
import FalahatgarEtAl2017MaxingRanking.CanonicalPruneSourceSchedule
import FalahatgarEtAl2017MaxingRanking.SeqEliminateFixedSample
import FalahatgarEtAl2017MaxingRanking.SeqEliminateProbability
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import FalahatgarEtAl2017MaxingRanking.GoodAnchors
import FalahatgarEtAl2017MaxingRanking.PickAnchorSampling
import FalahatgarEtAl2017MaxingRanking.PickAnchorProbability
import FalahatgarEtAl2017MaxingRanking.PickAnchorTail
import FalahatgarEtAl2017MaxingRanking.PickAnchorSeqEliminate
import FalahatgarEtAl2017MaxingRanking.PickAnchorJointProbability
import FalahatgarEtAl2017MaxingRanking.StrongTransitivityRanking
import FalahatgarEtAl2017MaxingRanking.CanonicalStrongTransitivityRanking
import FalahatgarEtAl2017MaxingRanking.StrongTransitivityAsymptotics
import FalahatgarEtAl2017MaxingRanking.BordaCore
import FalahatgarEtAl2017MaxingRanking.BordaProbability
import FalahatgarEtAl2017MaxingRanking.CanonicalBordaBatches
import FalahatgarEtAl2017MaxingRanking.BordaBanditBridge
import FalahatgarEtAl2017MaxingRanking.RankingLowerBound
import FalahatgarEtAl2017MaxingRanking.OptMaximizeFinal
import FalahatgarEtAl2017MaxingRanking.FinalCheckProbability
import FalahatgarEtAl2017MaxingRanking.OptMaximizeProbability
import FalahatgarEtAl2017MaxingRanking.OptMaximizeAnchorPrune
import FalahatgarEtAl2017MaxingRanking.OptMaximizeFallback
import FalahatgarEtAl2017MaxingRanking.FreshFinalCheck
import FalahatgarEtAl2017MaxingRanking.OptMaximizeResource
import FalahatgarEtAl2017MaxingRanking.OptMaximizeResourceTrace
import FalahatgarEtAl2017MaxingRanking.OptMaximizeResourceAsymptotics
import FalahatgarEtAl2017MaxingRanking.SeqEliminateAsymptotics
import FalahatgarEtAl2017MaxingRanking.BordaAsymptotics
import FalahatgarEtAl2017MaxingRanking.PickAnchorAsymptotics
import FalahatgarEtAl2017MaxingRanking.PruneAsymptotics
import FalahatgarEtAl2017MaxingRanking.PruneRetention
import FalahatgarEtAl2017MaxingRanking.PruneProbability
import FalahatgarEtAl2017MaxingRanking.PruneSize

/-!
# Falahatgar et al. (2017): implementation theorem layer

The interface includes the source-visible deterministic event in Theorem 2's
proof and the finite event-composition theorem that instantiates its adaptive
Compare confidence schedule.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
Theorem 6's finite OPT-Maximize contract. The source cutoff is rounded upward
and capped at the population size. Its four non-base phases use Algorithm 3's
printed `δ / 4` allocation. One finite trace event, of probability at
least `1 - δ`, contains both the returned `ε`-maximum and its deterministic
comparison envelope.
-/
theorem theorem6_optMaximize_sourceCutoff_joint_envelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (lower upper epsilon delta : ℝ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    1 - delta ≤ canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
      lower upper epsilon delta
      (sourceOptMaximizeAlgorithm3PruneMaxBatch (Arm := Arm) lower upper delta)
      preferenceGap maximum hprobability hdelta hdeltaLeOne
      (by
        intro round hround
        exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
          lower upper delta round hround) := by
  classical
  exact canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability_ge
    lower upper epsilon delta
    (sourceOptMaximizeAlgorithm3PruneMaxBatch (Arm := Arm) lower upper delta)
    preferenceGap maximum hprobability ranking hranking hdelta hdeltaLeOne hlower hantisymmetric hself
    hcomplete hsst
    (by
      intro round hround
      exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
        lower upper delta round hround)
    hupperNonnegative hmaximumAbsolute hseparation hepsilon hfinalSeparation

/--
Theorem 6's clarified finite contract at Algorithm 3's printed thresholds
`ε / 3` and `2ε / 3`.  The source clarification and integer rounding are explicit
in the algorithmic law; no batch-bound witness remains in this source-facing
specialization.
-/
theorem theorem6_optMaximize_sourceParameters_joint_envelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hepsilon : 0 < epsilon) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    1 - delta ≤ canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
      (epsilon / 3) (2 * epsilon / 3) epsilon delta
      (sourceOptMaximizeAlgorithm3PruneMaxBatch
        (Arm := Arm) (epsilon / 3) (2 * epsilon / 3) delta)
      preferenceGap maximum hprobability hdelta hdeltaLeOne
      (by
        intro round hround
        exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
          (epsilon / 3) (2 * epsilon / 3) delta round hround) := by
  classical
  exact theorem6_optMaximize_sourceCutoff_joint_envelope
    (epsilon / 3) (2 * epsilon / 3) epsilon delta preferenceGap maximum hprobability ranking hranking
    hdelta hdeltaLeOne (by linarith) hantisymmetric hself hcomplete hsst (by linarith)
    hmaximumAbsolute (by linarith) hepsilon (by linarith)

/--
For fixed positive `ε` and valid `δ`, Theorem 6's exact population envelope
at the source thresholds is linear in the number of arms. This is a
rate theorem for the finite envelope above; the source's unshifted uniform
`log (1 / δ)` display is intentionally not substituted for this statement.
-/
theorem theorem6_optMaximize_sourceParameters_rateEnvelope_isBigO_linear
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceOptMaximizeAlgorithm3RateEnvelope armCount
          (epsilon / 3) (2 * epsilon / 3) epsilon delta)
      (fun armCount : ℕ => (armCount : ℝ)) := by
  exact sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_linear
    (by linarith) hdelta hdeltaLeOne

/--
At Algorithm 3's printed accuracy thresholds, the finite envelope
has the source's linear-in-arms confidence-and-accuracy rate shape.  The
shifted confidence logarithm preserves the finite `delta = 1` endpoint; this
is an asymptotic result for fixed displayed `epsilon` and `delta` values.
-/
theorem theorem6_optMaximize_sourceParameters_rateEnvelope_isBigO_sourceRateShape
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceOptMaximizeAlgorithm3RateEnvelope armCount
          (epsilon / 3) (2 * epsilon / 3) epsilon delta)
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2) :=
  sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_sourceRateShape
    hepsilon hdelta hdeltaLeOne

/--
The complete Algorithm-3 branchwise resource envelope has the same
source rate shape.  The small-confidence branch is Seq-Eliminate and the
remaining branch is the literal four-phase OPT-Maximize envelope.
-/
theorem theorem6_optMaximize_sourceParameters_branchEnvelope_isBigO_sourceRateShape
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ => sourceOptMaximizeAlgorithm3TotalRateEnvelope
        armCount epsilon delta)
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2) :=
  sourceOptMaximizeAlgorithm3TotalRateEnvelope_isBigO_sourceRateShape
    hepsilon hdelta hdeltaLeOne

/--
Theorem 8's qualitative finite Borda-maxing conclusion, instantiated with the
verified sequential replay of Zhou--Chen--Li's uniform final batch.  This has
an explicit ceiling budget and literal `1 - delta` guarantee; it is distinct
from the cited paper's sharper QE resource-rate statement.
-/
theorem theorem8_bordaMaxing_uniformPolicy_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon
      (ZhouChenLi2014OptimalPACMultipleArm.uniformBernoulliBatchProcedure (Arm := Arm)
        (ZhouChenLi2014OptimalPACMultipleArm.uniformBernoulliBatchSampleBudget
          (Fintype.card Arm) epsilon delta)) := by
  classical
  exact adaptiveCanonicalBordaSuccessProbability_uniformBernoulliBatchProcedure
    winProbability hprobability epsilon delta hepsilon hdelta hdeltaLeOne

/--
The concrete proof witness for Theorem 8's abstract algorithm-existence
statement. Its semantic interface exposes only an adaptive comparison policy,
its returned arm, and its unpadded realized comparison count; the cited
quartile-elimination construction remains proof implementation.
-/
noncomputable def theorem8BordaMaxingSourceRateAlgorithm
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (roundCount : ℕ) (epsilon delta : ℝ) :
    FiniteAdaptiveBordaMaxingAlgorithm Arm := by
  classical
  let totalBudget :=
    ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
      (Fintype.card Arm) (delta / 2)
      (epsilon / 2 *
        (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2)
  let qeSlotCount := Fintype.card
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialSlot
      roundCount totalBudget)
  let finalBudget :=
    ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalMaxPullBudget
      Arm (epsilon / 2) (delta / 2)
  let procedure :=
    ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
      roundCount totalBudget (Finset.univ : Finset Arm) Finset.univ_nonempty
      (epsilon / 2) (delta / 2)
  let executionCount := fun rewards =>
    ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalPullCount
      roundCount totalBudget (Finset.univ : Finset Arm)
      (ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
        qeSlotCount finalBudget rewards)
      (epsilon / 2) (delta / 2)
  have hcountLe : ∀ rewards, executionCount rewards ≤ qeSlotCount + finalBudget := by
    intro rewards
    let qeHistory := ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
      qeSlotCount finalBudget rewards
    let active :=
      ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialState
        roundCount totalBudget (Finset.univ : Finset Arm) qeHistory roundCount
    have hlocal : Fintype.card
        (ZhouChenLi2014OptimalPACMultipleArm.UniformBatchCoordinate active
          (ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalSampleCount
            (epsilon / 2) (delta / 2) active)) ≤ finalBudget := by
      simpa [finalBudget, active] using
        (ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalPullBudget_le_max
          (Arm := Arm) (epsilon / 2) (delta / 2) active)
    change qeSlotCount + Fintype.card
        (ZhouChenLi2014OptimalPACMultipleArm.UniformBatchCoordinate active
          (ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalSampleCount
            (epsilon / 2) (delta / 2) active)) ≤ qeSlotCount + finalBudget
    exact Nat.add_le_add_left hlocal qeSlotCount
  have hcountStable : ∀ rewards alternative,
      (∀ comparison, comparison.val < executionCount rewards →
        alternative comparison = rewards comparison) →
      executionCount alternative = executionCount rewards := by
    intro rewards alternative hprefix
    have hqe :
        ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
            qeSlotCount finalBudget alternative =
          ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
            qeSlotCount finalBudget rewards := by
      funext position
      apply hprefix
      have hqeCount : qeSlotCount ≤ executionCount rewards := by
        change qeSlotCount ≤ qeSlotCount + _
        omega
      exact lt_of_lt_of_le position.isLt hqeCount
    simp [executionCount, hqe]
  have houtputStable : ∀ rewards alternative,
      (∀ comparison, comparison.val < executionCount rewards →
        alternative comparison = rewards comparison) →
      procedure.output alternative = procedure.output rewards := by
    intro rewards alternative hprefix
    have hqe :
        ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
            qeSlotCount finalBudget alternative =
          ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
            qeSlotCount finalBudget rewards := by
      funext position
      apply hprefix
      have hqeCount : qeSlotCount ≤ executionCount rewards := by
        change qeSlotCount ≤ qeSlotCount + _
        omega
      exact lt_of_lt_of_le position.isLt hqeCount
    let qeHistory := ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
      qeSlotCount finalBudget rewards
    let active :=
      ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialState
        roundCount totalBudget (Finset.univ : Finset Arm) qeHistory roundCount
    let sampleCount :=
      ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalSampleCount
        (epsilon / 2) (delta / 2) active
    let localBudget := Fintype.card
      (ZhouChenLi2014OptimalPACMultipleArm.UniformBatchCoordinate active sampleCount)
    have hlocal : localBudget ≤ finalBudget := by
      simpa [localBudget, sampleCount, finalBudget, active] using
        (ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalPullBudget_le_max
          (Arm := Arm) (epsilon / 2) (delta / 2) active)
    have hfinal :
        ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefixLE
            localBudget finalBudget hlocal
            (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalSuffix
              qeSlotCount finalBudget alternative) =
          ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefixLE
            localBudget finalBudget hlocal
            (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalSuffix
              qeSlotCount finalBudget rewards) := by
      funext position
      apply hprefix
      change qeSlotCount + position.val < executionCount rewards
      have hcountEq : executionCount rewards = qeSlotCount + localBudget := by
        rfl
      rw [hcountEq]
      omega
    change
      ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalPaddedTraceOutput
          (epsilon / 2) (delta / 2)
          (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialState
            roundCount totalBudget (Finset.univ : Finset Arm)
            (ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
              qeSlotCount finalBudget alternative) roundCount)
          (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalSuffix
            qeSlotCount finalBudget alternative) =
        ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalPaddedTraceOutput
          (epsilon / 2) (delta / 2)
          (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialState
            roundCount totalBudget (Finset.univ : Finset Arm)
            (ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
              qeSlotCount finalBudget rewards) roundCount)
          (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalSuffix
            qeSlotCount finalBudget rewards)
    rw [hqe]
    have hfinalExpanded := hfinal
    simp only [localBudget, sampleCount, active, qeHistory] at hfinalExpanded
    unfold ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalPaddedTraceOutput
    dsimp only
    rw [hfinalExpanded]
  exact
    { pullBudget := qeSlotCount + finalBudget
      procedure := procedure
      executionComparisonCount := executionCount
      executionComparisonCount_le_pullBudget := hcountLe
      executionComparisonCount_stable := hcountStable
      output_stable_through_execution := houtputStable }

/-- Theorem 8's finite Borda-maxing reduction instantiated with Zhou--Chen--Li's
literal sequential QE-plus-uniform-final policy.  The confidence and accuracy
budgets are split evenly between QE and the final stage; the source's sharper
asymptotic resource calculation remains a separate supporting theorem. -/
theorem theorem8_bordaMaxing_sequentialQEPolicy_finite_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (roundCount : ℕ) (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
      roundCount
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceAccuracyTotalBudgetRequirement
        (Fintype.card Arm) roundCount (epsilon / 2) (delta / 2))
      (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon procedure := by
  classical
  dsimp
  let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
    roundCount
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceAccuracyTotalBudgetRequirement
      (Fintype.card Arm) roundCount (epsilon / 2) (delta / 2))
    (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
  change 1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
    winProbability hprobability epsilon procedure
  rw [adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability]
  unfold ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
  have hsource := ZhouChenLi2014OptimalPACMultipleArm.sourceQE_sequentialUniformFinalProcedure_finitePAC_of_accuracyBudget
      (bordaScore winProbability)
      (bordaScore_validBernoulliMeans winProbability hprobability)
      roundCount (delta / 2) (epsilon / 2) (epsilon / 2) (delta / 2) epsilon
      (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  rw [pmfProbClassical_eq_pmfProb, pmfProb_map] at hsource
  simpa [procedure, EpsilonBordaMaximum] using hsource

/-- Theorem 8 through Zhou--Chen--Li's direct geometric-envelope budget.  The
policy is fully finite with no residual sample-count premise; `scale` is the
explicit QE-loss allowance before the final `epsilon / 2` Borda stage.  The
next theorem specializes this flexible finite budget to the proved source-rate
form. -/
theorem theorem8_bordaMaxing_sequentialQEPolicy_geometricEnvelope_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (roundCount : ℕ) (epsilon delta scale : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (haccuracy : scale /
      (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2 + epsilon / 2 ≤
        epsilon) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
      roundCount
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeTotalBudgetRequirement
        (Fintype.card Arm) roundCount (delta / 2) scale)
      (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon procedure := by
  classical
  dsimp
  let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
    roundCount
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeTotalBudgetRequirement
      (Fintype.card Arm) roundCount (delta / 2) scale)
    (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
  change 1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
    winProbability hprobability epsilon procedure
  rw [adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability]
  unfold ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
  have hsource :=
    ZhouChenLi2014OptimalPACMultipleArm.sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricEnvelopeBudget
      (bordaScore winProbability)
      (bordaScore_validBernoulliMeans winProbability hprobability)
      roundCount (delta / 2) (epsilon / 2) (delta / 2) epsilon scale
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hscale haccuracy
  rw [pmfProbClassical_eq_pmfProb, pmfProb_map] at hsource
  simpa [procedure, EpsilonBordaMaximum] using hsource

/-- Theorem 8 through Zhou--Chen--Li's explicit source-rate budget.  The QE
allocation is bounded by the source's live-round geometric rate and the final
uniform Borda stage receives the other half of the accuracy and confidence
budgets. -/
theorem theorem8_bordaMaxing_sequentialQEPolicy_geometricRate_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (roundCount : ℕ) (epsilon delta scale : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (haccuracy : scale /
      (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2 + epsilon / 2 ≤
        epsilon) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
      roundCount
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
        (Fintype.card Arm) (delta / 2) scale)
      (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon procedure := by
  classical
  dsimp
  let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
    roundCount
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
      (Fintype.card Arm) (delta / 2) scale)
    (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
  change 1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
    winProbability hprobability epsilon procedure
  rw [adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability]
  unfold ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
  have hsource :=
    ZhouChenLi2014OptimalPACMultipleArm.sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricRateBudget
      (bordaScore winProbability)
      (bordaScore_validBernoulliMeans winProbability hprobability)
      roundCount (delta / 2) (epsilon / 2) (delta / 2) epsilon scale
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hscale haccuracy
  rw [pmfProbClassical_eq_pmfProb, pmfProb_map] at hsource
  simpa [procedure, EpsilonBordaMaximum] using hsource

/-- Theorem 8 with Zhou--Chen--Li's paper-parameter source-rate policy.  The
only public accuracy and confidence parameters are the source `epsilon` and
`delta`; the QE/final split is fixed internally. -/
theorem theorem8_bordaMaxing_sequentialQEPolicy_sourceRate_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (roundCount : ℕ) (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
      roundCount
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
        (Fintype.card Arm) (delta / 2)
        (epsilon / 2 *
          (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2))
      (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon procedure := by
  classical
  dsimp
  let procedure := ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalProcedure
    roundCount
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
      (Fintype.card Arm) (delta / 2)
      (epsilon / 2 *
        (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2))
    (Finset.univ : Finset Arm) Finset.univ_nonempty (epsilon / 2) (delta / 2)
  change 1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
    winProbability hprobability epsilon procedure
  rw [adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability]
  unfold ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
  have hsource :=
    ZhouChenLi2014OptimalPACMultipleArm.sourceQE_sequentialUniformFinalProcedure_finitePAC_of_sourceRateBudget
      (bordaScore winProbability)
      (bordaScore_validBernoulliMeans winProbability hprobability)
      roundCount epsilon delta hepsilon hdelta hdeltaLeOne
  rw [pmfProbClassical_eq_pmfProb, pmfProb_map] at hsource
  simpa [procedure, EpsilonBordaMaximum] using hsource

/-- The resource half of Theorem 8's source-rate reduction.  Each pull of
the displayed QE policy is one uniform-opponent Borda comparison, so the
unpadded history-selected execution has the same explicit source-rate bound
as Zhou--Chen--Li's Bernoulli implementation. -/
theorem theorem8_bordaMaxing_sequentialQEPolicy_sourceRate_execution_comparisons_le
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (roundCount : ℕ) (epsilon delta : ℝ)
    (qeHistory : Fin (Fintype.card
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialSlot roundCount
        (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
          (Fintype.card Arm) (delta / 2)
          (epsilon / 2 *
            (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2)))) → Bool)
    (hroundCount : Fintype.card Arm ≤ roundCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialUniformFinalPullCount
      roundCount
      (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
        (Fintype.card Arm) (delta / 2)
        (epsilon / 2 *
          (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2))
      (Finset.univ : Finset Arm) qeHistory (epsilon / 2) (delta / 2) : ℝ) ≤
      ZhouChenLi2014OptimalPACMultipleArm.sourceQESequentialUniformFinalRateCoefficient *
        Fintype.card Arm * (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
  classical
  simpa [Finset.card_univ] using
    (ZhouChenLi2014OptimalPACMultipleArm.sourceQE_terminal_execution_pullCount_real_le_sourceRateForm
      roundCount (Finset.univ : Finset Arm) epsilon delta qeHistory Finset.univ_nonempty
      hroundCount hepsilon hepsilonLeOne hdelta hdeltaLeOne)

/--
Main Theorem 8 in source-facing algorithm-existence form. One universal
constant works for every finite arm set and every valid accuracy/confidence
pair. The witness is an adaptive uniform-opponent comparison algorithm whose
unpadded realized comparison count obeys the displayed source-rate envelope.
-/
theorem theorem8_bordaMaxing_sourceRate_exists :
    ∃ coefficient : ℝ,
      ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
        (epsilon delta : ℝ),
        0 < epsilon → epsilon ≤ 1 → 0 < delta → delta ≤ 1 →
        ∃ algorithm : FiniteAdaptiveBordaMaxingAlgorithm Arm,
          ∀ (winProbability : Arm → Arm → ℝ),
            ∀ hprobability : BordaWinProbabilities winProbability,
            1 - delta ≤ finiteAdaptiveBordaMaxingSuccessProbability
              winProbability hprobability epsilon algorithm ∧
            ∀ rewards,
              (algorithm.executionComparisonCount rewards : ℝ) ≤
                coefficient * Fintype.card Arm *
                  (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
  classical
  refine ⟨ZhouChenLi2014OptimalPACMultipleArm.sourceQESequentialUniformFinalRateCoefficient, ?_⟩
  intro Arm _ _ epsilon delta hepsilon hepsilonLeOne hdelta hdeltaLeOne
  let algorithm := theorem8BordaMaxingSourceRateAlgorithm
    (Arm := Arm) (Fintype.card Arm) epsilon delta
  refine ⟨algorithm, ?_⟩
  intro winProbability hprobability
  constructor
  · simpa [algorithm, theorem8BordaMaxingSourceRateAlgorithm,
      finiteAdaptiveBordaMaxingSuccessProbability] using
      (theorem8_bordaMaxing_sequentialQEPolicy_sourceRate_highProbability
        winProbability hprobability (Fintype.card Arm) epsilon delta
        hepsilon hdelta hdeltaLeOne)
  · intro rewards
    simpa [algorithm, theorem8BordaMaxingSourceRateAlgorithm] using
      (theorem8_bordaMaxing_sequentialQEPolicy_sourceRate_execution_comparisons_le
        (Arm := Arm) (Fintype.card Arm) epsilon delta
        (ZhouChenLi2014OptimalPACMultipleArm.rewardTracePrefix
          (Fintype.card
            (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceSequentialSlot
              (Fintype.card Arm)
              (ZhouChenLi2014OptimalPACMultipleArm.quartileSourceGeometricEnvelopeRateBudget
                (Fintype.card Arm) (delta / 2)
                (epsilon / 2 *
                  (1 - ZhouChenLi2014OptimalPACMultipleArm.quartileSourceFailureDecay) ^ 2))))
          (ZhouChenLi2014OptimalPACMultipleArm.quartileUniformFinalMaxPullBudget
            Arm (epsilon / 2) (delta / 2)) rewards)
        (le_refl _) hepsilon hepsilonLeOne hdelta hdeltaLeOne)

/--
Theorem 9's concrete uniform-opponent sampler returns an epsilon-Borda
ranking with failure probability at most `delta` when its empirical-score
ordering is used.
-/
theorem theorem9_bordaRanking_uniformSampler_failure_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    (canonicalBordaBatchLaw winProbability hprobability
      (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
      {labelTable | ¬ EpsilonBordaRanking winProbability epsilon
        (empiricalBordaRanking (fun arm => bordaEmpiricalScore
          (canonicalBordaBatchObservation
            (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable))} ≤ delta := by
  classical
  exact canonicalEmpiricalBordaRanking_failure_probability
    winProbability hprobability epsilon delta Fintype.card_pos hepsilon hdelta hdeltaLeOne

/--
Theorem 9's exact all-arms Borda sampling total has the fixed-parameter
`O(n log n)` source rate.
-/
theorem theorem9_bordaRanking_sourceTotalSampleCount_isBigO_n_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ => (bordaTotalSampleCount armCount epsilon delta : ℝ))
      (fun armCount : ℕ => (armCount : ℝ) * Real.log (armCount : ℝ)) :=
  bordaTotalSampleCount_isBigO_n_mul_log hepsilon hdelta hdeltaLeOne

/-- Theorem 9's exact all-arm ceiling budget has an explicit source-rate
envelope throughout the source parameter range. -/
theorem theorem9_bordaRanking_sourceTotalSampleCount_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
      3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 :=
  bordaTotalSampleCount_real_le_sourceRateForm armCount epsilon delta harmCount
    hepsilon hepsilonLeOne hdelta hdeltaLeOne

/-- Appendix B.2 / Lemma 20's source-facing probability conclusion for the
literal threshold-selection execution. Each pair-estimate tail remains
explicit here; the next source boundary is their canonical unordered-batch
joint law, not a caller-supplied output-ranking certificate. -/
theorem lemma20_strongTransitivityRanking_thresholdOutput_highProbability
    {Arm Outcome : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (preferenceGap : Arm → Arm → ℝ)
    (estimate : Outcome → Arm → Arm → ℝ) (epsilon delta : ℝ)
    (sourceRanking : Fin (Fintype.card Arm) → Arm)
    (hsourceRanking : PreferenceRanking preferenceGap sourceRanking)
    (hfailure : ∀ pair : Arm × Arm,
      pmfProbClassical law (PairwiseEstimateFailure preferenceGap estimate epsilon pair) ≤
        delta / (Fintype.card (Arm × Arm) : ℝ)) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => EpsilonPreferenceRanking preferenceGap epsilon
        (strongTransitivityRankingOutput (estimate outcome) epsilon)) :=
  strongTransitivityRankingOutput_success_probability_of_pairEstimateGuarantees
    law preferenceGap estimate epsilon delta sourceRanking hsourceRanking hfailure

/-- Appendix B.2 / Lemmas 19--20 under the source's actual all-pairs
sampling experiment.  Each unordered distinct pair is sampled exactly once
at Algorithm 6's ceiling budget; the reverse estimate is a complement rather
than a second independent batch.  The concrete Algorithm-7 recursion then
returns an `epsilon`-ranking with probability at least `1 - delta`. -/
theorem lemma20_strongTransitivityRanking_canonicalUnorderedBatches_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (sourceRanking : Fin (Fintype.card Arm) → Arm)
    (hsourceRanking : PreferenceRanking preferenceGap sourceRanking)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta ≤ pmfProbClassical
      (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta)
      (fun batchTable => EpsilonPreferenceRanking preferenceGap epsilon
        (strongTransitivityRankingOutput
          (canonicalStrongTransitivityRankingEstimate epsilon delta batchTable) epsilon)) :=
  canonicalStrongTransitivityRankingOutput_highProbability preferenceGap hprobability epsilon delta
    sourceRanking hsourceRanking hantisymmetric hcard hepsilon hdelta hdeltaLeOne

/-- At fixed positive accuracy and valid confidence, Lemma 20's exact
unordered-pair comparison count is `O(n² log n)`.  The finite predecessor
retains the source's `epsilon` and `delta` dependence explicitly. -/
theorem lemma20_strongTransitivityRanking_sourceComparisonCount_isBigO_n_sq_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ =>
        (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ))
      (fun armCount : ℕ => (armCount : ℝ) ^ 2 * Real.log (armCount : ℝ)) :=
  strongTransitivityComparisonCount_isBigO_n_sq_mul_log hepsilon hdelta hdeltaLeOne

/-- Lemma 20's exact unordered-pair cost has one explicit all-parameter
source-rate envelope.  The additive one inside the confidence logarithm
retains the finite ceiling term at `delta = 1`. -/
theorem lemma20_strongTransitivityRanking_sourceComparisonCount_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
      5 * (armCount : ℝ) ^ 2 *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 :=
  strongTransitivityComparisonCount_real_le_sourceRateForm armCount epsilon delta harmCount
    hepsilon hepsilonLeOne hdelta hdeltaLeOne

/--
Theorem 2 / Appendix A.3, conditional form: all validated Compare calls make
Seq-Eliminate return an `ε`-maximum under the paper's SST and no-draw model.
-/
theorem seqEliminate_correct_of_validCompareCalls {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    EpsilonMaximum preferenceGap epsilon (sequentialEliminate step initial challengers) :=
  sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon step hantisymmetric
    hsst hepsilon hvalid maximum initial challengers hmaximum happears

/--
For fixed positive accuracy and valid confidence, Theorem 2's exact source
ceiling envelope is `O(n log n)`.  Its finite stopping-time bridge retains one
per-call confidence `δ / n`, as in Seq-Eliminate itself.
-/
theorem theorem2_seqEliminate_sourceEnvelope_isBigO_n_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ => seqEliminateSourceComparisonEnvelope armCount epsilon delta)
      (fun armCount : ℕ => (armCount : ℝ) * Real.log (armCount : ℝ)) :=
  seqEliminateSourceComparisonEnvelope_isBigO_n_mul_log hepsilon hdelta hdeltaLeOne

/-- Theorem 2's ceiling-corrected source resource envelope has an explicit
all-parameter rate.  The shifted logarithm retains the finite endpoint at
`delta = 1`; the exact adaptive stopping-time theorem above feeds into this
envelope. -/
theorem theorem2_seqEliminate_sourceEnvelope_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    seqEliminateSourceComparisonEnvelope armCount epsilon delta ≤
      3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 :=
  seqEliminateSourceComparisonEnvelope_real_le_sourceRateForm armCount epsilon delta harmCount
    hepsilon hepsilonLeOne hdelta hdeltaLeOne

/--
Lemma 3's literal Pick-Anchor comparison count is bounded uniformly by a
finite source-parameter expression.  The `+ 1` terms retain the source's
integral sample ceiling and make the rate valid at `delta = 1`.
-/
theorem lemma3_pickAnchor_sourceComparisonCap_real_le_sourceRateForm
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (epsilon delta : ℝ)
    (hcutoff : 0 < cutoff) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      5 *
          ((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) *
        (1 + Real.log
          (((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) / delta)) /
        epsilon ^ 2 :=
  pickAnchorSource_ceilingComparisonCap_real_le_sourceRateForm cutoff epsilon delta hcutoff
    hepsilon hepsilonLeOne hdelta hdeltaLeOne

/--
At the rounded source cutoff used by Algorithm 3, Lemma 3's exact
ceiling-corrected Pick-Anchor comparison envelope is `o(n)` at fixed positive
accuracy and valid confidence.  This is a one-parameter specialization of the
source's broader two-parameter display, not a replacement for that display.
-/
theorem lemma3_pickAnchor_sourceCutoffComparisonEnvelope_isLittleO_linear
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (fun armCount : ℕ =>
      sourceOptMaximizePickAnchorComparisonEnvelope armCount epsilon delta) =o[Filter.atTop]
      fun armCount : ℕ => (armCount : ℝ) :=
  sourceOptMaximizePickAnchorComparisonEnvelope_isLittleO_linear
    hepsilon hdelta hdeltaLeOne

/--
At Algorithm 3's rounded source cutoff, Lemma 15's sharp finite Prune cost
envelope is `O(n)` at fixed positive normalized confidence.  The theorem
retains the source's geometric bad-arm term; it does not claim the paper's
general multivariate asymptotic display.
-/
theorem lemma15_prune_sourceCutoffEnvelope_isBigO_linear
    {lower upper delta : ℝ} (hdelta : 0 < delta) (_hdeltaHalf : delta ≤ 1 / 2) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ => sourceLemma15PruneRateEnvelope armCount lower upper delta)
      (fun armCount : ℕ => (armCount : ℝ)) :=
  sourceLemma15PruneRateEnvelope_isBigO_linear hdelta

/--
Lemma 15's printed resource form, made precise as a uniform asymptotic bound
over any valid sequence of confidence and accuracy-gap parameters.  The
source's cutoff--confidence condition remains part of its probability
theorem; this result is the corresponding comparison-envelope statement.
-/
theorem lemma15_prune_sourceCutoffEnvelope_isBigO_parametric_sourceRateShape
    (lower upper delta : ℕ → ℝ)
    (hparameters : ∀ᶠ armCount : ℕ in Filter.atTop,
      0 < upper armCount - lower armCount ∧ upper armCount - lower armCount ≤ 1 ∧
        0 < delta armCount ∧ delta armCount ≤ 1 / 2) :
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceLemma15PruneRateEnvelope armCount (lower armCount) (upper armCount)
          (delta armCount))
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta armCount)) /
          (upper armCount - lower armCount) ^ 2) :=
  sourceLemma15PruneRateEnvelope_isBigO_parametric_sourceRateShape
    lower upper delta hparameters

/--
Lemma 3 / Appendix A.5 with the source's exact uniform-without-replacement
Pick-Anchor sampler.  A tie-safe top set of the stated cutoff is hit with
failure at most `δ / 2`; if the sampled Seq-Eliminate winner has its stated
`ε`-maximum guarantee with the remaining `δ / 2` budget, the output is an
`(ε, cutoff)`-good anchor with probability at least `1 - δ`.
-/
theorem pickAnchor_goodAnchor_highProbability_of_uniformSampleAndWinner
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (top : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (winner : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hcutoff : 0 < cutoff) (htopCard : top.card = cutoff)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hwinnerFailure : pmfProbClassical
      (pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
        -epsilon ≤ preferenceGap (winner sample) arm) ≤ delta / 2) :
    1 - delta ≤ pmfProbClassical
      (pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => GoodAnchor preferenceGap epsilon cutoff (winner sample)) :=
  pickAnchor_goodAnchor_probability_of_uniformSample_and_sampleWinner cutoff delta epsilon top
    preferenceGap winner hantisymmetric hsst hepsilon hcutoff htopCard htopRank hdeltaPos hdeltaLe
    hwinnerFailure

/--
Lemma 3's sampled Seq-Eliminate subroutine, conditional on the source's
all-pair adaptive-Compare validity event.  The conclusion ranges only over
the realized uniform-without-replacement sample, and the maximum witness is
therefore sample-local rather than a global arm.
-/
theorem pickAnchor_sampleWinner_is_sampleEpsilonMaximum_of_validAdaptiveCalls
    {Arm Ω : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (observation : Arm → Arm → ℕ → Ω → ℝ) (budget : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : ∀ incumbent challenger,
      AdaptiveCompareStepCallValid observation budget preferenceGap epsilon delta outcome
        incumbent challenger)
    (maximum : Arm)
    (hmaximumMem : maximum ∈ pickAnchorSampleSet sample)
    (hmaximum : ∀ arm ∈ pickAnchorSampleSet sample,
      0 ≤ preferenceGap maximum arm) :
    ∀ arm ∈ pickAnchorSampleSet sample,
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation budget epsilon delta outcome) sample hcount) arm :=
  pickAnchorSample_adaptiveSeqEliminate_epsilonMaximum_of_allPairCallValid
    sample hcount observation budget preferenceGap epsilon delta outcome
    hantisymmetric hsst hepsilon hvalid maximum hmaximumMem hmaximum

/--
Lemma 3's source-level probability composition on a joint experiment whose
outcome contains both the fresh sample and the comparison randomness.  The
two explicit premises are exactly the uniform-sample top-hit and sampled
Seq-Eliminate failure bounds, each allocated `δ / 2` in Appendix A.5.
-/
theorem pickAnchor_goodAnchor_highProbability_of_jointExperiment
    {Arm Ω : Type*} [Fintype Arm] [DecidableEq Arm] [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : Ω → Finset Arm) (winner : Ω → Arm)
    (top : Finset Arm) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (delta : ℝ)
    (hmiss : law.real {outcome | ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome} ≤ delta / 2)
    (hwinnerFailure : law.real {outcome | ¬ ∀ arm ∈ sample outcome,
      -epsilon ≤ preferenceGap (winner outcome) arm} ≤ delta / 2)
    (hgoodMeasurable : MeasurableSet {outcome |
      GoodAnchor preferenceGap epsilon cutoff (winner outcome)}) :
    1 - delta ≤ law.real {outcome |
      GoodAnchor preferenceGap epsilon cutoff (winner outcome)} :=
  pickAnchor_goodAnchor_measure_probability_of_topSetHit_and_sampleWinner
    law sample winner top preferenceGap epsilon cutoff hantisymmetric hsst hepsilon htopRank delta
    hmiss hwinnerFailure hgoodMeasurable

end FalahatgarEtAl2017MaxingRanking
