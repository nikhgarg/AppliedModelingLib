import FalahatgarEtAl2017MaxingRanking.CanonicalBordaBatches
import ZhouChenLi2014OptimalPACMultipleArm.PaperInterface
import ZhouChenLi2014OptimalPACMultipleArm.UniformBatchPolicy

/-!
# The Borda-evaluation / Bernoulli-bandit bridge

Falahatgar et al.'s maximum-selection reduction evaluates an arm by choosing a
uniform opponent and observing the comparison outcome.  This file proves that
one such evaluation has exactly the Bernoulli law whose mean is the arm's Borda
score.  It is the source-to-model bridge used for the cited PAC best-arm
selection result in Theorem 8.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem bordaScore_validBernoulliMeans {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) :
    ZhouChenLi2014OptimalPACMultipleArm.ValidBernoulliMeans
      (bordaScore winProbability) := by
  intro arm
  unfold bordaScore
  have hcard : 0 < (Fintype.card Arm : ℝ) := by positivity
  constructor
  · exact div_nonneg
      (Finset.sum_nonneg fun opponent _ => (hprobability arm opponent).1) hcard.le
  · rw [div_le_iff₀ hcard]
    calc
      ∑ opponent : Arm, winProbability arm opponent ≤ ∑ _opponent : Arm, (1 : ℝ) :=
        Finset.sum_le_sum fun opponent _ => (hprobability arm opponent).2
      _ = 1 * (Fintype.card Arm : ℝ) := by simp

theorem canonicalBordaTrialLaw_apply_true_toReal {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (arm : Arm) :
    (canonicalBordaTrialLaw winProbability hprobability arm true).toReal =
      bordaScore winProbability arm := by
  classical
  calc
    (canonicalBordaTrialLaw winProbability hprobability arm true).toReal =
        (canonicalBordaTrialLaw winProbability hprobability arm).toMeasure[binaryRatingScore] := by
      rw [PMF.integral_eq_sum]
      simp [binaryRatingScore]
    _ = bordaScore winProbability arm :=
      integral_canonicalBordaTrialLaw winProbability hprobability arm

theorem canonicalBordaTrialLaw_eq_bernoulliRewardLaw {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (arm : Arm) :
    canonicalBordaTrialLaw winProbability hprobability arm =
      ZhouChenLi2014OptimalPACMultipleArm.bernoulliRewardLaw
        (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability) arm := by
  classical
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((canonicalBordaTrialLaw winProbability hprobability arm).apply_ne_top outcome)
    ((ZhouChenLi2014OptimalPACMultipleArm.bernoulliRewardLaw
      (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
      arm).apply_ne_top outcome)).mp
  have htrue := canonicalBordaTrialLaw_apply_true_toReal winProbability hprobability arm
  have htargetTrue :
      (ZhouChenLi2014OptimalPACMultipleArm.bernoulliRewardLaw
        (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
        arm true).toReal = bordaScore winProbability arm := by
    unfold ZhouChenLi2014OptimalPACMultipleArm.bernoulliRewardLaw
    rw [PMF.bernoulli_apply]
    rfl
  cases outcome with
  | false =>
      have hsource := pmfToRealSum (canonicalBordaTrialLaw winProbability hprobability arm)
      have htarget := pmfToRealSum
        (ZhouChenLi2014OptimalPACMultipleArm.bernoulliRewardLaw
          (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
          arm)
      simp only [Fintype.sum_bool] at hsource htarget
      nlinarith
  | true => exact htrue.trans htargetTrue.symm

/--
The finite reward law obtained when an adaptive best-arm policy receives the
source Borda evaluation after each history-selected pull.
-/
noncomputable def adaptiveCanonicalBordaRewardPrefixLaw {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    {pullBudget : ℕ} (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) :
    (roundCount : ℕ) → (hroundCount : roundCount ≤ pullBudget) →
      PMF (Fin roundCount → Bool)
  | 0, _ => PMF.pure Fin.elim0
  | roundCount + 1, hroundCount =>
      PMF.bind
        (adaptiveCanonicalBordaRewardPrefixLaw winProbability hprobability procedure roundCount
          (Nat.le_of_succ_le hroundCount))
        (fun history =>
          PMF.map (fun reward => Fin.snoc history reward)
            (canonicalBordaTrialLaw winProbability hprobability
              (procedure.pull ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ history)))

/-- The full source Borda reward trace for a finite adaptive best-arm policy. -/
noncomputable def adaptiveCanonicalBordaRewardLaw {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    {pullBudget : ℕ} (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) : PMF (Fin pullBudget → Bool) :=
  adaptiveCanonicalBordaRewardPrefixLaw winProbability hprobability procedure pullBudget (le_refl _)

/--
The source adaptive Borda sampler is exactly the adaptive Bernoulli model with
mean vector equal to the Borda scores, including the dependence of each pull
on all earlier rewards.
-/
theorem adaptiveCanonicalBordaRewardPrefixLaw_eq_adaptiveBernoulliRewardPrefixLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] {pullBudget : ℕ}
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ pullBudget),
      adaptiveCanonicalBordaRewardPrefixLaw winProbability hprobability procedure roundCount hroundCount =
        ZhouChenLi2014OptimalPACMultipleArm.adaptiveBernoulliRewardPrefixLaw
          (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
          procedure roundCount hroundCount := by
  classical
  intro roundCount
  induction roundCount with
  | zero =>
      intro _
      rfl
  | succ roundCount ih =>
      intro hroundCount
      rw [adaptiveCanonicalBordaRewardPrefixLaw,
        ZhouChenLi2014OptimalPACMultipleArm.adaptiveBernoulliRewardPrefixLaw]
      rw [ih (Nat.le_of_succ_le hroundCount)]
      congr 1
      funext history
      rw [canonicalBordaTrialLaw_eq_bernoulliRewardLaw]

theorem adaptiveCanonicalBordaRewardLaw_eq_adaptiveBernoulliRewardLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] {pullBudget : ℕ}
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) :
    adaptiveCanonicalBordaRewardLaw winProbability hprobability procedure =
      ZhouChenLi2014OptimalPACMultipleArm.adaptiveBernoulliRewardLaw
        (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
        procedure := by
  exact adaptiveCanonicalBordaRewardPrefixLaw_eq_adaptiveBernoulliRewardPrefixLaw
    winProbability hprobability procedure pullBudget (le_refl _)

/--
The exact probability that a finite adaptive policy returns an
`epsilon`-Borda maximum under the source comparison sampler.
-/
noncomputable def adaptiveCanonicalBordaSuccessProbability {Arm : Type*}
    [Fintype Arm] [Nonempty Arm] {pullBudget : ℕ}
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (epsilon : ℝ)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) : ℝ := by
  classical
  letI : DecidablePred (fun rewards =>
    EpsilonBordaMaximum winProbability epsilon (procedure.output rewards)) := Classical.decPred _
  exact pmfProb (adaptiveCanonicalBordaRewardLaw winProbability hprobability procedure)
    (fun rewards => EpsilonBordaMaximum winProbability epsilon (procedure.output rewards))

/--
An adaptive Borda-maxing algorithm together with the number of comparisons
used by each realized execution. The finite policy fixes the history-dependent
arm pulls and returned arm; `executionComparisonCount` records the unpadded
source execution rather than any inert trace padding used to give Lean one
finite reward-vector type.
-/
structure FiniteAdaptiveBordaMaxingAlgorithm (Arm : Type*) where
  pullBudget : ℕ
  procedure :
    ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget
  executionComparisonCount : (Fin pullBudget → Bool) → ℕ
  executionComparisonCount_le_pullBudget :
    ∀ rewards, executionComparisonCount rewards ≤ pullBudget
  executionComparisonCount_stable :
    ∀ rewards alternative,
      (∀ round, round.val < executionComparisonCount rewards →
        alternative round = rewards round) →
      executionComparisonCount alternative = executionComparisonCount rewards
  output_stable_through_execution :
    ∀ rewards alternative,
      (∀ round, round.val < executionComparisonCount rewards →
        alternative round = rewards round) →
      procedure.output alternative = procedure.output rewards

/-- The success probability of an abstract adaptive Borda-maxing algorithm. -/
noncomputable def finiteAdaptiveBordaMaxingSuccessProbability {Arm : Type*}
    [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability) (epsilon : ℝ)
    (algorithm : FiniteAdaptiveBordaMaxingAlgorithm Arm) : ℝ :=
  adaptiveCanonicalBordaSuccessProbability winProbability hprobability epsilon
    algorithm.procedure

/--
The adaptive source Borda success probability is definitionally the finite
Bernoulli best-arm success probability after the proved law identification.
-/
theorem adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] {pullBudget : ℕ}
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon : ℝ)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget) :
    adaptiveCanonicalBordaSuccessProbability winProbability hprobability epsilon procedure =
      ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
        (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
        epsilon procedure := by
  classical
  unfold adaptiveCanonicalBordaSuccessProbability
    ZhouChenLi2014OptimalPACMultipleArm.finiteBestArmSuccessProbability
  rw [adaptiveCanonicalBordaRewardLaw_eq_adaptiveBernoulliRewardLaw]
  congr 1

/--
Any verified finite PAC best-arm procedure immediately gives the finite
source-model statement used by Falahatgar et al.'s Theorem 8 reduction.
-/
theorem adaptiveCanonicalBordaSuccessProbability_of_finitePACBestArmGuarantee
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] {pullBudget : ℕ}
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ)
    (procedure : ZhouChenLi2014OptimalPACMultipleArm.FiniteAdaptiveBernoulliBestArmProcedure
      Arm pullBudget)
    (hguarantee : ZhouChenLi2014OptimalPACMultipleArm.FinitePACBestArmGuarantee
      (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
      epsilon delta procedure) :
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon procedure := by
  rw [adaptiveCanonicalBordaSuccessProbability_eq_finiteBestArmSuccessProbability]
  exact hguarantee

/--
An explicit finite Borda-maxing procedure: replay Zhou--Chen--Li's verified
uniform final batch as a sequential policy and evaluate every pull through the
source's uniform-opponent comparison sampler.  This closes the qualitative
Theorem-8 reduction with a conservative all-arms resource bound; the cited
paper's sharper QE resource rate is formalized separately.
-/
theorem adaptiveCanonicalBordaSuccessProbability_uniformBernoulliBatchProcedure
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta ≤ adaptiveCanonicalBordaSuccessProbability
      winProbability hprobability epsilon
      (ZhouChenLi2014OptimalPACMultipleArm.uniformBernoulliBatchProcedure (Arm := Arm)
        (ZhouChenLi2014OptimalPACMultipleArm.uniformBernoulliBatchSampleBudget
          (Fintype.card Arm) epsilon delta)) := by
  apply adaptiveCanonicalBordaSuccessProbability_of_finitePACBestArmGuarantee
    winProbability hprobability epsilon delta
  exact ZhouChenLi2014OptimalPACMultipleArm.finitePACBestArmGuarantee_uniformBernoulliBatchProcedure
      (bordaScore winProbability) (bordaScore_validBernoulliMeans winProbability hprobability)
      epsilon delta hepsilon hdelta hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
