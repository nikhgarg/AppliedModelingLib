import ZhouChenLi2014OptimalPACMultipleArm.CanonicalFreshQuartileRounds
import ZhouChenLi2014OptimalPACMultipleArm.QuartileTermination
import ZhouChenLi2014OptimalPACMultipleArm.QuartileAllocation
import ZhouChenLi2014OptimalPACMultipleArm.QuartileBudgetRounds
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSourceSchedule
import ZhouChenLi2014OptimalPACMultipleArm.QuartileDirectBudget
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSequentialSlots
import ZhouChenLi2014OptimalPACMultipleArm.QuartileBatchPolicy
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSequentialPolicy
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSourceUniformFinal
import ZhouChenLi2014OptimalPACMultipleArm.QuartileSequentialUniformFinal
import ZhouChenLi2014OptimalPACMultipleArm.UniformBatchPolicy

/-!
# Zhou--Chen--Li (2014): exposed theorem surface

The current surface fixes the finite adaptive Bernoulli experiment to which
the paper's `K = 1` best-arm theorem applies.  A conservative uniform final
batch is proved equal to a concrete finite sequential policy and is
`epsilon`-PAC. The fresh QE probability layer is instantiated on concrete
Bernoulli batches and, with an explicit finite accuracy-budget convention,
composes with the uniform final batch on one PMF. The literal combined
sequential policy's returned-arm PMF is identified with that experiment. Its
source-form resource rate is proved for the exact unpadded execution. The
source's implicit quartile tie convention is formalized with the
author-approved deterministic tie-breaking clarification recorded in the
paper-local source record.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL

/--
Finite `K = 1` source-QE correctness followed by the supplement's uniform
final stage. The geometric confidence/allocation shapes are source-visible;
the integer accuracy ceiling is the documented formalizer convention in
`QuartileAccuracyBudget`, not a recovered hidden big-O constant.
-/
theorem sourceQE_uniformFinal_finitePAC_of_accuracyBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonQE : 0 < epsilonQE) (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (haccuracy : epsilonQE + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount
          (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
            roundCount epsilonQE deltaQE)
          Finset.univ deltaQE epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) :=
  quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_accuracyTotalBudget
    mean hmean roundCount deltaQE epsilonQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonQE hepsilonFinal hdeltaFinal hdeltaFinalLeOne haccuracy

/-- The same finite PAC bound when the QE portion is the literal sequential
source policy.  The conditional final kernel is the one with an independently
proved fixed-state sequential replay. -/
theorem sourceQE_sequentialPrefix_uniformFinal_finitePAC_of_accuracyBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonQE : 0 < epsilonQE) (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (haccuracy : epsilonQE + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceSequentialUniformFinalJointLaw mean hmean
          (quartileSourceError
            (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
              roundCount epsilonQE deltaQE)
            (Fintype.card Arm) deltaQE)
          roundCount
          (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
            roundCount epsilonQE deltaQE)
          Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  let sourceBudget := quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
    roundCount epsilonQE deltaQE
  have hsource : 1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceSequentialUniformFinalJointLaw mean hmean
          (quartileSourceError sourceBudget (Finset.univ : Finset Arm).card deltaQE)
          roundCount sourceBudget (Finset.univ : Finset Arm) Finset.univ_nonempty
          epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
    rw [quartileSourceSequentialUniformFinalJointLaw_eq_source]
    exact sourceQE_uniformFinal_finitePAC_of_accuracyBudget
      mean hmean roundCount deltaQE epsilonQE epsilonFinal deltaFinal epsilon
      hdeltaQE hdeltaQELeOne hepsilonQE hepsilonFinal hdeltaFinal hdeltaFinalLeOne haccuracy
  simpa [sourceBudget, Finset.card_univ] using hsource

/-- The finite PAC guarantee for one literal history-dependent procedure:
chronological source QE followed by the survivor-selected padded uniform final
stage.  Its output PMF is proved equal to the source joint experiment before
the existing finite source theorem is applied. -/
theorem sourceQE_sequentialUniformFinalProcedure_finitePAC_of_accuracyBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonQE : 0 < epsilonQE) (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (haccuracy : epsilonQE + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
              roundCount epsilonQE deltaQE)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
              roundCount epsilonQE deltaQE)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean epsilon) := by
  classical
  let sourceBudget := quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
    roundCount epsilonQE deltaQE
  let sourceError := quartileSourceError sourceBudget (Fintype.card Arm) deltaQE
  have hsource := sourceQE_sequentialPrefix_uniformFinal_finitePAC_of_accuracyBudget
    mean hmean roundCount deltaQE epsilonQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonQE hepsilonFinal hdeltaFinal hdeltaFinalLeOne haccuracy
  have hsourceOutput : 1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((quartileSourceSequentialUniformFinalJointLaw mean hmean sourceError roundCount
          sourceBudget (Finset.univ : Finset Arm) Finset.univ_nonempty
          epsilonFinal deltaFinal).map
          (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2))
        (EpsilonPACBestArm mean epsilon) := by
    rw [pmfProbClassical_eq_pmfProb] at hsource ⊢
    rw [pmfProb_map]
    simpa [sourceBudget, sourceError, Finset.card_univ] using hsource
  rw [adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_jointLaw_output
    mean hmean sourceError roundCount sourceBudget (Finset.univ : Finset Arm)
    Finset.univ_nonempty epsilonFinal deltaFinal]
  simpa [sourceBudget, sourceError, Finset.card_univ] using hsourceOutput

/-- End-to-end literal-policy PAC theorem that stops accumulating QE loss
once the deterministic three-arm terminal condition holds.  This is the
source-shaped numerical boundary for the sharp-rate proof: only positivity of
nonterminal floored allocations remains as a premise. -/
theorem sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilonFinal deltaFinal : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round (Fintype.card Arm) →
      0 < quartileSourceScheduledPerArmSampleCount totalBudget (Fintype.card Arm) round) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
            Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
            Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean
          ((∑ round ∈ Finset.range roundCount,
            2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round) +
              epsilonFinal)) := by
  classical
  have hsource := quartileSourceTerminalUniformFinalJoint_epsilonPAC_probability_ge_one_sub
    mean hmean roundCount totalBudget deltaQE epsilonFinal deltaFinal
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne hcount
  have hsourceOutput : 1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((quartileSourceTerminalUniformFinalJointLaw mean hmean roundCount totalBudget
          (Finset.univ : Finset Arm) deltaQE epsilonFinal deltaFinal).map
          (fun stateOutcome => canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2))
        (EpsilonPACBestArm mean
          ((∑ round ∈ Finset.range roundCount,
            2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round) +
              epsilonFinal)) := by
    rw [pmfProbClassical_eq_pmfProb] at hsource ⊢
    rw [pmfProb_map]
    simpa using hsource
  rw [adaptiveQuartileSourceSequentialUniformFinalProcedure_outputLaw_eq_terminalJoint_output
    mean hmean roundCount totalBudget (Finset.univ : Finset Arm) Finset.univ_nonempty
    deltaQE epsilonFinal deltaFinal]
  simpa using hsourceOutput

/-- Target-accuracy form of the terminal-aware literal-policy theorem. -/
theorem sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC_of_totalError
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round (Fintype.card Arm) →
      0 < quartileSourceScheduledPerArmSampleCount totalBudget (Fintype.card Arm) round)
    (haccuracy :
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round) +
          epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
            Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
            Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean epsilon) := by
  have hbase := sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC
    mean hmean roundCount totalBudget deltaQE epsilonFinal deltaFinal
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne hcount
  calc
    1 - (deltaQE + deltaFinal) ≤
        pmfProbClassical
          ((adaptiveBernoulliRewardLaw mean hmean
            (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
              Finset.univ_nonempty epsilonFinal deltaFinal)).map
            (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
              Finset.univ_nonempty epsilonFinal deltaFinal).output)
          (EpsilonPACBestArm mean
            ((∑ round ∈ Finset.range roundCount,
              2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round) +
                epsilonFinal)) := hbase
    _ ≤ pmfProbClassical
          ((adaptiveBernoulliRewardLaw mean hmean
            (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
              Finset.univ_nonempty epsilonFinal deltaFinal)).map
            (quartileSourceSequentialUniformFinalProcedure roundCount totalBudget Finset.univ
              Finset.univ_nonempty epsilonFinal deltaFinal).output)
          (EpsilonPACBestArm mean epsilon) := by
      apply pmfProbClassical_le_of_imp
      intro arm hpac
      exact epsilonPACBestArm_mono mean arm haccuracy hpac

/-- Fully specified terminal-aware finite PAC specialization.  The source
total is the maximum of direct geometric-envelope ceiling requirements; it
has no residual sample-count or accumulated-loss premise.  Proving that this
explicit total has the paper's sharp asymptotic form is the remaining rate
calculation. -/
theorem sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricEnvelopeBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonFinal deltaFinal epsilon scale : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hscale : 0 < scale)
    (haccuracy : scale / (1 - quartileSourceFailureDecay) ^ 2 + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeTotalBudgetRequirement (Fintype.card Arm)
              roundCount deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeTotalBudgetRequirement (Fintype.card Arm)
              roundCount deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean epsilon) := by
  apply sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC_of_totalError
    mean hmean roundCount
    (quartileSourceGeometricEnvelopeTotalBudgetRequirement (Fintype.card Arm)
      roundCount deltaQE scale)
    deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round hround _
    exact quartileSourceGeometricEnvelope_scheduledSampleCount_pos
      (Fintype.card Arm) roundCount deltaQE scale round Fintype.card_pos
      hdeltaQE hdeltaQELeOne hscale hround
  · have hsum := quartileSourceTerminalError_sum_le_closed_of_geometricTotalBudget
      (Fintype.card Arm) roundCount deltaQE scale Fintype.card_pos
      hdeltaQE hdeltaQELeOne hscale
    linarith

/-- Fully specified source-terminal finite PAC specialization.  Its direct
budget is maximized only over live QE rounds, matching the source stopping
rule; the fixed trace's later coordinates are inert replay padding. -/
theorem sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricNonterminalEnvelopeBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonFinal deltaFinal epsilon scale : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hscale : 0 < scale)
    (haccuracy : scale / (1 - quartileSourceFailureDecay) ^ 2 + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement (Fintype.card Arm)
              roundCount deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement (Fintype.card Arm)
              roundCount deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean epsilon) := by
  apply sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC_of_totalError
    mean hmean roundCount
    (quartileSourceGeometricEnvelopeNonterminalTotalBudgetRequirement (Fintype.card Arm)
      roundCount deltaQE scale)
    deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round hround hnonterminal
    apply quartileSourceGeometricEnvelope_scheduledSampleCount_pos_of_threshold
      _ (Fintype.card Arm) deltaQE scale round hdeltaQE hdeltaQELeOne hscale
    exact quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_nonterminalTotalBudget
      (Fintype.card Arm) roundCount deltaQE scale round Fintype.card_pos hround hnonterminal
  · have hsum := quartileSourceTerminalError_sum_le_closed_of_geometricNonterminalTotalBudget
      (Fintype.card Arm) roundCount deltaQE scale Fintype.card_pos
      hdeltaQE hdeltaQELeOne hscale
    linarith

/-- Corollary 4.4's finite source-rate specialization.  The literal policy
uses an explicit natural budget whose live QE rounds satisfy the source
geometric allocation, and whose terminal-aware loss plus uniform final stage
is `epsilon`-PAC. -/
theorem sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricRateBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonFinal deltaFinal epsilon scale : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hscale : 0 < scale)
    (haccuracy : scale / (1 - quartileSourceFailureDecay) ^ 2 + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeRateBudget (Fintype.card Arm) deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal)).map
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeRateBudget (Fintype.card Arm) deltaQE scale)
            Finset.univ Finset.univ_nonempty epsilonFinal deltaFinal).output)
        (EpsilonPACBestArm mean epsilon) := by
  apply sourceQE_sequentialUniformFinalProcedure_terminalError_finitePAC_of_totalError
    mean hmean roundCount
    (quartileSourceGeometricEnvelopeRateBudget (Fintype.card Arm) deltaQE scale)
    deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round _ hnonterminal
    apply quartileSourceGeometricEnvelope_scheduledSampleCount_pos_of_threshold
      _ (Fintype.card Arm) deltaQE scale round hdeltaQE hdeltaQELeOne hscale
    exact quartileSourceGeometricEnvelope_sampleThreshold_le_scheduledSampleCount_of_rateBudget
      (Fintype.card Arm) deltaQE scale round Fintype.card_pos
      hdeltaQE hdeltaQELeOne hscale hnonterminal
  · have hsum := quartileSourceTerminalError_sum_le_closed_of_geometricRateBudget
      (Fintype.card Arm) roundCount deltaQE scale Fintype.card_pos
      hdeltaQE hdeltaQELeOne hscale
    linarith

/-- The paper-parameter form of the source-rate policy: the QE envelope uses
half the total accuracy after accounting for its geometric sum, and the final
uniform stage uses the other half. -/
theorem sourceQE_sequentialUniformFinalProcedure_finitePAC_of_sourceRateBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta ≤
      pmfProbClassical
        ((adaptiveBernoulliRewardLaw mean hmean
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeRateBudget (Fintype.card Arm) (delta / 2)
              (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2))
            Finset.univ Finset.univ_nonempty (epsilon / 2) (delta / 2))).map
          (quartileSourceSequentialUniformFinalProcedure roundCount
            (quartileSourceGeometricEnvelopeRateBudget (Fintype.card Arm) (delta / 2)
              (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2))
            Finset.univ Finset.univ_nonempty (epsilon / 2) (delta / 2)).output)
        (EpsilonPACBestArm mean epsilon) := by
  have hdecayGap : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hscale : 0 < epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2 := by
    positivity
  have haccuracy :
      (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) /
          (1 - quartileSourceFailureDecay) ^ 2 + epsilon / 2 ≤ epsilon := by
    field_simp [hdecayGap.ne']; norm_num
  simpa using
    (sourceQE_sequentialUniformFinalProcedure_finitePAC_of_geometricRateBudget
      mean hmean roundCount (delta / 2) (epsilon / 2) (delta / 2) epsilon
      (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hscale haccuracy)

/-- Algorithm 1's QE prefix is now an actual history-dependent finite policy
whose horizon is bounded by the source's total QE allocation.  The separate
replay-law bridge identifies its reward trace with the already-checked fresh
QE batch PMF. -/
theorem sourceQE_sequentialPrefix_horizon_le_totalBudget
    (roundCount totalBudget : ℕ) :
    Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) ≤ totalBudget :=
  quartileSourceSequentialQEProcedure_pullBudget_le_totalBudget roundCount totalBudget

/-- Source Algorithm 1's unpadded execution cost at its finite terminal
condition.  The fixed-horizon replay policy has a larger inert suffix solely
for its common trace type; this theorem counts the actual history-selected
uniform final batch, whose survivor set has at most three arms. -/
theorem sourceQE_terminal_execution_pullCount_le
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (epsilon deltaFinal : ℝ) (hroundCount : initial.card ≤ roundCount) :
    quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        epsilon deltaFinal ≤
      totalBudget + quartileUniformFinalTerminalMaxPullBudget Arm epsilon deltaFinal :=
  quartileSourceSequentialUniformFinalPullCount_le_terminalMax roundCount totalBudget initial
    qeHistory epsilon deltaFinal hroundCount

/-- Cardinality-only resource form of the source terminal execution bound.
The final addend is a four-case maximum for terminal survivor counts, hence
has no dependence on the original arm cardinality. -/
theorem sourceQE_terminal_execution_pullCount_le_threeArmBudget
    {Arm : Type*} [Fintype Arm]
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) → Bool)
    (epsilon deltaFinal : ℝ) (hroundCount : initial.card ≤ roundCount) :
    quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        epsilon deltaFinal ≤
      totalBudget + quartileUniformFinalThreeArmPullBudget epsilon deltaFinal :=
  quartileSourceSequentialUniformFinalPullCount_le_threeArmBudget roundCount totalBudget initial
    qeHistory epsilon deltaFinal hroundCount

/-- End-to-end resource bound for the unpadded source execution at Corollary
4.4's paper parameters.  The first summand is the proved geometric QE rate;
the second is the proved four-case terminal final-batch ceiling bound.  Thus
the resource count follows the actual history-selected terminal batch rather
than the larger inertly padded replay horizon. -/
theorem sourceQE_terminal_execution_pullCount_real_le_sourceRatePlusTerminalCap
    {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (initial : Finset Arm) (epsilon delta : ℝ)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount
      (quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
        (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)))) → Bool)
    (hinitial : initial.Nonempty)
    (hroundCount : initial.card ≤ roundCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (quartileSourceSequentialUniformFinalPullCount roundCount
      (quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
        (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2))
      initial qeHistory (epsilon / 2) (delta / 2) : ℝ) ≤
      2 * quartileSourceGeometricEnvelopeRateCoefficient * initial.card *
          (1 + Real.log (1 / (delta / 2))) /
            (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 +
        3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) := by
  let totalBudget := quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
    (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)
  have hcount := sourceQE_terminal_execution_pullCount_le_threeArmBudget
    roundCount totalBudget initial qeHistory (epsilon / 2) (delta / 2) hroundCount
  have hcountReal :
      (quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        (epsilon / 2) (delta / 2) : ℝ) ≤
        (totalBudget : ℝ) +
          (quartileUniformFinalThreeArmPullBudget (epsilon / 2) (delta / 2) : ℝ) := by
    exact_mod_cast hcount
  have hqe := quartileSourceGeometricEnvelopeSourceRateBudget_real_le initial.card epsilon delta
    hinitial.card_pos hepsilon hepsilonLeOne hdelta hdeltaLeOne
  have hterminal := quartileUniformFinalThreeArmPullBudget_real_le
    (epsilon / 2) (delta / 2) (by linarith) (by linarith) (by linarith)
  calc
    (quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        (epsilon / 2) (delta / 2) : ℝ) ≤
        (totalBudget : ℝ) +
          (quartileUniformFinalThreeArmPullBudget (epsilon / 2) (delta / 2) : ℝ) := hcountReal
    _ ≤ 2 * quartileSourceGeometricEnvelopeRateCoefficient * initial.card *
          (1 + Real.log (1 / (delta / 2))) /
            (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 +
        3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) :=
      add_le_add hqe hterminal

/-- The explicit constant in the end-to-end source resource theorem.  Its
first term is the geometric QE coefficient at the source accuracy split; its
second term covers the terminal batch's three Hoeffding ceilings. -/
noncomputable def sourceQESequentialUniformFinalRateCoefficient : ℝ :=
  2 * quartileSourceGeometricEnvelopeRateCoefficient /
      ((1 / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2) +
    27 * (1 + Real.log 6)

/-- Corollary 4.4's source-rate resource theorem for the literal unpadded
execution.  The pathwise cost includes the QE pulls actually scheduled before
the deterministic three-arm terminal state and the selected terminal uniform
batch; it is bounded by one explicit `n / epsilon^2` positive-log envelope. -/
theorem sourceQE_terminal_execution_pullCount_real_le_sourceRateForm
    {Arm : Type*} [Fintype Arm]
    (roundCount : ℕ) (initial : Finset Arm) (epsilon delta : ℝ)
    (qeHistory : Fin (Fintype.card (quartileSourceSequentialSlot roundCount
      (quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
        (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)))) → Bool)
    (hinitial : initial.Nonempty)
    (hroundCount : initial.card ≤ roundCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (quartileSourceSequentialUniformFinalPullCount roundCount
      (quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
        (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2))
      initial qeHistory (epsilon / 2) (delta / 2) : ℝ) ≤
      sourceQESequentialUniformFinalRateCoefficient * initial.card *
        (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
  let rateScale : ℝ := (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2
  let qeCoefficient : ℝ :=
    2 * quartileSourceGeometricEnvelopeRateCoefficient /
      ((1 / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2)
  let terminalCoefficient : ℝ := 27 * (1 + Real.log 6)
  let totalBudget := quartileSourceGeometricEnvelopeRateBudget initial.card (delta / 2)
    (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2)
  have hsource := sourceQE_terminal_execution_pullCount_real_le_sourceRatePlusTerminalCap
    roundCount initial epsilon delta qeHistory hinitial hroundCount
    hepsilon hepsilonLeOne hdelta hdeltaLeOne
  have hgapPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hqeRewrite :
      2 * quartileSourceGeometricEnvelopeRateCoefficient * initial.card *
          (1 + Real.log (1 / (delta / 2))) /
            (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 =
        qeCoefficient * initial.card * rateScale := by
    dsimp [qeCoefficient, rateScale]
    field_simp [hepsilonSqPos.ne', hgapPos.ne']
  have hterminalEnvelope := quartileUniformFinalThreeArmEnvelope_real_le_sourceRateForm
    epsilon delta hepsilon hepsilonLeOne hdelta hdeltaLeOne
  have hterminalRewrite :
      27 * (1 + Real.log 6) * (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 =
        terminalCoefficient * rateScale := by
    dsimp [terminalCoefficient, rateScale]
    ring
  have hlogNonneg : 0 ≤ Real.log (1 / (delta / 2)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith : 0 < delta / 2)).mpr
    linarith
  have hrateScaleNonneg : 0 ≤ rateScale := by
    dsimp [rateScale]
    exact div_nonneg (by linarith) hepsilonSqPos.le
  have hterminalCoefficientNonneg : 0 ≤ terminalCoefficient := by
    dsimp [terminalCoefficient]
    have hlogSixNonneg : 0 ≤ Real.log 6 := by
      apply Real.log_nonneg
      norm_num
    positivity
  have hinitalCardGeOne : 1 ≤ (initial.card : ℝ) := by
    exact_mod_cast hinitial.card_pos
  have hterminalAbsorb : terminalCoefficient * rateScale ≤
      terminalCoefficient * initial.card * rateScale := by
    have hproductNonneg : 0 ≤ terminalCoefficient * rateScale :=
      mul_nonneg hterminalCoefficientNonneg hrateScaleNonneg
    nlinarith [mul_nonneg hproductNonneg (sub_nonneg.mpr hinitalCardGeOne)]
  have htotal :
      2 * quartileSourceGeometricEnvelopeRateCoefficient * initial.card *
          (1 + Real.log (1 / (delta / 2))) /
            (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 +
        3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) ≤
        qeCoefficient * initial.card * rateScale + terminalCoefficient * initial.card * rateScale := by
    rw [hqeRewrite]
    calc
      qeCoefficient * initial.card * rateScale +
          3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) ≤
        qeCoefficient * initial.card * rateScale + terminalCoefficient * rateScale := by
          apply add_le_add_right
          rw [← hterminalRewrite]
          exact hterminalEnvelope
      _ ≤ qeCoefficient * initial.card * rateScale +
          terminalCoefficient * initial.card * rateScale := by
          gcongr
  calc
    (quartileSourceSequentialUniformFinalPullCount roundCount totalBudget initial qeHistory
        (epsilon / 2) (delta / 2) : ℝ) ≤
        2 * quartileSourceGeometricEnvelopeRateCoefficient * initial.card *
          (1 + Real.log (1 / (delta / 2))) /
            (epsilon / 2 * (1 - quartileSourceFailureDecay) ^ 2) ^ 2 +
          3 * (2 / (epsilon / 2) ^ 2 * Real.log (6 / (delta / 2)) + 1) := by
      simpa [totalBudget] using hsource
    _ ≤ qeCoefficient * initial.card * rateScale + terminalCoefficient * initial.card * rateScale :=
      htotal
    _ = sourceQESequentialUniformFinalRateCoefficient * initial.card *
        (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2 := by
      dsimp [sourceQESequentialUniformFinalRateCoefficient, qeCoefficient,
        terminalCoefficient, rateScale]
      ring

/-- The terminal-state condition for the source QE PMF itself: every state in
its finite support has at most three surviving arms once the selected horizon
contains at least one round per initial arm. -/
theorem sourceQE_terminal_state_card_le_three
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (delta : ℝ)
    (stateFailure : Finset Arm × Bool)
    (hsupport : stateFailure ∈
      (quartileSourceQEStateLaw mean hmean roundCount totalBudget initial delta).support)
    (hroundCount : initial.card ≤ roundCount) :
    stateFailure.1.card ≤ 3 :=
  quartileSourceQEStateLaw_support_card_le_three mean hmean roundCount totalBudget initial delta
    stateFailure hsupport hroundCount

/-- The full reward trace of the literal source QE policy has, after its
chronological state/flag decoder, exactly the fresh QE state law used by the
finite QE-plus-final-stage theorem. -/
theorem sourceQE_sequentialPrefix_stateLaw_eq_fresh
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (delta : ℝ) :
    let hboundary : quartileSourceSequentialRoundPrefixLength totalBudget roundCount =
        Fintype.card (quartileSourceSequentialSlot roundCount totalBudget) := by
      simpa [quartileSourceSequentialRoundPrefixLength] using
        (quartileSourceSequentialSlot_card roundCount totalBudget).symm
    (adaptiveBernoulliRewardPrefixLaw mean hmean
      (quartileSourceSequentialQEProcedure roundCount totalBudget initial hinitial)
      (Fintype.card (quartileSourceSequentialSlot roundCount totalBudget)) (Nat.le_refl _)).map
      (fun trace =>
        quartileSourceSequentialBoundaryStateFailure mean
          (quartileSourceError totalBudget initial.card delta)
          roundCount totalBudget initial roundCount
          (fun position => trace (Fin.cast hboundary position))) =
      quartileSourceQEStateLaw mean hmean roundCount totalBudget initial delta := by
  simpa [quartileSourceQEStateLaw] using
    (adaptiveQuartileSourceSequentialQERewardLaw_map_boundaryStateFailure_eq_freshQuartileRoundsStateLaw
      mean hmean (quartileSourceError totalBudget initial.card delta)
      roundCount totalBudget initial hinitial)

end ZhouChenLi2014OptimalPACMultipleArm
