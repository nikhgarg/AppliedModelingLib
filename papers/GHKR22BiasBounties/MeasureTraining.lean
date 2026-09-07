import GHKR22BiasBounties.MeasureVCTraining
import GHKR22BiasBounties.Training
import AppliedModelingLib.Foundations.Probability.InfiniteAdaptiveSampling

/-!
# Algorithm 5 on arbitrary measurable populations

This file lifts Algorithm 5 and Theorem 16 to the source paper's full
distributional domain.  The executable runner and empirical optimization
oracle are reused from `Training`; population accuracy and progress are stated
with Bochner integrals.  Fresh blocks are realized by a constant Markov kernel
whose value is the finite iid product of the population law.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open AppliedModelingLib Probability
open AppliedModelingLib.Statistics

/-! ## Deterministic, distributional Algorithm 5 -/

/-- Uniform empirical/population accuracy in one training round. -/
def MeasureTrainingRoundAccurate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (eta : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (current : Model X Y) (C : Set (CandidatePair X Y)) : Prop :=
  ∀ candidate ∈ C,
    |empiricalCandidateObjective loss sample current candidate -
      measureCertificateImprovementScore law loss current
        candidate.1 candidate.2| ≤ eta

/-- Measurability of every group and replacement model offered by the
Algorithm 5 candidate class. -/
def MeasureCandidateClassMeasurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (C : Set (CandidatePair X Y)) : Prop :=
  ∀ candidate ∈ C,
    MeasurableGroup candidate.1 ∧ MeasurableModel candidate.2

/-- Every block in an execution trace is accurate for the current model
selected from the preceding blocks. -/
def MeasureTrainByOptTraceAccurate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Y n) (initial : Model X Y) :
    (rounds : ℕ) → (Fin rounds → Fin n → X × Y) → Prop
  | 0, _ => True
  | rounds + 1, trace =>
      MeasureTrainByOptTraceAccurate law loss C epsilon eta oracle initial
          rounds (Fin.init trace) ∧
        MeasureTrainingRoundAccurate law loss eta (trace (Fin.last rounds))
          (trainByOptCurrentOfHistory loss epsilon oracle initial rounds
            (Fin.init trace)) C

/-- A stopped round is approximately Bayes optimal under an arbitrary law. -/
theorem measureTrainByOpt_stop_approxBayesOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4)
    {n : ℕ} (round : TrainingRound X Y n) (current : Model X Y)
    (hmax : EmpiricalCandidateMaximizer loss round.sample current C round.chosen)
    (haccurate : MeasureTrainingRoundAccurate law loss eta round.sample current C)
    (hstop : empiricalCandidateObjective loss round.sample current round.chosen ≤
      3 * epsilon / 4) :
    MeasureApproxBayesOptimal law loss C epsilon current := by
  intro candidate hcandidate
  have hcAccurate := haccurate candidate hcandidate
  have hempiricalMax := hmax.2 candidate hcandidate
  rcases abs_le.mp hcAccurate with ⟨hlower, hupper⟩
  linarith

/-- Exact arbitrary-law loss identity for one candidate update. -/
theorem measureModelLoss_sub_candidateUpdate_eq_score
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {current : Model X Y} (hcurrent : MeasurableModel current)
    {candidate : CandidatePair X Y}
    (hcandidate : MeasurableGroup candidate.1 ∧
      MeasurableModel candidate.2) :
    measureModelLoss law loss current -
        measureModelLoss law loss
          (listUpdate current candidate.1 candidate.2) =
      measureCertificateImprovementScore law loss current
        candidate.1 candidate.2 := by
  rw [measureModelLoss_sub_listUpdate_eq_numerator_sub law hloss hcurrent
      hcandidate.2 hcandidate.1,
    ← measureCertificateImprovementScore_eq_numerator_sub law hloss hcurrent
      hcandidate.2 hcandidate.1]

/-- Every continued accurate round lowers population loss by at least
`epsilon / 2`. -/
theorem measureContinued_training_round_loss_drop
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (C : Set (CandidatePair X Y))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon eta : ℝ) (heta : eta ≤ epsilon / 4)
    {n : ℕ} (round : TrainingRound X Y n)
    {current : Model X Y} (hcurrent : MeasurableModel current)
    (hchosen : round.chosen ∈ C)
    (haccurate : MeasureTrainingRoundAccurate law loss eta round.sample current C)
    (hcontinue : 3 * epsilon / 4 <
      empiricalCandidateObjective loss round.sample current round.chosen) :
    measureModelLoss law loss
        (listUpdate current round.chosen.1 round.chosen.2) ≤
      measureModelLoss law loss current - epsilon / 2 := by
  have hacc := haccurate round.chosen hchosen
  have hpopulation : epsilon / 2 ≤
      measureCertificateImprovementScore law loss current
        round.chosen.1 round.chosen.2 := by
    rcases abs_le.mp hacc with ⟨hlower, hupper⟩
    linarith
  rw [← measureModelLoss_sub_candidateUpdate_eq_score law hloss hcurrent
    (hCmeasurable round.chosen hchosen)] at hpopulation
  linarith

/-- Exact empirical optimization keeps every reached model measurable. -/
theorem measurableModel_trainByOptRun_output
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : BoundedLoss Y) (C : Set (CandidatePair X Y))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon : ℝ) {n : ℕ} (oracle : TrainingOracle X Y n)
    (horacle : ExactTrainingOracle loss C oracle)
    {initial : Model X Y} (hinitial : MeasurableModel initial) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y),
      MeasurableModel
        (trainByOptRun loss epsilon oracle initial rounds trace).output := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simpa [trainByOptRun, TrainByOptOutcome.output] using hinitial
  | succ rounds ih =>
      intro trace
      have hprefixMeasurable := ih (Fin.init trace)
      cases hprefix : trainByOptRun loss epsilon oracle initial rounds
          (Fin.init trace) with
      | stopped previous previousCalls =>
          rw [hprefix] at hprefixMeasurable
          simpa [trainByOptRun, hprefix, TrainByOptOutcome.output] using
            hprefixMeasurable
      | running current previousCalls =>
          rw [hprefix] at hprefixMeasurable
          simp only [TrainByOptOutcome.output] at hprefixMeasurable
          simp only [trainByOptRun, hprefix]
          split
          · simpa [TrainByOptOutcome.output] using hprefixMeasurable
          · simp only [TrainByOptOutcome.output]
            have hchosen := (horacle current (trace (Fin.last rounds))).1
            exact measurableModel_listUpdate hprefixMeasurable
              (hCmeasurable _ hchosen).2 (hCmeasurable _ hchosen).1

/-- If the measure-theoretic runner stops, its returned model is
approximately Bayes optimal. -/
theorem measureTrainByOptRun_stopped_approxBayesOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n)
    (horacle : ExactTrainingOracle loss C oracle)
    (initial : Model X Y) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y)
      (output : Model X Y) (calls : ℕ),
      trainByOptRun loss epsilon oracle initial rounds trace =
          .stopped output calls →
      MeasureTrainByOptTraceAccurate law loss C epsilon eta oracle initial
          rounds trace →
      MeasureApproxBayesOptimal law loss C epsilon output := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace output calls hrun _
      simp [trainByOptRun] at hrun
  | succ rounds ih =>
      intro trace output calls hrun haccurate
      rcases haccurate with ⟨hprefixAccurate, hlastAccurate⟩
      simp only [trainByOptRun] at hrun
      cases hprefix : trainByOptRun loss epsilon oracle initial rounds
          (Fin.init trace) with
      | stopped previous previousCalls =>
          rw [hprefix] at hrun
          have hprevious :=
            ih (Fin.init trace) previous previousCalls hprefix hprefixAccurate
          cases hrun
          exact hprevious
      | running current previousCalls =>
          rw [hprefix] at hrun
          dsimp only at hrun
          split at hrun
          · rename_i hstop
            have hcurrent :
                trainByOptCurrentOfHistory loss epsilon oracle initial rounds
                    (Fin.init trace) = current := by
              simp [trainByOptCurrentOfHistory, hprefix,
                TrainByOptOutcome.output]
            rw [hcurrent] at hlastAccurate
            let round : TrainingRound X Y n :=
              { sample := trace (Fin.last rounds)
                chosen := oracle current (trace (Fin.last rounds)) }
            have hoptimal := measureTrainByOpt_stop_approxBayesOptimal
              law loss C epsilon eta heta round current
              (horacle current round.sample) hlastAccurate hstop
            cases hrun
            exact hoptimal
          · simp at hrun

/-- If all supplied blocks are consumed, every round was a successful
population-loss-decreasing update. -/
theorem measureTrainByOptRun_running_loss_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (C : Set (CandidatePair X Y))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon eta : ℝ) (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n)
    (horacle : ExactTrainingOracle loss C oracle)
    {initial : Model X Y} (hinitial : MeasurableModel initial) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y)
      (output : Model X Y) (calls : ℕ),
      trainByOptRun loss epsilon oracle initial rounds trace =
          .running output calls →
      MeasureTrainByOptTraceAccurate law loss C epsilon eta oracle initial
          rounds trace →
      measureModelLoss law loss output ≤
        measureModelLoss law loss initial - (rounds : ℝ) * (epsilon / 2) := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace output calls hrun _
      simp only [trainByOptRun] at hrun
      cases hrun
      simp
  | succ rounds ih =>
      intro trace output calls hrun haccurate
      rcases haccurate with ⟨hprefixAccurate, hlastAccurate⟩
      simp only [trainByOptRun] at hrun
      cases hprefix : trainByOptRun loss epsilon oracle initial rounds
          (Fin.init trace) with
      | stopped previous previousCalls =>
          rw [hprefix] at hrun
          simp at hrun
      | running current previousCalls =>
          rw [hprefix] at hrun
          dsimp only at hrun
          split at hrun
          · simp at hrun
          · rename_i hcontinue
            cases hrun
            have hcurrentEq :
                trainByOptCurrentOfHistory loss epsilon oracle initial rounds
                    (Fin.init trace) = current := by
              simp [trainByOptCurrentOfHistory, hprefix,
                TrainByOptOutcome.output]
            rw [hcurrentEq] at hlastAccurate
            let round : TrainingRound X Y n :=
              { sample := trace (Fin.last rounds)
                chosen := oracle current (trace (Fin.last rounds)) }
            have hprefixLoss := ih (Fin.init trace) current previousCalls
              hprefix hprefixAccurate
            have hcurrentMeasurable := measurableModel_trainByOptRun_output
              loss C hCmeasurable epsilon oracle horacle hinitial rounds
                (Fin.init trace)
            rw [hprefix] at hcurrentMeasurable
            simp only [TrainByOptOutcome.output] at hcurrentMeasurable
            have hlastLoss := measureContinued_training_round_loss_drop
              law hloss C hCmeasurable epsilon eta heta round
                hcurrentMeasurable (horacle current round.sample).1
                hlastAccurate (lt_of_not_ge hcontinue)
            calc
              measureModelLoss law loss
                  (listUpdate current round.chosen.1 round.chosen.2) ≤
                  measureModelLoss law loss current - epsilon / 2 := hlastLoss
              _ ≤ (measureModelLoss law loss initial -
                    (rounds : ℝ) * (epsilon / 2)) - epsilon / 2 :=
                  sub_le_sub_right hprefixLoss _
              _ = measureModelLoss law loss initial -
                    ((rounds + 1 : ℕ) : ℝ) * (epsilon / 2) := by
                  push_cast
                  ring

/-- A measurable zero-loss model is approximately Bayes optimal for every
nonnegative tolerance. -/
theorem measureApproxBayesOptimal_of_modelLoss_eq_zero
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (C : Set (CandidatePair X Y))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    {current : Model X Y} (hcurrent : MeasurableModel current)
    (hzero : measureModelLoss law loss current = 0) :
    MeasureApproxBayesOptimal law loss C epsilon current := by
  intro candidate hcandidate
  have hcandidateMeasurable := hCmeasurable candidate hcandidate
  have hupdatedMeasurable := measurableModel_listUpdate hcurrent
    hcandidateMeasurable.2 hcandidateMeasurable.1
  have hupdated := measureModelLoss_nonneg law hloss hupdatedMeasurable
  have hidentity := measureModelLoss_sub_candidateUpdate_eq_score
    law hloss hcurrent hcandidateMeasurable
  rw [hzero] at hidentity
  linarith

/-- Deterministic Theorem 16 for the literal runner on an arbitrary
population measure. -/
theorem measureTheorem16_trainByOptRun
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (C : Set (CandidatePair X Y))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon eta : ℝ) (hepsilon : 0 ≤ epsilon)
    (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n)
    (horacle : ExactTrainingOracle loss C oracle)
    {initial : Model X Y} (hinitial : MeasurableModel initial)
    (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y)
    (haccurate : MeasureTrainByOptTraceAccurate law loss C epsilon eta
      oracle initial rounds trace)
    (hbudget : 1 ≤ (rounds : ℝ) * (epsilon / 2)) :
    MeasureApproxBayesOptimal law loss C epsilon
        (trainByOptRun loss epsilon oracle initial rounds trace).output ∧
      (trainByOptRun loss epsilon oracle initial rounds trace).calls ≤ rounds := by
  constructor
  · cases hrun : trainByOptRun loss epsilon oracle initial rounds trace with
    | stopped output calls =>
        simp only [hrun, TrainByOptOutcome.output]
        exact measureTrainByOptRun_stopped_approxBayesOptimal
          law loss C epsilon eta heta oracle horacle initial rounds trace
            output calls hrun haccurate
    | running output calls =>
        simp only [hrun, TrainByOptOutcome.output]
        have hlossDrop := measureTrainByOptRun_running_loss_le
          law hloss C hCmeasurable epsilon eta heta oracle horacle hinitial
            rounds trace output calls hrun haccurate
        have hinitialOne := measureModelLoss_le_one law hloss hinitial
        have houtputMeasurable := measurableModel_trainByOptRun_output
          loss C hCmeasurable epsilon oracle horacle hinitial rounds trace
        rw [hrun] at houtputMeasurable
        simp only [TrainByOptOutcome.output] at houtputMeasurable
        have hnonneg := measureModelLoss_nonneg law hloss houtputMeasurable
        have hzero : measureModelLoss law loss output = 0 := by
          apply le_antisymm
          · linarith
          · exact hnonneg
        exact measureApproxBayesOptimal_of_modelLoss_eq_zero law hloss C
          hCmeasurable epsilon hepsilon houtputMeasurable hzero
  · exact trainByOptRun_calls_le loss epsilon oracle initial rounds trace

/-! ## Fresh iid block semantics -/

/-- The constant batch-index family used by Algorithm 5. -/
abbrev MeasureTrainingBatchIndex (n : ℕ) (_round : ℕ) := Fin n

/-- Every Algorithm 5 round draws a fresh iid block from the same population
law.  The kernel is constant in the preceding history, making independence
from the adaptively selected current model explicit. -/
noncomputable def measureTrainingBatchKernel
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (n iteration : ℕ) :
    Kernel
      ((i : Finset.Iic iteration) →
        AppliedModelingLib.HeterogeneousBatchTraceCoordinate
          (MeasureTrainingBatchIndex n) (X × Bool) i.1)
      (AppliedModelingLib.HeterogeneousBatchTraceCoordinate
        (MeasureTrainingBatchIndex n) (X × Bool) (iteration + 1)) :=
  Kernel.const _ (finiteIIDSampleLaw law n)

instance measureTrainingBatchKernel_isMarkovKernel
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (n iteration : ℕ) :
    IsMarkovKernel (measureTrainingBatchKernel law n iteration) := by
  let hsample : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  refine ⟨fun _history => ?_⟩
  simpa [measureTrainingBatchKernel, Kernel.const_apply] using hsample

/-- Common Ionescu--Tulcea law of the infinite stream of fresh training
blocks. -/
noncomputable def measureTrainingInfiniteTraceLaw
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (n : ℕ) :
    Measure ((i : ℕ) →
      AppliedModelingLib.HeterogeneousBatchTraceCoordinate
        (MeasureTrainingBatchIndex n) (X × Bool) i) :=
  AppliedModelingLib.heterogeneousBatchTraceInfiniteLaw
    (MeasureTrainingBatchIndex n) (measureTrainingBatchKernel law n)

instance measureTrainingInfiniteTraceLaw_isProbabilityMeasure
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (n : ℕ) :
    IsProbabilityMeasure (measureTrainingInfiniteTraceLaw law n) := by
  unfold measureTrainingInfiniteTraceLaw
  infer_instance

/-- The history-dependent Lemma 15 failure event for the next fresh block. -/
def MeasureTrainByOptVCBadEvent
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (G : Set (Group X))
    (H : Set (Model X Bool)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (iteration : ℕ)
    (history : AppliedModelingLib.HeterogeneousBatchTrace
      (MeasureTrainingBatchIndex n) (X × Bool) iteration)
    (sample : MeasureTrainingBatchIndex n iteration → X × Bool) : Prop :=
  MeasureCertificateVCDeviationEvent law
    (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial
      iteration history)
    G H eta sample

/-- The joint history/next-block measurability condition required to turn the
outer event into a measurable Ionescu--Tulcea cylinder.  This condition also
records the standard requirement that the optimizer's tie-breaking be
measurable as it changes the current model with the history. -/
def MeasureTrainByOptVCBadEventPairMeasurable
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (G : Set (Group X))
    (H : Set (Model X Bool)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool) : Prop :=
  ∀ iteration, MeasurableSet
    (AppliedModelingLib.heterogeneousBatchTraceBadEventPair
      (MeasureTrainingBatchIndex n)
      (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
      iteration)

/-- The current model selected by every finite history is measurable as a
prediction map. -/
theorem measurableModel_measureTrainByOptCurrentOfHistory
    {X : Type*} [MeasurableSpace X]
    (C : Set (CandidatePair X Bool))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (epsilon : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (iteration : ℕ)
    (history : AppliedModelingLib.HeterogeneousBatchTrace
      (MeasureTrainingBatchIndex n) (X × Bool) iteration) :
    MeasurableModel
      (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial
        iteration history) := by
  exact measurableModel_trainByOptRun_output binaryZeroOneLoss C hCmeasurable
    epsilon oracle horacle hinitial iteration history

/-- Conditional on every preceding history, one fresh block obeys the
arbitrary-population Lemma 15 bound. -/
theorem measureTrainByOptVC_conditionalFailure_le
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (C : Set (CandidatePair X Bool))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (epsilon : ℝ) {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (delta : ℝ) (hdelta : 0 < delta)
    (hupdateEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
        (listUpdateVCDimensionBound dG dH) n (delta / 2))
    (hcurrentEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law ({current} : Set (BinaryClassifier X))
        1 n (delta / 2))
    (iteration : ℕ)
    (history : AppliedModelingLib.HeterogeneousBatchTrace
      (MeasureTrainingBatchIndex n) (X × Bool) iteration) :
    (finiteIIDSampleLaw law n).real
      {sample | MeasureTrainByOptVCBadEvent law G H epsilon
        (certificateVCConfidenceRadius dG dH n delta) oracle initial
        iteration history sample} ≤ delta := by
  let current := trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle
    initial iteration history
  have hcurrent : MeasurableModel current :=
    measurableModel_measureTrainByOptCurrentOfHistory C hCmeasurable epsilon
      oracle horacle hinitial iteration history
  change MeasureCertificateVCDeviationFailure law current G H
      (certificateVCConfidenceRadius dG dH n delta) n ≤ delta
  exact measureLemma15_vc_uniform_convergence law hcurrent G H
    hGmeasurable hHmeasurable dG dH hvcG hvcH n hcount hdimension
    delta hdelta (hupdateEvents current hcurrent) (hcurrentEvents current hcurrent)

/-- One history-dependent bad cylinder has probability at most its allocated
confidence budget under the common fresh-block trace law. -/
theorem measureTrainByOptVC_infiniteBadEvent_le
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (C : Set (CandidatePair X Bool))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (epsilon : ℝ) {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (delta : ℝ) (hdelta : 0 < delta)
    (hupdateEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
        (listUpdateVCDimensionBound dG dH) n (delta / 2))
    (hcurrentEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law ({current} : Set (BinaryClassifier X))
        1 n (delta / 2))
    (hpairMeasurable : MeasureTrainByOptVCBadEventPairMeasurable law G H
      epsilon (certificateVCConfidenceRadius dG dH n delta) oracle initial)
    (iteration : ℕ) :
    (measureTrainingInfiniteTraceLaw law n).real
      (AppliedModelingLib.adaptiveFreshHeterogeneousInfiniteTraceBadEvent
        (MeasureTrainingBatchIndex n)
        (MeasureTrainByOptVCBadEvent law G H epsilon
          (certificateVCConfidenceRadius dG dH n delta) oracle initial)
        iteration) ≤ delta := by
  apply AppliedModelingLib.measureReal_heterogeneousBatchTraceInfiniteBadEvent_le
    (MeasureTrainingBatchIndex n) (measureTrainingBatchKernel law n)
    (MeasureTrainByOptVCBadEvent law G H epsilon
      (certificateVCConfidenceRadius dG dH n delta) oracle initial)
    iteration delta hdelta.le (hpairMeasurable iteration)
  intro historyPrefix
  rw [measureTrainingBatchKernel, Kernel.const_apply]
  have hreal := measureTrainByOptVC_conditionalFailure_le law G H
    hGmeasurable hHmeasurable C hCmeasurable dG dH hvcG hvcH epsilon
    hcount hdimension oracle horacle hinitial delta hdelta hupdateEvents
    hcurrentEvents iteration
      (AppliedModelingLib.heterogeneousBatchTraceOfPrefix iteration historyPrefix)
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  calc
    (finiteIIDSampleLaw law n)
        {batch | MeasureTrainByOptVCBadEvent law G H epsilon
          (certificateVCConfidenceRadius dG dH n delta) oracle initial
          iteration (AppliedModelingLib.heterogeneousBatchTraceOfPrefix iteration historyPrefix)
          batch} =
        ENNReal.ofReal ((finiteIIDSampleLaw law n).real
          {batch | MeasureTrainByOptVCBadEvent law G H epsilon
            (certificateVCConfidenceRadius dG dH n delta) oracle initial
            iteration (AppliedModelingLib.heterogeneousBatchTraceOfPrefix iteration historyPrefix)
            batch}) := (MeasureTheory.ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal delta := ENNReal.ofReal_le_ofReal hreal

/-- Union of the bad cylinders among the first `rounds` training blocks. -/
def MeasureTrainByOptVCFiniteBadEvent
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (G : Set (Group X))
    (H : Set (Model X Bool)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (rounds : ℕ) :
    Set ((i : ℕ) → AppliedModelingLib.HeterogeneousBatchTraceCoordinate
      (MeasureTrainingBatchIndex n) (X × Bool) i) :=
  ⋃ iteration : Fin rounds,
    AppliedModelingLib.adaptiveFreshHeterogeneousInfiniteTraceBadEvent
      (MeasureTrainingBatchIndex n)
      (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
      iteration.1

/-- Outer probability of at least one Lemma 15 failure in the supplied
horizon. -/
noncomputable def MeasureTrainByOptVCFailureProbability
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (epsilon eta : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) (rounds : ℕ) : ℝ :=
  (measureTrainingInfiniteTraceLaw law n).real
    (MeasureTrainByOptVCFiniteBadEvent law G H epsilon eta oracle initial rounds)

/-- Adaptive finite-horizon union bound for arbitrary population laws. -/
theorem measureTrainByOptVCFailureProbability_le_mul
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (C : Set (CandidatePair X Bool))
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (epsilon : ℝ) {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (deltaPerRound : ℝ) (hdeltaPerRound : 0 < deltaPerRound)
    (hupdateEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
        (listUpdateVCDimensionBound dG dH) n (deltaPerRound / 2))
    (hcurrentEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law ({current} : Set (BinaryClassifier X))
        1 n (deltaPerRound / 2))
    (hpairMeasurable : MeasureTrainByOptVCBadEventPairMeasurable law G H
      epsilon (certificateVCConfidenceRadius dG dH n deltaPerRound)
      oracle initial)
    (rounds : ℕ) :
    MeasureTrainByOptVCFailureProbability law G H epsilon
        (certificateVCConfidenceRadius dG dH n deltaPerRound)
        oracle initial rounds ≤ (rounds : ℝ) * deltaPerRound := by
  unfold MeasureTrainByOptVCFailureProbability MeasureTrainByOptVCFiniteBadEvent
  calc
    (measureTrainingInfiniteTraceLaw law n).real
        (⋃ iteration : Fin rounds,
          AppliedModelingLib.adaptiveFreshHeterogeneousInfiniteTraceBadEvent
            (MeasureTrainingBatchIndex n)
            (MeasureTrainByOptVCBadEvent law G H epsilon
              (certificateVCConfidenceRadius dG dH n deltaPerRound)
              oracle initial)
            iteration.1) ≤
        ∑ iteration : Fin rounds,
          (measureTrainingInfiniteTraceLaw law n).real
            (AppliedModelingLib.adaptiveFreshHeterogeneousInfiniteTraceBadEvent
              (MeasureTrainingBatchIndex n)
              (MeasureTrainByOptVCBadEvent law G H epsilon
                (certificateVCConfidenceRadius dG dH n deltaPerRound)
                oracle initial)
              iteration.1) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _iteration : Fin rounds, deltaPerRound := by
      apply Finset.sum_le_sum
      intro iteration _
      exact measureTrainByOptVC_infiniteBadEvent_le law G H hGmeasurable
        hHmeasurable C hCmeasurable dG dH hvcG hvcH epsilon hcount
        hdimension oracle horacle hinitial deltaPerRound hdeltaPerRound
        hupdateEvents hcurrentEvents hpairMeasurable iteration.1
    _ = (rounds : ℝ) * deltaPerRound := by simp

/-- Exclusion from the finite union of bad cylinders implies that the
corresponding extracted prefix satisfies the recursive no-bad predicate. -/
theorem not_measureTrainByOptVCAnyBad_of_not_finiteBad
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (G : Set (Group X))
    (H : Set (Model X Bool)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (trace : (i : ℕ) → AppliedModelingLib.HeterogeneousBatchTraceCoordinate
      (MeasureTrainingBatchIndex n) (X × Bool) i) :
    ∀ rounds,
      trace ∉ MeasureTrainByOptVCFiniteBadEvent law G H epsilon eta
        oracle initial rounds →
      ¬ AppliedModelingLib.adaptiveFreshHeterogeneousTraceAnyBadEvent
        (MeasureTrainingBatchIndex n)
        (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
        rounds (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace) := by
  intro rounds
  induction rounds with
  | zero =>
      intro _
      simp [AppliedModelingLib.adaptiveFreshHeterogeneousTraceAnyBadEvent]
  | succ rounds ih =>
      intro houtside hbad
      change
        AppliedModelingLib.adaptiveFreshHeterogeneousTraceAnyBadEvent
            (MeasureTrainingBatchIndex n)
            (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
            rounds (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace) ∨
          MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial
            rounds (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace)
              (trace (rounds + 1)) at hbad
      rcases hbad with hprevious | hlast
      · apply ih
        · intro hmember
          apply houtside
          rcases Set.mem_iUnion.mp hmember with ⟨iteration, hiteration⟩
          apply Set.mem_iUnion.mpr
          exact ⟨iteration.castSucc, hiteration⟩
        · exact hprevious
      · apply houtside
        apply Set.mem_iUnion.mpr
        exact ⟨Fin.last rounds, hlast⟩

/-- No VC failure in a finite trace gives exactly the deterministic accuracy
invariant consumed by Algorithm 5. -/
theorem measureTrainByOptTraceAccurate_of_not_vcBadEvent
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) (G : Set (Group X))
    (H : Set (Model X Bool))
    (C : Set (CandidatePair X Bool))
    (hcontained : CandidateClassContainedIn C G H)
    (epsilon eta : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Bool),
      ¬ AppliedModelingLib.adaptiveFreshHeterogeneousTraceAnyBadEvent
        (MeasureTrainingBatchIndex n)
        (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
        rounds trace →
      MeasureTrainByOptTraceAccurate law binaryZeroOneLoss C epsilon eta
        oracle initial rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace _
      trivial
  | succ rounds ih =>
      intro trace hgood
      have hprefix :
          ¬ AppliedModelingLib.adaptiveFreshHeterogeneousTraceAnyBadEvent
            (MeasureTrainingBatchIndex n)
            (MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial)
            rounds (Fin.init trace) := by
        intro hbad
        exact hgood (Or.inl hbad)
      have hlast :
          ¬ MeasureTrainByOptVCBadEvent law G H epsilon eta oracle initial
            rounds (Fin.init trace) (trace (Fin.last rounds)) := by
        intro hbad
        exact hgood (Or.inr hbad)
      constructor
      · exact ih (Fin.init trace) hprefix
      · intro candidate hcandidate
        rcases hcontained candidate hcandidate with ⟨hgroup, hmodel⟩
        apply le_of_not_gt
        intro hgap
        apply hlast
        exact ⟨candidate.1, hgroup, candidate.2, hmodel, by
          simpa [empiricalCandidateObjective] using hgap⟩

/-- Outer probability that the model returned from the first `rounds` fresh
blocks is not approximately Bayes optimal. -/
noncomputable def MeasureTrainByOptOutputFailureProbability
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (C : Set (CandidatePair X Bool)) (epsilon : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (rounds : ℕ) : ℝ :=
  (measureTrainingInfiniteTraceLaw law n).real {trace |
    ¬ MeasureApproxBayesOptimal law binaryZeroOneLoss C epsilon
      (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds
        (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace)).output}

/-- Theorem 16 on an arbitrary measurable population.  The conclusion is an
outer-probability bound, so it remains valid even before separately proving
measurability of the optimizer's output event. -/
theorem measureTheorem16_trainByOpt_highProbability
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (C : Set (CandidatePair X Bool))
    (hcontained : CandidateClassContainedIn C G H)
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (rounds : ℕ) (hbudget : 1 ≤ (rounds : ℝ) * (epsilon / 2))
    (delta : ℝ) (hdelta : 0 < delta)
    (hradius : certificateVCConfidenceRadius dG dH n
      (delta / (rounds : ℝ)) ≤ epsilon / 4)
    (hupdateEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
        (listUpdateVCDimensionBound dG dH) n
        ((delta / (rounds : ℝ)) / 2))
    (hcurrentEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law ({current} : Set (BinaryClassifier X))
        1 n ((delta / (rounds : ℝ)) / 2))
    (hpairMeasurable : MeasureTrainByOptVCBadEventPairMeasurable law G H
      epsilon (certificateVCConfidenceRadius dG dH n
        (delta / (rounds : ℝ))) oracle initial) :
    MeasureTrainByOptOutputFailureProbability law C epsilon oracle initial
      rounds ≤ delta := by
  have hrounds : 0 < rounds := by
    by_contra hzero
    have : rounds = 0 := Nat.eq_zero_of_not_pos hzero
    subst rounds
    norm_num at hbudget
  have hroundsReal : 0 < (rounds : ℝ) := by exact_mod_cast hrounds
  let deltaPerRound := delta / (rounds : ℝ)
  have hdeltaPerRound : 0 < deltaPerRound := div_pos hdelta hroundsReal
  have hbadBound := measureTrainByOptVCFailureProbability_le_mul law G H
    hGmeasurable hHmeasurable C hCmeasurable dG dH hvcG hvcH epsilon
    hcount hdimension oracle horacle hinitial deltaPerRound hdeltaPerRound
    hupdateEvents hcurrentEvents hpairMeasurable rounds
  have hfailureSubset :
      {trace : (i : ℕ) → AppliedModelingLib.HeterogeneousBatchTraceCoordinate
          (MeasureTrainingBatchIndex n) (X × Bool) i |
        ¬ MeasureApproxBayesOptimal law binaryZeroOneLoss C epsilon
          (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds
            (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace)).output} ⊆
        MeasureTrainByOptVCFiniteBadEvent law G H epsilon
          (certificateVCConfidenceRadius dG dH n deltaPerRound)
          oracle initial rounds := by
    intro trace hfailure
    by_contra hnoBad
    have hnoAny := not_measureTrainByOptVCAnyBad_of_not_finiteBad
      law G H epsilon (certificateVCConfidenceRadius dG dH n deltaPerRound)
      oracle initial trace rounds hnoBad
    have haccurate := measureTrainByOptTraceAccurate_of_not_vcBadEvent
      law G H C hcontained epsilon
      (certificateVCConfidenceRadius dG dH n deltaPerRound)
      oracle initial rounds
      (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace) hnoAny
    have hsuccess := (measureTheorem16_trainByOptRun law
      measurableBoundedLoss_binaryZeroOneLoss C hCmeasurable epsilon
      (certificateVCConfidenceRadius dG dH n deltaPerRound) hepsilon.le
      hradius oracle horacle hinitial rounds
      (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace)
      haccurate hbudget).1
    exact hfailure hsuccess
  unfold MeasureTrainByOptOutputFailureProbability
  calc
    (measureTrainingInfiniteTraceLaw law n).real
        {trace |
          ¬ MeasureApproxBayesOptimal law binaryZeroOneLoss C epsilon
            (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds
              (AppliedModelingLib.heterogeneousBatchTraceOfInfiniteTrace rounds trace)).output} ≤
        MeasureTrainByOptVCFailureProbability law G H epsilon
          (certificateVCConfidenceRadius dG dH n deltaPerRound)
          oracle initial rounds := by
      exact measureReal_mono hfailureSubset (measure_ne_top _ _)
    _ ≤ (rounds : ℝ) * deltaPerRound := hbadBound
    _ = delta := by
      dsimp [deltaPerRound]
      field_simp

/-- Source-rounded Theorem 16 on an arbitrary measurable population.  This
packages the canonical `ceil (2 / epsilon)` fresh-block horizon, the exact
high-probability guarantee, the oracle-call bound, and the rectangular sample
count.  The event-measurability premises are the standard permissible-class
conditions needed for arbitrary (possibly uncountable) VC classes. -/
theorem measureTheorem16_trainByOpt_sourceRounded
    {X : Type*} [MeasurableSpace X]
    (law : Measure (X × Bool)) [IsProbabilityMeasure law]
    (G : Set (Group X)) (H : Set (Model X Bool))
    (hGmeasurable : ∀ g ∈ G, MeasurableGroup g)
    (hHmeasurable : ∀ h ∈ H, MeasurableModel h)
    (C : Set (CandidatePair X Bool))
    (hcontained : CandidateClassContainedIn C G H)
    (hCmeasurable : MeasureCandidateClassMeasurable C)
    (dG dH : ℕ) (hvcG : VCDimensionAtMost G dG)
    (hvcH : VCDimensionAtMost H dH)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {blockSize : ℕ} (hcount : 0 < blockSize)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ blockSize + blockSize)
    (oracle : TrainingOracle X Bool blockSize)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    {initial : Model X Bool} (hinitial : MeasurableModel initial)
    (delta : ℝ) (hdelta : 0 < delta)
    (hradius : certificateVCConfidenceRadius dG dH blockSize
      (delta / (trainByOptRoundBudget epsilon : ℝ)) ≤ epsilon / 4)
    (hupdateEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
        (listUpdateVCDimensionBound dG dH) blockSize
        ((delta / (trainByOptRoundBudget epsilon : ℝ)) / 2))
    (hcurrentEvents : ∀ current, MeasurableModel current →
      VCSourceEventsMeasurable law ({current} : Set (BinaryClassifier X))
        1 blockSize ((delta / (trainByOptRoundBudget epsilon : ℝ)) / 2))
    (hpairMeasurable : MeasureTrainByOptVCBadEventPairMeasurable law G H
      epsilon (certificateVCConfidenceRadius dG dH blockSize
        (delta / (trainByOptRoundBudget epsilon : ℝ))) oracle initial) :
    MeasureTrainByOptOutputFailureProbability law C epsilon oracle initial
        (trainByOptRoundBudget epsilon) ≤ delta ∧
      (∀ trace : Fin (trainByOptRoundBudget epsilon) →
          Fin blockSize → X × Bool,
        (trainByOptRun binaryZeroOneLoss epsilon oracle initial
          (trainByOptRoundBudget epsilon) trace).calls ≤
            trainByOptRoundBudget epsilon) ∧
      Fintype.card
          (Fin (trainByOptRoundBudget epsilon) × Fin blockSize) =
        trainByOptRoundBudget epsilon * blockSize := by
  refine ⟨?_, ?_, theorem16_total_sample_count _ _⟩
  · exact measureTheorem16_trainByOpt_highProbability law G H hGmeasurable
      hHmeasurable C hcontained hCmeasurable dG dH hvcG hvcH epsilon
      hepsilon hcount hdimension oracle horacle hinitial
      (trainByOptRoundBudget epsilon)
      (trainByOptRoundBudget_sufficient epsilon hepsilon) delta hdelta
      hradius hupdateEvents hcurrentEvents hpairMeasurable
  · intro trace
    exact trainByOptRun_calls_le binaryZeroOneLoss epsilon oracle initial
      (trainByOptRoundBudget epsilon) trace

end

end GHKR22BiasBounties
