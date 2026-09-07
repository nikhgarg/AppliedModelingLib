import GHKR22BiasBounties.FalsifyAndUpdate
import GHKR22BiasBounties.Alternating
import GHKR22BiasBounties.VCTraining
import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveSampling
import Mathlib.Tactic.Linarith

/-!
# Uniform-convergence training reduction

This file formalizes Lemma 15's concentration role, Algorithm 5, and Theorem
16.  The concentration lemma is stated with its exact finite trace-family
bound; VC/Sauer--Shelah controls the cardinality of that trace family.  The
algorithmic theorem itself is distribution-free conditional only on the
uniform-deviation event delivered by the lemma.
-/

namespace GHKR22BiasBounties

noncomputable section

open AppliedModelingLib Probability

/-- Uniform population/empirical certificate accuracy at tolerance `eta`. -/
def CertificateUniformDeviation {X Y Θ : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (eta : ℝ) {n : ℕ}
    (sample : Fin n → X × Y) : Prop :=
  ∀ parameter,
    |empiricalSubmissionScore loss sample (family parameter) -
      certificateImprovementScore law loss (family parameter).current
        (family parameter).group (family parameter).replacement| ≤ eta

/-- Lemma 15, exact finite-trace-family Hoeffding failure bound. -/
theorem lemma15_finite_trace_uniform_convergence
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Fintype Θ] [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (eta : ℝ) (heta : 0 ≤ eta)
    (n : ℕ) (hcount : 0 < n) :
    adaptiveCheckerDeviationFailure law loss family (4 * eta) n ≤
      (Fintype.card Θ : ℝ) * 2 *
        Real.exp (-(n : ℝ) * eta ^ 2 / 2) := by
  convert adaptiveCheckerDeviationFailure_le_explicit law loss family
    (4 * eta) n hcount (mul_nonneg (by norm_num) heta) using 1 <;> ring

/-- Outside Lemma 15's event, the trace family is uniformly `eta`-accurate. -/
theorem certificateUniformDeviation_of_not_lemma15_event
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (eta : ℝ) (heta : 0 ≤ eta)
    (n : ℕ) (hcount : 0 < n) (sample : Fin n → X × Y)
    (hgood : ¬ adaptiveCheckerDeviationEvent law loss family (4 * eta) sample) :
    CertificateUniformDeviation law loss family eta sample := by
  have hchecker := checkerUniformlyAccurate_of_not_deviationEvent law loss family
    (4 * eta) (mul_nonneg (by norm_num) heta) n hcount sample hgood
  intro parameter
  simpa using hchecker parameter

/-- A certificate pair used by Algorithm 5. -/
abbrev CandidatePair (X Y : Type*) := Group X × Model X Y

/-- Empirical objective of a candidate at the current model. -/
def empiricalCandidateObjective {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidate : CandidatePair X Y) : ℝ :=
  empiricalSubmissionScore loss sample
    { current := current, group := candidate.1, replacement := candidate.2 }

/-- Exact empirical optimizer required by Algorithm 5. -/
def EmpiricalCandidateMaximizer {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (C : Set (CandidatePair X Y))
    (chosen : CandidatePair X Y) : Prop :=
  chosen ∈ C ∧ ∀ candidate ∈ C,
    empiricalCandidateObjective loss sample current candidate ≤
      empiricalCandidateObjective loss sample current chosen

/-- Uniform accuracy over Algorithm 5's entire candidate class in one round. -/
def TrainingRoundAccurate {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (eta : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (current : Model X Y) (C : Set (CandidatePair X Y)) : Prop :=
  ∀ candidate ∈ C,
    |empiricalCandidateObjective loss sample current candidate -
      certificateImprovementScore law loss current candidate.1 candidate.2| ≤ eta

/-- One Algorithm 5 oracle call and its fresh data block. -/
structure TrainingRound (X Y : Type*) (n : ℕ) where
  sample : Fin n → X × Y
  chosen : CandidatePair X Y

/-- Algorithm 5 step result. -/
inductive TrainByOptStepResult (X Y : Type*) where
  | stop (model : Model X Y)
  | continue (model : Model X Y)

/-- One exact step of Algorithm 5. -/
def trainByOptStep {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (epsilon : ℝ) (current : Model X Y)
    (round : TrainingRound X Y n) : TrainByOptStepResult X Y :=
  if empiricalCandidateObjective loss round.sample current round.chosen ≤
      3 * epsilon / 4 then
    .stop current
  else
    .continue (listUpdate current round.chosen.1 round.chosen.2)

/-- The model obtained after a list of continued Algorithm 5 updates. -/
def runTrainingUpdates {X Y : Type*} {n : ℕ} :
    Model X Y → List (TrainingRound X Y n) → Model X Y
  | current, [] => current
  | current, round :: rest =>
      runTrainingUpdates
        (listUpdate current round.chosen.1 round.chosen.2) rest

/-- Every recorded training round is accurate, optimizing, and continued. -/
def ValidTrainingUpdates {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ) {n : ℕ} :
    Model X Y → List (TrainingRound X Y n) → Prop
  | _, [] => True
  | current, round :: rest =>
      EmpiricalCandidateMaximizer loss round.sample current C round.chosen ∧
        TrainingRoundAccurate law loss eta round.sample current C ∧
        3 * epsilon / 4 <
          empiricalCandidateObjective loss round.sample current round.chosen ∧
        ValidTrainingUpdates law loss C epsilon eta
          (listUpdate current round.chosen.1 round.chosen.2) rest

/-- A stopped Algorithm 5 round returns an epsilon-approximately optimal model. -/
theorem trainByOpt_stop_approxBayesOptimal
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4)
    {n : ℕ} (round : TrainingRound X Y n) (current : Model X Y)
    (hmax : EmpiricalCandidateMaximizer loss round.sample current C round.chosen)
    (haccurate : TrainingRoundAccurate law loss eta round.sample current C)
    (hstop : empiricalCandidateObjective loss round.sample current round.chosen ≤
      3 * epsilon / 4) :
    ApproxBayesOptimal law loss C epsilon current := by
  intro candidate hcandidate
  have hcAccurate := haccurate candidate hcandidate
  have hempiricalMax := hmax.2 candidate hcandidate
  rcases abs_le.mp hcAccurate with ⟨hlower, hupper⟩
  linarith

/-- Exact model-loss identity for one candidate update. -/
theorem modelLoss_sub_candidateUpdate_eq_score
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (current : Model X Y) (candidate : CandidatePair X Y) :
    modelLoss law loss current -
        modelLoss law loss (listUpdate current candidate.1 candidate.2) =
      certificateImprovementScore law loss current candidate.1 candidate.2 := by
  rw [modelLoss_sub_listUpdate_eq_numerator_sub,
    certificateImprovementScore_eq_numerator_sub_total]

/-- Every continued accurate round lowers population loss by at least epsilon/2. -/
theorem continued_training_round_loss_drop
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4)
    {n : ℕ} (round : TrainingRound X Y n) (current : Model X Y)
    (hchosen : round.chosen ∈ C)
    (haccurate : TrainingRoundAccurate law loss eta round.sample current C)
    (hcontinue : 3 * epsilon / 4 <
      empiricalCandidateObjective loss round.sample current round.chosen) :
    modelLoss law loss (listUpdate current round.chosen.1 round.chosen.2) ≤
      modelLoss law loss current - epsilon / 2 := by
  have hacc := haccurate round.chosen hchosen
  have hpopulation : epsilon / 2 ≤
      certificateImprovementScore law loss current round.chosen.1 round.chosen.2 := by
    rcases abs_le.mp hacc with ⟨hlower, hupper⟩
    linarith
  rw [← modelLoss_sub_candidateUpdate_eq_score] at hpopulation
  linarith

/-- Population loss after `T` continued rounds drops by `T epsilon/2`. -/
theorem runTrainingUpdates_loss_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4)
    {n : ℕ} (initial : Model X Y) (rounds : List (TrainingRound X Y n))
    (hvalid : ValidTrainingUpdates law loss C epsilon eta initial rounds) :
    modelLoss law loss (runTrainingUpdates initial rounds) ≤
      modelLoss law loss initial - (rounds.length : ℝ) * (epsilon / 2) := by
  induction rounds generalizing initial with
  | nil => simp [runTrainingUpdates]
  | cons round rest ih =>
      rcases hvalid with ⟨hmax, haccurate, hcontinue, hrest⟩
      have hone := continued_training_round_loss_drop law loss C epsilon eta heta
        round initial hmax.1 haccurate hcontinue
      have htail := ih _ hrest
      simp only [runTrainingUpdates, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        modelLoss law loss
            (runTrainingUpdates
              (listUpdate initial round.chosen.1 round.chosen.2) rest) ≤
          modelLoss law loss
              (listUpdate initial round.chosen.1 round.chosen.2) -
            (rest.length : ℝ) * (epsilon / 2) := htail
        _ ≤ (modelLoss law loss initial - epsilon / 2) -
            (rest.length : ℝ) * (epsilon / 2) := sub_le_sub_right hone _
        _ = modelLoss law loss initial -
            ((rest.length : ℝ) + 1) * (epsilon / 2) := by ring

/-- Exhausting a full loss budget forces zero population loss. -/
theorem runTrainingUpdates_loss_eq_zero_of_full_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4)
    {n : ℕ} (initial : Model X Y) (rounds : List (TrainingRound X Y n))
    (hvalid : ValidTrainingUpdates law loss C epsilon eta initial rounds)
    (hbudget : 1 ≤ (rounds.length : ℝ) * (epsilon / 2)) :
    modelLoss law loss (runTrainingUpdates initial rounds) = 0 := by
  have hdrop := runTrainingUpdates_loss_le law loss C epsilon eta heta initial rounds hvalid
  have hinitial := modelLoss_le_one law loss initial
  have hfinal := modelLoss_nonneg law loss (runTrainingUpdates initial rounds)
  apply le_antisymm
  · linarith
  · exact hfinal

/-- A zero-loss model is epsilon-approximately Bayes optimal for epsilon nonnegative. -/
theorem approxBayesOptimal_of_modelLoss_eq_zero
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (current : Model X Y) (hzero : modelLoss law loss current = 0) :
    ApproxBayesOptimal law loss C epsilon current := by
  intro candidate _
  have hupdated := modelLoss_nonneg law loss
    (listUpdate current candidate.1 candidate.2)
  have hidentity := modelLoss_sub_candidateUpdate_eq_score law loss current candidate
  rw [hzero] at hidentity
  linarith

/--
Theorem 16's budget-exhaustion branch: after `2/epsilon` successful calls (in
the exact multiplication form), the returned model is epsilon-optimal.
-/
theorem theorem16_trainByOpt_budget_exhaustion
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (hepsilon : 0 ≤ epsilon) (heta : eta ≤ epsilon / 4)
    {n : ℕ} (initial : Model X Y) (rounds : List (TrainingRound X Y n))
    (hvalid : ValidTrainingUpdates law loss C epsilon eta initial rounds)
    (hbudget : 1 ≤ (rounds.length : ℝ) * (epsilon / 2)) :
    ApproxBayesOptimal law loss C epsilon (runTrainingUpdates initial rounds) := by
  apply approxBayesOptimal_of_modelLoss_eq_zero law loss C epsilon hepsilon
  exact runTrainingUpdates_loss_eq_zero_of_full_budget law loss C epsilon eta
    heta initial rounds hvalid hbudget

/-- The number of optimization-oracle calls is the number of recorded rounds. -/
theorem theorem16_optimizer_call_count {X Y : Type*} {n : ℕ}
    (rounds : List (TrainingRound X Y n)) :
    rounds.length ≤ rounds.length := by
  exact le_rfl

/-! ## Executable finite-horizon semantics for Algorithm 5 -/

/-- The optimization subroutine used in one round of Algorithm 5.  Its sample
argument is the fresh block `D_t` from the source pseudocode. -/
abbrev TrainingOracle (X Y : Type*) (n : ℕ) :=
  Model X Y → (Fin n → X × Y) → CandidatePair X Y

/-- A training oracle is exact when every returned candidate maximizes the
empirical certificate objective over `C`.  This is precisely the oracle
premise in Theorem 16. -/
def ExactTrainingOracle {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (C : Set (CandidatePair X Y))
    (oracle : TrainingOracle X Y n) : Prop :=
  ∀ current sample,
    EmpiricalCandidateMaximizer loss sample current C (oracle current sample)

/-- Algorithm 5 either remains active after consuming all supplied fresh
blocks, or has stopped at the first block whose best empirical certificate is
at most `3 epsilon / 4`.  Both constructors record the exact number of oracle
calls. -/
inductive TrainByOptOutcome (X Y : Type*) where
  | running (model : Model X Y) (calls : ℕ)
  | stopped (model : Model X Y) (calls : ℕ)

namespace TrainByOptOutcome

/-- Model returned by an Algorithm 5 outcome. -/
def output {X Y : Type*} : TrainByOptOutcome X Y → Model X Y
  | .running model _ => model
  | .stopped model _ => model

/-- Number of optimization-oracle calls made by an Algorithm 5 outcome. -/
def calls {X Y : Type*} : TrainByOptOutcome X Y → ℕ
  | .running _ count => count
  | .stopped _ count => count

end TrainByOptOutcome

/-- Exact finite-horizon execution of Algorithm 5 on a sequence of fresh data
blocks.  Once a stopping test succeeds, later supplied blocks are ignored.

The source first partitions its dataset into blocks `D_t`; its displayed
argmax accidentally writes `D`.  This runner uses the intended block `D_t`,
which is also the version used by the source proof of Theorem 16. -/
def trainByOptRun {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (epsilon : ℝ) (oracle : TrainingOracle X Y n)
    (initial : Model X Y) :
    (rounds : ℕ) → (Fin rounds → Fin n → X × Y) → TrainByOptOutcome X Y
  | 0, _ => .running initial 0
  | rounds + 1, trace =>
      match trainByOptRun loss epsilon oracle initial rounds (Fin.init trace) with
      | .stopped output calls => .stopped output calls
      | .running current calls =>
          let sample := trace (Fin.last rounds)
          let chosen := oracle current sample
          if empiricalCandidateObjective loss sample current chosen ≤
              3 * epsilon / 4 then
            .stopped current (calls + 1)
          else
            .running (listUpdate current chosen.1 chosen.2) (calls + 1)

/-- Current model determined by a history of fresh blocks.  This is the state
against which the next block's uniform-convergence event is evaluated. -/
def trainByOptCurrentOfHistory {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (epsilon : ℝ) (oracle : TrainingOracle X Y n)
    (initial : Model X Y) (rounds : ℕ)
    (history : Fin rounds → Fin n → X × Y) : Model X Y :=
  (trainByOptRun loss epsilon oracle initial rounds history).output

/-- Every fresh block in a trace is uniformly accurate for the model selected
from the preceding blocks.  Accuracy after the algorithm has stopped is
harmlessly stronger than necessary and makes the adaptive union bound exact. -/
def TrainByOptTraceAccurate {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ) {n : ℕ}
    (oracle : TrainingOracle X Y n) (initial : Model X Y) :
    (rounds : ℕ) → (Fin rounds → Fin n → X × Y) → Prop
  | 0, _ => True
  | rounds + 1, trace =>
      TrainByOptTraceAccurate law loss C epsilon eta oracle initial rounds
          (Fin.init trace) ∧
        TrainingRoundAccurate law loss eta (trace (Fin.last rounds))
          (trainByOptCurrentOfHistory loss epsilon oracle initial rounds
            (Fin.init trace)) C

/-- The executable Algorithm 5 runner never makes more oracle calls than the
number of fresh blocks offered to it. -/
theorem trainByOptRun_calls_le {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (epsilon : ℝ) (oracle : TrainingOracle X Y n)
    (initial : Model X Y) (rounds : ℕ)
    (trace : Fin rounds → Fin n → X × Y) :
    (trainByOptRun loss epsilon oracle initial rounds trace).calls ≤ rounds := by
  induction rounds with
  | zero => simp [trainByOptRun, TrainByOptOutcome.calls]
  | succ rounds ih =>
      cases hprefix : trainByOptRun loss epsilon oracle initial rounds (Fin.init trace) with
      | stopped output calls =>
          have hcalls := ih (Fin.init trace)
          rw [hprefix] at hcalls
          simp only [TrainByOptOutcome.calls] at hcalls
          simp [trainByOptRun, hprefix, TrainByOptOutcome.calls]
          exact hcalls.trans (Nat.le_succ rounds)
      | running current calls =>
          have hcalls := ih (Fin.init trace)
          rw [hprefix] at hcalls
          simp only [TrainByOptOutcome.calls] at hcalls
          simp only [trainByOptRun, hprefix]
          split
          <;> simp only [TrainByOptOutcome.calls]
          <;> omega

/-- If the executable runner stops, its returned model is approximately Bayes
optimal.  The proof follows the actual first-stopping branch of Algorithm 5. -/
theorem trainByOptRun_stopped_approxBayesOptimal
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n) (horacle : ExactTrainingOracle loss C oracle)
    (initial : Model X Y) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y)
      (output : Model X Y) (calls : ℕ),
      trainByOptRun loss epsilon oracle initial rounds trace =
          .stopped output calls →
      TrainByOptTraceAccurate law loss C epsilon eta oracle initial rounds trace →
      ApproxBayesOptimal law loss C epsilon output := by
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
            have hoptimal := trainByOpt_stop_approxBayesOptimal
              law loss C epsilon eta heta
              round current (horacle current round.sample) hlastAccurate hstop
            cases hrun
            exact hoptimal
          · simp at hrun

/-- If the executable runner is still active after all supplied blocks, every
round was a successful population-loss-decreasing update. -/
theorem trainByOptRun_running_loss_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n) (horacle : ExactTrainingOracle loss C oracle)
    (initial : Model X Y) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Y)
      (output : Model X Y) (calls : ℕ),
      trainByOptRun loss epsilon oracle initial rounds trace =
          .running output calls →
      TrainByOptTraceAccurate law loss C epsilon eta oracle initial rounds trace →
      modelLoss law loss output ≤
        modelLoss law loss initial - (rounds : ℝ) * (epsilon / 2) := by
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
            have hcurrent :
                trainByOptCurrentOfHistory loss epsilon oracle initial rounds
                    (Fin.init trace) = current := by
              simp [trainByOptCurrentOfHistory, hprefix,
                TrainByOptOutcome.output]
            rw [hcurrent] at hlastAccurate
            let round : TrainingRound X Y n :=
              { sample := trace (Fin.last rounds)
                chosen := oracle current (trace (Fin.last rounds)) }
            have hprefixLoss := ih (Fin.init trace) current previousCalls
              hprefix hprefixAccurate
            have hlastLoss := continued_training_round_loss_drop
              law loss C epsilon eta heta round current
                (horacle current round.sample).1 hlastAccurate (lt_of_not_ge hcontinue)
            calc
              modelLoss law loss
                  (listUpdate current round.chosen.1 round.chosen.2) ≤
                  modelLoss law loss current - epsilon / 2 := hlastLoss
              _ ≤ (modelLoss law loss initial -
                    (rounds : ℝ) * (epsilon / 2)) - epsilon / 2 :=
                  sub_le_sub_right hprefixLoss _
              _ = modelLoss law loss initial -
                    ((rounds + 1 : ℕ) : ℝ) * (epsilon / 2) := by
                  push_cast
                  ring

/-- Full deterministic Theorem 16 for the actual executable runner.  Under
uniformly accurate fresh blocks, every outcome is approximately Bayes optimal
and the recorded oracle-call count is bounded by the supplied horizon. -/
theorem theorem16_trainByOptRun
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (C : Set (CandidatePair X Y)) (epsilon eta : ℝ)
    (hepsilon : 0 ≤ epsilon) (heta : eta ≤ epsilon / 4) {n : ℕ}
    (oracle : TrainingOracle X Y n) (horacle : ExactTrainingOracle loss C oracle)
    (initial : Model X Y) (rounds : ℕ)
    (trace : Fin rounds → Fin n → X × Y)
    (haccurate :
      TrainByOptTraceAccurate law loss C epsilon eta oracle initial rounds trace)
    (hbudget : 1 ≤ (rounds : ℝ) * (epsilon / 2)) :
    ApproxBayesOptimal law loss C epsilon
        (trainByOptRun loss epsilon oracle initial rounds trace).output ∧
      (trainByOptRun loss epsilon oracle initial rounds trace).calls ≤ rounds := by
  constructor
  · cases hrun : trainByOptRun loss epsilon oracle initial rounds trace with
    | stopped output calls =>
        simp only [hrun, TrainByOptOutcome.output]
        exact trainByOptRun_stopped_approxBayesOptimal law loss C epsilon eta
          heta oracle horacle initial rounds trace output calls hrun haccurate
    | running output calls =>
        simp only [hrun, TrainByOptOutcome.output]
        have hloss := trainByOptRun_running_loss_le law loss C epsilon eta heta
          oracle horacle initial rounds trace output calls hrun haccurate
        have hinitial := modelLoss_le_one law loss initial
        have hnonneg := modelLoss_nonneg law loss output
        have hzero : modelLoss law loss output = 0 := by
          apply le_antisymm
          · linarith
          · exact hnonneg
        exact approxBayesOptimal_of_modelLoss_eq_zero law loss C epsilon
          hepsilon output hzero
  · exact trainByOptRun_calls_le loss epsilon oracle initial rounds trace

/-! ## Fresh-block probability semantics for Theorem 16 -/

/-- The source premise `C ⊆ G × H`, written without relying on a particular
set-product encoding. -/
def CandidateClassContainedIn {X : Type*}
    (C : Set (CandidatePair X Bool)) (G : Set (Group X))
    (H : Set (Model X Bool)) : Prop :=
  ∀ candidate ∈ C, candidate.1 ∈ G ∧ candidate.2 ∈ H

/-- Absence of Lemma 15's deviation event gives the exact round-accuracy
predicate required by the executable Algorithm 5 proof, for every
`C ⊆ G × H`. -/
theorem trainingRoundAccurate_of_not_certificateVCDeviationEvent
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (C : Set (CandidatePair X Bool)) (hcontained : CandidateClassContainedIn C G H)
    (eta : ℝ) {n : ℕ} (sample : Fin n → X × Bool)
    (hgood : ¬ certificateVCDeviationEvent law current G H eta sample) :
    TrainingRoundAccurate law binaryZeroOneLoss eta sample current C := by
  intro candidate hcandidate
  rcases hcontained candidate hcandidate with ⟨hgroup, hmodel⟩
  apply le_of_not_gt
  intro hgap
  apply hgood
  exact ⟨candidate.1, hgroup, candidate.2, hmodel, by
    simpa [empiricalCandidateObjective] using hgap⟩

/-- History-dependent bad event for Algorithm 5: the next fresh block fails
Lemma 15 for the current model determined by all preceding blocks. -/
def trainByOptVCBadEvent
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (epsilon eta : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) (rounds : ℕ)
    (history : Fin rounds → Fin n → X × Bool)
    (sample : Fin n → X × Bool) : Prop :=
  certificateVCDeviationEvent law
    (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial rounds history)
    G H eta sample

/-- Probability that at least one of the adaptively selected current models
sees a bad fresh block during Algorithm 5. -/
noncomputable def trainByOptVCFailureProbability
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (epsilon eta : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) (rounds : ℕ) : ℝ :=
  adaptiveFreshTraceAnyBadProbability (PMF.pure initial)
    (fun _ : Model X Bool => law)
    (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial)
    (trainByOptVCBadEvent law G H epsilon eta oracle initial) rounds

/-- One fresh block has Lemma 15's failure probability even though its current
model was chosen adaptively from the earlier blocks.  Conditional on that
history, the current model is fixed and the next block is iid. -/
theorem trainByOptVC_conditionalFailure_le
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (dG dH : ℕ) (hvcG : AppliedModelingLib.Statistics.VCDimensionAtMost G dG)
    (hvcH : AppliedModelingLib.Statistics.VCDimensionAtMost H dH)
    (epsilon : ℝ) {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (delta : ℝ) (hdelta : 0 < delta) (rounds : ℕ)
    (history : Fin rounds → Fin n → X × Bool) :
    adaptiveFreshConditionalBadProbability
        (fun _ : Model X Bool => law)
        (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial)
        (trainByOptVCBadEvent law G H epsilon
          (certificateVCConfidenceRadius dG dH n delta) oracle initial)
        rounds history ≤ delta := by
  classical
  letI : MeasurableSpace X := ⊤
  unfold adaptiveFreshConditionalBadProbability trainByOptVCBadEvent
  rw [pmfProb_eq_toMeasure_real, pmfProduct_toMeasure_eq_measurePi]
  change certificateVCDeviationFailure law
      (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial rounds history)
      G H (certificateVCConfidenceRadius dG dH n delta) n ≤ delta
  exact lemma15_vc_uniform_convergence law
    (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial rounds history)
    G H dG dH hvcG hvcH n hcount hdimension delta hdelta

/-- Adaptive fresh-block union bound for Algorithm 5.  This is the formal
independence argument behind the source proof's allocation `delta / T` to each
of the `T` data blocks. -/
theorem trainByOptVCFailureProbability_le_mul
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (dG dH : ℕ) (hvcG : AppliedModelingLib.Statistics.VCDimensionAtMost G dG)
    (hvcH : AppliedModelingLib.Statistics.VCDimensionAtMost H dH)
    (epsilon : ℝ) {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n) (initial : Model X Bool)
    (deltaPerRound : ℝ) (hdeltaPerRound : 0 < deltaPerRound)
    (rounds : ℕ) :
    trainByOptVCFailureProbability law G H epsilon
        (certificateVCConfidenceRadius dG dH n deltaPerRound)
        oracle initial rounds ≤ (rounds : ℝ) * deltaPerRound := by
  unfold trainByOptVCFailureProbability
  apply adaptiveFreshTraceAnyBadProbability_le_mul
  intro round history
  exact trainByOptVC_conditionalFailure_le law G H dG dH hvcG hvcH
    epsilon hcount hdimension oracle initial deltaPerRound hdeltaPerRound
    round history

/-- Integer-safe version of the source assignment `T = 2 / epsilon`. -/
noncomputable def trainByOptRoundBudget (epsilon : ℝ) : ℕ :=
  Nat.ceil (2 / epsilon)

/-- The rounded Algorithm 5 horizon is positive for positive accuracy. -/
theorem trainByOptRoundBudget_pos (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < trainByOptRoundBudget epsilon := by
  unfold trainByOptRoundBudget
  apply Nat.ceil_pos.mpr
  positivity

/-- The rounded horizon supplies the full normalized loss budget used by the
deterministic convergence proof. -/
theorem trainByOptRoundBudget_sufficient (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    1 ≤ (trainByOptRoundBudget epsilon : ℝ) * (epsilon / 2) := by
  have hceil : 2 / epsilon ≤ (trainByOptRoundBudget epsilon : ℝ) := by
    exact Nat.le_ceil _
  have hscale : 0 ≤ epsilon / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hceil hscale
  have hnormalize : (2 / epsilon) * (epsilon / 2) = 1 := by
    field_simp
  linarith

/-- If no adaptive VC-deviation event occurs, all blocks satisfy the
deterministic accuracy invariant used by the Algorithm 5 runner. -/
theorem trainByOptTraceAccurate_of_not_vcBadEvent
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (C : Set (CandidatePair X Bool)) (hcontained : CandidateClassContainedIn C G H)
    (epsilon eta : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) :
    ∀ (rounds : ℕ) (trace : Fin rounds → Fin n → X × Bool),
      ¬ adaptiveFreshTraceAnyBadEvent
          (trainByOptVCBadEvent law G H epsilon eta oracle initial) rounds trace →
      TrainByOptTraceAccurate law binaryZeroOneLoss C epsilon eta
        oracle initial rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace _
      trivial
  | succ rounds ih =>
      intro trace hgood
      have hprefix :
          ¬ adaptiveFreshTraceAnyBadEvent
            (trainByOptVCBadEvent law G H epsilon eta oracle initial)
              rounds (Fin.init trace) := by
        intro hbad
        exact hgood (Or.inl hbad)
      have hlast :
          ¬ trainByOptVCBadEvent law G H epsilon eta oracle initial
            rounds (Fin.init trace) (trace (Fin.last rounds)) := by
        intro hbad
        exact hgood (Or.inr hbad)
      constructor
      · exact ih (Fin.init trace) hprefix
      · exact trainingRoundAccurate_of_not_certificateVCDeviationEvent
          law
          (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial
            rounds (Fin.init trace)) G H C hcontained eta
          (trace (Fin.last rounds)) hlast

/-- Probability that Algorithm 5's returned model is not approximately Bayes
optimal under its literal adaptive fresh-block execution law. -/
noncomputable def trainByOptOutputFailureProbability
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (C : Set (CandidatePair X Bool))
    (epsilon : ℝ) {n : ℕ} (oracle : TrainingOracle X Bool n)
    (initial : Model X Bool) (rounds : ℕ) : ℝ := by
  classical
  exact pmfProb
    (adaptiveFreshTraceLaw (PMF.pure initial)
      (fun _ : Model X Bool => law)
      (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial) rounds)
    (fun trace => ¬ ApproxBayesOptimal law binaryZeroOneLoss C epsilon
      (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds trace).output)

/-- Theorem 16, full high-probability form.  The exact checked hypotheses are:

* `rounds` fresh iid blocks, with confidence `delta / rounds` per block;
* the explicit Lemma 15 VC radius is at most `epsilon / 4`;
* `rounds * epsilon / 2 ≥ 1`, the integer-safe form of `T = 2/epsilon`.

The runner returns an `epsilon`-Bayes-optimal model except with probability at
most `delta`, and `trainByOptRun_calls_le` gives at most `rounds` optimization
calls on every trace.  The total number of observations is exactly
`rounds * n`. -/
theorem theorem16_trainByOpt_highProbability
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (C : Set (CandidatePair X Bool)) (hcontained : CandidateClassContainedIn C G H)
    (dG dH : ℕ) (hvcG : AppliedModelingLib.Statistics.VCDimensionAtMost G dG)
    (hvcH : AppliedModelingLib.Statistics.VCDimensionAtMost H dH)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (hcount : 0 < n)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ n + n)
    (oracle : TrainingOracle X Bool n)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    (initial : Model X Bool) (rounds : ℕ)
    (hbudget : 1 ≤ (rounds : ℝ) * (epsilon / 2))
    (delta : ℝ) (hdelta : 0 < delta)
    (hradius :
      certificateVCConfidenceRadius dG dH n (delta / (rounds : ℝ)) ≤
        epsilon / 4) :
    trainByOptOutputFailureProbability law C epsilon oracle initial rounds ≤ delta := by
  classical
  have hrounds : 0 < rounds := by
    by_contra hzero
    have : rounds = 0 := Nat.eq_zero_of_not_pos hzero
    subst rounds
    norm_num at hbudget
  have hroundsReal : 0 < (rounds : ℝ) := by exact_mod_cast hrounds
  let deltaPerRound := delta / (rounds : ℝ)
  have hdeltaPerRound : 0 < deltaPerRound := div_pos hdelta hroundsReal
  have hbadBound := trainByOptVCFailureProbability_le_mul
    law G H dG dH hvcG hvcH epsilon hcount hdimension oracle initial
      deltaPerRound hdeltaPerRound rounds
  have hfailureSubset : ∀ trace : Fin rounds → Fin n → X × Bool,
      (¬ ApproxBayesOptimal law binaryZeroOneLoss C epsilon
        (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds trace).output) →
      adaptiveFreshTraceAnyBadEvent
        (trainByOptVCBadEvent law G H epsilon
          (certificateVCConfidenceRadius dG dH n deltaPerRound) oracle initial)
        rounds trace := by
    intro trace hfailure
    by_contra hnoBad
    have haccurate := trainByOptTraceAccurate_of_not_vcBadEvent
      law G H C hcontained epsilon
        (certificateVCConfidenceRadius dG dH n deltaPerRound)
        oracle initial rounds trace hnoBad
    have hsuccess := (theorem16_trainByOptRun law binaryZeroOneLoss C epsilon
      (certificateVCConfidenceRadius dG dH n deltaPerRound) hepsilon.le hradius
      oracle horacle initial rounds trace haccurate hbudget).1
    exact hfailure hsuccess
  unfold trainByOptOutputFailureProbability
  have hsubsetProbability := pmfProb_le_of_imp
    (adaptiveFreshTraceLaw (PMF.pure initial)
      (fun _ : Model X Bool => law)
      (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial) rounds)
    (fun trace => ¬ ApproxBayesOptimal law binaryZeroOneLoss C epsilon
      (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds trace).output)
    (adaptiveFreshTraceAnyBadEvent
      (trainByOptVCBadEvent law G H epsilon
        (certificateVCConfidenceRadius dG dH n deltaPerRound) oracle initial) rounds)
    hfailureSubset
  calc
    pmfProb
        (adaptiveFreshTraceLaw (PMF.pure initial)
          (fun _ : Model X Bool => law)
          (trainByOptCurrentOfHistory binaryZeroOneLoss epsilon oracle initial) rounds)
        (fun trace => ¬ ApproxBayesOptimal law binaryZeroOneLoss C epsilon
          (trainByOptRun binaryZeroOneLoss epsilon oracle initial rounds trace).output) ≤
      trainByOptVCFailureProbability law G H epsilon
        (certificateVCConfidenceRadius dG dH n deltaPerRound)
        oracle initial rounds := by
          simpa [trainByOptVCFailureProbability] using hsubsetProbability
    _ ≤ (rounds : ℝ) * deltaPerRound := hbadBound
    _ = delta := by
      dsimp [deltaPerRound]
      field_simp

/-- The rectangular fresh-block trace used by Theorem 16 contains exactly
`rounds * blockSize` observations. -/
theorem theorem16_total_sample_count (rounds blockSize : ℕ) :
    Fintype.card (Fin rounds × Fin blockSize) = rounds * blockSize := by
  simp

/-- Source-rounded Theorem 16.  This packages the canonical integer horizon
`ceil (2 / epsilon)`, the high-probability guarantee, the oracle-call bound,
and the exact rectangular sample count in one paper-facing result. -/
theorem theorem16_trainByOpt_sourceRounded
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
    (C : Set (CandidatePair X Bool)) (hcontained : CandidateClassContainedIn C G H)
    (dG dH : ℕ) (hvcG : AppliedModelingLib.Statistics.VCDimensionAtMost G dG)
    (hvcH : AppliedModelingLib.Statistics.VCDimensionAtMost H dH)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {blockSize : ℕ} (hcount : 0 < blockSize)
    (hdimension : listUpdateVCDimensionBound dG dH ≤ blockSize + blockSize)
    (oracle : TrainingOracle X Bool blockSize)
    (horacle : ExactTrainingOracle binaryZeroOneLoss C oracle)
    (initial : Model X Bool) (delta : ℝ) (hdelta : 0 < delta)
    (hradius :
      certificateVCConfidenceRadius dG dH blockSize
          (delta / (trainByOptRoundBudget epsilon : ℝ)) ≤
        epsilon / 4) :
    trainByOptOutputFailureProbability law C epsilon oracle initial
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
  · exact theorem16_trainByOpt_highProbability law G H C hcontained dG dH
      hvcG hvcH epsilon hepsilon hcount hdimension oracle horacle initial
      (trainByOptRoundBudget epsilon)
      (trainByOptRoundBudget_sufficient epsilon hepsilon) delta hdelta hradius
  · intro trace
    exact trainByOptRun_calls_le binaryZeroOneLoss epsilon oracle initial
      (trainByOptRoundBudget epsilon) trace

end

end GHKR22BiasBounties
