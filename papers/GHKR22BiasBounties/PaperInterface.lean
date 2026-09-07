import GHKR22BiasBounties.DistributionalPaperInterface
import GHKR22BiasBounties.Assumptions

/-!
# Human-facing paper interface: An Algorithmic Framework for Bias Bounties

This is the compact semantic-review surface for the paper.  The executable
algorithm specifications use finite PMFs, so they cover every finite-support
population law and every empirical law.  The measure-theoretic endpoints cover
arbitrary population laws.  The loss is the paper's arbitrary `[0,1]`-valued
loss except in the binary-classification reductions, where the source
specializes to zero-one loss.

The finite/executable specifications below make the source repairs explicit;
the arbitrary-distribution theorem surface is in
`DistributionalPaperInterface.lean`.  Theorem 11 uses
the exact sparse-transcript count and an explicit failure probability because
the displayed source statement has an undefined confidence symbol and an
incorrect transcript inequality.  Algorithm 4 is one global state machine:
external and internal repair submissions share a checker, and every accepted
repair restarts the full protected-history scan.  Algorithm 5 optimizes on the fresh block `D_t` (the pseudocode writes
`D`, while its proof requires `D_t`) and uses the integer-safe horizon
`ceil (2/epsilon)`.  Lemma 22 uses the exact disagreement-loss identity.
Algorithm 6 is the minimal two-gap coordinate-ascent correction; its
positive-score premise is separated from local optimality, since local
optimality alone does not imply a positive certificate.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Statistics

/-- The finite ternary alphabet has the discrete sigma algebra in the
arbitrary-population source interface. -/
local instance paperInterfaceTernaryLabelMeasurableSpace :
    MeasurableSpace TernaryLabel := ⊤

/-! ## Definitions 1--7 -/

/-- Definition 1: a subgroup is a Boolean predicate and its population mass is
the expectation of its membership indicator. -/
def definition1_subgroupsSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (g : Group X),
    groupMass law g =
      AppliedModelingLib.pmfExp law (fun datum => if g datum.1 then 1 else 0)

/-- Definition 2: overall loss is expected pointwise loss, while group loss is
the mass-weighted group numerator divided by group mass.  The Lean definition
uses the standard totalized division value zero when the group has zero mass. -/
def definition2_modelLossSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (f : Model X Y) (g : Group X),
    modelLoss law loss f =
        AppliedModelingLib.pmfExp law (fun datum => loss.value (f datum.1) datum.2) ∧
      groupLoss law loss f g =
        groupLossNumerator law loss f g / groupMass law g

/-- Definition 3: Bayes optimality is pointwise minimization of conditional
risk.  Multiplying by the feature mass gives the division-free formula below,
which is also meaningful off support. -/
def definition3_bayesOptimalSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y),
    BayesOptimal law loss f ↔
      ∀ x prediction,
        pointwiseRiskNumerator law loss x (f x) ≤
          pointwiseRiskNumerator law loss x prediction

/-- Definition 5: the primitive, zero-mass-safe condition is the paper's
mass-weighted inequality.  If all certified groups have positive mass it is
equivalent to the source's displayed conditional-loss formula. -/
def definition5_approxBayesOptimalSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (certificates : Set (Group X × Model X Y))
      (epsilon : ℝ) (f : Model X Y),
    (ApproxBayesOptimal law loss certificates epsilon f ↔
      ∀ pair ∈ certificates,
        certificateImprovementScore law loss f pair.1 pair.2 ≤ epsilon) ∧
    ((∀ pair ∈ certificates, 0 < groupMass law pair.1) →
      (ApproxBayesOptimal law loss certificates epsilon f ↔
        ∀ pair ∈ certificates,
          groupLoss law loss f pair.1 ≤
            groupLoss law loss pair.2 pair.1 +
              epsilon / groupMass law pair.1))

/-- Definition 7: a `(mu, Delta)` certificate consists exactly of positive
parameters, sufficient group mass, and the asserted conditional-loss gap. -/
def definition7_certificateSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (f : Model X Y) (g : Group X) (h : Model X Y) (mu Delta : ℝ),
    CertificateOfSuboptimality law loss f g h mu Delta ↔
      0 < mu ∧ 0 < Delta ∧ mu ≤ groupMass law g ∧
        groupLoss law loss h g + Delta ≤ groupLoss law loss f g

/-- The empirical certificate-optimization problem displayed before
Algorithm 5.  The relational maximizer form makes the source's `arg max`
meaning explicit without assuming a choice operator. -/
def certificateOptimizationObjectiveSpec : Prop :=
  ∀ {X Y : Type*} {n : ℕ}
      (loss : BoundedLoss Y) (sample : Fin n → X × Y)
      (current : Model X Y) (candidates : Set (CandidatePair X Y))
      (chosen : CandidatePair X Y),
    EmpiricalCandidateMaximizer loss sample current candidates chosen ↔
      chosen ∈ candidates ∧ ∀ candidate ∈ candidates,
        empiricalCandidateObjective loss sample current candidate ≤
          empiricalCandidateObjective loss sample current chosen

/-! ## Observation 4, Algorithm 1, and Theorems 8--10 -/

/-- Observation 4: pointwise Bayes optimality is equivalent to optimality on
every Boolean subgroup. -/
def observation4_bayes_groupwiseSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y),
    BayesOptimal law loss f ↔ GroupwiseOptimal law loss f

/-- Audit-only boundary for the paper's advertised arbitrary-distribution
domain.  On the continuous uniform law, a measurable model changed at the
null support point `1/2` is optimal on every measurable group but is not
pointwise Bayes optimal there.  Thus the printed pointwise Observation 4 needs
an almost-everywhere reformulation outside the finite-support setting. -/
def observation4_arbitraryDistribution_counterexampleSpec : Prop :=
  OptimalOnEveryMeasurableGroup observation4UniformFeatureLaw
      observation4NullSpikeModel ∧
    ¬ PointwiseBayesOnSupport observation4UniformFeatureLaw
      observation4NullSpikeModel

/-- Repaired arbitrary-distribution Observation 4.  Given a Markov kernel for
the conditional label law, almost-everywhere optimality against every
integrable alternative model is equivalent to optimality on every measurable
group.  This modelwise form allows an arbitrary label space; for countable
labels it agrees with the common-null-set actionwise Bayes formulation. -/
def source_observation4Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (featureLaw : MeasureTheory.Measure X)
      [MeasureTheory.IsProbabilityMeasure featureLaw]
      (labels : ProbabilityTheory.Kernel X Y)
      [ProbabilityTheory.IsMarkovKernel labels]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ current : Model X Y, MeasurableModel current →
    (AEOptimalAgainstEveryIntegrableModelForRisk featureLaw
          (kernelConditionalRisk labels loss) current ↔
        OptimalOnEveryMeasurableGroupForRisk featureLaw
          (kernelConditionalRisk labels loss) current)

universe u v

/-- Reusable name for the canonical source-facing Observation 4 proposition. -/
abbrev observation4_arbitraryDistribution_aeSpec : Prop :=
  source_observation4Spec.{u, v}

/-- Theorem 8: a certificate with product larger than `epsilon` exists exactly
when the current model is not `epsilon`-approximately Bayes optimal. -/
def theorem8_certificate_characterizationSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (certificates : Set (Group X × Model X Y))
      (epsilon : ℝ), 0 ≤ epsilon → ∀ f : Model X Y,
    (∃ g h mu Delta,
        (g, h) ∈ certificates ∧
        CertificateOfSuboptimality law loss f g h mu Delta ∧
        epsilon < mu * Delta) ↔
      ¬ ApproxBayesOptimal law loss certificates epsilon f

/-- Algorithm 1: pointwise list update uses the replacement on the submitted
group and preserves the current model off that group. -/
def algorithm1_listUpdateSpec : Prop :=
  ∀ {X Y : Type*} (f : Model X Y) (g : Group X) (h : Model X Y) (x : X),
    listUpdate f g h x = if g x then h x else f x

/-- Theorem 9: list update exactly installs the submitted group predictor and
decreases total loss by at least the certificate value. -/
def theorem9_listUpdate_progressSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      {law : Distribution X Y} {loss : BoundedLoss Y}
      {f : Model X Y} {g : Group X} {h : Model X Y} {mu Delta : ℝ},
    CertificateOfSuboptimality law loss f g h mu Delta →
      groupLoss law loss (listUpdate f g h) g = groupLoss law loss h g ∧
      modelLoss law loss (listUpdate f g h) ≤
        modelLoss law loss f - mu * Delta

/-- Theorem 10: a sequence of accepted updates of value at least `epsilon`
has length at most the initial loss divided by `epsilon`, hence at most
`1 / epsilon`. -/
def theorem10_update_countSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (epsilon : ℝ), 0 < epsilon →
      ∀ (initial : Model X Y) (updates : List (Update X Y)),
      ValidUpdateSequence law loss epsilon initial updates →
        (updates.length : ℝ) ≤ modelLoss law loss initial / epsilon ∧
        modelLoss law loss initial / epsilon ≤ 1 / epsilon

/-! ## Adaptive certificate checking and falsify-and-update -/

/-- Algorithm 2's exact empirical threshold semantics. -/
def algorithm2_certificateCheckerSpec : Prop :=
  ∀ {X Y : Type*} {n : ℕ}
      (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
      (submission : Submission X Y),
    (certificateCheckerDecision epsilon loss sample submission = .accepted ↔
      3 * epsilon / 4 ≤ empiricalSubmissionScore loss sample submission) ∧
    (certificateCheckerDecision epsilon loss sample submission = .rejected ↔
      empiricalSubmissionScore loss sample submission < 3 * epsilon / 4)

/-- Corrected Theorem 11 for the literal recursive Algorithm 2 runner.  Every
transcript-adaptive strategy is encoded into an exact sparse family of size
`U * (U+1)^floor(2/epsilon)`.  The displayed probability is the chance that
some actually issued accept/reject decision violates the source semantics. -/
def theorem11_adaptive_certificate_checkerSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (epsilon : ℝ), 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ strategy : AdaptiveSubmissionStrategy X Y,
      certificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
        (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Algorithm 3's executable transition uses the checker's actual decision,
keeps the model on rejection, and applies ListUpdate on acceptance. -/
def algorithm3_falsifyAndUpdateSpec : Prop :=
  ∀ {X Y : Type*} {n : ℕ}
      (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
      (state : FalsifyState X Y) (proposal : ProposedUpdate X Y),
    let decision := certificateCheckerDecision epsilon loss sample
      (proposalSubmission state proposal)
    let output := falsifyAndUpdateStep epsilon loss sample state proposal
    match decision with
    | .rejected =>
        output.current = state.current ∧ output.accepted = state.accepted
    | .accepted =>
        output.current = listUpdate state.current proposal.group proposal.replacement ∧
          output.accepted = state.accepted + 1

/-- Theorem 12 for the literal transcript-adaptive Algorithm 3 runner.  The
bad event includes any incorrect accept/reject semantics, premature halt, or
violation of the `2 / epsilon` update budget. -/
def theorem12_falsifyAndUpdateSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (epsilon : ℝ), 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y),
      adaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
        (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Remark 13: sparse transcripts yield an exact family size
`U * (U+1)^K`, independent of the submitted models' syntactic complexity. -/
def remark13_logarithmic_submission_dependenceSpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (U K : ℕ) (family : AdaptiveQueryIndex U K → Submission X Y)
      (epsilon : ℝ) (n : ℕ), 0 < n → 0 ≤ epsilon →
      letI : TopologicalSpace (AdaptiveQueryIndex U K) := ⊤
      adaptiveCheckerDeviationFailure law loss family epsilon n ≤
        (U * (U + 1) ^ K : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Corrected whole-process Algorithm 4 semantics.  Both external proposals
and repairs are queried through the same `CertificateChecker` transcript.  An
accepted external proposal and an accepted repair both install the list update
and restart the complete protected-group/public-model scan; a rejected repair
advances that scan.  The rounded global horizon is
`U + floor(2/epsilon)^3`. -/
def algorithm4_monotoneBountySpec : Prop :=
  (∀ {X Y : Type*} {n : ℕ}
      (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
      (U : ℕ) (initial : Model X Y)
      (strategy : AdaptiveMonotoneProposalStrategy X Y),
    monotoneBountyTranscript epsilon loss sample U initial strategy =
      certificateCheckerRun epsilon loss sample
        (monotoneBountyQueryBudget epsilon U)
        (monotoneBountySubmissionStrategy initial U strategy)) ∧
  (∀ {X Y : Type*} (initial : Model X Y) (U : ℕ)
      (strategy : AdaptiveMonotoneProposalStrategy X Y)
      (transcript : List CertificateDecision)
      (decision : CertificateDecision),
    let state := monotoneBountyStateFromTranscript initial U strategy transcript
    monotoneBountySubmissionStrategy initial U strategy transcript =
        monotoneBountySubmission U strategy state ∧
      monotoneBountyStateFromTranscript initial U strategy
          (transcript ++ [decision]) =
        monotoneBountyStepFromDecision U strategy state decision ∧
      (∀ (candidate : ProposedUpdate X Y) (rest : List (ProposedUpdate X Y)),
        state.remainingRepairs = candidate :: rest →
        monotoneBountyStepCore U strategy state .accepted =
          restartMonotoneRepairScan
            { state with
              current := listUpdate state.current candidate.group
                candidate.replacement
              accepted := state.accepted + 1 }) ∧
      (state.remainingRepairs = [] → state.externalProcessed < U →
        monotoneBountyStepCore U strategy state .accepted =
          restartMonotoneRepairScan
            { state with
              current := listUpdate state.current
                (strategy state.reverseTranscript.reverse).group
                (strategy state.reverseTranscript.reverse).replacement
              accepted := state.accepted + 1
              externalProcessed := state.externalProcessed + 1
              protectedGroups :=
                (strategy state.reverseTranscript.reverse).group ::
                  state.protectedGroups }) ∧
      (∀ (candidate : ProposedUpdate X Y) (rest : List (ProposedUpdate X Y)),
        state.remainingRepairs = candidate :: rest →
        monotoneBountyStepCore U strategy state .rejected =
          let advanced :=
            { state with
              remainingRepairs := rest
              rejectedRepairsReverse :=
                candidate :: state.rejectedRepairsReverse }
          match rest with
          | [] => publishMonotoneBountyState advanced
          | _ :: _ => advanced)) ∧
  (∀ epsilon : ℝ, ∀ U : ℕ,
    monotoneBountyQueryBudget epsilon U =
      U + checkerAcceptanceBudget epsilon ^ 3)

/-- Corrected whole-process Theorem 14.  One shared checker processes adaptive
external proposals and internal repairs.  Its bad event includes any local
checker-semantic error, premature halt, failure to finish all proposals and the
last scan, excess accepted updates, or a nonmonotone published model. -/
def theorem14_monotoneBountySpec : Prop :=
  ∀ {X Y : Type*} [Fintype X] [Fintype Y]
      [DecidableEq X] [DecidableEq Y]
      (law : Distribution X Y) (loss : BoundedLoss Y)
      (epsilon : ℝ), 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ (initial : Model X Y)
        (strategy : AdaptiveMonotoneProposalStrategy X Y),
      monotoneBountyFailure law loss epsilon n U initial strategy ≤
        let Q := monotoneBountyQueryBudget epsilon U
        (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-! ## Uniform-convergence training -/

/-- Lemma 15 with an explicit VC radius.  The checked list-update closure has
dimension at most the ceiling of
`2 D log₂(eD)`, where `D=(d_G+1)+(d_H+1)`; this makes the source's
soft-linear `\widetilde O(d_G+d_H)` dependence precise. -/
def lemma15_vc_uniform_convergenceSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (G : Set (Group X)) (H : Set (Model X Bool))
      (dG dH : ℕ),
      AppliedModelingLib.Statistics.VCDimensionAtMost G dG →
      AppliedModelingLib.Statistics.VCDimensionAtMost H dH →
      ∀ (n : ℕ), 0 < n →
      listUpdateVCDimensionBound dG dH ≤ n + n →
      ∀ delta : ℝ, 0 < delta →
      certificateVCDeviationFailure law current G H
          (certificateVCConfidenceRadius dG dH n delta) n ≤ delta

/-- Corrected Algorithm 5 semantics.  At every round the optimizer returns an
empirical maximizer for that round's block `D_t`; the runner tests that same
block, stops at the threshold, and otherwise installs the selected list
update.  The source's real-valued horizon is interpreted as an integer ceiling.
-/
def algorithm5_trainByOptSpec : Prop :=
  (∀ {X Y : Type*} {n : ℕ}
      (loss : BoundedLoss Y) (C : Set (CandidatePair X Y)) (epsilon : ℝ)
      (oracle : TrainingOracle X Y n) (initial : Model X Y),
    (∀ current sample,
      oracle current sample ∈ C ∧
        ∀ candidate ∈ C,
          empiricalCandidateObjective loss sample current candidate ≤
            empiricalCandidateObjective loss sample current
              (oracle current sample)) →
    (∀ trace : Fin 0 → Fin n → X × Y,
      trainByOptRun loss epsilon oracle initial 0 trace = .running initial 0) ∧
    ∀ (rounds : ℕ) (trace : Fin (rounds + 1) → Fin n → X × Y),
      trainByOptRun loss epsilon oracle initial (rounds + 1) trace =
        match trainByOptRun loss epsilon oracle initial rounds (Fin.init trace) with
        | .stopped output calls => .stopped output calls
        | .running current calls =>
            let sample := trace (Fin.last rounds)
            let chosen := oracle current sample
            if empiricalCandidateObjective loss sample current chosen ≤
                3 * epsilon / 4 then
              .stopped current (calls + 1)
            else
              .running (listUpdate current chosen.1 chosen.2) (calls + 1)) ∧
  (∀ epsilon : ℝ, 0 < epsilon →
    trainByOptRoundBudget epsilon = Nat.ceil (2 / epsilon))

/-- Theorem 16 in full high-probability form.  Algorithm 5 uses
`ceil (2/epsilon)` fresh blocks, allocates confidence `delta/T` to each block,
and assumes the explicit Lemma 15 radius is at most `epsilon/4`.  Its returned
model fails `epsilon`-Bayes optimality with probability at most `delta`; every
execution makes at most `T` exact-optimization calls; and the sample rectangle
has exactly `T * blockSize` observations. -/
def theorem16_trainByOptSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (G : Set (Group X)) (H : Set (Model X Bool))
      (C : Set (CandidatePair X Bool)),
      CandidateClassContainedIn C G H →
      ∀ (dG dH : ℕ),
      AppliedModelingLib.Statistics.VCDimensionAtMost G dG →
      AppliedModelingLib.Statistics.VCDimensionAtMost H dH →
      ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ {blockSize : ℕ}, 0 < blockSize →
      listUpdateVCDimensionBound dG dH ≤ blockSize + blockSize →
      ∀ (oracle : TrainingOracle X Bool blockSize),
      ExactTrainingOracle binaryZeroOneLoss C oracle →
      ∀ (initial : Model X Bool) (delta : ℝ), 0 < delta →
      certificateVCConfidenceRadius dG dH blockSize
          (delta / (trainByOptRoundBudget epsilon : ℝ)) ≤ epsilon / 4 →
      trainByOptOutputFailureProbability law C epsilon oracle initial
          (trainByOptRoundBudget epsilon) ≤ delta ∧
        (∀ trace : Fin (trainByOptRoundBudget epsilon) →
            Fin blockSize → X × Bool,
          (trainByOptRun binaryZeroOneLoss epsilon oracle initial
            (trainByOptRoundBudget epsilon) trace).calls ≤
              trainByOptRoundBudget epsilon) ∧
        Fintype.card
            (Fin (trainByOptRoundBudget epsilon) × Fin blockSize) =
          trainByOptRoundBudget epsilon * blockSize

/-! ## Cost-sensitive and alternating optimization reductions -/

/-- Definition 17: non-deferral determines the derived group, and the ternary
prediction determines the derived binary model (zero is the harmless value on
deferred points). -/
def definition17_derivedCertificateSpec : Prop :=
  ∀ {X : Type*} (p : TernaryPredictor X) (x : X),
    derivedGroup p x = (p x != .defer) ∧
      derivedModel p x =
        match p x with
        | .zero => false
        | .one => true
        | .defer => false

/-- Definition 18: a cost-sensitive solution is precisely a member of `K`
whose expected induced cost is no larger than every other member's cost. -/
def definition18_costSensitiveMinimizerSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X),
    CostSensitiveMinimizer law current K pStar ↔
      pStar ∈ K ∧ ∀ p ∈ K,
        expectedTernaryCost law current pStar ≤
          expectedTernaryCost law current p

/-- Definition 19: the induced cost has the source's `0, 1, -1, 0` cases. -/
def definition19_inducedCostSpec : Prop :=
  ∀ {X : Type*} (current : Model X Bool)
      (datum : X × Bool) (prediction : TernaryLabel),
    inducedCost current datum prediction =
      if prediction = .defer then 0
      else if current datum.1 = datum.2 ∧
          ternaryBinaryPrediction prediction ≠ datum.2 then 1
      else if ternaryBinaryPrediction prediction = datum.2 ∧
          current datum.1 ≠ datum.2 then -1
      else 0

/-- Theorem 20: minimizing the induced ternary cost exactly maximizes the
binary certificate objective over the induced pair class. -/
def theorem20_ternary_cost_sensitive_reductionSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X),
      CostSensitiveMinimizer law current K pStar →
      DerivedCertificateMaximizer law current K pStar

/-- Lemma 21: ERM on a fixed group returns a fixed-group certificate-objective
maximizer. -/
def lemma21_group_erm_reductionSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (g : Group X) (H : Set (Model X Bool)) (hStar : Model X Bool),
      GroupRestrictedERM law g H hStar →
      hStar ∈ H ∧ ∀ h ∈ H,
        binaryCertificateObjective law current g h ≤
          binaryCertificateObjective law current g hStar

/-- Corrected Lemma 22: ERM under the exact disagreement-loss construction
returns a fixed-model certificate-objective maximizer. -/
def lemma22_disagreement_erm_reductionSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current replacement : Model X Bool)
      (G : Set (Group X)) (gStar : Group X),
      DisagreementERM law current replacement G gStar →
      gStar ∈ G ∧ ∀ g ∈ G,
        binaryCertificateObjective law current g replacement ≤
        binaryCertificateObjective law current gStar replacement

/-- Corrected Algorithm 6 semantics: halting certifies both coordinate gaps,
and every successful coordinate move gains strictly more than `epsilon`. -/
def algorithm6_twoGapCoordinateAscentSpec : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
      (oracle : CoordinateBestResponses law current G H)
      (pair : CertificatePair X),
    PairAdmissible G H pair →
      (coordinateAscentStep law current epsilon oracle pair = none →
        EpsilonCoordinatewiseLocal law current G H epsilon pair) ∧
      (∀ next,
        coordinateAscentStep law current epsilon oracle pair = some next →
          PairAdmissible G H next ∧
          binaryCertificateObjective law current pair.group pair.replacement + epsilon <
            binaryCertificateObjective law current next.group next.replacement)

/-- Corrected Theorem 23: the two-gap coordinate loop returns a two-sided
`epsilon` local optimum when it succeeds, every improving trajectory has at
most `2 / epsilon` updates, positive output score yields a genuine
certificate, and positive initialization recovers the paper's advertised
positive-certificate conclusion. -/
def theorem23_coordinate_ascentSpec : Prop :=
  (∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (epsilon : ℝ), 0 < epsilon →
      ∀ {G : Set (Group X)} {H : Set (Model X Bool)}
      (oracle : CoordinateBestResponses law current G H)
      (fuel : ℕ), 2 ≤ ((fuel : ℝ) + 1) * epsilon →
      ∀ initial : CertificatePair X,
      PairAdmissible G H initial →
      ∃ output,
        coordinateAscentLoop law current epsilon oracle fuel initial = some output ∧
          EpsilonCoordinatewiseLocal law current G H epsilon output) ∧
  (∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (epsilon : ℝ), 0 < epsilon →
      ∀ (initial : CertificatePair X) (updates : List (CertificatePair X)),
      ImprovingCoordinateSequence law current epsilon initial updates →
      (updates.length : ℝ) ≤ 2 / epsilon) ∧
  (∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (pair : CertificatePair X),
      0 < binaryCertificateObjective law current pair.group pair.replacement →
      CertificateOfSuboptimality law binaryZeroOneLoss current pair.group
        pair.replacement (groupMass law pair.group)
        (groupLoss law binaryZeroOneLoss current pair.group -
          groupLoss law binaryZeroOneLoss pair.replacement pair.group)) ∧
  (∀ {X : Type*} [Fintype X] [DecidableEq X]
      (law : Distribution X Bool) (current : Model X Bool)
      (epsilon : ℝ), 0 < epsilon →
      ∀ {G : Set (Group X)} {H : Set (Model X Bool)}
      (oracle : CoordinateBestResponses law current G H)
      (fuel : ℕ), 2 ≤ ((fuel : ℝ) + 1) * epsilon →
      ∀ initial : CertificatePair X,
      PairAdmissible G H initial →
      0 < binaryCertificateObjective law current initial.group
        initial.replacement →
      ∃ output,
        coordinateAscentLoop law current epsilon oracle fuel initial = some output ∧
          EpsilonCoordinatewiseLocal law current G H epsilon output ∧
          CertificateOfSuboptimality law binaryZeroOneLoss current output.group
            output.replacement (groupMass law output.group)
            (groupLoss law binaryZeroOneLoss current output.group -
              groupLoss law binaryZeroOneLoss output.replacement output.group))

/-- Checked witness that the positive-certificate conclusion printed in
Theorem 23 does not follow from local optimality alone. -/
def theorem23_source_claim_counterexampleSpec : Prop :=
  EpsilonCoordinatewiseLocal theorem23CounterexampleLaw
      theorem23CounterexampleModel
      ({theorem23CounterexampleGroup} : Set (Group Unit))
      ({theorem23CounterexampleModel} : Set (Model Unit Bool))
      (1 / 2 : ℝ) theorem23CounterexamplePair ∧
    ¬ ∃ mu Delta,
      CertificateOfSuboptimality theorem23CounterexampleLaw binaryZeroOneLoss
        theorem23CounterexampleModel theorem23CounterexampleGroup
        theorem23CounterexampleModel mu Delta

/-! ## Canonical source-result surface

The declarations above retain executable finite-population statements and the
separate arbitrary-population development retains reusable measure-theoretic
statements.  The propositions below are the one-per-presentation review
surface for the paper's asserted results.  They select the arbitrary-law
endpoint whenever the source quantifies over an arbitrary population law.
Algorithms and numbered definitions are reviewed through their defining Lean
declarations rather than as theorem propositions.
-/

/-- Theorem 8 on arbitrary measurable population distributions. -/
def source_theorem8Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ (certificates : Set (Group X × Model X Y)),
      (∀ pair ∈ certificates,
        MeasurableGroup pair.1 ∧ MeasurableModel pair.2) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ current : Model X Y,
      MeasurableModel current →
    ((∃ group replacement mu Delta,
        (group, replacement) ∈ certificates ∧
        MeasureCertificateOfSuboptimality law loss current group replacement
          mu Delta ∧
        epsilon < mu * Delta) ↔
      ¬ MeasureApproxBayesOptimal law loss certificates epsilon current)

/-- Theorem 9 on arbitrary measurable population distributions. -/
def source_theorem9Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      {law : Measure (X × Y)} [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ {current replacement : Model X Y}, MeasurableModel current →
      MeasurableModel replacement →
      ∀ {group : Group X}, MeasurableGroup group →
      ∀ {mu Delta : ℝ},
      MeasureCertificateOfSuboptimality law loss current group replacement
        mu Delta →
    measureGroupLoss law loss (listUpdate current group replacement) group =
        measureGroupLoss law loss replacement group ∧
      measureModelLoss law loss (listUpdate current group replacement) ≤
        measureModelLoss law loss current - mu * Delta

/-- Theorem 10 on arbitrary measurable population distributions. -/
def source_theorem10Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (initial : Model X Y) (updates : List (Update X Y)),
      MeasureValidUpdateSequence law loss epsilon initial updates →
    (updates.length : ℝ) ≤ measureModelLoss law loss initial / epsilon ∧
      measureModelLoss law loss initial / epsilon ≤ 1 / epsilon

/-- Theorem 11 with the exact sparse-transcript family and explicit failure
tail replacing the source's undefined confidence symbol. -/
def source_theorem11Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ strategy : AdaptiveSubmissionStrategy X Y,
      (∀ transcript, MeasureSubmissionMeasurable (strategy transcript)) →
    measureCertificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Theorem 12 for the complete arbitrary-population adaptive runner. -/
def source_theorem12Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ initial : Model X Y, MeasurableModel initial →
      ∀ strategy : AdaptiveProposalStrategy X Y,
      (∀ transcript, MeasureProposalMeasurable (strategy transcript)) →
    measureAdaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Remark 13's theorem-like finite-family conclusion for arbitrary
measurable submissions. -/
def source_remark13Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ (U K : ℕ) (family : AdaptiveQueryIndex U K → Submission X Y),
      (∀ query, MeasureSubmissionMeasurable (family query)) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ n : ℕ, 0 < n →
    measureAdaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (U * (U + 1) ^ K : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Theorem 14 for the corrected single-transcript monotone process. -/
def source_theorem14Spec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (n U : ℕ), 0 < n →
      ∀ initial : Model X Y, MeasurableModel initial →
      ∀ strategy : AdaptiveMonotoneProposalStrategy X Y,
      (∀ transcript, MeasureProposalMeasurable (strategy transcript)) →
    let Q := monotoneBountyQueryBudget epsilon U
    measureMonotoneBountyFailure law loss epsilon n U initial strategy ≤
      (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Lemma 15's explicit arbitrary-population VC-uniform-convergence form. -/
def source_lemma15Spec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ (G : Set (Group X)) (H : Set (Model X Bool)),
      (∀ g ∈ G, MeasurableGroup g) →
      (∀ h ∈ H, MeasurableModel h) →
      ∀ (dG dH : ℕ), VCDimensionAtMost G dG → VCDimensionAtMost H dH →
      ∀ n : ℕ, 0 < n →
      listUpdateVCDimensionBound dG dH ≤ n + n →
      ∀ delta : ℝ, 0 < delta →
      VCSourceEventsMeasurable law (ListUpdateClass current G H)
          (listUpdateVCDimensionBound dG dH) n (delta / 2) →
      VCSourceEventsMeasurable law
          ({current} : Set (BinaryClassifier X)) 1 n (delta / 2) →
    MeasureCertificateVCDeviationFailure law current G H
        (certificateVCConfidenceRadius dG dH n delta) n ≤ delta

/-- Theorem 16's arbitrary-population high-probability training guarantee. -/
def source_theorem16Spec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      (G : Set (Group X)) (H : Set (Model X Bool)),
      (∀ g ∈ G, MeasurableGroup g) →
      (∀ h ∈ H, MeasurableModel h) →
      ∀ (C : Set (CandidatePair X Bool)),
      CandidateClassContainedIn C G H → MeasureCandidateClassMeasurable C →
      ∀ (dG dH : ℕ), VCDimensionAtMost G dG → VCDimensionAtMost H dH →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ {blockSize : ℕ}, 0 < blockSize →
      listUpdateVCDimensionBound dG dH ≤ blockSize + blockSize →
      ∀ oracle : TrainingOracle X Bool blockSize,
      ExactTrainingOracle binaryZeroOneLoss C oracle →
      ∀ {initial : Model X Bool}, MeasurableModel initial →
      ∀ delta : ℝ, 0 < delta →
      certificateVCConfidenceRadius dG dH blockSize
          (delta / (trainByOptRoundBudget epsilon : ℝ)) ≤ epsilon / 4 →
      (∀ current, MeasurableModel current →
        VCSourceEventsMeasurable law (ListUpdateClass current G H)
          (listUpdateVCDimensionBound dG dH) blockSize
          ((delta / (trainByOptRoundBudget epsilon : ℝ)) / 2)) →
      (∀ current, MeasurableModel current →
        VCSourceEventsMeasurable law
          ({current} : Set (BinaryClassifier X)) 1 blockSize
          ((delta / (trainByOptRoundBudget epsilon : ℝ)) / 2)) →
      MeasureTrainByOptVCBadEventPairMeasurable law G H epsilon
          (certificateVCConfidenceRadius dG dH blockSize
            (delta / (trainByOptRoundBudget epsilon : ℝ))) oracle initial →
    MeasureTrainByOptOutputFailureProbability law C epsilon oracle initial
        (trainByOptRoundBudget epsilon) ≤ delta ∧
      (∀ trace : Fin (trainByOptRoundBudget epsilon) →
          Fin blockSize → X × Bool,
        (trainByOptRun binaryZeroOneLoss epsilon oracle initial
          (trainByOptRoundBudget epsilon) trace).calls ≤
            trainByOptRoundBudget epsilon) ∧
      Fintype.card
          (Fin (trainByOptRoundBudget epsilon) × Fin blockSize) =
        trainByOptRoundBudget epsilon * blockSize

/-- Theorem 20's arbitrary-population cost-sensitive reduction. -/
def source_theorem20Spec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X),
      (∀ p ∈ K, Measurable p) →
      MeasureCostSensitiveMinimizer law current K pStar →
    MeasureDerivedCertificateMaximizer law current K pStar

/-- Lemma 21's arbitrary-population fixed-group ERM reduction. -/
def source_lemma21Spec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ {group : Group X}, MeasurableGroup group →
      ∀ (H : Set (Model X Bool)),
      (∀ h ∈ H, MeasurableModel h) →
      ∀ hStar : Model X Bool,
      MeasureGroupRestrictedERM law group H hStar →
    hStar ∈ H ∧ ∀ h ∈ H,
      MeasureBinaryCertificateObjective law current group h ≤
        MeasureBinaryCertificateObjective law current group hStar

/-- Lemma 22's arbitrary-population disagreement-ERM reduction, using the
corrected constant-minus-objective identity. -/
def source_lemma22Spec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current replacement : Model X Bool},
      MeasurableModel current → MeasurableModel replacement →
      ∀ (G : Set (Group X)),
      (∀ g ∈ G, MeasurableGroup g) →
      ∀ gStar : Group X,
      MeasureDisagreementERM law current replacement G gStar →
    gStar ∈ G ∧ ∀ g ∈ G,
      MeasureBinaryCertificateObjective law current g replacement ≤
        MeasureBinaryCertificateObjective law current gStar replacement

/-- Algorithm 6's repaired two-gap coordinate transition on an arbitrary
population. -/
def source_algorithm6_twoGapCoordinateAscentSpec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) (current : Model X Bool)
      (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
      (oracle : MeasureCoordinateBestResponses law current G H)
      (pair : CertificatePair X), PairAdmissible G H pair →
    (measureCoordinateAscentStep law current epsilon oracle pair = none →
      MeasureEpsilonCoordinatewiseLocal law current G H epsilon pair) ∧
    (∀ next,
      measureCoordinateAscentStep law current epsilon oracle pair = some next →
        PairAdmissible G H next ∧
          MeasureBinaryCertificateObjective law current pair.group
              pair.replacement + epsilon <
            MeasureBinaryCertificateObjective law current next.group
              next.replacement)

/-- Theorem 23 for repaired two-gap coordinate ascent.  Positive
initialization is explicit because the source's arbitrary-start positive-
certificate conclusion is false. -/
def source_theorem23Spec : Prop :=
  (∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ (G : Set (Group X)) (H : Set (Model X Bool)),
      (∀ g ∈ G, MeasurableGroup g) →
      (∀ h ∈ H, MeasurableModel h) →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ oracle : MeasureCoordinateBestResponses law current G H,
      ∀ initial : CertificatePair X, PairAdmissible G H initial →
      0 < MeasureBinaryCertificateObjective law current initial.group
        initial.replacement →
    ∃ output,
      measureCoordinateAscentLoop law current epsilon oracle
          (measureCoordinateAscentFuel epsilon) initial = some output ∧
        MeasureEpsilonCoordinatewiseLocal law current G H epsilon output ∧
        MeasureCertificateOfSuboptimality law binaryZeroOneLoss current
          output.group output.replacement (measureGroupMass law output.group)
          (measureGroupLoss law binaryZeroOneLoss current output.group -
            measureGroupLoss law binaryZeroOneLoss output.replacement
              output.group)) ∧
  (∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (initial : CertificatePair X) (updates : List (CertificatePair X)),
      MeasureImprovingCoordinateSequence law current epsilon initial updates →
      MeasurableGroup initial.group → MeasurableModel initial.replacement →
      MeasurableGroup (updates.getLastD initial).group →
      MeasurableModel (updates.getLastD initial).replacement →
    (updates.length : ℝ) ≤ 2 / epsilon) ∧
  (∀ epsilon : ℝ, 0 < epsilon →
    measureCoordinateAscentFuel epsilon + 1 = Nat.ceil (2 / epsilon))

end

end GHKR22BiasBounties
