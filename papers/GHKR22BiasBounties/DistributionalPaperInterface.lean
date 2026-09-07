import GHKR22BiasBounties.MainTheorems

/-!
# Arbitrary-distribution paper interface: An Algorithmic Framework for Bias Bounties

The paper quantifies over arbitrary population distributions.  The executable
finite-PMF interface is useful for empirical laws, but it is not the full
source domain.  This file exposes the corresponding measure-theoretic claims
for measurable losses, models, groups, and adaptive submissions.  Those are
well-definedness conditions for the expectations in the paper, not finite-
support or parametric restrictions.

Observation 4 is handled in `PaperInterface.lean`: its literal pointwise form
is false on atomless populations, while the almost-everywhere conditional-risk
form is proved there.  Algorithms 1--5 have distribution-independent
transition semantics and therefore are not duplicated here.  Their
distributional guarantees are exposed below.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Statistics

/-- The paper's finite ternary alphabet carries its discrete sigma algebra. -/
local instance distributionalInterfaceTernaryLabelMeasurableSpace :
    MeasurableSpace TernaryLabel := ⊤

/-! ## Population definitions and update calculus -/

/-- Definition 1 for an arbitrary population law. -/
def definition1_measure_subgroupsSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      (group : Group X), MeasurableGroup group →
    measureGroupMass law group =
      ∫ datum, groupIndicator group datum.1 ∂law

/-- Definition 2 for an arbitrary population law, including the source's
conditional group loss with its explicit mass-weighted numerator. -/
def definition2_measure_modelLossSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ (model : Model X Y), MeasurableModel model →
      ∀ (group : Group X), MeasurableGroup group →
    measureModelLoss law loss model = ∫ datum, datumLoss loss model datum ∂law ∧
      measureGroupLoss law loss model group =
        measureGroupLossNumerator law loss model group /
          measureGroupMass law group

/-- Definition 3 on an arbitrary population.  Pointwise conditional laws are
only determined almost everywhere, so this is the distribution-invariant
reading of the source definition. -/
def definition3_measure_aeBayesOptimalSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (featureLaw : Measure X) [IsProbabilityMeasure featureLaw]
      (labels : Kernel X Y) [IsMarkovKernel labels]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ (current : Model X Y), MeasurableModel current →
    (AEBayesOptimalForRisk featureLaw (kernelConditionalRisk labels loss)
        current ↔
      ∀ᵐ x ∂featureLaw, ∀ prediction : Y,
        kernelConditionalRisk labels loss x (current x) ≤
          kernelConditionalRisk labels loss x prediction)

/-- Definition 5 on arbitrary populations.  The mass-weighted formulation is
the total primitive; on every positive-mass certified group it is equivalent
to the paper's divided display. -/
def definition5_measure_approxBayesOptimalSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ (certificates : Set (Group X × Model X Y)),
      (∀ pair ∈ certificates,
        MeasurableGroup pair.1 ∧ MeasurableModel pair.2) →
      ∀ (epsilon : ℝ) (current : Model X Y), MeasurableModel current →
    (MeasureApproxBayesOptimal law loss certificates epsilon current ↔
      ∀ pair ∈ certificates,
        measureCertificateImprovementScore law loss current pair.1 pair.2 ≤
          epsilon) ∧
    ((∀ pair ∈ certificates, 0 < measureGroupMass law pair.1) →
      (MeasureApproxBayesOptimal law loss certificates epsilon current ↔
        ∀ pair ∈ certificates,
          measureGroupLoss law loss current pair.1 ≤
            measureGroupLoss law loss pair.2 pair.1 +
              epsilon / measureGroupMass law pair.1))

/-- Definition 7 on arbitrary populations. -/
def definition7_measure_certificateSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      (loss : BoundedLoss Y), MeasurableBoundedLoss loss →
      ∀ (current : Model X Y), MeasurableModel current →
      ∀ (group : Group X), MeasurableGroup group →
      ∀ (replacement : Model X Y), MeasurableModel replacement →
      ∀ (mu Delta : ℝ),
    MeasureCertificateOfSuboptimality law loss current group replacement
        mu Delta ↔
      0 < mu ∧ 0 < Delta ∧ mu ≤ measureGroupMass law group ∧
        measureGroupLoss law loss replacement group + Delta ≤
          measureGroupLoss law loss current group

/-- Theorem 8 on arbitrary measurable populations. -/
def theorem8_measure_certificate_characterizationSpec : Prop :=
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

/-- Theorem 9 on arbitrary measurable populations. -/
def theorem9_measure_listUpdate_progressSpec : Prop :=
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

/-- Theorem 10 on arbitrary measurable populations. -/
def theorem10_measure_update_countSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∀ (initial : Model X Y) (updates : List (Update X Y)),
      MeasureValidUpdateSequence law loss epsilon initial updates →
    (updates.length : ℝ) ≤ measureModelLoss law loss initial / epsilon ∧
      measureModelLoss law loss initial / epsilon ≤ 1 / epsilon

/-! ## Adaptive checking and monotone bounty -/

/-- Corrected Theorem 11 on arbitrary measurable populations. -/
def theorem11_measure_adaptive_certificate_checkerSpec : Prop :=
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

/-- Corrected Theorem 12 on arbitrary measurable populations. -/
def theorem12_measure_falsifyAndUpdateSpec : Prop :=
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

/-- Remark 13 on arbitrary measurable populations. -/
def remark13_measure_logarithmic_submission_dependenceSpec : Prop :=
  ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
      (law : Measure (X × Y)) [IsProbabilityMeasure law]
      {loss : BoundedLoss Y}, MeasurableBoundedLoss loss →
      ∀ (U K : ℕ) (family : AdaptiveQueryIndex U K → Submission X Y),
      (∀ query, MeasureSubmissionMeasurable (family query)) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → ∀ n : ℕ, 0 < n →
    measureAdaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (U * (U + 1) ^ K : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32)

/-- Corrected Theorem 14 on arbitrary measurable populations. -/
def theorem14_measure_monotoneBountySpec : Prop :=
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

/-! ## VC training and optimization reductions -/

/-- Lemma 15 on an arbitrary measurable population. -/
def lemma15_measure_vc_uniform_convergenceSpec : Prop :=
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

/-- Theorem 16 on an arbitrary measurable population, with the rounded fresh-
block horizon and exact sample count. -/
def theorem16_measure_trainByOptSpec : Prop :=
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

/-- Definition 18 on an arbitrary measurable population. -/
def definition18_measure_costSensitiveMinimizerSpec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      (current : Model X Bool), MeasurableModel current →
      ∀ (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X),
      (∀ p ∈ K, Measurable p) →
    (MeasureCostSensitiveMinimizer law current K pStar ↔
      pStar ∈ K ∧ ∀ p ∈ K,
        measureExpectedTernaryCost law current pStar ≤
          measureExpectedTernaryCost law current p)

/-- Theorem 20 on an arbitrary measurable population. -/
def theorem20_measure_ternary_cost_sensitive_reductionSpec : Prop :=
  ∀ {X : Type*} [MeasurableSpace X]
      (law : Measure (X × Bool)) [IsProbabilityMeasure law]
      {current : Model X Bool}, MeasurableModel current →
      ∀ (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X),
      (∀ p ∈ K, Measurable p) →
      MeasureCostSensitiveMinimizer law current K pStar →
    MeasureDerivedCertificateMaximizer law current K pStar

/-- Lemma 21 on an arbitrary measurable population. -/
def lemma21_measure_group_erm_reductionSpec : Prop :=
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

/-- Corrected Lemma 22 on an arbitrary measurable population. -/
def lemma22_measure_disagreement_erm_reductionSpec : Prop :=
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

/-- Corrected Algorithm 6 transition semantics on an arbitrary population. -/
def algorithm6_measure_twoGapCoordinateAscentSpec : Prop :=
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

/-- Corrected Theorem 23 on arbitrary measurable populations.  Positive
initial score is exactly the additional premise needed for the paper's
advertised positive-certificate conclusion.  The remaining clauses record
the strict-update bound and the exact rounded number of best-response rounds:
each loop round calls the model oracle once and the group oracle at most once. -/
def theorem23_measure_coordinate_ascentSpec : Prop :=
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
