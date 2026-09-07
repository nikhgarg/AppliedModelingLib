import DSWG24DiscretizationBias.MainTheorems
import DSWG24DiscretizationBias.Assumptions
import DSWG24DiscretizationBias.ProofBridge

namespace DSWG24DiscretizationBias

namespace PaperInterface

open scoped BigOperators ProbabilityTheory
open MeasureTheory
open DSWG24DiscretizationBias.ProofBridge
noncomputable section

/-- Source-facing semantic target for the definition `bayesOptimal`. -/
def bayes_optimal_definitionSpec {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype σ] [DecidableEq σ] {N K : ℕ}
    (μ : PMF Ω) (observedDataset : Ω → σ)
    (trueLabels : Ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.bayesOptimal (Ω := Ω) (σ := σ) (N := N) (K := K) (μ := μ) (observedDataset := observedDataset) (trueLabels := trueLabels) (posterior := posterior) ↔
    ∀ xs i y,
        AppliedModelingLib.pmfProb μ
            (fun w => observedDataset w = xs ∧ trueLabels w i = y) =
          posterior xs i y *
            AppliedModelingLib.pmfProb μ (fun w => observedDataset w = xs)

/-- Source-facing semantic target for the definition `posteriorSimplex`. -/
def posterior_simplex_definitionSpec {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.posteriorSimplex (X := X) (Y := Y) (q := q) ↔
    (∀ x, (∑ y : Y, q x y) = 1) ∧
        (∀ x y, 0 ≤ q x y) ∧
          (∀ x y, q x y ≤ 1)

/-- Source-facing semantic target for the definition `calibrated`. -/
def calibration_definitionSpec {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.calibrated (X := X) (Y := Y) (μ := μ) (q := q) ↔
    by
      classical
      exact
        ∀ (y : Y) (s : Set ℝ), MeasurableSet s →
          (∫ xy, (if q xy.1 y ∈ s then
              if xy.2 = y then (1 : ℝ) else 0
            else 0) ∂μ) =
            ∫ xy, (if q xy.1 y ∈ s then q xy.1 y else 0) ∂μ

/-- Source-facing semantic target for the weak argmax definition. -/
def argmax_rule_definitionSpec {X Y : Type*}
    (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.isArgmaxRule (X := X) (Y := Y) q rule ↔
    ∀ x y, q x y ≤ q x (rule x)

/-- Source-facing semantic target for the definition `isTieBrokenArgmaxRule`. -/
def tie_broken_argmax_definitionSpec {N K : ℕ}
    (q : Fin N → Fin K → ℝ) (rule : Fin N → Fin K) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.isTieBrokenArgmaxRule (N := N) (K := K) (q := q) (rule := rule) ↔
    ∀ i, isFirstArgmax (q i) (rule i)

/-- Source-facing semantic target for the definition `isThompsonSamplingRule`. -/
def thompson_sampling_definitionSpec {N K : ℕ} (q selectionProbability : Fin N → Fin K → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.isThompsonSamplingRule (N := N) (K := K) (q := q) (selectionProbability := selectionProbability) ↔
    ∀ i y, selectionProbability i y = q i y

/-- Source-facing semantic target for the definition `isIndependentRule`. -/
def independent_rule_definitionSpec {X : Type*} {N K : ℕ}
    (rule : (Fin N → X) → Fin N → Fin K) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.isIndependentRule (X := X) (N := N) (K := K) (rule := rule) ↔
    ∃ d : X → Fin K, ∀ xs i, rule xs i = d (xs i)

/-- Source-facing semantic target for the randomized independent-rule definition. -/
def independent_randomized_rule_definitionSpec {X : Type*} {N K : ℕ}
    (jointProbability : (Fin N → X) → (Fin N → Fin K) → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.isIndependentRandomizedRule
      (X := X) (N := N) (K := K) jointProbability ↔
    ∃ rowProbability : X → Fin K → ℝ,
      (∀ x y, 0 ≤ rowProbability x y) ∧
        (∀ x, (∑ y : Fin K, rowProbability x y) = 1) ∧
          ∀ xs decision,
            jointProbability xs decision = ∏ i : Fin N, rowProbability (xs i) (decision i)

/-- Source-facing semantic target for the definition `maximizesEquation1`. -/
def integer_optimization_rule_definitionSpec {N K : ℕ} (γ : ℝ)
    (q : Fin N → Fin K → ℝ) (pref : Fin K → ℝ)
    (decision : Fin N → Fin K) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.maximizesEquation1 (N := N) (K := K) (γ := γ) (q := q) (pref := pref) (decision := decision) ↔
    ∀ other : Fin N → Fin K,
        equation1Objective γ q pref other ≤ equation1Objective γ q pref decision

/-- Source-facing semantic target for the definition `paretoOptimal`. -/
def pareto_optimality_definitionSpec {Rule : Type*}
    (accuracyMetric fidelityMetric : Rule → ℝ) (rule : Rule) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.paretoOptimal (Rule := Rule) (accuracyMetric := accuracyMetric) (fidelityMetric := fidelityMetric) (rule := rule) ↔
    Pareto.ParetoOptimal accuracyMetric fidelityMetric rule

/-- Source-facing semantic target for the definition `sourcePNq`. -/
def nontrivial_reference_family_definitionSpec {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.sourcePNq (Sample := Sample) (N := N) (K := K) (posterior := posterior) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt) ↔
    referenceSimplexAt prefAt ∧
        (∀ sample, isAggregateFirstArgmax (posterior sample) (aggregateArgmax sample)) ∧
          (∀ sample, 1 / (N : ℝ) ≤ prefAt sample (aggregateArgmax sample))

/-- Source-facing semantic target for the dataset-indexed reference distribution. -/
def reference_distribution_definitionSpec {Sample : Type*} {K : ℕ}
    (prefAt : Sample → Fin K → ℝ) : Prop :=
  DSWG24DiscretizationBias.ProofBridge.referenceSimplexAt (Sample := Sample) (K := K) prefAt ↔
    ∀ sample,
      (∀ y, 0 ≤ prefAt sample y) ∧ (∑ y : Fin K, prefAt sample y) = 1

/-- Source-facing semantic target for the aggregate-most-likely class definition. -/
def dataset_most_likely_class_definitionSpec {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K) : Prop :=
  (∀ sample,
    DSWG24DiscretizationBias.ProofBridge.isAggregateFirstArgmax
      (posterior sample) (aggregateArgmax sample)) ↔
    ∀ sample,
      DSWG24DiscretizationBias.ProofBridge.isFirstArgmax
        (DSWG24DiscretizationBias.ProofBridge.aggregatePosterior (posterior sample))
        (aggregateArgmax sample)

/-- Source-facing semantic target migrated from `theorem1iNoInformationBiasSpec`. -/
def theorem1i_no_information_biasSpec
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) : Prop :=
  (Finite.paperBias μ (fun _ : X => z) (prior μ) y =
          if z = y then 1 - prior μ y else -prior μ y) ∧
        (Finite.paperBias μ (fun _ : X => z) (Finite.paperAggregatePosterior μ q) y =
          if z = y then 1 - prior μ y else -prior μ y)

def theorem1ii_perfect_classifier_zero_biasSpec
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  ∀ y : Y, ProofBridge.perfectClassifierOnSupport μ q rule →
    (Finite.paperBias μ rule (ProofBridge.prior μ) y = 0 ∧
      Finite.paperBias μ rule (Finite.paperAggregatePosterior μ q) y = 0)

/-- Source-facing semantic target migrated from `theorem1iiiArgmaxBiasLeMaeSpec`. -/
def theorem1iii_argmax_bias_le_maeSpec
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) : Prop :=
  continuousJointPriorBias μ argmaxRule y ≤ continuousJointClassifierMAE μ q ∧
    continuousJointAggregateBias μ q argmaxRule y ≤ continuousJointClassifierMAE μ q

/-- Source-facing semantic target migrated from `theorem1iiiTightBinaryExampleSpec`. -/
def theorem1iii_tight_binary_exampleSpec : Prop :=
  Finite.paperAggregateBias Finite.paperTheorem1TightMu
        Finite.paperTheorem1TightQ Finite.paperTheorem1TightArgmax 0 =
      classifierMAE Finite.paperTheorem1TightMu Finite.paperTheorem1TightQ

/-- Source-facing semantic target migrated from `theorem2iJointRuleExistsSpec`. -/
def theorem2i_joint_rule_existsSpec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : Prop :=
  ∃ optRule : σ → Fin N → Fin K,
        ∀ rule : σ → Fin N → Fin K,
          expectedObjective expect observedDataset trueLabels γ fidelityTerm rule ≤
            expectedObjective expect observedDataset trueLabels γ fidelityTerm optRule

/-- Source-facing semantic target migrated from `theorem2iiArgmaxAccuracyMaximizingSpec`. -/
def theorem2ii_argmax_accuracy_maximizingSpec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, AppliedModelingLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : Prop :=
  AppliedModelingLib.Decision.expectedDecisionAccuracy
          expect observedDataset trueLabels decisionRule ≤
        AppliedModelingLib.Decision.expectedDecisionAccuracy
          expect observedDataset trueLabels argmaxRule

/-- Source-facing semantic target migrated from `theorem2iiiParetoOptimalAgreesArgmaxSpec`. -/
def theorem2iii_non_argmax_not_paretoSpec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) : Prop :=
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
      sourcePNq
        (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
        aggregateArgmax prefAt →
      0 < N →
      Pareto.ParetoOptimal
        (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
          (fun sample => Theorem2iii.sampledPosterior posterior sample))
        (Theorem2iii.expectedDatasetFidelityAt
          (Theorem2iii.iidSamplePMF μ N) prefAt)
        (fun sample => Theorem2iii.sampledDecision rule sample) →
      AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0

/-- Source-facing semantic target migrated from `theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec`. -/
def theorem2iii_weighted_objective_maximizer_agrees_argmaxSpec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) : Prop :=
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
      sourcePNq
        (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
        aggregateArgmax prefAt →
      0 ≤ γ → γ < 1 → 0 < N →
      (∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt)
            (fun sample => Theorem2iii.sampledDecision rule sample)) →
      AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0

/-- Source-facing randomized Pareto endpoint for Theorem 2(iii). -/
def theorem2iii_randomized_non_argmax_not_paretoSpec
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) : Prop :=
  2 ≤ K → K < N →
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
    0 < AppliedModelingLib.pmfProb ν
      (fun z : Z => rule z ≠ argmaxRule (feature z)) →
    sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt →
    0 < N →
      ¬ Pareto.ParetoOptimal
        (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
          (fun sample => Theorem2iii.sampledPosterior
            (fun z y => posterior (feature z) y) sample))
        (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
          (fun sample => prefAt (fun i => feature (sample i))))
        (fun sample => Theorem2iii.sampledDecision rule sample)

/-- Source-facing randomized weighted-objective endpoint for Theorem 2(iii). -/
def theorem2iii_randomized_weighted_objective_maximizer_agrees_argmaxSpec
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) : Prop :=
  2 ≤ K → K < N →
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
    0 < AppliedModelingLib.pmfProb ν
      (fun z : Z => rule z ≠ argmaxRule (feature z)) →
    sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt →
    0 ≤ γ → γ < 1 → 0 < N →
      ¬ ∀ other : (Fin N → Z) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
              (fun sample => Theorem2iii.sampledPosterior
                (fun z y => posterior (feature z) y) sample))
            (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
              (fun sample => prefAt (fun i => feature (sample i)))) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
              (fun sample => Theorem2iii.sampledPosterior
                (fun z y => posterior (feature z) y) sample))
            (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
              (fun sample => prefAt (fun i => feature (sample i))))
            (fun sample => Theorem2iii.sampledDecision rule sample)

/-- Combined randomized independent-rule endpoints for Theorem 2(iii). -/
def theorem2iii_randomized_augmented_endpointsSpec
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) : Prop :=
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
    0 < AppliedModelingLib.pmfProb ν
      (fun z : Z => rule z ≠ argmaxRule (feature z)) →
    sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt →
    0 ≤ γ → γ < 1 → 0 < N →
      (¬ Pareto.ParetoOptimal
        (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
          (fun sample => Theorem2iii.sampledPosterior
            (fun z y => posterior (feature z) y) sample))
        (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
          (fun sample => prefAt (fun i => feature (sample i))))
        (fun sample => Theorem2iii.sampledDecision rule sample)) ∧
      (¬ ∀ other : (Fin N → Z) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
              (fun sample => Theorem2iii.sampledPosterior
                (fun z y => posterior (feature z) y) sample))
            (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
              (fun sample => prefAt (fun i => feature (sample i)))) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
              (fun sample => Theorem2iii.sampledPosterior
                (fun z y => posterior (feature z) y) sample))
            (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
              (fun sample => prefAt (fun i => feature (sample i))))
            (fun sample => Theorem2iii.sampledDecision rule sample))

end

end PaperInterface
end DSWG24DiscretizationBias
