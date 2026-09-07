import DSWG24DiscretizationBias.PaperInterface

import DSWG24DiscretizationBias.ProofBridge



namespace DSWG24DiscretizationBias

namespace PaperInterface

open scoped BigOperators ProbabilityTheory
open MeasureTheory
open DSWG24DiscretizationBias.ProofBridge
noncomputable section

theorem bayes_optimal_definition {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype σ] [DecidableEq σ] {N K : ℕ}
    (μ : PMF Ω) (observedDataset : Ω → σ)
    (trueLabels : Ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ) : bayes_optimal_definitionSpec (Ω := Ω) (σ := σ) (N := N) (K := K) (μ := μ) (observedDataset := observedDataset) (trueLabels := trueLabels) (posterior := posterior) := by
  rfl

theorem posterior_simplex_definition {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) : posterior_simplex_definitionSpec (X := X) (Y := Y) (q := q) := by
  rfl

theorem calibration_definition {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) : calibration_definitionSpec (X := X) (Y := Y) (μ := μ) (q := q) := by
  rfl

theorem argmax_rule_definition {X Y : Type*}
    (q : X → Y → ℝ) (rule : X → Y) :
    argmax_rule_definitionSpec (X := X) (Y := Y) q rule := by
  rfl

theorem tie_broken_argmax_definition {N K : ℕ}
    (q : Fin N → Fin K → ℝ) (rule : Fin N → Fin K) : tie_broken_argmax_definitionSpec (N := N) (K := K) (q := q) (rule := rule) := by
  rfl

theorem thompson_sampling_definition {N K : ℕ} (q selectionProbability : Fin N → Fin K → ℝ) : thompson_sampling_definitionSpec (N := N) (K := K) (q := q) (selectionProbability := selectionProbability) := by
  rfl

theorem independent_rule_definition {X : Type*} {N K : ℕ}
    (rule : (Fin N → X) → Fin N → Fin K) : independent_rule_definitionSpec (X := X) (N := N) (K := K) (rule := rule) := by
  rfl

theorem independent_randomized_rule_definition {X : Type*} {N K : ℕ}
    (jointProbability : (Fin N → X) → (Fin N → Fin K) → ℝ) :
    independent_randomized_rule_definitionSpec
      (X := X) (N := N) (K := K) jointProbability := by
  rfl

theorem integer_optimization_rule_definition {N K : ℕ} (γ : ℝ)
    (q : Fin N → Fin K → ℝ) (pref : Fin K → ℝ)
    (decision : Fin N → Fin K) : integer_optimization_rule_definitionSpec (N := N) (K := K) (γ := γ) (q := q) (pref := pref) (decision := decision) := by
  rfl

theorem pareto_optimality_definition {Rule : Type*}
    (accuracyMetric fidelityMetric : Rule → ℝ) (rule : Rule) : pareto_optimality_definitionSpec (Rule := Rule) (accuracyMetric := accuracyMetric) (fidelityMetric := fidelityMetric) (rule := rule) := by
  rfl

theorem nontrivial_reference_family_definition {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ) : nontrivial_reference_family_definitionSpec (Sample := Sample) (N := N) (K := K) (posterior := posterior) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt) := by
  rfl

theorem reference_distribution_definition {Sample : Type*} {K : ℕ}
    (prefAt : Sample → Fin K → ℝ) :
    reference_distribution_definitionSpec (Sample := Sample) (K := K) prefAt := by
  rfl

theorem dataset_most_likely_class_definition {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K) :
    dataset_most_likely_class_definitionSpec
      (Sample := Sample) (N := N) (K := K) posterior aggregateArgmax := by
  rfl

theorem theorem1i_no_information_bias
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) : theorem1i_no_information_biasSpec (μ := μ) (q := q) (z := z) (y := y) (hnoInformation := hnoInformation) (hplurality := hplurality) := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem1i_no_information_bias_spec (μ := μ) (q := q) (z := z) (y := y) (hnoInformation := hnoInformation) (hplurality := hplurality)

theorem theorem1ii_perfect_classifier_zero_bias
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) :
    theorem1ii_perfect_classifier_zero_biasSpec μ q rule := by
  intro y hperfect
  exact ⟨(ProofBridge.theorem1ii_prior_reference_zero_bias_on_support_spec μ q rule) y hperfect,
    (ProofBridge.theorem1ii_aggregate_reference_zero_bias_on_support_spec μ q rule) y hperfect⟩

theorem theorem1iii_argmax_bias_le_mae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) : theorem1iii_argmax_bias_le_maeSpec (X := X) (Y := Y) (μ := μ) (q := q) (argmaxRule := argmaxRule) (y := y) (hrule := hrule) (hargmax := hargmax) (hsimplex := hsimplex) (hscore := hscore) (hcal := hcal) := by
  change
    continuousJointPriorBias μ argmaxRule y ≤ continuousJointClassifierMAE μ q ∧
      continuousJointAggregateBias μ q argmaxRule y ≤ continuousJointClassifierMAE μ q
  constructor
  · exact DSWG24DiscretizationBias.ProofBridge.theorem1iii_argmax_bias_le_mae_spec (X := X) (Y := Y) (μ := μ) (q := q) (argmaxRule := argmaxRule) (y := y) (hrule := hrule) (hargmax := hargmax) (hsimplex := hsimplex) (hscore := hscore) (hcal := hcal)
  · have hpriorAggregate :
        (∫ xy, (if xy.2 = y then (1 : ℝ) else 0) ∂μ) =
          continuousJointAggregatePosterior μ q y :=
      DSWG24DiscretizationBias.ProofBridge.continuousJointPrior_eq_jointAggregatePosterior_of_calibrated
        μ q y hcal
    rw [continuousJointAggregateBias, ← hpriorAggregate]
    exact DSWG24DiscretizationBias.ProofBridge.theorem1iii_argmax_bias_le_mae_spec (X := X) (Y := Y) (μ := μ) (q := q) (argmaxRule := argmaxRule) (y := y) (hrule := hrule) (hargmax := hargmax) (hsimplex := hsimplex) (hscore := hscore) (hcal := hcal)

theorem theorem1iii_tight_binary_example : theorem1iii_tight_binary_exampleSpec := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem1iii_tight_binary_example_spec

theorem theorem2i_joint_rule_exists
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
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : theorem2i_joint_rule_existsSpec (ω := ω) (σ := σ) (N := N) (K := K) (hK := hK) (hNK := hNK) (expect := expect) (hlin := hlin) (observedDataset := observedDataset) (trueLabels := trueLabels) (γ := γ) (posterior := posterior) (fidelityTerm := fidelityTerm) (hbayesRow := hbayesRow) := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem2i_joint_rule_exists_spec (ω := ω) (σ := σ) (N := N) (K := K) (hK := hK) (hNK := hNK) (expect := expect) (hlin := hlin) (observedDataset := observedDataset) (trueLabels := trueLabels) (γ := γ) (posterior := posterior) (fidelityTerm := fidelityTerm) (hbayesRow := hbayesRow)

theorem theorem2ii_argmax_accuracy_maximizing
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
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : theorem2ii_argmax_accuracy_maximizingSpec (ω := ω) (σ := σ) (N := N) (K := K) (hK := hK) (hNK := hNK) (expect := expect) (hlin := hlin) (observedDataset := observedDataset) (trueLabels := trueLabels) (posterior := posterior) (decisionRule := decisionRule) (argmaxRule := argmaxRule) (hargmax := hargmax) (hbayesRow := hbayesRow) := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem2ii_argmax_accuracy_maximizing_spec (ω := ω) (σ := σ) (N := N) (K := K) (hK := hK) (hNK := hNK) (expect := expect) (hlin := hlin) (observedDataset := observedDataset) (trueLabels := trueLabels) (posterior := posterior) (decisionRule := decisionRule) (argmaxRule := argmaxRule) (hargmax := hargmax) (hbayesRow := hbayesRow)

theorem theorem2iii_non_argmax_not_pareto
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) : theorem2iii_non_argmax_not_paretoSpec (X := X) (N := N) (K := K) (μ := μ) (posterior := posterior) (rule := rule) (argmaxRule := argmaxRule) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt) := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem2iii_source_pareto_optimal_agrees_argmax_spec (X := X) (N := N) (K := K) (μ := μ) (posterior := posterior) (rule := rule) (argmaxRule := argmaxRule) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt)

theorem theorem2iii_weighted_objective_maximizer_agrees_argmax
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) : theorem2iii_weighted_objective_maximizer_agrees_argmaxSpec (X := X) (N := N) (K := K) (μ := μ) (posterior := posterior) (rule := rule) (argmaxRule := argmaxRule) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt) (γ := γ) := by
  exact DSWG24DiscretizationBias.ProofBridge.theorem2iii_source_weighted_objective_maximizer_agrees_argmax_spec (X := X) (N := N) (K := K) (μ := μ) (posterior := posterior) (rule := rule) (argmaxRule := argmaxRule) (aggregateArgmax := aggregateArgmax) (prefAt := prefAt) (γ := γ)

theorem theorem2iii_randomized_non_argmax_not_pareto
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) :
    theorem2iii_randomized_non_argmax_not_paretoSpec
      (Z := Z) (X := X) (N := N) (K := K) ν feature posterior rule argmaxRule
      aggregateArgmax prefAt := by
  intro hK hNK hargmax hdisagree hPNq hNpos
  exact
    (DSWG24DiscretizationBias.ProofBridge.theorem2iii_source_randomized_augmented_endpoints
      ν feature posterior rule argmaxRule hargmax hdisagree aggregateArgmax prefAt hPNq
      (γ := 0) (by norm_num) (by norm_num) hNpos).1

theorem theorem2iii_randomized_weighted_objective_maximizer_agrees_argmax
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) :
    theorem2iii_randomized_weighted_objective_maximizer_agrees_argmaxSpec
      (Z := Z) (X := X) (N := N) (K := K) ν feature posterior rule argmaxRule
      aggregateArgmax prefAt γ := by
  intro hK hNK hargmax hdisagree hPNq hγnonneg hγlt hNpos
  exact
    (DSWG24DiscretizationBias.ProofBridge.theorem2iii_source_randomized_augmented_endpoints
      ν feature posterior rule argmaxRule hargmax hdisagree aggregateArgmax prefAt hPNq
      hγnonneg hγlt hNpos).2

theorem theorem2iii_randomized_augmented_endpoints
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) :
    theorem2iii_randomized_augmented_endpointsSpec
      (Z := Z) (X := X) (N := N) (K := K) ν feature posterior rule argmaxRule
      aggregateArgmax prefAt γ := by
  intro hargmax hdisagree hPNq hγnonneg hγlt hNpos
  exact DSWG24DiscretizationBias.ProofBridge.theorem2iii_source_randomized_augmented_endpoints
    ν feature posterior rule argmaxRule hargmax hdisagree aggregateArgmax prefAt hPNq
    hγnonneg hγlt hNpos

end

end PaperInterface
end DSWG24DiscretizationBias
