import GJ19OptimalBinaryRatingSystems.PaperInterface

import GJ19OptimalBinaryRatingSystems.ProofBridge



namespace GJ19OptimalBinaryRatingSystems

namespace PaperInterface

open AppliedModelingLib.Probability
open Filter
open Topology
open MeasureTheory
open GJ19OptimalBinaryRatingSystems.ProofBridge
open scoped BigOperators
open scoped Function
open scoped ProbabilityTheory
noncomputable section

theorem definition_bernoulli_kl_formula (a b : ℝ) : definition_bernoulli_kl_formulaSpec (a := a) (b := b) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.definition_bernoulli_kl_formula (a := a) (b := b)

theorem lemma31_closed_adjacent_rate_formula
    (gLo gHi tLo tHi : ℝ) : lemma31_closed_adjacent_rate_formulaSpec (gLo := gLo) (gHi := gHi) (tLo := tLo) (tHi := tHi) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.lemma31_closed_adjacent_rate_formula (gLo := gLo) (gHi := gHi) (tLo := tLo) (tHi := tHi)

theorem paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) : paper_corollaryC2_uniform_equalized_last_rate_tendsto_zeroSpec (levels := levels) (hlevels := hlevels) (heq := heq) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero (levels := levels) (hlevels := hlevels) (heq := heq)

theorem paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) : paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zeroSpec (levels := levels) (hlevels := hlevels) (heq := heq) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero (levels := levels) (hlevels := hlevels) (heq := heq)

theorem lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) : lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objectiveSpec (m := m) (hm := hm) (oldLevels := oldLevels) (holdLevels := holdLevels) (holdEq := holdEq) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective (m := m) (hm := hm) (oldLevels := oldLevels) (holdLevels := holdLevels) (holdEq := holdEq)

theorem paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ (m : ℕ) (θ : ℝ), betaSeq (m + 2) θ = levels m (levelIndex m θ))
    (hoptimal :
      ∀ m : ℕ,
        AppliedModelingLib.Optimization.IsMaximizerOn BinaryEndpointLevelVector
          (fun xs => binaryEndpointAwareAdjacentRateObjective xs (fun _ => (1 : ℝ)))
          (levels m))
    (hlevelIndex_val :
      ∀ m : ℕ, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        (levelIndex m θ).val =
          min ⌊((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ⌋₊ (m + 1))
    (hquantile_range :
      ∀ m : ℕ, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit Filter.atTop
        (Set.Icc (0 : ℝ) 1)) : paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_meshSpec (betaSeq := betaSeq) (quantileSeq := quantileSeq) (quantileLimit := quantileLimit) (levels := levels) (levelIndex := levelIndex) (hrepr := hrepr) (hoptimal := hoptimal) (hlevelIndex_val := hlevelIndex_val) (hquantile_range := hquantile_range) (hquantile := hquantile) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh (betaSeq := betaSeq) (quantileSeq := quantileSeq) (quantileLimit := quantileLimit) (levels := levels) (levelIndex := levelIndex) (hrepr := hrepr) (hoptimal := hoptimal) (hlevelIndex_val := hlevelIndex_val) (hquantile_range := hquantile_range) (hquantile := hquantile)

theorem definitionC1_kendall_spearman_population_objectives
    (M : ℕ) (s : ℕ → ℝ) : definitionC1_kendall_spearman_population_objectivesSpec (M := M) (s := s) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.definitionC1_kendall_spearman_population_objectives (M := M) (s := s)

theorem paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    (M : ℕ) (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) : paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objectiveSpec (M := M) (s := s) (h0 := h0) (hM := hM) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective (M := M) (s := s) (h0 := h0) (hM := hM)

theorem paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) : paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispacedSpec (M := M) (s := s) (h0 := h0) (hM := hM) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced (M := M) (s := s) (h0 := h0) (hM := hM)

theorem paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) : paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispacedSpec (M := M) (s := s) (hmono := hmono) (h0 := h0) (hM := hM) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced (M := M) (s := s) (hmono := hmono) (h0 := h0) (hM := hM)

theorem source_quality_domain_realizes_spec : source_quality_domainSpec := by
  unfold source_quality_domainSpec
  exact by intros; rfl

theorem source_matching_function_realizes_spec : source_matching_functionSpec := by
  unfold source_matching_functionSpec
  exact by intros; rfl

theorem source_matching_count_realizes_spec : source_matching_countSpec := by
  unfold source_matching_countSpec
  exact by intros; rfl

theorem source_empirical_reputation_score_realizes_spec : source_empirical_reputation_scoreSpec := by
  unfold source_empirical_reputation_scoreSpec
  exact by intros; rfl

theorem source_system_state_realizes_spec : source_system_stateSpec := by
  unfold source_system_stateSpec
  exact by intros; rfl

theorem appendixB1_active_set_realizes_spec : appendixB1_active_setSpec := by
  unfold appendixB1_active_setSpec
  exact by intros; rfl

theorem appendixB1_transition_kernel_realizes_spec : appendixB1_transition_kernelSpec := by
  unfold appendixB1_transition_kernelSpec
  exact by intros; rfl

theorem appendixB1_state_update_realizes_spec : appendixB1_state_updateSpec := by
  unfold appendixB1_state_updateSpec
  exact by intros; rfl

theorem section4_question_distribution_realizes_spec {Y : Type*} [Fintype Y] (H : Y → ℝ) : section4_question_distributionSpec (Y := Y) (H := H) := by
  rfl

theorem section4_induced_binary_response_realizes_spec {Y : Type*} [Fintype Y]
    (ψ : ℝ → Y → ℝ) (H : Y → ℝ) (θ : ℝ) : section4_induced_binary_responseSpec (Y := Y) (ψ := ψ) (H := H) (θ := θ) := by
  rfl

theorem section4_l1_design_objective_realizes_spec
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : section4_l1_design_objectiveSpec (Representative := Representative) (Y := Y) (quality := quality) (β := β) (ψHat := ψHat) (H := H) := by
  rfl

theorem section4_question_design_solution_realizes_spec
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : section4_question_design_solutionSpec (Representative := Representative) (Y := Y) (quality := quality) (β := β) (ψHat := ψHat) (H := H) := by
  rfl

theorem appendixB5_random_question_experiment_realizes_spec
    (Ω Item Y : Type*) : appendixB5_random_question_experimentSpec (Ω := Ω) (Item := Item) (Y := Y) := by
  intro value
  exact ⟨value.question, value.positiveResponse, rfl, rfl⟩

theorem appendixB5_known_type_experiment_realizes_spec
    (Representative Y : Type*) [Fintype Representative] [Fintype Y] : appendixB5_known_type_experimentSpec (Representative := Representative) (Y := Y) := by
  intro value
  exact ⟨value.quality, value.empiricalResponse, rfl, rfl⟩

theorem appendixB5_unknown_type_experiment_realizes_spec
    (Item Y : Type*) [Fintype Item] [Fintype Y] : appendixB5_unknown_type_experimentSpec (Item := Item) (Y := Y) := by
  intro value
  exact ⟨value.trueQuality, value.empiricalResponse, value.empiricalAverageScore, value.rankedItem, rfl, rfl, rfl, rfl⟩

theorem appendixB5_empirical_question_response_realizes_spec
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) : appendixB5_empirical_question_responseSpec (Ω := Ω) (Item := Item) (Y := Y) (E := E) (i := i) (y := y) (N := N) (ω := ω) := by
  rfl

theorem theorem31_source_cell_matching_rate_eq_lower_cutpoint
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2))
    (hcut : cut i.val ≤ cut (i.val + 1))
    (hg : MonotoneOn g (Set.Icc (cut i.val) (cut (i.val + 1)))) : theorem31_source_cell_matching_rate_eq_lower_cutpointSpec (m := m) (cut := cut) (g := g) (i := i) (hcut := hcut) (hg := hg) := by
  exact GJ19OptimalBinaryRatingSystems.sourceCellMatchingRate_eq_lower_cutpoint (m := m) (cut := cut) (g := g) (i := i) (hcut := hcut) (hg := hg)

theorem theorem31_source_matching_function_lexicographic_formula {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight_pos : ∀ q ∈ sourceOrderedQualityPairs, 0 < weight q)
    (hweight_norm : ∫ q in sourceOrderedQualityPairs, weight q ∂(volume.prod volume) = 1)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) : theorem31_source_matching_function_lexicographic_formulaSpec hm weight hweight_pos hweight_norm g hg := by
  exact GJ19OptimalBinaryRatingSystems.theorem31_source_matching_function_lexicographic_formula hm weight hweight_pos hweight_norm g hg

theorem lemmaB1_matching_rate_shift
    {m k : ℕ} (hk0 : 0 < k) (hkm : k < m + 1)
    (sampleRate shiftedRate : Fin (m + 2) → ℝ)
    (levels shiftedLevels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (hshiftedLevels : BinaryEndpointLevelVector shiftedLevels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hshiftedEq :
      BinaryEndpointAwareAdjacentRatesEqualize shiftedLevels shiftedRate)
    (hsample_pos : ∀ i : Fin (m + 2), 0 < sampleRate i)
    (hshifted_pos : ∀ i : Fin (m + 2), 0 < shiftedRate i)
    (habove :
      ∀ i : Fin (m + 2), k < i.val → shiftedRate i ≤ sampleRate i)
    (hbelow :
      ∀ i : Fin (m + 2), i.val < k → sampleRate i ≤ shiftedRate i)
    (hpivot :
      sampleRate ⟨k, by omega⟩ = shiftedRate ⟨k, by omega⟩) : lemmaB1_matching_rate_shiftSpec (m := m) (k := k) (hk0 := hk0) (hkm := hkm) (sampleRate := sampleRate) (shiftedRate := shiftedRate) (levels := levels) (shiftedLevels := shiftedLevels) (hlevels := hlevels) (hshiftedLevels := hshiftedLevels) (heq := heq) (hshiftedEq := hshiftedEq) (hsample_pos := hsample_pos) (hshifted_pos := hshifted_pos) (habove := habove) (hbelow := hbelow) (hpivot := hpivot) := by
  exact GJ19OptimalBinaryRatingSystems.lemmaB1_matching_rate_shift (m := m) (k := k) (hk0 := hk0) (hkm := hkm) (sampleRate := sampleRate) (shiftedRate := shiftedRate) (levels := levels) (shiftedLevels := shiftedLevels) (hlevels := hlevels) (hshiftedLevels := hshiftedLevels) (heq := heq) (hshiftedEq := hshiftedEq) (hsample_pos := hsample_pos) (hshifted_pos := hshifted_pos) (habove := habove) (hbelow := hbelow) (hpivot := hpivot)

theorem lemmaB2_knownTypeExperiment_random_question_slln
    {Ω Representative Y : Type*} [MeasurableSpace Ω]
    [Fintype Representative] [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : SourceRandomQuestionExperiment Ω Representative Y)
    (quality : Representative → ℝ) (ψ : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (sourceQuestionAskedIndicator E i y 0) P)
    (hasked_indep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator E i y))
    (hasked_ident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator E i y n)
          (sourceQuestionAskedIndicator E i y 0) P P)
    (hasked_mean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, sourceQuestionAskedIndicator E i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (sourceQuestionPositiveIndicator E i y 0) P)
    (hpositive_indep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator E i y))
    (hpositive_ident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator E i y n)
          (sourceQuestionPositiveIndicator E i y 0) P P)
    (hpositive_mean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, sourceQuestionPositiveIndicator E i y 0 ω ∂P =
          H y * ψ (quality i) y) : lemmaB2_knownTypeExperiment_random_question_sllnSpec (Ω := Ω) (Representative := Representative) (Y := Y) (P := P) (E := E) (quality := quality) (ψ := ψ) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) := by
  exact GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_ae_question_response_of_iid (Ω := Ω) (Representative := Representative) (Y := Y) (P := P) (E := E) (quality := quality) (ψ := ψ) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean)

theorem lemmaB3_unknownTypeExperiment_random_question_response_and_rank
    {Ω Y : Type*} {L : ℕ} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : SourceRandomQuestionExperiment Ω (Fin L) Y)
    (quality : Fin L → ℝ) (ψ : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ i : Fin L, ∀ y : Y,
        Integrable (sourceQuestionAskedIndicator E i y 0) P)
    (hasked_indep :
      ∀ i : Fin L, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator E i y))
    (hasked_ident :
      ∀ i : Fin L, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator E i y n)
          (sourceQuestionAskedIndicator E i y 0) P P)
    (hasked_mean :
      ∀ i : Fin L, ∀ y : Y,
        ∫ ω, sourceQuestionAskedIndicator E i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ i : Fin L, ∀ y : Y,
        Integrable (sourceQuestionPositiveIndicator E i y 0) P)
    (hpositive_indep :
      ∀ i : Fin L, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator E i y))
    (hpositive_ident :
      ∀ i : Fin L, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator E i y n)
          (sourceQuestionPositiveIndicator E i y 0) P P)
    (hpositive_mean :
      ∀ i : Fin L, ∀ y : Y,
        ∫ ω, sourceQuestionPositiveIndicator E i y 0 ω ∂P =
          H y * ψ (quality i) y)
    (hscore_integrable :
      ∀ i : Fin L, Integrable (sourceAggregatePositiveIndicator E i 0) P)
    (hscore_indep :
      ∀ i : Fin L,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceAggregatePositiveIndicator E i))
    (hscore_ident :
      ∀ i : Fin L, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceAggregatePositiveIndicator E i n)
          (sourceAggregatePositiveIndicator E i 0) P P)
    (hscore_mean :
      ∀ i : Fin L,
        ∫ ω, sourceAggregatePositiveIndicator E i 0 ω ∂P =
          sourceExpectedAggregateScore ψ H (quality i))
    (hscore_strict :
      StrictMono (fun i : Fin L =>
        sourceExpectedAggregateScore ψ H (quality i))) : lemmaB3_unknownTypeExperiment_random_question_response_and_rankSpec (Ω := Ω) (Y := Y) (L := L) (P := P) (E := E) (quality := quality) (ψ := ψ) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hscore_integrable := hscore_integrable) (hscore_indep := hscore_indep) (hscore_ident := hscore_ident) (hscore_mean := hscore_mean) (hscore_strict := hscore_strict) := by
  exact GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid (Ω := Ω) (Y := Y) (L := L) (P := P) (E := E) (quality := quality) (ψ := ψ) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hscore_integrable := hscore_integrable) (hscore_indep := hscore_indep) (hscore_ident := hscore_ident) (hscore_mean := hscore_mean) (hscore_strict := hscore_strict)

theorem lemmaC6_monotone_matching_penultimate_level_bound
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) : lemmaC6_monotone_matching_penultimate_level_boundSpec (m := m) (hm := hm) (levels := levels) (sampleRate := sampleRate) (hlevels := hlevels) (heq := heq) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono) := by
  exact GJ19OptimalBinaryRatingSystems.BinaryEndpointLevelVector_monotone_equalized_last_low_ge_one_sub_inv (m := m) (hm := hm) (levels := levels) (sampleRate := sampleRate) (hlevels := hlevels) (heq := heq) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono)

theorem theorem32_weighted_nested_bisection_output_realizes_spec
    (m outerSteps innerSteps : ℕ)
    (sampleRate : Fin (m + 2) → ℝ) (grid : ℝ) : theorem32_weighted_nested_bisection_outputSpec (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps) (sampleRate := sampleRate) (grid := grid) := by
  rfl

theorem theorem32_weighted_nested_bisection_loss_and_runtime
    {m : ℕ} (hm : 1 < m)
    (optimal sampleRate : Fin (m + 2) → ℝ)
    (eps : ℝ)
    (hoptimalLevels : BinaryEndpointLevelVector optimal)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (heps : 0 < eps) : theorem32_weighted_nested_bisection_loss_and_runtimeSpec (m := m) (hm := hm) (optimal := optimal) (sampleRate := sampleRate) (eps := eps) (hoptimalLevels := hoptimalLevels) (heq := heq) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono) (hfirst_sample := hfirst_sample) (heps := heps) := by
  exact GJ19OptimalBinaryRatingSystems.theorem32WeightedNestedBisectionOutput_exists_source_depth_of_eps_pos (m := m) (hm := hm) (optimal := optimal) (sampleRate := sampleRate) (eps := eps) (hoptimalLevels := hoptimalLevels) (heq := heq) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono) (hfirst_sample := hfirst_sample) (heps := heps)

theorem source_definition_pairwise_accuracy_eq1_realizes_spec : source_definition_pairwise_accuracy_eq1Spec := by
  unfold source_definition_pairwise_accuracy_eq1Spec
  exact by intros; rfl

theorem source_definition_weighted_objective_eq2_realizes_spec : source_definition_weighted_objective_eq2Spec := by
  unfold source_definition_weighted_objective_eq2Spec
  exact by intros; rfl

theorem source_definition_large_deviation_rate_realizes_spec : source_definition_large_deviation_rateSpec := by
  unfold source_definition_large_deviation_rateSpec
  exact by intros; rfl

/--
The project-approved cross-bin Equation-(2) clarification identifies its
large-deviation gap with the error already analyzed in Appendix C.  Same-bin
pairs are outside this objective and require no cancellation condition.
-/
theorem source_clarified_crossBin_objective_rate_from_appendixC
    {μ : Measure ℝ} {sameLevel : ℝ × ℝ → Prop} [DecidablePred sameLevel]
    (model : SourceStrictUpperPairCrossBinObjectiveRealization μ sameLevel)
    {rate : ℝ}
    (haux : HasExponentialRate
      (sourceStrictUpperPairWeightedSeparatedRawError μ model.weight sameLevel
        model.pairwiseAccuracy) rate) :
    source_clarified_crossBin_objective_rate_from_appendixCSpec model haux := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.SourceStrictUpperPairCrossBinObjectiveRealization_large_deviation_rate
      model haux

/--
Source-facing form of the corrected cross-bin objective transfer when the
input rate is the tie-erased `Wbar_k` sequence of Appendix C.  This is a
project-approved correction to the rate objective, not a claim that the
archival all-pairs Equation (2) already had this domain restriction.
-/
theorem source_clarified_crossBin_objective_rate_from_tieErasedSourceWbar
    {μ : Measure ℝ} {sameLevel : ℝ × ℝ → Prop} [DecidablePred sameLevel]
    (model : SourceStrictUpperPairCrossBinObjectiveRealization μ sameLevel)
    {rate : ℝ}
    (haux : HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ model.weight
        (fun k q => if sameLevel q then 0 else 1 - model.pairwiseAccuracy k q))
      rate) :
    source_clarified_crossBin_objective_rate_from_tieErasedSourceWbarSpec
      model haux := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.SourceStrictUpperPairCrossBinObjectiveRealization_large_deviation_rate_of_lemmaC4TieErasedSourceWbar
      model haux

/-! Minimal source-to-auxiliary transfer contract for the still-open Lemma C.4
identification.  This is intentionally a proof-facing helper rather than a
source claim: the eventual equality premise must still be established from a
chosen population/ranking model. -/
theorem source_definition_large_deviation_rate_of_eventually_eq_auxiliary
    {W : ℝ} {Wk auxiliary : ℕ → ℝ} {rate : ℝ}
    (haux : HasExponentialRate auxiliary rate)
    (heq : ∀ᶠ k : ℕ in Filter.atTop, W - Wk k = auxiliary k) :
    source_definition_large_deviation_rate W Wk rate := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_large_deviation_rate_of_eventually_eq_auxiliary haux heq

/-! Exact objective algebra for the explicit strict-upper-pair source
convention. The remaining source review is only the instantiation of these
objects with the paper's printed `W` and `W_k`. -/
theorem source_strictUpperPair_weighted_limit_sub_finiteObjective_eq_rawError
    (μ : Measure ℝ) (weight : ℝ × ℝ → ℝ)
    (pairwiseAccuracy : ℕ → ℝ × ℝ → ℝ) (k : ℕ)
    (hweight_int : Integrable weight
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hfinite_int : Integrable
      (fun q : ℝ × ℝ => weight q * pairwiseAccuracy k q)
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) :
    GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLimit μ weight -
        GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedFiniteObjective μ weight pairwiseAccuracy k =
      GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedRawError μ weight pairwiseAccuracy k := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLimit_sub_finiteObjective_eq_rawError
    μ weight pairwiseAccuracy k hweight_int hfinite_int

theorem source_strictUpperPair_objectiveRealization_error_eq_rawError
    {μ : Measure ℝ}
    (model : GJ19OptimalBinaryRatingSystems.ProofBridge.SourceStrictUpperPairObjectiveRealization μ) :
    ∀ k : ℕ, model.W - model.Wk k =
      GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedRawError
        μ model.weight model.pairwiseAccuracy k := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairObjectiveRealization_error_eq_rawError model

/-! Minimal finite repair for the paper's same-level cancellation sentence:
equal seller laws plus equal sample counts force the strict-order objective to
cancel by exchange symmetry. -/
theorem source_same_level_equal_law_equal_counts_objective_eq_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) (n : ℕ)
    (hlaw : M.typeLaw hi = M.typeLaw lo) :
    twoSamplePkObjectiveProb M hi lo n n (n : ℝ)⁻¹ (n : ℝ)⁻¹ = 0 := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.twoSamplePkObjectiveProb_eq_zero_of_equal_law_equal_counts
      M hi lo n hlaw

/-! Source-level same-cell repair: equality of rating laws and matching rates
forces exact floor-count cancellation at every horizon. -/
theorem source_same_level_equal_law_equal_sampleRate_objective_eq_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ)
    (hlaw : M.typeLaw hi = M.typeLaw lo)
    (hsample : sampleRate hi = sampleRate lo) :
    twoSampleFloorPkObjectiveProb M sampleRate hi lo k = 0 := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.twoSampleFloorPkObjectiveProb_eq_zero_of_equal_law_equal_sampleRate
      M sampleRate hi lo k hlaw hsample

/-! For the source Bernoulli model, constant rating and matching probabilities
within a level cell give the exact signed-order cancellation needed by the
literal `W-W_k` bridge. -/
theorem source_same_level_equal_successProb_equal_sampleRate_objective_eq_zero
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller) (k : ℕ)
    (hsuccess : successProb hi = successProb lo)
    (hsample : sampleRate hi = sampleRate lo) :
    twoSampleFloorPkObjectiveProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo k = 0 := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.binaryRatingModel_twoSampleFloorPkObjectiveProb_eq_zero_of_equal_successProb_equal_sampleRate
      successProb hprob0 hprob1 sampleRate hi lo k hsuccess hsample

/-! General source-gap algebra retaining the limiting same-level accuracy
instead of silently replacing it by one. -/
theorem source_strictUpperPair_limitingAccuracy_sub_finiteObjective_eq_gap
    (μ : Measure ℝ) (weight limitingAccuracy : ℝ × ℝ → ℝ)
    (pairwiseAccuracy : ℕ → ℝ × ℝ → ℝ) (k : ℕ)
    (hlimit_int : Integrable
      (fun q : ℝ × ℝ => weight q * limitingAccuracy q)
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hfinite_int : Integrable
      (fun q : ℝ × ℝ => weight q * pairwiseAccuracy k q)
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) :
    GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLimitingAccuracyObjective
          μ weight limitingAccuracy -
        GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedFiniteObjective
          μ weight pairwiseAccuracy k =
      ∫ q in AppliedModelingLib.strictUpperPairSet,
        weight q * (limitingAccuracy q - pairwiseAccuracy k q) ∂(μ.prod μ) := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLimitingAccuracyObjective_sub_finiteObjective_eq_gap
      μ weight limitingAccuracy pairwiseAccuracy k hlimit_int hfinite_int

/-! Literal signed-objective repair for Lemma C.4.  The level-aware gap is the
printed `W - W_k`; the tie-erased cross-level error is equal to it only after
same-level signed-order cancellation has been established. -/
theorem source_strictUpperPair_levelGap_eq_limitingAccuracy_sub_finiteObjective
    (μ : Measure ℝ) (weight : ℝ × ℝ → ℝ)
    (sameLevel : ℝ × ℝ → Prop) [DecidablePred sameLevel]
    (pairwiseAccuracy : ℕ → ℝ × ℝ → ℝ) (k : ℕ)
    (hlimit_int : Integrable
      (fun q : ℝ × ℝ => weight q *
        sourceStrictUpperPairLevelLimitingAccuracy sameLevel q)
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hfinite_int : Integrable
      (fun q : ℝ × ℝ => weight q * pairwiseAccuracy k q)
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) :
    sourceStrictUpperPairWeightedLimitingAccuracyObjective μ weight
          (sourceStrictUpperPairLevelLimitingAccuracy sameLevel) -
        sourceStrictUpperPairWeightedFiniteObjective μ weight pairwiseAccuracy k =
      sourceStrictUpperPairWeightedLevelGap μ weight sameLevel pairwiseAccuracy k := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLevelGap_eq_limitingAccuracy_sub_finiteObjective
      μ weight sameLevel pairwiseAccuracy k hlimit_int hfinite_int

theorem source_strictUpperPair_levelGap_eq_separatedRawError_of_sameLevel_cancellation
    (μ : Measure ℝ) (weight : ℝ × ℝ → ℝ)
    (sameLevel : ℝ × ℝ → Prop) [DecidablePred sameLevel]
    (pairwiseAccuracy : ℕ → ℝ × ℝ → ℝ) (k : ℕ)
    (hsame :
      ∀ᵐ q ∂((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet),
        sameLevel q → pairwiseAccuracy k q = 0) :
    sourceStrictUpperPairWeightedLevelGap μ weight sameLevel pairwiseAccuracy k =
      sourceStrictUpperPairWeightedSeparatedRawError μ weight sameLevel pairwiseAccuracy k := by
  exact
    GJ19OptimalBinaryRatingSystems.ProofBridge.sourceStrictUpperPairWeightedLevelGap_eq_separatedRawError_of_sameLevel_cancellation
      μ weight sameLevel pairwiseAccuracy k hsame

/-! Finite uniform-pair specialization: once pairwise error-rate certificates
are available, the actual finite ranking-objective error inherits the minimum
certificate rate. This is a proved finite bridge, not the unresolved continuum
identification in Lemma C.4. -/
theorem finite_binary_uniform_ranking_objective_exact_rate_from_error_rate_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (E : FiniteErrorRateCertificate Pair)
    (herror :
      ∀ p : Pair,
        E.errorProb p =
          twoSampleFloorPkComplementErrorProb M sampleRate (pairHi p) (pairLo p))
    (pMin : Pair)
    (hrate_ge : ∀ p : Pair, E.rate pMin ≤ E.rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (E.rate pMin) := by
  exact GJ19OptimalBinaryRatingSystems.finite_binary_uniform_ranking_objective_exact_rate_from_error_rate_certificates
    M sampleRate pairHi pairLo E herror pMin hrate_ge

/-! The source's ordered adjacent-level specialization is also exported at
the paper-facing interface.  This closes only the finite adjacent aggregation
step; the continuum Lemma C.4 identification remains open. -/
theorem finite_binary_adjacent_uniform_ranking_objective_exact_rate_from_error_rate_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (E : FiniteErrorRateCertificate (Fin (m + 1)))
    (herror :
      ∀ i : Fin (m + 1),
        E.errorProb i =
          twoSampleFloorPkComplementErrorProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), E.rate iMin ≤ E.rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (E.rate iMin) := by
  exact
    GJ19OptimalBinaryRatingSystems.finite_binary_adjacent_uniform_objective_exact_rate_from_error_rate_certificates
      M sampleRate E herror iMin hrate_ge

/-! Conditional source-facing composition for the remaining continuum seam.
The eventual-equality premise is intentionally explicit: it is the exact
source-model obligation still missing from Lemma C.4. -/
theorem source_definition_large_deviation_rate_of_eventually_eq_finite_adjacent_uniform_objective
    {W : ℝ} {Wk : ℕ → ℝ}
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (E : FiniteErrorRateCertificate (Fin (m + 1)))
    (herror :
      ∀ i : Fin (m + 1),
        E.errorProb i =
          twoSampleFloorPkComplementErrorProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), E.rate iMin ≤ E.rate i)
    (heq : ∀ᶠ k : ℕ in Filter.atTop,
      W - Wk k =
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k) :
    source_definition_large_deviation_rate W Wk (E.rate iMin) := by
  apply source_definition_large_deviation_rate_of_eventually_eq_auxiliary
      (W := W) (Wk := Wk)
      (auxiliary := fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
  · exact
      GJ19OptimalBinaryRatingSystems.finite_binary_adjacent_uniform_objective_exact_rate_from_error_rate_certificates
        M sampleRate E herror iMin hrate_ge
  · exact heq

/-! Source-facing export of the already proved canonical selected-pullback C.4
forward branch.  This is conditional on the named pullback convention and is
not the unresolved raw continuum objective identification. -/
theorem lemmaC4_appropriate_finite_levels_weighted_pullback_source_rate_certificate
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (theorem31SelectedPullbackSourceWeight S.weight)
              (theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut
                S.hmono S.sampleRate levels hlevels))
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  exact
    GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_pullback_source_rate_certificate
      μ S

theorem lemmaC4_appropriate_finite_levels_const_weight_pullback_source_rate_certificate
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsConstWeightModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (theorem31SelectedPullbackSourceWeight
                (fun _ : ℝ × ℝ => (1 : ℝ)))
              (theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut
                S.hmono S.sampleRate levels hlevels))
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  exact
    GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_const_weight_pullback_source_rate_certificate
      μ S

theorem source_definition_step_rule_partition_levels_realizes_spec : source_definition_step_rule_partition_levelsSpec := by
  unfold source_definition_step_rule_partition_levelsSpec
  exact by intros; rfl

theorem source_definition_lexicographic_optimality_realizes_spec {α : Type*} (feasible : α → Prop) (primary secondary : α → ℝ) (x : α) : source_definition_lexicographic_optimalitySpec feasible primary secondary x := by
  rfl

theorem source_theorem31_adjacent_rate_eq3
    {m : ℕ} (cutpoints : ℕ → ℝ) (g : ℝ → ℝ)
    (j : Fin (m + 1)) (hcut : Monotone cutpoints) (hg : Monotone g)
    (tHi tLo : ℝ) : source_theorem31_adjacent_rate_eq3Spec (m := m) (cutpoints := cutpoints) (g := g) (j := j) (hcut := hcut) (hg := hg) (tHi := tHi) (tLo := tLo) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_theorem31_adjacent_rate_eq3 (m := m) (cutpoints := cutpoints) (g := g) (j := j) (hcut := hcut) (hg := hg) (tHi := tHi) (tLo := tLo)

theorem source_lemma31_equalization_eq4
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) : source_lemma31_equalization_eq4Spec (m := m) (hm := hm) (sampleRate := sampleRate) (hsample_pos := hsample_pos) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_lemma31_equalization_eq4 (m := m) (hm := hm) (sampleRate := sampleRate) (hsample_pos := hsample_pos)

theorem source_theoremB1_quantile_representation_realizes_spec : source_theoremB1_quantile_representationSpec := by
  unfold source_theoremB1_quantile_representationSpec
  exact by intros; rfl

theorem paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking
    {Ω Y : Type*} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : (L : ℕ) → SourceRandomQuestionExperiment Ω (Fin (L + 1)) Y)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (representative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionAskedIndicator (E L) i y 0) P)
    (hasked_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator (E L) i y))
    (hasked_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator (E L) i y n)
          (sourceQuestionAskedIndicator (E L) i y 0) P P)
    (hasked_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionAskedIndicator (E L) i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionPositiveIndicator (E L) i y 0) P)
    (hpositive_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator (E L) i y))
    (hpositive_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator (E L) i y n)
          (sourceQuestionPositiveIndicator (E L) i y 0) P P)
    (hpositive_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionPositiveIndicator (E L) i y 0 ω ∂P =
          H y * psi (quality L i) y)
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (representative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') : paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_trackingSpec (Ω := Ω) (Y := Y) (P := P) (E := E) (quality := quality) (representative := representative) (psi := psi) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hmesh := hmesh) (K := K) (hK := hK) (hlipschitz := hlipschitz) := by
  exact GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_ae_iterated_uniform_of_random_question_iid (Ω := Ω) (Y := Y) (P := P) (E := E) (quality := quality) (representative := representative) (psi := psi) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hmesh := hmesh) (K := K) (hK := hK) (hlipschitz := hlipschitz)

theorem paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking
    {Ω Y : Type*} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : (L : ℕ) → SourceRandomQuestionExperiment Ω (Fin (L + 1)) Y)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (rankRepresentative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionAskedIndicator (E L) i y 0) P)
    (hasked_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator (E L) i y))
    (hasked_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator (E L) i y n)
          (sourceQuestionAskedIndicator (E L) i y 0) P P)
    (hasked_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionAskedIndicator (E L) i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionPositiveIndicator (E L) i y 0) P)
    (hpositive_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator (E L) i y))
    (hpositive_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator (E L) i y n)
          (sourceQuestionPositiveIndicator (E L) i y 0) P P)
    (hpositive_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionPositiveIndicator (E L) i y 0 ω ∂P =
          H y * psi (quality L i) y)
    (hscore_integrable :
      ∀ L (i : Fin (L + 1)),
        Integrable (sourceAggregatePositiveIndicator (E L) i 0) P)
    (hscore_indep :
      ∀ L (i : Fin (L + 1)),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceAggregatePositiveIndicator (E L) i))
    (hscore_ident :
      ∀ L (i : Fin (L + 1)) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceAggregatePositiveIndicator (E L) i n)
          (sourceAggregatePositiveIndicator (E L) i 0) P P)
    (hscore_mean :
      ∀ L (i : Fin (L + 1)),
        ∫ ω, sourceAggregatePositiveIndicator (E L) i 0 ω ∂P =
          sourceExpectedAggregateScore psi H (quality L i))
    (hscore_strict :
      ∀ L : ℕ,
        StrictMono (fun i : Fin (L + 1) =>
          sourceExpectedAggregateScore psi H (quality L i)))
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (rankRepresentative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') : paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_trackingSpec (Ω := Ω) (Y := Y) (P := P) (E := E) (quality := quality) (rankRepresentative := rankRepresentative) (psi := psi) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hscore_integrable := hscore_integrable) (hscore_indep := hscore_indep) (hscore_ident := hscore_ident) (hscore_mean := hscore_mean) (hscore_strict := hscore_strict) (hmesh := hmesh) (K := K) (hK := hK) (hlipschitz := hlipschitz) := by
  exact GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_ae_iterated_uniform_and_rank_of_random_question_iid (Ω := Ω) (Y := Y) (P := P) (E := E) (quality := quality) (rankRepresentative := rankRepresentative) (psi := psi) (H := H) (hHpos := hHpos) (hasked_integrable := hasked_integrable) (hasked_indep := hasked_indep) (hasked_ident := hasked_ident) (hasked_mean := hasked_mean) (hpositive_integrable := hpositive_integrable) (hpositive_indep := hpositive_indep) (hpositive_ident := hpositive_ident) (hpositive_mean := hpositive_mean) (hscore_integrable := hscore_integrable) (hscore_indep := hscore_indep) (hscore_ident := hscore_ident) (hscore_mean := hscore_mean) (hscore_strict := hscore_strict) (hmesh := hmesh) (K := K) (hK := hK) (hlipschitz := hlipschitz)

theorem source_lemmaC1_pairwise_error_rate_from_derivatives
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) : source_lemmaC1_pairwise_error_rate_from_derivativesSpec (Seller := Seller) (Pair := Pair) (successProb := successProb) (hprob0 := hprob0) (hprob1 := hprob1) (hprob_pos := hprob_pos) (hprob_lt_one := hprob_lt_one) (sampleRate := sampleRate) (pairHi := pairHi) (pairLo := pairLo) (hpositive_hi := hpositive_hi) (hpositive_lo := hpositive_lo) (a := a) (z := z) (hz := hz) (hderiv_hi := hderiv_hi) (hderiv_lo := hderiv_lo) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_lemmaC1_pairwise_error_rate_from_derivatives (Seller := Seller) (Pair := Pair) (successProb := successProb) (hprob0 := hprob0) (hprob1 := hprob1) (hprob_pos := hprob_pos) (hprob_lt_one := hprob_lt_one) (sampleRate := sampleRate) (pairHi := pairHi) (pairLo := pairLo) (hpositive_hi := hpositive_hi) (hpositive_lo := hpositive_lo) (a := a) (z := z) (hz := hz) (hderiv_hi := hderiv_hi) (hderiv_lo := hderiv_lo)

theorem source_lemmaC2_binary_complement_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) : source_lemmaC2_binary_complement_rateSpec (Seller := Seller) (successProb := successProb) (hprob0 := hprob0) (hprob1 := hprob1) (sampleRate := sampleRate) (hi := hi) (lo := lo) (hgHi := hgHi) (hgLo := hgLo) (hpHi0 := hpHi0) (hpHi1 := hpHi1) (hpLo0 := hpLo0) (hpLo1 := hpLo1) (hpLo_le_hi := hpLo_le_hi) := by
  exact GJ19OptimalBinaryRatingSystems.binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair (Seller := Seller) (successProb := successProb) (hprob0 := hprob0) (hprob1 := hprob1) (sampleRate := sampleRate) (hi := hi) (lo := lo) (hgHi := hgHi) (hgLo := hgLo) (hpHi0 := hpHi0) (hpHi1 := hpHi1) (hpLo0 := hpLo0) (hpLo1 := hpLo1) (hpLo_le_hi := hpLo_le_hi)

theorem source_theoremC1_laplace_principle
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) : source_theoremC1_laplace_principleSpec (Ω := Ω) (μ := μ) (phiSeq := phiSeq) (phi := phi) (rate := rate) (hintegrable := hintegrable) (hess := hess) (huniform := huniform) := by
  exact GJ19OptimalBinaryRatingSystems.theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf (Ω := Ω) (μ := μ) (phiSeq := phiSeq) (phi := phi) (rate := rate) (hintegrable := hintegrable) (hess := hess) (huniform := huniform)

theorem source_remarkC1_full_square_application_under_explicit_conditions
    (weight : (ℝ × ℝ) → ℝ)
    (phiSeq : ℕ → (ℝ × ℝ) → ℝ) (phi : (ℝ × ℝ) → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : ℝ × ℝ =>
          weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ x ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))), 0 ≤ weight x)
    (hweight_bound :
      ∀ᵐ x ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))), weight x ≤ W)
    (hess :
      HasAEEssentialInfimum
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))) phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))) weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : ℝ × ℝ, |phiSeq k x - phi x| ≤ ε) : source_remarkC1_full_square_application_under_explicit_conditionsSpec (weight := weight) (phiSeq := phiSeq) (phi := phi) (rate := rate) (W := W) (hintegrable := hintegrable) (hWpos := hWpos) (hweight_nonneg := hweight_nonneg) (hweight_bound := hweight_bound) (hess := hess) (hweighted_near := hweighted_near) (huniform := huniform) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_remarkC1_full_square_application_under_explicit_conditions (weight := weight) (phiSeq := phiSeq) (phi := phi) (rate := rate) (W := W) (hintegrable := hintegrable) (hWpos := hWpos) (hweight_nonneg := hweight_nonneg) (hweight_bound := hweight_bound) (hess := hess) (hweighted_near := hweighted_near) (huniform := huniform)

theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component] [Nonempty Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε) : paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRateSpec (Ω := Ω) (Component := Component) (μ := μ) (P := P) (weight := weight) (kernel := kernel) (phi := phi) (rate := rate) (W := W) (hkernel_int := hkernel_int) (hweight_int := hweight_int) (hWpos := hWpos) (hweight_nonneg := hweight_nonneg) (hweight_bound := hweight_bound) (hess := hess) (hweighted_near := hweighted_near) (hkernel_pos := hkernel_pos) (huniform_log := huniform_log) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate (Ω := Ω) (Component := Component) (μ := μ) (P := P) (weight := weight) (kernel := kernel) (phi := phi) (rate := rate) (W := W) (hkernel_int := hkernel_int) (hweight_int := hweight_int) (hWpos := hWpos) (hweight_nonneg := hweight_nonneg) (hweight_bound := hweight_bound) (hess := hess) (hweighted_near := hweighted_near) (hkernel_pos := hkernel_pos) (huniform_log := huniform_log)

theorem paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate
    (μ : Measure ℝ) [SFinite μ] [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [(μ.prod μ).IsOpenPosMeasure]
    {m : ℕ} (hm : 0 < m)
    (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (levels sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component))
    (lo hi : ℝ)
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finiteStep :
      ¬ lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi) : paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rateSpec (μ := μ) (m := m) (hm := hm) (cut := cut) (hmono := hmono) (hcut_strict := hcut_strict) (levels := levels) (sampleRate := sampleRate) (hlevels := hlevels) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono) (weight := weight) (hweight_int := hweight_int) (hweight_nonneg := hweight_nonneg) (hweight_cont := hweight_cont) (hweight_midpoint_pos := hweight_midpoint_pos) (lo := lo) (hi := hi) (R := R) (hnot_finiteStep := hnot_finiteStep) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate (μ := μ) (m := m) (hm := hm) (cut := cut) (hmono := hmono) (hcut_strict := hcut_strict) (levels := levels) (sampleRate := sampleRate) (hlevels := hlevels) (hsample_pos := hsample_pos) (hsample_mono := hsample_mono) (weight := weight) (hweight_int := hweight_int) (hweight_nonneg := hweight_nonneg) (hweight_cont := hweight_cont) (hweight_midpoint_pos := hweight_midpoint_pos) (lo := lo) (hi := hi) (R := R) (hnot_finiteStep := hnot_finiteStep)

theorem source_remarkC2_weighted_kl_separation_monotonicity
    {gHi gLo pLo pHi : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_hi : pLo < pHi) (hpHi1 : pHi < 1) : source_remarkC2_weighted_kl_separation_monotonicitySpec (gHi := gHi) (gLo := gLo) (pLo := pLo) (pHi := pHi) (hgHi := hgHi) (hgLo := hgLo) (hpLo0 := hpLo0) (hpLo_lt_hi := hpLo_lt_hi) (hpHi1 := hpHi1) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_remarkC2_weighted_kl_separation_monotonicity (gHi := gHi) (gLo := gLo) (pLo := pLo) (pHi := pHi) (hgHi := hgHi) (hgLo := hgLo) (hpLo0 := hpLo0) (hpLo_lt_hi := hpLo_lt_hi) (hpHi1 := hpHi1)

theorem source_appendixC5_rate_notation_eq23_realizes_spec {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : source_appendixC5_rate_notation_eq23Spec (m := m) (successProb := successProb) (sampleRate := sampleRate) (i := i) := by
  rfl

theorem source_lemmaC5_uniform_doubled_chain
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) : source_lemmaC5_uniform_doubled_chainSpec (m := m) (hm := hm) (oldLevels := oldLevels) (holdLevels := holdLevels) (holdEq := holdEq) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_lemmaC5_uniform_doubled_chain (m := m) (hm := hm) (oldLevels := oldLevels) (holdLevels := holdLevels) (holdEq := holdEq)

theorem source_lemmaC5_refinement_equations24_25_realizes_spec : source_lemmaC5_refinement_equations24_25Spec := by
  unfold source_lemmaC5_refinement_equations24_25Spec
  exact ⟨by
    intro m k hk0 hkm oldLevels
    exact GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointLevels_middle_odd hk0 hkm oldLevels, by
    intro pLo pHi hpLo0 hpHi1 hlt
    exact GJ19OptimalBinaryRatingSystems.lemmaC5_uniform_interiorEqualSplit_rate_eq hpLo0 hpHi1 hlt⟩

theorem source_lemmaC9_nested_bisection_runtime_log_squared
    {M : ℕ} (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) : source_lemmaC9_nested_bisection_runtime_log_squaredSpec (M := M) (hM := hM) (delta := delta) (hdelta := hdelta) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_lemmaC9_nested_bisection_runtime_log_squared (M := M) (hM := hM) (delta := delta) (hdelta := hdelta)

theorem source_theoremB1_proof_selector_nesting
    {M q : ℕ} (hM : 0 < M) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : source_theoremB1_proof_selector_nestingSpec (M := M) (q := q) (hM := hM) (θ := θ) (hθ0 := hθ0) (hθ1 := hθ1) := by
  exact GJ19OptimalBinaryRatingSystems.theoremB1SourceDoubledIndexIterate_floor_window (M := M) (q := q) (hM := hM) (θ := θ) (hθ0 := hθ0) (hθ1 := hθ1)

theorem source_corollaryC4_kendall_spearman_subsequence
    (C : ℕ) : source_corollaryC4_kendall_spearman_subsequenceSpec (C := C) := by
  exact GJ19OptimalBinaryRatingSystems.ProofBridge.source_corollaryC4_kendall_spearman_subsequence (C := C)

end

end PaperInterface
end GJ19OptimalBinaryRatingSystems
