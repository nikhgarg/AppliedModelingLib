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

/-- Source-facing semantic target for `definition_bernoulli_kl_formula`. -/
def definition_bernoulli_kl_formulaSpec (a b : ℝ) : Prop :=
  paperBernoulliKL a b =
    a * Real.log (a / b) +
      (1 - a) * Real.log ((1 - a) / (1 - b))

/-- Source-facing semantic target for `lemma31_closed_adjacent_rate_formula`. -/
def lemma31_closed_adjacent_rate_formulaSpec
    (gLo gHi tLo tHi : ℝ) : Prop :=
  paperAdjacentBinaryClosedRate gLo gHi tLo tHi =
    -(gLo + gHi) *
      Real.log
        (((1 - tLo) ^ (gLo / (gLo + gHi))) *
            ((1 - tHi) ^ (gHi / (gLo + gHi))) +
          (tLo ^ (gLo / (gLo + gHi))) *
            (tHi ^ (gHi / (gLo + gHi))))

/-- Source-facing semantic target for `paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero`. -/
def paper_corollaryC2_uniform_equalized_last_rate_tendsto_zeroSpec
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) : Prop :=
  Tendsto
    (fun N : ℕ =>
      binaryEndpointAwareAdjacentRate (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin ((N + 1) + 1)))
    atTop (nhds 0)

/-- Source-facing semantic target for `paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero`. -/
def paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zeroSpec
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) : Prop :=
  Tendsto
    (fun N : ℕ =>
      binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N))
    atTop (nhds 0)

/-- Source-facing semantic target for `lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective`. -/
def lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objectiveSpec
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) : Prop :=
  (1 / 5 : ℝ) *
      binaryEndpointAwareAdjacentRateObjective oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
    binaryEndpointAwareAdjacentRateObjective
      (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))

/-- Source-facing semantic target for `corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq`. -/
def corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sqSpec
    (levels sampleRate : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, 0 < m → BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ, 0 < m →
      BinaryEndpointAwareAdjacentRatesEqualize (levels m) (sampleRate m))
    (hsample_pos : ∀ m : ℕ, 0 < m →
      ∀ idx : Fin (m + 2), 0 < sampleRate m idx)
    (hsample_mono : ∀ m : ℕ, 0 < m →
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate m a ≤ sampleRate m b)
    (hfirst_sample : ∀ m : ℕ, 0 < m →
      sampleRate m (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
    C / (((m + 2 : ℕ) : ℝ) ^ 3) ≤
      levels m (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))

/-- Source-facing semantic target for `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`. -/
def paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_meshSpec
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
        (Set.Icc (0 : ℝ) 1)) : Prop :=
  theoremB1UniformOptimalSubsequencePrincipleTo betaSeq quantileSeq quantileLimit

/-- Source-facing semantic target for `definitionC1_kendall_spearman_population_objectives`. -/
def definitionC1_kendall_spearman_population_objectivesSpec
    (M : ℕ) (s : ℕ → ℝ) : Prop :=
  kendallConstantWeightIntervalObjective M s =
      (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 2) / 2 ∧
    spearmanLinearWeightIntervalObjective M s =
      (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 3) / 6

/-- Source-facing semantic target for `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective`. -/
def paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objectiveSpec
    (M : ℕ) (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) : Prop :=
  spearmanLinearWeightOrderedPairIntervalObjective M s =
    spearmanLinearWeightIntervalObjective M s

/-- Source-facing semantic target for `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced`. -/
def paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispacedSpec
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) : Prop :=
  (∑ i : Fin M, ∑ j : Fin M,
      if i < j then
        (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
      else 0) ≤
    (1 - (M : ℝ)⁻¹) / 2

/-- Source-facing semantic target for `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced`. -/
def paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispacedSpec
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) : Prop :=
  spearmanLinearWeightOrderedPairIntervalObjective M s ≤
    (1 - ((M : ℝ)⁻¹) ^ 2) / 6

/-- Source-facing semantic target for the bundled definition `source_quality_domain`. -/
def source_quality_domainSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.source_quality_domain = GJ19OptimalBinaryRatingSystems.sourceQualityDomain)

/-- Source-facing semantic target for the bundled definition `source_matching_function`. -/
def source_matching_functionSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.source_matching_function = GJ19OptimalBinaryRatingSystems.SourceMatchingFunction)

/-- Source-facing semantic target for the bundled definition `source_matching_count`. -/
def source_matching_countSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.source_matching_count = GJ19OptimalBinaryRatingSystems.sourceMatchingCount)

/-- Source-facing semantic target for the bundled definition `source_empirical_reputation_score`. -/
def source_empirical_reputation_scoreSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.source_empirical_reputation_score = GJ19OptimalBinaryRatingSystems.sourceEmpiricalReputationScore)

/-- Source-facing semantic target for the bundled definition `source_system_state`. -/
def source_system_stateSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.source_system_state = GJ19OptimalBinaryRatingSystems.SourceSystemState)

/-- Source-facing semantic target for the bundled definition `appendixB1_active_set`. -/
def appendixB1_active_setSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.appendixB1_active_set = GJ19OptimalBinaryRatingSystems.sourceAppendixBActiveSet)

/-- Source-facing semantic target for the bundled definition `appendixB1_transition_kernel`. -/
def appendixB1_transition_kernelSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.appendixB1_transition_kernel = GJ19OptimalBinaryRatingSystems.sourceAppendixBTransitionKernel)

/-- Source-facing semantic target for the bundled definition `appendixB1_state_update`. -/
def appendixB1_state_updateSpec : Prop :=
  (GJ19OptimalBinaryRatingSystems.ProofBridge.appendixB1_state_update = GJ19OptimalBinaryRatingSystems.sourceAppendixBStateUpdateMass)

/-- Source-facing semantic target for `SourceQuestionDistribution`. -/
def section4_question_distributionSpec {Y : Type*} [Fintype Y] (H : Y → ℝ) : Prop :=
  GJ19OptimalBinaryRatingSystems.ProofBridge.section4_question_distribution H =
    ((∀ y : Y, 0 ≤ H y) ∧ ∑ y : Y, H y = 1)

/-- Source-facing semantic target for `sourceInducedBinaryResponse`. -/
def section4_induced_binary_responseSpec {Y : Type*} [Fintype Y]
    (ψ : ℝ → Y → ℝ) (H : Y → ℝ) (θ : ℝ) : Prop :=
  GJ19OptimalBinaryRatingSystems.sourceInducedBinaryResponse (Y := Y) (ψ := ψ) (H := H) (θ := θ) =
    ∑ y : Y, ψ θ y * H y

/-- Source-facing semantic target for `sourceQuestionDesignL1Objective`. -/
def section4_l1_design_objectiveSpec
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : Prop :=
  GJ19OptimalBinaryRatingSystems.sourceQuestionDesignL1Objective (Representative := Representative) (Y := Y) (quality := quality) (β := β) (ψHat := ψHat) (H := H) =
    ∑ i : Representative,
        |β (quality i) - ∑ y : Y, ψHat i y * H y|

/-- Source-facing semantic target for `SourceQuestionDesignSolution`. -/
def section4_question_design_solutionSpec
    {Representative Y : Type*} [Fintype Representative] [Fintype Y]
    (quality : Representative → ℝ) (β : ℝ → ℝ)
    (ψHat : Representative → Y → ℝ) (H : Y → ℝ) : Prop :=
  GJ19OptimalBinaryRatingSystems.ProofBridge.section4_question_design_solution
      quality β ψHat H =
    AppliedModelingLib.Optimization.IsMinimizerOn
      (SourceQuestionDistribution : (Y → ℝ) → Prop)
      (sourceQuestionDesignL1Objective quality β ψHat) H

/-- Source-facing field-level semantic target for `SourceRandomQuestionExperiment`. -/
def appendixB5_random_question_experimentSpec
    (Ω Item Y : Type*) : Prop :=
  ∀ value : GJ19OptimalBinaryRatingSystems.SourceRandomQuestionExperiment Ω Item Y,
    ∃ question : Item → ℕ → Ω → Y,
    ∃ positiveResponse : Item → ℕ → Ω → Bool,
      value.question = question ∧
      value.positiveResponse = positiveResponse

/-- Source-facing field-level semantic target for `SourceKnownTypeExperiment`. -/
def appendixB5_known_type_experimentSpec
    (Representative Y : Type*) [Fintype Representative] [Fintype Y] : Prop :=
  ∀ value : GJ19OptimalBinaryRatingSystems.SourceKnownTypeExperiment Representative Y,
    ∃ quality : Representative → ℝ,
    ∃ empiricalResponse : ℕ → Representative → Y → ℝ,
      value.quality = quality ∧
      value.empiricalResponse = empiricalResponse

/-- Source-facing field-level semantic target for `SourceUnknownTypeExperiment`. -/
def appendixB5_unknown_type_experimentSpec
    (Item Y : Type*) [Fintype Item] [Fintype Y] : Prop :=
  ∀ value : GJ19OptimalBinaryRatingSystems.SourceUnknownTypeExperiment Item Y,
    ∃ trueQuality : Item → ℝ,
    ∃ empiricalResponse : ℕ → Item → Y → ℝ,
    ∃ empiricalAverageScore : ℕ → Item → ℝ,
    ∃ rankedItem : ℕ → Item → Item,
      value.trueQuality = trueQuality ∧
      value.empiricalResponse = empiricalResponse ∧
      value.empiricalAverageScore = empiricalAverageScore ∧
      value.rankedItem = rankedItem

/-- Source-facing semantic target for `sourceExperimentEmpiricalQuestionResponse`. -/
def appendixB5_empirical_question_responseSpec
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) : Prop :=
  GJ19OptimalBinaryRatingSystems.sourceExperimentEmpiricalQuestionResponse (Ω := Ω) (Item := Item) (Y := Y) (E := E) (i := i) (y := y) (N := N) (ω := ω) =
    sourceExperimentPositiveQuestionCount E i y N ω /
        sourceExperimentQuestionCount E i y N ω

/-- Source-facing semantic target for `theorem31_source_cell_matching_rate_eq_lower_cutpoint`. -/
def theorem31_source_cell_matching_rate_eq_lower_cutpointSpec
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2))
    (hcut : cut i.val ≤ cut (i.val + 1))
    (hg : MonotoneOn g (Set.Icc (cut i.val) (cut (i.val + 1)))) : Prop :=
  sourceCellMatchingRate cut g i = g (cut i.val)

/-- Theorem 3.1 formula optimization for strict source partitions with at least
three cells. Matching-rate infima and value integrals use the same disjoint cells;
the identification with the exponent of `W - W_k` remains separate. -/
def theorem31_source_matching_function_lexicographic_formulaSpec {m : ℕ} (hm : 0 < m)
    (weight : ℝ × ℝ → ℝ)
    (hweight_pos : ∀ q ∈ sourceOrderedQualityPairs, 0 < weight q)
    (hweight_norm : ∫ q in sourceOrderedQualityPairs, weight q ∂(volume.prod volume) = 1)
    (g : ℝ → ℝ) (hg : SourceMatchingFunction g) : Prop :=
  ∃ s : Fin ((m + 2) + 1) → ℝ, ∃ levels : Fin (m + 2) → ℝ,
      s ∈ sourceStrictCutpointSet (m + 2) ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels (sourceFiniteSampleRate g s) ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin ((m + 2) + 1) → ℝ) × (Fin (m + 2) → ℝ) =>
          design.1 ∈ sourceStrictCutpointSet (m + 2) ∧ BinaryEndpointLevelVector design.2)
        (fun design => sourceAllCrossCellValue weight design.1)
        (fun design => binaryEndpointAwareAdjacentRateObjective design.2
          (sourceFiniteSampleRate g design.1)) (s, levels)

/-- Source-facing semantic target for `lemmaB1_matching_rate_shift`. -/
def lemmaB1_matching_rate_shiftSpec
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
      sampleRate ⟨k, by omega⟩ = shiftedRate ⟨k, by omega⟩) : Prop :=
  shiftedLevels ⟨k, by omega⟩ ≤ levels ⟨k, by omega⟩

/-- Source-facing semantic target for `lemmaB2_knownTypeExperiment_random_question_slln`. -/
def lemmaB2_knownTypeExperiment_random_question_sllnSpec
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
          H y * ψ (quality i) y) : Prop :=
  ∀ᵐ ω ∂P, ∀ i : Representative, ∀ y : Y,
    Tendsto
      (fun N : ℕ =>
        sourceExperimentEmpiricalQuestionResponse E i y N ω)
      atTop (nhds (ψ (quality i) y))

/-- Source-facing semantic target for `lemmaB3_unknownTypeExperiment_random_question_response_and_rank`. -/
def lemmaB3_unknownTypeExperiment_random_question_response_and_rankSpec
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
        sourceExpectedAggregateScore ψ H (quality i))) : Prop :=
  ∀ᵐ ω ∂P,
    TendstoUniformlyOn
      (fun N : ℕ => fun p : Fin L × Y =>
        sourceExperimentEmpiricalQuestionResponse E p.1 p.2 N ω)
      (fun p : Fin L × Y => ψ (quality p.1) p.2)
      atTop Set.univ ∧
    (∀ᶠ N : ℕ in atTop,
      StrictMono (fun i : Fin L =>
        sourceExperimentEmpiricalMean
          (sourceAggregatePositiveIndicator E i) N ω))

/-- Source-facing semantic target for `lemmaC6_monotone_matching_penultimate_level_bound`. -/
def lemmaC6_monotone_matching_penultimate_level_boundSpec
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) : Prop :=
  1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
    levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))

/-- Source-facing semantic target for `theorem32WeightedNestedBisectionOutput`. -/
def theorem32_weighted_nested_bisection_outputSpec
    (m outerSteps innerSteps : ℕ)
    (sampleRate : Fin (m + 2) → ℝ) (grid : ℝ) : Prop :=
  GJ19OptimalBinaryRatingSystems.theorem32WeightedNestedBisectionOutput (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps) (sampleRate := sampleRate) (grid := grid) =
    let gLast : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun lastLow =>
        theorem32WeightedBackwardGridRateBisectionLevels
          m innerSteps sampleRate grid (gLast * (-Real.log lastLow)) lastLow
      let above : ℝ → Bool := fun lastLow =>
        theorem32OuterSourceWeightedRateAbove (candidate lastLow) sampleRate
      let lastLow : ℝ :=
        (AppliedModelingLib.Optimization.realBisectionRun above outerSteps
          (1 - 1 / ((m + 1 : ℕ) : ℝ)) (1 - grid)).2
      candidate lastLow

/-- Source-facing semantic target for `theorem32_weighted_nested_bisection_loss_and_runtime`. -/
def theorem32_weighted_nested_bisection_loss_and_runtimeSpec
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
    (heps : 0 < eps) : Prop :=
  let grid := theorem32WeightedSourceGrid sampleRate eps
  let lastLower : ℝ := 1 - 1 / ((m + 1 : ℕ) : ℝ)
  let sourceDepthBudget : ℝ :=
    max (((1 - grid) - lastLower) / 2) 1
  let runtimeLog : ℝ :=
    Real.logb 2 (max 1 (sourceDepthBudget / grid)) + 2
  0 < grid ∧
    ∃ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ runtimeLog ∧
        binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
            binaryEndpointAwareAdjacentRateObjective
              (theorem32WeightedNestedBisectionOutput
                m (L + 1) L sampleRate grid) sampleRate ≤ eps ∧
          nestedBisectionOperationCount (m + 2) (L + 1) L ≤
            AppliedModelingLib.Optimization.nestedBisectionStepBound (m + 2) L ∧
          ((nestedBisectionOperationCount
              (m + 2) (L + 1) L : ℕ) : ℝ) ≤
            ((m + 2 : ℕ) : ℝ) * runtimeLog ^ 2

/-- Source-facing semantic target for the bundled definition `source_definition_pairwise_accuracy_eq1`. -/
def source_definition_pairwise_accuracy_eq1Spec : Prop :=
  (∀ (probabilityCorrect probabilityIncorrect : ℝ), GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_pairwise_accuracy_eq1 (probabilityCorrect := probabilityCorrect) (probabilityIncorrect := probabilityIncorrect) = probabilityCorrect - probabilityIncorrect)

/-- Source-facing semantic target for the bundled definition `source_definition_weighted_objective_eq2`. -/
def source_definition_weighted_objective_eq2Spec : Prop :=
  (∀ (weight pairwiseAccuracy : ℝ → ℝ → ℝ) (Wk : ℝ),
    GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_weighted_objective_eq2
      (weight := weight) (pairwiseAccuracy := pairwiseAccuracy) (Wk := Wk) =
      ((∀ θ1 ∈ Set.Icc (0 : ℝ) 1, ∀ θ2 ∈ Set.Ico (0 : ℝ) θ1,
          0 < weight θ1 θ2) ∧
        (∫ θ1 in Set.Icc (0 : ℝ) 1,
          ∫ θ2 in Set.Ico (0 : ℝ) θ1, weight θ1 θ2) = 1 ∧
        Wk = ∫ θ1 in Set.Icc (0 : ℝ) 1,
          ∫ θ2 in Set.Ico (0 : ℝ) θ1,
            weight θ1 θ2 * pairwiseAccuracy θ1 θ2))

/-- Source-facing semantic target for the bundled definition `source_definition_large_deviation_rate`. -/
def source_definition_large_deviation_rateSpec : Prop :=
  (∀ (W : ℝ) (Wk : ℕ → ℝ) (rate : ℝ), GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_large_deviation_rate (W := W) (Wk := Wk) (rate := rate) = HasExponentialRate (fun k : ℕ => W - Wk k) rate)

/-- Source-facing semantic target for the bundled definition `source_definition_step_rule_partition_levels`. -/
def source_definition_step_rule_partition_levelsSpec : Prop :=
  (∀ (m : ℕ) (cutpoints : Fin ((m + 2) + 1) → ℝ) (levels : Fin (m + 2) → ℝ),
    GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_step_rule_partition_levels
      (m := m) (cutpoints := cutpoints) (levels := levels) =
        (cutpoints ∈ sourceStrictCutpointSet (m + 2) ∧
          BinaryEndpointLevelVector levels))

def source_definition_lexicographic_optimalitySpec {α : Type*} (feasible : α → Prop) (primary secondary : α → ℝ) (x : α) : Prop :=
  GJ19OptimalBinaryRatingSystems.ProofBridge.source_definition_lexicographic_optimality
      feasible primary secondary x =
    (feasible x ∧ ∀ y, feasible y →
      primary y < primary x ∨
        (primary y = primary x ∧ secondary y ≤ secondary x))

/-- Source-facing semantic target for `source_theorem31_adjacent_rate_eq3`. -/
def source_theorem31_adjacent_rate_eq3Spec
    {m : ℕ} (cutpoints : ℕ → ℝ) (g : ℝ → ℝ)
    (j : Fin (m + 1)) (hcut : Monotone cutpoints) (hg : Monotone g)
    (tHi tLo : ℝ) : Prop :=
  sourceCellMatchingRate cutpoints g (adjacentLowIndex j) =
      g (cutpoints (adjacentLowIndex j).val) ∧
    sourceCellMatchingRate cutpoints g (adjacentHighIndex j) =
      g (cutpoints (adjacentHighIndex j).val) ∧
    paperAdjacentBinaryRatingRate
        (sourceCellMatchingRate cutpoints g (adjacentHighIndex j))
        (sourceCellMatchingRate cutpoints g (adjacentLowIndex j))
        tHi tLo =
      sInf (Set.range fun a : ℝ =>
        sourceCellMatchingRate cutpoints g (adjacentHighIndex j) *
            paperBernoulliKL a tHi +
          sourceCellMatchingRate cutpoints g (adjacentLowIndex j) *
            paperBernoulliKL a tLo)

/-- Source-facing semantic target for `source_lemma31_equalization_eq4`. -/
def source_lemma31_equalization_eq4Spec
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) : Prop :=
  ∃! levels : Fin (m + 2) → ℝ,
    BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs sampleRate)
        levels

/-- Source-facing semantic target for the bundled definition `source_theoremB1_quantile_representation`. -/
def source_theoremB1_quantile_representationSpec : Prop :=
  (∀ (M : ℕ) (cellIndex : ℝ → Fin M) (levels : Fin M → ℝ)
    (quantile beta : ℝ → ℝ),
    GJ19OptimalBinaryRatingSystems.ProofBridge.source_theoremB1_quantile_representation
      (M := M) (cellIndex := cellIndex) (levels := levels)
      (quantile := quantile) (beta := beta) =
      ((∀ θ : ℝ, quantile θ = ((cellIndex θ).val : ℝ) / (M : ℝ)) ∧
        ∀ θ : ℝ, beta θ = levels (cellIndex θ)))

/-- Source-facing semantic target for `paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking`. -/
def paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_trackingSpec
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
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') : Prop :=
  ∀ᵐ ω ∂P,
    ∀ ε > 0,
      ∀ᶠ L : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
            dist
                (sourceExperimentEmpiricalQuestionResponse
                  (E L) (representative L θ) y N ω)
                (psi θ y) < ε

/-- Source-facing semantic target for `paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking`. -/
def paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_trackingSpec
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
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') : Prop :=
  ∀ᵐ ω ∂P,
    ∀ ε > 0,
      ∀ᶠ L : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop,
          StrictMono (fun i : Fin (L + 1) =>
            sourceExperimentEmpiricalMean
              (sourceAggregatePositiveIndicator (E L) i) N ω) ∧
            ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
              dist
                  (sourceExperimentEmpiricalQuestionResponse
                    (E L) (rankRepresentative L θ) y N ω)
                  (psi θ y) < ε

/-- Source-facing semantic target for `source_lemmaC1_pairwise_error_rate_from_derivatives`. -/
def source_lemmaC1_pairwise_error_rate_from_derivativesSpec
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
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) : Prop :=
  Nonempty
    (PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo)

/-- Source-facing semantic target for `source_lemmaC2_binary_complement_rate`. -/
def source_lemmaC2_binary_complement_rateSpec
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) : Prop :=
  ExponentialRateCertificate
    (twoSampleFloorPkComplementErrorProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
    (weightedBernoulliClosedThresholdRate
      (sampleRate hi) (sampleRate lo)
      (successProb hi) (successProb lo))

/-- Source-facing semantic target for `source_theoremC1_laplace_principle`. -/
def source_theoremC1_laplace_principleSpec
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) : Prop :=
  HasExponentialRate
    (fun k : ℕ => ∫ x, Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
    rate

/-- Source-facing semantic target for `source_remarkC1_full_square_application_under_explicit_conditions`. -/
def source_remarkC1_full_square_application_under_explicit_conditionsSpec
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
        ∀ x : ℝ × ℝ, |phiSeq k x - phi x| ≤ ε) : Prop :=
  HasExponentialRate
    (fun k : ℕ =>
      ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))))
    rate

/-- Source-facing semantic target for `paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate`. -/
def paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRateSpec
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
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε) : Prop :=
  ∃ minComponent : Component,
    (∀ component, rate minComponent ≤ rate component) ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in P.support, weight x * kernel k x ∂μ)
        (rate minComponent)

/-- Source-facing semantic target for `paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate`. -/
def paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rateSpec
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
      ¬ lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi) : Prop :=
  ((lemmaC4FiniteRangeOnIoo (cutpointStepSuccessProb cut levels) lo hi ∧
    (∃ rate : ℝ,
        0 < rate ∧
          AppliedModelingLib.Probability.ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (theorem31SelectedPullbackSourceWeight weight)
              (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
                sampleRate levels hlevels)) rate)) ∧
    (HasExponentialRate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (lemmaC4RawSourcePbarKernel R)) 0 ∧
      ∀ rate : ℝ, 0 < rate →
        ¬ AppliedModelingLib.Probability.ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (lemmaC4RawSourcePbarKernel R)) rate))

/-- Source-facing semantic target for `source_remarkC2_weighted_kl_separation_monotonicity`. -/
def source_remarkC2_weighted_kl_separation_monotonicitySpec
    {gHi gLo pLo pHi : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_hi : pLo < pHi) (hpHi1 : pHi < 1) : Prop :=
  ContinuousAt
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
      (pHi, pLo) ∧
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
      weightedBernoulliClosedThresholdRate gHi gLo p p = 0) ∧
    0 < weightedBernoulliClosedThresholdRate gHi gLo pHi pLo ∧
    StrictMonoOn
      (fun x : ℝ =>
        weightedBernoulliClosedThresholdRate gHi gLo x pLo)
      (Set.Icc pLo pHi) ∧
    StrictAntiOn
      (fun x : ℝ =>
        weightedBernoulliClosedThresholdRate gHi gLo pHi x)
      (Set.Icc pLo pHi)

/-- Source-facing semantic target for `binaryEndpointAwareAdjacentRate`. -/
def source_appendixC5_rate_notation_eq23Spec {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : Prop :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRate (m := m) (successProb := successProb) (sampleRate := sampleRate) (i := i) =
    if i.val = 0 then
        sampleRate (adjacentHighIndex i) *
          (-Real.log (1 - successProb (adjacentHighIndex i)))
      else if i.val = m then
        sampleRate (adjacentLowIndex i) *
          (-Real.log (successProb (adjacentLowIndex i)))
      else
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i))
          (successProb (adjacentLowIndex i))

/-- Source-facing semantic target for `source_lemmaC5_uniform_doubled_chain`. -/
def source_lemmaC5_uniform_doubled_chainSpec
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) : Prop :=
  BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) ∧
    BinaryEndpointAwareAdjacentRatesEqualize
      (uniformDoubledEndpointLevels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ∧
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector :
        (Fin ((2 * m + 1) + 2) → ℝ) → Prop)
      (fun xs : Fin ((2 * m + 1) + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective xs (fun _ => (1 : ℝ)))
      (uniformDoubledEndpointLevels oldLevels)

def source_lemmaC5_refinement_equations24_25Spec : Prop :=
  (∀ {m k : ℕ} (hk0 : 0 < k) (hkm : k < m) (oldLevels : Fin (m + 2) → ℝ),
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliInteriorEqualSplit
        (oldLevels ⟨k, by omega⟩)
        (oldLevels ⟨k + 1, by omega⟩)) ∧
  (∀ {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1) (hlt : pLo < pHi),
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliInteriorEqualSplit pLo pHi))

/-- Source-facing semantic target for `source_lemmaC8_uniform_first_level_polynomial_lower_bound`. -/
def source_lemmaC8_uniform_first_level_polynomial_lower_boundSpec
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, 0 < m → BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ, 0 < m →
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ))) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
    C / (((m + 2 : ℕ) : ℝ) ^ 3) ≤
      levels m (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))

/-- The quadratic first-level certificate proves the source's weaker uniform
`C M⁻³` bound once `M` is represented by the endpoint-vector size `m + 2`. -/
private lemma source_cubic_first_level_bound_of_quadratic
    (m : ℕ) (x : ℝ)
    (hquadratic : ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 ≤ x) :
    (1 / 2 : ℝ) / (((m + 2 : ℕ) : ℝ) ^ 3) ≤ x := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsmall : 0 < (((m + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hdenom : (((m + 1 : ℕ) : ℝ) ^ 2) ≤ (((m + 2 : ℕ) : ℝ) ^ 3) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith [pow_nonneg hm0 3]
  calc
    (1 / 2 : ℝ) / (((m + 2 : ℕ) : ℝ) ^ 3) ≤
        (1 / 2 : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) hsmall hdenom
    _ = ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 := by
      field_simp [ne_of_gt hsmall]
    _ ≤ x := hquadratic

/-- Corollary C.3 in its printed uniform-polynomial form. The stronger
quadratic certificate is used only to establish this source claim. -/
theorem corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    (levels sampleRate : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, 0 < m → BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ, 0 < m →
      BinaryEndpointAwareAdjacentRatesEqualize (levels m) (sampleRate m))
    (hsample_pos : ∀ m : ℕ, 0 < m →
      ∀ idx : Fin (m + 2), 0 < sampleRate m idx)
    (hsample_mono : ∀ m : ℕ, 0 < m →
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate m a ≤ sampleRate m b)
    (hfirst_sample : ∀ m : ℕ, 0 < m →
      sampleRate m (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1) :
    corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sqSpec
      levels sampleRate hlevels heq hsample_pos hsample_mono hfirst_sample := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro m hm
  apply source_cubic_first_level_bound_of_quadratic
  exact ProofBridge.corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    hm (hlevels m hm) (heq m hm) (hsample_pos m hm) (hsample_mono m hm)
    (hfirst_sample m hm)

/-- Lemma C.8 in its printed uniform-polynomial form. -/
theorem source_lemmaC8_uniform_first_level_polynomial_lower_bound
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, 0 < m → BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ, 0 < m →
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    source_lemmaC8_uniform_first_level_polynomial_lower_boundSpec levels hlevels heq := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro m hm
  apply source_cubic_first_level_bound_of_quadratic
  exact ProofBridge.source_lemmaC8_uniform_first_level_polynomial_lower_bound
    hm (hlevels m hm) (heq m hm)

/-- Source-facing semantic target for `source_lemmaC9_nested_bisection_runtime_log_squared`. -/
def source_lemmaC9_nested_bisection_runtime_log_squaredSpec
    {M : ℕ} (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) : Prop :=
  ∃ L : ℕ,
    (1 : ℝ) ≤ delta * (2 : ℝ) ^ L ∧
      ((L + 1 : ℕ) : ℝ) ≤
        Real.logb 2 (max 1 (1 / delta)) + 2 ∧
      ((nestedBisectionOperationCount M (L + 1) L : ℕ) : ℝ) ≤
        (M : ℝ) * (Real.logb 2 (max 1 (1 / delta)) + 2) ^ 2

/-- Source-facing semantic target for `source_theoremB1_proof_selector_nesting`. -/
def source_theoremB1_proof_selector_nestingSpec
    {M q : ℕ} (hM : 0 < M) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : Prop :=
  let old := Nat.floor ((M : ℝ) * θ)
  let refined :=
    Nat.floor (((theoremB1SourceDoubledIndexIterate M q : ℕ) : ℝ) * θ)
  refined ≤ 2 ^ q * old + 2 ^ q ∧
    2 ^ q * old ≤ refined + 2 ^ q

/-- Source-facing semantic target for `source_corollaryC4_kendall_spearman_subsequence`. -/
def source_corollaryC4_kendall_spearman_subsequenceSpec
    (C : ℕ) : Prop :=
  (∀ M : ℕ, Nonempty (Fin M) → 0 < M →
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (theorem31KendallFiniteDesignFeasible M)
      (theorem31KendallFiniteDesignValue M)
      (theorem31FiniteDesignEndpointRate M)
      (theorem31CanonicalUniformEndpointDesign M)) ∧
    (∀ M : ℕ, Nonempty (Fin M) → 0 < M →
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (theorem31SpearmanFiniteDesignFeasible M)
        (theorem31SpearmanFiniteDesignValue M)
        (theorem31FiniteDesignEndpointRate M)
        (theorem31CanonicalUniformEndpointDesign M)) ∧
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1)

end

end PaperInterface
end GJ19OptimalBinaryRatingSystems
