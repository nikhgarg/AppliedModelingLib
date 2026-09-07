import GGSG19TopThree.ProofBridge

namespace GGSG19TopThree

namespace PaperInterface

open AppliedModelingLib.SocialChoice.Ranking
open AppliedModelingLib.Probability
open MeasureTheory
open scoped ProbabilityTheory
open GGSG19TopThree.ProofBridge
noncomputable section

/-- Source-facing semantic target for `source_model_k_ranking_score`. -/
def source_model_k_ranking_scoreSpec {n : ℕ} (K : ℕ)
    (beta : Candidate n → ℝ) (ranking : Ranking n)
    (candidate : Candidate n) : Prop :=
  kRankingScore K beta ranking candidate =
    (if (rankOf ranking candidate).val < K then
      beta (rankOf ranking candidate)
    else 0)

/-- Source-facing semantic target for `source_model_k_approval_score`. -/
def source_model_k_approval_scoreSpec {n : ℕ} (K : ℕ)
    (ranking : Ranking n) (candidate : Candidate n) : Prop :=
  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K ranking candidate =
    if (rankOf ranking candidate).val < K then 1 else 0

/-- Source-facing semantic target for `source_model_reasonable_positional_scoring_rules`. -/
def source_model_reasonable_positional_scoring_rulesSpec
    {n : ℕ} (beta : Candidate n → ℝ) : Prop :=
  ReasonablePrefixWeights
      (fun cut : RankingProperPrefixCut n =>
        beta ⟨cut.val, by omega⟩ -
          beta ⟨cut.val + 1, by omega⟩) ↔
    (∀ cut : RankingProperPrefixCut n,
      beta ⟨cut.val + 1, by omega⟩ ≤
        beta ⟨cut.val, by omega⟩) ∧
    ∃ cut : RankingProperPrefixCut n,
      beta ⟨cut.val + 1, by omega⟩ <
        beta ⟨cut.val, by omega⟩

/-- Source-facing semantic target for `source_model_cumulative_scores_ranking_and_outcome`. -/
def source_model_cumulative_scores_ranking_and_outcomeSpec
    {n Stage : ℕ}
    (score : Candidate n → Ranking n → ℝ)
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (path : ℕ → Ranking n × Ranking n) (N : ℕ) (hN : 0 < N) : Prop :=
  (∀ candidate : Candidate n,
    iidUniformTieCandidateAverageScore score path N candidate =
      (N : ℝ)⁻¹ *
        (∑ voter ∈ Finset.range N, score candidate (path voter).1)) ∧
    (iidUniformTieTieredCorrect score targetPrefix path N ↔
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage → lo ∉ targetPrefix stage →
            iidUniformTieCandidateAverageScore score path N lo <
                iidUniformTieCandidateAverageScore score path N hi ∨
              (iidUniformTieCandidateAverageScore score path N lo =
                  iidUniformTieCandidateAverageScore score path N hi ∧
                rankOf (path N).2 hi < rankOf (path N).2 lo))

/-- Source-facing semantic target for `paper_definition_large_deviation_rate_statement`. -/
def paper_definition_large_deviation_rate_statementSpec
    (A : ℕ → ℝ) (r : ℝ) : Prop :=
  paper_definition_large_deviation_rate A r ↔
    (∀ N : ℕ, 0 ≤ A N) ∧
      Filter.Tendsto A Filter.atTop (nhds 0) ∧
      0 < r ∧
      Filter.Tendsto
        (fun N : ℕ => -((N : ℝ)⁻¹) * Real.log (A N))
        Filter.atTop (nhds r)

/-- Source-facing semantic target for `paper_definition_design_invariant_statement`. -/
def paper_definition_design_invariant_statementSpec
    {Ω Rule Outcome : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reasonable : Rule → Prop)
    (outcome : Rule → ℕ → Ω → Outcome) : Prop :=
  paper_definition_design_invariant μ reasonable outcome ↔
    ∃ Ostar : Outcome,
      ∀ β : Rule, reasonable β →
        ∀ᵐ ω ∂μ,
          ∀ᶠ N : ℕ in Filter.atTop, outcome β N ω = Ostar

/-- Source-facing semantic target for `paper_definition_rate_optimal_statement`. -/
def paper_definition_rate_optimal_statementSpec
    {Rule : Type*} (feasible : Set Rule) (rate : Rule → ℝ) (βstar : Rule) : Prop :=
  paper_definition_rate_optimal feasible rate βstar ↔
    βstar ∈ feasible ∧
      ∀ β : Rule, β ∈ feasible → rate β ≤ rate βstar

/-- Source-facing semantic target for `source_proposition1_thm_consistency_tiered`. -/
def source_proposition1_thm_consistency_tieredSpec
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) : Prop :=
  (∀ stage : Fin Stage,
    ∀ hi lo : Candidate n,
      hi ∈ targetPrefix stage →
        lo ∉ targetPrefix stage →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
    PropositionOneUniformTieConsistency law targetPrefix

/-- Source-facing semantic target for `source_proposition2_thm_pairwiselearning_finite_support`. -/
def source_proposition2_thm_pairwiselearning_finite_supportSpec
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) : Prop :=
  (ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (pairwiseScoringRate law hiScore loScore) ∨
      (∃ pZero : ℝ,
        AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = 0) =
          pZero ∧
        0 < pZero ∧
        ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (-Real.log pZero)) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0)) ∧
    ∀ n,
      pairwiseScoringErrorProb law hiScore loScore n ≤
        Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore)

/-- Source-facing semantic target for `source_proposition3_lem_pairwiselearning_approval_finite_ternary`. -/
def source_proposition3_lem_pairwiselearning_approval_finite_ternarySpec
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown pZero : ℝ}
    (hle : pDown ≤ pUp)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hUpProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 1) =
        pUp)
    (hDownProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        pDown)
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero) : Prop :=
  ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) ∨
    (∀ᶠ n in Filter.atTop,
      pairwiseScoringErrorProb law hiScore loScore n = 0)

/-- Source-facing semantic target for `source_proposition4_thm_goal_learning_exact_minimum_rate`. -/
def source_proposition4_thm_goal_learning_exact_minimum_rateSpec
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal)) : Prop :=
  HasExtendedExponentialRate
    (fun sampleSize =>
      ∑ pair : Pair,
        finiteScoreGapPairwiseErrorProb law score
          (hi pair) (lo pair) sampleSize)
    (finiteOutcomeLearningExtendedRate
      (fun pair : Pair =>
        pairwiseScoringExtendedRate law
          (score (hi pair)) (score (lo pair))))

/-- Source-facing semantic target for `source_proposition4_thm_goal_learning_finite_sample_M_sq_bound`. -/
def source_proposition4_thm_goal_learning_finite_sample_M_sq_boundSpec
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (hcard : Fintype.card Pair ≤ Fintype.card Candidate ^ 2)
    (n : ℕ) : Prop :=
  (∑ pair : Pair,
    finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
    (Fintype.card Candidate : ℝ) ^ 2 *
      Real.exp (-(n : ℝ) *
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            pairwiseScoringRate law
              (score (hi pair)) (score (lo pair))))

/-- Source-facing semantic target for `source_theorem1_lem_randomizebetterscoring_arbitrary_goal`. -/
def source_theorem1_lem_randomizebetterscoring_arbitrary_goalSpec
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      ∀ pair,
        BddBelow (Set.range fun z : ℝ =>
          finiteLogMGF law (staticGap pair) z)) : Prop :=
  finiteOutcomeLearningRate
      (fun pair : Pair =>
        randomizedScoringMixtureRate law weight (gap pair)) ≤
    finiteOutcomeLearningRate
      (fun pair : Pair => finiteChernoffRate law (staticGap pair))

/-- Source-facing semantic target for `source_theorem2_lem_randomizenotbetterapproval_pairwise`. -/
def source_theorem2_lem_randomizenotbetterapproval_pairwiseSpec
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) : Prop :=
  ∃ rule : Rule,
    (approvalPairwiseRate
        (∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
        (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo) :
      WithTop ℝ) ≤
      approvalPairwiseExtendedRate
        (kApprovalPairUpProb law (K rule) hi lo)
        (kApprovalPairDownProb law (K rule) hi lo)

/-- Source-facing semantic target for `source_theorem_lem_randomizebetterapproval_w_selection_constructed`. -/
def source_theorem_lem_randomizebetterapproval_w_selection_constructedSpec : Prop :=
  StrictTopPrefixDominanceOn
         constructedWSelectionRanking1TopPrefixProb
         constructedWSelectionCrossTier ∧
       (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
           (fun K =>
             finiteOutcomeLearningRate
               (constructedWSelectionRanking1StaticKRate K)) <
         finiteOutcomeLearningRate
           constructedWSelectionRanking1RandomizedApprovalRate

/-- Source-facing semantic target for `source_corollary_lem_mallowsnorando_zero_noise`. -/
def source_corollary_lem_mallowsnorando_zero_noiseSpec
    {n : ℕ} (center : Ranking n) (W : Candidate n) (hW : 0 < W.val)
    (randomizedRate : WithTop ℝ) : Prop :=
  HasExtendedExponentialRate (zeroNoiseTopWApprovalError center W) ⊤ ∧
    randomizedRate ≤ ⊤

/-- Source-facing semantic target for `source_corollary_lem_mallowsnorando`. -/
def source_corollary_lem_mallowsnorandoSpec
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) : Prop :=
  ∃ cut : RankingProperPrefixCut n,
    (∀ cut' : RankingProperPrefixCut n,
      mallowsTopWKApprovalOutcomeRate
          (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
          (cut'.val + 1) ≤
        mallowsTopWKApprovalOutcomeRate
          (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
          (cut.val + 1)) ∧
    mallowsTopWRandomizedKApprovalOutcomeRate
        (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 K weight ≤
      mallowsTopWKApprovalOutcomeRate
        (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
        (cut.val + 1)

/-- Source-facing semantic target for `source_theorem_lem_mallowsnotWK_counterexample`. -/
def source_theorem_lem_mallowsnotWK_counterexampleSpec : Prop :=
  ∃ M : MallowsSpec 2,
    M.center = Equiv.refl (Candidate 2) ∧
      M.q = mallowsHighNoisePhi ∧
        ∃ better : Fin 3,
          better ≠ (2 : Fin 3) ∧
            finiteOutcomeLearningRate
                (mallowsW3StaticKApprovalPairRate M (2 : Fin 3)) <
              finiteOutcomeLearningRate
                (mallowsW3StaticKApprovalPairRate M better)

/-- Source-facing semantic target for `source_example_durham_ward1_randomized_approval_improves_static3_static4`. -/
def source_example_durham_ward1_randomized_approval_improves_static3_static4Spec : Prop :=
  max
      (finiteOutcomeLearningRate durhamWard1K3Rate)
      (finiteOutcomeLearningRate durhamWard1K4Rate) <
    finiteOutcomeLearningRate durhamWard1RandomizedRate

/-- Source-facing semantic target for `source_proof_mallows_common_pivotal_pair`. -/
def source_proof_mallows_common_pivotal_pairSpec
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    (K : ℕ) (hK_pos : 0 < K) (hK_lt : K < n + 2) : Prop :=
  mallowsTopWKApprovalOutcomeRate
      (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 K =
    mallowsTopWKApprovalPairRate
      (MallowsSpec.ofQ center q hDomain.2.1) W K
      (topWBoundaryPair center W hDomain.1)

/-- Source-facing semantic target for `source_proof_mallows_four_candidate_joint_location_matrix`. -/
def source_proof_mallows_four_candidate_joint_location_matrixSpec
    (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (ell k : Fin 4) : Prop :=
  mallowsFourCandidate34JointLocationProb q hDomain.1 ell k =
    if ell = k then 0
    else
      q ^ (if ell.val < k.val then
          5 - ell.val - k.val
        else
          6 - ell.val - k.val) /
        (1 + q + q ^ 2) /
        (1 + q + q ^ 2 + q ^ 3)

/-- Source-facing semantic target for `source_mallows_repeated_insertion_probability_formula`. -/
def source_mallows_repeated_insertion_probability_formulaSpec
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (stage inserted : Fin N) : Prop :=
  ((mallowsInsertionPMF q hDomain.1 stage) inserted).toReal =
      if inserted.val ≤ stage.val then
        q ^ (stage.val - inserted.val) /
          Finset.sum (Finset.range (stage.val + 1))
            (fun r => q ^ (stage.val - r))
      else 0

/-- Source-facing semantic target for `source_mallows_arbitrary_pair_joint_location_dynamic_program`. -/
def source_mallows_arbitrary_pair_joint_location_dynamic_programSpec
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (leftStage rightStage : Fin N) : Prop :=
  (∀ state : MallowsPairPositionState N,
    (mallowsPairDPTabulationRun
        (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
        leftStage rightStage N).table state =
      ((mallowsPairProcess
        (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
        leftStage rightStage N) state).toReal) ∧
    (∑ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun
        (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
        leftStage rightStage N).table state = 1) ∧
    (mallowsPairDPTabulationRun
        (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
        leftStage rightStage N).scalarOperations =
      mallowsPairDPDenseOperationBudget N ∧
    (mallowsPairDPTabulationRun
        (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
        leftStage rightStage N).scalarOperations ≤ (N + 1) ^ 6

end

end PaperInterface
end GGSG19TopThree
