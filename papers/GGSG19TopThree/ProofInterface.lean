import GGSG19TopThree.PaperInterface

import GGSG19TopThree.ProofBridge



namespace GGSG19TopThree

namespace PaperInterface

open AppliedModelingLib.SocialChoice.Ranking
open AppliedModelingLib.Probability
open MeasureTheory
open scoped ProbabilityTheory
open GGSG19TopThree.ProofBridge
noncomputable section

theorem source_model_k_ranking_score {n : ℕ} (K : ℕ)
    (beta : Candidate n → ℝ) (ranking : Ranking n)
    (candidate : Candidate n) : source_model_k_ranking_scoreSpec (n := n) (K := K) (beta := beta) (ranking := ranking) (candidate := candidate) := by
  exact GGSG19TopThree.ProofBridge.source_model_k_ranking_score (n := n) (K := K) (beta := beta) (ranking := ranking) (candidate := candidate)

theorem source_model_k_approval_score {n : ℕ} (K : ℕ)
    (ranking : Ranking n) (candidate : Candidate n) : source_model_k_approval_scoreSpec (n := n) (K := K) (ranking := ranking) (candidate := candidate) := by
  exact GGSG19TopThree.ProofBridge.source_model_k_approval_score (n := n) (K := K) (ranking := ranking) (candidate := candidate)

theorem source_model_reasonable_positional_scoring_rules
    {n : ℕ} (beta : Candidate n → ℝ) : source_model_reasonable_positional_scoring_rulesSpec (n := n) (beta := beta) := by
  exact GGSG19TopThree.ProofBridge.source_model_reasonable_positional_scoring_rules (n := n) (beta := beta)

theorem source_model_cumulative_scores_ranking_and_outcome
    {n Stage : ℕ}
    (score : Candidate n → Ranking n → ℝ)
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (path : ℕ → Ranking n × Ranking n) (N : ℕ) (hN : 0 < N) : source_model_cumulative_scores_ranking_and_outcomeSpec (n := n) (Stage := Stage) (score := score) (targetPrefix := targetPrefix) (path := path) (N := N) (hN := hN) := by
  exact GGSG19TopThree.ProofBridge.source_model_cumulative_scores_ranking_and_outcome (n := n) (Stage := Stage) (score := score) (targetPrefix := targetPrefix) (path := path) (N := N) (hN := hN)

theorem paper_definition_large_deviation_rate_statement
    (A : ℕ → ℝ) (r : ℝ) : paper_definition_large_deviation_rate_statementSpec (A := A) (r := r) := by
  exact GGSG19TopThree.ProofBridge.paper_definition_large_deviation_rate_statement (A := A) (r := r)

theorem paper_definition_design_invariant_statement
    {Ω Rule Outcome : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reasonable : Rule → Prop)
    (outcome : Rule → ℕ → Ω → Outcome) : paper_definition_design_invariant_statementSpec (Ω := Ω) (Rule := Rule) (Outcome := Outcome) (μ := μ) (reasonable := reasonable) (outcome := outcome) := by
  exact GGSG19TopThree.ProofBridge.paper_definition_design_invariant_statement (Ω := Ω) (Rule := Rule) (Outcome := Outcome) (μ := μ) (reasonable := reasonable) (outcome := outcome)

theorem paper_definition_rate_optimal_statement
    {Rule : Type*} (feasible : Set Rule) (rate : Rule → ℝ) (βstar : Rule) : paper_definition_rate_optimal_statementSpec (Rule := Rule) (feasible := feasible) (rate := rate) (βstar := βstar) := by
  exact GGSG19TopThree.ProofBridge.paper_definition_rate_optimal_statement (Rule := Rule) (feasible := feasible) (rate := rate) (βstar := βstar)

theorem source_proposition1_thm_consistency_tiered
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) : source_proposition1_thm_consistency_tieredSpec (n := n) (Stage := Stage) (law := law) (targetPrefix := targetPrefix) := by
  exact GGSG19TopThree.ProofBridge.source_proposition1_thm_consistency_tiered (n := n) (Stage := Stage) (law := law) (targetPrefix := targetPrefix)

theorem source_proposition2_thm_pairwiselearning_finite_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) : source_proposition2_thm_pairwiselearning_finite_supportSpec (Signal := Signal) (law := law) (hiScore := hiScore) (loScore := loScore) (hmean := hmean) := by
  exact GGSG19TopThree.ProofBridge.source_proposition2_thm_pairwiselearning_finite_support (Signal := Signal) (law := law) (hiScore := hiScore) (loScore := loScore) (hmean := hmean)

theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary
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
        pZero) : source_proposition3_lem_pairwiselearning_approval_finite_ternarySpec (Signal := Signal) (law := law) (hiScore := hiScore) (loScore := loScore) (pUp := pUp) (pDown := pDown) (pZero := pZero) (hle := hle) (hscore := hscore) (hUpProb := hUpProb) (hDownProb := hDownProb) (hZeroProb := hZeroProb) := by
  exact GGSG19TopThree.ProofBridge.source_proposition3_lem_pairwiselearning_approval_finite_ternary (Signal := Signal) (law := law) (hiScore := hiScore) (loScore := loScore) (pUp := pUp) (pDown := pDown) (pZero := pZero) (hle := hle) (hscore := hscore) (hUpProb := hUpProb) (hDownProb := hDownProb) (hZeroProb := hZeroProb)

theorem source_proposition4_thm_goal_learning_exact_minimum_rate
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal)) : source_proposition4_thm_goal_learning_exact_minimum_rateSpec (Pair := Pair) (Candidate := Candidate) (Signal := Signal) (law := law) (score := score) (hi := hi) (lo := lo) (hmean := hmean) := by
  exact GGSG19TopThree.ProofBridge.source_proposition4_thm_goal_learning_exact_minimum_rate (Pair := Pair) (Candidate := Candidate) (Signal := Signal) (law := law) (score := score) (hi := hi) (lo := lo) (hmean := hmean)

theorem source_proposition4_thm_goal_learning_finite_sample_M_sq_bound
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (hcard : Fintype.card Pair ≤ Fintype.card Candidate ^ 2)
    (n : ℕ) : source_proposition4_thm_goal_learning_finite_sample_M_sq_boundSpec (Pair := Pair) (Candidate := Candidate) (Signal := Signal) (law := law) (score := score) (hi := hi) (lo := lo) (hmean := hmean) (hcard := hcard) (n := n) := by
  exact GGSG19TopThree.ProofBridge.source_proposition4_thm_goal_learning_finite_sample_M_sq_bound (Pair := Pair) (Candidate := Candidate) (Signal := Signal) (law := law) (score := score) (hi := hi) (lo := lo) (hmean := hmean) (hcard := hcard) (n := n)

theorem source_theorem1_lem_randomizebetterscoring_arbitrary_goal
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
          finiteLogMGF law (staticGap pair) z)) : source_theorem1_lem_randomizebetterscoring_arbitrary_goalSpec (Pair := Pair) (Rule := Rule) (Signal := Signal) (law := law) (weight := weight) (gap := gap) (staticGap := staticGap) (hstatic := hstatic) (hweight := hweight) (hsum := hsum) (hstatic_bdd := hstatic_bdd) := by
  exact GGSG19TopThree.ProofBridge.source_theorem1_lem_randomizebetterscoring_arbitrary_goal (Pair := Pair) (Rule := Rule) (Signal := Signal) (law := law) (weight := weight) (gap := gap) (staticGap := staticGap) (hstatic := hstatic) (hweight := hweight) (hsum := hsum) (hstatic_bdd := hstatic_bdd)

theorem source_theorem2_lem_randomizenotbetterapproval_pairwise
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) : source_theorem2_lem_randomizenotbetterapproval_pairwiseSpec (n := n) (Rule := Rule) (law := law) (K := K) (weight := weight) (hweight := hweight) (hsum := hsum) (hi := hi) (lo := lo) := by
  exact GGSG19TopThree.ProofBridge.source_theorem2_lem_randomizenotbetterapproval_pairwise (n := n) (Rule := Rule) (law := law) (K := K) (weight := weight) (hweight := hweight) (hsum := hsum) (hi := hi) (lo := lo)

theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed : source_theorem_lem_randomizebetterapproval_w_selection_constructedSpec := by
  exact GGSG19TopThree.ProofBridge.source_theorem_lem_randomizebetterapproval_w_selection_constructed

theorem source_corollary_lem_mallowsnorando_zero_noise
    {n : ℕ} (center : Ranking n) (W : Candidate n) (hW : 0 < W.val)
    (randomizedRate : WithTop ℝ) : source_corollary_lem_mallowsnorando_zero_noiseSpec (n := n) (center := center) (W := W) (hW := hW) (randomizedRate := randomizedRate) := by
  exact GGSG19TopThree.ProofBridge.source_corollary_lem_mallowsnorando_zero_noise (n := n) (center := center) (W := W) (hW := hW) (randomizedRate := randomizedRate)

theorem source_corollary_lem_mallowsnorando
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) : source_corollary_lem_mallowsnorandoSpec (n := n) (center := center) (q := q) (W := W) (hDomain := hDomain) (Rule := Rule) (K := K) (hK_pos := hK_pos) (hK_lt := hK_lt) (weight := weight) (hweight := hweight) (hsum := hsum) := by
  exact GGSG19TopThree.ProofBridge.source_corollary_lem_mallowsnorando (n := n) (center := center) (q := q) (W := W) (hDomain := hDomain) (Rule := Rule) (K := K) (hK_pos := hK_pos) (hK_lt := hK_lt) (weight := weight) (hweight := hweight) (hsum := hsum)

theorem source_theorem_lem_mallowsnotWK_counterexample : source_theorem_lem_mallowsnotWK_counterexampleSpec := by
  exact GGSG19TopThree.ProofBridge.source_theorem_lem_mallowsnotWK_counterexample

theorem source_example_durham_ward1_randomized_approval_improves_static3_static4 : source_example_durham_ward1_randomized_approval_improves_static3_static4Spec := by
  exact GGSG19TopThree.ProofBridge.source_example_durham_ward1_randomized_approval_improves_static3_static4

theorem source_proof_mallows_common_pivotal_pair
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    (K : ℕ) (hK_pos : 0 < K) (hK_lt : K < n + 2) : source_proof_mallows_common_pivotal_pairSpec (n := n) (center := center) (q := q) (W := W) (hDomain := hDomain) (K := K) (hK_pos := hK_pos) (hK_lt := hK_lt) := by
  exact GGSG19TopThree.ProofBridge.source_proof_mallows_common_pivotal_pair (n := n) (center := center) (q := q) (W := W) (hDomain := hDomain) (K := K) (hK_pos := hK_pos) (hK_lt := hK_lt)

theorem source_proof_mallows_four_candidate_joint_location_matrix
    (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (ell k : Fin 4) : source_proof_mallows_four_candidate_joint_location_matrixSpec (q := q) (hDomain := hDomain) (ell := ell) (k := k) := by
  exact GGSG19TopThree.ProofBridge.source_proof_mallows_four_candidate_joint_location_matrix (q := q) (hDomain := hDomain) (ell := ell) (k := k)

theorem source_mallows_repeated_insertion_probability_formula
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (stage inserted : Fin N) : source_mallows_repeated_insertion_probability_formulaSpec (N := N) (q := q) (hDomain := hDomain) (stage := stage) (inserted := inserted) := by
  exact GGSG19TopThree.ProofBridge.source_mallows_repeated_insertion_probability_formula (N := N) (q := q) (hDomain := hDomain) (stage := stage) (inserted := inserted)

theorem source_mallows_arbitrary_pair_joint_location_dynamic_program
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (leftStage rightStage : Fin N) : source_mallows_arbitrary_pair_joint_location_dynamic_programSpec (N := N) (q := q) (hDomain := hDomain) (leftStage := leftStage) (rightStage := rightStage) := by
  exact GGSG19TopThree.ProofBridge.source_mallows_arbitrary_pair_joint_location_dynamic_program (N := N) (q := q) (hDomain := hDomain) (leftStage := leftStage) (rightStage := rightStage)

end

end PaperInterface
end GGSG19TopThree
