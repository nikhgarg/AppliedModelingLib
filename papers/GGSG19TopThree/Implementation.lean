import GGSG19TopThree.MainTheorems
import GGSG19TopThree.MallowsApproval
import GGSG19TopThree.MallowsBoundary
import GGSG19TopThree.MallowsOneLoserBoundary
import GGSG19TopThree.MallowsTopTwoBoundary

/-!
# Proof Interface: Who is in Your Top Three?

This proof-facing interface exposes the source formulas from Section 3.1 of
Garg--Gelauff--Sakshuwong--Goel (2019).  The paper's central analytic task is
to certify the pairwise Chernoff/LDP rate for iid voter score gaps; the current
surface includes a support-aware stationary finite-tilt method-of-types route
for that exact-rate layer, plus reusable finite aggregation around it.  The
compact human-review surface is `PaperInterface.lean`.

## Paper Definitions

- `definition_large_deviation_rate`: paper definition of an exponential rate.
- `proposition2_pairwise_rate_formula`: source formula for positional scoring
  pairwise rates.
- `proposition3_approval_pairwise_rate_formula`: source formula for K-approval
  pairwise rates.

## Named Results Exposed

- `proposition1_design_invariance_prefix_score_core`: finite prefix-probability
  separation core behind asymptotic design invariance.
- `proposition1_design_invariance_tierwise_prefix_score_core`: finite
  tierwise version over all required higher-tier/lower-tier pairs.
- `proposition1_strict_prefix_dominance_implies_all_reasonable_prefix_score_consistency`:
  ADI-shaped forward conclusion over all reasonable prefix-score rules.
- `proposition1_ranking_law_strict_prefix_dominance_implies_all_reasonable_prefix_score_consistency`:
  Proposition 1 forward direction specialized to the paper's finite ranking
  law and W-selection goal.
- `proposition1_ranking_law_tiered_prefix_selection_error_tendsto_zero`:
  Proposition 1 forward direction for finite tiered goals represented by
  cumulative tier-prefix sets.
- `proposition1_ranking_law_strict_prefix_dominance_iff_all_reasonable_prefix_score_separation`:
  Proposition 1 finite ranking-law W-selection iff in source prefix-score
  language.
- `proposition1_ranking_law_tiered_strict_prefix_dominance_iff_all_reasonable_prefix_score_separation`:
  Proposition 1 finite ranking-law tiered-goal iff in source prefix-score
  language.
- `proposition1_ranking_law_prefix_score_separation_implies_all_reasonable_prefix_score_consistency`:
  Proposition 1 W-selection convergence from the equivalent expected-score
  separation condition.
- `proposition1_ranking_law_prefix_score_separation_implies_all_reasonable_tiered_prefix_score_consistency`:
  Proposition 1 tiered convergence from the equivalent expected-score
  separation condition.
- `proposition1_induced_prefix_expected_score_bridge`: finite one-voter law
  bridge from prefix events to expected prefix scores.
- `proposition1_induced_prefix_expected_gap_positive`: finite one-voter law
  bridge turning strict prefix dominance into a positive expected score gap.
- `proposition1_induced_prefix_pairwise_error_positive_exponential_decay`:
  strict prefix dominance gives a positive exponential iid pairwise error
  upper-bound rate for the induced prefix-score rule.
- `proposition1_induced_prefix_pairwise_error_positive_exponential_decay_on`:
  tierwise version over every required higher/lower pair.
- `proposition1_induced_prefix_relevant_pair_aggregate_positive_exponential_decay`:
  finite weighted aggregate version over a relevant-pair index type.
- `proposition1_induced_prefix_pairwise_error_tendsto_zero`: induced iid
  pairwise prefix-score error probabilities converge to zero.
- `proposition1_induced_prefix_relevant_pair_aggregate_tendsto_zero`: finite
  relevant-pair aggregate error converges to zero.
- `proposition1_induced_prefix_selection_error_tendsto_zero`: source-level
  W-set selection conclusion from strict prefix dominance and score-top
  selection.
- `proposition1_induced_prefix_selection_error_tendsto_zero_on`: source-shaped
  version using the W-set's natural higher-tier/lower-tier predicate.
- `proposition1_induced_prefix_selection_error_tendsto_one_of_reverse_prefix_expected_score`:
  strict converse fragment: a true loser with strictly larger induced expected
  prefix score makes score-top W-selection fail with probability tending to one.
- `proposition1_induced_prefix_all_reasonable_consistency_implies_weak_expected_score_separation`:
  necessary weak expected-score separation from all-reasonable prefix-score
  consistency.
- `proposition1_ranking_law_canonical_selection_error_tendsto_one_of_reverse_top_prefix_prob`:
  ranking-law strict converse fragment for a single reversed top-prefix
  probability, using the corresponding indicator prefix score.
- `proposition1_ranking_law_canonical_selection_error_not_tendsto_zero_of_reverse_top_prefix_prob`:
  direct non-consistency form of that strict converse fragment.
- `proposition1_ranking_law_reverse_top_prefix_prob_witnesses_reasonable_nonconsistency`:
  bundles the indicator prefix score's reasonableness with the same
  non-consistency witness.
- `proposition1_ranking_law_reverse_top_prefix_prob_refutes_all_reasonable_prefix_score_consistency`:
  strict reversed-prefix converse fragment in all-reasonable-score form.
- `proposition1_ranking_law_all_reasonable_prefix_score_consistency_implies_weak_top_prefix_dominance`:
  necessary weak-dominance direction obtained from the strict reverse witness.
- `proposition1_ranking_law_prefix_score_consistency_strict_forward_weak_necessary`:
  strict-sufficient / weak-necessary sandwich for the ranking-law W-selection
  consistency surface.
- `proposition1_ranking_law_strict_prefix_dominance_iff_all_reasonable_prefix_score_consistency_of_no_cross_tier_prefix_ties`:
  Proposition 1 W-selection consistency iff away from exact cross-tier prefix
  ties.
- `proposition1_ranking_law_tiered_strict_prefix_dominance_iff_all_reasonable_tiered_prefix_score_consistency_of_no_cross_tier_prefix_ties`:
  Proposition 1 tiered consistency iff away from exact cross-tier prefix ties.
- `proposition2_pairwise_chernoff_upper_bound`: iid finite-score Chernoff
  upper-bound endpoint for any nonpositive dual parameter.
- `proposition2_pairwise_chernoff_pointwise_upper_bound_at_rate_of_stationary`:
  finite-`N` Chernoff upper bound at the exact source pairwise rate from a
  stationary nonpositive dual.
- `proposition2_pairwise_chernoff_pointwise_upper_bound_at_rate_of_mean_nonneg_pos_neg_atoms`:
  finite-`N` Chernoff upper bound at the exact source pairwise rate for finite
  laws with nonnegative mean and positive/negative score-gap atoms.
- `proposition2_pairwise_positive_expected_gap_chernoff_upper_bound_exists`:
  positive expected one-voter score gap gives some positive exponential iid
  pairwise error upper-bound rate.
- `proposition2_pairwise_positive_expected_gap_chernoff_dual_exists`:
  positive expected one-voter score gap gives an explicit nonpositive dual
  with positive dual rate and a corresponding iid upper-bound certificate.
- `proposition2_pairwise_exact_rate_from_support_nonneg_zero_gap_prob`:
  one-sided finite-real boundary exact rate when all positive-mass gaps are
  nonnegative and the zero-gap probability is positive.
- `proposition2_pairwise_eventually_zero_from_support_pos`: one-sided
  finite-real boundary with strictly positive support, where the finite iid
  pairwise mistake event is eventually empty.
- `proposition2_pairwise_exact_rate_from_finite_iid_cramer`: exact iid
  pairwise rate from reusable finite-support Cramer bounds.
- `proposition2_pairwise_exact_rate_from_bucket_lower`: exact iid pairwise
  rate from explicit finite empirical bucket/type lower bounds.
- `proposition2_pairwise_exact_rate_from_count_vector_lower`: exact iid
  pairwise rate from explicit finite empirical count-vector lower bounds.
- `proposition2_pairwise_exact_rate_from_empirical_type_lower`: exact iid
  pairwise rate from exact multinomial empirical-type lower bounds.
- `proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_support`:
  exact iid pairwise rate from the stationary finite tilt by method of types,
  preserving the finite signal law's support.
- `proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms`:
  support-aware exact iid pairwise rate where the stationary tilt is found
  internally from nonnegative mean and positive/negative score-gap atoms.
- `proposition2_pairwise_stationary_tilt_rate_identity_and_exact_rate_of_mean_nonneg_pos_neg_atoms`:
  bundled Prop. 2 stationary-tilt endpoint exposing the internally found dual,
  displayed rate identity, and exact iid error rate.
- `proposition2_pairwise_exact_rate_or_boundary_from_finite_support_mean_nonneg`:
  finite-support Prop. 2 trichotomy: stationary exact finite rate, zero-gap
  boundary exact finite rate, or strict-support eventual-zero boundary.
- `proposition3_approval_pairwise_rate_exact_minimization`: K-approval ternary
  closed-form rate equals the log-MGF infimum.
- `proposition3_approval_pairwise_chernoff_upper_bound`: K-approval ternary
  closed-form Chernoff upper-bound endpoint.
- `proposition3_approval_pairwise_chernoff_pointwise_upper_bound`: finite-`N`
  K-approval ternary closed-form Chernoff upper bound at
  `approvalPairwiseRate`.
- `proposition3_approval_pairwise_exact_rate_from_finite_iid_cramer`:
  K-approval exact pairwise rate from all-dual ternary MGF identification and
  finite-support Cramer bounds.
- `proposition3_approval_pairwise_cramer_certificate_from_ternary_scores`:
  the finite iid Cramer certificate required by the Cramer-form endpoint is
  closed for nondegenerate ternary approval-style score gaps.
- `proposition3_approval_pairwise_exact_rate_from_ternary_scores`: exact
  K-approval pairwise rate from the natural plus/zero/minus score-gap
  classification and nonzero event probabilities.
- `proposition3_approval_pairwise_exact_rate_from_ternary_scores_down_zero`:
  K-approval boundary exact rate when down-gaps have zero probability and
  zero-gaps have positive probability.
- `proposition3_approval_pairwise_eventually_zero_from_ternary_scores_down_zero_zero_zero`:
  K-approval strict boundary where the iid pairwise mistake event is
  eventually empty.
- `proposition3_approval_pairwise_exact_rate_or_eventually_zero_from_ternary_scores`:
  finite ternary K-approval trichotomy: source closed-form exact rate or
  strict-boundary eventual-zero error.
- `proposition3_k_approval_pairwise_exact_rate_from_ranking_law`: exact
  K-approval pairwise rate directly from a finite ranking law.
- `proposition3_k_approval_pairwise_exact_rate_from_ranking_law_down_zero`:
  K-approval boundary exact rate directly from a finite ranking law.
- `proposition3_k_approval_pairwise_exact_rate_or_eventually_zero_from_ranking_law`:
  finite ranking-law K-approval trichotomy under weak up/down ordering.
- `proposition4_k_approval_relevant_pair_rate_certificate_from_ranking_law`:
  relevant-pair K-approval exact-rate certificate directly from a finite
  ranking law.
- `proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs`:
  exact finite aggregation over the relevant K-approval pair set.
- `proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_exact_or_eventually_zero`:
  exact finite aggregation over relevant K-approval pairs when
  non-minimizing pairs may be strict-boundary eventually zero.
- `proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_down_zero`:
  exact finite aggregation over relevant K-approval pairs in the zero-down
  boundary case.
- `proposition3_approval_pairwise_exact_rate_from_ternary_lower_bounds`:
  exact K-approval pairwise rate from lower-tail lower bounds only; the
  Chernoff upper-bound side is formalized.
- `proposition3_approval_pairwise_exact_rate_from_poly_geometric_lower`:
  exact K-approval pairwise rate from the polynomial-times-geometric lower
  bound shape produced by finite-type lower-bound arguments.
- `proposition4_outcome_error_upper_bound_from_pairwise_certificates`: finite
  aggregation part of the outcome-learning proposition.
- `proposition4_relevant_score_gap_error_sum_pointwise_upper_bound_from_duals`:
  finite-`N` Chernoff upper bound for the expected number of indexed relevant
  pairwise mistakes.
- `proposition4_relevant_score_gap_error_sum_pointwise_upper_bound_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms`:
  finite-`N` relevant-pair upper bound at the realized finite outcome-learning
  rate, using the support-aware Prop. 2 pointwise bound.
- `proposition4_cross_tier_error_sum_pointwise_upper_bound_from_duals`:
  finite-`N` Chernoff upper bound in the source's coarse `M^2` form for
  W-selection cross-tier pairwise mistakes.
- `proposition4_cross_tier_error_sum_pointwise_upper_bound_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms`:
  finite-`N` W-selection cross-tier bound in the source's coarse `M^2` form at
  the realized finite outcome-learning rate.
- `proposition4_outcome_error_exact_rate_from_pairwise_minimum`: exact finite
  minimum-rate aggregation endpoint.
- `proposition4_outcome_error_exact_rate_from_relevant_pairs_finite_support_exact_or_boundary_or_eventually_zero`:
  exact finite aggregation from the finite-support Prop. 2 trichotomy, allowing
  source-rate, zero-gap boundary, and strict-boundary branches.
- `proposition4_outcome_error_exact_rate_from_support_nonneg_zero_gap_prob`:
  exact finite aggregation for one-sided nonnegative score gaps with positive
  zero-gap probability.
- `proposition4_outcome_error_exact_rate_from_support_nonneg_zero_gap_prob_relevant_pairs`:
  relevant-pair version of the one-sided zero-gap finite-real aggregation
  theorem.
- `proposition4_outcome_error_exact_rate_from_approval_ternary_scores_down_zero`:
  exact finite aggregation for ternary approval-style boundary pairs with zero
  down-gap probability.
- `proposition4_relevant_score_gap_aggregate_eventually_zero_from_support_pos`:
  one-sided strict-support relevant-pair aggregation, where every indexed
  pairwise mistake event is eventually empty.
- `proposition4_outcome_error_upper_bound_from_finite_score_gap_duals`: finite
  aggregation directly from iid finite-score Chernoff duals.
- `proposition4_relevant_score_gap_aggregate_positive_exponential_decay`:
  finite weighted aggregate has some positive exponential upper-bound rate once
  every relevant score gap has positive one-voter expectation.
- `proposition4_outcome_error_exact_rate_from_finite_score_gap_cramer`: exact
  finite aggregation directly from iid finite-score Cramer certificates.
- `proposition4_outcome_error_exact_rate_from_finite_score_gap_empirical_type_lower`:
  exact finite aggregation from exact multinomial empirical-type lower bounds.
- `proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support`:
  exact finite aggregation from stationary finite tilts by method of types, for
  finite signal laws with support-preserving empirical types.
- `proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_at_finiteOutcomeLearningRate`:
  the same supplied-stationary finite aggregation theorem stated at the
  realized finite outcome-learning rate.
- `proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms`:
  support-aware finite aggregation where per-pair stationary tilts are found
  internally from nonnegative means and positive/negative score-gap atoms.
- `proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate_relevant_pairs`:
  support-aware stationary finite aggregation over exactly the relevant
  ordered-pair index used by the paper theorem.
- `proposition4_cross_tier_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate`:
  source-shaped W-selection `Q^N` exact-rate theorem over cross-tier pairs.
- `proposition4_outcome_error_exact_rate_from_approval_cramer`: exact finite
  aggregation stated directly in closed-form K-approval rates.
- `proposition4_outcome_error_exact_rate_from_approval_ternary_scores`: exact
  finite aggregation for K-approval from concrete ternary score gaps.
- `randomized_scoring_pairwise_rate_le_static_of_log_mgf_domination`: pairwise
  rate comparison from the source convexity/log-MGF domination step.
- `randomized_scoring_mixture_rate_le_static_of_weighted_score`: direct finite
  Jensen proof that the convex-combination scoring rule weakly dominates a
  randomized scoring-rule mixture in pairwise Chernoff rate.
- `randomized_scoring_sampling_law_finite_chernoff_rate_eq_mixture_rate`: the
  actual one-voter randomized scoring law has exactly that mixture rate.
- `randomized_scoring_outcome_rate_le_static_of_pairwise`: finite-min bridge for
  the scoring-rule randomization comparison.
- `randomized_scoring_actual_outcome_rate_le_static_of_weighted_score`: actual
  randomized scoring mechanism weakly dominated in finite outcome-learning
  rate by the convex-combination scoring rule.
- `randomized_scoring_prefix_cross_tier_static_selection_and_rate`: source
  W-set boundary-pair version combining static reasonableness, canonical
  selection consistency, and finite outcome-rate domination.
- `randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate`:
  actual-law version of that W-set boundary-pair theorem.
- `randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate`:
  one-sided static-boundary companion for randomized scoring: the
  convex-combination rule selects the W-set and its relevant static pairwise
  errors are eventually empty.
- `randomized_scoring_prefix_cross_tier_static_selection_and_zero_gap_static_aggregate`:
  one-sided zero-gap finite-real companion for randomized scoring: the
  convex-combination rule selects the W-set and its relevant static pairwise
  aggregate has exact finite rate.
- `randomized_scoring_prefix_cross_tier_static_selection_and_mixed_static_aggregate`:
  mixed finite/boundary companion for randomized scoring: the convex-combination
  rule selects the W-set and its relevant static pairwise aggregate has exact
  finite rate when the relevant pairs satisfy the Proposition 2 envelope.
- `randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_eventually_zero_static_aggregate`:
  finite-real/boundary split for the actual-law randomized scoring theorem.
- `randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_zero_gap_or_eventually_zero_static_aggregate`:
  actual-law randomized scoring trichotomy with finite-real comparison,
  zero-gap exact static aggregate, or strict eventually-empty boundary.
- `randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_mixed_static_aggregate_or_eventually_zero_static_aggregate`:
  actual-law randomized scoring wrapper with finite-real comparison, mixed
  finite/boundary exact static aggregate, or strict eventually-empty boundary.
- `randomized_approval_pairwise_rate_le_static_of_convexity`: finite static
  K-approval rule weakly beats a randomized K-approval rule once the paper's
  convexity bound is supplied.
- `randomized_approval_pairwise_rate_le_static`: direct positive-base
  K-approval no-randomization theorem.
- `randomized_approval_pairwise_rate_le_static_of_valid_probabilities_or_static_boundary`:
  source-shaped valid-probability K-approval no-randomization theorem, with
  degenerate static boundaries reported explicitly.
- `randomized_k_approval_pairwise_rate_le_static_or_static_boundary`:
  actual randomized K-approval fixed-pair theorem using the ranking-law
  up/down probability definitions.
- `randomized_k_approval_pairwise_rate_le_static`:
  actual randomized K-approval fixed-pair theorem on the positive-base region.
- `randomized_approval_pairwise_exact_rate_and_static_rate_ge_or_static_boundary_from_sampling_law`:
  actual randomized K-approval fixed-pair exact-rate theorem with the
  source no-randomization conclusion or an explicit static boundary branch.
- `randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary`:
  source-facing aggregate exact-rate and no-randomization wrapper with an
  explicit static boundary branch.
- `randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_component_witnesses_or_static_boundary`:
  aggregate exact-rate wrapper deriving mixed positivity from positive-weight
  component witnesses.
- `randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_component_positive_oriented_pivotal_pair_or_static_boundary`:
  aggregate exact-rate wrapper deriving the witness hypotheses from uniformly
  positive oriented static components.
- `mallows_w_selection_no_randomization_of_common_pivotal_pair`: outcome-level
  Mallows no-randomization bridge from a common pivotal-pair certificate.
- `mallows_w_selection_no_randomization_of_common_pivotal_pair_positive`:
  positive-base version using the proved K-approval Jensen theorem.
- `k_approval_outcome_no_randomization_from_common_pivotal_pair_positive`:
  finite outcome-rate version of the common-pivotal-pair no-randomization
  bridge.
- `k_approval_outcome_no_randomization_from_static_pivotal_pair_positive`:
  finite outcome-rate bridge requiring only static pivotality of the boundary
  pair.
- `k_approval_outcome_no_randomization_from_static_pivotal_pair_valid_probabilities_or_static_boundary`:
  static-pivotal outcome bridge over valid approval probabilities, with
  degenerate static boundaries reported explicitly.
- `randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_or_mixed_boundary`:
  actual ranking-law K-approval outcome-rate lift from a static pivotal pair.
- `randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary`:
  actual ranking-law K-approval outcome-rate lift over valid approval
  probabilities, with degenerate static boundaries reported explicitly.
- `mallows_k_approval_no_randomization_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows q<1 no-randomization endpoint for actual
  randomized finite families of nontrivial K-approval rules.
- `randomized_approval_w_selection_improves_from_two_static_minima`: finite
  min-rate certificate for the W-selection examples where randomization helps.
- `durham_ward1_randomized_approval_improves_static3_static4`: exact
  thousandth-probability version of the Durham Ward 1 empirical randomization
  improvement example.
- `randomized_approval_w_selection_constructed_design_invariant_example`:
  constructed finite W-selection example satisfying strict prefix dominance
  where randomized approval strictly improves on the two static rules.
- `mallows_high_noise_w3_k2_rate_gt_k3_rate`: high-noise `M = 4`, `W = 3`
  Mallows example showing W-approval need not be optimal from the closed
  model-derived pivotal-pair probability formulas.
- `mallows_high_noise_w3_k2_rate_gt_k3_rate_from_mallows_model`: end-to-end
  identity-centered Mallows version of that high-noise example.
- `mallows_high_noise_w3_k2_rate_gt_k3_rate_concrete_mallows`: concrete
  normalized identity-centered Mallows law at `q = 4/5`.
- `mallows_high_noise_w3_k2_pair23_exact_rate_certificate_concrete_mallows`:
  exact iid pairwise rate certificate for the concrete K=2 pivotal pair.
- `mallows_high_noise_w3_k1_pair23_exact_rate_certificate_concrete_mallows`:
  exact iid pairwise rate certificate for the concrete K=1 pivotal pair.
- `mallows_high_noise_w3_k3_pair23_exact_rate_certificate_concrete_mallows`:
  exact iid pairwise rate certificate for the concrete K=3 pivotal pair.
- `mallows_high_noise_w3_k2_outcome_rate_gt_k3_outcome_rate_concrete_mallows`:
  concrete finite W-selection outcome-rate version of the high-noise example.
- `mallows_high_noise_w3_k2_outcome_rate_gt_k1_outcome_rate_concrete_mallows`:
  concrete high-noise outcome-rate comparison against 1-approval.
- `mallows_high_noise_w3_k2_best_among_nontrivial_static_k_concrete_mallows`:
  concrete high-noise certificate that K=2 beats K=1 and K=3.
- `mallows_w3_k2_best_among_nontrivial_static_k_from_mallows_model_q_high_noise`:
  symbolic four-candidate Mallows certificate that K=2 beats K=1 and K=3
  under the explicit high-noise condition `1 < q^2 + q^3`.
- `mallows_high_noise_w3_all_static_probabilities_exact_rates_and_k2_best_from_mallows_model`:
  closed high-noise Mallows package deriving all nontrivial static approval
  pivotal-pair probabilities from the Mallows model, proving exact aggregate
  rates, and showing K=2 beats K=1 and K=3.
- `mallows_high_noise_w3_randomized_k_approval_no_improvement_concrete_mallows`:
  concrete high-noise no-randomization theorem for mixtures over K=1,2,3.
- `mallows_w3_static_k_pivotal_pair_from_mallows_model_q_lt_one`: symbolic
  four-candidate Mallows certificate that K=1,2,3 all have boundary pair
  `(3,4)` as a finite W-selection minimizer for any `0 < q < 1`.
- `mallows_top_w_one_approval_boundary_pair_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows certificate that one-approval has the
  adjacent W-selection boundary pair as a finite minimizer for any `0 < q < 1`.
- `mallows_top_w_k_approval_boundary_pair_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows certificate that every nontrivial
  K-approval rule has the adjacent W-selection boundary pair as a finite
  minimizer for any `0 < q < 1`.
- `mallows_top_w_k_approval_outcome_error_exact_rate_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows exact iid aggregate error-rate endpoint
  for every nontrivial K-approval rule, realized at the adjacent W-selection
  boundary pair.
- `mallows_top_w_randomized_k_approval_outcome_error_exact_rate_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows exact iid aggregate error-rate endpoint
  for randomized K-approval, realized at the adjacent W-selection boundary
  pair under the explicit randomized rule-sampling law.
- `mallows_one_loser_k_approval_pair_probabilities_from_mallows_model`:
  arbitrary finite-candidate Mallows all-but-one approval pair probabilities
  as last-rank Mallows weights divided by the partition.
- `mallows_top_two_k_approval_pair_probability_rank_sum_from_mallows_model`:
  arbitrary finite-candidate Mallows `K = 2` pair up-probability as a
  normalized rank-sum over ordered first/second fibers.
- `mallows_top_w_all_but_one_approval_boundary_pair_from_mallows_model_q_lt_one`:
  arbitrary finite-candidate Mallows certificate that all-but-one approval has
  the adjacent all-but-one W-selection boundary pair as a finite minimizer for
  any `0 < q < 1`.
- `mallows_w3_randomized_k_approval_no_improvement_from_mallows_model_q_lt_one`:
  symbolic four-candidate Mallows no-randomization theorem for mixtures over
  K=1,2,3 and any `0 < q < 1`.
- `mallows_k_approval_static_exact_rates_randomized_boundary_and_no_improvement_from_mallows_model_q_lt_one`:
  bundled arbitrary finite-candidate Mallows static exact-rate, randomized
  boundary, and no-randomization endpoint.
- `mallows_k_approval_static_and_randomized_exact_rates_boundary_and_no_improvement_from_mallows_model_q_lt_one`:
  bundled arbitrary finite-candidate Mallows static and randomized exact-rate,
  randomized boundary, and no-randomization endpoint.
- `mallows_high_noise_w3_k1_outcome_error_exact_rate_concrete_mallows`:
  concrete finite aggregate exact-rate theorem for 1-approval.
- `mallows_high_noise_w3_k2_outcome_error_exact_rate_concrete_mallows`:
  concrete finite aggregate exact-rate theorem for 2-approval.
- `mallows_high_noise_w3_k3_outcome_error_exact_rate_concrete_mallows`:
  concrete finite aggregate exact-rate theorem for 3-approval.
- `mallows_high_noise_w3_k1_outcome_error_tendsto_zero_concrete_mallows`:
  concrete finite aggregate convergence theorem for 1-approval.
- `mallows_high_noise_w3_k2_outcome_error_tendsto_zero_concrete_mallows`:
  concrete finite aggregate convergence theorem for 2-approval.
- `mallows_high_noise_w3_k3_outcome_error_tendsto_zero_concrete_mallows`:
  concrete finite aggregate convergence theorem for 3-approval.
- `mallows_high_noise_w3_k2_outcome_error_exact_rate_from_mallows_model`:
  model-parametric finite aggregate exact-rate theorem for 2-approval.
- `mallows_high_noise_w3_k3_outcome_error_exact_rate_from_mallows_model`:
  model-parametric finite aggregate exact-rate theorem for 3-approval.
- `mallows_high_noise_w3_k2_outcome_error_tendsto_zero_from_mallows_model`:
  model-parametric finite aggregate convergence theorem for 2-approval.
- `mallows_high_noise_w3_k3_outcome_error_tendsto_zero_from_mallows_model`:
  model-parametric finite aggregate convergence theorem for 3-approval.
- `mallows_high_noise_w3_k2_outcome_rate_gt_k3_outcome_rate_from_mallows_model`:
  model-parametric finite W-selection outcome-rate version.
- `mallows_high_noise_w3_pivotal_pair_min_rates_and_w_approval_not_optimal`:
  model-parametric package identifying the source pivotal pair/min-rates and
  deriving the W-approval-not-optimal outcome-rate comparison.
- `mallows_high_noise_w3_k2_probabilities_from_rank_factorization`: derives
  the `K = 2` pair probabilities used by that example from the reusable
  canonical Mallows rank-factorization theorem.
- `mallows_high_noise_w3_probabilities_from_rank_factorizations`: derives the
  `K = 2` and `K = 3` pair probabilities used by that example from the
  canonical first/top-two rank-factorization theorem and the reusable raw
  Mallows first-tail theorem under position reversal.
-/

namespace GGSG19TopThree

open AppliedModelingLib.SocialChoice.Ranking

noncomputable section

open AppliedModelingLib.Probability

/-- Definition, Section 3.1: `r = -lim (1 / N) log A_N`. -/
abbrev definition_large_deviation_rate (A : ℕ → ℝ) (r : ℝ) : Prop :=
  largeDeviationRate A r

/--
Proposition 1 finite algebra core: a higher-tier candidate strictly dominates a
lower-tier candidate at every top-prefix probability iff every reasonable
nonconstant nonincreasing positional score vector separates their asymptotic
expected scores.
-/
theorem proposition1_design_invariance_prefix_score_core
    {Cut Candidate : Type*} [Fintype Cut] [DecidableEq Cut]
    (topPrefixProb : Candidate → Cut → ℝ) (hi lo : Candidate) :
    StrictTopPrefixDominance topPrefixProb hi lo ↔
      AllReasonablePrefixScoresSeparate topPrefixProb hi lo :=
  strictTopPrefixDominance_iff_allReasonablePrefixScoresSeparate
    topPrefixProb hi lo

/--
Proposition 1 finite tierwise algebra core: strict top-prefix dominance over
all required higher-tier/lower-tier pairs iff every reasonable positional score
rule separates all such pairs in expected score.
-/
theorem proposition1_design_invariance_tierwise_prefix_score_core
    {Cut Candidate : Type*} [Fintype Cut] [DecidableEq Cut]
    (topPrefixProb : Candidate → Cut → ℝ)
    (crossTier : Candidate → Candidate → Prop) :
    StrictTopPrefixDominanceOn topPrefixProb crossTier ↔
      AllReasonablePrefixScoresSeparateOn topPrefixProb crossTier :=
  strictTopPrefixDominanceOn_iff_allReasonablePrefixScoresSeparateOn
    topPrefixProb crossTier

/--
Scoring-rule randomization algebra: a finite mixture of reasonable
nonconstant nonincreasing prefix-weight vectors is again a reasonable
prefix-weight vector, so the convex-combination scoring rule stays in the
paper's admissible design class.
-/
theorem randomized_scoring_reasonable_prefix_weights_weighted_sum
    {Rule Cut : Type*} [Fintype Rule]
    (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule)) :
    ReasonablePrefixWeights
      (fun cut => ∑ rule : Rule, weight rule * diff rule cut) :=
  ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff

/--
Scoring-rule randomization algebra: one-voter prefix-score contributions are
linear in the adjacent prefix-weight vector.  This identifies the paper's
static convex-combination score with the weighted sum of component scores.
-/
theorem randomized_scoring_prefix_score_from_event_weighted_sum
    {Rule Cut Candidate Signal : Type*} [Fintype Rule] [Fintype Cut]
    (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) (signal : Signal) :
    prefixScoreFromEvent
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
        inPrefix candidate signal =
      ∑ rule : Rule,
        weight rule *
          prefixScoreFromEvent (diff rule) inPrefix candidate signal :=
  prefixScoreFromEvent_weighted_sum
    weight diff inPrefix candidate signal

/--
Proposition 1 stochastic-law bridge: if top-prefix probabilities are induced
by a finite one-voter law and prefix event, then the expected one-voter
prefix-score contribution is exactly the finite prefix-score expression used by
the design-invariance algebra core.
-/
theorem proposition1_induced_prefix_expected_score_bridge
    {Cut Candidate Signal : Type*} [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) :
    AppliedModelingLib.pmfExp law
        (prefixScoreFromEvent diff inPrefix candidate) =
      prefixExpectedScore diff
        (prefixProbFromEvent law inPrefix) candidate :=
  pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore
    law diff inPrefix candidate

/--
Proposition 1 stochastic-law gap bridge: strict top-prefix dominance in the
finite one-voter law implies every reasonable prefix score has positive
expected one-voter score gap.
-/
theorem proposition1_induced_prefix_expected_gap_positive
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    0 <
      AppliedModelingLib.pmfExp law
        (fun signal =>
          prefixScoreFromEvent diff inPrefix hi signal -
            prefixScoreFromEvent diff inPrefix lo signal) :=
  pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
    law diff inPrefix hdom hdiff

/--
Proposition 1 stochastic separation bridge: strict prefix dominance plus a
reasonable prefix-score rule gives a strictly positive exponential upper-bound
rate for the iid pairwise score error.
-/
theorem proposition1_induced_prefix_pairwise_error_positive_exponential_decay
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law
            (prefixScoreFromEvent diff inPrefix hi)
            (prefixScoreFromEvent diff inPrefix lo)) rate :=
  prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst
    law diff inPrefix hdom hdiff

/--
Proposition 1 tierwise stochastic separation bridge: every required
higher/lower pair gets a strictly positive exponential upper-bound rate.
-/
theorem proposition1_induced_prefix_pairwise_error_positive_exponential_decay_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (crossTier : Candidate → Candidate → Prop)
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix) crossTier)
    (hdiff : ReasonablePrefixWeights diff) :
    ∀ hi lo, crossTier hi lo →
      ∃ rate : ℝ,
        0 < rate ∧
          HasExpUpperBoundWithConst
            (pairwiseScoringErrorProb law
              (prefixScoreFromEvent diff inPrefix hi)
              (prefixScoreFromEvent diff inPrefix lo)) rate :=
  prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst_on
    law diff inPrefix crossTier hdom hdiff

/--
Proposition 1 asymptotic conclusion: strict prefix dominance plus a reasonable
prefix-score rule makes the induced iid pairwise score error probability tend
to zero.
-/
theorem proposition1_induced_prefix_pairwise_error_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (prefixScoreFromEvent diff inPrefix hi)
        (prefixScoreFromEvent diff inPrefix lo))
      Filter.atTop (nhds 0) :=
  prefixScoringPairwiseError_tendsto_zero
    law diff inPrefix hdom hdiff

/--
Proposition 1 tierwise asymptotic conclusion: every required higher/lower
pair has induced iid prefix-score error probability tending to zero.
-/
theorem proposition1_induced_prefix_pairwise_error_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (crossTier : Candidate → Candidate → Prop)
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix) crossTier)
    (hdiff : ReasonablePrefixWeights diff) :
    ∀ hi lo, crossTier hi lo →
      Filter.Tendsto
        (pairwiseScoringErrorProb law
          (prefixScoreFromEvent diff inPrefix hi)
          (prefixScoreFromEvent diff inPrefix lo))
        Filter.atTop (nhds 0) :=
  prefixScoringPairwiseError_tendsto_zero_on
    law diff inPrefix crossTier hdom hdiff

/--
Proposition 1 finite-outcome stochastic bridge: strict prefix dominance for
every indexed relevant pair gives a positive exponential upper-bound rate for
the weighted sum of all indexed iid prefix-score pairwise errors.
-/
theorem proposition1_induced_prefix_relevant_pair_aggregate_positive_exponential_decay
    {Cut Pair Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Pair] [Nonempty Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hdom :
      ∀ pair,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          (hi pair) (lo pair))
    (hdiff : ReasonablePrefixWeights diff) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n =>
            ∑ pair : Pair,
              pairWeight pair *
                pairwiseScoringErrorProb law
                  (prefixScoreFromEvent diff inPrefix (hi pair))
                  (prefixScoreFromEvent diff inPrefix (lo pair)) n)
          targetRate :=
  prefixScoringRelevantPairAggregateError_exists_pos_expUpperBoundWithConst
    law diff inPrefix hi lo hweight hdom hdiff

/--
Proposition 1 finite-outcome asymptotic conclusion: strict prefix dominance
for every indexed relevant pair makes the finite weighted aggregate of iid
prefix-score pairwise errors tend to zero.
-/
theorem proposition1_induced_prefix_relevant_pair_aggregate_tendsto_zero
    {Cut Pair Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Pair] [Nonempty Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hdom :
      ∀ pair,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          (hi pair) (lo pair))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (fun n =>
        ∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (prefixScoreFromEvent diff inPrefix (hi pair))
              (prefixScoreFromEvent diff inPrefix (lo pair)) n)
      Filter.atTop (nhds 0) :=
  prefixScoringRelevantPairAggregateError_tendsto_zero
    law diff inPrefix hi lo hweight hdom hdiff

/--
Proposition 1 source-level selection conclusion: if strict prefix dominance
holds for every true-winner/true-loser pair, then any rule that selects a
score-top W-set of the correct size has vanishing probability of selecting the
wrong W-set.
-/
theorem proposition1_induced_prefix_selection_error_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hdom :
      ∀ pair : CrossTierPair winnerSet,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          pair.hi pair.lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 0) :=
  prefixScoringSelectionError_tendsto_zero
    law diff inPrefix winnerSet selected hcard htop hdom hdiff

/--
Proposition 1 canonical source-level selection conclusion: if strict prefix
dominance holds for every true-winner/true-loser pair, then the natural
score-top W-set chosen by finite maximization has vanishing probability of
selecting the wrong W-set.
-/
theorem proposition1_induced_prefix_canonical_selection_error_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ pair : CrossTierPair winnerSet,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          pair.hi pair.lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  prefixScoringCanonicalSelectionError_tendsto_zero
    law diff inPrefix winnerSet hdom hdiff

/--
Proposition 1 source-level selection conclusion, source-shaped version: strict
top-prefix dominance over the W-set's natural cross-tier predicate implies that
the probability of selecting a wrong W-set tends to zero.
-/
theorem proposition1_induced_prefix_selection_error_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 0) :=
  prefixScoringSelectionError_tendsto_zero_on
    law diff inPrefix winnerSet selected hcard htop hdom hdiff

/--
Proposition 1 canonical source-level selection conclusion: strict top-prefix
dominance over the W-set's natural cross-tier predicate implies that the
internally chosen score-top W-set has vanishing probability of selecting the
wrong W-set.  The selected set and its cardinality/topness witnesses are
constructed by finite score maximization.
-/
theorem proposition1_induced_prefix_canonical_selection_error_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  prefixScoringCanonicalSelectionError_tendsto_zero_on
    law diff inPrefix winnerSet hdom hdiff

/--
Proposition 1 strict converse fragment: if a true loser has strictly larger
induced expected prefix score than a true winner under the displayed prefix
score vector, then any score-top W-selector is asymptotically wrong.  This is
the strict reverse case; source-level exact cross-tier equality is outside
Proposition 1's strict target-ranking/tier condition.
-/
theorem proposition1_induced_prefix_selection_error_tendsto_one_of_reverse_prefix_expected_score
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 1) :=
  prefixScoringSelectionError_tendsto_one_of_reverse_prefix_expected_score
    law diff inPrefix winnerSet selected hhi hlo htop hreverse

/--
Canonical version of the Proposition 1 strict reverse expected-score fragment.
-/
theorem proposition1_induced_prefix_canonical_selection_error_tendsto_one_of_reverse_prefix_expected_score
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 1) :=
  prefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
    law diff inPrefix winnerSet hhi hlo hreverse

/--
Necessary weak expected-score separation for the source prefix-score surface:
if every reasonable prefix score's canonical W-selection error tends to zero,
then every true winner weakly beats every true loser in one-voter expected
score for every reasonable prefix-score vector.
-/
theorem proposition1_induced_prefix_all_reasonable_consistency_implies_weak_expected_score_separation
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (hall :
      ∀ diff : Cut → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              winnerSet
              (fun n sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore
                    (fun candidate =>
                      prefixScoreFromEvent diff inPrefix candidate)
                    sample)
                  winnerSet))
            Filter.atTop (nhds 0)) :
    ∀ diff : Cut → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : Candidate,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo ≤
                prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi :=
  prefixScoringAllReasonableConsistency_implies_weak_expected_score_separation
    law inPrefix winnerSet hall

/--
Proposition 1 ADI-shaped forward conclusion over the formal admissible class:
strict top-prefix dominance over the W-set's natural cross-tier predicate makes
the canonical score-top W-set converge to the same outcome for every reasonable
prefix-score rule.
-/
theorem proposition1_strict_prefix_dominance_implies_all_reasonable_prefix_score_consistency
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ∀ diff : Cut → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            winnerSet
            (fun n sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore
                  (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
                  sample)
                winnerSet))
          Filter.atTop (nhds 0) := by
  intro diff hdiff
  exact
    proposition1_induced_prefix_canonical_selection_error_tendsto_zero_on
      law diff inPrefix winnerSet hdom hdiff

/--
Proposition 1 ranking-law W-selection conclusion: if every true winner has
strictly larger top-prefix probability than every true loser at every prefix
cut, then the canonical score-top W-set is asymptotically correct for the
given reasonable ranking-prefix score rule.
-/
theorem proposition1_ranking_law_canonical_selection_error_tendsto_zero
    {n : ℕ}
    (law : PMF (Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ hi lo : Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  rankingPrefixScoringCanonicalSelectionError_tendsto_zero_on
    law diff winnerSet hdom hdiff

/--
Proposition 1 ranking-law W-selection conclusion for any deterministic
score-top selected W-set of the correct size.
-/
theorem proposition1_ranking_law_selection_error_tendsto_zero
    {n : ℕ}
    (law : PMF (Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (Candidate n))
    (selected :
      (voters : ℕ) → (Fin voters → Ranking n) → Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ voters sample, (selected voters sample).card = winnerSet.card)
    (htop :
      ∀ voters sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore (rankingPrefixScore diff) sample)
          (selected voters sample))
    (hdom :
      ∀ hi lo : Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet selected)
      Filter.atTop (nhds 0) :=
  rankingPrefixScoringSelectionError_tendsto_zero_on
    law diff winnerSet selected hcard htop hdom hdiff

/--
Proposition 1 ranking-law strict converse fragment: if a lower candidate has
strictly larger expected score than a true winner for a displayed ranking-prefix
score vector, the canonical score-top W-selector fails with probability
tending to one.  This covers the strict reverse case, not tie boundaries.
-/
theorem proposition1_ranking_law_canonical_selection_error_tendsto_one_of_reverse_prefix_expected_score
    {n : ℕ}
    (law : PMF (Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (Candidate n))
    {hi lo : Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (hreverse :
      prefixExpectedScore diff (rankingTopPrefixProb law) hi <
        prefixExpectedScore diff (rankingTopPrefixProb law) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            winnerSet))
      Filter.atTop (nhds 1) :=
  rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
    law diff winnerSet hhi hlo hreverse

/--
Proposition 1 ranking-law strict converse fragment for a single reversed
top-prefix probability.  The score rule is the indicator for that prefix cut,
which is a reasonable prefix-weight vector.
-/
theorem proposition1_ranking_law_canonical_selection_error_tendsto_one_of_reverse_top_prefix_prob
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    {hi lo : Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore
          (fun k : RankingProperPrefixCut n =>
            if k = cut then (1 : ℝ) else 0))
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (rankingPrefixScore
                (fun k : RankingProperPrefixCut n =>
                  if k = cut then (1 : ℝ) else 0))
              sample)
            winnerSet))
      Filter.atTop (nhds 1) :=
  rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_top_prefix_prob
    law winnerSet hhi hlo hreverse

/--
Direct non-consistency form of the strict reversed-top-prefix fragment: the
canonical score-top W-selection error for the corresponding indicator prefix
score cannot converge to zero.
-/
theorem proposition1_ranking_law_canonical_selection_error_not_tendsto_zero_of_reverse_top_prefix_prob
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    {hi lo : Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ¬ Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore
          (fun k : RankingProperPrefixCut n =>
            if k = cut then (1 : ℝ) else 0))
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (rankingPrefixScore
                (fun k : RankingProperPrefixCut n =>
                  if k = cut then (1 : ℝ) else 0))
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  rankingPrefixScoringCanonicalSelectionError_not_tendsto_zero_of_reverse_top_prefix_prob
    law winnerSet hhi hlo hreverse

/--
Bundled strict converse witness for Proposition 1: a reversed top-prefix
probability gives a reasonable indicator prefix score whose canonical
W-selection error cannot converge to zero.
-/
theorem proposition1_ranking_law_reverse_top_prefix_prob_witnesses_reasonable_nonconsistency
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    {hi lo : Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ReasonablePrefixWeights
        (fun k : RankingProperPrefixCut n =>
          if k = cut then (1 : ℝ) else 0) ∧
      ¬ Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (rankingPrefixScore
            (fun k : RankingProperPrefixCut n =>
              if k = cut then (1 : ℝ) else 0))
          winnerSet
          (fun voters sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (rankingPrefixScore
                  (fun k : RankingProperPrefixCut n =>
                    if k = cut then (1 : ℝ) else 0))
                sample)
              winnerSet))
        Filter.atTop (nhds 0) :=
  rankingPrefixScoringCanonicalSelectionError_indicator_reasonable_and_not_tendsto_zero_of_reverse_top_prefix_prob
    law winnerSet hhi hlo hreverse

/--
All-reasonable-score form of the strict Proposition 1 converse fragment: if a
lower candidate has strictly larger probability at one top-prefix cut than a
true winner, then it is not the case that every reasonable ranking-prefix score
has vanishing canonical W-selection error.
-/
theorem proposition1_ranking_law_reverse_top_prefix_prob_refutes_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    {hi lo : Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ¬ (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0)) :=
  rankingStrictReverseTopPrefixProb_not_all_reasonable_prefix_score_consistency
    law winnerSet hhi hlo hreverse

/--
Necessary weak-dominance fragment for Proposition 1: if every reasonable
ranking-prefix score has vanishing canonical W-selection error, then every
true winner weakly dominates every true loser at every top-prefix probability.
The source proposition states strict cross-tier top-prefix dominance; this
weak statement is only the reusable Lean converse fragment used before
applying the source-aligned no-cross-tier-equality bridge.
-/
theorem proposition1_ranking_law_all_reasonable_prefix_score_consistency_implies_weak_top_prefix_dominance
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    (hall :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) :
    ∀ hi lo : Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut ≤
              rankingTopPrefixProb law hi cut :=
  rankingAllReasonablePrefixScoreConsistency_implies_weak_top_prefix_dominance
    law winnerSet hall

/--
Paper-shaped Proposition 1 sandwich currently closed in Lean: the source's
strict cross-tier top-prefix condition implies all-reasonable-score
consistency, and all-reasonable-score consistency implies weak top-prefix
dominance. Exact cross-tier equality is outside the source strict condition;
finite-sample random tie-breaking and within-tier ties are separate from this
strict target-ranking/tier hypothesis.
-/
theorem proposition1_ranking_law_prefix_score_consistency_strict_forward_weak_necessary
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)] :
    ((∀ hi lo : Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) →
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) ∧
      ((∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) →
        ∀ hi lo : Candidate n,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≤
                  rankingTopPrefixProb law hi cut) :=
  rankingPrefixScoreConsistency_strict_forward_weak_necessary law winnerSet

/--
Proposition 1 ranking-law W-selection iff in the source's strict cross-tier
case: under the no-cross-tier-equality hypothesis corresponding to the paper's
strict top-prefix condition, source strict dominance is equivalent to
vanishing canonical W-selection error for every reasonable ranking-prefix
score rule.
-/
theorem proposition1_ranking_law_strict_prefix_dominance_iff_all_reasonable_prefix_score_consistency_of_no_cross_tier_prefix_ties
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hNoTie :
      ∀ hi lo : Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut ≠
                rankingTopPrefixProb law hi cut) :
    (∀ hi lo : Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) :=
  rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_consistency_of_no_cross_tier_prefix_ties
    law winnerSet hNoTie

/--
Proposition 1 ranking-law tiered-goal iff in the source's strict cross-tier
case: under the no-cross-tier-equality hypothesis corresponding to the paper's
strict top-prefix condition on every cumulative target-prefix boundary, source
strict dominance is equivalent to vanishing canonical tier-prefix error for
every reasonable ranking-prefix score rule.
-/
theorem proposition1_ranking_law_tiered_strict_prefix_dominance_iff_all_reasonable_tiered_prefix_score_consistency_of_no_cross_tier_prefix_ties
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hNoTie :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≠
                  rankingTopPrefixProb law hi cut) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopTieredPrefixSelectionErrorProb law
              (rankingPrefixScore diff)
              targetPrefix
              (fun stage voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  (targetPrefix stage)))
            Filter.atTop (nhds 0)) :=
  rankingTieredStrictPrefixDominance_iff_all_reasonable_tiered_prefix_score_consistency_of_no_cross_tier_prefix_ties
    law targetPrefix hnonempty hNoTie

/--
Proposition 1 finite ranking-law W-selection iff: strict top-prefix dominance
over every true-winner/true-loser pair is equivalent to separation by every
reasonable ranking-prefix score rule.
-/
theorem proposition1_ranking_law_strict_prefix_dominance_iff_all_reasonable_prefix_score_separation
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n)) :
    (∀ hi lo : Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
    (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : Candidate n,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                prefixExpectedScore diff (rankingTopPrefixProb law) hi) :=
  rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
    law winnerSet

/--
Proposition 1 finite ranking-law tiered-goal iff: strict top-prefix dominance
across every cumulative target prefix is equivalent to separation across every
cumulative target prefix by every reasonable ranking-prefix score rule.
-/
theorem proposition1_ranking_law_tiered_strict_prefix_dominance_iff_all_reasonable_prefix_score_separation
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
    (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        ∀ stage : Fin Stage,
          ∀ hi lo : Candidate n,
            hi ∈ targetPrefix stage →
              lo ∉ targetPrefix stage →
                prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                  prefixExpectedScore diff (rankingTopPrefixProb law) hi) :=
  rankingTieredStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
    law targetPrefix

/--
Proposition 1 ranking-law W-selection forward direction over all reasonable
ranking-prefix scoring rules.
-/
theorem proposition1_ranking_law_strict_prefix_dominance_implies_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ hi lo : Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0) :=
  rankingStrictPrefixDominance_implies_all_reasonable_prefix_score_consistency
    law winnerSet hdom

/--
Proposition 1 ranking-law W-selection forward direction from the equivalent
expected-score separation condition over all reasonable ranking-prefix scoring
rules.
-/
theorem proposition1_ranking_law_prefix_score_separation_implies_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (Ranking n))
    (winnerSet : Finset (Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hsep :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          ∀ hi lo : Candidate n,
            hi ∈ winnerSet →
              lo ∉ winnerSet →
                prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                  prefixExpectedScore diff (rankingTopPrefixProb law) hi) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0) :=
  rankingPrefixScoreSeparation_implies_all_reasonable_prefix_score_consistency
    law winnerSet hsep

/--
Proposition 1 ranking-law tiered-goal forward bridge: when a finite tiered goal
is represented by cumulative true tier-prefix sets, strict top-prefix
dominance across every cumulative prefix makes all prefixes asymptotically
correct under the canonical score-top selections.
-/
theorem proposition1_ranking_law_tiered_prefix_selection_error_tendsto_zero
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hdom :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut <
                  rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopTieredPrefixSelectionErrorProb law
        (rankingPrefixScore diff)
        targetPrefix
        (fun stage voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            (targetPrefix stage)))
      Filter.atTop (nhds 0) :=
  rankingPrefixScoringCanonicalTieredPrefixSelectionError_tendsto_zero
    law diff targetPrefix hnonempty hdom hdiff

/--
Proposition 1 ranking-law tiered-goal forward bridge from the equivalent
expected-score separation condition over all reasonable ranking-prefix scoring
rules.
-/
theorem proposition1_ranking_law_prefix_score_separation_implies_all_reasonable_tiered_prefix_score_consistency
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hsep :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          ∀ stage : Fin Stage,
            ∀ hi lo : Candidate n,
              hi ∈ targetPrefix stage →
                lo ∉ targetPrefix stage →
                  prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                    prefixExpectedScore diff (rankingTopPrefixProb law) hi) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopTieredPrefixSelectionErrorProb law
            (rankingPrefixScore diff)
            targetPrefix
            (fun stage voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                (targetPrefix stage)))
          Filter.atTop (nhds 0) :=
  rankingPrefixScoreSeparation_implies_all_reasonable_tiered_prefix_score_consistency
    law targetPrefix hnonempty hsep

/-- Proposition 2 formula for the pairwise positional-scoring learning rate. -/
theorem proposition2_pairwise_rate_formula
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) :
    pairwiseScoringRate law hiScore loScore =
      -sInf (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z) :=
  pairwiseScoringRate_eq_source_formula law hiScore loScore

/--
Proposition 2 rate-identity helper: an attained global finite log-MGF minimum
identifies the source pairwise Chernoff rate with `-log base`.
-/
theorem proposition2_pairwise_rate_eq_neg_log_base_from_log_mgf_global_min
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_logMGF_global_min
    law hiScore loScore hmin hwitness

/--
Proposition 2 rate-identity helper in first-order form: convexity plus a zero
derivative at the displayed dual parameter certifies the attained log-MGF
minimum.
-/
theorem proposition2_pairwise_rate_eq_neg_log_base_from_convex_log_mgf_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_convex_logMGF_deriv_zero
    law hiScore loScore hconv hderiv hwitness

/--
Proposition 2 rate-identity helper in stationary-equation form: convexity plus
the explicit weighted exponential score equation certifies the attained
log-MGF minimum.
-/
theorem proposition2_pairwise_rate_eq_neg_log_base_from_convex_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_convex_stationary
    law hiScore loScore hconv hstationary hwitness

/--
Proposition 2 rate-identity helper in first-order form.  For finite support,
log-MGF convexity is proved in the shared library, so the caller only supplies
the zero-derivative and attained-value checks.
-/
theorem proposition2_pairwise_rate_eq_neg_log_base_from_log_mgf_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_logMGF_deriv_zero
    law hiScore loScore hderiv hwitness

/--
Proposition 2 rate-identity helper in stationary-equation form.  For finite
support, log-MGF convexity is discharged internally.
-/
theorem proposition2_pairwise_rate_eq_neg_log_base_from_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_stationary
    law hiScore loScore hstationary hwitness

/--
Proposition 2 Chernoff upper bound: a nonpositive dual parameter gives an
exponential upper bound for the iid finite score-gap mistake probability.
-/
theorem proposition2_pairwise_chernoff_upper_bound
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z : ℝ}
    (hz : z ≤ 0) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      (-(finiteLogMGF law (fun signal => hiScore signal - loScore signal) z)) :=
  pairwiseScoringError_hasExpUpperBoundWithConst_of_dual
    law hiScore loScore hz

/--
Proposition 2 Chernoff upper-bound target-rate form: an explicit nonpositive
dual parameter whose negative log-MGF is at least the requested rate gives an
iid exponential upper bound at that rate.
-/
theorem proposition2_pairwise_chernoff_upper_bound_of_nonpos_dual_rate_le
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      rate ≤
        -(finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z)) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore) rate :=
  pairwiseScoringError_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
    law hiScore loScore hz hrate

/--
Proposition 2 finite-`N` Chernoff upper bound: the same nonpositive dual
certifies a pointwise bound `Pr(error at n) <= exp (-n * rate)`.
-/
theorem proposition2_pairwise_chernoff_pointwise_upper_bound_of_nonpos_dual_rate_le
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      rate ≤
        -(finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z))
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * rate) :=
  pairwiseScoringErrorProb_le_exp_of_nonpos_dual_rate_le
    law hiScore loScore hz hrate n

/--
Proposition 2 finite-`N` Chernoff upper bound at the exact displayed source
rate, from a supplied stationary nonpositive Chernoff dual.
-/
theorem proposition2_pairwise_chernoff_pointwise_upper_bound_at_rate_of_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z : ℝ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_stationary
    law hiScore loScore hz hstationary n

/--
Proposition 2 finite-`N` Chernoff upper bound at the exact displayed source
rate, with the stationary nonpositive dual found from finite support,
nonnegative mean, and positive/negative score-gap atoms.
-/
theorem proposition2_pairwise_chernoff_pointwise_upper_bound_at_rate_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg n

/--
Proposition 2 positive-gap Chernoff consequence: if the one-voter score gap has
positive expectation, then the iid pairwise mistake probability has some
strictly positive exponential upper-bound rate.
-/
theorem proposition2_pairwise_positive_expected_gap_chernoff_upper_bound_exists
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 <
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) rate :=
  pairwiseScoringError_exists_pos_expUpperBoundWithConst_of_expected_gap_pos
    law hiScore loScore hmean

/--
Proposition 2 positive-gap Chernoff dual existence: if the one-voter score gap
has positive expectation, there is a nonpositive dual parameter with positive
dual rate that certifies an iid pairwise mistake upper bound.
-/
theorem proposition2_pairwise_positive_expected_gap_chernoff_dual_exists
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 <
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ z : ℝ,
      z ≤ 0 ∧
        0 <
          -(finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z) ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore)
          (-(finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)) :=
  pairwiseScoringError_exists_nonpos_dual_positive_rate
    law hiScore loScore hmean

/--
Proposition 2 one-sided exact finite-real boundary case: if every positive-mass
one-voter score gap is nonnegative and the zero-gap event has probability
`pZero > 0`, then pairwise mistakes occur exactly when every sampled voter has
zero gap, giving exact rate `-log pZero`.
-/
theorem proposition2_pairwise_exact_rate_from_support_nonneg_zero_gap_prob
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 ≤ hiScore signal - loScore signal)
    {pZero : ℝ}
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero)
    (hZero_pos : 0 < pZero) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (-Real.log pZero) :=
  pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
    law hiScore loScore hsupport hZeroProb hZero_pos

/--
Proposition 2 one-sided strict-support boundary case: if every positive-mass
one-voter score gap is strictly positive, then the finite iid pairwise mistake
event is eventually empty.
-/
theorem proposition2_pairwise_eventually_zero_from_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal) :
    ∀ᶠ n in Filter.atTop,
      pairwiseScoringErrorProb law hiScore loScore n = 0 :=
  pairwiseScoringError_eventually_zero_of_support_pos
    law hiScore loScore hsupport

/--
Proposition 2 one-sided strict-support upper-bound case: if every positive-mass
one-voter score gap is strictly positive, then the pairwise mistake probability
has an eventual exponential upper bound at any finite target rate.
-/
theorem proposition2_pairwise_upper_bound_from_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      targetRate :=
  pairwiseScoringError_hasExpUpperBoundWithConst_of_support_pos
    law hiScore loScore hsupport targetRate

/--
Proposition 2 exact pairwise rate: reusable finite-support Cramer upper/lower
bounds around the log-MGF formula produce the exact iid score-gap exponential
rate.
-/
theorem proposition2_pairwise_exact_rate_from_finite_iid_cramer
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (C : FiniteIidScoreGapCramerCertificate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore C

/--
Proposition 2 exact pairwise rate from an explicit finite left-tail lower
certificate: once the Chernoff upper-bound side is available at every slower
rate and a concrete path/type lower bound realizes the same geometric base,
the paper's source pairwise rate formula is the exact iid exponential rate.
-/
theorem proposition2_pairwise_exact_rate_from_path_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower
    law hiScore loScore hupper C hrate

/--
Proposition 2 exact pairwise rate from a concrete lower-tail path/type lower
certificate, with the Chernoff upper side discharged by nonnegative expected
score gap and bounded-below finite log-MGF range.
-/
theorem proposition2_pairwise_exact_rate_from_path_lower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C hrate

/--
Proposition 2 exact pairwise rate from a concrete lower-tail path/type lower
certificate, with the Chernoff upper side discharged by nonnegative expected
score gap and concrete positive-mass atoms on both sides of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_path_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Proposition 2 exact pairwise rate from a direct finite left-tail probability
lower certificate: once the Chernoff upper-bound side is available at every
slower rate and the lower bound realizes the same geometric base, the paper's
source pairwise rate formula is the exact iid exponential rate.
-/
theorem proposition2_pairwise_exact_rate_from_tail_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tailLower
    law hiScore loScore hupper C hrate

/--
Proposition 2 exact pairwise rate from a bounded left-tail window under an
exponential tilt.  This is the change-of-measure route for finite-support
Cramer lower bounds; the remaining paper-specific input is the tilted-window
mass lower bound and the rate-identification equality for the chosen tilt.
-/
theorem proposition2_pairwise_exact_rate_from_tilted_window
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          AppliedModelingLib.pmfProb
            (AppliedModelingLib.pmfProduct (Fin n) Signal
              (finiteExponentialTilt law
                (fun signal => hiScore signal - loScore signal) z))
            (fun sample : Fin n → Signal =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ∧
                finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ≤ 0))
    (hrate :
      -Real.log
          (finiteMGF law
            (fun signal => hiScore signal - loScore signal) z) =
        pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tiltedWindow
    law hiScore loScore hupper hz hlowerConst_pos hwindow hrate

/--
Proposition 2 exact pairwise rate from a stationary exponential tilt and a
bounded tilted-window lower bound.  The finite log-MGF convexity theorem
identifies the stationary tilt with the source Chernoff exponent.
-/
theorem proposition2_pairwise_exact_rate_from_stationary_tilted_window
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          AppliedModelingLib.pmfProb
            (AppliedModelingLib.pmfProduct (Fin n) Signal
              (finiteExponentialTilt law
                (fun signal => hiScore signal - loScore signal) z))
            (fun sample : Fin n → Signal =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ∧
                finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ≤ 0)) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_stationaryTiltedWindow
    law hiScore loScore hmean
    hmassPos hgapPos hmassNeg hgapNeg
    hz hstationary hlowerConst_pos hwindow

/--
Proposition 2 exact pairwise rate from a direct finite left-tail probability
lower certificate, with the Chernoff upper side discharged by nonnegative
expected score gap and bounded-below finite log-MGF range.
-/
theorem proposition2_pairwise_exact_rate_from_tail_lower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tailLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C hrate

/--
Proposition 2 exact pairwise rate from a direct finite left-tail probability
lower certificate, with the Chernoff upper side discharged by nonnegative
expected score gap and concrete positive-mass atoms on both sides of the score
gap.
-/
theorem proposition2_pairwise_exact_rate_from_tail_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tailLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
bucket/type lower certificate: once the Chernoff upper-bound side is available
at every slower rate and the bucket lower bound realizes the same geometric
base, the paper's source pairwise rate formula is the exact iid exponential
rate.
-/
theorem proposition2_pairwise_exact_rate_from_bucket_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_bucketLower
    law hiScore loScore hupper C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
bucket/type lower certificate, with the Chernoff upper side discharged by
nonnegative expected score gap and bounded-below finite log-MGF range.
-/
theorem proposition2_pairwise_exact_rate_from_bucket_lower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_bucketLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
bucket/type lower certificate, with the Chernoff upper side discharged by
nonnegative expected score gap and concrete positive-mass atoms on both sides
of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_bucket_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_bucketLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
count-vector lower certificate: once the Chernoff upper-bound side is available
at every slower rate and the count-vector lower bound realizes the same
geometric base, the paper's source pairwise rate formula is the exact iid
exponential rate.
-/
theorem proposition2_pairwise_exact_rate_from_count_vector_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_countVectorLower
    law hiScore loScore hupper C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
count-vector lower certificate, with the Chernoff upper side discharged by
nonnegative expected score gap and bounded-below finite log-MGF range.
-/
theorem proposition2_pairwise_exact_rate_from_count_vector_lower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_countVectorLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C hrate

/--
Proposition 2 exact pairwise rate from an explicit finite empirical
count-vector lower certificate, with the Chernoff upper side discharged by
nonnegative expected score gap and concrete positive-mass atoms on both sides
of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_count_vector_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_countVectorLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Proposition 2 exact pairwise rate from an exact finite empirical-type lower
certificate: once the Chernoff upper-bound side is available at every slower
rate and the multinomial type-mass lower bound realizes the same geometric
base, the paper's source pairwise rate formula is the exact iid exponential
rate.
-/
theorem proposition2_pairwise_exact_rate_from_empirical_type_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower
    law hiScore loScore hupper C hrate

/--
Proposition 2 exact pairwise rate from an exact finite empirical-type lower
certificate, with the Chernoff upper side discharged by nonnegative expected
score gap and bounded-below finite log-MGF range.
-/
theorem proposition2_pairwise_exact_rate_from_empirical_type_lower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C hrate

/--
Proposition 2 exact pairwise rate from an exact finite empirical-type lower
certificate, with the Chernoff upper side discharged by nonnegative expected
score gap and concrete positive-mass atoms on both sides of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_empirical_type_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Proposition 2 helper: build the empirical count-vector lower certificate from
a periodic finite type.  The period count vector must sum to `Q`, lie in the
pairwise left tail, and have product mass at least `base ^ Q`; residue samples
are assigned to a tail-safe positive-mass filler signal.
-/
def proposition2_pairwise_periodic_count_vector_lower_certificate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore :=
  pairwiseScoringError_periodicCountVectorLowerCertificate
    law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos

/--
Proposition 2 helper: build the entropy-aware empirical-type lower certificate
from a periodic finite type.  The period count vector must sum to `Q`, lie in
the pairwise left tail, and have full one-period type mass at least
`base ^ Q`; residue samples are assigned to a tail-safe positive-mass filler
signal.
-/
def proposition2_pairwise_periodic_empirical_type_lower_certificate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
  pairwiseScoringError_periodicEmpiricalTypeLowerCertificate
    law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos

/--
Proposition 2 helper: rate-parameterized entropy-aware periodic empirical-type
lower certificate.  The one-period check is stated as
`exp (-Q * baseRate) <=` the full type mass, avoiding a separate real-root
witness.
-/
def proposition2_pairwise_periodic_empirical_type_lower_certificate_of_rate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {baseRate : ℝ}
    (hbase_period :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
  pairwiseScoringError_periodicEmpiricalTypeLowerCertificate_of_rate
    law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
    hbase_period hfiller_pos

/--
Proposition 2 exact pairwise rate from periodic empirical-count data, with the
Chernoff upper side discharged by nonnegative expected score gap and concrete
positive-mass atoms on both sides of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : -Real.log base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hrate

/--
Proposition 2 exact pairwise rate from entropy-aware periodic empirical-type
data, with the Chernoff upper side discharged by nonnegative expected score
gap and concrete positive-mass atoms on both sides of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_empirical_type_lower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : -Real.log base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hrate

/--
Proposition 2 exact pairwise rate from a rate-parameterized entropy-aware
periodic empirical-type witness.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_empirical_type_lower_rate_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {baseRate : ℝ}
    (hbase_period :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : baseRate = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_period hfiller_pos hrate

/--
Proposition 2 exact pairwise rate from periodic empirical-count data and a
certified global log-MGF minimizer for the resulting geometric base.  This is
the checkable minimizer version of the periodic/type lower-bound route.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_log_mgf_global_min
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_logMGF_global_min
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hmin hwitness

/--
Proposition 2 exact pairwise rate from periodic empirical-count data and a
first-order certificate for the finite log-MGF minimizer.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_convex_log_mgf_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_convex_logMGF_deriv_zero
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hconv hderiv hwitness

/--
Proposition 2 exact pairwise rate from periodic empirical-count data,
convexity, and the explicit stationary equation for the finite log-MGF
minimizer.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_convex_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_convex_stationary
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hconv hstationary hwitness

/--
Proposition 2 exact pairwise rate from periodic empirical-count data and a
zero derivative at the finite log-MGF minimizer.  Finite-support log-MGF
convexity is supplied by the shared library.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_log_mgf_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_logMGF_deriv_zero
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hderiv hwitness

/--
Proposition 2 exact pairwise rate from periodic empirical-count data and the
explicit stationary equation for the finite log-MGF minimizer.  Finite-support
log-MGF convexity is supplied by the shared library.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_of_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_stationary
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos hstationary hwitness

/--
Proposition 2 exact pairwise rate from a method-of-types witness family:
for every target rate strictly above the Chernoff exponent, an explicit
periodic empirical-count vector gives the lower bound, while the Chernoff
upper side is discharged generically.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_count_vector_lower_witnesses
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/--
Proposition 2 exact pairwise rate from periodic empirical-type witness
families that include the full one-period multinomial type mass.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_empirical_type_lower_witnesses
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
              ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/--
Proposition 2 exact pairwise rate from rate-parameterized periodic
empirical-type witness families.  Each target-rate witness supplies a block
rate `baseRate < targetRate` and proves the full one-period type mass is at
least `exp (-Q * baseRate)`.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_empirical_type_lower_rate_witnesses
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (baseRate : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          Real.exp (-(Q : ℝ) * baseRate) ≤
            (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
              ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/--
Proposition 2 exact pairwise rate from logarithmic periodic empirical-type
witness families.  This is the method-of-types-facing form: each target-rate
witness proves the log of the full one-period type mass is at least
`-Q * baseRate`.
-/
theorem proposition2_pairwise_exact_rate_from_periodic_empirical_type_lower_log_witnesses
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (baseRate : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          (∀ signal : Signal, q signal ≠ 0 → 0 < (law signal).toReal) ∧
          -(Q : ℝ) * baseRate ≤
            Real.log (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) +
              ∑ signal : Signal,
                (q signal : ℝ) * Real.log (law signal).toReal ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_log_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/--
Proposition 2 exact pairwise rate from the stationary exponential tilt by a
finite method-of-types lower bound.  The rounded empirical types preserve
support, so the route does not require every signal atom to have positive mass.
-/
theorem proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hstationary

/--
Proposition 2 exact pairwise rate from a support-preserving stationary
finite-tilt method-of-types argument.  The stationary tilt is found internally
from nonnegative mean and positive-mass atoms on both sides of the score gap.
-/
theorem proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg

/--
Proposition 2 bundled stationary-tilt endpoint: from nonnegative expected
score gap and positive-mass atoms on both sides, Lean finds a nonpositive
stationary dual parameter, identifies the paper's Chernoff rate as
`-log MGF(z)`, and proves the exact iid exponential rate for the pairwise
mistake probability.
-/
theorem proposition2_pairwise_stationary_tilt_rate_identity_and_exact_rate_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0) :
    ∃ z : ℝ,
      z ≤ 0 ∧
        (∑ signal : Signal,
          (law signal).toReal *
            ((hiScore signal - loScore signal) *
              Real.exp (z * (hiScore signal - loScore signal)))) = 0 ∧
        pairwiseScoringRate law hiScore loScore =
          -Real.log
            (finiteMGF law
              (fun signal => hiScore signal - loScore signal) z) ∧
        ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (pairwiseScoringRate law hiScore loScore) := by
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  rcases
      exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
        law gap hmean hmassPos hgapPos hmassNeg hgapNeg with
    ⟨z, hz_nonpos, hstationary⟩
  refine ⟨z, hz_nonpos, by simpa [gap] using hstationary, ?_, ?_⟩
  · have hrate :=
      pairwiseScoringRate_eq_neg_log_base_of_stationary
        law hiScore loScore
        (base := finiteMGF law gap z) (z0 := z)
        (by simpa [gap] using hstationary)
        (by simp [gap, finiteLogMGF])
    simpa [gap] using hrate
  · exact
      proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_support
        law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
        (z := z) (by simpa [gap] using hstationary)

/--
Proposition 2 finite-support trichotomy: under nonnegative expected score gap,
the finite iid pairwise mistake probability either has the source Chernoff
rate, has the one-sided zero-gap boundary exact rate, or is eventually zero in
the strict one-sided boundary case.
-/
theorem proposition2_pairwise_exact_rate_or_boundary_from_finite_support_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ExponentialRateCertificate
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
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg
    law hiScore loScore hmean

/--
Proposition 2 finite-support dichotomy: under nonnegative expected score gap,
the finite iid pairwise mistake probability either has an exact finite
exponential rate or is eventually zero in the strict one-sided boundary case.
-/
theorem proposition2_pairwise_exact_rate_or_eventually_zero_from_finite_support_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    (∃ rate : ℝ,
      ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  pairwiseScoringError_exponentialRateCertificate_or_eventually_zero_of_mean_nonneg
    law hiScore loScore hmean

/--
Proposition 2 finite-support extended-rate endpoint: under nonnegative expected
score gap, the iid pairwise mistake probability has a finite exponential rate
or the extended rate `⊤` in the eventual-zero boundary case.
-/
theorem proposition2_pairwise_extended_rate_from_finite_support_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate :=
  pairwiseScoringError_hasExtendedExponentialRate_of_mean_nonneg
    law hiScore loScore hmean

/--
Proposition 2 exact pairwise rate from the stationary exponential tilt by a
finite method-of-types lower bound.  This full-support wrapper is retained for
paper instances where all finite signal atoms are known positive.
-/
theorem proposition2_pairwise_exact_rate_from_stationary_tilted_modal_log_full_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlaw_full : ∀ signal : Signal, 0 < (law signal).toReal)
    {z : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_full_support
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    hlaw_full hstationary

/--
Proposition 2 exact pairwise rate from entropy-aware empirical-type witness
families: for every target rate strictly above the Chernoff exponent, an
explicit finite empirical type gives the lower bound with its multinomial
type-mass factor.
-/
theorem proposition2_pairwise_exact_rate_from_empirical_type_lower_witnesses
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore,
          -Real.log C.base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/-- Proposition 3 formula for the K-approval pairwise learning rate. -/
theorem proposition3_approval_pairwise_rate_formula (pUp pDown : ℝ) :
    approvalPairwiseRate pUp pDown =
      -Real.log (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown) :=
  approvalPairwiseRate_eq_source_formula pUp pDown

/--
Remark `tminusaplusa`: in the oriented approval-rate region, increasing the
probability that the true higher-tier candidate is approved without the lower
tier candidate, or decreasing the reverse probability, strictly increases the
pairwise learning rate.
-/
theorem remark_tminusaplusa_approval_pairwise_rate_strict_mono
    {a b c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbase_pos : 0 < approvalPairwiseBase c d)
    (hbetter_base_pos : 0 < approvalPairwiseBase a b)
    (hd_le_c : d ≤ c)
    (hc_le_a : c ≤ a)
    (hb_le_d : b ≤ d)
    (hstrict : c < a ∨ b < d) :
    approvalPairwiseRate c d < approvalPairwiseRate a b := by
  have hb_le_a : b ≤ a :=
    le_trans hb_le_d (le_trans hd_le_c hc_le_a)
  exact approvalPairwiseRate_lt_of_up_lt_or_down_gt hc hd ha hb
    hbase_pos hbetter_base_pos hd_le_c hb_le_a hc_le_a hb_le_d hstrict

/--
Proposition 3 exact minimization: the K-approval closed form is the negative
infimum of the ternary approval-gap log-MGF.
-/
theorem proposition3_approval_pairwise_rate_exact_minimization
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    approvalPairwiseRate pUp pDown =
      -sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) :=
  approvalPairwiseRate_eq_ternary_log_mgf_inf hUp hDown hsum

/--
Proposition 3 Chernoff upper bound for K-approval: after identifying the
one-voter score-gap MGF with the ternary approval-gap MGF, the closed-form
approval exponent bounds the iid pairwise mistake probability.
-/
theorem proposition3_approval_pairwise_chernoff_upper_bound
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF law (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown)) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) :=
  approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_mgf
    law hiScore loScore hUp hDown hle hsum hmgf

/--
Proposition 3 finite-`N` Chernoff upper bound for K-approval: after identifying
the one-voter score-gap MGF with the ternary approval-gap MGF, the paper's
closed-form approval exponent gives the pointwise iid pairwise mistake bound.
-/
theorem proposition3_approval_pairwise_chernoff_pointwise_upper_bound
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF law (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown))
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * approvalPairwiseRate pUp pDown) :=
  approvalPairwiseErrorProb_le_exp_neg_approvalPairwiseRate_of_ternary_mgf
    law hiScore loScore hUp hDown hle hsum hmgf n

/--
Proposition 3 exact K-approval pairwise rate: all-dual ternary MGF
identification plus finite-support Cramer bounds give the closed-form
large-deviation rate.
-/
theorem proposition3_approval_pairwise_exact_rate_from_finite_iid_cramer
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1)
    (hmgf :
      ∀ z : ℝ,
        finiteMGF law (fun signal => hiScore signal - loScore signal) z =
          ternaryGapMGF pUp pDown z)
    (C : FiniteIidScoreGapCramerCertificate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) :=
  approvalPairwiseError_exponentialRateCertificate_of_cramer_ternary_mgf
    law hiScore loScore hUp hDown hsum hmgf C

/--
Proposition 3 finite iid Cramer certificate for ternary approval-style gaps:
the reusable Cramer boundary is closed by the finite ternary counting lower
bound whenever `0 < pDown <= pUp`.
-/
theorem proposition3_approval_pairwise_cramer_certificate_from_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
        pDown) :
    FiniteIidScoreGapCramerCertificate law hiScore loScore :=
  finiteIidScoreGapCramerCertificate_of_approval_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb

/--
Proposition 3 exact K-approval pairwise rate from the natural finite
score-gap classification.  If every voter contributes a gap in `{+1, 0, -1}`
and the two nonzero gap probabilities are `pUp` and `pDown`, then the paper's
closed-form approval rate follows from the finite ternary counting lower bound
and the Chernoff upper bound.
-/
theorem proposition3_approval_pairwise_exact_rate_from_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
        pDown) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) :=
  approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb

/--
Proposition 3 boundary exact K-approval pairwise rate from the natural ternary
score-gap classification.  If down-gaps have zero probability and zero-gaps
have positive probability, then the source closed form with `pDown = 0` is the
exact iid pairwise rate.
-/
theorem proposition3_approval_pairwise_exact_rate_from_ternary_scores_down_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pZero : ℝ}
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hUpProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 1) =
        pUp)
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero)
    (hZero_pos : 0 < pZero)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp 0) :=
  approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_down_zero
    law hiScore loScore hscore hUpProb hZeroProb hZero_pos hDownZero

/--
Proposition 3 strict K-approval boundary: if all positive-mass one-voter gaps
are `+1`, equivalently both zero- and down-gap events have zero probability
under the ternary classification, then the finite iid pairwise mistake event
is eventually empty.
-/
theorem proposition3_approval_pairwise_eventually_zero_from_ternary_scores_down_zero_zero_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hZeroZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        0)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ∀ᶠ n in Filter.atTop,
      pairwiseScoringErrorProb law hiScore loScore n = 0 :=
  approvalPairwiseError_eventually_zero_of_ternary_scores_down_zero_zero_zero
    law hiScore loScore hscore hZeroZero hDownZero

/--
Proposition 3 strict K-approval boundary upper bound: the eventually-empty
boundary event admits an exponential upper bound at every target rate.
-/
theorem proposition3_approval_pairwise_upper_bound_from_ternary_scores_down_zero_zero_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hZeroZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        0)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      targetRate :=
  approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_scores_down_zero_zero_zero
    law hiScore loScore hscore hZeroZero hDownZero targetRate

/--
Proposition 3 finite ternary trichotomy: under the weak source ordering
`pDown <= pUp`, a finite ternary approval-style pair either has the source
closed-form exact iid rate, or it is in the strict one-sided boundary where
the finite iid pairwise mistake event is eventually empty.
-/
theorem proposition3_approval_pairwise_exact_rate_or_eventually_zero_from_ternary_scores
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
        pZero) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (approvalPairwiseRate pUp pDown) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  approvalPairwiseError_exponentialRateCertificate_or_eventually_zero_of_ternary_scores
    law hiScore loScore hle hscore hUpProb hDownProb hZeroProb

/--
Proposition 3 finite ternary extended-rate endpoint: the pairwise K-approval
mistake probability has the source closed-form finite rate, or extended rate
`⊤` in the strict eventual-zero boundary case.
-/
theorem proposition3_approval_pairwise_extended_rate_from_ternary_scores
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
        pZero) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate :=
  approvalPairwiseError_hasExtendedExponentialRate_of_ternary_scores
    law hiScore loScore hle hscore hUpProb hDownProb hZeroProb

/--
Proposition 3 convergence consequence from the exact ternary K-approval
pairwise rate: if that source closed-form rate is positive, the iid pairwise
mistake probability tends to zero.
-/
theorem proposition3_approval_pairwise_error_tendsto_zero_from_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    (hrate_pos : 0 < approvalPairwiseRate pUp pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law hiScore loScore)
      Filter.atTop (nhds 0) :=
  approvalPairwiseError_tendsto_zero_of_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb hrate_pos

/--
Proposition 3 convergence consequence from exact ternary K-approval rates under
the paper's strict up/down separation condition.
-/
theorem proposition3_approval_pairwise_error_tendsto_zero_from_ternary_scores_of_down_lt_up
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hsum : pUp + pDown ≤ 1)
    (hlt : pDown < pUp)
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
        pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law hiScore loScore)
      Filter.atTop (nhds 0) :=
  approvalPairwiseError_tendsto_zero_of_ternary_scores_of_down_lt_up
    law hiScore loScore hUp hDown hle hsum hlt hscore hUpProb hDownProb

/--
Proposition 3 exact K-approval pairwise rate directly from a finite ranking
law.  The K-approval score gap is automatically ternary; the only paper-facing
probability inputs are the up/down K-approval event probabilities.
-/
theorem proposition3_k_approval_pairwise_exact_rate_from_ranking_law
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hUpProb : kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb : kApprovalPairDownProb law K hi lo = pDown) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      (approvalPairwiseRate pUp pDown) :=
  kApprovalPairwiseError_exponentialRateCertificate
    law K hi lo hUp hDown hle hUpProb hDownProb

/--
Proposition 3 exact K-approval pairwise rate directly from the finite ranking
law's own up/down event probabilities.
-/
theorem proposition3_k_approval_pairwise_exact_rate_from_ranking_law_probabilities
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hUp : 0 < kApprovalPairUpProb law K hi lo)
    (hDown : 0 < kApprovalPairDownProb law K hi lo)
    (hle :
      kApprovalPairDownProb law K hi lo ≤
        kApprovalPairUpProb law K hi lo) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      (approvalPairwiseRate
        (kApprovalPairUpProb law K hi lo)
        (kApprovalPairDownProb law K hi lo)) :=
  kApprovalPairwiseError_exponentialRateCertificate_of_probabilities
    law K hi lo hUp hDown hle

/--
Proposition 3 boundary exact K-approval pairwise rate directly from a finite
ranking law.  If the down-event has zero probability and the zero-gap event has
positive probability, the source closed form with `pDown = 0` is exact.
-/
theorem proposition3_k_approval_pairwise_exact_rate_from_ranking_law_down_zero
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    {pUp pZero : ℝ}
    (hUpProb : kApprovalPairUpProb law K hi lo = pUp)
    (hZeroProb : kApprovalPairZeroProb law K hi lo = pZero)
    (hZero_pos : 0 < pZero)
    (hDownZero : kApprovalPairDownProb law K hi lo = 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      (approvalPairwiseRate pUp 0) :=
  kApprovalPairwiseError_exponentialRateCertificate_down_zero
    law K hi lo hUpProb hZeroProb hZero_pos hDownZero

/--
Proposition 3 strict K-approval boundary directly from a finite ranking law:
if zero- and down-gap events both have zero probability, the finite iid
pairwise mistake event is eventually empty.
-/
theorem proposition3_k_approval_pairwise_eventually_zero_from_ranking_law_down_zero_zero_zero
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hZeroZero : kApprovalPairZeroProb law K hi lo = 0)
    (hDownZero : kApprovalPairDownProb law K hi lo = 0) :
    ∀ᶠ sampleSize in Filter.atTop,
      pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo)
        sampleSize = 0 :=
  kApprovalPairwiseError_eventually_zero_down_zero_zero_zero
    law K hi lo hZeroZero hDownZero

/--
Proposition 3 strict K-approval boundary upper bound directly from a finite
ranking law: the eventually-empty boundary event has an exponential upper
bound at every target rate.
-/
theorem proposition3_k_approval_pairwise_upper_bound_from_ranking_law_down_zero_zero_zero
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hZeroZero : kApprovalPairZeroProb law K hi lo = 0)
    (hDownZero : kApprovalPairDownProb law K hi lo = 0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      targetRate :=
  kApprovalPairwiseError_hasExpUpperBoundWithConst_down_zero_zero_zero
    law K hi lo hZeroZero hDownZero targetRate

/--
Proposition 3 finite ranking-law K-approval trichotomy: under weak up/down
ordering, a finite K-approval pair either has the source closed-form exact iid
rate, or the strict one-sided boundary makes the iid pairwise mistake event
eventually empty.
-/
theorem proposition3_k_approval_pairwise_exact_rate_or_eventually_zero_from_ranking_law
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hle : kApprovalPairDownProb law K hi lo ≤
      kApprovalPairUpProb law K hi lo) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law
          (fun π => kApprovalScore K π hi)
          (fun π => kApprovalScore K π lo))
        (approvalPairwiseRate
          (kApprovalPairUpProb law K hi lo)
          (kApprovalPairDownProb law K hi lo)) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        pairwiseScoringErrorProb law
          (fun π => kApprovalScore K π hi)
          (fun π => kApprovalScore K π lo)
          sampleSize = 0) :=
  kApprovalPairwiseError_exponentialRateCertificate_or_eventually_zero
    law K hi lo hle

/--
Proposition 3 K-approval ranking-law extended-rate endpoint.
-/
theorem proposition3_k_approval_pairwise_extended_rate_from_ranking_law
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hle : kApprovalPairDownProb law K hi lo ≤
      kApprovalPairUpProb law K hi lo) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law
          (fun π => kApprovalScore K π hi)
          (fun π => kApprovalScore K π lo))
        rate :=
  kApprovalPairwiseError_hasExtendedExponentialRate
    law K hi lo hle

/--
Proposition 3 convergence consequence directly for finite ranking laws under
K-approval: if the source closed-form pairwise approval rate is positive, the
iid pairwise mistake probability tends to zero.
-/
theorem proposition3_k_approval_pairwise_error_tendsto_zero_from_ranking_law
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hUpProb : kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb : kApprovalPairDownProb law K hi lo = pDown)
    (hrate_pos : 0 < approvalPairwiseRate pUp pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  kApprovalPairwiseError_tendsto_zero
    law K hi lo hUp hDown hle hUpProb hDownProb hrate_pos

/--
Proposition 3 convergence consequence directly for finite ranking laws under
K-approval and the paper's strict up/down separation condition.
-/
theorem proposition3_k_approval_pairwise_error_tendsto_zero_from_ranking_law_of_down_lt_up
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hsum : pUp + pDown ≤ 1)
    (hlt : pDown < pUp)
    (hUpProb : kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb : kApprovalPairDownProb law K hi lo = pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  kApprovalPairwiseError_tendsto_zero_of_down_lt_up
    law K hi lo hUp hDown hle hsum hlt hUpProb hDownProb

/--
Proposition 3 convergence consequence directly for finite ranking laws under
strict separation of the actual K-approval up/down event probabilities.
-/
theorem proposition3_k_approval_pairwise_error_tendsto_zero_from_ranking_law_probabilities_of_down_lt_up
    {n : ℕ} (law : PMF (Ranking n)) (K : ℕ) (hi lo : Candidate n)
    (hUp : 0 < kApprovalPairUpProb law K hi lo)
    (hDown : 0 < kApprovalPairDownProb law K hi lo)
    (hlt :
      kApprovalPairDownProb law K hi lo <
        kApprovalPairUpProb law K hi lo) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => kApprovalScore K π hi)
        (fun π => kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  kApprovalPairwiseError_tendsto_zero_of_probabilities_down_lt_up
    law K hi lo hUp hDown hlt

/--
Proposition 4 K-approval all-pairs bridge: a finite ranking law with identified
approval up/down probabilities yields exact pairwise rate certificates for all
ordered candidate pairs, ready for finite outcome aggregation.
-/
def proposition4_k_approval_relevant_pair_rate_certificate_from_ranking_law
    {n : ℕ} {Pair : Type*}
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair) :
    FiniteErrorRateCertificate Pair :=
  kApprovalRelevantPairRateCertificate
    law K hi lo pUp pDown hUp hDown hle hUpProb hDownProb

/--
Proposition 4 K-approval all-pairs bridge stated directly from the finite
ranking law's own up/down event probabilities.
-/
def proposition4_k_approval_relevant_pair_rate_certificate_from_ranking_law_probabilities
    {n : ℕ} {Pair : Type*}
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hUp :
      ∀ pair, 0 < kApprovalPairUpProb law K (hi pair) (lo pair))
    (hDown :
      ∀ pair, 0 < kApprovalPairDownProb law K (hi pair) (lo pair))
    (hle :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) ≤
          kApprovalPairUpProb law K (hi pair) (lo pair)) :
    FiniteErrorRateCertificate Pair :=
  kApprovalRelevantPairRateCertificate_of_probabilities
    law K hi lo hUp hDown hle

/--
Proposition 4 exact finite aggregation specialized to K-approval over a finite
set of relevant ordered pairs.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min :
      approvalPairwiseRate (pUp pairMin) (pDown pairMin) = minRate)
    (hrate_ge :
      ∀ pair, minRate ≤ approvalPairwiseRate (pUp pair) (pDown pair)) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
    law K hi lo pUp pDown hUp hDown hle hUpProb hDownProb
    hweight pairMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation for K-approval with mixed pairwise
boundary behavior.  One positive-weight relevant pair supplies the exact
minimum source approval rate; every relevant pair satisfies weak up/down
ordering, so non-minimizing pairs may either have an exact source rate at least
that minimum or be strict-boundary eventually zero.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_exact_or_eventually_zero
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hle :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) ≤
          kApprovalPairUpProb law K (hi pair) (lo pair))
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hpairMin_exact :
      ExponentialRateCertificate
        (pairwiseScoringErrorProb law
          (fun π => kApprovalScore K π (hi pairMin))
          (fun π => kApprovalScore K π (lo pairMin)))
        (approvalPairwiseRate
          (kApprovalPairUpProb law K (hi pairMin) (lo pairMin))
          (kApprovalPairDownProb law K (hi pairMin) (lo pairMin))))
    (hrate_min :
      approvalPairwiseRate
          (kApprovalPairUpProb law K (hi pairMin) (lo pairMin))
          (kApprovalPairDownProb law K (hi pairMin) (lo pairMin)) =
        minRate)
    (hrate_ge :
      ∀ pair,
        minRate ≤
          approvalPairwiseRate
            (kApprovalPairUpProb law K (hi pair) (lo pair))
            (kApprovalPairDownProb law K (hi pair) (lo pair))) :
    HasExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (fun π => kApprovalScore K π (hi pair))
              (fun π => kApprovalScore K π (lo pair))
              sampleSize)
      minRate :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_exact_or_eventually_zero
    law K hi lo hle hweight pairMin hweight_pos hpairMin_exact
    hrate_min hrate_ge

/--
Proposition 4 automatic K-approval finite aggregation: under the finite
K-approval pairwise trichotomy, a positive-weight aggregate over relevant
pairs either has some exact finite exponential rate or is eventually zero.
-/
theorem proposition4_outcome_error_exact_rate_or_eventually_zero_from_k_approval_relevant_pairs_trichotomy
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hle :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) ≤
          kApprovalPairUpProb law K (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb law
                (fun π => kApprovalScore K π (hi pair))
                (fun π => kApprovalScore K π (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (fun π => kApprovalScore K π (hi pair))
              (fun π => kApprovalScore K π (lo pair))
              sampleSize) = 0) :=
  outcomeError_hasExponentialRate_or_eventually_zero_of_kApproval_relevant_pairs_trichotomy
    law K hi lo hle hweight hweight_pos

/--
Proposition 4 automatic K-approval finite aggregation as an extended-rate
endpoint.  The extended rate is `⊤` precisely for the strict eventual-zero
boundary branch.
-/
theorem proposition4_outcome_error_extended_rate_from_k_approval_relevant_pairs_trichotomy
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hle :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) ≤
          kApprovalPairUpProb law K (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb law
                (fun π => kApprovalScore K π (hi pair))
                (fun π => kApprovalScore K π (lo pair))
                sampleSize)
        rate :=
  outcomeError_hasExtendedExponentialRate_of_kApproval_relevant_pairs_trichotomy
    law K hi lo hle hweight hweight_pos

/--
Proposition 4 exact finite aggregation specialized to K-approval over a finite
set of relevant ordered pairs in the zero-down boundary case.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_down_zero
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pZero : Pair → ℝ)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hZeroProb :
      ∀ pair, kApprovalPairZeroProb law K (hi pair) (lo pair) = pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    (hDownZero :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = 0)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min : approvalPairwiseRate (pUp pairMin) 0 = minRate)
    (hrate_ge :
      ∀ pair, minRate ≤ approvalPairwiseRate (pUp pair) 0) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_down_zero law K hi lo pUp pZero
          hUpProb hZeroProb hZero_pos hDownZero).aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_down_zero
    law K hi lo pUp pZero hUpProb hZeroProb hZero_pos hDownZero
    hweight pairMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation at the finite outcome-learning rate for
K-approval relevant pairs in the zero-down boundary case.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_down_zero_at_finiteOutcomeLearningRate
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pZero : Pair → ℝ)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hZeroProb :
      ∀ pair, kApprovalPairZeroProb law K (hi pair) (lo pair) = pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    (hDownZero :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = 0)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_down_zero law K hi lo pUp pZero
          hUpProb hZeroProb hZero_pos hDownZero).aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) 0)) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_down_zero_at_finiteOutcomeLearningRate
    law K hi lo pUp pZero hUpProb hZeroProb hZero_pos hDownZero
    hweight hweight_pos

/--
Proposition 4 exact finite aggregation specialized to K-approval over a finite
set of relevant ordered pairs, with the finite minimum rate chosen internally.
If every relevant pair has positive weight, the outcome-error exponent is the
finite outcome-learning rate over the relevant pair exponents.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_at_finiteOutcomeLearningRate
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate
    law K hi lo pUp pDown hUp hDown hle hUpProb hDownProb
    hweight hweight_pos

/--
Proposition 4 exact finite aggregation at the finite outcome-learning rate,
deriving weak pairwise ordering from strict up/down separation.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
    law K hi lo pUp pDown hUp hDown hlt hUpProb hDownProb
    hweight hweight_pos

/--
Proposition 4 exact finite aggregation at the finite outcome-learning rate,
stated directly from the finite ranking law's up/down event probabilities.
-/
theorem proposition4_outcome_error_exact_rate_from_k_approval_relevant_pairs_at_finiteOutcomeLearningRate_from_probabilities_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hUp :
      ∀ pair, 0 < kApprovalPairUpProb law K (hi pair) (lo pair))
    (hDown :
      ∀ pair, 0 < kApprovalPairDownProb law K (hi pair) (lo pair))
    (hlt :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) <
          kApprovalPairUpProb law K (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_of_probabilities
          law K hi lo hUp hDown (fun pair => (hlt pair).le))
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair =>
          approvalPairwiseRate
            (kApprovalPairUpProb law K (hi pair) (lo pair))
            (kApprovalPairDownProb law K (hi pair) (lo pair)))) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_probabilities_down_lt_up
    law K hi lo hUp hDown hlt hweight hweight_pos

/--
Proposition 4 convergence form for K-approval over a finite set of relevant
ordered pairs: a positive lower bound on all relevant closed-form pair rates
makes the weighted outcome-error aggregate tend to zero.
-/
theorem proposition4_outcome_error_tendsto_zero_from_k_approval_relevant_pairs
    {n : ℕ} {Pair : Type*} [Fintype Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ} {rateFloor : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor :
      ∀ pair, rateFloor ≤ approvalPairwiseRate (pUp pair) (pDown pair)) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_kApproval_relevant_pairs
    law K hi lo pUp pDown hUp hDown hle hUpProb hDownProb
    hweight hrateFloor_pos hrateFloor

/--
Proposition 4 convergence form for K-approval over a finite nonempty set of
relevant ordered pairs, using only the paper's strict up/down separation and
probability-mass constraints to make the finite outcome rate positive.
-/
theorem proposition4_outcome_error_tendsto_zero_from_k_approval_relevant_pairs_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hsum : ∀ pair, pUp pair + pDown pair ≤ 1)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up
    law K hi lo pUp pDown hUp hDown hsum hlt hUpProb hDownProb hweight

/--
Proposition 4 convergence form for K-approval over a finite nonempty set of
relevant ordered pairs, using only strict up/down separation.  The probability
mass constraint is derived from disjointness of the corresponding K-approval
up/down events.
-/
theorem proposition4_outcome_error_tendsto_zero_from_k_approval_relevant_pairs_of_down_lt_up_auto_sum
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair, kApprovalPairUpProb law K (hi pair) (lo pair) = pUp pair)
    (hDownProb :
      ∀ pair, kApprovalPairDownProb law K (hi pair) (lo pair) = pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up_auto_sum
    law K hi lo pUp pDown hUp hDown hlt hUpProb hDownProb hweight

/--
Proposition 4 convergence form for K-approval stated directly from the finite
ranking law's up/down event probabilities.
-/
theorem proposition4_outcome_error_tendsto_zero_from_k_approval_relevant_pairs_from_probabilities_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (Ranking n)) (K : ℕ)
    (hi lo : Pair → Candidate n)
    (hUp :
      ∀ pair, 0 < kApprovalPairUpProb law K (hi pair) (lo pair))
    (hDown :
      ∀ pair, 0 < kApprovalPairDownProb law K (hi pair) (lo pair))
    (hlt :
      ∀ pair,
        kApprovalPairDownProb law K (hi pair) (lo pair) <
          kApprovalPairUpProb law K (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate_of_probabilities
          law K hi lo hUp hDown (fun pair => (hlt pair).le))
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_probabilities_down_lt_up
    law K hi lo hUp hDown hlt hweight

/--
Proposition 3 exact K-approval pairwise rate with only the analytic lower-bound
side supplied.  The finite Chernoff upper-bound side is discharged by the
formalized ternary score-gap argument.
-/
theorem proposition3_approval_pairwise_exact_rate_from_ternary_lower_bounds
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    (hpos :
      ∀ᶠ n in Filter.atTop,
        0 < pairwiseScoringErrorProb law hiScore loScore n)
    (hlower :
      ∀ targetRate,
        approvalPairwiseRate pUp pDown < targetRate →
          HasExpLowerBoundWithConst
            (pairwiseScoringErrorProb law hiScore loScore) targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) :=
  approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_lower_bounds
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb hpos hlower

/--
Proposition 3 exact K-approval pairwise rate from the concrete lower-bound
shape produced by a finite-type or multinomial lower-bound argument: an
eventual lower bound by `c * exp(-rate)^n / (n+1)^d`.
-/
theorem proposition3_approval_pairwise_exact_rate_from_poly_geometric_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    {lowerConst : ℝ} (hlowerConst : 0 < lowerConst) (lowerDegree : ℕ)
    (hlower :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst *
            Real.exp (-(approvalPairwiseRate pUp pDown)) ^ n /
              (((n.succ : ℕ) : ℝ) ^ lowerDegree) ≤
          pairwiseScoringErrorProb law hiScore loScore n) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) :=
  approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_poly_geometric_lower
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb
    hlowerConst lowerDegree hlower

/--
Proposition 4, finite aggregation part: pairwise learning-rate certificates
give a finite outcome-error exponential upper bound.
-/
theorem proposition4_outcome_error_upper_bound_from_pairwise_certificates
    {Candidate : Type*} [Fintype Candidate]
    (C : PairwiseErrorRateCertificate Candidate)
    {pairWeight : Candidate → Candidate → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate < C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate :=
  outcomeError_hasExpUpperBound_of_pairwise_rate_certificates
    C hweight hrate

/--
Proposition 4 finite-`N` relevant-pair upper bound: if every indexed relevant
pair has a nonpositive Chernoff dual certifying at least `targetRate`, then the
unweighted expected number of indexed pairwise mistakes is at most
`card(Pair) * exp (-n * targetRate)`.
-/
theorem proposition4_relevant_score_gap_error_sum_pointwise_upper_bound_from_duals
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (dual : Pair → ℝ) {targetRate : ℝ}
    (hdual : ∀ pair, dual pair ≤ 0)
    (hrate :
      ∀ pair,
        targetRate ≤
          -(finiteLogMGF law
            (fun signal => score (hi pair) signal - score (lo pair) signal)
            (dual pair)))
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Pair : ℝ) * Real.exp (-(n : ℝ) * targetRate) :=
  finiteRelevantScoreGapErrorSum_le_card_mul_exp_of_nonpos_duals
    law score hi lo dual hdual hrate n

/--
Proposition 4 finite-`N` relevant-pair upper bound at the realized finite
outcome-learning rate.  The per-pair pointwise bounds are supplied by the
support-aware Proposition 2 finite-sample theorem.
-/
theorem proposition4_relevant_score_gap_error_sum_pointwise_upper_bound_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal => score (hi pair) signal - score (lo pair) signal))
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 < score (hi pair) (aPos pair) - score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
        score (hi pair) (aNeg pair) - score (lo pair) (aNeg pair) < 0)
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Pair : ℝ) *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              pairwiseScoringRate law
                (score (hi pair)) (score (lo pair)))) :=
  finiteRelevantScoreGapErrorSum_le_card_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    law score hi lo hmean hmassPos hgapPos hmassNeg hgapNeg n

/--
Proposition 4 finite-`N` W-selection upper bound in the paper's coarse `M^2`
form over all true-winner/true-loser cross-tier pairs.
-/
theorem proposition4_cross_tier_error_sum_pointwise_upper_bound_from_duals
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (dual : CrossTierPair winnerSet → ℝ) {targetRate : ℝ}
    (hdual : ∀ pair, dual pair ≤ 0)
    (hrate :
      ∀ pair,
        targetRate ≤
          -(finiteLogMGF law
            (fun signal => score pair.hi signal - score pair.lo signal)
            (dual pair)))
    (n : ℕ) :
    (∑ pair : CrossTierPair winnerSet,
      finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n) ≤
      (Fintype.card Candidate : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) * targetRate) :=
  crossTierScoreGapErrorSum_le_candidate_card_sq_mul_exp_of_nonpos_duals
    law score winnerSet dual hdual hrate n

/--
Proposition 4 finite-`N` W-selection upper bound in the paper's coarse `M^2`
form at the realized finite outcome-learning rate.  The per-pair pointwise
bounds are supplied by the support-aware Proposition 2 finite-sample theorem.
-/
theorem proposition4_cross_tier_error_sum_pointwise_upper_bound_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal => score pair.hi signal - score pair.lo signal))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 < score pair.hi (aPos pair) - score pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
        score pair.hi (aNeg pair) - score pair.lo (aNeg pair) < 0)
    (n : ℕ) :
    (∑ pair : CrossTierPair winnerSet,
      finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n) ≤
      (Fintype.card Candidate : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : CrossTierPair winnerSet =>
              pairwiseScoringRate law
                (score pair.hi) (score pair.lo))) :=
  crossTierScoreGapErrorSum_le_candidate_card_sq_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    law score winnerSet hmean hmassPos hgapPos hmassNeg hgapNeg n

/--
Proposition 4 exact aggregation endpoint: a finite weighted sum of pairwise
error probabilities has exponential rate equal to the realized minimum
pairwise rate, provided the minimum pair has positive weight.
-/
theorem proposition4_outcome_error_exact_rate_from_pairwise_minimum
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (C : PairwiseErrorRateCertificate Candidate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min : C.rate hiMin loMin = minRate)
    (hrate_ge : ∀ hi lo, minRate ≤ C.rate hi lo) :
    HasExponentialRate (C.aggregateError pairWeight) minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    C hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from the finite-support Proposition 2
trichotomy.  One positive-weight relevant pair supplies the exact minimum
rate.  Every relevant score-gap pair has nonnegative mean and therefore is
either certified at the source pairwise scoring rate, certified in the
zero-gap boundary at `-log pZero`, or eventually zero in the strict one-sided
boundary case.
-/
theorem proposition4_outcome_error_exact_rate_from_relevant_pairs_finite_support_exact_or_boundary_or_eventually_zero
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hpairMin_exact :
      ExponentialRateCertificate
        (finiteScoreGapPairwiseErrorProb law score
          (hi pairMin) (lo pairMin))
        minRate)
    (hsource_rate_ge :
      ∀ pair,
        minRate ≤
          pairwiseScoringRate law
            (score (hi pair)) (score (lo pair)))
    (hzero_rate_ge :
      ∀ pair pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero) :
    HasExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize)
      minRate :=
  outcomeError_hasExponentialRate_of_relevant_pairs_finite_support_exact_or_boundary_or_eventually_zero
    law score hi lo hmean hweight pairMin hweight_pos hpairMin_exact
    hsource_rate_ge hzero_rate_ge

/--
Proposition 4 automatic finite-support trichotomy aggregation: if all relevant
pairs have nonnegative expected score gap, a positive-weight finite aggregate
of their pairwise errors either has some exact finite exponential rate or is
eventually zero.
-/
theorem proposition4_outcome_error_exact_rate_or_eventually_zero_from_relevant_pairs_finite_support_trichotomy
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              finiteScoreGapPairwiseErrorProb law score
                (hi pair) (lo pair) sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize) = 0) :=
  outcomeError_hasExponentialRate_or_eventually_zero_of_relevant_pairs_finite_support_trichotomy
    law score hi lo hmean hweight hweight_pos

/--
Proposition 4 automatic finite aggregation as an extended-rate endpoint.  This
is the source-facing finite-support statement: a positive finite aggregate has
a finite exact exponent unless it is eventually zero, represented by `⊤`.
-/
theorem proposition4_outcome_error_extended_rate_from_relevant_pairs_finite_support_trichotomy
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              finiteScoreGapPairwiseErrorProb law score
                (hi pair) (lo pair) sampleSize)
        rate :=
  outcomeError_hasExtendedExponentialRate_of_relevant_pairs_finite_support_trichotomy
    law score hi lo hmean hweight hweight_pos

/--
Proposition 4 pairwise certificate constructor for the one-sided finite-real
boundary case: every positive-mass score gap is nonnegative, and each ordered
pair has positive zero-gap probability.
-/
def proposition4_pairwise_rate_certificate_from_support_nonneg_zero_gap_prob
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pZero : Candidate → Candidate → ℝ)
    (hsupport :
      ∀ hi lo signal, 0 < (law signal).toReal →
        0 ≤ score hi signal - score lo signal)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_support_nonneg_zero_gap_prob
    law score pZero hsupport hZeroProb hZero_pos

/--
Proposition 4 exact finite aggregation for the one-sided finite-real boundary
case.  The realized minimum rate is computed from the per-pair zero-gap
probability as `-log pZero`.
-/
theorem proposition4_outcome_error_exact_rate_from_support_nonneg_zero_gap_prob
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pZero : Candidate → Candidate → ℝ)
    (hsupport :
      ∀ hi lo signal, 0 < (law signal).toReal →
        0 ≤ score hi signal - score lo signal)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min : -Real.log (pZero hiMin loMin) = minRate)
    (hrate_ge : ∀ hi lo, minRate ≤ -Real.log (pZero hi lo)) :
    HasExponentialRate
      ((proposition4_pairwise_rate_certificate_from_support_nonneg_zero_gap_prob
          law score pZero hsupport hZeroProb hZero_pos).aggregateError
        pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (proposition4_pairwise_rate_certificate_from_support_nonneg_zero_gap_prob
      law score pZero hsupport hZeroProb hZero_pos)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 relevant-pair certificate constructor for the one-sided
finite-real boundary case.  This version indexes only the finite paper-facing
relevant pairs rather than all ordered candidate pairs.
-/
def proposition4_relevant_pair_rate_certificate_from_support_nonneg_zero_gap_prob
    {Pair Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (pZero : Pair → ℝ)
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 ≤ score (hi pair) signal - score (lo pair) signal)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair) :
    FiniteErrorRateCertificate Pair :=
  finiteScoreGapRelevantPairRateCertificate_of_support_nonneg_zero_gap_prob
    law score hi lo pZero hsupport hZeroProb hZero_pos

/--
Proposition 4 exact finite aggregation for the one-sided finite-real boundary
over a finite relevant-pair set.  The realized minimum rate is computed from
the relevant pair's zero-gap probability as `-log pZero`.
-/
theorem proposition4_outcome_error_exact_rate_from_support_nonneg_zero_gap_prob_relevant_pairs
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (pZero : Pair → ℝ)
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 ≤ score (hi pair) signal - score (lo pair) signal)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min : -Real.log (pZero pairMin) = minRate)
    (hrate_ge : ∀ pair, minRate ≤ -Real.log (pZero pair)) :
    HasExponentialRate
      ((proposition4_relevant_pair_rate_certificate_from_support_nonneg_zero_gap_prob
          law score hi lo pZero hsupport hZeroProb hZero_pos)
        |>.aggregateError pairWeight)
      minRate :=
  finiteRelevantScoreGapAggregateError_hasExponentialRate_of_support_nonneg_zero_gap_prob
    law score hi lo pZero hsupport hZeroProb hZero_pos
    hweight pairMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 pairwise certificate constructor for K-approval-style ternary
boundary pairs: each ordered pair has ternary one-voter score gaps, zero
down-gap probability, and positive zero-gap probability.
-/
def proposition4_pairwise_rate_certificate_from_approval_ternary_scores_down_zero
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pZero : Candidate → Candidate → ℝ)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo)
    (hDownZero :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          0) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_approval_ternary_scores_down_zero
    law score pUp pZero hscore hUpProb hZeroProb hZero_pos hDownZero

/--
Proposition 4 exact finite aggregation for K-approval-style ternary boundary
pairs.  The realized minimum rate is computed in the source closed-form
language as `approvalPairwiseRate (pUp hi lo) 0`.
-/
theorem proposition4_outcome_error_exact_rate_from_approval_ternary_scores_down_zero
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pZero : Candidate → Candidate → ℝ)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo)
    (hDownZero :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min : approvalPairwiseRate (pUp hiMin loMin) 0 = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤ approvalPairwiseRate (pUp hi lo) 0) :
    HasExponentialRate
      ((proposition4_pairwise_rate_certificate_from_approval_ternary_scores_down_zero
          law score pUp pZero hscore hUpProb hZeroProb hZero_pos hDownZero)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (proposition4_pairwise_rate_certificate_from_approval_ternary_scores_down_zero
      law score pUp pZero hscore hUpProb hZeroProb hZero_pos hDownZero)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 strict-support relevant-pair aggregation: if every indexed
relevant score gap is strictly positive on every positive-mass signal, then the
finite aggregate pairwise mistake event is eventually empty.
-/
theorem proposition4_relevant_score_gap_aggregate_eventually_zero_from_support_pos
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 < score (hi pair) signal - score (lo pair) signal) :
    ∀ᶠ n in Filter.atTop,
      (∑ pair : Pair,
        pairWeight pair *
          finiteScoreGapPairwiseErrorProb law score
            (hi pair) (lo pair) n) = 0 :=
  finiteRelevantScoreGapAggregateError_eventually_zero_of_support_pos
    law score hi lo (pairWeight := pairWeight) hsupport

/--
Proposition 4 strict-support relevant-pair aggregation: the same eventually
empty aggregate has an exponential upper bound at any finite target rate.
-/
theorem proposition4_relevant_score_gap_aggregate_upper_bound_from_support_pos
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 < score (hi pair) signal - score (lo pair) signal)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (fun n =>
        ∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) n)
      targetRate :=
  finiteRelevantScoreGapAggregateError_hasExpUpperBoundWithConst_of_support_pos
    law score hi lo (pairWeight := pairWeight) hsupport targetRate

/--
Proposition 4 finite aggregation from iid finite score-gap Chernoff duals.
This closes the finite upper-bound aggregation route without assuming exact
pairwise rate certificates.
-/
theorem proposition4_outcome_error_upper_bound_from_finite_score_gap_duals
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (dual : Candidate → Candidate → ℝ)
    {pairWeight : Candidate → Candidate → ℝ} {targetRate : ℝ}
    (hdual : ∀ hi lo : Candidate, dual hi lo ≤ 0)
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate :
      ∀ hi lo,
        targetRate ≤ finiteScoreGapPairwiseDualRate law score dual hi lo) :
    HasExpUpperBoundWithConst
      ((finiteScoreGapPairwiseUpperBoundCertificate
          law score dual hdual).aggregateError pairWeight)
      targetRate :=
  outcomeError_hasExpUpperBound_of_finite_score_gap_duals
    law score dual hdual hweight hrate

/--
Proposition 4 positive-gap finite aggregation: for a finite nonempty relevant
pair index, positive one-voter expected score gap on every indexed pair gives
some positive exponential upper-bound rate for the weighted aggregate error.
-/
theorem proposition4_relevant_score_gap_aggregate_positive_exponential_decay
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hmean :
      ∀ pair,
        0 <
          AppliedModelingLib.pmfExp law
            (fun signal => score (hi pair) signal - score (lo pair) signal)) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n =>
            ∑ pair : Pair,
              pairWeight pair *
                finiteScoreGapPairwiseErrorProb law score
                  (hi pair) (lo pair) n)
          targetRate :=
  finiteRelevantScoreGapAggregateError_exists_pos_expUpperBoundWithConst
    law score hi lo hweight hmean

/--
Proposition 4 exact finite aggregation from finite iid score-gap Cramer
certificates: the outcome-error rate is the realized minimum pairwise
Chernoff/log-MGF rate when the minimum pair has positive weight.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_cramer
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo))
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate law score cramer)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_cramer
    law score cramer hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from per-pair periodic
method-of-types witnesses: every relevant pair supplies a periodic empirical
count-vector lower witness at every slower target rate, and the aggregate
outcome-error exponent is the realized minimum pairwise Chernoff rate.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_periodic_count_vector_lower_witnesses
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (score hi signal - score lo signal) ≤ 0) ∧
          score hi filler - score lo filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from entropy-aware empirical-type
method-of-types witnesses.  Each pair may choose a finite empirical type at
every strictly slower target rate, with the multinomial type-mass factor
included in the lower-bound certificate.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_empirical_type_lower_witnesses
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
          ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate
              law (score hi) (score lo),
            -Real.log C.base < targetRate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
path/type lower certificates: concrete lower-bound witnesses for every
ordered pair combine with the Chernoff upper-bound side and finite minimum-rate
aggregation to give the exact outcome-error exponent.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_path_lower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapPathLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_pathLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_pathLower
    law score hupper lower hrate hweight hiMin loMin hweight_pos
    hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from path/type lower certificates, with
every pair's Chernoff upper side discharged by nonnegative expected score gap
and concrete positive-mass atoms on both sides of the score gap.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_path_lower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapPathLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_pathLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_pathLower_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    lower hrate hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from direct finite score-gap
tail-probability lower certificates: lower-bound witnesses for every ordered
pair combine with the Chernoff upper-bound side and finite minimum-rate
aggregation to give the exact outcome-error exponent.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_tail_lower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapTailLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_tailLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_tailLower
    law score hupper lower hrate hweight hiMin loMin hweight_pos
    hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from direct finite score-gap
tail-probability lower certificates, with every pair's Chernoff upper side
discharged by nonnegative expected score gap and concrete positive-mass atoms
on both sides of the score gap.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_tail_lower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapTailLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_tailLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_tailLower_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower hrate
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from exact finite score-gap
empirical-type lower certificates: multinomial type-mass lower-bound
witnesses for every ordered pair combine with the Chernoff upper-bound side
and finite minimum-rate aggregation to give the exact outcome-error exponent.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_empirical_type_lower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower
    law score hupper lower hrate hweight hiMin loMin hweight_pos
    hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from exact finite score-gap
empirical-type lower certificates, with every pair's Chernoff upper side
discharged by nonnegative expected score gap and concrete positive-mass atoms
on both sides of the score gap.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_empirical_type_lower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower hrate
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from stationary finite exponential
tilts.  The pairwise exact rates are closed by the support-preserving
method-of-types theorem, then combined by finite minimum-rate aggregation.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          z hstationary)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    z hstationary
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from supplied support-preserving
stationary finite tilts, stated at the realized finite outcome-learning rate.
The minimizing ordered candidate pair is selected internally from finiteness.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hweight_pos : ∀ hi lo, 0 < pairWeight hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          z hstationary)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Candidate × Candidate =>
          finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2)) :=
  outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_at_finiteOutcomeLearningRate
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    z hstationary hweight hweight_pos

/--
Proposition 4 exact finite aggregation from support-preserving stationary
finite tilts.  The per-pair stationary tilts are found internally from
nonnegative expected gaps and positive-mass atoms on both sides of each score
gap, then combined by finite minimum-rate aggregation.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 relevant-pair stationary bridge: a finite family of relevant
ordered candidate pairs with nonnegative expected gaps and positive-mass atoms
on both sides gives exact-rate certificates for exactly those pairwise errors.
-/
def proposition4_relevant_pair_rate_certificate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Pair Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0) :
    FiniteErrorRateCertificate Pair :=
  finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg

/--
Proposition 4 exact finite aggregation from support-aware stationary finite
tilts over a finite relevant-pair index.  A supplied relevant pair realizes
the finite minimum rate.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_relevant_pairs
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score
        (hi pairMin) (lo pairMin) = minRate)
    (hrate_ge :
      ∀ pair,
        minRate ≤
          finiteIidPairwiseScoreGapChernoffRate law score
            (hi pair) (lo pair)) :
    HasExponentialRate
      ((proposition4_relevant_pair_rate_certificate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    hweight pairMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from support-aware stationary finite
tilts over exactly the relevant ordered-pair index, stated at that finite
relevant-pair outcome-learning rate.  The minimizing relevant pair is selected
internally from finiteness.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate_relevant_pairs
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((proposition4_relevant_pair_rate_certificate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteIidPairwiseScoreGapChernoffRate law score
            (hi pair) (lo pair))) :=
  outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    hweight hweight_pos

/--
Proposition 4 source-shaped W-selection exact-rate theorem: the expected number
of cross-tier pairwise errors has exponential rate equal to the finite minimum
of the source pairwise scoring rates over true-winner/true-loser pairs.
-/
theorem proposition4_cross_tier_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score pair.hi signal - score pair.lo signal))
    (aPos aNeg : CrossTierPair winnerSet → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score pair.hi (aPos pair) -
        score pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score pair.hi (aNeg pair) -
        score pair.lo (aNeg pair) < 0) :
    HasExponentialRate
      (fun n =>
        ∑ pair : CrossTierPair winnerSet,
          finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n)
      (finiteOutcomeLearningRate
        (fun pair : CrossTierPair winnerSet =>
          pairwiseScoringRate law (score pair.hi) (score pair.lo))) :=
  crossTierOutcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    law score winnerSet hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg

/--
Proposition 4 exact finite aggregation at the realized finite outcome-learning
rate.  This is the finite stationary-tilt endpoint with the minimizing
ordered candidate pair selected internally from finiteness.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    {pairWeight : Candidate → Candidate → ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hweight_pos : ∀ hi lo, 0 < pairWeight hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Candidate × Candidate =>
          finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2)) :=
  outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    hweight hweight_pos

/--
Proposition 4 exact finite aggregation from stationary finite exponential
tilts.  This full-support wrapper is retained for paper instances where all
finite signal atoms are known positive.
-/
theorem proposition4_outcome_error_exact_rate_from_stationary_tilted_modal_log_full_support
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (hlaw_full : ∀ signal : Signal, 0 < (law signal).toReal)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_full_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          hlaw_full z hstationary)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_full_support
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    hlaw_full z hstationary
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
bucket/type lower certificates: empirical bucket lower-bound witnesses for
every ordered pair combine with the Chernoff upper-bound side and finite
minimum-rate aggregation to give the exact outcome-error exponent.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_bucket_lower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapBucketLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_bucketLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_bucketLower
    law score hupper lower hrate hweight hiMin loMin hweight_pos
    hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from empirical bucket/type lower
certificates, with every pair's Chernoff upper side discharged by nonnegative
expected score gap and concrete positive-mass atoms on both sides of the score
gap.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_bucket_lower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapBucketLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_bucketLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_bucketLower_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    lower hrate hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
empirical count-vector lower certificates: count-vector lower-bound witnesses
for every ordered pair combine with the Chernoff upper-bound side and finite
minimum-rate aggregation to give the exact outcome-error exponent.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_count_vector_lower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCountVectorLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_countVectorLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_countVectorLower
    law score hupper lower hrate hweight hiMin loMin hweight_pos
    hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
empirical count-vector lower certificates, with every pair's Chernoff upper
side discharged by nonnegative expected score gap and concrete positive-mass
atoms on both sides of the score gap.
-/
theorem proposition4_outcome_error_exact_rate_from_finite_score_gap_count_vector_lower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCountVectorLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_countVectorLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_finite_score_gap_countVectorLower_of_mean_nonneg_pos_neg_atoms
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    lower hrate hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation for K-approval: after all-dual ternary
MGF identification and finite-support Cramer bounds, the outcome-error
large-deviation rate is the realized minimum closed-form approval pair rate.
-/
theorem proposition4_outcome_error_exact_rate_from_approval_cramer
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hsum : ∀ hi lo, pUp hi lo + pDown hi lo ≤ 1)
    (hmgf :
      ∀ hi lo z,
        finiteMGF law
            (fun signal => score hi signal - score lo signal) z =
          ternaryGapMGF (pUp hi lo) (pDown hi lo) z)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo))
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      approvalPairwiseRate (pUp hiMin loMin) (pDown hiMin loMin) = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    HasExponentialRate
      ((approvalPairwiseRateCertificate law score pUp pDown
          hUp hDown hsum hmgf cramer)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_approval_cramer
    law score pUp pDown hUp hDown hsum hmgf cramer
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation for K-approval from concrete ternary
score gaps: if every pair has the natural `{+1, 0, -1}` gap law with nonzero
probabilities `pUp` and `pDown`, then the outcome-error rate is the realized
minimum closed-form approval pair rate.
-/
theorem proposition4_outcome_error_exact_rate_from_approval_ternary_scores
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hle : ∀ hi lo, pDown hi lo ≤ pUp hi lo)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hDownProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          pDown hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      approvalPairwiseRate (pUp hiMin loMin) (pDown hiMin loMin) = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    HasExponentialRate
      ((approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
          hUp hDown hle hscore hUpProb hDownProb)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_approval_ternary_scores
    law score pUp pDown hUp hDown hle hscore hUpProb hDownProb
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 convergence form from concrete ternary approval-style score
gaps: a positive lower bound on all closed-form pair rates makes the finite
weighted aggregate of pairwise errors tend to zero.
-/
theorem proposition4_outcome_error_tendsto_zero_from_approval_ternary_scores
    {Candidate Signal : Type*} [Fintype Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hle : ∀ hi lo, pDown hi lo ≤ pUp hi lo)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hDownProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          pDown hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {rateFloor : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor :
      ∀ hi lo,
        rateFloor ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    Filter.Tendsto
      ((approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
          hUp hDown hle hscore hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_approval_ternary_scores
    law score pUp pDown hUp hDown hle hscore hUpProb hDownProb
    hweight hrateFloor_pos hrateFloor

/--
Randomized scoring pairwise comparison: a pointwise log-MGF domination
certificate gives the pairwise Chernoff-rate comparison used in the source
convexity proof.
-/
theorem randomized_scoring_pairwise_rate_le_static_of_log_mgf_domination
    {StaticSignal RandomizedSignal : Type*}
    [Fintype StaticSignal] [Fintype RandomizedSignal]
    [DecidableEq StaticSignal] [DecidableEq RandomizedSignal]
    (staticLaw : PMF StaticSignal) (randomizedLaw : PMF RandomizedSignal)
    (staticHiScore staticLoScore : StaticSignal → ℝ)
    (randomizedHiScore randomizedLoScore : RandomizedSignal → ℝ)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF staticLaw
          (fun signal => staticHiScore signal - staticLoScore signal) z))
    (hlog :
      ∀ z : ℝ,
        finiteLogMGF staticLaw
            (fun signal => staticHiScore signal - staticLoScore signal) z ≤
          finiteLogMGF randomizedLaw
            (fun signal => randomizedHiScore signal - randomizedLoScore signal)
            z) :
    pairwiseScoringRate randomizedLaw randomizedHiScore randomizedLoScore ≤
      pairwiseScoringRate staticLaw staticHiScore staticLoScore :=
  pairwiseScoringRate_le_static_of_logMGF_domination
    staticLaw randomizedLaw staticHiScore staticLoScore
    randomizedHiScore randomizedLoScore hstatic_bdd hlog

/--
Randomized scoring pairwise comparison with the static boundedness side
condition discharged from concrete positive and negative pivotal atoms.
-/
theorem randomized_scoring_pairwise_rate_le_static_of_log_mgf_domination_of_pos_neg_atoms
    {StaticSignal RandomizedSignal : Type*}
    [Fintype StaticSignal] [Fintype RandomizedSignal]
    [DecidableEq StaticSignal] [DecidableEq RandomizedSignal]
    (staticLaw : PMF StaticSignal) (randomizedLaw : PMF RandomizedSignal)
    (staticHiScore staticLoScore : StaticSignal → ℝ)
    (randomizedHiScore randomizedLoScore : RandomizedSignal → ℝ)
    {aPos aNeg : StaticSignal}
    (hmassPos : 0 < (staticLaw aPos).toReal)
    (hgapPos : 0 < staticHiScore aPos - staticLoScore aPos)
    (hmassNeg : 0 < (staticLaw aNeg).toReal)
    (hgapNeg : staticHiScore aNeg - staticLoScore aNeg < 0)
    (hlog :
      ∀ z : ℝ,
        finiteLogMGF staticLaw
            (fun signal => staticHiScore signal - staticLoScore signal) z ≤
          finiteLogMGF randomizedLaw
            (fun signal => randomizedHiScore signal - randomizedLoScore signal)
            z) :
    pairwiseScoringRate randomizedLaw randomizedHiScore randomizedLoScore ≤
      pairwiseScoringRate staticLaw staticHiScore staticLoScore :=
  pairwiseScoringRate_le_static_of_logMGF_domination_of_pos_neg_atoms
    staticLaw randomizedLaw staticHiScore staticLoScore
    randomizedHiScore randomizedLoScore
    hmassPos hgapPos hmassNeg hgapNeg hlog

/--
Randomized scoring direct finite Jensen endpoint: if the static score gap is
the weighted average of the component score gaps signal-by-signal, then the
static convex-combination scoring rule weakly dominates the randomized
scoring-rule mixture in pairwise Chernoff rate.
-/
theorem randomized_scoring_mixture_rate_le_static_of_weighted_score
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z)) :
    randomizedScoringMixtureRate law weight gap ≤
      finiteChernoffRate law staticGap :=
  randomizedScoringMixtureRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum hstatic_bdd

/--
Randomized scoring direct finite Jensen endpoint with static boundedness
discharged from concrete positive and negative pivotal atoms.
-/
theorem randomized_scoring_mixture_rate_le_static_of_weighted_score_of_pos_neg_atoms
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < staticGap aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : staticGap aNeg < 0) :
    randomizedScoringMixtureRate law weight gap ≤
      finiteChernoffRate law staticGap :=
  randomizedScoringMixtureRate_le_static_of_weighted_score_of_pos_neg_atoms
    law weight gap staticGap hstatic hweight hsum
    hmassPos hgapPos hmassNeg hgapNeg

/--
Actual randomized scoring law identity: drawing a rule from the finite weight
vector and then drawing a signal has exactly the mixture Chernoff rate used in
the source convexity proof.
-/
theorem randomized_scoring_sampling_law_finite_chernoff_rate_eq_mixture_rate
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (gap : Rule → Signal → ℝ) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) =
      randomizedScoringMixtureRate law weight gap :=
  randomizedScoringSamplingLaw_finiteChernoffRate_eq_mixtureRate
    law weight hweight hsum gap

/--
Randomized scoring comparison: pairwise domination of pivotal rates lifts to
domination of the finite outcome-learning rate.
-/
theorem randomized_scoring_outcome_rate_le_static_of_pairwise
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticRate randomizedRate : Pair → ℝ)
    (hpair : ∀ pair, randomizedRate pair ≤ staticRate pair) :
    finiteOutcomeLearningRate randomizedRate ≤
      finiteOutcomeLearningRate staticRate :=
  randomizedScoring_outcomeRate_le_static_of_pairwise
    staticRate randomizedRate hpair

/--
Randomized scoring source theorem, finite-outcome form: the static
convex-combination scoring rule weakly dominates the randomized scoring-rule
mixture in outcome learning rate.
-/
theorem randomized_scoring_outcome_rate_le_static_of_weighted_score
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
          finiteLogMGF law (staticGap pair) z)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum hstatic_bdd

/--
Randomized scoring source theorem, finite-outcome form, with every per-pair
static boundedness side condition discharged from concrete positive and
negative pivotal atoms.
-/
theorem randomized_scoring_outcome_rate_le_static_of_weighted_score_of_pos_neg_atoms
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
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos : ∀ pair, 0 < staticGap pair (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg : ∀ pair, staticGap pair (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    law weight gap staticGap hstatic hweight hsum
    hmassPos hgapPos hmassNeg hgapNeg

/--
Randomized scoring source theorem, finite-outcome form, for the one-sided
zero-gap boundary: positive zero static-gap probability for every relevant
pair discharges the static boundedness side condition.
-/
theorem randomized_scoring_outcome_rate_le_static_of_weighted_score_of_zero_score_prob_pos
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
    (hzero_pos :
      ∀ pair,
        0 < AppliedModelingLib.pmfProb law (fun signal => staticGap pair signal = 0)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
    law weight gap staticGap hstatic hweight hsum hzero_pos

/--
Actual randomized scoring source theorem, finite-outcome form: the one-voter
mechanism that samples a scoring rule before sampling the signal is weakly
dominated by the static convex-combination scoring rule.
-/
theorem randomized_scoring_actual_outcome_rate_le_static_of_weighted_score
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
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
          finiteLogMGF law (staticGap pair) z)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum hstatic_bdd

/--
Actual randomized scoring source theorem, finite-outcome form, with every
per-pair static boundedness side condition discharged from concrete positive
and negative pivotal atoms.
-/
theorem randomized_scoring_actual_outcome_rate_le_static_of_weighted_score_of_pos_neg_atoms
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos : ∀ pair, 0 < staticGap pair (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg : ∀ pair, staticGap pair (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    law weight gap staticGap hstatic hweight hsum
    hmassPos hgapPos hmassNeg hgapNeg

/--
Actual randomized scoring source theorem, finite-outcome form, for the
one-sided zero-gap boundary.
-/
theorem randomized_scoring_actual_outcome_rate_le_static_of_weighted_score_of_zero_score_prob_pos
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hzero_pos :
      ∀ pair,
        0 < AppliedModelingLib.pmfProb law (fun signal => staticGap pair signal = 0)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
    law weight gap staticGap hstatic hweight hsum hzero_pos

/--
Actual randomized scoring, one-pair comparison to a named finite bound.  This
is the pairwise bridge used by mixed finite/static-boundary aggregate
statements: first compare the randomized pair to the static Chernoff
expression, then compare that static expression to the displayed target rate.
-/
theorem randomized_scoring_actual_pairwise_rate_le_bound_of_weighted_score
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal =
          ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z))
    {targetRate : ℝ}
    (hstatic_le_target :
      finiteChernoffRate law staticGap ≤ targetRate) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) ≤
      targetRate :=
  randomizedScoringActual_pairwiseRate_le_bound_of_weighted_score
    law weight gap staticGap hstatic hweight hsum
    hstatic_bdd hstatic_le_target

/--
Randomized scoring theorem in the paper's prefix-score language: a randomized
finite family of reasonable positional prefix-score rules has a reasonable
static convex-combination rule, and that static rule weakly dominates the
randomized scoring mixture in finite outcome-learning rate.
-/
theorem randomized_scoring_prefix_reasonable_static_and_outcome_rate_le_static_of_pos_neg_atoms
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aNeg pair) < 0) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            randomizedScoringMixtureRate law weight
              (fun rule signal =>
                prefixScoreFromEvent (diff rule) inPrefix (hi pair) signal -
                  prefixScoreFromEvent (diff rule) inPrefix (lo pair) signal)) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (hi pair) signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (lo pair) signal)) :=
  ⟨ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff,
    randomizedScoringPrefix_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
      law weight diff inPrefix hi lo hweight hsum
      hmassPos hgapPos hmassNeg hgapNeg⟩

/--
Actual-law randomized scoring theorem in the paper's prefix-score language: the
randomized one-voter mechanism is weakly dominated in finite outcome-learning
rate by the static convex-combination prefix-score rule.
-/
theorem randomized_scoring_prefix_actual_reasonable_static_and_outcome_rate_le_static_of_pos_neg_atoms
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [DecidableEq Rule]
    [Fintype Cut] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aNeg pair) < 0) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    (hi pair) signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    (lo pair) signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (hi pair) signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (lo pair) signal)) :=
  ⟨ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff,
    randomizedScoringPrefixActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
      law weight diff inPrefix hi lo hweight hsum
      hmassPos hgapPos hmassNeg hgapNeg⟩

/--
Actual-law randomized scoring theorem in the paper's prefix-score language for
the one-sided zero-gap boundary.  The static convex-combination rule is
reasonable, and positive zero static-gap probability for each relevant pair is
enough for the finite-rate comparison.
-/
theorem randomized_scoring_prefix_actual_reasonable_static_and_outcome_rate_le_static_of_zero_score_prob_pos
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [DecidableEq Rule]
    [Fintype Cut] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hzero_pos :
      ∀ pair,
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (hi pair) signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (lo pair) signal = 0)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    (hi pair) signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    (lo pair) signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (hi pair) signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix (lo pair) signal)) :=
  ⟨ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff,
    randomizedScoringPrefixActual_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
      law weight diff inPrefix hi lo hweight hsum hzero_pos⟩

/--
Actual-law prefix-score pairwise comparison to a named finite bound.  This is
the source-language form of the one-pair mixed-aggregate bridge.
-/
theorem randomized_scoring_prefix_actual_pairwise_rate_le_bound_of_weighted_score
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law
          (fun signal =>
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix lo signal) z))
    {targetRate : ℝ}
    (hstatic_le_target :
      finiteChernoffRate law
          (fun signal =>
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix lo signal) ≤
        targetRate) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal =>
          prefixScoreFromEvent (diff signal.1) inPrefix hi signal.2 -
            prefixScoreFromEvent (diff signal.1) inPrefix lo signal.2) ≤
      targetRate :=
  randomizedScoringPrefixActual_pairwiseRate_le_bound_of_weighted_score
    law weight diff inPrefix hi lo hweight hsum
    hstatic_bdd hstatic_le_target

/--
Actual-law prefix-score pairwise comparison to a named finite bound, with the
static boundedness and static bound discharged from the two source boundary
cases that can realize a finite rate: a two-sided Chernoff branch, or a
one-sided zero-gap branch.
-/
theorem randomized_scoring_prefix_actual_pairwise_rate_le_bound_of_source_or_zero_gap
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {targetRate : ℝ}
    (hcase :
      (∃ aPos aNeg : Signal,
        0 < (law aPos).toReal ∧
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix hi aPos -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix lo aPos ∧
          0 < (law aNeg).toReal ∧
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix hi aNeg -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix lo aNeg < 0 ∧
          pairwiseScoringRate law
              (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix hi signal)
              (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix lo signal) ≤
            targetRate) ∨
      (∃ pZero : ℝ,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix lo signal = 0) =
          pZero ∧
        0 < pZero ∧
        -Real.log pZero ≤ targetRate)) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal =>
          prefixScoreFromEvent (diff signal.1) inPrefix hi signal.2 -
            prefixScoreFromEvent (diff signal.1) inPrefix lo signal.2) ≤
      targetRate := by
  let staticGap : Signal → ℝ := fun signal =>
    prefixScoreFromEvent
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
        inPrefix hi signal -
      prefixScoreFromEvent
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
        inPrefix lo signal
  rcases hcase with hsource | hzero
  · rcases hsource with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg,
        hsource_le_target⟩
    have hstatic_bdd :
        BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z) :=
      finiteLogMGF_bddBelow_of_pos_neg_atoms
        law staticGap hmassPos (by simpa [staticGap] using hgapPos)
        hmassNeg (by simpa [staticGap] using hgapNeg)
    have hstatic_le_target :
        finiteChernoffRate law staticGap ≤ targetRate := by
      simpa [staticGap, pairwiseScoringRate, finiteScoreGapChernoffRate] using
        hsource_le_target
    exact
      randomized_scoring_prefix_actual_pairwise_rate_le_bound_of_weighted_score
        law weight diff inPrefix hi lo hweight hsum
        (by simpa [staticGap] using hstatic_bdd)
        (by simpa [staticGap] using hstatic_le_target)
  · rcases hzero with ⟨pZero, hZeroProb, hZero_pos, hzero_le_target⟩
    have hzero_prob_pos :
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal => staticGap signal = 0) := by
      simpa [staticGap, hZeroProb] using hZero_pos
    have hstatic_bdd :
        BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z) :=
      finiteLogMGF_bddBelow_of_zero_score_prob_pos
        law staticGap hzero_prob_pos
    have hstatic_le_zero :
        finiteChernoffRate law staticGap ≤
          -Real.log
            (AppliedModelingLib.pmfProb law (fun signal => staticGap signal = 0)) :=
      finiteChernoffRate_le_neg_log_pmfProb_score_eq_zero
        law staticGap hzero_prob_pos
    have hzero_le_target' :
        -Real.log
            (AppliedModelingLib.pmfProb law (fun signal => staticGap signal = 0)) ≤
          targetRate := by
      simpa [staticGap, hZeroProb] using hzero_le_target
    exact
      randomized_scoring_prefix_actual_pairwise_rate_le_bound_of_weighted_score
        law weight diff inPrefix hi lo hweight hsum
        (by simpa [staticGap] using hstatic_bdd)
        (hstatic_le_zero.trans hzero_le_target')

/--
Randomized scoring theorem over the source W-set boundary pairs: the
convex-combination scoring rule is reasonable, selects the true W-set
asymptotically under Proposition 1 strict dominance, and weakly dominates the
finite outcome-learning rate of the randomized mechanism.
-/
theorem randomized_scoring_prefix_cross_tier_static_selection_and_rate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aNeg pair) < 0) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            randomizedScoringMixtureRate law weight
              (fun rule signal =>
                prefixScoreFromEvent (diff rule) inPrefix pair.hi signal -
                  prefixScoreFromEvent (diff rule) inPrefix pair.lo signal)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) :=
  randomizedScoringPrefix_crossTier_static_selection_and_rate
    law weight diff inPrefix winnerSet hweight hsum hdiff hdom
    hmassPos hgapPos hmassNeg hgapNeg

/--
Actual-law randomized scoring theorem over the source W-set boundary pairs:
the convex-combination scoring rule is reasonable, selects the true W-set
asymptotically under Proposition 1 strict dominance, and weakly dominates the
finite outcome-learning rate of the actual randomized mechanism.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aNeg pair) < 0) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) :=
  randomizedScoringPrefixActual_crossTier_static_selection_and_rate
    law weight diff inPrefix winnerSet hweight hsum hdiff hdom
    hmassPos hgapPos hmassNeg hgapNeg

/--
Source-facing automatic Theorem 1 aggregate endpoint: the randomized scoring
rule's convex-combination static rule is reasonable and asymptotically selects
the true W-set under Proposition 1 strict dominance; its source relevant-pair
error aggregate either has an exact finite exponential rate or is eventually
zero.  This packages the finite-support Proposition 2/4 trichotomy without
requiring callers to classify two-sided and one-sided supports by hand.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((∃ minRate : ℝ,
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0)) :=
  randomizedScoringPrefixActual_crossTier_static_selection_and_automatic_static_aggregate
    law weight diff inPrefix winnerSet hweight hsum hdiff hdom

/--
Source-facing automatic Theorem 1 aggregate endpoint as an extended-rate
statement.  The static convex-combination scoring rule selects the true W-set,
and its relevant-pair error aggregate has a finite rate or extended rate `⊤`
in the eventual-zero boundary case.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_extended_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ∃ rate : WithTop ℝ,
        HasExtendedExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          rate := by
  rcases
      randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_static_aggregate
        law weight diff inPrefix winnerSet hweight hsum hdiff hdom with
    ⟨hreasonable, hselection, haggregate⟩
  refine ⟨hreasonable, hselection, ?_⟩
  rcases haggregate with hfinite | hzero
  · rcases hfinite with ⟨rate, hrate⟩
    exact ⟨(rate : WithTop ℝ),
      HasExtendedExponentialRate.finite hrate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Bundled Theorem 1 endpoint: the convex-combination static rule is reasonable,
selects the true W-set, and has a boundary-aware finite-rate-or-eventually-zero
aggregate.  In the ordinary two-sided finite-rate case, the actual randomized
mechanism's finite outcome-learning rate is weakly dominated by this static
rule's finite outcome-learning rate.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_aggregate_and_rate_comparison_when_two_sided
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((∃ minRate : ℝ,
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0)) ∧
      ((∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) →
        finiteOutcomeLearningRate
            (fun pair : CrossTierPair winnerSet =>
              finiteChernoffRate
                (randomizedScoringSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Signal =>
                  prefixScoreFromEvent (diff signal.1) inPrefix
                      pair.hi signal.2 -
                    prefixScoreFromEvent (diff signal.1) inPrefix
                      pair.lo signal.2)) ≤
          finiteOutcomeLearningRate
            (fun pair : CrossTierPair winnerSet =>
              finiteChernoffRate law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal))) := by
  rcases
      randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_static_aggregate
        law weight diff inPrefix winnerSet hweight hsum hdiff hdom with
    ⟨hreasonable, hselection, haggregate⟩
  refine ⟨hreasonable, hselection, haggregate, ?_⟩
  intro htwoSided
  rcases htwoSided with
    ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
  exact
    (randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
      law weight diff inPrefix winnerSet hweight hsum hdiff hdom
      hmassPos hgapPos hmassNeg hgapNeg).2.2

/--
Randomized scoring one-sided static-boundary companion over the source W-set
boundary pairs: the convex-combination scoring rule is reasonable, selects the
true W-set asymptotically under Proposition 1 strict dominance, and its static
relevant pairwise mistake aggregate is eventually empty.
-/
theorem randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hsupport :
      ∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      (∀ᶠ n in Filter.atTop,
        (∑ pair : CrossTierPair winnerSet,
          finiteScoreGapPairwiseErrorProb law
            (fun candidate =>
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix candidate)
            pair.hi pair.lo n) = 0) := by
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · simpa [staticDiff] using
      finiteRelevantScoreGapAggregateError_eventually_zero_of_support_pos
        (Pair := CrossTierPair winnerSet)
        (law := law)
        (score := fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
        (hi := fun pair : CrossTierPair winnerSet => pair.hi)
        (lo := fun pair : CrossTierPair winnerSet => pair.lo)
        (pairWeight := fun _ => (1 : ℝ))
        hsupport

/--
Randomized scoring one-sided finite-real boundary companion over the source
W-set boundary pairs: the convex-combination scoring rule is reasonable,
selects the true W-set asymptotically under Proposition 1 strict dominance,
and its static relevant pairwise mistake aggregate has exact rate determined
by the zero-gap probabilities.
-/
theorem randomized_scoring_prefix_cross_tier_static_selection_and_zero_gap_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (pZero : CrossTierPair winnerSet → ℝ)
    {minRate : ℝ}
    (pairMin : CrossTierPair winnerSet)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hsupport :
      ∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 ≤
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)
    (hZeroProb :
      ∀ pair : CrossTierPair winnerSet,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair : CrossTierPair winnerSet, 0 < pZero pair)
    (hrate_min : -Real.log (pZero pairMin) = minRate)
    (hrate_ge :
      ∀ pair : CrossTierPair winnerSet, minRate ≤ -Real.log (pZero pair)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo sampleSize)
        minRate := by
  classical
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · have hrate :
        HasExponentialRate
          (((proposition4_relevant_pair_rate_certificate_from_support_nonneg_zero_gap_prob
              (Pair := CrossTierPair winnerSet)
              law
              (fun candidate =>
                prefixScoreFromEvent staticDiff inPrefix candidate)
              (fun pair : CrossTierPair winnerSet => pair.hi)
              (fun pair : CrossTierPair winnerSet => pair.lo)
              pZero
              (by simpa [staticDiff] using hsupport)
              (by simpa [staticDiff] using hZeroProb)
              hZero_pos)
            |>.aggregateError (fun _ => (1 : ℝ))))
          minRate :=
      proposition4_outcome_error_exact_rate_from_support_nonneg_zero_gap_prob_relevant_pairs
        (Pair := CrossTierPair winnerSet)
        law
        (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        pZero
        (by simpa [staticDiff] using hsupport)
        (by simpa [staticDiff] using hZeroProb)
        hZero_pos
        (pairWeight := fun _ => (1 : ℝ))
        (minRate := minRate)
        (by intro pair; norm_num)
        pairMin
        (by norm_num)
        hrate_min hrate_ge
    simpa [staticDiff,
      proposition4_relevant_pair_rate_certificate_from_support_nonneg_zero_gap_prob,
      finiteScoreGapRelevantPairRateCertificate_of_support_nonneg_zero_gap_prob]
      using hrate

/--
Actual-law randomized scoring one-sided finite-real boundary companion over the
source W-set boundary pairs.  In addition to the exact static aggregate rate
from the zero-gap probabilities, the actual randomized mechanism's finite
outcome-learning rate is bounded by that same static rate.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_zero_gap_static_aggregate_and_rate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (pZero : CrossTierPair winnerSet → ℝ)
    {minRate : ℝ}
    (pairMin : CrossTierPair winnerSet)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hsupport :
      ∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 ≤
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)
    (hZeroProb :
      ∀ pair : CrossTierPair winnerSet,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair : CrossTierPair winnerSet, 0 < pZero pair)
    (hrate_min : -Real.log (pZero pairMin) = minRate)
    (hrate_ge :
      ∀ pair : CrossTierPair winnerSet, minRate ≤ -Real.log (pZero pair)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo sampleSize)
        minRate ∧
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        minRate := by
  classical
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  rcases
      randomized_scoring_prefix_cross_tier_static_selection_and_zero_gap_static_aggregate
        law weight diff inPrefix winnerSet pZero pairMin
        hweight hsum hdiff hdom hsupport hZeroProb hZero_pos
        hrate_min hrate_ge with
    ⟨hreasonable, hselection, hstatic_rate⟩
  rcases
      randomized_scoring_prefix_actual_reasonable_static_and_outcome_rate_le_static_of_zero_score_prob_pos
        (Pair := CrossTierPair winnerSet)
        law weight diff inPrefix
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        hweight hsum hdiff
        (by
          intro pair
          rw [hZeroProb pair]
          exact hZero_pos pair) with
    ⟨_hreasonable_again, hrate_to_chernoff⟩
  have hchernoff_to_zero :
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
                  prefixScoreFromEvent staticDiff inPrefix pair.lo signal)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet => -Real.log (pZero pair)) := by
    refine finiteOutcomeLearningRate_mono ?_
    intro pair
    have hzero_prob_pos :
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
                prefixScoreFromEvent staticDiff inPrefix pair.lo signal = 0) := by
      simpa [staticDiff, hZeroProb pair] using hZero_pos pair
    simpa [staticDiff, hZeroProb pair] using
      finiteChernoffRate_le_neg_log_pmfProb_score_eq_zero
        law
        (fun signal =>
          prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
            prefixScoreFromEvent staticDiff inPrefix pair.lo signal)
        hzero_prob_pos
  have hzero_min :
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet => -Real.log (pZero pair)) =
        minRate :=
    finiteOutcomeLearningRate_eq_of_min_pair
      (fun pair : CrossTierPair winnerSet => -Real.log (pZero pair))
      pairMin hrate_min hrate_ge
  refine ⟨hreasonable, hselection, hstatic_rate, ?_⟩
  calc
    finiteOutcomeLearningRate
        (fun pair : CrossTierPair winnerSet =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal =>
              prefixScoreFromEvent (diff signal.1) inPrefix
                  pair.hi signal.2 -
                prefixScoreFromEvent (diff signal.1) inPrefix
                  pair.lo signal.2))
        ≤ finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
                  prefixScoreFromEvent staticDiff inPrefix pair.lo signal)) := by
          simpa [staticDiff] using hrate_to_chernoff
    _ ≤ finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet => -Real.log (pZero pair)) :=
          hchernoff_to_zero
    _ = minRate := hzero_min

/--
Randomized scoring mixed finite-rate static-aggregate companion over the
source W-set boundary pairs: the convex-combination scoring rule is
reasonable, selects the true W-set asymptotically under Proposition 1 strict
dominance, and its static relevant pairwise mistake aggregate has the exact
finite rate `minRate` when each relevant pair is either certified at a finite
rate at least `minRate` or eventually zero.
-/
theorem randomized_scoring_prefix_cross_tier_static_selection_and_mixed_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    {minRate : ℝ}
    (pairMin : CrossTierPair winnerSet)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hpairMin_exact :
      ExponentialRateCertificate
        (finiteScoreGapPairwiseErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          pairMin.hi pairMin.lo)
        minRate)
    (hsource_rate_ge :
      ∀ pair : CrossTierPair winnerSet,
        minRate ≤
          pairwiseScoringRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal)
            (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hzero_rate_ge :
      ∀ pair : CrossTierPair winnerSet, ∀ pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo sampleSize)
        minRate := by
  classical
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · have hrate :
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              (1 : ℝ) *
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent staticDiff inPrefix candidate)
                  pair.hi pair.lo sampleSize)
          minRate :=
      proposition4_outcome_error_exact_rate_from_relevant_pairs_finite_support_exact_or_boundary_or_eventually_zero
        (Pair := CrossTierPair winnerSet)
        law
        (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        (by simpa [staticDiff] using hmean)
        (pairWeight := fun _ => (1 : ℝ))
        (minRate := minRate)
        (by intro pair; norm_num)
        pairMin
        (by norm_num)
        (by simpa [staticDiff] using hpairMin_exact)
        (by simpa [staticDiff] using hsource_rate_ge)
        (by simpa [staticDiff] using hzero_rate_ge)
    simpa [staticDiff] using hrate

/--
Actual-law mixed finite-rate companion with an explicit minimizing-pair
comparison.  Once the mixed static aggregate has exact rate `minRate`, it is
enough to show that the actual randomized pairwise Chernoff rate at the same
minimizing pair is at most `minRate`; the finite outcome-learning rate then
inherits that bound.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_mixed_static_aggregate_and_min_pair_rate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    {minRate : ℝ}
    (pairMin : CrossTierPair winnerSet)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hpairMin_exact :
      ExponentialRateCertificate
        (finiteScoreGapPairwiseErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          pairMin.hi pairMin.lo)
        minRate)
    (hsource_rate_ge :
      ∀ pair : CrossTierPair winnerSet,
        minRate ≤
          pairwiseScoringRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal)
            (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hzero_rate_ge :
      ∀ pair : CrossTierPair winnerSet, ∀ pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero)
    (hmin_pair_compare :
      finiteChernoffRate
          (randomizedScoringSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Signal =>
            prefixScoreFromEvent (diff signal.1) inPrefix
                pairMin.hi signal.2 -
              prefixScoreFromEvent (diff signal.1) inPrefix
                pairMin.lo signal.2) ≤
        minRate) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo sampleSize)
        minRate ∧
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        minRate := by
  rcases
      randomized_scoring_prefix_cross_tier_static_selection_and_mixed_static_aggregate
        law weight diff inPrefix winnerSet pairMin
        hweight hsum hdiff hdom hmean hpairMin_exact
        hsource_rate_ge hzero_rate_ge with
    ⟨hreasonable, hselection, hstatic_rate⟩
  refine ⟨hreasonable, hselection, hstatic_rate, ?_⟩
  exact
    (finiteOutcomeLearningRate_le
      (fun pair : CrossTierPair winnerSet =>
        finiteChernoffRate
          (randomizedScoringSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Signal =>
            prefixScoreFromEvent (diff signal.1) inPrefix
                pair.hi signal.2 -
              prefixScoreFromEvent (diff signal.1) inPrefix
                pair.lo signal.2))
      pairMin).trans hmin_pair_compare

/--
Actual-law mixed finite-rate companion with the minimizing-pair comparison
discharged from the source finite branch or the one-sided zero-gap branch.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_mixed_static_aggregate_and_rate_from_min_pair_source_or_zero_gap
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    {minRate : ℝ}
    (pairMin : CrossTierPair winnerSet)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hpairMin_exact :
      ExponentialRateCertificate
        (finiteScoreGapPairwiseErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          pairMin.hi pairMin.lo)
        minRate)
    (hsource_rate_ge :
      ∀ pair : CrossTierPair winnerSet,
        minRate ≤
          pairwiseScoringRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal)
            (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))
    (hzero_rate_ge :
      ∀ pair : CrossTierPair winnerSet, ∀ pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero)
    (hpairMin_source_or_zero :
      (∃ aPos aNeg : Signal,
        0 < (law aPos).toReal ∧
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pairMin.hi aPos -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pairMin.lo aPos ∧
          0 < (law aNeg).toReal ∧
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pairMin.hi aNeg -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pairMin.lo aNeg < 0 ∧
          pairwiseScoringRate law
              (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.hi signal)
              (fun signal =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.lo signal) ≤
            minRate) ∨
      (∃ pZero : ℝ,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.lo signal = 0) =
          pZero ∧
        0 < pZero ∧
        -Real.log pZero ≤ minRate)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo sampleSize)
        minRate ∧
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        minRate := by
  have hmin_pair_compare :
      finiteChernoffRate
          (randomizedScoringSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Signal =>
            prefixScoreFromEvent (diff signal.1) inPrefix
                pairMin.hi signal.2 -
              prefixScoreFromEvent (diff signal.1) inPrefix
                pairMin.lo signal.2) ≤
        minRate :=
    randomized_scoring_prefix_actual_pairwise_rate_le_bound_of_source_or_zero_gap
      law weight diff inPrefix pairMin.hi pairMin.lo hweight hsum
      hpairMin_source_or_zero
  exact
    randomized_scoring_prefix_actual_cross_tier_static_selection_and_mixed_static_aggregate_and_min_pair_rate
      law weight diff inPrefix winnerSet pairMin
      hweight hsum hdiff hdom hmean hpairMin_exact
      hsource_rate_ge hzero_rate_ge hmin_pair_compare

/--
Actual-law randomized scoring wrapper with automatic static-aggregate
trichotomy.  The two-sided branch gives the usual randomized-vs-static
finite-rate comparison.  Otherwise, nonnegative expected static score gaps on
the W-set boundary pairs are enough to conclude that the static relevant
pairwise aggregate either has some exact finite rate or is eventually zero.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_trichotomy_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal))) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal))) ∨
        ((∃ minRate : ℝ,
          HasExponentialRate
            (fun sampleSize =>
              ∑ pair : CrossTierPair winnerSet,
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix candidate)
                  pair.hi pair.lo sampleSize)
            minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0))) := by
  rcases hcase with htwoSided | hmean
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hrate⟩
    exact ⟨hreasonable, hselection, Or.inl hrate⟩
  · classical
    let staticDiff : Cut → ℝ :=
      fun cut => ∑ rule : Rule, weight rule * diff rule cut
    have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
      ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
    have hagg :
        (∃ minRate : ℝ,
          HasExponentialRate
            (fun sampleSize =>
              ∑ pair : CrossTierPair winnerSet,
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent staticDiff inPrefix candidate)
                  pair.hi pair.lo sampleSize)
            minRate) ∨
          (∀ᶠ sampleSize in Filter.atTop,
            (∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent staticDiff inPrefix candidate)
                pair.hi pair.lo sampleSize) = 0) := by
      simpa [staticDiff] using
        proposition4_outcome_error_exact_rate_or_eventually_zero_from_relevant_pairs_finite_support_trichotomy
          (Pair := CrossTierPair winnerSet)
          law
          (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
          (fun pair : CrossTierPair winnerSet => pair.hi)
          (fun pair : CrossTierPair winnerSet => pair.lo)
          (by simpa [staticDiff] using hmean)
          (pairWeight := fun _ => (1 : ℝ))
          (by intro pair; norm_num)
          (by intro pair; norm_num)
    refine ⟨hstatic_reasonable, ?_, ?_⟩
    · simpa [staticDiff] using
        prefixScoringCanonicalSelectionError_tendsto_zero_on
          law staticDiff inPrefix winnerSet hdom hstatic_reasonable
    · rcases hagg with hfinite | hzero
      · exact Or.inr (Or.inl hfinite)
      · exact Or.inr (Or.inr (by simpa [staticDiff] using hzero))

/--
Actual-law randomized scoring theorem over source W-set boundary pairs, with
the finite-real/boundary split made explicit.  In the two-sided finite-real
case, the actual randomized mechanism is weakly dominated in finite
outcome-learning rate by the convex-combination static rule.  In the one-sided
static-boundary case, the static relevant pairwise mistake aggregate is
eventually empty instead of having a finite real rate.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_eventually_zero_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal))) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0)) := by
  rcases hcase with htwoSided | hsupport
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hrate⟩
    exact ⟨hreasonable, hselection, Or.inl hrate⟩
  · rcases
        randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hsupport with
      ⟨hreasonable, hselection, heventually⟩
    exact ⟨hreasonable, hselection, Or.inr heventually⟩

/--
Actual-law randomized scoring theorem over source W-set boundary pairs, with
the finite-real trichotomy made explicit.  The two-sided case gives the usual
randomized-vs-static finite-rate comparison; the one-sided zero-gap case gives
an exact finite real rate for the static aggregate; the strict one-sided case
is eventually error-free.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_zero_gap_or_eventually_zero_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∃ (pZero : CrossTierPair winnerSet → ℝ) (minRate : ℝ)
          (pairMin : CrossTierPair winnerSet),
        (∀ pair : CrossTierPair winnerSet,
          ∀ signal, 0 < (law signal).toReal →
            0 ≤
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo signal) ∧
          (∀ pair : CrossTierPair winnerSet,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal = 0) =
              pZero pair) ∧
          (∀ pair : CrossTierPair winnerSet, 0 < pZero pair) ∧
          -Real.log (pZero pairMin) = minRate ∧
          (∀ pair : CrossTierPair winnerSet,
            minRate ≤ -Real.log (pZero pair))) ∨
      (∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal))) ∨
        ((∃ minRate : ℝ,
          HasExponentialRate
            (fun sampleSize =>
              ∑ pair : CrossTierPair winnerSet,
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix candidate)
                  pair.hi pair.lo sampleSize)
            minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0))) := by
  rcases hcase with htwoSided | hboundary
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hrate⟩
    exact ⟨hreasonable, hselection, Or.inl hrate⟩
  · rcases hboundary with hzero | hsupport
    · rcases hzero with
        ⟨pZero, minRate, pairMin, hsupport_nonneg, hZeroProb,
          hZero_pos, hrate_min, hrate_ge⟩
      rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_zero_gap_static_aggregate
            law weight diff inPrefix winnerSet pZero pairMin
            hweight hsum hdiff hdom hsupport_nonneg hZeroProb hZero_pos
            hrate_min hrate_ge with
        ⟨hreasonable, hselection, hrate⟩
      exact ⟨hreasonable, hselection, Or.inr (Or.inl ⟨minRate, hrate⟩)⟩
    · rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
            law weight diff inPrefix winnerSet hweight hsum hdiff hdom
            hsupport with
        ⟨hreasonable, hselection, heventually⟩
      exact ⟨hreasonable, hselection, Or.inr (Or.inr heventually)⟩

/--
Actual-law randomized scoring theorem over source W-set boundary pairs, with a
mixed finite/boundary static-aggregate branch.  The two-sided case gives the
usual randomized-vs-static finite-rate comparison; the mixed case gives an
exact finite real rate for the static aggregate even when different relevant
pairs use different Proposition 2 trichotomy branches; the strict one-sided
case is eventually error-free.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_mixed_static_aggregate_or_eventually_zero_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∃ (minRate : ℝ) (pairMin : CrossTierPair winnerSet),
        (∀ pair : CrossTierPair winnerSet,
          0 ≤
            AppliedModelingLib.pmfExp law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) ∧
          ExponentialRateCertificate
            (finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pairMin.hi pairMin.lo)
            minRate ∧
          (∀ pair : CrossTierPair winnerSet,
            minRate ≤
              pairwiseScoringRate law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal)
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal)) ∧
          (∀ pair : CrossTierPair winnerSet, ∀ pZero,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal = 0) =
              pZero →
            0 < pZero →
              minRate ≤ -Real.log pZero)) ∨
      (∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal))) ∨
        ((∃ minRate : ℝ,
          HasExponentialRate
            (fun sampleSize =>
              ∑ pair : CrossTierPair winnerSet,
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix candidate)
                  pair.hi pair.lo sampleSize)
            minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0))) := by
  rcases hcase with htwoSided | hboundary
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hrate⟩
    exact ⟨hreasonable, hselection, Or.inl hrate⟩
  · rcases hboundary with hmixed | hsupport
    · rcases hmixed with
        ⟨minRate, pairMin, hmean, hpairMin_exact,
          hsource_rate_ge, hzero_rate_ge⟩
      rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_mixed_static_aggregate
            law weight diff inPrefix winnerSet pairMin
            hweight hsum hdiff hdom hmean hpairMin_exact
            hsource_rate_ge hzero_rate_ge with
        ⟨hreasonable, hselection, hrate⟩
      exact ⟨hreasonable, hselection, Or.inr (Or.inl ⟨minRate, hrate⟩)⟩
    · rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
            law weight diff inPrefix winnerSet hweight hsum hdiff hdom
            hsupport with
        ⟨hreasonable, hselection, heventually⟩
      exact ⟨hreasonable, hselection, Or.inr (Or.inr heventually)⟩

/--
Actual-law randomized scoring theorem over source W-set boundary pairs, with
comparison-capable finite branches.  The two-sided branch gives the usual
randomized-vs-static finite-rate comparison; the mixed branch gives an exact
static aggregate rate together with a randomized bound to that rate once the
minimizing pair is classified as source-finite or zero-gap finite; the strict
one-sided branch is eventually error-free.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate_or_mixed_static_aggregate_rate_or_eventually_zero_static_aggregate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∃ (minRate : ℝ) (pairMin : CrossTierPair winnerSet),
        (∀ pair : CrossTierPair winnerSet,
          0 ≤
            AppliedModelingLib.pmfExp law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) ∧
          ExponentialRateCertificate
            (finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pairMin.hi pairMin.lo)
            minRate ∧
          (∀ pair : CrossTierPair winnerSet,
            minRate ≤
              pairwiseScoringRate law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal)
                (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal)) ∧
          (∀ pair : CrossTierPair winnerSet, ∀ pZero,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal = 0) =
              pZero →
            0 < pZero →
              minRate ≤ -Real.log pZero) ∧
          ((∃ aPos aNeg : Signal,
            0 < (law aPos).toReal ∧
              0 <
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pairMin.hi aPos -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pairMin.lo aPos ∧
              0 < (law aNeg).toReal ∧
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.hi aNeg -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.lo aNeg < 0 ∧
              pairwiseScoringRate law
                  (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.hi signal)
                  (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.lo signal) ≤
                minRate) ∨
          (∃ pZero : ℝ,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.lo signal = 0) =
              pZero ∧
            0 < pZero ∧
            -Real.log pZero ≤ minRate))) ∨
      (∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal))) ∨
        ((∃ minRate : ℝ,
          HasExponentialRate
            (fun sampleSize =>
              ∑ pair : CrossTierPair winnerSet,
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix candidate)
                  pair.hi pair.lo sampleSize)
            minRate ∧
          finiteOutcomeLearningRate
              (fun pair : CrossTierPair winnerSet =>
                finiteChernoffRate
                  (randomizedScoringSamplingLaw law weight hweight hsum)
                  (fun signal : Rule × Signal =>
                    prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.hi signal.2 -
                      prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.lo signal.2)) ≤
            minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0))) := by
  rcases hcase with htwoSided | hboundary
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hrate⟩
    exact ⟨hreasonable, hselection, Or.inl hrate⟩
  · rcases hboundary with hmixed | hsupport
    · rcases hmixed with
        ⟨minRate, pairMin, hmean, hpairMin_exact,
          hsource_rate_ge, hzero_rate_ge, hpairMin_case⟩
      rcases
          randomized_scoring_prefix_actual_cross_tier_static_selection_and_mixed_static_aggregate_and_rate_from_min_pair_source_or_zero_gap
            law weight diff inPrefix winnerSet pairMin
            hweight hsum hdiff hdom hmean hpairMin_exact
            hsource_rate_ge hzero_rate_ge hpairMin_case with
        ⟨hreasonable, hselection, hrate, hcompare⟩
      exact ⟨hreasonable, hselection,
        Or.inr (Or.inl ⟨minRate, hrate, hcompare⟩)⟩
    · rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
            law weight diff inPrefix winnerSet hweight hsum hdiff hdom
            hsupport with
        ⟨hreasonable, hselection, heventually⟩
      exact ⟨hreasonable, hselection, Or.inr (Or.inr heventually)⟩

/--
Actual-law randomized scoring theorem over source W-set boundary pairs, stated
as one extended-rate comparison.  The convex-combination static rule is
reasonable and selects the true W-set.  Its static relevant-pair error
aggregate has a source-facing extended rate, and the actual randomized
finite outcome-learning rate is weakly below that extended static rate.  In
finite branches this is the usual real-valued comparison; in the strict
one-sided branch the static rate is `⊤`.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_extended_static_rate_comparison
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hcase :
      (∃ aPos aNeg : CrossTierPair winnerSet → Signal,
        (∀ pair, 0 < (law (aPos pair)).toReal) ∧
          (∀ pair,
            0 <
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aPos pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aPos pair)) ∧
          (∀ pair, 0 < (law (aNeg pair)).toReal) ∧
          (∀ pair,
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.hi (aNeg pair) -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pair.lo (aNeg pair) < 0)) ∨
      (∃ (minRate : ℝ) (pairMin : CrossTierPair winnerSet),
        (∀ pair : CrossTierPair winnerSet,
          0 ≤
            AppliedModelingLib.pmfExp law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) ∧
          ExponentialRateCertificate
            (finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pairMin.hi pairMin.lo)
            minRate ∧
          (∀ pair : CrossTierPair winnerSet,
            minRate ≤
              pairwiseScoringRate law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal)
                (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal)) ∧
          (∀ pair : CrossTierPair winnerSet, ∀ pZero,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal = 0) =
              pZero →
            0 < pZero →
              minRate ≤ -Real.log pZero) ∧
          ((∃ aPos aNeg : Signal,
            0 < (law aPos).toReal ∧
              0 <
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pairMin.hi aPos -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pairMin.lo aPos ∧
              0 < (law aNeg).toReal ∧
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.hi aNeg -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix pairMin.lo aNeg < 0 ∧
              pairwiseScoringRate law
                  (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.hi signal)
                  (fun signal =>
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.lo signal) ≤
                minRate) ∨
          (∃ pZero : ℝ,
            AppliedModelingLib.pmfProb law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pairMin.lo signal = 0) =
              pZero ∧
            0 < pZero ∧
            -Real.log pZero ≤ minRate))) ∨
      (∀ pair : CrossTierPair winnerSet,
        ∀ signal, 0 < (law signal).toReal →
          0 <
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ∃ staticRate : WithTop ℝ,
        HasExtendedExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          staticRate ∧
          ((finiteOutcomeLearningRate
              (fun pair : CrossTierPair winnerSet =>
                finiteChernoffRate
                  (randomizedScoringSamplingLaw law weight hweight hsum)
                  (fun signal : Rule × Signal =>
                    prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.hi signal.2 -
                      prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.lo signal.2)) : WithTop ℝ) ≤
            staticRate) := by
  rcases hcase with htwoSided | hboundary
  · rcases htwoSided with
      ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg⟩
    let staticDiff : Cut → ℝ :=
      fun cut => ∑ rule : Rule, weight rule * diff rule cut
    have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
      ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
    have hmean :
        ∀ pair : CrossTierPair winnerSet,
          0 ≤
            AppliedModelingLib.pmfExp law
              (fun signal =>
                prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
                  prefixScoreFromEvent staticDiff inPrefix pair.lo signal) := by
      intro pair
      exact le_of_lt
        (pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
          law staticDiff inPrefix
          (hdom pair.hi pair.lo ⟨pair.hi_mem, pair.lo_not_mem⟩)
          hstatic_reasonable)
    rcases
        randomized_scoring_prefix_actual_cross_tier_static_selection_and_rate
          law weight diff inPrefix winnerSet hweight hsum hdiff hdom
          hmassPos hgapPos hmassNeg hgapNeg with
      ⟨hreasonable, hselection, hcompare⟩
    have hstatic_rate :
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          (finiteOutcomeLearningRate
            (fun pair : CrossTierPair winnerSet =>
              finiteChernoffRate law
                (fun signal =>
                  prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.hi signal -
                    prefixScoreFromEvent
                      (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                      inPrefix pair.lo signal))) := by
      simpa [staticDiff, pairwiseScoringRate, finiteScoreGapChernoffRate,
        finiteIidPairwiseScoreGapChernoffRate] using
        proposition4_cross_tier_outcome_error_exact_rate_from_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
          law
          (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
          winnerSet
          hmean aPos aNeg
          (by simpa [staticDiff] using hmassPos)
          (by simpa [staticDiff] using hgapPos)
          (by simpa [staticDiff] using hmassNeg)
          (by simpa [staticDiff] using hgapNeg)
    refine ⟨hreasonable, hselection, ?_⟩
    refine ⟨(finiteOutcomeLearningRate
      (fun pair : CrossTierPair winnerSet =>
        finiteChernoffRate law
          (fun signal =>
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix pair.lo signal)) : WithTop ℝ), ?_, ?_⟩
    · exact HasExtendedExponentialRate.finite hstatic_rate
    · exact WithTop.coe_le_coe.2 hcompare
  · rcases hboundary with hmixed | hsupport
    · rcases hmixed with
        ⟨minRate, pairMin, hmean, hpairMin_exact,
          hsource_rate_ge, hzero_rate_ge, hpairMin_case⟩
      rcases
          randomized_scoring_prefix_actual_cross_tier_static_selection_and_mixed_static_aggregate_and_rate_from_min_pair_source_or_zero_gap
            law weight diff inPrefix winnerSet pairMin
            hweight hsum hdiff hdom hmean hpairMin_exact
            hsource_rate_ge hzero_rate_ge hpairMin_case with
        ⟨hreasonable, hselection, hstatic_rate, hcompare⟩
      refine ⟨hreasonable, hselection, ?_⟩
      exact ⟨(minRate : WithTop ℝ),
        HasExtendedExponentialRate.finite hstatic_rate,
        WithTop.coe_le_coe.2 hcompare⟩
    · rcases
          randomized_scoring_prefix_cross_tier_static_selection_and_eventually_zero_static_aggregate
            law weight diff inPrefix winnerSet hweight hsum hdiff hdom
            hsupport with
        ⟨hreasonable, hselection, heventually⟩
      refine ⟨hreasonable, hselection, ?_⟩
      exact ⟨⊤, HasExtendedExponentialRate.infinite heventually, le_top⟩

/--
Paper-facing static-dominance proposition for Theorem
`lem:randomizebetterscoring`.  It states that the convex-combination static
scoring rule has an extended finite-outcome error rate that weakly dominates
the randomized scoring mixture, without exposing the randomized product sample
space or the selected extended-rate witness in the review-surface theorem.
-/
def randomizedScoringPrefixStaticDominatesRandomized
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) : Prop :=
  ∃ staticRate : WithTop ℝ,
    HasExtendedExponentialRate
      (fun sampleSize =>
        ∑ pair : CrossTierPair winnerSet,
          finiteScoreGapPairwiseErrorProb law
            (fun candidate =>
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix candidate)
            pair.hi pair.lo sampleSize)
      staticRate ∧
      ((finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) : WithTop ℝ) ≤
        staticRate)

/--
Automatic actual-law randomized scoring theorem over source W-set boundary
pairs, stated as one extended-rate comparison.  Unlike the branch-split
wrapper above, this theorem does not ask the caller to identify the finite
static minimizing pair.  The finite-support Proposition 2 trichotomy supplies
per-pair exact-rate certificates together with the randomized-pair comparison
to the same finite rate; finite aggregation then selects the pivotal static
pair internally.  If every static relevant-pair error is eventually zero, the
static extended rate is `⊤`.
-/
theorem randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_extended_static_rate_comparison
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ∃ staticRate : WithTop ℝ,
        HasExtendedExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          staticRate ∧
          ((finiteOutcomeLearningRate
              (fun pair : CrossTierPair winnerSet =>
                finiteChernoffRate
                  (randomizedScoringSamplingLaw law weight hweight hsum)
                  (fun signal : Rule × Signal =>
                    prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.hi signal.2 -
                      prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.lo signal.2)) : WithTop ℝ) ≤
            staticRate) := by
  classical
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  let staticScore : Candidate → Signal → ℝ :=
    fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate
  let staticError : CrossTierPair winnerSet → ℕ → ℝ :=
    fun pair sampleSize =>
      finiteScoreGapPairwiseErrorProb law staticScore
        pair.hi pair.lo sampleSize
  let randomizedPairRate : CrossTierPair winnerSet → ℝ :=
    fun pair =>
      finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal =>
          prefixScoreFromEvent (diff signal.1) inPrefix
              pair.hi signal.2 -
            prefixScoreFromEvent (diff signal.1) inPrefix
              pair.lo signal.2)
  have hreasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  have hselection :
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent staticDiff inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) := by
    exact
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hreasonable
  have hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              staticScore pair.hi signal - staticScore pair.lo signal) := by
    intro pair
    exact le_of_lt
      (pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
        law staticDiff inPrefix
        (hdom pair.hi pair.lo ⟨pair.hi_mem, pair.lo_not_mem⟩)
        hreasonable)
  have hcase_payload :
      ∀ pair : CrossTierPair winnerSet,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (staticError pair) rate_i ∧
            randomizedPairRate pair ≤ rate_i) ∨
          (∀ᶠ n in Filter.atTop, staticError pair n = 0) := by
    intro pair
    rcases
        pairwiseScoringError_source_or_zero_certificate_or_eventually_zero_of_mean_nonneg
          law (staticScore pair.hi) (staticScore pair.lo)
          (hmean pair) with
      hsource | hboundary
    · rcases hsource with
        ⟨aPos, aNeg, hmassPos, hgapPos, hmassNeg, hgapNeg, hcert⟩
      left
      refine
        ⟨pairwiseScoringRate law (staticScore pair.hi) (staticScore pair.lo),
          ?_, ?_⟩
      · simpa [staticError, staticScore] using hcert
      · have hstatic_bdd :
            BddBelow (Set.range fun z : ℝ =>
              finiteLogMGF law
                (fun signal =>
                  staticScore pair.hi signal -
                    staticScore pair.lo signal) z) :=
          finiteLogMGF_bddBelow_of_pos_neg_atoms
            law
            (fun signal =>
              staticScore pair.hi signal - staticScore pair.lo signal)
            hmassPos hgapPos hmassNeg hgapNeg
        have hstatic_le :
            finiteChernoffRate law
                (fun signal =>
                  staticScore pair.hi signal -
                    staticScore pair.lo signal) ≤
              pairwiseScoringRate law
                (staticScore pair.hi) (staticScore pair.lo) := by
          rfl
        simpa [randomizedPairRate, staticScore, staticDiff,
          pairwiseScoringRate, finiteScoreGapChernoffRate] using
          randomizedScoringPrefixActual_pairwiseRate_le_bound_of_weighted_score
            law weight diff inPrefix pair.hi pair.lo hweight hsum
            hstatic_bdd hstatic_le
    · rcases hboundary with hzero | hstrict
      · rcases hzero with ⟨pZero, hZeroProb, hZero_pos, hcert⟩
        left
        refine ⟨-Real.log pZero, ?_, ?_⟩
        · simpa [staticError, staticScore] using hcert
        · have hzero_prob_pos :
              0 <
                AppliedModelingLib.pmfProb law
                  (fun signal =>
                    staticScore pair.hi signal -
                      staticScore pair.lo signal = 0) := by
            rw [hZeroProb]
            exact hZero_pos
          have hstatic_bdd :
              BddBelow (Set.range fun z : ℝ =>
                finiteLogMGF law
                  (fun signal =>
                    staticScore pair.hi signal -
                      staticScore pair.lo signal) z) :=
            finiteLogMGF_bddBelow_of_zero_score_prob_pos
              law
              (fun signal =>
                staticScore pair.hi signal - staticScore pair.lo signal)
              hzero_prob_pos
          have hstatic_le :
              finiteChernoffRate law
                  (fun signal =>
                    staticScore pair.hi signal -
                      staticScore pair.lo signal) ≤
                -Real.log pZero := by
            simpa [hZeroProb] using
              finiteChernoffRate_le_neg_log_pmfProb_score_eq_zero
                law
                (fun signal =>
                  staticScore pair.hi signal - staticScore pair.lo signal)
                hzero_prob_pos
          simpa [randomizedPairRate, staticScore, staticDiff] using
            randomizedScoringPrefixActual_pairwiseRate_le_bound_of_weighted_score
              law weight diff inPrefix pair.hi pair.lo hweight hsum
              hstatic_bdd hstatic_le
      · right
        simpa [staticError, staticScore] using hstrict
  rcases
      finite_weighted_sum_hasExponentialRate_with_min_component_payload_or_eventually_zero_of_cert_or_eventually_zero
        (payload := fun pair rate => randomizedPairRate pair ≤ rate)
        (p := staticError) (weight := fun _ : CrossTierPair winnerSet => (1 : ℝ))
        (by intro pair; norm_num)
        (by intro pair; norm_num)
        hcase_payload with
    hfinite | hzero
  · rcases hfinite with
      ⟨pairMin, minRate, _hmin_cert, hmin_compare, _hcase_ge,
        hstatic_rate⟩
    have houtcome_compare :
        finiteOutcomeLearningRate randomizedPairRate ≤ minRate :=
      (finiteOutcomeLearningRate_le randomizedPairRate pairMin).trans
        hmin_compare
    refine ⟨by simpa [staticDiff] using hreasonable, ?_, ?_⟩
    · simpa [staticDiff] using hselection
    · refine ⟨(minRate : WithTop ℝ), ?_, ?_⟩
      · exact HasExtendedExponentialRate.finite
          (by
            simpa [staticError, staticScore, staticDiff] using hstatic_rate)
      · simpa [randomizedPairRate, staticDiff] using
          WithTop.coe_le_coe.2 houtcome_compare
  · refine ⟨by simpa [staticDiff] using hreasonable, ?_, ?_⟩
    · simpa [staticDiff] using hselection
    · refine ⟨⊤, ?_, le_top⟩
      exact HasExtendedExponentialRate.infinite
        (by simpa [staticError, staticScore, staticDiff] using hzero)

/--
Randomized K-approval comparison: after the source convexity calculation bounds
the randomized pairwise rate by the weighted average of the static K-approval
rates, one static K-approval rule weakly beats the randomized rule for that
pair.
-/
theorem randomized_approval_pairwise_rate_le_static_of_convexity
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hconvex :
      approvalPairwiseRate mixedUp mixedDown ≤
        ∑ rule : Rule,
          weight rule * approvalPairwiseRate (pUp rule) (pDown rule)) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) :=
  randomizedApproval_pairwiseRate_le_static_of_convexity
    weight pUp pDown hmixedUp hmixedDown hweight hsum hconvex

/--
K-approval no-randomization pairwise theorem on the positive-base region:
some static K-approval rule weakly beats the randomized K-approval rule for the
pair.
-/
theorem randomized_approval_pairwise_rate_le_static
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) :=
  randomizedApproval_pairwiseRate_le_static
    weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
    hbase_pos hmixed_base_pos

/--
Source-shaped fixed-pair K-approval no-randomization theorem over valid
approval probabilities: either some static rule weakly beats the randomized
pairwise closed-form rate, or Lean identifies a degenerate static boundary
rule outside the positive-base real-rate Jensen argument.
-/
theorem randomized_approval_pairwise_rate_le_static_of_valid_probabilities_or_static_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1) :
    (∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) :=
  randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
    weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown hprob

/--
Actual fixed-pair K-approval no-randomization theorem: for any finite
randomization over K-approval rules and any ordered candidate pair, either a
static K-approval rule weakly beats the randomized pairwise closed-form rate,
or a static rule lies on the degenerate zero-base boundary.
-/
theorem randomized_k_approval_pairwise_rate_le_static_or_static_boundary
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    (∃ rule : Rule,
      approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
        approvalPairwiseRate
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo) = 0) :=
  randomizedKApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
    law K weight hweight hsum hi lo

/--
Actual fixed-pair K-approval no-randomization theorem in extended-rate form:
for any finite randomization over K-approval rules and any ordered candidate
pair, some static K-approval rule weakly beats the randomized pairwise rate,
with zero-base static boundaries interpreted as top extended rates.
-/
theorem randomized_k_approval_pairwise_extended_rate_le_static
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    ∃ rule : Rule,
      (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo) :
        WithTop ℝ) ≤
        approvalPairwiseExtendedRate
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo) :=
  randomizedKApproval_pairwiseRate_le_static_extended
    law K weight hweight hsum hi lo

/--
Actual fixed-pair K-approval no-randomization theorem on the positive-base
region: for any finite randomization over K-approval rules and any ordered
candidate pair, some static K-approval rule weakly beats the randomized
pairwise closed-form rate for that pair.
-/
theorem randomized_k_approval_pairwise_rate_le_static
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n)
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo))
    (hmixed_base_pos :
      0 <
        approvalPairwiseBase
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) :
    ∃ rule : Rule,
      approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
        approvalPairwiseRate
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo) :=
  randomized_approval_pairwise_rate_le_static
    weight
    (fun rule => kApprovalPairUpProb law (K rule) hi lo)
    (fun rule => kApprovalPairDownProb law (K rule) hi lo)
    rfl rfl hweight hsum
    (fun rule => kApprovalPairUpProb_nonneg law (K rule) hi lo)
    (fun rule => kApprovalPairDownProb_nonneg law (K rule) hi lo)
    hbase_pos hmixed_base_pos

/--
Source-shaped fixed-pair K-approval randomization theorem: for the actual
randomized one-voter law that first draws a finite K-approval rule and then a
ranking, the mixed pairwise error has the exact mixed approval exponent, and
some static K-approval rule weakly beats that exponent for the same ordered
candidate pair.
-/
theorem randomized_approval_pairwise_exact_rate_and_static_rate_ge_from_sampling_law
    {n : ℕ}
    {Rule : Type*} [Fintype Rule] [Nonempty Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n)
    (hmixedUp_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
    (hmixedDown_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo)
    (hmixedDown_le_up :
      (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo))
    (hmixed_base_pos :
      0 <
        approvalPairwiseBase
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb
          (randomizedKApprovalSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 hi)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 lo))
        (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) ∧
      ∃ rule : Rule,
        approvalPairwiseRate
            (∑ rule : Rule,
              weight rule * kApprovalPairUpProb law (K rule) hi lo)
            (∑ rule : Rule,
              weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo) :=
  randomizedKApprovalPairwiseError_exactRate_and_exists_static_rate_ge
    law K weight hweight hsum hi lo hmixedUp_pos hmixedDown_pos
    hmixedDown_le_up hbase_pos hmixed_base_pos

/--
Source-shaped fixed-pair K-approval randomization theorem with valid static
probabilities: the actual randomized one-voter law has the exact mixed
approval exponent, and either some static K-approval rule weakly beats that
exponent for the same ordered pair or a static rule is on the explicit
zero-base boundary of the real-valued closed form.
-/
theorem randomized_approval_pairwise_exact_rate_and_static_rate_ge_or_static_boundary_from_sampling_law
    {n : ℕ}
    {Rule : Type*} [Fintype Rule] [Nonempty Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n)
    (hmixedUp_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo)
    (hmixedDown_pos :
      0 <
        ∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo)
    (hmixedDown_le_up :
      (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
        ∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule) hi lo) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb
          (randomizedKApprovalSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 hi)
          (fun signal : Rule × Ranking n =>
            kApprovalScore (K signal.1) signal.2 lo))
        (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)) ∧
      ((∃ rule : Rule,
        approvalPairwiseRate
            (∑ rule : Rule,
              weight rule * kApprovalPairUpProb law (K rule) hi lo)
            (∑ rule : Rule,
              weight rule * kApprovalPairDownProb law (K rule) hi lo) ≤
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo)) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) hi lo)
            (kApprovalPairDownProb law (K rule) hi lo) = 0)) := by
  constructor
  · exact
      randomizedKApprovalPairwiseError_exponentialRateCertificate
        law K weight hweight hsum hi lo
        (pUp :=
          ∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
        (pDown :=
          ∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo)
        hmixedUp_pos hmixedDown_pos hmixedDown_le_up rfl rfl
  · exact
      randomizedKApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
        law K weight hweight hsum hi lo

/--
Randomized K-approval finite aggregation theorem: for a finite set of relevant
ordered pairs, the actual randomized one-voter law has exact aggregate
exponent equal to the finite minimum of the mixed K-approval pairwise
exponents.
-/
theorem randomized_approval_relevant_pair_aggregate_exact_rate_from_sampling_law
    {n : ℕ} {Rule Pair : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Pair → Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairUpProb law (K rule)
            (hi pair) (lo pair)) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        (∑ rule : Rule,
          weight rule * kApprovalPairDownProb law (K rule)
            (hi pair) (lo pair)) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((randomizedKApprovalRelevantPairRateCertificate
          law K weight hweight hsum hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) :=
  randomizedKApprovalRelevantPairRateCertificate_aggregate_hasExponentialRate_at_finiteOutcomeLearningRate
    law K weight hweight hsum hi lo pUp pDown
    hUp hDown hle hUpProb hDownProb hpairWeight hpairWeight_pos

/--
Randomized K-approval aggregate trichotomy: for a finite family of relevant
ordered pairs, if the actual randomized one-voter law has nonnegative mixed
expected K-approval score gap on every relevant pair, then the randomized
aggregate error either has an exact finite exponential rate or is eventually
zero.  This is the boundary-aware companion to the positive-probability exact
aggregate theorem.
-/
theorem randomized_approval_relevant_pair_aggregate_exact_rate_or_eventually_zero_from_mixed_expected_gap_nonneg
    {n : ℕ} {Rule Pair : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Pair → Candidate n)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedKApprovalSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 (hi pair) -
                kApprovalScore (K signal.1) signal.2 (lo pair)))
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb
              (randomizedKApprovalSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (hi pair))
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (lo pair))
              sampleSize) = 0) := by
  simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw] using
  randomizedKApprovalOutcomeError_hasExponentialRate_or_eventually_zero_of_mixed_expected_gap_nonneg
      law K weight hi lo hweight hsum
      (by
        simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw]
          using hmean)
      hpairWeight hpairWeight_pos

/--
Randomized K-approval aggregate extended-rate endpoint: the actual randomized
one-voter law has a finite aggregate exponent or extended rate `⊤` in the
eventual-zero boundary case.
-/
theorem randomized_approval_relevant_pair_aggregate_extended_rate_from_mixed_expected_gap_nonneg
    {n : ℕ} {Rule Pair : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Pair] [DecidableEq Pair]
    (law : PMF (Ranking n)) (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Pair → Candidate n)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedKApprovalSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 (hi pair) -
                kApprovalScore (K signal.1) signal.2 (lo pair)))
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate := by
  simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw] using
    randomizedKApprovalOutcomeError_hasExtendedExponentialRate_of_mixed_expected_gap_nonneg
      law K weight hi lo hweight hsum
      (by
        simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw]
          using hmean)
      hpairWeight hpairWeight_pos

/--
K-approval no-randomization pairwise theorem with a mixed-rule boundary
branch: static rules stay in the positive-base region, while the randomized
mixture may have zero real-valued base.  Valid probability bounds make the
boundary weak comparison trivial in the total-real rate model.
-/
theorem randomized_approval_pairwise_rate_le_static_or_mixed_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule)) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) :=
  randomizedApproval_pairwiseRate_le_static_or_mixed_boundary
    weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown hprob
    hbase_pos

/--
Mallows W-selection no-randomization bridge: if the same pivotal boundary pair
determines the outcome-learning rate for every static K-approval rule and for
the randomized rule, then some static K-approval rule weakly beats the
randomized outcome-learning rate.
-/
theorem mallows_w_selection_no_randomization_of_common_pivotal_pair
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown)
    (hconvex :
      approvalPairwiseRate mixedUp mixedDown ≤
        ∑ rule : Rule,
          weight rule * approvalPairwiseRate (pUp rule) (pDown rule)) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule :=
  mallowsWSelection_no_randomization_of_common_pivotal_pair
    weight pUp pDown staticOutcomeRate hmixedUp hmixedDown hweight hsum
    hstatic_pivotal hrandomized_pivotal hconvex

/--
Positive-base Mallows W-selection no-randomization bridge using the proved
K-approval Jensen theorem rather than an external convexity certificate.
-/
theorem mallows_w_selection_no_randomization_of_common_pivotal_pair_positive
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule :=
  mallowsWSelection_no_randomization_of_common_pivotal_pair_positive
    weight pUp pDown staticOutcomeRate hmixedUp hmixedDown hweight hsum
    hUp hDown hbase_pos hmixed_base_pos hstatic_pivotal
    hrandomized_pivotal

/--
Mixed-boundary Mallows W-selection no-randomization bridge: static rules stay
in the positive-base region, while the randomized mixture may have zero
real-valued boundary base.
-/
theorem mallows_w_selection_no_randomization_of_common_pivotal_pair_or_mixed_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule :=
  mallowsWSelection_no_randomization_of_common_pivotal_pair_or_mixed_boundary
    weight pUp pDown staticOutcomeRate hmixedUp hmixedDown hweight hsum
    hUp hDown hprob hbase_pos hstatic_pivotal hrandomized_pivotal

/--
Finite outcome-rate K-approval no-randomization bridge: if the same concrete
pivotal pair realizes the finite outcome-learning rate for every static rule
and for the randomized rule, the pairwise K-approval theorem gives a static
rule weakly beating the randomized outcome rate.
-/
theorem k_approval_outcome_no_randomization_from_common_pivotal_pair_positive
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      finiteOutcomeLearningRate randomizedPairRate =
        randomizedPairRate pivotal)
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) :=
  kApprovalOutcome_no_randomization_of_common_pivotal_pair_positive
    weight pUp pDown staticPairRate randomizedPairRate pivotal
    hmixedUp hmixedDown hweight hsum hUp hDown hbase_pos
    hmixed_base_pos hstatic_pivotal hstatic_boundary
    hrandomized_pivotal hrandomized_boundary

/--
Finite outcome-rate common-pivotal bridge with a mixed-rule boundary branch:
the randomized mixture may have zero real-valued boundary base.
-/
theorem k_approval_outcome_no_randomization_from_common_pivotal_pair_or_mixed_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      finiteOutcomeLearningRate randomizedPairRate =
        randomizedPairRate pivotal)
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) :=
  kApprovalOutcome_no_randomization_of_common_pivotal_pair_or_mixed_boundary
    weight pUp pDown staticPairRate randomizedPairRate pivotal
    hmixedUp hmixedDown hweight hsum hUp hDown hprob hbase_pos
    hstatic_pivotal hstatic_boundary hrandomized_pivotal hrandomized_boundary

/--
Finite outcome-rate K-approval no-randomization bridge with only static
pivotality: the randomized rule need not have the same pivotal pair, since its
finite outcome rate is bounded above by its boundary-pair rate.
-/
theorem k_approval_outcome_no_randomization_from_static_pivotal_pair_positive
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) :=
  kApprovalOutcome_no_randomization_of_static_pivotal_pair_positive
    weight pUp pDown staticPairRate randomizedPairRate pivotal
    hmixedUp hmixedDown hweight hsum hUp hDown hbase_pos
    hmixed_base_pos hstatic_pivotal hstatic_boundary
    hrandomized_boundary

/--
Finite outcome-rate static-pivotal bridge with a mixed-rule boundary branch:
the randomized rule need not have the same pivotal pair, and its boundary pair
may have zero real-valued base.
-/
theorem k_approval_outcome_no_randomization_from_static_pivotal_pair_or_mixed_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) :=
  kApprovalOutcome_no_randomization_of_static_pivotal_pair_or_mixed_boundary
    weight pUp pDown staticPairRate randomizedPairRate pivotal
    hmixedUp hmixedDown hweight hsum hUp hDown hprob hbase_pos
    hstatic_pivotal hstatic_boundary hrandomized_boundary

/--
Finite outcome-rate static-pivotal bridge over valid approval probabilities:
the randomized rule need not have the same pivotal pair.  Either a static rule
weakly beats the randomized finite outcome rate, or a static boundary pair is
degenerate in the real-valued approval-rate formula.
-/
theorem k_approval_outcome_no_randomization_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    (∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) :=
  kApprovalOutcome_no_randomization_of_static_pivotal_pair_valid_probabilities_or_static_boundary
    weight pUp pDown staticPairRate randomizedPairRate pivotal
    hmixedUp hmixedDown hweight hsum hUp hDown hprob
    hstatic_pivotal hstatic_boundary hrandomized_boundary

/--
Actual ranking-law K-approval outcome-rate lift with a static pivotal pair.
The static component rates use the paper's K-approval up/down probabilities
for each relevant pair, while the randomized rate uses their weighted mixture.
-/
theorem randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_or_mixed_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [Nonempty Rule] [Fintype Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) :=
  randomizedKApproval_outcomeRate_le_static_from_static_pivotal_pair_or_mixed_boundary
    law K weight hi lo pivotal hweight hsum hbase_pos hstatic_pivotal

/--
Actual ranking-law K-approval outcome-rate lift over valid K-approval
probabilities.  Either a static component weakly beats the randomized finite
outcome rate, or the supplied static pivotal pair is a degenerate zero-base
boundary for some component.
-/
theorem randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [Nonempty Rule] [Fintype Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rule : Rule,
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
      (∃ rule : Rule,
        approvalPairwiseBase
          (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
          (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
            0) :=
  randomizedKApproval_outcomeRate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    law K weight hi lo pivotal hweight hsum hstatic_pivotal

/--
Bundled positive-base Theorem 2 endpoint: for the actual randomized
K-approval sampling law over a finite relevant-pair family, the randomized
aggregate error has exact finite outcome-learning rate, and some static
K-approval component weakly beats that randomized finite outcome rate when the
static pivotal approval bases are positive.
-/
theorem randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_pivotal_pair_or_mixed_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hmixedUp_pos :
      ∀ pair,
        0 <
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hmixedDown_pos :
      ∀ pair,
        0 <
          ∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
    (hmixedDown_le_up :
      ∀ pair,
        (∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair)) ≤
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    HasExponentialRate
        ((randomizedKApprovalRelevantPairRateCertificate
            law K weight hweight hsum hi lo
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
            hmixedUp_pos hmixedDown_pos hmixedDown_le_up
            (fun _ => rfl) (fun _ => rfl))
          |>.aggregateError pairWeight)
        (finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∧
      ∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) := by
  constructor
  · exact
      randomized_approval_relevant_pair_aggregate_exact_rate_from_sampling_law
        law K weight hweight hsum hi lo
        (fun pair =>
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
        (fun pair =>
          ∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
        hmixedUp_pos hmixedDown_pos hmixedDown_le_up
        (fun _ => rfl) (fun _ => rfl)
        hpairWeight hpairWeight_pos
  · exact
      randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_or_mixed_boundary
        law K weight hi lo pivotal hweight hsum hbase_pos hstatic_pivotal

/--
Bundled source-facing Theorem 2 endpoint: for the actual randomized
K-approval sampling law over a finite relevant-pair family, the randomized
aggregate error has exact finite outcome-learning rate, and under the
static-pivotal hypothesis some static K-approval component weakly beats that
randomized finite outcome rate unless the static pivotal pair is on the
explicit zero-base boundary.
-/
theorem randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hmixedUp_pos :
      ∀ pair,
        0 <
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hmixedDown_pos :
      ∀ pair,
        0 <
          ∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
    (hmixedDown_le_up :
      ∀ pair,
        (∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair)) ≤
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    HasExponentialRate
        ((randomizedKApprovalRelevantPairRateCertificate
            law K weight hweight hsum hi lo
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
            hmixedUp_pos hmixedDown_pos hmixedDown_le_up
            (fun _ => rfl) (fun _ => rfl))
          |>.aggregateError pairWeight)
        (finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) := by
  constructor
  · exact
      randomized_approval_relevant_pair_aggregate_exact_rate_from_sampling_law
        law K weight hweight hsum hi lo
        (fun pair =>
          ∑ rule : Rule,
            weight rule *
              kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
        (fun pair =>
          ∑ rule : Rule,
            weight rule *
              kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
        hmixedUp_pos hmixedDown_pos hmixedDown_le_up
        (fun _ => rfl) (fun _ => rfl)
        hpairWeight hpairWeight_pos
  · exact
      randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
        law K weight hi lo pivotal hweight hsum hstatic_pivotal

/--
Boundary-aware bundled Theorem 2 endpoint: the actual randomized K-approval
aggregate error either has an exact finite exponential rate or is eventually
zero, and under the static-pivotal hypothesis some static K-approval component
weakly beats the randomized finite outcome-rate formula unless that static
pivotal pair is on the explicit zero-base boundary.
-/
theorem randomized_k_approval_aggregate_rate_or_eventually_zero_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hmixed_expected_gap_nonneg :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedKApprovalSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 (hi pair) -
                kApprovalScore (K signal.1) signal.2 (lo pair)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    ((∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb
              (randomizedKApprovalSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (hi pair))
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (lo pair))
              sampleSize) = 0)) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) := by
  constructor
  · exact
      randomized_approval_relevant_pair_aggregate_exact_rate_or_eventually_zero_from_mixed_expected_gap_nonneg
        law K weight hweight hsum hi lo hmixed_expected_gap_nonneg
        hpairWeight hpairWeight_pos
  · exact
      randomized_k_approval_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
        law K weight hi lo pivotal hweight hsum hstatic_pivotal

/--
Extended-rate bundled Theorem 2 endpoint: the actual randomized K-approval
aggregate error has a source-facing extended rate, and under the static
pivotal hypothesis some static K-approval component weakly beats the
randomized finite outcome-rate formula unless that static pivotal pair lies
on the explicit zero-base boundary.
-/
theorem randomized_k_approval_aggregate_extended_rate_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hmixed_expected_gap_nonneg :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedKApprovalSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 (hi pair) -
                kApprovalScore (K signal.1) signal.2 (lo pair)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) := by
  constructor
  · exact
      randomized_approval_relevant_pair_aggregate_extended_rate_from_mixed_expected_gap_nonneg
        law K weight hweight hsum hi lo hmixed_expected_gap_nonneg
        hpairWeight hpairWeight_pos
  · exact
      (randomized_k_approval_aggregate_rate_or_eventually_zero_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
        law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
        hmixed_expected_gap_nonneg hstatic_pivotal).2

/--
Boundary-aware bundled Theorem 2 endpoint from component orientation: if every
static K-approval component is oriented with down-probability at most
up-probability on every relevant pair, then the actual randomized aggregate
error either has an exact finite exponential rate or is eventually zero.  The
same static-pivotal comparison gives a static K-approval component that weakly
beats the randomized finite outcome-rate formula unless the static pivotal
pair is on the explicit zero-base boundary.
-/
theorem randomized_k_approval_aggregate_rate_or_eventually_zero_and_outcome_rate_le_static_from_static_component_orientation_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hstaticDown_le_up :
      ∀ pair rule,
        kApprovalPairDownProb law (K rule) (hi pair) (lo pair) ≤
          kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    ((∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb
              (randomizedKApprovalSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (hi pair))
              (fun signal : Rule × Ranking n =>
                kApprovalScore (K signal.1) signal.2 (lo pair))
              sampleSize) = 0)) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) :=
  randomized_k_approval_aggregate_rate_or_eventually_zero_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
    law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
    (fun pair => by
      simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw] using
        randomizedKApproval_mixedExpectedGap_nonneg_of_static_down_le_up
          law K weight hweight hsum (hi pair) (lo pair)
          (fun rule => hstaticDown_le_up pair rule))
    hstatic_pivotal

/--
Extended-rate Theorem 2 endpoint from component orientation: if every static
K-approval component is oriented with down-probability at most up-probability
on every relevant pair, the actual randomized aggregate has a source-facing
extended rate, and the static-pivotal comparison gives a static K-approval
component that weakly beats the randomized finite outcome-rate formula unless
the static pivotal pair is on the explicit zero-base boundary.
-/
theorem randomized_k_approval_aggregate_extended_rate_and_outcome_rate_le_static_from_static_component_orientation_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hstaticDown_le_up :
      ∀ pair rule,
        kApprovalPairDownProb law (K rule) (hi pair) (lo pair) ≤
          kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) :=
  randomized_k_approval_aggregate_extended_rate_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
    law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
    (fun pair => by
      simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw] using
        randomizedKApproval_mixedExpectedGap_nonneg_of_static_down_le_up
          law K weight hweight hsum (hi pair) (lo pair)
          (fun rule => hstaticDown_le_up pair rule))
    hstatic_pivotal

/--
Extended-rate Theorem 2 endpoint with the static boundary absorbed into the
ordered rate comparison.  The actual randomized aggregate has a source-facing
extended rate, and some static K-approval rule weakly beats the randomized
finite outcome-rate formula when the static pivotal pair has positive base;
if that static pivotal base is zero, the right-hand side is `⊤`.
-/
theorem randomized_k_approval_aggregate_extended_rate_and_extended_outcome_comparison_from_static_pivotal_pair
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hmixed_expected_gap_nonneg :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedKApprovalSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Ranking n =>
              kApprovalScore (K signal.1) signal.2 (hi pair) -
                kApprovalScore (K signal.1) signal.2 (lo pair)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate) ∧
      (∃ rule : Rule,
        ((finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) :
          WithTop ℝ) ≤
          approvalPairwiseExtendedRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)))) := by
  rcases
      randomized_k_approval_aggregate_extended_rate_and_outcome_rate_le_static_from_static_pivotal_pair_or_static_boundary
        law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
        hmixed_expected_gap_nonneg hstatic_pivotal with
    ⟨haggregate, hcomparison_or_boundary⟩
  refine ⟨haggregate, ?_⟩
  rcases hcomparison_or_boundary with hcomparison | hboundary
  · rcases hcomparison with ⟨rule, hcomparison⟩
    refine ⟨rule, ?_⟩
    have hcomparison_pivotal :
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) := by
      simpa [hstatic_pivotal rule] using hcomparison
    by_cases hzero :
        approvalPairwiseBase
          (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
          (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) = 0
    · simpa [approvalPairwiseExtendedRate, hzero]
    · simpa [approvalPairwiseExtendedRate, hzero] using hcomparison_pivotal
  · rcases hboundary with ⟨rule, hzero⟩
    refine ⟨rule, ?_⟩
    simpa [approvalPairwiseExtendedRate, hzero]

/--
Extended-rate Theorem 2 endpoint from component orientation, with the static
zero-base boundary absorbed into an ordered extended comparison.  This is the
source-facing no-randomization wrapper: the randomized aggregate has an
extended rate, and some static K-approval component is at least as good in
extended pivotal-outcome rate.
-/
theorem randomized_k_approval_aggregate_extended_rate_and_extended_outcome_comparison_from_static_component_orientation
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hstaticDown_le_up :
      ∀ pair rule,
        kApprovalPairDownProb law (K rule) (hi pair) (lo pair) ≤
          kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedKApprovalSamplingLaw law weight hweight hsum)
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × Ranking n =>
                  kApprovalScore (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate) ∧
      (∃ rule : Rule,
        ((finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) :
          WithTop ℝ) ≤
          approvalPairwiseExtendedRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)))) :=
  randomized_k_approval_aggregate_extended_rate_and_extended_outcome_comparison_from_static_pivotal_pair
    law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
    (fun pair => by
      simpa [randomizedKApprovalSamplingLaw, randomizedScoringSamplingLaw] using
        randomizedKApproval_mixedExpectedGap_nonneg_of_static_down_le_up
          law K weight hweight hsum (hi pair) (lo pair)
          (fun rule => hstaticDown_le_up pair rule))
    hstatic_pivotal

/--
Bundled Theorem 2 endpoint with positive-component witnesses: the actual
randomized K-approval aggregate error has exact finite outcome-learning rate
as soon as each relevant mixed up/down probability has one positive-weight
positive component.  This avoids requiring every randomized component to be
strictly positive on every relevant pair.
-/
theorem randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_component_witnesses_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hstaticUp_component :
      ∀ pair,
        ∃ rule : Rule,
          0 < weight rule ∧
            0 < kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstaticDown_component :
      ∀ pair,
        ∃ rule : Rule,
          0 < weight rule ∧
            0 < kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
    (hstaticDown_le_up :
      ∀ pair rule,
        kApprovalPairDownProb law (K rule) (hi pair) (lo pair) ≤
          kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    HasExponentialRate
        ((randomizedKApprovalRelevantPairRateCertificate
            law K weight hweight hsum hi lo
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
            (fun pair => by
              rcases hstaticUp_component pair with
                ⟨rule, hweight_pos, hUp_pos⟩
              exact
                randomizedKApproval_mixedPairUpProb_pos_of_positive_component
                  law K weight hweight (hi pair) (lo pair)
                  hweight_pos hUp_pos)
            (fun pair => by
              rcases hstaticDown_component pair with
                ⟨rule, hweight_pos, hDown_pos⟩
              exact
                randomizedKApproval_mixedPairDownProb_pos_of_positive_component
                  law K weight hweight (hi pair) (lo pair)
                  hweight_pos hDown_pos)
            (fun pair =>
              randomizedKApproval_mixedPairDownProb_le_upProb
                law K weight hweight (hi pair) (lo pair)
                (fun rule => hstaticDown_le_up pair rule))
            (fun _ => rfl) (fun _ => rfl))
          |>.aggregateError pairWeight)
        (finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) :=
  randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
    (fun pair => by
      rcases hstaticUp_component pair with ⟨rule, hweight_pos, hUp_pos⟩
      exact
        randomizedKApproval_mixedPairUpProb_pos_of_positive_component
          law K weight hweight (hi pair) (lo pair) hweight_pos hUp_pos)
    (fun pair => by
      rcases hstaticDown_component pair with ⟨rule, hweight_pos, hDown_pos⟩
      exact
        randomizedKApproval_mixedPairDownProb_pos_of_positive_component
          law K weight hweight (hi pair) (lo pair) hweight_pos hDown_pos)
    (fun pair =>
      randomizedKApproval_mixedPairDownProb_le_upProb
        law K weight hweight (hi pair) (lo pair)
        (fun rule => hstaticDown_le_up pair rule))
    hstatic_pivotal

/--
Bundled Theorem 2 endpoint with component-level probability assumptions: the
actual randomized K-approval aggregate error has exact finite outcome-learning
rate, and the no-randomization comparison follows unless the static pivotal
pair is on the explicit zero-base boundary.  The mixed positive-probability
and orientation hypotheses are derived from the static components by reusable
weighted-sum lemmas.
-/
theorem randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_component_positive_oriented_pivotal_pair_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Nonempty Rule]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → Candidate n)
    (pivotal : Pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair)
    (hstaticUp_pos :
      ∀ pair rule,
        0 < kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstaticDown_pos :
      ∀ pair rule,
        0 < kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
    (hstaticDown_le_up :
      ∀ pair rule,
        kApprovalPairDownProb law (K rule) (hi pair) (lo pair) ≤
          kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal))) :
    HasExponentialRate
        ((randomizedKApprovalRelevantPairRateCertificate
            law K weight hweight hsum hi lo
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
            (fun pair =>
              ∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair))
            (fun pair =>
              randomizedKApproval_mixedPairUpProb_pos
                law K weight hweight hsum (hi pair) (lo pair)
                (fun rule => hstaticUp_pos pair rule))
            (fun pair =>
              randomizedKApproval_mixedPairDownProb_pos
                law K weight hweight hsum (hi pair) (lo pair)
                (fun rule => hstaticDown_pos pair rule))
            (fun pair =>
              randomizedKApproval_mixedPairDownProb_le_upProb
                law K weight hweight (hi pair) (lo pair)
                (fun rule => hstaticDown_le_up pair rule))
            (fun _ => rfl) (fun _ => rfl))
          |>.aggregateError pairWeight)
        (finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∧
      ((∃ rule : Rule,
        finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (∑ rule : Rule,
                  weight rule *
                    kApprovalPairDownProb law (K rule) (hi pair) (lo pair))) ≤
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              approvalPairwiseRate
                (kApprovalPairUpProb law (K rule) (hi pair) (lo pair))
                (kApprovalPairDownProb law (K rule) (hi pair) (lo pair)))) ∨
        (∃ rule : Rule,
          approvalPairwiseBase
            (kApprovalPairUpProb law (K rule) (hi pivotal) (lo pivotal))
            (kApprovalPairDownProb law (K rule) (hi pivotal) (lo pivotal)) =
              0)) :=
  randomized_k_approval_aggregate_exact_rate_and_outcome_rate_le_static_from_static_component_witnesses_or_static_boundary
    law K weight hi lo pivotal hweight hsum hpairWeight hpairWeight_pos
    (fun pair => by
      rcases AppliedModelingLib.exists_positive_weight_of_nonneg_sum_eq_one
          weight hweight hsum with
        ⟨rule, hweight_pos⟩
      exact ⟨rule, hweight_pos, hstaticUp_pos pair rule⟩)
    (fun pair => by
      rcases AppliedModelingLib.exists_positive_weight_of_nonneg_sum_eq_one
          weight hweight hsum with
        ⟨rule, hweight_pos⟩
      exact ⟨rule, hweight_pos, hstaticDown_pos pair rule⟩)
    hstaticDown_le_up hstatic_pivotal

/--
W-selection randomization-can-help certificate: if two static approval rules
have the same finite outcome-learning rate and the randomized rule strictly
beats that base rate on every pivotal pair, then the randomized rule strictly
improves the finite outcome-learning rate over both static rules.
-/
theorem randomized_approval_w_selection_improves_from_two_static_minima
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticAUp staticADown staticBUp staticBDown
      randomizedUp randomizedDown : Pair → ℝ)
    {baseRate : ℝ}
    (hA :
      finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticAUp pair) (staticADown pair)) =
        baseRate)
    (hB :
      finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticBUp pair) (staticBDown pair)) =
        baseRate)
    (hrandomized :
      ∀ pair,
        baseRate <
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :
    max
        (finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticAUp pair) (staticADown pair)))
        (finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticBUp pair) (staticBDown pair))) <
      finiteOutcomeLearningRate
        (fun pair =>
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :=
  randomizedApproval_outcomeRate_strictly_improves_two_static_minima
    staticAUp staticADown staticBUp staticBDown randomizedUp randomizedDown
    hA hB hrandomized

/--
W-selection randomization-can-help certificate in the source theorem's
`max_K r(K)` form: if every static approval cutoff in a finite family has
outcome rate at most `baseRate`, and the randomized rule beats `baseRate` on
every pivotal pair, then the randomized rule strictly beats the best static
approval cutoff in that finite family.
-/
theorem randomized_approval_w_selection_improves_over_all_static_from_rate_bound
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (staticUp staticDown : Rule → Pair → ℝ)
    (randomizedUp randomizedDown : Pair → ℝ) {baseRate : ℝ}
    (hstatic :
      ∀ rule,
        finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate (staticUp rule pair) (staticDown rule pair)) ≤
          baseRate)
    (hrandomized :
      ∀ pair,
        baseRate <
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :
    (Finset.univ : Finset Rule).sup' finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate (staticUp rule pair) (staticDown rule pair))) <
      finiteOutcomeLearningRate
        (fun pair =>
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :=
  randomizedApproval_outcomeRate_strictly_improves_all_static_of_bound
    staticUp staticDown randomizedUp randomizedDown hstatic hrandomized

/--
Constructed W-selection `max_K` package: for the exact finite K/L construction,
if the representative K′ side-case buckets are bounded by the K/L base rate,
then the randomized approval rule strictly beats the finite supremum over the
static K, L, and side-case categories.
-/
theorem randomized_approval_w_selection_constructed_static_categories_maxK
    {oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp : ℝ}
    (hOneSided :
      approvalPairwiseRate oneSidedUp 0 ≤
        constructedWSelectionStaticBaseRate)
    (hNearTie :
      approvalPairwiseRate (nearTieBase + nearTieEps) nearTieBase ≤
        constructedWSelectionStaticBaseRate)
    (hOneSidedBoundary :
      approvalPairwiseRate oneSidedBoundaryUp 0 ≤
        constructedWSelectionStaticBaseRate) :
    (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
        finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate
                (constructedWSelectionStaticCategoryUp
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair)
                (constructedWSelectionStaticCategoryDown
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair))) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelectionRandomizedApproval_improves_static_categories
    hOneSided hNearTie hOneSidedBoundary

/--
Constructed W-selection `max_K` package with the source's `K' = L + 1`
one-sided-boundary condition: that side-case rate is bounded by the K/L base
whenever the paper's base inequality `base(refUp, refDown) < 1 - pUp` holds for
a reference approval rate already below the constructed base.
-/
theorem randomized_approval_w_selection_constructed_static_categories_maxK_of_boundary_base
    {oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp refUp refDown : ℝ}
    (hOneSided :
      approvalPairwiseRate oneSidedUp 0 ≤
        constructedWSelectionStaticBaseRate)
    (hNearTie :
      approvalPairwiseRate (nearTieBase + nearTieEps) nearTieBase ≤
        constructedWSelectionStaticBaseRate)
    (href_base_pos : 0 < approvalPairwiseBase refUp refDown)
    (href_rate_le_base :
      approvalPairwiseRate refUp refDown ≤
        constructedWSelectionStaticBaseRate)
    (hboundary_base_lt :
      approvalPairwiseBase refUp refDown < 1 - oneSidedBoundaryUp) :
    (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
        finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate
                (constructedWSelectionStaticCategoryUp
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair)
                (constructedWSelectionStaticCategoryDown
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair))) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelectionRandomizedApproval_improves_static_categories_of_boundary_base
    hOneSided hNearTie href_base_pos href_rate_le_base hboundary_base_lt

/--
Constructed W-selection `max_K` existence package: the K′ side-case parameters
can be chosen positive and small enough that the randomized approval rule
strictly beats the best finite static category in the constructed source proof.
-/
theorem randomized_approval_w_selection_constructed_exists_static_categories_maxK :
    ∃ oneSidedUp nearTieEps oneSidedBoundaryUp : ℝ,
      0 < oneSidedUp ∧ oneSidedUp < 1 ∧
        0 < nearTieEps ∧ nearTieEps < 1 ∧
          0 < oneSidedBoundaryUp ∧ oneSidedBoundaryUp < 1 ∧
            (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
                finiteUnivNonempty
                (fun rule =>
                  finiteOutcomeLearningRate
                    (fun pair =>
                      approvalPairwiseRate
                        (constructedWSelectionStaticCategoryUp
                          oneSidedUp (constructedWSelectionProb 27)
                          nearTieEps oneSidedBoundaryUp rule pair)
                        (constructedWSelectionStaticCategoryDown
                          oneSidedUp (constructedWSelectionProb 27)
                          nearTieEps oneSidedBoundaryUp rule pair))) <
              finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelectionRandomizedApproval_exists_static_categories_maxK

/--
Constructive source-shaped package for
`lem:randomizebetterapproval_Wselection`: the exact finite table satisfies
strict prefix dominance for W-selection, and small K′ side-case parameters make
the randomized approval rule strictly beat the best finite static category in
the constructed `max_K` family.
-/
theorem randomized_approval_w_selection_constructed_design_invariant_and_static_categories_maxK :
    StrictTopPrefixDominanceOn
        constructedWSelectionTopPrefixProb
        constructedWSelectionCrossTier ∧
      ∃ oneSidedUp nearTieEps oneSidedBoundaryUp : ℝ,
        0 < oneSidedUp ∧ oneSidedUp < 1 ∧
          0 < nearTieEps ∧ nearTieEps < 1 ∧
            0 < oneSidedBoundaryUp ∧ oneSidedBoundaryUp < 1 ∧
              (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
                  finiteUnivNonempty
                  (fun rule =>
                    finiteOutcomeLearningRate
                      (fun pair =>
                        approvalPairwiseRate
                          (constructedWSelectionStaticCategoryUp
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair)
                          (constructedWSelectionStaticCategoryDown
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair))) <
                finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelection_designInvariant_and_randomizedApproval_improves_static_categories

/--
The six source rankings with probabilities
`46, 656, 227, 7, 44, 20` thousandths induce exactly the finite top-prefix
probability table used in the constructed W-selection proof, after embedding
the source candidates into the canonical three-candidate ranking universe.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_prefix_table
    (candidate : ConstructedWSelectionCandidate) (cut : Fin 2) :
    rankingTopPrefixProb
        constructedWSelectionRanking1Law
        (constructedWSelectionCandidateToRanking1 candidate)
        cut =
      constructedWSelectionTopPrefixProb candidate cut :=
  constructedWSelectionRanking1TopPrefixProb_eq candidate cut

/--
Constructed W-selection design-invariance from an actual finite ranking law:
the explicit six-ranking PMF over `Ranking 1` satisfies strict top-prefix
dominance for the designated winner against both lower-tier candidates.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_strict_prefix_dominance :
    StrictTopPrefixDominanceOn
      constructedWSelectionRanking1TopPrefixProb
      constructedWSelectionCrossTier :=
  constructedWSelectionRanking1Law_strictTopPrefixDominanceOn

/--
Canonical winner-set form of the constructed-law strict prefix-dominance
condition: the embedded winner beats every non-winner in every proper ranking
prefix under the explicit six-ranking law.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_winner_set_strict_prefix_dominance :
    ∀ hi lo : ConstructedWSelectionRanking1Candidate,
      hi ∈ constructedWSelectionRanking1WinnerSet →
        lo ∉ constructedWSelectionRanking1WinnerSet →
          ∀ cut : RankingProperPrefixCut 1,
            rankingTopPrefixProb constructedWSelectionRanking1Law lo cut <
              rankingTopPrefixProb constructedWSelectionRanking1Law hi cut :=
  constructedWSelectionRanking1Law_winnerSet_strictPrefixDominance

/--
Finite Proposition 1 consequence for the constructed law: every reasonable
ranking-prefix score vector separates the embedded winner from every non-winner
in expected one-voter score.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_all_reasonable_prefix_score_separation :
    ∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : ConstructedWSelectionRanking1Candidate,
          hi ∈ constructedWSelectionRanking1WinnerSet →
            lo ∉ constructedWSelectionRanking1WinnerSet →
              prefixExpectedScore diff
                  (rankingTopPrefixProb constructedWSelectionRanking1Law)
                  lo <
                prefixExpectedScore diff
                  (rankingTopPrefixProb constructedWSelectionRanking1Law)
                  hi :=
  constructedWSelectionRanking1Law_allReasonablePrefixScoreSeparation

/--
Asymptotic Proposition 1 consequence for the constructed law: every reasonable
ranking-prefix score vector makes the canonical score-top W-selection error
tend to zero for the embedded singleton winner set.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_all_reasonable_prefix_score_consistency :
    ∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0) :=
  constructedWSelectionRanking1Law_allReasonablePrefixScoreConsistency

/--
For the explicit six-ranking law, the source K=1 approval up-probability table
is the actual K-approval pair-up probability against the relevant loser.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k1_up_prob
    (pair : ConstructedWSelectionPair) :
    kApprovalPairUpProb
        constructedWSelectionRanking1Law 1
        (constructedWSelectionCandidateToRanking1
          ConstructedWSelectionCandidate.winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK1Up pair :=
  constructedWSelectionRanking1K1UpProb_eq pair

/--
For the explicit six-ranking law, the source K=1 approval down-probability
table is the actual K-approval pair-down probability against the relevant
loser.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k1_down_prob
    (pair : ConstructedWSelectionPair) :
    kApprovalPairDownProb
        constructedWSelectionRanking1Law 1
        (constructedWSelectionCandidateToRanking1
          ConstructedWSelectionCandidate.winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK1Down pair :=
  constructedWSelectionRanking1K1DownProb_eq pair

/--
For the explicit six-ranking law, the source K=2 approval up-probability table
is the actual K-approval pair-up probability against the relevant loser.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k2_up_prob
    (pair : ConstructedWSelectionPair) :
    kApprovalPairUpProb
        constructedWSelectionRanking1Law 2
        (constructedWSelectionCandidateToRanking1
          ConstructedWSelectionCandidate.winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK2Up pair :=
  constructedWSelectionRanking1K2UpProb_eq pair

/--
For the explicit six-ranking law, the source K=2 approval down-probability
table is the actual K-approval pair-down probability against the relevant
loser.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k2_down_prob
    (pair : ConstructedWSelectionPair) :
    kApprovalPairDownProb
        constructedWSelectionRanking1Law 2
        (constructedWSelectionCandidateToRanking1
          ConstructedWSelectionCandidate.winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK2Down pair :=
  constructedWSelectionRanking1K2DownProb_eq pair

/--
For the explicit six-ranking law, the source K=1 approval table yields the
exact finite outcome-error exponent over the two relevant loser pairs.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k1_exact_outcome_rate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1K1RelevantPairRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate constructedWSelectionK1Rate) :=
  constructedWSelectionRanking1K1_outcomeError_hasExponentialRate
    hweight hweight_pos

/--
For the explicit six-ranking law, the source K=2 approval table yields the
exact finite outcome-error exponent over the two relevant loser pairs.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_k2_exact_outcome_rate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1K2RelevantPairRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate constructedWSelectionK2Rate) :=
  constructedWSelectionRanking1K2_outcomeError_hasExponentialRate
    hweight hweight_pos

/--
The constructed randomized approval up-probability table is the 50/50 average
of the actual K=1 and K=2 approval up-probabilities under the explicit
six-ranking law.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_randomized_up_average
    (pair : ConstructedWSelectionPair) :
    (kApprovalPairUpProb
          constructedWSelectionRanking1Law 1
          (constructedWSelectionCandidateToRanking1
            ConstructedWSelectionCandidate.winner)
          (constructedWSelectionPairLoserToRanking1 pair) +
        kApprovalPairUpProb
          constructedWSelectionRanking1Law 2
          (constructedWSelectionCandidateToRanking1
            ConstructedWSelectionCandidate.winner)
          (constructedWSelectionPairLoserToRanking1 pair)) / 2 =
      constructedWSelectionRandomizedUp pair :=
  constructedWSelectionRanking1RandomizedUpProb_eq_average pair

/--
The constructed randomized approval down-probability table is the 50/50 average
of the actual K=1 and K=2 approval down-probabilities under the explicit
six-ranking law.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_randomized_down_average
    (pair : ConstructedWSelectionPair) :
    (kApprovalPairDownProb
          constructedWSelectionRanking1Law 1
          (constructedWSelectionCandidateToRanking1
            ConstructedWSelectionCandidate.winner)
          (constructedWSelectionPairLoserToRanking1 pair) +
        kApprovalPairDownProb
          constructedWSelectionRanking1Law 2
          (constructedWSelectionCandidateToRanking1
            ConstructedWSelectionCandidate.winner)
          (constructedWSelectionPairLoserToRanking1 pair)) / 2 =
      constructedWSelectionRandomizedDown pair :=
  constructedWSelectionRanking1RandomizedDownProb_eq_average pair

/--
Actual finite `max_K` version for the constructed three-candidate ranking law:
the 50/50 randomized approval rule strictly beats every static K-approval
cutoff `K = 0, 1, 2, 3` in finite W-selection learning rate.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_improves_all_static_k :
    (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
        (fun K =>
          finiteOutcomeLearningRate
            (constructedWSelectionRanking1StaticKRate K)) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelectionRanking1RandomizedApproval_improves_all_staticK

/--
Actual finite `max_K` version with the randomized RHS also expressed as the
50/50 mixture of actual K=1 and K=2 approval probabilities under the explicit
six-ranking law.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_actual_randomized_improves_all_static_k :
    (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
        (fun K =>
          finiteOutcomeLearningRate
            (constructedWSelectionRanking1StaticKRate K)) <
      finiteOutcomeLearningRate
        constructedWSelectionRanking1RandomizedApprovalRate :=
  constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK

/--
For the explicit six-ranking law, the actual 50/50 randomized approval
mechanism first samples K=1 or K=2 uniformly and then samples a ranking; its
two-pair W-selection aggregate has exact finite exponent equal to the
randomized approval finite outcome-learning rate.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_randomized_exact_outcome_rate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1RandomizedApprovalRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        constructedWSelectionRanking1RandomizedApprovalRate) :=
  constructedWSelectionRanking1RandomizedApproval_outcomeError_hasExponentialRate
    hweight hweight_pos

/--
Actual randomized-mechanism endpoint for the constructed law: the voter-level
50/50 randomized approval process has the stated exact aggregate exponent, and
that exponent is strictly larger than every static K-approval cutoff
`K = 0, 1, 2, 3`.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_randomized_exact_rate_and_improves_all_static_k
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
        (constructedWSelectionRanking1RandomizedApprovalRateCertificate
          |>.aggregateError pairWeight)
        (finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate) ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  ⟨randomized_approval_w_selection_constructed_ranking_law_randomized_exact_outcome_rate
      hweight hweight_pos,
    constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK⟩

/--
Closed finite constructed-law version of
`lem:randomizebetterapproval_Wselection`: the explicit six-ranking law is
W-selection consistent for every reasonable prefix-score rule, the actual
voter-level 50/50 randomized approval mechanism has its exact unit-weight
aggregate exponent, and that exponent strictly beats every static K-approval
cutoff `K = 0, 1, 2, 3`.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_complete_actual_endpoint :
    (∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0)) ∧
      HasExponentialRate
        (constructedWSelectionRanking1RandomizedApprovalRateCertificate
          |>.aggregateError constructedWSelectionPairUnitWeight)
        (finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate) ∧
        (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
            (fun K =>
              finiteOutcomeLearningRate
                (constructedWSelectionRanking1StaticKRate K)) <
          finiteOutcomeLearningRate
            constructedWSelectionRanking1RandomizedApprovalRate :=
  constructedWSelectionRanking1_consistency_exactRandomizedApprovalRate_and_improves_all_staticK

/--
Finite constructed-law endpoint: the explicit six-ranking law satisfies
W-selection strict prefix dominance, and its 50/50 randomized approval rule
strictly beats every static K-approval cutoff `K = 0, 1, 2, 3`.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_design_invariant_and_all_static_k :
    StrictTopPrefixDominanceOn
        constructedWSelectionRanking1TopPrefixProb
        constructedWSelectionCrossTier ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  constructedWSelectionRanking1_designInvariant_and_randomizedApproval_improves_all_staticK

/--
Finite constructed-law endpoint in the source asymptotic form: every
reasonable prefix-score rule is W-selection consistent for the explicit
six-ranking law, and the actual 50/50 randomized approval rule strictly beats
every static K-approval cutoff `K = 0, 1, 2, 3`.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_consistency_and_actual_randomized_improves_all_static_k :
    (∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0)) ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  constructedWSelectionRanking1_consistency_and_actualRandomizedApproval_improves_all_staticK

/--
Constructive source-shaped package using the actual six-ranking law: the law
satisfies strict prefix dominance for W-selection, and small K′ side-case
parameters make the randomized approval rule strictly beat the best finite
static category in the constructed `max_K` family.
-/
theorem randomized_approval_w_selection_constructed_ranking_law_and_static_categories_maxK :
    StrictTopPrefixDominanceOn
        constructedWSelectionRanking1TopPrefixProb
        constructedWSelectionCrossTier ∧
      ∃ oneSidedUp nearTieEps oneSidedBoundaryUp : ℝ,
        0 < oneSidedUp ∧ oneSidedUp < 1 ∧
          0 < nearTieEps ∧ nearTieEps < 1 ∧
            0 < oneSidedBoundaryUp ∧ oneSidedBoundaryUp < 1 ∧
              (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
                  finiteUnivNonempty
                  (fun rule =>
                    finiteOutcomeLearningRate
                      (fun pair =>
                        approvalPairwiseRate
                          (constructedWSelectionStaticCategoryUp
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair)
                          (constructedWSelectionStaticCategoryDown
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair))) <
                finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  ⟨constructedWSelectionRanking1Law_strictTopPrefixDominanceOn,
    constructedWSelectionRandomizedApproval_exists_static_categories_maxK⟩

/--
Concrete feasibility witness for the source proof's W-selection constants:
there are rational values satisfying the ordering, normalization, Q-size, and
base-inequality side conditions used after the constructed table.
-/
theorem randomized_approval_w_selection_source_constants_feasible :
    ∃ ε a T2 T1 Q : ℝ,
      0 < ε ∧ ε < a ∧ a < T2 / 2 ∧ T2 / 2 < T2 ∧ T2 < T1 ∧
        T1 + 2 * T2 + a = 1 ∧
          1 - ε > approvalPairwiseBase T1 T2 ∧
            (T1 + 2 * T2 - 3 * a - ε) / Q < T1 + 3 * a ∧
              3 * a > T1 / Q ∧
                2 < Q ∧
                  1 - T2 + a - ε > approvalPairwiseBase T1 T2 :=
  constructedWSelection_source_constants_feasible

/--
Durham Ward 1 empirical randomization example: with the source probabilities
represented exactly as thousandths, randomizing between 3-approval and
4-approval strictly improves the finite outcome-learning rate over both static
rules for the two pivotal pairs reported in the paper.
-/
theorem durham_ward1_randomized_approval_improves_static3_static4 :
    max
        (finiteOutcomeLearningRate durhamWard1K3Rate)
        (finiteOutcomeLearningRate durhamWard1K4Rate) <
      finiteOutcomeLearningRate durhamWard1RandomizedRate :=
  durhamWard1RandomizedApproval_improves_static3_static4

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: shifting a
positive mass `a` from the reverse approval event to the favorable approval
event strictly improves the pairwise approval learning rate, giving
`r(T1+a,T2-a) > r(T1,T2)` in the paper's notation.
-/
theorem randomized_approval_w_selection_positive_mass_shift_rate_improvement
    {T1 T2 a : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 < a)
    (hbase_pos : 0 < approvalPairwiseBase T1 T2)
    (hshift_base_pos : 0 < approvalPairwiseBase (T1 + a) (T2 - a))
    (horient : T2 ≤ T1)
    (hdown_nonneg : 0 ≤ T2 - a) :
    approvalPairwiseRate T1 T2 <
      approvalPairwiseRate (T1 + a) (T2 - a) :=
  approvalPairwiseRate_lt_of_pos_mass_shift
    hT1 hT2 ha hbase_pos hshift_base_pos horient hdown_nonneg

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: when the
constructed example splits a positive mass transfer between two randomized
approval rules, both resulting pivotal-pair rates strictly beat the static
bottleneck rate `r(T1,T2)`.
-/
theorem randomized_approval_w_selection_split_mass_rate_improvement
    {T1 T2 a p : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 < a)
    (hp_pos : 0 < p) (hp_lt : p < 1)
    (hbase_pos : 0 < approvalPairwiseBase T1 T2)
    (hbase_p_pos : 0 < approvalPairwiseBase (T1 + p * a) (T2 - p * a))
    (hbase_one_sub_pos :
      0 < approvalPairwiseBase (T1 + (1 - p) * a)
        (T2 - (1 - p) * a))
    (horient : T2 ≤ T1)
    (hp_down_nonneg : 0 ≤ T2 - p * a)
    (hone_sub_down_nonneg : 0 ≤ T2 - (1 - p) * a) :
    approvalPairwiseRate T1 T2 <
      min
        (approvalPairwiseRate (T1 + p * a) (T2 - p * a))
        (approvalPairwiseRate (T1 + (1 - p) * a)
          (T2 - (1 - p) * a)) :=
  approvalPairwiseRate_lt_min_of_split_mass_improvement
    hT1 hT2 ha hp_pos hp_lt hbase_pos hbase_p_pos hbase_one_sub_pos
    horient hp_down_nonneg hone_sub_down_nonneg

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: the lower of
the two randomized pivotal-pair rates with split probabilities `p` and `1-p`
is the rate at the smaller split fraction `min(p,1-p)`.
-/
theorem randomized_approval_w_selection_split_rate_min_fraction
    {T1 T2 a p : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 ≤ a)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hbase_p : 0 < approvalPairwiseBase (T1 + p * a) (T2 - p * a))
    (hbase_one_sub :
      0 < approvalPairwiseBase (T1 + (1 - p) * a)
        (T2 - (1 - p) * a))
    (horient : T2 ≤ T1)
    (hdown_p : 0 ≤ T2 - p * a)
    (hdown_one_sub : 0 ≤ T2 - (1 - p) * a) :
    min
        (approvalPairwiseRate (T1 + p * a) (T2 - p * a))
        (approvalPairwiseRate (T1 + (1 - p) * a)
          (T2 - (1 - p) * a)) =
      approvalPairwiseRate (T1 + (min p (1 - p)) * a)
        (T2 - (min p (1 - p)) * a) :=
  approvalPairwiseRate_min_split_eq_min_fraction
    hT1 hT2 ha hp_nonneg hp_le_one hbase_p hbase_one_sub
    horient hdown_p hdown_one_sub

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: a one-sided
approval side case, with unfavorable mass zero and sufficiently small favorable
mass, can be made slower than any fixed positive target rate.
-/
theorem randomized_approval_w_selection_one_sided_sidecase_rate_small
    {targetRate : ℝ} (htarget : 0 < targetRate) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      approvalPairwiseRate ε 0 < targetRate :=
  exists_pos_up_zero_down_rate_lt htarget

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: the near-tie
side case with probabilities `a + ε` versus `a` can also be made slower than
any fixed positive target rate.
-/
theorem randomized_approval_w_selection_near_tie_sidecase_rate_small
    {a targetRate : ℝ} (ha : 0 ≤ a) (htarget : 0 < targetRate) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      approvalPairwiseRate (a + ε) a < targetRate :=
  exists_pos_shift_rate_lt ha htarget

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: the
approval-rate expression tends to zero when the favorable and unfavorable
one-voter approval probabilities converge to the same nonnegative limit.
This is the formal version of the source's `r(...) -> 0` side-case paragraphs.
-/
theorem randomized_approval_w_selection_sidecase_rate_tendsto_zero
    {α : Type*} {l : Filter α} {pUp pDown : α → ℝ} {p : ℝ}
    (hpUp : Filter.Tendsto pUp l (nhds p))
    (hpDown : Filter.Tendsto pDown l (nhds p))
    (hp : 0 ≤ p) :
    Filter.Tendsto
      (fun x => approvalPairwiseRate (pUp x) (pDown x))
      l (nhds 0) :=
  approvalPairwiseRate_tendsto_zero_of_tendsto_same hpUp hpDown hp

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: once a
side-case approval rate tends to zero, it is eventually below any fixed
positive reference rate.
-/
theorem randomized_approval_w_selection_sidecase_rate_eventually_lt
    {α : Type*} {l : Filter α} {pUp pDown : α → ℝ}
    {p targetRate : ℝ}
    (hpUp : Filter.Tendsto pUp l (nhds p))
    (hpDown : Filter.Tendsto pDown l (nhds p))
    (hp : 0 ≤ p)
    (htarget : 0 < targetRate) :
    ∀ᶠ x in l,
      approvalPairwiseRate (pUp x) (pDown x) < targetRate :=
  approvalPairwiseRate_eventually_lt_of_tendsto_same
    hpUp hpDown hp htarget

/--
Source proof step for `lem:randomizebetterapproval_Wselection`: in the
one-sided `K' = L + 1` side case, the paper's base inequality
`base(T1,T2) < 1 - pUp` makes that side-case rate strictly worse than the
reference approval rate.
-/
theorem randomized_approval_w_selection_one_sided_sidecase_rate_worse
    {pUp T1 T2 : ℝ}
    (hbase_pos : 0 < approvalPairwiseBase T1 T2)
    (hbase_lt : approvalPairwiseBase T1 T2 < 1 - pUp) :
    approvalPairwiseRate pUp 0 <
      approvalPairwiseRate T1 T2 :=
  approvalPairwiseRate_zero_down_lt_of_base_lt_one_sub_up
    hbase_pos hbase_lt

/--
Constructed W-selection randomization example: the exact finite table satisfies
strict top-prefix dominance for the designated winner and has a randomized
approval rule with strictly larger finite outcome-learning rate than the two
static rules used in the construction.
-/
theorem randomized_approval_w_selection_constructed_design_invariant_example :
    StrictTopPrefixDominanceOn
        constructedWSelectionTopPrefixProb
        constructedWSelectionCrossTier ∧
      max
          (finiteOutcomeLearningRate constructedWSelectionK1Rate)
          (finiteOutcomeLearningRate constructedWSelectionK2Rate) <
        finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  constructedWSelection_designInvariant_and_randomizedApproval_improves

/--
Mallows high-noise example (`M = 4`, `W = 3`, `phi = 4/5`): using the source
pair-probability formulas for the pivotal pair `(3,4)`, 2-approval has strictly
larger pairwise learning rate than 3-approval.
-/
theorem mallows_high_noise_w3_k2_rate_gt_k3_rate :
    approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) :=
  mallowsHighNoiseW3K2_rate_gt_K3_rate

/--
Mallows high-noise example, end-to-end version: for a four-candidate
identity-centered Mallows law with `q = 4/5`, the actual approval-event
probabilities make 2-approval strictly faster than 3-approval on the source
pivotal pair `(3,4)`.
-/
theorem mallows_high_noise_w3_k2_rate_gt_k3_rate_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    approvalPairwiseRate
        (mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2)) <
      approvalPairwiseRate
        (mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2)) :=
  mallowsHighNoiseW3K2_rate_gt_K3_rate_of_mallows M hcenter hq

/--
Mallows high-noise example, fully concrete version: for the normalized
four-candidate identity-centered Mallows law at `q = 4/5`, the source pivotal
pair `(3,4)` has a strictly larger 2-approval learning rate than 3-approval
learning rate.
-/
theorem mallows_high_noise_w3_k2_rate_gt_k3_rate_concrete_mallows :
    approvalPairwiseRate
        (mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
          (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopThreePairUpProb mallowsHighNoiseW3Spec
          (3 : Candidate 2) (2 : Candidate 2)) <
      approvalPairwiseRate
        (mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
          (2 : Candidate 2) (3 : Candidate 2))
        (mallowsTopTwoPairUpProb mallowsHighNoiseW3Spec
          (3 : Candidate 2) (2 : Candidate 2)) :=
  mallowsHighNoiseW3K2_rate_gt_K3_rate_concrete

/--
Concrete high-noise Mallows `K = 2` pivotal-pair exact-rate certificate: the
finite iid K-approval score-gap mistake probability has the closed-form
approval learning rate for the source pair `(3,4)`.
-/
theorem mallows_high_noise_w3_k2_pair23_exact_rate_certificate_concrete_mallows :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 2 π (2 : Candidate 2))
        (fun π => kApprovalScore 2 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi)) :=
  mallowsHighNoiseW3K2_pair23_exact_rate_certificate_concrete

/--
Concrete high-noise Mallows `K = 1` pivotal-pair exact-rate certificate: the
finite iid K-approval score-gap mistake probability has the closed-form
approval learning rate for the source pair `(3,4)`.
-/
theorem mallows_high_noise_w3_k1_pair23_exact_rate_certificate_concrete_mallows :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 1 π (2 : Candidate 2))
        (fun π => kApprovalScore 1 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi)) :=
  mallowsHighNoiseW3K1_pair23_exact_rate_certificate_concrete

/--
Concrete high-noise Mallows `K = 3` pivotal-pair exact-rate certificate: the
finite iid K-approval score-gap mistake probability has the closed-form
approval learning rate for the source pair `(3,4)`.
-/
theorem mallows_high_noise_w3_k3_pair23_exact_rate_certificate_concrete_mallows :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb mallowsHighNoiseW3Spec.law
        (fun π => kApprovalScore 3 π (2 : Candidate 2))
        (fun π => kApprovalScore 3 π (3 : Candidate 2)))
      (approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi)) :=
  mallowsHighNoiseW3K3_pair23_exact_rate_certificate_concrete

/--
Mallows high-noise W-selection outcome-rate example, fully concrete version:
for the normalized four-candidate identity-centered Mallows law at `q = 4/5`,
the finite outcome-learning rate of 3-approval is strictly lower than the
finite outcome-learning rate of 2-approval.  The finite minimum is proved over
the three winner-vs-loser pairs, so this is the paper's W-selection comparison
rather than only the pivotal-pair calculation.
-/
theorem mallows_high_noise_w3_k2_outcome_rate_gt_k3_outcome_rate_concrete_mallows :
    mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec <
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_concrete

/--
Mallows high-noise W-selection outcome-rate comparison against 1-approval:
for the normalized four-candidate identity-centered Mallows law at `q = 4/5`,
the finite outcome-learning rate of 1-approval is strictly lower than the
finite outcome-learning rate of 2-approval.
-/
theorem mallows_high_noise_w3_k2_outcome_rate_gt_k1_outcome_rate_concrete_mallows :
    mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec <
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3K2_outcomeRate_gt_K1_outcomeRate_concrete

/--
Concrete high-noise Mallows nontrivial-K certificate: in the four-candidate
`W = 3` example, `K = 1`, `K = 2`, and `K = 3` all have their finite
W-selection minimum at source pair `(3,4)`, and `K = 2` strictly beats both
other nontrivial static K-approval mechanisms.
-/
theorem mallows_high_noise_w3_k2_best_among_nontrivial_static_k_concrete_mallows :
    mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K1PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K2PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec =
        mallowsW3K3PairRate mallowsHighNoiseW3Spec (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec <
        mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec ∧
      mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec <
        mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
  mallowsHighNoiseW3_K2_best_among_nontrivial_static_K_concrete

/--
Symbolic high-noise Mallows nontrivial-K certificate: for any four-candidate
identity-centered Mallows law with `0 < q < 1` and `1 < q^2 + q^3`, `K = 1`,
`K = 2`, and `K = 3` all have their finite W-selection minimum at the source
boundary pair `(3,4)`, and `K = 2` strictly beats both other nontrivial static
K-approval mechanisms.
-/
theorem mallows_w3_k2_best_among_nontrivial_static_k_from_mallows_model_q_high_noise
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) (hhigh : 1 < M.q ^ 2 + M.q ^ 3) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M :=
  mallowsW3_K2_best_among_nontrivial_static_K_of_mallows_q_high_noise
    M hcenter hq_lt hhigh

/--
Concrete high-noise Mallows no-randomization theorem: for the normalized
four-candidate identity-centered Mallows law at `q = 4/5`, any randomized
mechanism over `K = 1,2,3` approval is weakly dominated in finite W-selection
learning rate by one of those static K-approval mechanisms.
-/
theorem mallows_high_noise_w3_randomized_k_approval_no_improvement_concrete_mallows
    (weight : Fin 3 → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Fin 3, weight rule) = 1) :
    ∃ rule : Fin 3,
      finiteOutcomeLearningRate
          (mallowsHighNoiseW3RandomizedKApprovalPairRate weight) ≤
        finiteOutcomeLearningRate
          (mallowsW3StaticKApprovalPairRate mallowsHighNoiseW3Spec rule) :=
  mallowsHighNoiseW3_randomizedKApproval_no_improvement_concrete
    weight hweight hsum

/--
Symbolic four-candidate Mallows pivotal-pair certificate: for any
identity-centered Mallows law with `0 < q < 1`, the finite W-selection
minimizer for each nontrivial static rule `K = 1,2,3` is the boundary pair
`(3,4)`.
-/
theorem mallows_w3_static_k_pivotal_pair_from_mallows_model_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1) :
    mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) :=
  ⟨mallowsW3K1OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt,
    mallowsW3K2OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt,
    mallowsW3K3OutcomeRate_eq_pair2_of_mallows_q_lt_one M hcenter hq_lt⟩

/--
Symbolic Mallows boundary-pair theorem for one-approval: for any finite
candidate universe, any center ranking, and any nonempty top-W target, the
finite W-selection minimum is attained at the adjacent center ranks `(W,W+1)`
under one-approval when `0 < q < 1`.
-/
theorem mallows_top_w_one_approval_boundary_pair_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW 1 =
      mallowsTopWKApprovalPairRate M W 1 (topWBoundaryPair M.center W hW) :=
  mallowsTopWKApprovalOutcomeRate_one_eq_boundary M W hW hq_lt

/--
Symbolic Mallows boundary-pair theorem for K-approval: for any finite candidate
universe, any center ranking, any nonempty top-W target, and any nontrivial
approval cutoff `0 < K < n + 2`, the finite W-selection minimum is attained at
the adjacent center ranks `(W,W+1)` when `0 < q < 1`.
-/
theorem mallows_top_w_k_approval_boundary_pair_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2) (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW K =
      mallowsTopWKApprovalPairRate M W K (topWBoundaryPair M.center W hW) :=
  mallowsTopWKApprovalOutcomeRate_eq_boundary M W hW K hK_pos hK_lt hq_lt

/--
Symbolic Mallows exact aggregate error-rate theorem for K-approval: for any
finite candidate universe, any center ranking, any nonempty top-W target, and
any nontrivial approval cutoff `0 < K < n + 2`, the weighted aggregate of iid
pairwise K-approval errors over the cross-tier pairs has exact exponential
rate equal to the adjacent boundary-pair rate when `0 < q < 1`.
-/
theorem mallows_top_w_k_approval_outcome_error_exact_rate_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val) (K : ℕ)
    (hK_pos : 0 < K) (hK_lt : K < n + 2) (hq_lt : M.q < 1)
    {pairWeight : TopWSelectionPair M.center W → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((mallowsTopWKApprovalRateCertificate M W K hK_pos hK_lt hq_lt)
        |>.aggregateError pairWeight)
      (mallowsTopWKApprovalPairRate M W K (topWBoundaryPair M.center W hW)) :=
  mallowsTopWKApprovalOutcomeError_hasExponentialRate_eq_boundary
    M W hW K hK_pos hK_lt hq_lt hweight hweight_pos

/--
Symbolic Mallows randomized K-approval boundary-pair theorem: for any finite
candidate universe, any center ranking, any nonempty top-W target, and any
finite randomized family of nontrivial approval cutoffs, the finite randomized
W-selection minimum is attained at the adjacent center ranks `(W,W+1)` when
`0 < q < 1`.
-/
theorem mallows_top_w_randomized_k_approval_boundary_pair_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight =
      mallowsTopWRandomizedKApprovalPairRate M W K weight
        (topWBoundaryPair M.center W hW) :=
  mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
    M W hW K weight hweight hsum hK_pos hK_lt hq_lt

/--
Symbolic Mallows exact aggregate error-rate theorem for randomized K-approval:
for any finite candidate universe, any center ranking, any nonempty top-W
target, and any finite randomized family of nontrivial approval cutoffs, the
weighted aggregate of iid randomized-rule pairwise errors has exact
exponential rate equal to the adjacent boundary-pair mixed rate when
`0 < q < 1`.  The randomized one-voter law explicitly draws a rule and then a
Mallows ranking.
-/
theorem mallows_top_w_randomized_k_approval_outcome_error_exact_rate_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {pairWeight : TopWSelectionPair M.center W → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((mallowsTopWRandomizedKApprovalRateCertificate
          M W K weight hweight hsum hK_pos hK_lt hq_lt)
        |>.aggregateError pairWeight)
      (mallowsTopWRandomizedKApprovalPairRate M W K weight
        (topWBoundaryPair M.center W hW)) :=
  mallowsTopWRandomizedKApprovalOutcomeError_hasExponentialRate_eq_boundary
    M W hW K weight hweight hsum hK_pos hK_lt hq_lt
    hpairWeight hpairWeight_pos

/--
Symbolic Mallows all-but-one approval probability theorem: in any finite
candidate universe, the `K = n + 1` approval up/down probabilities for an
ordered pair are the normalized Mallows masses of the lower/higher candidate
being ranked last.
-/
theorem mallows_one_loser_k_approval_pair_probabilities_from_mallows_model
    {n : ℕ} (M : MallowsSpec n) {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law (n + 1) hi lo =
        mallowsOneLoserLastRankWeight M lo / M.partition ∧
      kApprovalPairDownProb M.law (n + 1) hi lo =
        mallowsOneLoserLastRankWeight M hi / M.partition :=
  ⟨kApprovalPairUpProb_oneLoser_eq_mallowsLastRankWeight_div_partition
      M hhi_lo,
    kApprovalPairDownProb_oneLoser_eq_mallowsLastRankWeight_div_partition
      M hhi_lo⟩

/--
Symbolic Mallows two-approval probability theorem: in any finite candidate
universe, the `K = 2` approval up-probability for an ordered pair is the
normalized rank-sum of unordered top-two Mallows fibers involving `hi` and a
candidate other than `hi` or `lo`.
-/
theorem mallows_top_two_k_approval_pair_probability_rank_sum_from_mallows_model
    {n : ℕ} (M : MallowsSpec n) (fac : M.RankFactorization)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law 2 hi lo =
      (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              fac.firstSecondTail)
        else 0) / M.partition :=
  kApprovalPairUpProb_two_eq_mallows_rank_sum_div_partition M fac hhi_lo

/--
Symbolic Mallows two-approval probability theorem using the canonical
rank-factorization bundled with the Mallows model.  This removes the explicit
factorization certificate from the paper-facing statement.
-/
theorem mallows_top_two_k_approval_pair_probability_rank_sum_from_mallows_model_canonical
    {n : ℕ} (M : MallowsSpec n)
    {hi lo : Candidate n} (hhi_lo : hi ≠ lo) :
    kApprovalPairUpProb M.law 2 hi lo =
      (∑ other : Candidate n,
        if other ≠ hi ∧ other ≠ lo then
          (1 + M.q) *
            (M.q ^ ((rankOf M.center hi : ℕ) +
                (rankOf M.center other : ℕ) - 1) *
              M.rankFactorization.firstSecondTail)
        else 0) / M.partition :=
  kApprovalPairUpProb_two_eq_mallows_rank_sum_div_partition
    M M.rankFactorization hhi_lo

/--
Symbolic Mallows two-approval boundary-pair theorem: in any finite candidate
universe with at least three candidates, the finite two-approval W-selection
minimum is attained at the adjacent center ranks `(W,W+1)` when `0 < q < 1`.
-/
theorem mallows_top_w_two_approval_boundary_pair_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (fac : M.RankFactorization) (hn : 0 < n)
    (W : Candidate n) (hW : 0 < W.val) (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M W hW 2 =
      mallowsTopWKApprovalPairRate M W 2
        (topWBoundaryPair M.center W hW) :=
  mallowsTopWTwoApprovalOutcomeRate_eq_boundary M fac hn W hW hq_lt

/--
Symbolic Mallows all-but-one approval boundary-pair theorem: for any finite
candidate universe and center ranking, the finite all-but-one W-selection
minimum is attained at the adjacent center ranks `(n+1,n+2)` under
`K = n + 1` approval when `0 < q < 1`.
-/
theorem mallows_top_w_all_but_one_approval_boundary_pair_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (hq_lt : M.q < 1) :
    mallowsTopWKApprovalOutcomeRate M (oneLoserLastRank n)
        (oneLoserLastRank_pos n) (n + 1) =
      mallowsTopWKApprovalPairRate M (oneLoserLastRank n) (n + 1)
        (topWBoundaryPair M.center (oneLoserLastRank n)
          (oneLoserLastRank_pos n)) :=
  mallowsTopWOneLoserApprovalOutcomeRate_eq_boundary M hq_lt

/--
Symbolic four-candidate Mallows no-randomization theorem: for any
identity-centered Mallows law with `0 < q < 1`, any randomized mechanism over
`K = 1,2,3` approval is weakly dominated in finite W-selection learning rate
by one of those static K-approval mechanisms.
-/
theorem mallows_w3_randomized_k_approval_no_improvement_from_mallows_model_q_lt_one
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq_lt : M.q < 1)
    (weight : Fin 3 → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Fin 3, weight rule) = 1) :
    ∃ rule : Fin 3,
      finiteOutcomeLearningRate
          (mallowsW3RandomizedKApprovalPairRate M.q weight) ≤
        finiteOutcomeLearningRate
          (mallowsW3StaticKApprovalPairRate M rule) :=
  mallowsW3_randomizedKApproval_no_improvement_of_mallows
    M hcenter hq_lt weight hweight hsum

/--
Arbitrary finite-candidate Mallows no-randomization theorem: for any Mallows
law with `q < 1`, any randomized finite family of nontrivial K-approval rules
is weakly dominated in finite W-selection learning rate by one of its static
K-approval components.
-/
theorem mallows_k_approval_no_randomization_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ rule : Rule,
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
        mallowsTopWKApprovalOutcomeRate M W hW (K rule) :=
  mallowsTopWRandomizedKApproval_noRandomization
    M W hW hq_lt K hK_pos hK_lt weight hweight hsum

/--
Arbitrary finite-candidate Mallows no-randomization theorem in the source
corollary's "Approval rate optimal mechanism" form: among all nontrivial
static K-approval cutoffs, choose one maximizing the finite W-selection
learning rate; that static cutoff weakly dominates any randomized finite
family of nontrivial K-approval rules.
-/
theorem mallows_k_approval_no_randomization_to_approval_rate_optimal_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ cut : RankingProperPrefixCut n,
      (∀ cut' : RankingProperPrefixCut n,
        mallowsTopWKApprovalOutcomeRate M W hW (cut'.val + 1) ≤
          mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
        mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1) :=
  mallowsTopWRandomizedKApproval_noRandomization_to_optimalStatic
    M W hW hq_lt K hK_pos hK_lt weight hweight hsum

/--
Bundled arbitrary finite-candidate Mallows randomization theorem: the adjacent
boundary pair realizes every static K-approval outcome rate and the randomized
outcome rate, and the randomized mechanism is weakly dominated by one of its
static K-approval components.
-/
theorem mallows_k_approval_randomized_boundary_and_no_randomization_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    (∀ rule : Rule,
      mallowsTopWKApprovalOutcomeRate M W hW (K rule) =
        mallowsTopWKApprovalPairRate M W (K rule)
          (topWBoundaryPair M.center W hW)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight =
        mallowsTopWRandomizedKApprovalPairRate M W K weight
          (topWBoundaryPair M.center W hW) ∧
      ∃ rule : Rule,
        mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
          mallowsTopWKApprovalOutcomeRate M W hW (K rule) :=
  ⟨fun rule =>
      mallowsTopWKApprovalOutcomeRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt,
    mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
      M W hW K weight hweight hsum hK_pos hK_lt hq_lt,
    mallowsTopWRandomizedKApproval_noRandomization
      M W hW hq_lt K hK_pos hK_lt weight hweight hsum⟩

/--
Bundled arbitrary finite-candidate Mallows exact-rate/no-randomization theorem:
each static nontrivial K-approval component has an exact finite aggregate iid
error exponent at the adjacent boundary pair, and the randomized K-approval
mechanism is weakly dominated by one of those static components in finite
W-selection learning rate.
-/
theorem mallows_k_approval_static_exact_rates_and_randomized_no_improvement_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {pairWeight : Rule → TopWSelectionPair M.center W → ℝ}
    (hpairWeight : ∀ rule pair, 0 ≤ pairWeight rule pair)
    (hpairWeight_pos : ∀ rule pair, 0 < pairWeight rule pair) :
    (∀ rule : Rule,
      HasExponentialRate
        ((mallowsTopWKApprovalRateCertificate
            M W (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
          |>.aggregateError (pairWeight rule))
        (mallowsTopWKApprovalPairRate M W (K rule)
          (topWBoundaryPair M.center W hW))) ∧
      ∃ rule : Rule,
        mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
          mallowsTopWKApprovalOutcomeRate M W hW (K rule) :=
  ⟨fun rule =>
      mallowsTopWKApprovalOutcomeError_hasExponentialRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt
        (hpairWeight rule) (hpairWeight_pos rule),
    mallowsTopWRandomizedKApproval_noRandomization
      M W hW hq_lt K hK_pos hK_lt weight hweight hsum⟩

/--
Bundled arbitrary finite-candidate Mallows static exact-rate, randomized
boundary, and no-randomization theorem: every static nontrivial K-approval
component has boundary-pair pivotality and exact finite aggregate iid error
rate, the randomized K-approval outcome rate has the same boundary pair, and
one static component weakly dominates the randomized mechanism in finite
W-selection learning rate.
-/
theorem mallows_k_approval_static_exact_rates_randomized_boundary_and_no_improvement_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {pairWeight : Rule → TopWSelectionPair M.center W → ℝ}
    (hpairWeight : ∀ rule pair, 0 ≤ pairWeight rule pair)
    (hpairWeight_pos : ∀ rule pair, 0 < pairWeight rule pair) :
    (∀ rule : Rule,
      mallowsTopWKApprovalOutcomeRate M W hW (K rule) =
        mallowsTopWKApprovalPairRate M W (K rule)
          (topWBoundaryPair M.center W hW)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight =
        mallowsTopWRandomizedKApprovalPairRate M W K weight
          (topWBoundaryPair M.center W hW) ∧
      (∀ rule : Rule,
        HasExponentialRate
          ((mallowsTopWKApprovalRateCertificate
              M W (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
            |>.aggregateError (pairWeight rule))
          (mallowsTopWKApprovalPairRate M W (K rule)
            (topWBoundaryPair M.center W hW))) ∧
      ∃ rule : Rule,
        mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
          mallowsTopWKApprovalOutcomeRate M W hW (K rule) :=
  ⟨fun rule =>
      mallowsTopWKApprovalOutcomeRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt,
    mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
      M W hW K weight hweight hsum hK_pos hK_lt hq_lt,
    fun rule =>
      mallowsTopWKApprovalOutcomeError_hasExponentialRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt
        (hpairWeight rule) (hpairWeight_pos rule),
    mallowsTopWRandomizedKApproval_noRandomization
      M W hW hq_lt K hK_pos hK_lt weight hweight hsum⟩

/--
Bundled arbitrary finite-candidate Mallows static and randomized exact-rate,
randomized boundary, and no-randomization theorem: every static nontrivial
K-approval component has boundary-pair pivotality and exact finite aggregate
iid error rate, the randomized K-approval aggregate also has the exact
boundary-pair mixed rate, and one static component weakly dominates the
randomized mechanism in finite W-selection learning rate.
-/
theorem mallows_k_approval_static_and_randomized_exact_rates_boundary_and_no_improvement_from_mallows_model_q_lt_one
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule] [DecidableEq Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {pairWeight : Rule → TopWSelectionPair M.center W → ℝ}
    (hpairWeight : ∀ rule pair, 0 ≤ pairWeight rule pair)
    (hpairWeight_pos : ∀ rule pair, 0 < pairWeight rule pair)
    {randomizedPairWeight : TopWSelectionPair M.center W → ℝ}
    (hrandomizedPairWeight : ∀ pair, 0 ≤ randomizedPairWeight pair)
    (hrandomizedPairWeight_pos : ∀ pair, 0 < randomizedPairWeight pair) :
    (∀ rule : Rule,
      mallowsTopWKApprovalOutcomeRate M W hW (K rule) =
        mallowsTopWKApprovalPairRate M W (K rule)
          (topWBoundaryPair M.center W hW)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight =
        mallowsTopWRandomizedKApprovalPairRate M W K weight
          (topWBoundaryPair M.center W hW) ∧
      (∀ rule : Rule,
        HasExponentialRate
          ((mallowsTopWKApprovalRateCertificate
              M W (K rule) (hK_pos rule) (hK_lt rule) hq_lt)
            |>.aggregateError (pairWeight rule))
          (mallowsTopWKApprovalPairRate M W (K rule)
            (topWBoundaryPair M.center W hW))) ∧
      HasExponentialRate
        ((mallowsTopWRandomizedKApprovalRateCertificate
            M W K weight hweight hsum hK_pos hK_lt hq_lt)
          |>.aggregateError randomizedPairWeight)
        (mallowsTopWRandomizedKApprovalPairRate M W K weight
          (topWBoundaryPair M.center W hW)) ∧
      ∃ rule : Rule,
        mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
          mallowsTopWKApprovalOutcomeRate M W hW (K rule) :=
  ⟨fun rule =>
      mallowsTopWKApprovalOutcomeRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt,
    mallowsTopWRandomizedKApprovalOutcomeRate_eq_boundary
      M W hW K weight hweight hsum hK_pos hK_lt hq_lt,
    fun rule =>
      mallowsTopWKApprovalOutcomeError_hasExponentialRate_eq_boundary
        M W hW (K rule) (hK_pos rule) (hK_lt rule) hq_lt
        (hpairWeight rule) (hpairWeight_pos rule),
    mallowsTopWRandomizedKApprovalOutcomeError_hasExponentialRate_eq_boundary
      M W hW K weight hweight hsum hK_pos hK_lt hq_lt
      hrandomizedPairWeight hrandomizedPairWeight_pos,
    mallowsTopWRandomizedKApproval_noRandomization
      M W hW hq_lt K hK_pos hK_lt weight hweight hsum⟩

/--
Concrete high-noise Mallows `K = 1` W-selection aggregate exact-rate theorem:
the finite sum of the three winner-vs-loser iid pairwise error probabilities
has exponential rate equal to the finite 1-approval outcome-learning rate.
-/
theorem mallows_high_noise_w3_k1_outcome_error_exact_rate_concrete_mallows :
    HasExponentialRate
      mallowsHighNoiseW3K1OutcomeErrorProb
      (mallowsW3K1OutcomeRate mallowsHighNoiseW3Spec) :=
  mallowsHighNoiseW3K1_outcome_error_exact_rate_concrete

/--
Concrete high-noise Mallows `K = 2` W-selection aggregate exact-rate theorem:
the finite sum of the three winner-vs-loser iid pairwise error probabilities
has exponential rate equal to the finite 2-approval outcome-learning rate.
-/
theorem mallows_high_noise_w3_k2_outcome_error_exact_rate_concrete_mallows :
    HasExponentialRate
      mallowsHighNoiseW3K2OutcomeErrorProb
      (mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec) :=
  mallowsHighNoiseW3K2_outcome_error_exact_rate_concrete

/--
Concrete high-noise Mallows `K = 3` W-selection aggregate exact-rate theorem:
the finite sum of the three winner-vs-loser iid pairwise error probabilities
has exponential rate equal to the finite 3-approval outcome-learning rate.
-/
theorem mallows_high_noise_w3_k3_outcome_error_exact_rate_concrete_mallows :
    HasExponentialRate
      mallowsHighNoiseW3K3OutcomeErrorProb
      (mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec) :=
  mallowsHighNoiseW3K3_outcome_error_exact_rate_concrete

/--
Concrete high-noise Mallows `K = 1` W-selection aggregate convergence
theorem: the finite sum of the three winner-vs-loser iid pairwise error
probabilities tends to zero.
-/
theorem mallows_high_noise_w3_k1_outcome_error_tendsto_zero_concrete_mallows :
    Filter.Tendsto
      mallowsHighNoiseW3K1OutcomeErrorProb
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K1_outcome_error_tendsto_zero_concrete

/--
Concrete high-noise Mallows `K = 2` W-selection aggregate convergence
theorem: the finite sum of the three winner-vs-loser iid pairwise error
probabilities tends to zero.
-/
theorem mallows_high_noise_w3_k2_outcome_error_tendsto_zero_concrete_mallows :
    Filter.Tendsto
      mallowsHighNoiseW3K2OutcomeErrorProb
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K2_outcome_error_tendsto_zero_concrete

/--
Concrete high-noise Mallows `K = 3` W-selection aggregate convergence
theorem: the finite sum of the three winner-vs-loser iid pairwise error
probabilities tends to zero.
-/
theorem mallows_high_noise_w3_k3_outcome_error_tendsto_zero_concrete_mallows :
    Filter.Tendsto
      mallowsHighNoiseW3K3OutcomeErrorProb
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K3_outcome_error_tendsto_zero_concrete

/--
Model-parametric high-noise Mallows `K = 1` W-selection aggregate exact-rate
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k1_outcome_error_exact_rate_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K1OutcomeErrorProbOf M)
      (mallowsW3K1OutcomeRate M) :=
  mallowsHighNoiseW3K1_outcome_error_exact_rate_of_mallows
    M hcenter hq

/--
Model-parametric high-noise Mallows `K = 2` W-selection aggregate exact-rate
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k2_outcome_error_exact_rate_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K2OutcomeErrorProbOf M)
      (mallowsW3K2OutcomeRate M) :=
  mallowsHighNoiseW3K2_outcome_error_exact_rate_of_mallows
    M hcenter hq

/--
Model-parametric high-noise Mallows `K = 3` W-selection aggregate exact-rate
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k3_outcome_error_exact_rate_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    HasExponentialRate
      (mallowsW3K3OutcomeErrorProbOf M)
      (mallowsW3K3OutcomeRate M) :=
  mallowsHighNoiseW3K3_outcome_error_exact_rate_of_mallows
    M hcenter hq

/--
Model-parametric high-noise Mallows `K = 2` W-selection aggregate convergence
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k2_outcome_error_tendsto_zero_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K2OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K2_outcome_error_tendsto_zero_of_mallows
    M hcenter hq

/--
Model-parametric high-noise Mallows `K = 3` W-selection aggregate convergence
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k3_outcome_error_tendsto_zero_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K3OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K3_outcome_error_tendsto_zero_of_mallows
    M hcenter hq

/--
Model-parametric high-noise Mallows `K = 1` W-selection aggregate convergence
theorem for any four-candidate identity-centered Mallows law with `q = 4/5`.
-/
theorem mallows_high_noise_w3_k1_outcome_error_tendsto_zero_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    Filter.Tendsto
      (mallowsW3K1OutcomeErrorProbOf M)
      Filter.atTop (nhds 0) :=
  mallowsHighNoiseW3K1_outcome_error_tendsto_zero_of_mallows
    M hcenter hq

/--
Mallows high-noise W-selection outcome-rate example, model-parametric version:
for any four-candidate identity-centered Mallows law with `q = 4/5`, the
finite outcome-learning rate of 3-approval is strictly lower than the finite
outcome-learning rate of 2-approval.
-/
theorem mallows_high_noise_w3_k2_outcome_rate_gt_k3_outcome_rate_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M :=
  mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_of_mallows
    M hcenter hq

/--
Mallows high-noise pivotal/min-rate package: for a four-candidate
identity-centered Mallows law with `q = 4/5`, both `K = 2` and `K = 3`
finite W-selection rates are realized at the source pair `(3,4)`, and the
resulting closed rates show that W-approval is not optimal.
-/
theorem mallows_high_noise_w3_pivotal_pair_min_rates_and_w_approval_not_optimal
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K2PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K2Up mallowsHighNoisePhi)
          (mallowsW3K2Down mallowsHighNoisePhi) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K3PairRate M (2 : Fin 3) =
        approvalPairwiseRate
          (mallowsW3K3Up mallowsHighNoisePhi)
          (mallowsW3K3Down mallowsHighNoisePhi) ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M :=
  mallowsHighNoiseW3_pivotalPair_minRates_and_WApproval_not_optimal_of_mallows
    M hcenter hq

/--
Source theorem `lem:mallowsnotWK`, existential form: under the Mallows model
and W-selection goal, W-approval may fail to be approval-rate optimal.
-/
theorem mallows_high_noise_w3_w_approval_not_approval_rate_optimal_counterexample :
    ∃ M : MallowsSpec 2,
      M.center = Equiv.refl (Candidate 2) ∧
        M.q = mallowsHighNoisePhi ∧
          ∃ better : Fin 3,
            better ≠ (2 : Fin 3) ∧
              finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M (2 : Fin 3)) <
                finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M better) :=
  mallowsW3_WApproval_not_approvalRateOptimal_counterexample

/--
Generic Mallows-API form of `lem:mallowsnotWK`: for the concrete high-noise
four-candidate Mallows law and `W = 3`, generic finite W-selection
3-approval has strictly lower outcome-learning rate than generic 2-approval.
-/
theorem mallows_high_noise_w3_w_approval_not_approval_rate_optimal_generic_mallows_api
    (hW : 0 < (3 : Candidate 2).val) :
    mallowsTopWKApprovalOutcomeRate
        mallowsHighNoiseW3Spec (3 : Candidate 2) hW 3 <
      mallowsTopWKApprovalOutcomeRate
        mallowsHighNoiseW3Spec (3 : Candidate 2) hW 2 := by
  have hq_lt : mallowsHighNoiseW3Spec.q < 1 := by
    norm_num [mallowsHighNoiseW3Spec, MallowsSpec.ofQ,
      mallowsHighNoisePhi]
  have hK2_pair :
      mallowsTopWKApprovalPairRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) 2
          (topWBoundaryPair mallowsHighNoiseW3Spec.center
            (3 : Candidate 2) hW) =
        mallowsW3K2PairRate mallowsHighNoiseW3Spec (2 : Fin 3) := by
    simp [mallowsTopWKApprovalPairRate, mallowsTopWKApprovalPairUpProb,
      mallowsTopWKApprovalPairDownProb, mallowsW3K2PairRate,
      mallowsW3WinnerCandidate, mallowsW3LoserCandidate,
      topWBoundaryPair, TopWSelectionPair.hi, TopWSelectionPair.lo]
    rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
        (M := mallowsHighNoiseW3Spec)
        (hi := mallowsHighNoiseW3Spec.center (2 : Candidate 2))
        (lo := mallowsHighNoiseW3Spec.center (3 : Candidate 2))
        (by simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ])]
    rw [kApprovalPairDownProb_eq_pairUpProb_swap]
    rw [← mallowsTopTwoPairUpProb_eq_kApprovalPairUpProb
        (M := mallowsHighNoiseW3Spec)
        (hi := mallowsHighNoiseW3Spec.center (3 : Candidate 2))
        (lo := mallowsHighNoiseW3Spec.center (2 : Candidate 2))
        (by simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ])]
    simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  have hK3_pair :
      mallowsTopWKApprovalPairRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) 3
          (topWBoundaryPair mallowsHighNoiseW3Spec.center
            (3 : Candidate 2) hW) =
        mallowsW3K3PairRate mallowsHighNoiseW3Spec (2 : Fin 3) := by
    simp [mallowsTopWKApprovalPairRate, mallowsTopWKApprovalPairUpProb,
      mallowsTopWKApprovalPairDownProb, mallowsW3K3PairRate,
      mallowsW3WinnerCandidate, mallowsW3LoserCandidate,
      topWBoundaryPair, TopWSelectionPair.hi, TopWSelectionPair.lo]
    rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
        (M := mallowsHighNoiseW3Spec)
        (hi := mallowsHighNoiseW3Spec.center (2 : Candidate 2))
        (lo := mallowsHighNoiseW3Spec.center (3 : Candidate 2))
        (by simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ])]
    rw [kApprovalPairDownProb_eq_pairUpProb_swap]
    rw [← mallowsTopThreePairUpProb_eq_kApprovalPairUpProb
        (M := mallowsHighNoiseW3Spec)
        (hi := mallowsHighNoiseW3Spec.center (3 : Candidate 2))
        (lo := mallowsHighNoiseW3Spec.center (2 : Candidate 2))
        (by simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ])]
    simp [mallowsHighNoiseW3Spec, MallowsSpec.ofQ]
  have hK2_outcome :
      mallowsTopWKApprovalOutcomeRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) hW 2 =
        mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec := by
    calc
      mallowsTopWKApprovalOutcomeRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) hW 2 =
        mallowsTopWKApprovalPairRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) 2
          (topWBoundaryPair mallowsHighNoiseW3Spec.center
            (3 : Candidate 2) hW) := by
          exact mallowsTopWKApprovalOutcomeRate_eq_boundary
            mallowsHighNoiseW3Spec (3 : Candidate 2) hW 2
            (by norm_num) (by norm_num) hq_lt
      _ = mallowsW3K2PairRate mallowsHighNoiseW3Spec (2 : Fin 3) :=
          hK2_pair
      _ = mallowsW3K2OutcomeRate mallowsHighNoiseW3Spec :=
          (mallowsHighNoiseW3K2OutcomeRate_eq_pair2_of_mallows
            mallowsHighNoiseW3Spec rfl rfl).symm
  have hK3_outcome :
      mallowsTopWKApprovalOutcomeRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) hW 3 =
        mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec := by
    calc
      mallowsTopWKApprovalOutcomeRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) hW 3 =
        mallowsTopWKApprovalPairRate
          mallowsHighNoiseW3Spec (3 : Candidate 2) 3
          (topWBoundaryPair mallowsHighNoiseW3Spec.center
            (3 : Candidate 2) hW) := by
          exact mallowsTopWKApprovalOutcomeRate_eq_boundary
            mallowsHighNoiseW3Spec (3 : Candidate 2) hW 3
            (by norm_num) (by norm_num) hq_lt
      _ = mallowsW3K3PairRate mallowsHighNoiseW3Spec (2 : Fin 3) :=
          hK3_pair
      _ = mallowsW3K3OutcomeRate mallowsHighNoiseW3Spec :=
          (mallowsHighNoiseW3K3OutcomeRate_eq_pair2_of_mallows
            mallowsHighNoiseW3Spec rfl rfl).symm
  rw [hK3_outcome, hK2_outcome]
  exact mallowsHighNoiseW3K2_outcomeRate_gt_K3_outcomeRate_concrete

/--
Mallows high-noise example, `K = 2` probability derivation: for a
four-candidate Mallows law centered at the identity ranking, the paper's source
formulas for `t^3_34(2)` and `t^4_34(2)` are obtained from the normalized
top-two Mallows weights.
-/
theorem mallows_high_noise_w3_k2_probabilities_from_rank_factorization
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K2Up M.q ∧
      mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K2Down M.q :=
  ⟨mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
    mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter⟩

/--
Mallows high-noise example, `K = 1` probability derivation: for a
four-candidate Mallows law centered at the identity ranking, the paper's source
formulas for the pivotal pair `(3,4)` are obtained from the normalized
first-choice Mallows weights.
-/
theorem mallows_high_noise_w3_k1_probabilities_from_rank_factorization
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    kApprovalPairUpProb M.law 1 (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K1Up M.q ∧
      kApprovalPairUpProb M.law 1 (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K1Down M.q := by
  constructor
  · rw [kApprovalPairUpProb_one_eq_firstChoiceProb
      M.law (by decide : (2 : Candidate 2) ≠ (3 : Candidate 2))]
    exact mallowsFirstChoiceProb_2_eq M hcenter
  · rw [kApprovalPairUpProb_one_eq_firstChoiceProb
      M.law (by decide : (3 : Candidate 2) ≠ (2 : Candidate 2))]
    exact mallowsFirstChoiceProb_3_eq M hcenter

/--
Mallows high-noise example probability derivation: for a four-candidate Mallows
law centered at the identity ranking, the paper's `K = 2` and `K = 3` source
formulas for the pivotal pair `(3,4)` follow from the reusable first/top-two
rank factorization plus the raw Mallows first-tail theorem under position
reversal.
-/
theorem mallows_high_noise_w3_probabilities_from_rank_factorizations
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K2Up M.q ∧
      mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K2Down M.q ∧
      mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K3Up M.q ∧
      mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K3Down M.q :=
  ⟨mallowsTopTwoPairUpProb_23_eq_mallowsW3K2Up M hcenter,
    mallowsTopTwoPairUpProb_32_eq_mallowsW3K2Down M hcenter,
    mallowsTopThreePairUpProb_23_eq_mallowsW3K3Up M hcenter,
    mallowsTopThreePairUpProb_32_eq_mallowsW3K3Down M hcenter⟩

/--
Mallows high-noise example probability derivation for all nontrivial static
approval rules in the four-candidate `W = 3` instance.  The `K = 1`, `K = 2`,
and `K = 3` source pivotal-pair probabilities all follow from reusable Mallows
rank-factorization identities.
-/
theorem mallows_high_noise_w3_all_static_probabilities_from_rank_factorizations
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2)) :
    kApprovalPairUpProb M.law 1 (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K1Up M.q ∧
      kApprovalPairUpProb M.law 1 (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K1Down M.q ∧
      mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K2Up M.q ∧
      mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K2Down M.q ∧
      mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K3Up M.q ∧
      mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K3Down M.q := by
  rcases mallows_high_noise_w3_k1_probabilities_from_rank_factorization
    M hcenter with ⟨hk1up, hk1down⟩
  rcases mallows_high_noise_w3_probabilities_from_rank_factorizations
    M hcenter with ⟨hk2up, hk2down, hk3up, hk3down⟩
  exact ⟨hk1up, hk1down, hk2up, hk2down, hk3up, hk3down⟩

/--
Closed high-noise Mallows static-approval package: for a four-candidate
identity-centered Mallows law with `q = 4/5`, the paper's pivotal-pair
probability formulas for `K = 1,2,3` are derived from reusable Mallows
rank-factorization identities; the corresponding finite aggregate error
probabilities have exact exponential rates; and `K = 2` strictly beats the
other nontrivial static approval rules for `W = 3`.
-/
theorem mallows_high_noise_w3_all_static_probabilities_exact_rates_and_k2_best_from_mallows_model
    (M : MallowsSpec 2) (hcenter : M.center = Equiv.refl (Candidate 2))
    (hq : M.q = mallowsHighNoisePhi) :
    kApprovalPairUpProb M.law 1 (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K1Up M.q ∧
      kApprovalPairUpProb M.law 1 (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K1Down M.q ∧
      mallowsTopTwoPairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K2Up M.q ∧
      mallowsTopTwoPairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K2Down M.q ∧
      mallowsTopThreePairUpProb M (2 : Candidate 2) (3 : Candidate 2) =
        mallowsW3K3Up M.q ∧
      mallowsTopThreePairUpProb M (3 : Candidate 2) (2 : Candidate 2) =
        mallowsW3K3Down M.q ∧
      HasExponentialRate
        (mallowsW3K1OutcomeErrorProbOf M)
        (mallowsW3K1OutcomeRate M) ∧
      HasExponentialRate
        (mallowsW3K2OutcomeErrorProbOf M)
        (mallowsW3K2OutcomeRate M) ∧
      HasExponentialRate
        (mallowsW3K3OutcomeErrorProbOf M)
        (mallowsW3K3OutcomeRate M) ∧
      mallowsW3K1OutcomeRate M = mallowsW3K1PairRate M (2 : Fin 3) ∧
      mallowsW3K2OutcomeRate M = mallowsW3K2PairRate M (2 : Fin 3) ∧
      mallowsW3K3OutcomeRate M = mallowsW3K3PairRate M (2 : Fin 3) ∧
      mallowsW3K1OutcomeRate M < mallowsW3K2OutcomeRate M ∧
      mallowsW3K3OutcomeRate M < mallowsW3K2OutcomeRate M := by
  rcases mallows_high_noise_w3_all_static_probabilities_from_rank_factorizations
    M hcenter with
    ⟨hk1up, hk1down, hk2up, hk2down, hk3up, hk3down⟩
  rcases mallowsHighNoiseW3_K2_best_among_nontrivial_static_K_of_mallows
    M hcenter hq with
    ⟨hk1min, hk2min, hk3min, hk1lt, hk3lt⟩
  exact
    ⟨hk1up, hk1down, hk2up, hk2down, hk3up, hk3down,
      mallows_high_noise_w3_k1_outcome_error_exact_rate_from_mallows_model
        M hcenter hq,
      mallows_high_noise_w3_k2_outcome_error_exact_rate_from_mallows_model
        M hcenter hq,
      mallows_high_noise_w3_k3_outcome_error_exact_rate_from_mallows_model
        M hcenter hq,
      hk1min, hk2min, hk3min, hk1lt, hk3lt⟩

end

end GGSG19TopThree
