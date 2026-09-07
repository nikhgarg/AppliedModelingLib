import NoothigattuEtAl2020PairwiseComparisons.PaperInterface

/-!
# Proof Interface: Axioms for Learning from Pairwise Comparisons

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace NoothigattuEtAl2020PairwiseComparisons

/-- Checked proof endpoint for source Claim A.1 (Supplement p. 13). -/
theorem claimA1_coin_flip_likelihood_proof :
    claimA1_coin_flip_likelihoodSpec :=
  claimA1_coin_flip_likelihood

/-- Checked proof endpoint for source Claim C.1 (Supplement p. 17). -/
theorem claimC1_strict_crossed_product_proof :
    claimC1_strict_crossed_productSpec := by
  intro c d e f hc hd he hf hdc hfe
  exact claimC1_strict_crossed_product hc hd he hf hdc hfe

/-- Checked proof endpoint for source Lemma 2.1 (main p. 4; Supplement A.1). -/
theorem lemma2_1_mle_exists_proof :
    lemma2_1_mle_existsSpec := by
  intro Alternative instFintype dataset link reference instDecidableEq hcontinuous hstrict
  exact lemma2_1_mle_exists dataset link reference hcontinuous hstrict

/-- Checked proof endpoint for source Lemma 2.2 (main p. 4; Supplement A.2). -/
theorem lemma2_2_one_neighbor_perfect_fit_proof :
    lemma2_2_one_neighbor_perfect_fitSpec := by
  intro Alternative instFintype dataset link reference score first second instDecidableEq
    hmle hneighbor hfirst hsecond hcontinuous hstrict
  exact lemma2_2_one_neighbor_perfect_fit dataset link reference score hmle hneighbor
    hfirst hsecond hcontinuous hstrict

/-- Checked proof endpoint for source Lemma 2.3 (main p. 4; Supplement A.3). -/
theorem lemma2_3_mle_supNorm_bound_proof :
    lemma2_3_mle_supNorm_boundSpec := by
  intro Alternative instFintype instDecidableEq dataset link reference score hmle hcomplete
    hcontinuous hstrict
  exact lemma2_3_mle_supNorm_bound dataset link reference score hmle hcomplete
    hcontinuous hstrict

/-- Checked proof endpoint for source Lemma 2.4 (main p. 4; Supplement B). -/
theorem lemma2_4_strictConcavity_and_unique_mle_proof :
    lemma2_4_strictConcavity_and_unique_mleSpec := by
  intro Alternative instFintype dataset link reference hlogStrict instDecidableEq
  exact lemma2_4_strictConcavity_and_unique_mle dataset (link : ℝ → ℝ) reference
    hlogStrict

/-- Checked proof endpoint for source Theorem 3.2 (main p. 5; Supplement C). -/
theorem theorem3_2_mle_satisfies_pareto_efficiency_proof :
    theorem3_2_mle_satisfies_pareto_efficiencySpec := by
  intro link hstrict Alternative instFintype dataset reference score first second instDecidableEq
    hmle hdominance
  exact theorem3_2_mle_satisfies_pareto_efficiency dataset link reference score hstrict
    hmle hdominance

/-- Checked proof endpoint for source Theorem 4.2 (main p. 5; Supplement D). -/
theorem theorem4_2_mle_satisfies_monotonicity_proof :
    theorem4_2_mle_satisfies_monotonicitySpec := by
  intro link hstrict hlogConcave _hdifferentiable Alternative instFintype instDecidableEq
  exact theorem4_2_mle_satisfies_monotonicity link hstrict hlogConcave

/-- Checked proof endpoint for source Theorem 5.3 (main p. 7; Supplement E). -/
theorem theorem5_3_mle_violates_pairwise_majority_consistency_proof :
    theorem5_3_mle_violates_pairwise_majority_consistencySpec :=
  theorem5_3_mle_violates_pairwise_majority_consistency

/-- Checked proof endpoint for source Theorem 6.3 (main p. 8; Supplement F). -/
theorem theorem6_3_mle_violates_separability_proof :
    theorem6_3_mle_violates_separabilitySpec :=
  theorem6_3_mle_violates_separability

end NoothigattuEtAl2020PairwiseComparisons
