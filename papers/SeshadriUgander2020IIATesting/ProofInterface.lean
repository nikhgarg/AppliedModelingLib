import SeshadriUgander2020IIATesting.PaperInterface

/-!
# Proof interface: Seshadri--Ugander (2020)

Each declaration below is the exact proof endpoint for one transparent source
Spec in `PaperInterface.lean`.
-/

namespace SeshadriUgander2020IIATesting

open AppliedModelingLib.Foundations.Graph

theorem lemma2_testing_reduction : lemma2_testing_reductionSpec := by
  intro F D W ε δ hε_nonneg hε_le_one hδ_nonneg N
  constructor
  · intro hscale
    exact D.lemma2_testing_reduction W ε δ hε_nonneg hε_le_one
      hδ_nonneg hscale N
  · intro hmean hfour
    nlinarith

theorem lemma3_chiSquare_mixture : lemma3_chiSquare_mixtureSpec := by
  exact ChoiceSystem.chiSquare_perturb_family_add_one_le

theorem lemma4_cycle_chiSquare : lemma4_cycle_chiSquareSpec := by
  exact ChoiceSystem.CycleDecomposition.chiSquare_oriented_family_add_one_le

theorem theorem1_testing_lower_bound : theorem1_testing_lower_boundSpec := by
  intro F D W δ hδ_pos hsmall N hN_pos
  refine ⟨D.theorem1_productTestingLowerBound W δ hδ_pos.le hsmall N, ?_, ?_⟩
  · exact D.theorem1_sampleLowerBound_of_hasQuarterAccurateTest
      W δ hδ_pos hsmall N
  · exact D.theorem1_radiusLowerBound_of_hasQuarterAccurateTest
      W δ hδ_pos hsmall N hN_pos

theorem corollary1_global_lower_bound_corrected :
    corollary1_global_lower_bound_correctedSpec := by
  exact ChoiceFrame.productTestingLowerBound_sourceCorollaryOne

theorem fact_convex_hull_dense : fact_convex_hull_denseSpec := by
  exact ChoiceSystem.finiteConvexHullIIA_dense_totalVariation

theorem lemma_iia_projection_invariance :
    lemma_iia_projection_invarianceSpec := by
  exact ChoiceSystem.iiaProjection_eq_of_marginals

theorem fact_entropy_cross_entropy : fact_entropy_cross_entropySpec := by
  exact appendixFact5_maxEntropy

theorem lemma_bipartite_cycle_decomposition :
    lemma_bipartite_cycle_decompositionSpec := by
  intro V _ _ G _ left right hBipartite
  obtain ⟨k, packing, hfirst⟩ :=
    exists_bipartite_two_one_cycle_packing hBipartite
  have hsecond := packing.parity_budget hBipartite
  obtain ⟨P, hresidual⟩ := packing.exists_partialSimpleCyclePacking
  have hsourceCap : 4 * Nat.log 2 left.ncard ≤
      2 * ⌊2 * Real.logb 2 left.ncard⌋₊ :=
    four_natLog_le_two_natFloor_two_logb _
  refine ⟨P.relaxLength hsourceCap, ?_⟩
  rw [P.usedEdges_relaxLength]
  exact hresidual.trans (le_min hfirst hsecond)

theorem lemma_comparison_incidence_decomposition_corrected :
    lemma_comparison_incidence_decomposition_correctedSpec := by
  intro F hEulerian hnfour hden
  obtain ⟨P, Q, hQcomplete, hbudget, _⟩ :=
    F.eulerian_incidenceGraph_exists_source_twoTierCycleBounds hEulerian
  let D := F.composedCycleDecomposition P Q hQcomplete
  refine ⟨D, ?_, ?_⟩
  · simpa [D, ChoiceFrame.sourceCorollaryMeanBound] using
      F.sourceComposed_cycleMean_le_source_min
        P Q hQcomplete hbudget hnfour hden
  · simpa [D, ChoiceFrame.sourceCorollaryDispersionBound] using
      F.sourceComposed_cycleDispersion_le_source_min
        P Q hQcomplete hbudget hnfour

theorem corollary_all_even_subsets_corrected :
    corollary_all_even_subsets_correctedSpec := by
  exact AllEvenChoiceSet.exists_cycleDecomposition_five_log_of_three

end SeshadriUgander2020IIATesting
