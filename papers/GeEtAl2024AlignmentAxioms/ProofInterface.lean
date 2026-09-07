import GeEtAl2024AlignmentAxioms.PaperInterface
import GeEtAl2024AlignmentAxioms.MainTheorems

/-!
# Proof interface: Ge et al. (2024)

Each theorem below is the unique proof endpoint for one complete source-result
`Spec` in `PaperInterface.lean`.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- The paper-facing standard-loss formulation is exactly the source-domain
nonnegativity condition together with the reusable ranking-level optimizer
predicate. -/
theorem standardLossFormulationSpec_iff_nonnegative_and_minimizing
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n
      (LinearFeasibleRanking features)) :
    standardLossFormulationSpec features loss rule ↔
      (∀ input, 0 ≤ loss input) ∧
        IsStandardLossMinimizing features loss rule := by
  rfl

/-- Checked uniqueness and explicit linear-infeasibility observations after Definition 2.2. -/
theorem definition2_2_pairwiseMajorityConsistencyAndConsequences :
    definition2_2_pairwiseMajorityConsistencyAndConsequencesSpec := by
  refine ⟨?_, c1ProfilePlus1_has_no_pairwiseMajorityRanking, ?_⟩
  · intro Voter _ n feasible rule
    exact definition2_2_pairwiseMajorityConsistent_core feasible rule
  · intro Voter _ n profile first second hfirst hsecond
    exact pairwiseMajorityRanking_unique profile first second hfirst hsecond

/-- Checked finite counterexample form of source Theorem 3.1. -/
theorem theorem3_1_lossBasedImpossibility : theorem3_1_lossBasedImpossibilitySpec := by
  intro loss hloss_nonnegative hloss_shape hinfimum
  have hexists : ∃ input, loss input < loss 0 := by
    by_contra hnot
    push Not at hnot
    have hlower : loss 0 ≤ sInf (Set.range loss) := by
      apply le_csInf
      · exact Set.range_nonempty loss
      · intro value hvalue
        obtain ⟨input, rfl⟩ := hvalue
        exact hnot input
    exact (not_le_of_gt hinfimum) hlower
  rcases hloss_shape with ⟨hmonotone, hconvex⟩ | hstrict
  · right
    obtain ⟨negativeInput, hnegative, hdip⟩ :=
      exists_negative_dip_of_monotone hmonotone hexists
    exact theorem3_1_negativeInputSixCandidate_of_monotoneConvex_sourceAssumptions
      hloss_nonnegative hmonotone hconvex hnegative hdip
  · obtain ⟨input, hdip⟩ := hexists
    by_cases hpositive : 0 < input
    · left
      refine ⟨input, hpositive, hdip, ?_⟩
      intro rule hminimizes
      exact positiveInput_branch_fails_pareto_and_pmc
        hloss_nonnegative hstrict hpositive hdip rule hminimizes
    · right
      have hnegative : input < 0 := by
        have hnonpositive : input ≤ 0 := le_of_not_gt hpositive
        have hne : input ≠ 0 := by
          intro hzero
          subst input
          exact (lt_irrefl (loss 0)) hdip
        exact lt_of_le_of_ne hnonpositive hne
      exact theorem3_1_negativeInputSixCandidate_of_strictConvex_sourceAssumptions
        hloss_nonnegative hstrict hnegative hdip

/-- Checked source Lemma 3.2 under either source loss alternative. -/
theorem lemma3_2_unconstrainedCoreSeparation :
    lemma3_2_unconstrainedCoreSeparationSpec := by
  intro loss negativeInput hloss_nonnegative hloss_shape hnegative hdip
  rcases hloss_shape with ⟨hmonotone, hconvex⟩ | hstrict
  · have hcontinuous := continuous_of_convexOn_univ hconvex
    obtain ⟨w, z1, z2, z3, z4, hw_pos, hderiv1, hderiv2, hderiv3, hderiv4,
      hz1_nonnegative, hz12, hz23, hz34⟩ :=
      exists_four_oneSided_derivative_data_of_monotone_convex_negative_dip
        hloss_nonnegative hmonotone hcontinuous hconvex hnegative hdip
    obtain ⟨p, hhalf, hp_lt_one, hseparation⟩ :=
      lemma3_2_weightedLoss_separation_from_four_oneSidedDerivatives
        hloss_nonnegative hcontinuous hconvex hnegative hdip hw_pos
        hderiv1 hderiv2 hderiv3 hderiv4 hz1_nonnegative hz12 hz23 hz34
    exact ⟨p, hhalf, hp_lt_one.le, hseparation⟩
  · have hcontinuous := continuous_of_convexOn_univ hstrict.convexOn
    obtain ⟨w, z1, z2, z3, z4, hw_pos, hderiv1, hderiv2, hderiv3, hderiv4,
      hz1_nonnegative, hz12, hz23, hz34⟩ :=
      exists_four_oneSided_derivative_data_of_strictConvex_negative_dip
        hcontinuous hstrict hnegative hdip
    obtain ⟨p, hhalf, hp_lt_one, hseparation⟩ :=
      lemma3_2_weightedLoss_separation_from_four_oneSidedDerivatives
        hloss_nonnegative hcontinuous hstrict.convexOn hnegative hdip hw_pos
        hderiv1 hderiv2 hderiv3 hderiv4 hz1_nonnegative hz12 hz23 hz34
    exact ⟨p, hhalf, hp_lt_one.le, hseparation⟩

/-- Checked conditional optimizer transfer for source Lemma 3.3. -/
theorem lemma3_3_coreMinimizers : lemma3_3_coreMinimizersSpec := by
  intro g A1 A2 hA hminimum hseparation
  exact lemma3_3_core_minimizers hA hminimum hseparation

/-- Checked strict-cone repair of source Lemma 3.4. -/
theorem lemma3_4_correctedCopyCone : lemma3_4_correctedCopyConeSpec := by
  intro g A3 A4 δ hA3_pos hδ_pos hδ_bounds hminimizer_bounds
  exact corrected_lemma3_4_core_minimizers_in_allCopiesBelowOriginalCone
    hA3_pos hδ_pos hδ_bounds hminimizer_bounds

/-- Checked perturbation-gap repair of source Lemma 3.5. -/
theorem lemma3_5_correctedPerturbationGap : lemma3_5_correctedPerturbationGapSpec := by
  intro loss negativeInput δ weight base hweight_half hweight_lt_one
    hloss_nonnegative hconvex hnegative hdip hcore_global hcore_below
  exact exists_radius_cPrimeAboveOrTiedGap_sixCandidateSourceObjective
    (le_of_lt hweight_half) hweight_lt_one
    hloss_nonnegative (continuous_of_convexOn_univ hconvex)
    (exists_right_tail_gt_of_convex_negative_dip hconvex hnegative hdip)
    hcore_global hcore_below

/-- Checked finite majority-loss endpoint for source Theorem 3.6. -/
theorem theorem3_6_majorityLoss : theorem3_6_majorityLossSpec := by
  intro Voter _ n dimension features loss rule hloss_nonnegative hloss_monotone
    hloss_zero_gt_infimum hminimizes
  exact theorem3_6_majorityLoss_core features loss rule hloss_nonnegative hloss_monotone
    hloss_zero_gt_infimum hminimizes

/-- Checked exact Theorem 3.7 endpoint and every attached mathematical clause. -/
theorem theorem3_7_C1FailsParetoAndConsequences :
    theorem3_7_C1FailsParetoAndConsequencesSpec := by
  refine ⟨theorem3_7_C1_failsPareto_finiteInstance, ?_, ?_,
    c1ProfilePlus1_has_no_pairwiseMajorityRanking⟩
  · intro Voter _ n feasible rule hC1 hPareto
    exact c1_and_pareto_imply_pairwiseMajorityConsistent feasible rule hC1 hPareto
  · intro Voter _ _ n profile ranking hmajority
    exact pairwiseMajorityRanking_respectsPareto profile ranking hmajority

/-- Checked finite fixed-tie LCPO construction for all four Theorem 4.3 axioms. -/
theorem theorem4_3_constructedFixedTieLCPO : theorem4_3_constructedFixedTieLCPOSpec := by
  intro Voter _ _ n feasible fallback hfallback
  exact theorem4_3_constructed_fixedTieLCPO_core feasible fallback hfallback

/-- Checked exact Appendix-B profile, majority ranking, uniqueness, and infeasibility. -/
theorem appendixBExplicitInfeasiblePMC : appendixBExplicitInfeasiblePMCSpec := by
  exact appendixB_uniquePMC_but_infeasible

/-- Checked Copeland and LCPO branches of source Theorem C.2. -/
theorem theoremC_2_copelandAndLCPOFailSeparability :
    theoremC_2_copelandAndLCPOFailSeparabilitySpec := by
  constructor
  · intro rule hcopeland
    exact theoremC_2_consistentlyTieBrokenCopeland_failsRankingSeparability rule hcopeland
  · intro copelandRule lcpoRule hlcpo
    exact theoremC_2_consistentlyTieBrokenLCPO_failsRankingSeparability
      copelandRule lcpoRule hlcpo

/-- Checked PMC and separability components of source Theorem C.3. -/
theorem theoremC_3_linearKemeny : theoremC_3_linearKemenySpec := by
  intro n feasible fallback hfallback voterCount
  exact ⟨canonicalKemenyRule_pairwiseMajorityConsistent feasible fallback hfallback voterCount,
    canonicalKemenyRule_rankingSeparability feasible fallback hfallback⟩

/-- Checked literal finite counterexample of source Theorem C.4. -/
theorem theoremC_4_linearKemenyFailsParetoAndMajorityConsistency :
    theoremC_4_linearKemenyFailsParetoAndMajorityConsistencySpec := by
  intro rule hselector
  exact theoremC_4_linearKemeny_failsParetoAndMajorityConsistency rule hselector

/-- Checked literal Pareto-Kemeny counterexample of source Theorem C.5. -/
theorem theoremC_5_paretoKemenyFailsSeparabilityAndMajorityConsistency :
    theoremC_5_paretoKemenyFailsSeparabilityAndMajorityConsistencySpec := by
  intro rule hselector hfirst
  exact theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency
    rule hselector hfirst

/-- Checked majority, winner-monotonicity, and separability components of Theorem C.6. -/
theorem theoremC_6_fixedTieLeximaxPlurality : theoremC_6_fixedTieLeximaxPluralitySpec := by
  intro n feasible rule hselector
  exact ⟨fun voterCount =>
      fixedTieLeximaxPluralitySelector_majorityConsistent feasible (rule voterCount)
        (hselector voterCount),
    fun voterCount =>
      fixedTieLeximaxPluralitySelector_winnerMonotonic feasible (rule voterCount)
        (hselector voterCount),
    fixedTieLeximaxPluralitySelector_rankingSeparability feasible rule hselector⟩

end GeEtAl2024AlignmentAxioms
