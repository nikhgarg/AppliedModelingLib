import JGS23SupplySideRecommenderSystems.PaperInterface

/-!
# Checked endpoints for the JGS source interface

Each theorem below realizes the corresponding transparent source `Spec` in
`PaperInterface`.  Proof implementations and legacy convenience theorems stay
outside the source interface.
-/

namespace JGS23SupplySideRecommenderSystems

open MeasureTheory

private theorem correctedInfiniteTwoGenreContentEquilibriumSpec_of_structure
    {cdf : ℝ → ℝ} {β θ : ℝ}
    (h : CorrectedInfiniteTwoGenreContentEquilibrium cdf β θ) :
    correctedInfiniteTwoGenreContentEquilibriumSpec cdf β θ := by
  refine ⟨h.firstGenre, h.secondGenre, h.conditionalQuality,
    h.firstWeight, h.secondWeight, h.firstGenre_nonnegative,
    h.secondGenre_nonnegative, h.firstGenre_l2_norm, h.secondGenre_l2_norm,
    h.conditionalQuality_probability, h.conditionalQuality_cdf,
    h.conditionalQuality_support_nonnegative, h.firstWeight_nonnegative,
    h.secondWeight_nonnegative, h.firstWeight_eq_half, h.secondWeight_eq_half,
    h.weights_sum, ?_, ?_⟩
  · intro r hr
    simpa [infiniteTwoGenreContentObjectiveSpec, normPowerCostSpec,
      correctedInfiniteTwoGenreContentObjective] using h.first_support_maximizes hr
  · intro r hr
    simpa [infiniteTwoGenreContentObjectiveSpec, normPowerCostSpec,
      correctedInfiniteTwoGenreContentObjective] using h.second_support_maximizes hr

private def finiteGenreConditionalNormLaw_of_spec
    {G : ℕ} {μ : MixedContentStrategy 2} {angle : Fin G → ℝ}
    (h : finiteGenreConditionalNormLawSpec μ angle) :
    FiniteGenreConditionalNormLaw μ angle :=
  ⟨h.weight, h.radial, h.weight_pos, h.weights_sum, h.radial_probability,
    h.radial_support_nonnegative, h.radial_has_positive_support, h.radial_cdf_c1,
    h.decomposition⟩

theorem propositionPure : propositionPureSpec := by
  simpa [propositionPureSpec] using @paper_not_pure_nash_norm_rpow_cost

theorem propositionExistence : propositionExistenceSpec := by
  simpa [propositionExistenceSpec, symmetricMixedNashModelSpec, normPowerCostSpec,
    paper_norm_rpow_cost] using @paper_proposition_existence_norm_rpow_cost

theorem propositionAtom : propositionAtomSpec := by
  simpa [propositionAtomSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash] using
    @paper_proposition_atom_atomless_of_source_symmetric_mixed_nash

theorem corollaryOnePopulation : corollaryOnePopulationSpec := by
  simpa [corollaryOnePopulationSpec, symmetricMixedNashModelSpec,
    SourceSymmetricMixedNash, normPowerCostSpec, paper_single_genre_cdf,
    singleGenreCdf, singleGenreCdfRaw] using @paper_corollary_onepopulation_concrete_full

theorem exampleOneDimensionalSetup : exampleOneDimensionalSetupSpec := by
  intro P _ _ β u genre ν hβ hu hgenre hgenre_norm hscore hmax hmeas
  simpa [exampleOneDimensionalSetupSpec, paper_single_genre_cdf,
    singleGenreCdf, singleGenreCdfRaw] using
    (corollaryOnePopulation (N := 1) ν hβ hu hgenre hgenre_norm hscore hmax hmeas)

theorem theoremSingleGenre : theoremSingleGenreSpec := by
  intro D N P _ _ _ users ν β hβ husers husers_nonzero hperturb hcompact hcontinuous
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hiff :
      ((∃ (μ : MixedContentStrategy D) (genre : Content D),
        symmetricMixedNashModelSpec (P := P) users (normPowerCostSpec ν β) μ ∧
        nonzeroSupportGenresSpec ν μ = ({genre} : Set (Content D))) ↔
        SingleGenreProductSupCondition
          {y : Fin N → ℝ | paper_powered_unit_image users
            (fun p => NonnegativeContent p ∧ ν.norm p ≤ 1) β y}) := by
    simpa [symmetricMixedNashModelSpec, SourceSymmetricMixedNash,
      nonzeroSupportGenresSpec, SourceNonzeroSupportGenres, normPowerCostSpec] using
      (paper_theorem_singlegenre_corrected_compact_source_iff ν hβ_pos husers
        husers_nonzero hperturb hcompact hcontinuous)
  refine ⟨hiff, ?_, ?_⟩
  · intro hno μ genre hnash hgenre
    exact hno (hiff.mp ⟨μ, genre, hnash, hgenre⟩)
  · intro β' hβ'_pos hβ'_le hproduct
    exact paper_theorem_singlegenre_product_sup_condition_of_le_exponent_of_compact_sublevels
      hβ'_pos hβ'_le husers hcompact hproduct

theorem lemmaOptimizationProgram : lemmaOptimizationProgramSpec := by
  intro D N P _ _ _ users ν β hβ husers husers_nonzero hcompact
  simpa [optimizationProgramCertificate, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, normPowerCostSpec] using
    paper_theorem_singlegenre_concrete_source_symmetric_mixed_nash_iff_product_sup_condition_of_compact_sublevels
      (D := D) (N := N) (P := P) (users := users) ν hβ husers husers_nonzero hcompact

theorem lemmaOptimizationProgramRestated : lemmaOptimizationProgramRestatedSpec := by
  intro D N P _ _ _ users ν β hβ husers husers_nonzero hcompact
  simpa [optimizationProgramCertificate, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, normPowerCostSpec] using
    paper_theorem_singlegenre_concrete_source_symmetric_mixed_nash_iff_product_sup_condition_of_compact_sublevels
      (D := D) (N := N) (P := P) (users := users) ν hβ husers husers_nonzero hcompact

theorem corollaryTwoUsers : corollaryTwoUsersSpec := by
  simpa [corollaryTwoUsersSpec, symmetricMixedNashModelSpec,
    SourceSymmetricMixedNash, nonzeroSupportGenresSpec, SourceNonzeroSupportGenres,
    normPowerCostSpec] using
    @paper_corollary_twousers_corrected_single_genre_equilibrium_iff_phase_threshold

theorem propositionPTwo : propositionPTwoSpec := by
  intro β hβ
  refine ⟨?_, pTwoStandardBasisValueMap_map_contentMeasure β, ?_, ?_, ?_⟩
  · simpa [symmetricMixedNashModelSpec, SourceSymmetricMixedNash, normPowerCostSpec] using
      pTwoSourceContentMeasure_is_sourceSymmetricMixedNash hβ
  · simpa [pTwoSourceCircleSupportSet] using
      pTwoSourceCircleMeasure_support_eq_supportSet hβ
  · change pTwoSourceCircleMeasure β =
      Measure.map (pTwoSourceCircleFromAngle β) pTwoSourceAngleDensityMeasure
    exact pTwoSourceCircleMeasure_eq_densityAngleMeasure_map β
  · intro z
    rw [pTwoSourceCircleMeasure_first_full_cdf hβ,
      pTwoSourceCircleFullCoordinateCdf_eq_sourceMarginalCdf hβ]
    rfl

theorem propositionFiniteP : propositionFinitePSpec := by
  intro P hP
  refine ⟨?_, finitePStandardBasisValueMap_map_contentMeasure P, ?_, ?_⟩
  · simpa [symmetricMixedNashModelSpec, normPowerCostSpec] using
      finitePSourceContentMeasure_is_sourceSymmetricMixedNash hP
  · simpa [finitePSourceCurveSupportSet] using
      finitePSourceCurveMeasure_support_eq_source_curve hP
  · intro z
    exact finitePSourceCurveMeasure_first_cdf_eq_sourceMarginalCdf hP z

theorem claimNecessarySufficient : claimNecessarySufficientSpec := by
  simpa [claimNecessarySufficientSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash,
    paper_necessarysuff_tie_aware_objective, strictScoreMassReparamObjective] using
    @paper_necessarysuff_tie_aware_iff

theorem theoremPhaseTransition : theoremPhaseTransitionSpec := by
  intro P _ β θ μ _ hP hβ hθ hθupper hnash hac hdiff1 hdiff2
  have htransition :=
    paper_canonical_two_user_corrected_phase_transition
      (P := P) hP hβ hθ hθupper (by simpa [normPowerCostSpec] using hnash)
      hac hdiff1 hdiff2
  refine ⟨htransition.1, ?_⟩
  intro hphase G hG angle weight radial hweight_pos hweights_sum
    hradial_probability hradial_support_nonnegative hradial_has_positive_support
    hradial_cdf_c1 hdecomposition hinjective hangle
  let law : finiteGenreConditionalNormLawSpec μ angle :=
    ⟨weight, radial, hweight_pos, hweights_sum, hradial_probability,
      hradial_support_nonnegative, hradial_has_positive_support, hradial_cdf_c1,
      hdecomposition⟩
  exact htransition.2 hphase hG angle
    (finiteGenreConditionalNormLaw_of_spec law) hinjective hangle

private theorem infiniteGenreConclusion
    {β θ : ℝ} (hθ : 0 < θ) (hθupper : θ < Real.pi / 2)
    (hphase : twoUserPhaseThreshold θ < β) :
    ∃ a C1 C2 A B phi : ℝ,
      infiniteProducerModelSpec
        (fun q : ℝ =>
          if q ≤ 0 then 0
          else if a ≤ q then 1
          else
            let k : ℕ := by
              classical
              exact if h : ∃ n : ℕ, a * C2 ^ n ≤ q then Nat.find h else 0
            if Even k then C2 ^ ((k : ℝ) * β)
            else C1 ^ (-2 : ℝ) * C2 ^ (-2 * ((k / 2 : ℕ) : ℝ) * β) *
              q ^ (2 * β)) β θ ∧
      phi ∈ Set.Icc 0 (θ / 2) ∧
      IsMaxOn (fun x : ℝ =>
        (Real.cos x) ^ β + (Real.cos (θ - x)) ^ β) (Set.Icc 0 (θ / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ β ∧ C1 = 1 + C2 ^ β ∧
      A = Real.cos phi ∧ B = Real.cos (θ - phi) ∧ C2 = B / A := by
  rcases paper_exists_corrected_infinite_two_genre_content_equilibrium_of_phase_threshold_lt
      hθ hθupper hphase with
    ⟨a, C1, C2, A, B, phi, hmodel, hphi, hmax, ha, hC2, hC2one,
      hC1, hbalance, hA, hB, hratio⟩
  refine ⟨a, C1, C2, A, B, phi, ?_, hphi, ?_, ha, hC2, hC2one,
    hC1, hbalance, hA, hB, hratio⟩
  · rw [infiniteProducerModelSpec]
    rcases correctedInfiniteTwoGenreContentEquilibriumSpec_of_structure hmodel with
      ⟨firstGenre, secondGenre, conditionalQuality, firstWeight, secondWeight,
        hfirst_nonnegative, hsecond_nonnegative, hfirst_norm, hsecond_norm,
        hquality_probability, hquality_cdf, hquality_support,
        hfirstWeight_nonnegative, hsecondWeight_nonnegative,
        hfirstWeight_half, hsecondWeight_half, hweights, hfirst_max, hsecond_max⟩
    refine ⟨firstGenre, secondGenre, conditionalQuality, firstWeight, secondWeight,
      hfirst_nonnegative, hsecond_nonnegative, hfirst_norm, hsecond_norm,
      hquality_probability, ?_, hquality_support, hfirstWeight_nonnegative,
      hsecondWeight_nonnegative, hfirstWeight_half, hsecondWeight_half, hweights,
      hfirst_max, hsecond_max⟩
    intro q
    simpa [infiniteGenreCandidateCdf, infiniteGenreCdfIndex] using hquality_cdf q
  · simpa [twoUserCosPowerSum] using hmax

theorem theoremInfiniteGenre : theoremInfiniteGenreSpec := by
  exact infiniteGenreConclusion

theorem theoremInfiniteGenreInformal : theoremInfiniteGenreInformalSpec := by
  exact infiniteGenreConclusion

theorem lemmaCdf : lemmaCdfSpec := by
  simpa [lemmaCdfSpec, paper_single_genre_cdf, singleGenreCdf,
    singleGenreCdfRaw] using @paper_lemma_cdf_concrete_ray_norm_law

theorem singleRayNashRatio : singleRayNashRatioSpec := by
  simpa [singleRayNashRatioSpec, symmetricMixedNashModelSpec,
    SourceSymmetricMixedNash, normPowerCostSpec, SingleGenreDirectionCondition,
    ratioObjective] using
    @paper_lemma_optsingledirection_concrete_ray_law_iff

theorem lemmaOptSingleDirection : lemmaOptSingleDirectionSpec := by
  intro D N P _ _ _ β users genre ν hβ hgenre_norm hgenre_nonnegative husers
    husers_nonzero hgenre_score hperturb hcompact hcontinuous
  constructor
  · rintro ⟨μ, hnash, hgenres⟩
    have hsource_nash : SourceSymmetricMixedNash (P := P) users
        (normRpowCost ν β) μ := by
      simpa [symmetricMixedNashModelSpec, normPowerCostSpec] using hnash
    have hsource_genres : SourceNonzeroSupportGenres ν μ ⊆ ({genre} : Set (Content D)) := by
      simpa [nonzeroSupportGenresSpec, SourceNonzeroSupportGenres] using hgenres.le
    have heq : μ = singleGenreContentLaw N P β genre :=
      sourceSymmetricMixedNash_eq_singleGenreContentLaw_of_compactSublevels_of_singleton_nonzeroSupportGenres_of_nonzero_users
        (j := Classical.choice (inferInstance : Nonempty (Fin P))) hsource_nash
        hsource_genres husers husers_nonzero hperturb hβ hcompact hcontinuous
    rw [heq] at hsource_nash
    exact (singleRayNashRatio (P := P) (users := users) (genre := genre) ν
      hβ hgenre_norm hgenre_nonnegative husers hgenre_score).mp (by
        simpa [symmetricMixedNashModelSpec, normPowerCostSpec] using hsource_nash)
  · intro hcondition
    have hnash := (singleRayNashRatio (P := P) (users := users) (genre := genre) ν
      hβ hgenre_norm hgenre_nonnegative husers hgenre_score).mpr hcondition
    refine ⟨singleGenreContentLaw N P β genre, ?_, ?_⟩
    · simpa [symmetricMixedNashModelSpec, normPowerCostSpec] using hnash
    · simpa [nonzeroSupportGenresSpec, SourceNonzeroSupportGenres] using
        (singleGenreContentLaw_nonzeroSupportGenres_eq_singleton ν hβ hgenre_norm)

theorem corollarySingleGenreStructure : corollarySingleGenreStructureSpec := by
  simpa [corollarySingleGenreStructureSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres, normPowerCostSpec,
    nashLogObjective] using
    @paper_corollary_singlegenrestructure_singleton_nonzero_support_nash_log_maximizer

theorem lemmaConditionGen : lemmaConditionGenSpec := by
  intro D N P _ _ _ β users ν hβ husers husers_nonzero hperturb hcompact hcontinuous
  constructor
  · intro hsingle
    have hproduct : SingleGenreProductSupCondition
        {y : Fin N → ℝ | paper_powered_unit_image users
          (fun q => NonnegativeContent q ∧ ν.norm q ≤ 1) β y} := by
      have hiff := paper_theorem_singlegenre_corrected_compact_source_iff
        (P := P) ν hβ husers husers_nonzero hperturb hcompact hcontinuous
      exact hiff.mp (by
        simpa [symmetricMixedNashModelSpec, SourceSymmetricMixedNash,
          nonzeroSupportGenresSpec, SourceNonzeroSupportGenres, normPowerCostSpec] using hsingle)
    obtain ⟨p, hp_nonnegative, hp_ball, hp_score, hp_nash⟩ :=
      (paper_theorem_singlegenre_concrete_source_symmetric_mixed_nash_iff_product_sup_condition_of_compact_sublevels
        (P := P) ν hβ husers husers_nonzero hcompact).mpr hproduct
    have hp_nonzero : NonzeroContent p := nonzeroContent_of_positive_score hp_score
    let genre : Content D := SourceNorm.normalizedContent ν p
    have hgenre_norm : ν.norm genre = 1 :=
      SourceNorm.norm_normalizedContent_eq_one ν hp_nonzero
    have hgenre_nonnegative : NonnegativeContent genre :=
      SourceNorm.normalizedContent_nonnegative ν hp_nonnegative
    have hgenre_score : ∀ i : Fin N,
        0 < paper_inferred_user_value (users i) genre := by
      intro i
      exact SourceNorm.score_normalizedContent_pos_of_score_pos
        ν (users i) hp_nonzero (hp_score i)
    refine ⟨genre, hgenre_nonnegative, hgenre_norm.le, hgenre_score, ?_⟩
    have hgenre_nash : symmetricMixedNashModelSpec (P := P) users
        (normPowerCostSpec ν β) (singleGenreContentLaw N P β genre) := by
      simpa [genre, symmetricMixedNashModelSpec, SourceSymmetricMixedNash,
        normPowerCostSpec] using hp_nash
    apply (lemmaOptSingleDirection (P := P) (users := users) (genre := genre) ν
      hβ hgenre_norm hgenre_nonnegative husers husers_nonzero hgenre_score
      hperturb hcompact hcontinuous).mp
    refine ⟨singleGenreContentLaw N P β genre, hgenre_nash, ?_⟩
    simpa [nonzeroSupportGenresSpec, SourceNonzeroSupportGenres] using
      (singleGenreContentLaw_nonzeroSupportGenres_eq_singleton ν hβ hgenre_norm)
  · rintro ⟨p, hp_nonnegative, hp_ball, hp_score, hcondition⟩
    have hp_nonzero : NonzeroContent p := nonzeroContent_of_positive_score hp_score
    have hp_nash :=
      paper_lemma_conditiongen_positive_ball_witness_source_symmetric_mixed_nash
        (P := P) ν hβ husers hp_nonnegative hp_ball hp_score (by
          simpa [SingleGenreDirectionCondition, ratioObjective] using hcondition)
    refine ⟨singleGenreContentLaw N P β (SourceNorm.normalizedContent ν p),
      SourceNorm.normalizedContent ν p, ?_, ?_⟩
    · simpa [symmetricMixedNashModelSpec, SourceSymmetricMixedNash,
        normPowerCostSpec] using hp_nash
    · simpa [nonzeroSupportGenresSpec, SourceNonzeroSupportGenres] using
        (singleGenreContentLaw_nonzeroSupportGenres_eq_singleton ν hβ
          (SourceNorm.norm_normalizedContent_eq_one ν hp_nonzero))

theorem corollaryBetaOne : corollaryBetaOneSpec := by
  simpa [corollaryBetaOneSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, normPowerCostSpec] using
    @paper_corollary_betaone_concrete_source_symmetric_mixed_nash_of_compact_convex_nonzero_users

theorem corollaryBetaP : corollaryBetaPSpec := by
  simpa [corollaryBetaPSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres, normPowerCostSpec] using
    @paper_corollary_betap_singleton_nonzero_support_equilibrium_of_pos_le_q

theorem corollaryBeta : corollaryBetaSpec := by
  simpa [corollaryBetaSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres, normPowerCostSpec] using
    @paper_corollary_beta_no_singleton_nonzero_support_equilibrium_of_lt_log_bound

theorem propositionSupportRestriction : propositionSupportRestrictionSpec := by
  intro P _ α β θ ε u v p0 μ _ hP husers_nonnegative hε hcontent_ball hu hv huv hα hβ
    hsin hθ_nonneg hθ_le_half_pi hnondegenerate hnash hscore_ac
  simpa [normPowerCostSpec] using
    paper_supportrestriction_no_l2_content_support_ball_of_original_two_user_source_nash
      (P := P) (α := α) (β := β) (θ := θ) (ε := ε) (u := u) (v := v) (p0 := p0) (μ := μ)
      hP husers_nonnegative hε hcontent_ball hu hv huv hα hβ hsin hθ_nonneg hθ_le_half_pi
      hnondegenerate hnash hscore_ac

theorem propositionUtility : propositionUtilitySpec := by
  simpa [propositionUtilitySpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, normPowerCostSpec] using
    @paper_proposition_utility_source_symmetric_mixed_nash_support_payoff_pos

theorem lemmaNonzero : lemmaNonzeroSpec := by
  simpa [lemmaNonzeroSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres] using
    @paper_lemma_singlegenre_genre_scores_positive_of_nonzero_users

theorem propositionZeroUtilitySingleGenre : propositionZeroUtilitySingleGenreSpec := by
  simpa [propositionZeroUtilitySingleGenreSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres, normPowerCostSpec] using
    @paper_proposition_zeroutilitysinglegenre_source_nash_of_compact_sublevels_without_zero_support_premise

theorem lemmaInducedCost : lemmaInducedCostSpec := by
  simpa [lemmaInducedCostSpec, twoUserNonnegativeFiberNormSq,
    paper_two_user_induced_cost_quadratic, twoUserInducedCostQuadratic,
    twoUserInducedCostNumerator] using
    @paper_canonical_two_user_induced_cost_quadratic_eq_nonnegative_fiber_cost

theorem lemmaFoc : lemmaFocSpec := by
  intro α β θ z1 z2 hbase
  exact ⟨paper_hasDerivAt_two_user_induced_cost_z1 hbase,
    paper_hasDerivAt_two_user_induced_cost_z2 hbase⟩

theorem lemmaSecondDerivative : lemmaSecondDerivativeSpec := by
  simpa [lemmaSecondDerivativeSpec] using
    @paper_two_user_induced_cost_cross_partial_param_factor

theorem lemmaRegionsColor : lemmaRegionsColorSpec := by
  simpa [lemmaRegionsColorSpec] using
    @paper_regionscolor_param_bracket_nonpos_of_objective_soc_and_graph_foc_derivatives

theorem propositionUniqueness : propositionUniquenessSpec := by
  intro P _ β θ μ _ hP hβ hθ hθupper hnash hac hdiff1 hdiff2 hphase
  exact (theoremPhaseTransition hP hβ hθ hθupper hnash hac hdiff1 hdiff2).1 hphase

theorem propositionFiniteGenre : propositionFiniteGenreSpec := by
  intro P _ β θ μ _ hP hβ hθ hθupper hnash hac hdiff1 hdiff2 hphase
  intro G hG angle law hinjective hangle
  exact (theoremPhaseTransition hP hβ hθ hθupper hnash hac hdiff1 hdiff2).2 hphase
    hG angle law.weight law.radial law.weight_pos law.weights_sum
    law.radial_probability law.radial_support_nonnegative law.radial_has_positive_support
    law.radial_cdf_c1 law.decomposition hinjective hangle

theorem lemmaSupInf : lemmaSupInfSpec := by
  simpa [lemmaSupInfSpec] using @paper_lemma_supinf_argmax_attains_inf

theorem claimEquivalence : claimEquivalenceSpec := by
  intro D K P users cost μ hK husers_nonzero
  change SourceSymmetricMixedNash (P := P) (twoPopulationUsers K users) cost μ ↔
    SourceSymmetricMixedNash (P := P) (l2NormalizedUsers users)
      (fun q => (2 : ℝ) / ((2 * K : ℕ) : ℝ) * cost q) μ
  exact (paper_claim_equivalence_equal_populations users hK).trans
    (sourceSymmetricMixedNash_l2NormalizedUsers_iff users husers_nonzero).symm

theorem corollaryTwoUsersProfit : corollaryTwoUsersProfitSpec := by
  intro β hβ
  refine ⟨(propositionPTwo hβ).1, ?_⟩
  simpa [normPowerCostSpec] using
    paper_corollary_2usersprofit_pTwo_equilibrium_payoff hβ

theorem lemmaStandardBasisMax : lemmaStandardBasisMaxSpec := by
  intro β z1 z2 w1 w2 hβ _ _ _ _ hradius
  simpa [lemmaStandardBasisMaxSpec, paper_standard_basis_objective,
    standardBasisObjective] using
    (@paper_standard_basis_objective_le_of_radius_two_le β z1 z2 w1 w2 hβ hradius)

end JGS23SupplySideRecommenderSystems
