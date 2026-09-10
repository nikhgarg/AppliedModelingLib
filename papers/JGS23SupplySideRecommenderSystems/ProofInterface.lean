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
  have hone :=
    corollaryOnePopulation (D := 1) (N := 1) (P := P) (β := β)
      (u := u) (genre := genre) ν hβ hu hgenre hgenre_norm hscore hmax hmeas
  refine ⟨hone.1, ?_, ?_, ?_⟩
  · simpa using hone.2.1
  · simpa [paper_single_genre_cdf, singleGenreCdf, singleGenreCdfRaw] using hone.2.2
  · intro μ hnash
    exact sourceSymmetricMixedNash_eq_oneDimensionalContentLaw hnash
      (by assumption)

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
  intro D K P _ _ users β θ hK husers_nonnegative hfirst_nonzero hsecond_nonzero
    hangle hβ_one hθ_pos hθ_le_half_pi
  constructor
  · simpa [symmetricMixedNashModelSpec, SourceSymmetricMixedNash,
      nonzeroSupportGenresSpec, SourceNonzeroSupportGenres, normPowerCostSpec] using
      (@paper_corollary_twousers_corrected_single_genre_equilibrium_iff_phase_threshold
        D K P _ _ users β θ hK husers_nonnegative hfirst_nonzero hsecond_nonzero
        hangle hβ_one hθ_pos hθ_le_half_pi)
  · have hθ_lt_pi : θ < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsin_half : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have htrig : 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 := by
      rw [Real.sin_sq_eq_half_sub]
      have hdouble : 2 * (θ / 2) = θ := by ring
      rw [hdouble]
      ring
    have hden : 0 < 1 - Real.cos θ := by
      rw [htrig]
      positivity
    have hthreshold_ge_one : 1 ≤ twoUserPhaseThreshold θ := by
      rw [twoUserPhaseThreshold]
      apply (le_div_iff₀ hden).2
      have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
      nlinarith
    let S : Set ℝ :=
      {β : ℝ | 1 ≤ β ∧ SingleGenreProductSupCondition
        (poweredScoreGeometrySpec (twoPopulationUsers K users) (SourceNorm.l2 D) β)}
    have hset : S = Set.Icc 1 (twoUserPhaseThreshold θ) := by
      ext β
      simp only [S, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨hβ_one, hproduct⟩
        exact ⟨hβ_one,
          (singleGenreProductSupCondition_inPoweredUnitImage_twoPopulationUsers_l2_raw_iff_le_phaseThreshold
            hK husers_nonnegative
            (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hfirst_nonzero)
            (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hsecond_nonzero)
            hangle hβ_one hθ_pos hθ_le_half_pi).mp hproduct⟩
      · rintro ⟨hβ_one, hβ_le⟩
        exact ⟨hβ_one,
          (singleGenreProductSupCondition_inPoweredUnitImage_twoPopulationUsers_l2_raw_iff_le_phaseThreshold
            hK husers_nonnegative
            (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hfirst_nonzero)
            (AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hsecond_nonzero)
            hangle hβ_one hθ_pos hθ_le_half_pi).mpr hβ_le⟩
    have hbounded : BddAbove S := by
      refine ⟨twoUserPhaseThreshold θ, ?_⟩
      intro β hβ
      exact (Set.mem_Icc.mp (hset ▸ hβ)).2
    change sSup ((fun β : ℝ => (β : WithTop ℝ)) '' S) =
      (twoUserPhaseThreshold θ : WithTop ℝ)
    rw [← WithTop.coe_sSup' hbounded, hset, csSup_Icc hthreshold_ge_one]

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
  intro D K P _ β θ u v μ _ hK hP hu_nonzero hv_nonzero
    hu_nonnegative hv_nonnegative hangle hβ hθ hθupper hnash hac hdiff1 hdiff2
  refine ⟨?_, ?_⟩
  · intro hphase
    exact twoPopulation_nonzeroSupportGenres_eq_singleton_of_normRpowCostNash_belowPhase_raw_users
      hK hP hu_nonzero hv_nonzero hu_nonnegative hv_nonnegative hangle hβ hθ hθupper
      hphase (by simpa [normPowerCostSpec] using hnash) hac hdiff1 hdiff2
  · intro hphase G hG direction law hdirection_injective
    letI : Nonempty (Fin G) := hG
    exact twoPopulation_no_finiteGenreConditionalNormLawAnyDim_of_normRpowCostNash_abovePhase_raw_users
      direction law hdirection_injective hK hu_nonzero hv_nonzero hu_nonnegative hv_nonnegative
      hangle hP hθ hθupper hphase (by simpa [normPowerCostSpec] using hnash)
      hac hdiff1 hdiff2

private theorem infiniteGenreConclusion
    {β θ : ℝ} (hθ : 0 < θ) (hθupper : θ < Real.pi / 2)
    (hphase : twoUserPhaseThreshold θ < β) :
    ∃ a C1 C2 A B phi : ℝ,
      infiniteProducerCandidateSpec
        (fun q : ℝ =>
          if q ≤ 0 then 0
          else if a ≤ q then 1
          else
            let k : ℕ := by
              classical
              exact if h : ∃ n : ℕ, a * C2 ^ n ≤ q then Nat.find h else 0
            if Even k then C2 ^ ((k : ℝ) * β)
            else C1 ^ (-2 : ℝ) * C2 ^ (-2 * ((k / 2 : ℕ) : ℝ) * β) *
              q ^ (2 * β)) β θ phi ∧
      phi ∈ Set.Icc 0 (θ / 2) ∧
      IsMaxOn (fun x : ℝ =>
        (Real.cos x) ^ β + (Real.cos (θ - x)) ^ β) (Set.Icc 0 (θ / 2)) phi ∧
      0 < a ∧ 0 < C2 ∧ C2 < 1 ∧
      C1 = a ^ β ∧ C1 = 1 + C2 ^ β ∧
      A = Real.cos phi ∧ B = Real.cos (θ - phi) ∧ C2 = B / A := by
  rcases paper_exists_corrected_infinite_two_genre_content_equilibrium_of_phase_threshold_lt
      hθ hθupper hphase with
    ⟨a, C1, C2, A, B, phi, hmodel, hfirst_eq, hsecond_eq, hgenres_ne,
      hphi, hmax, ha, hC2, hC2one,
      hC1, hbalance, hA, hB, hratio⟩
  refine ⟨a, C1, C2, A, B, phi, ?_, hphi, ?_, ha, hC2, hC2one,
    hC1, hbalance, hA, hB, hratio⟩
  · rw [infiniteProducerCandidateSpec]
    refine ⟨hmodel.firstGenre, hmodel.secondGenre, hmodel.conditionalQuality,
      hmodel.firstWeight, hmodel.secondWeight, hfirst_eq, hsecond_eq, hgenres_ne,
      hmodel.firstGenre_nonnegative, hmodel.secondGenre_nonnegative,
      hmodel.firstGenre_l2_norm, hmodel.secondGenre_l2_norm,
      hmodel.conditionalQuality_probability, ?_,
      hmodel.conditionalQuality_support_nonnegative,
      hmodel.firstWeight_nonnegative, hmodel.secondWeight_nonnegative,
      hmodel.firstWeight_eq_half, hmodel.secondWeight_eq_half, hmodel.weights_sum,
      hmodel.first_support_maximizes, hmodel.second_support_maximizes⟩
    intro q
    simpa [infiniteGenreCandidateCdf, infiniteGenreCdfIndex] using
      hmodel.conditionalQuality_cdf q
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
  intro D N P _ _ _ users ν husers husers_nonzero hcompact hconvex
  obtain ⟨p, hp_nonnegative, hp_ball, hp_score, hp_nash⟩ :=
    (@paper_corollary_betaone_concrete_source_symmetric_mixed_nash_of_compact_convex_nonzero_users
      D N P _ _ _ users ν husers husers_nonzero hcompact hconvex)
  refine ⟨p, hp_nonnegative, hp_ball, hp_score, ?_, ?_⟩
  · simpa [symmetricMixedNashModelSpec, paper_source_symmetric_mixed_nash,
      SourceSymmetricMixedNash, normPowerCostSpec] using hp_nash
  · unfold betaStarDefinitionSpec
    refine le_csSup ?_ ?_
    · exact ⟨⊤, fun _ _ => le_top⟩
    · refine ⟨1, ?_, rfl⟩
      constructor
      · norm_num
      · simpa [poweredScoreGeometrySpec] using
          (singleGenreProductSupCondition_poweredUnitImage_one_of_convex_unitFeasible
            ((convex_nonnegativeContentSet (D := D)).inter (hconvex 1)))

theorem corollaryBetaP : corollaryBetaPSpec := by
  constructor
  · intro D N P _ _ _ q β users hq hβ hβ_le_q husers husers_nonzero
    constructor
    · simpa [symmetricMixedNashModelSpec, paper_source_symmetric_mixed_nash,
        SourceSymmetricMixedNash, nonzeroSupportGenresSpec, paper_nonzero_support_genres,
        SourceNonzeroSupportGenres, normPowerCostSpec] using
        (@paper_corollary_betap_singleton_nonzero_support_equilibrium_of_pos_le_q
          D N P _ _ _ q β users hq hβ hβ_le_q husers husers_nonzero)
    · unfold betaStarDefinitionSpec
      refine le_csSup ?_ ?_
      · exact ⟨⊤, fun _ _ => le_top⟩
      · refine ⟨q, ?_, rfl⟩
        constructor
        · exact hq
        · simpa [poweredScoreGeometrySpec, SourceNorm.lp] using
            (singleGenreProductSupCondition_inPoweredUnitImage_lp_at_exponent hq husers)
  · intro D _ q hq
    let qpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    let S : Set ℝ :=
      {β : ℝ | 1 ≤ β ∧ SingleGenreProductSupCondition
        (poweredScoreGeometrySpec (standardBasisUsers D) (SourceNorm.lp D qpos) β)}
    have husers_nonnegative : ∀ i : Fin D, NonnegativeContent (standardBasisUsers D i) := by
      intro i
      simpa [standardBasisUsers] using standardBasisContent_nonnegative D i
    have hproduct_q : SingleGenreProductSupCondition
        (poweredScoreGeometrySpec (standardBasisUsers D) (SourceNorm.lp D qpos) q) := by
      simpa [poweredScoreGeometrySpec, SourceNorm.lp] using
        (singleGenreProductSupCondition_inPoweredUnitImage_lp_at_exponent hq
          husers_nonnegative)
    have hset : S = Set.Icc 1 q := by
      ext β
      simp only [S, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨hβ_one, hproduct⟩
        refine ⟨hβ_one, ?_⟩
        by_contra hnot
        have hq_lt_β : q < β := lt_of_not_ge hnot
        exact
          (not_singleGenreProductSupCondition_inPoweredUnitImage_standardBasis_lp_of_lt
            hq hq_lt_β) (by simpa [poweredScoreGeometrySpec, SourceNorm.lp] using hproduct)
      · rintro ⟨hβ_one, hβ_le_q⟩
        have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_one
        exact ⟨hβ_one,
          singleGenreProductSupCondition_inPoweredUnitImage_of_le_exponent_of_compactSublevels
            hβ_pos hβ_le_q husers_nonnegative
            (SourceNorm.lp_compactSublevels qpos) hproduct_q⟩
    have hbounded : BddAbove S := by
      refine ⟨q, ?_⟩
      intro β hβ
      exact (Set.mem_Icc.mp (hset ▸ hβ)).2
    change sSup ((fun β : ℝ => (β : WithTop ℝ)) '' S) = (q : WithTop ℝ)
    rw [← WithTop.coe_sSup' hbounded, hset, csSup_Icc hq]

theorem corollaryBeta : corollaryBetaSpec := by
  constructor
  · simpa [corollaryBetaSpec, symmetricMixedNashModelSpec,
      paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
      paper_nonzero_support_genres, SourceNonzeroSupportGenres, normPowerCostSpec] using
      @paper_corollary_beta_no_singleton_nonzero_support_equilibrium_of_lt_log_bound
  · constructor
    · intro D N _ users ν husers_nonnegative hcompact_sublevels haggregate_bound hdual_witness
      unfold betaStarDefinitionSpec
      let S : Set ℝ :=
        {β : ℝ | 1 ≤ β ∧ SingleGenreProductSupCondition
          (poweredScoreGeometrySpec users ν β)}
      change sSup ((fun β : ℝ => (β : WithTop ℝ)) '' S) ≤ (1 : WithTop ℝ)
      have hupper : ∀ β ∈ S, β ≤ 1 := by
        intro β hβ
        rcases hβ with ⟨hβ_one, hproduct⟩
        by_contra hnot
        have hβ_one_lt : 1 < β := lt_of_not_ge hnot
        exact
          (not_singleGenreProductSupCondition_inPoweredUnitImage_of_Z_eq_one
            ν husers_nonnegative hcompact_sublevels haggregate_bound hdual_witness hβ_one_lt)
          (by simpa [poweredScoreGeometrySpec] using hproduct)
      rcases S.eq_empty_or_nonempty with hS | hS
      · rw [hS, Set.image_empty]
        rw [WithTop.sSup_eq (by simp) (by simp)]
        norm_num
      · have hbounded : BddAbove S := ⟨1, fun β hβ => hupper β hβ⟩
        rw [← WithTop.coe_sSup' hbounded]
        exact WithTop.coe_le_coe.mpr (csSup_le hS fun β hβ => hupper β hβ)
    · intro D N _ Z users ν husers_nonnegative hcompact_sublevels haggregate_bound hdual_witness
      intro hZ_one_lt hZ_lt_card
      unfold betaStarDefinitionSpec
      let threshold : ℝ :=
        Real.log (N : ℝ) / (Real.log (N : ℝ) - Real.log Z)
      let S : Set ℝ :=
        {β : ℝ | 1 ≤ β ∧ SingleGenreProductSupCondition
          (poweredScoreGeometrySpec users ν β)}
      change sSup ((fun β : ℝ => (β : WithTop ℝ)) '' S) ≤ (threshold : WithTop ℝ)
      have hthreshold_pos : 0 < threshold := by
        apply div_pos
        · exact Real.log_pos (lt_trans hZ_one_lt hZ_lt_card)
        · apply sub_pos.mpr
          exact Real.log_lt_log (lt_trans zero_lt_one hZ_one_lt) hZ_lt_card
      have hupper : ∀ β ∈ S, β ≤ threshold := by
        intro β hβ
        rcases hβ with ⟨hβ_one, hproduct⟩
        by_contra hnot
        have hbound : threshold < β := lt_of_not_ge hnot
        exact
          (not_singleGenreProductSupCondition_inPoweredUnitImage_of_lt_general_threshold
            ν husers_nonnegative hcompact_sublevels haggregate_bound hdual_witness
            hZ_one_lt hZ_lt_card hbound)
          (by simpa [poweredScoreGeometrySpec] using hproduct)
      rcases S.eq_empty_or_nonempty with hS | hS
      · rw [hS, Set.image_empty]
        rw [WithTop.sSup_eq (by simp) (by simp)]
        simpa only [Set.preimage_empty, Real.sSup_empty] using
          WithTop.coe_le_coe.mpr hthreshold_pos.le
      · have hbounded : BddAbove S := ⟨threshold, fun β hβ => hupper β hβ⟩
        rw [← WithTop.coe_sSup' hbounded]
        exact WithTop.coe_le_coe.mpr (csSup_le hS fun β hβ => hupper β hβ)

theorem propositionSupportRestriction : propositionSupportRestrictionSpec := by
  intro P _ α β θ ε u v p0 μ _ hP husers_nonnegative hε hcontent_ball hu hv huv hα hβ
    hsin hθ_nonneg hθ_le_half_pi hnondegenerate hnash hscore_ac
  simpa [normPowerCostSpec] using
    paper_supportrestriction_no_l2_content_support_ball_of_original_two_user_source_nash
      (P := P) (α := α) (β := β) (θ := θ) (ε := ε) (u := u) (v := v) (p0 := p0) (μ := μ)
      hP husers_nonnegative hε hcontent_ball hu hv huv hα hβ hsin hθ_nonneg hθ_le_half_pi
      hnondegenerate hnash hscore_ac

/--
The source max--min definition of `Q` supplies the unit-direction bound used
by the profitable-deviation argument.  Though source actions are nonnegative,
the coordinatewise positive part of any ambient direction has no larger L2
norm and weakly raises every nonnegative user's score, so the bound extends to
the helper's all-direction formulation.
-/
theorem equilibriumProfitModel_qUpperBound_and_nonneg
    {D N P : ℕ} [Nonempty (Fin N)] {users : Fin N → Content D}
    {μ : MixedContentStrategy D} {β profit Q : ℝ}
    (hmodel : equilibriumProfitModelSpec (P := P) users (SourceNorm.l2 D)
      (normPowerCostSpec (SourceNorm.l2 D) β) μ profit Q)
    (husers_nonnegative : ∀ i : Fin N, NonnegativeContent (users i)) :
    SourceUnitDirectionQUpperBound
      (l2NormalizedUsers users) (SourceNorm.l2 D) Q ∧ 0 ≤ Q := by
  classical
  rcases hmodel with ⟨_, husers_nonzero, _, hQ⟩
  let S : Set ℝ := {q : ℝ | ∃ p : Content D,
    NonnegativeContent p ∧ (SourceNorm.l2 D).norm p ≤ 1 ∧
      ∀ i : Fin N, q ≤ score p ((SourceNorm.l2 D).normalizedContent (users i))}
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    intro q hq
    rcases hq with ⟨p, _hp_nonnegative, hp_norm, hq⟩
    let i0 : Fin N := Classical.choice inferInstance
    have hp_norm' : AppliedModelingLib.FiniteDimensionalNorms.l2 p ≤ 1 := by
      exact hp_norm
    have hi0_norm : AppliedModelingLib.FiniteDimensionalNorms.l2
        ((SourceNorm.l2 D).normalizedContent (users i0)) = 1 := by
      exact SourceNorm.norm_normalizedContent_eq_one (SourceNorm.l2 D)
        (husers_nonzero i0)
    have hscore : score p ((SourceNorm.l2 D).normalizedContent (users i0)) ≤
        AppliedModelingLib.FiniteDimensionalNorms.l2 p *
          AppliedModelingLib.FiniteDimensionalNorms.l2
            ((SourceNorm.l2 D).normalizedContent (users i0)) := by
      change AppliedModelingLib.FiniteDimensionalNorms.dot p
          ((SourceNorm.l2 D).normalizedContent (users i0)) ≤ _
      exact le_trans (le_abs_self _)
        (AppliedModelingLib.FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 _ _)
    calc
      q ≤ score p ((SourceNorm.l2 D).normalizedContent (users i0)) := hq i0
      _ ≤ AppliedModelingLib.FiniteDimensionalNorms.l2 p *
          AppliedModelingLib.FiniteDimensionalNorms.l2
            ((SourceNorm.l2 D).normalizedContent (users i0)) := hscore
      _ = AppliedModelingLib.FiniteDimensionalNorms.l2 p := by rw [hi0_norm, mul_one]
      _ ≤ 1 := hp_norm'
  have hQ' : Q = sSup S := by
    exact hQ
  have hzero_mem : (0 : ℝ) ∈ S := by
    refine ⟨0, zeroContent_nonnegative, ?_, ?_⟩
    · rw [SourceNorm.norm_zero]
      norm_num
    · intro i
      simp
  constructor
  · intro p hp_norm
    let ppos : Content D := nonnegativePart p
    have hppos_nonnegative : NonnegativeContent ppos := by
      exact nonnegativePart_nonnegative p
    have hp_norm' : AppliedModelingLib.FiniteDimensionalNorms.l2 p = 1 := by
      exact hp_norm
    have hppos_norm : (SourceNorm.l2 D).norm ppos ≤ 1 := by
      calc
        (SourceNorm.l2 D).norm ppos =
            AppliedModelingLib.FiniteDimensionalNorms.l2 ppos := rfl
        _ ≤ AppliedModelingLib.FiniteDimensionalNorms.l2 p :=
          l2_nonnegativePart_le p
        _ = 1 := hp_norm'
    obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin N))
      (fun i : Fin N => score (l2NormalizedUsers users i) ppos)
      Finset.univ_nonempty
    let q : ℝ := score (l2NormalizedUsers users i) ppos
    have hq_mem : q ∈ S := by
      refine ⟨ppos, hppos_nonnegative, hppos_norm, ?_⟩
      intro k
      dsimp [q]
      calc
        score (l2NormalizedUsers users i) ppos ≤
            score (l2NormalizedUsers users k) ppos :=
          hmin k (Finset.mem_univ k)
        _ = score ppos (l2NormalizedUsers users k) := score_comm _ _
        _ = score ppos ((SourceNorm.l2 D).normalizedContent (users k)) := rfl
    have hq_le : q ≤ Q := by
      rw [hQ']
      exact le_csSup hbounded hq_mem
    have hi_nonnegative : NonnegativeContent (l2NormalizedUsers users i) := by
      dsimp [l2NormalizedUsers]
      exact SourceNorm.normalizedContent_nonnegative (SourceNorm.l2 D)
        (husers_nonnegative i)
    refine ⟨i, ?_⟩
    calc
      score (l2NormalizedUsers users i) p ≤
          score (l2NormalizedUsers users i) ppos :=
        score_le_score_nonnegativePart hi_nonnegative
      _ = q := rfl
      _ ≤ Q := hq_le
  · rw [hQ']
    exact le_csSup hbounded hzero_mem

theorem propositionUtility : propositionUtilitySpec := by
  intro D N P _ _ users μ β profit Q hmodel husers_nonnegative hβ hQ
  let j : Fin P := Classical.choice inferInstance
  have hbridge := equilibriumProfitModel_qUpperBound_and_nonneg hmodel husers_nonnegative
  rcases hmodel with ⟨hnash, husers_nonzero, hprofit, _⟩
  have hnash' : SourceSymmetricMixedNash (P := P) users
      (normRpowCost (SourceNorm.l2 D) β) μ := by
    simpa [symmetricMixedNashModelSpec, paper_source_symmetric_mixed_nash,
      SourceSymmetricMixedNash, normPowerCostSpec] using hnash
  have hintegral : 0 < ∫ p, SourceMixedPurePayoff
      (ExpectedUsersWonAgainstSymmetricMixed users j)
      (normPowerCostSpec (SourceNorm.l2 D) β) p μ ∂μ := by
    simpa [normPowerCostSpec] using
      integral_sourceMixedPurePayoff_pos_of_positive_profit_condition_l2_normalized_users
        (j := j) hnash' husers_nonnegative husers_nonzero hbridge.1 hβ hbridge.2 hQ
  exact lt_of_lt_of_eq hintegral (hprofit j)

theorem lemmaNonzero : lemmaNonzeroSpec := by
  simpa [lemmaNonzeroSpec, symmetricMixedNashModelSpec,
    paper_source_symmetric_mixed_nash, SourceSymmetricMixedNash, nonzeroSupportGenresSpec,
    paper_nonzero_support_genres, SourceNonzeroSupportGenres] using
    @paper_lemma_singlegenre_genre_scores_positive_of_nonzero_users

theorem propositionZeroUtilitySingleGenre : propositionZeroUtilitySingleGenreSpec := by
  intro D N P _ _ users ν μ j genre β profit hnash hprofit hno_atoms hgenres hgenre_score
    hmeas_norm husers hβ hcompact_sublevels hcontinuous
  have hnash' : SourceSymmetricMixedNash (P := P) users (normRpowCost ν β) μ := by
    simpa [symmetricMixedNashModelSpec, paper_source_symmetric_mixed_nash,
      SourceSymmetricMixedNash, normPowerCostSpec] using hnash
  have hintegral :
      (∫ q, SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normRpowCost ν β) q μ ∂μ) = 0 := by
    exact integral_sourceMixedPurePayoff_eq_zero_of_singleton_nonzeroSupportGenres
      hnash' hno_atoms hgenres hgenre_score hmeas_norm husers hβ hcompact_sublevels hcontinuous
  calc
    profit = ∫ q, SourceMixedPurePayoff
        (ExpectedUsersWonAgainstSymmetricMixed users j)
        (normPowerCostSpec ν β) q μ ∂μ := hprofit.symm
    _ = 0 := by simpa [normPowerCostSpec] using hintegral

theorem lemmaInducedCost : lemmaInducedCostSpec := by
  simpa [lemmaInducedCostSpec, twoUserNonnegativeFiberNormSq,
    paper_two_user_induced_cost_quadratic, twoUserInducedCostQuadratic,
    twoUserInducedCostNumerator] using
    @paper_canonical_two_user_induced_cost_quadratic_eq_nonnegative_fiber_cost

theorem lemmaFoc : lemmaFocSpec := by
  intro α β θ z1 z2 hbase
  refine ⟨paper_hasDerivAt_two_user_induced_cost_z1 hbase,
    paper_hasDerivAt_two_user_induced_cost_z2 hbase, ?_⟩
  intro P _ α β θ μ _ hsin hnash hscore_ac hcdf hinterior z hz hz_ne
  constructor
  · exact first_iidMaximumCdf_deriv_eq_inducedCostPartial_of_sourceSymmetricMixedNash_of_scoreCdfContDiffAt_of_strictInteriorAwayOrigin
      hsin hnash hscore_ac
      (fun x hx => (hcdf 0 x (by simpa using hx)).of_le (by norm_num))
      hinterior hz hz_ne
  · exact second_iidMaximumCdf_deriv_eq_inducedCostPartial_of_sourceSymmetricMixedNash_of_scoreCdfContDiffAt_of_strictInteriorAwayOrigin
      hsin hnash hscore_ac
      (fun x hx => (hcdf 1 x (by simpa using hx)).of_le (by norm_num))
      hinterior hz hz_ne

theorem lemmaSecondDerivative : lemmaSecondDerivativeSpec := by
  simpa [lemmaSecondDerivativeSpec] using
    @paper_two_user_induced_cost_cross_partial_param_factor

theorem lemmaRegionsColor : lemmaRegionsColorSpec := by
  intro u v H1 H2 g S α β θ φ r a b x slope
    hu_nonnegative hv_nonnegative hu hv huv hα hβ hsin hH1_mono hH2_mono
    hSnonnegative hxI hxparam hgparam hderiv hgraph hmax
  simpa [lemmaRegionsColorSpec] using
    (twoUser_regionscolor_param_bracket_nonpos_of_C1_graph
      hu_nonnegative hv_nonnegative hu hv huv hα hβ hsin hH1_mono hH2_mono
      hSnonnegative hxI hxparam hgparam hderiv hgraph hmax)

theorem propositionUniqueness : propositionUniquenessSpec := by
  intro P _ β θ μ _ hP hβ hθ hθupper hnash hac hdiff1 hdiff2 hphase
  exact (paper_canonical_two_user_corrected_phase_transition
    (P := P) hP hβ hθ hθupper (by simpa [normPowerCostSpec] using hnash)
    hac hdiff1 hdiff2).1 hphase

theorem propositionFiniteGenre : propositionFiniteGenreSpec := by
  intro P _ β θ μ _ hP hβ hθ hθupper hnash hac hdiff1 hdiff2 hphase
  intro G hG angle law hinjective hangle
  exact (paper_canonical_two_user_corrected_phase_transition
    (P := P) hP hβ hθ hθupper (by simpa [normPowerCostSpec] using hnash)
    hac hdiff1 hdiff2).2 hphase
    hG angle (finiteGenreConditionalNormLaw_of_spec law) hinjective hangle

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
