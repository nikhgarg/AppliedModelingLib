import FalahatgarEtAl2017MaxingRanking.PaperInterface

/-! # Exact-type proof endpoints for the paper-facing Specs. -/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib MeasureTheory ProbabilityTheory

/-- Exact-type proof endpoint for the finite SST existence claim in the main-paper prose. -/
theorem sstMaximumAndRankingExistence_proof :
    sstMaximumAndRankingExistenceSpec := by
  unfold sstMaximumAndRankingExistenceSpec
  intro Arm _ _ _ preferenceGap hantisymmetric hsst
  let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
  exact ⟨exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap hcomplete hsst,
    exists_preferenceRanking_of_preferenceComplete_sst preferenceGap hcomplete hsst⟩

/-- Exact-type proof endpoint for Main Lemma 1. -/
theorem lemma1_compare_proof : lemma1_compareSpec := by
  unfold lemma1_compareSpec
  constructor
  · intro Ω observation lower upper delta outcome hseparation hdelta hdeltaLeOne
    exact ⟨adaptiveCompareStoppingTime_le_count observation
      (fixedSampleBudget lower upper delta) lower upper delta outcome,
      fixedSampleBudget_realTarget_le lower upper delta,
      fixedSampleBudget_lt_realTarget_add_one lower upper delta hdelta hdeltaLeOne⟩
  · exact ⟨@finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget,
      @finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget⟩

/-- Exact-type proof endpoint for Main Theorem 2. -/
theorem theorem2_seqEliminate_proof : theorem2_seqEliminateSpec := by
  unfold theorem2_seqEliminateSpec
  constructor
  · intro Arm _ _ _ preferenceGap hprobability epsilon delta hantisymmetric hself hsst
      hepsilon hdelta hdeltaLeOne
    let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
    exact canonicalFreshUniformSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
      preferenceGap hprobability epsilon delta hantisymmetric hself hcomplete hsst
      hepsilon hdelta hdeltaLeOne
  · exact @theorem2_seqEliminate_sourceEnvelope_real_le_sourceRateForm

/-- Exact-type proof endpoint for Main Lemma 3. -/
theorem lemma3_pickAnchor_proof : lemma3_pickAnchorSpec := by
  unfold lemma3_pickAnchorSpec
  constructor
  · intro Arm _ _ _ cutoff delta epsilon preferenceGap hprobability hcutoff hcutoffLeCard
      hdelta hdeltaLeOne hepsilon hantisymmetric hself hsst
    let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
    let hrankingExists :=
      exists_preferenceRanking_of_preferenceComplete_sst preferenceGap hcomplete hsst
    let ranking := Classical.choose hrankingExists
    exact canonicalFreshPickAnchorUniform_goodAnchor_highProbability_of_preferenceRanking
      cutoff delta epsilon preferenceGap hprobability ranking
      (Classical.choose_spec hrankingExists) hcutoff hcutoffLeCard hdelta hdeltaLeOne
      hepsilon hantisymmetric hself hcomplete hsst
  · exact @lemma3_pickAnchor_sourceComparisonCap_real_le_sourceRateForm

/-- Exact-type proof endpoint for Main Remark 4. -/
theorem remark4_pickAnchorLinearCutoff_proof : remark4_pickAnchorLinearCutoffSpec := by
  unfold remark4_pickAnchorLinearCutoffSpec
  intro Arm _ _ cutoff c epsilon delta hcutoff hepsilon hepsilonLeOne hc hdelta hdeltaLeOne
    hlinearCutoff
  have hbase := lemma3_pickAnchor_sourceComparisonCap_real_le_sourceRateForm
    (Arm := Arm) cutoff epsilon delta hcutoff hepsilon hepsilonLeOne hdelta hdeltaLeOne
  have hlogNonnegative : 0 ≤ Real.log (2 / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).2
    nlinarith
  let sourceRatio : ℝ :=
    (Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1
  let constantRatio : ℝ := 1 / c * Real.log (2 / delta) + 1
  have hratio : sourceRatio ≤ constantRatio := by
    dsimp [sourceRatio, constantRatio]
    simpa [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_right hlinearCutoff hlogNonnegative) 1
  have hsourceRatioOne : 1 ≤ sourceRatio := by
    dsimp [sourceRatio]
    have hcardNonnegative : 0 ≤ (Fintype.card Arm : ℝ) := Nat.cast_nonneg _
    have hcutoffReal : 0 < (cutoff : ℝ) := by exact_mod_cast hcutoff
    have : 0 ≤ (Fintype.card Arm : ℝ) / (cutoff : ℝ) :=
      div_nonneg hcardNonnegative hcutoffReal.le
    nlinarith [mul_nonneg this hlogNonnegative]
  have hsourceRatioPos : 0 < sourceRatio := lt_of_lt_of_le zero_lt_one hsourceRatioOne
  have hconstantRatioPos : 0 < constantRatio := lt_of_lt_of_le hsourceRatioPos hratio
  have hscaled : sourceRatio / delta ≤ constantRatio / delta :=
    div_le_div_of_nonneg_right hratio hdelta.le
  have hlogScaled : Real.log (sourceRatio / delta) ≤ Real.log (constantRatio / delta) :=
    Real.log_le_log (div_pos hsourceRatioPos hdelta) hscaled
  have hsourceLogFactorNonnegative : 0 ≤ 1 + Real.log (sourceRatio / delta) := by
    have hone : 1 ≤ sourceRatio / delta := by
      apply (le_div_iff₀ hdelta).2
      simpa using hdeltaLeOne.trans hsourceRatioOne
    nlinarith [Real.log_nonneg hone]
  have hconstantLogFactorNonnegative : 0 ≤ 1 + Real.log (constantRatio / delta) := by
    linarith
  calc
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
        5 * sourceRatio * (1 + Real.log (sourceRatio / delta)) / epsilon ^ 2 := by
          simpa [sourceRatio] using hbase
    _ ≤ 5 * constantRatio * (1 + Real.log (constantRatio / delta)) / epsilon ^ 2 := by
      gcongr
    _ = _ := by rfl

/-- Exact-type proof endpoint for Main Lemma 5. -/
theorem lemma5_prune_proof : lemma5_pruneSpec := by
  unfold lemma5_pruneSpec
  intro Arm _ _ preferenceGap hprobability anchor lower upper delta cutoff hantisymmetric hsst
    hupperNonnegative hanchor hseparation hdelta hdeltaHalf hcutoff hdeltaLower
  dsimp only
  constructor
  · exact canonicalFreshStoppedPruneTrace_sourceLemma5_size_cost_probability preferenceGap
      hprobability anchor lower upper delta cutoff hanchor hseparation hdelta hdeltaHalf hcutoff
      hdeltaLower
  · intro hanchorNotMaximum
    exact canonicalFreshStoppedPruneActive_sourceLemma5_maximum_probability preferenceGap
      hprobability anchor lower upper delta cutoff hantisymmetric hsst hupperNonnegative
      hanchorNotMaximum hseparation hdelta (hdeltaHalf.trans (by norm_num))

/-- Exact-type proof endpoint for Main Theorem 6. -/
theorem theorem6_optMaximize_proof : theorem6_optMaximizeSpec := by
  unfold theorem6_optMaximizeSpec
  constructor
  · intro Arm _ _ epsilon delta preferenceGap hprobability hdelta hdeltaLeOne
      hantisymmetric hself hsst hepsilon
    classical
    dsimp only
    let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
    let hmaximumExists :=
      exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap hcomplete hsst
    let hrankingExists :=
      exists_preferenceRanking_of_preferenceComplete_sst preferenceGap hcomplete hsst
    exact theorem6_optMaximize_sourceParameters_joint_envelope
      epsilon delta preferenceGap (Classical.choose hmaximumExists) hprobability
      (Classical.choose hrankingExists) (Classical.choose_spec hrankingExists)
      hdelta hdeltaLeOne hantisymmetric hself hcomplete hsst
      (Classical.choose_spec hmaximumExists) hepsilon
  · exact @theorem6_optMaximize_sourceParameters_branchEnvelope_isBigO_sourceRateShape

/-- Exact-type proof endpoint for Main Theorem 7. -/
theorem theorem7_rankingLowerBound_proof : theorem7_rankingLowerBoundSpec := by
  unfold theorem7_rankingLowerBoundSpec
  intro Seed _ _
  letI : DecidableEq Seed := Classical.decEq Seed
  dsimp only
  intro n comparisonBudget mu seedLaw hmu hmuHalf hcard hmuSource hbudget procedure
  exact theorem7_exists_source_hard_instance_of_seeded_procedure (Seed := Seed)
    seedLaw hmu hmuHalf hcard hmuSource hbudget procedure

/-- Exact-type proof endpoint for Main Theorem 8. -/
theorem theorem8_bordaMaxing_proof : theorem8_bordaMaxingSpec := by
  unfold theorem8_bordaMaxingSpec
  exact theorem8_bordaMaxing_sourceRate_exists

/-- Exact-type proof endpoint for Main Theorem 9 / Supplement Theorem 22. -/
theorem theorem9_bordaRanking_proof : theorem9_bordaRankingSpec := by
  unfold theorem9_bordaRankingSpec
  constructor
  · intro Arm _ _ winProbability hprobability epsilon delta hepsilon hdelta hdeltaLeOne
    classical
    refine ⟨@empiricalBordaRanking Arm inferInstance, empiricalBordaRanking_isRule, ?_⟩
    exact theorem9_bordaRanking_uniformSampler_failure_probability
      winProbability hprobability epsilon delta hepsilon hdelta hdeltaLeOne
  · exact @theorem9_bordaRanking_sourceTotalSampleCount_real_le_sourceRateForm

/-- Exact-type proof endpoint for Supplement Lemma 10. -/
theorem lemma10_compareCap_proof : lemma10_compareCapSpec := by
  unfold lemma10_compareCapSpec
  intro Ω observation lower upper delta outcome hlower hseparation hdelta hdeltaLeOne
  exact ⟨adaptiveCompareStoppingTime_le_count observation
    (fixedSampleBudget lower upper delta) lower upper delta outcome,
    fixedSampleBudget_realTarget_le lower upper delta,
    fixedSampleBudget_lt_realTarget_add_one lower upper delta hdelta hdeltaLeOne⟩

/-- Exact-type proof endpoint for Supplement Lemma 11. -/
theorem lemma11_compareLower_proof : lemma11_compareLowerSpec := by
  unfold lemma11_compareLowerSpec
  intro Ω _ law _ observation lower upper trueGap delta hindependent hmeasurable hbounded
    hmean hgap hlower hseparation hdelta hdeltaLeOne
  exact finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget law observation
    lower upper trueGap delta hindependent hmeasurable hbounded hmean hgap hseparation hdelta
    hdeltaLeOne

/-- Exact-type proof endpoint for Supplement Lemma 12. -/
theorem lemma12_compareUpper_proof : lemma12_compareUpperSpec := by
  unfold lemma12_compareUpperSpec
  intro Ω _ law _ observation lower upper trueGap delta hindependent hmeasurable hbounded
    hmean hgap hlower hseparation hdelta hdeltaLeOne
  exact finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget law observation
    lower upper trueGap delta hindependent hmeasurable hbounded hmean hgap hseparation hdelta
    hdeltaLeOne

/-- Exact-type proof endpoint for Supplement Lemma 13. -/
theorem lemma13_pruneRetention_proof : lemma13_pruneRetentionSpec := by
  unfold lemma13_pruneRetentionSpec
  intro Ω Arm _
  letI : DecidableEq Arm := Classical.decEq Arm
  dsimp only
  exact finiteBatchAdaptivePrune_retention_probability (Ω := Ω) (Arm := Arm)

/-- Exact-type proof endpoint for Supplement Lemma 14. -/
theorem lemma14_pruneOneRound_proof : lemma14_pruneOneRoundSpec := by
  unfold lemma14_pruneOneRoundSpec
  intro Arm _ _ preferenceGap hprobability active anchor lower upper delta cutoff hanchor
    hseparation hdelta hdeltaLeOne hcutoff hdeltaLower hdeltaUpper
  constructor
  · exact canonicalPruneRound_card_failure_probability_le_delta_half_of_sourceLemma14
      preferenceGap hprobability active anchor lower upper delta cutoff hanchor hseparation hdelta
      hdeltaLeOne hcutoff hdeltaLower hdeltaUpper
  · exact finiteCallCount_ceilingBudget_real_le_sourceBudget active.card lower upper
      (delta / 4) (by positivity) (by linarith)

/-- Exact-type proof endpoint for Supplement Lemma 15. -/
theorem lemma15_pruneMultiRound_proof : lemma15_pruneMultiRoundSpec := by
  unfold lemma15_pruneMultiRoundSpec
  intro Arm _
  letI : DecidableEq Arm := Classical.decEq Arm
  dsimp only
  intro preferenceGap hprobability anchor lower upper delta cutoff initial hanchor hseparation hdelta
    hdeltaHalf hcutoff hdeltaLower
  have hcardPosNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr ⟨anchor⟩
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPosNat
  have hcutoffPosReal : 0 < (cutoff : ℝ) :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have hcutoffGeOne : (1 : ℝ) ≤ cutoff := by
    have hcutoffPosNat : 0 < cutoff := by exact_mod_cast hcutoffPosReal
    exact_mod_cast hcutoffPosNat
  have hdeltaLowerCard : 1 / (Fintype.card Arm : ℝ) ≤ delta := by
    calc
      1 / (Fintype.card Arm : ℝ) ≤ (cutoff : ℝ) / (Fintype.card Arm : ℝ) := by
        exact div_le_div_of_nonneg_right hcutoffGeOne hcardPos.le
      _ ≤ delta := hdeltaLower
  have hsource :=
    canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma5_sharpEnvelope
      preferenceGap hprobability anchor lower upper delta
      (sourcePruneMaxBatch (Arm := Arm) lower upper delta) cutoff
      (fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta) initial
      hanchor hseparation hdelta hdeltaHalf hcutoff.le hdeltaLowerCard
  exact hsource.trans <| pmfProb_le_of_imp _ _ _ (by
    intro stateFailure hsuccess
    exact ⟨hsuccess.2.1, hsuccess.2.2⟩)

/-- Exact-type proof endpoint for Supplement Lemma 16. -/
theorem lemma16_finalCheckAnchor_proof : lemma16_finalCheckAnchorSpec := by
  unfold lemma16_finalCheckAnchorSpec
  intro Arm _ _ anchor fallback candidates preferenceGap hprobability epsilon delta hantisymmetric
    hanchor hepsilon hdelta hdeltaLeOne
  classical
  dsimp only
  have hcard : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have heta : 0 < (delta / 4) / (Fintype.card Arm : ℝ) := by positivity
  have hetaLeOne : (delta / 4) / (Fintype.card Arm : ℝ) ≤ 1 := by
    have hcardGeOne : 1 ≤ (Fintype.card Arm : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hcard
    calc
      (delta / 4) / (Fintype.card Arm : ℝ) ≤ delta / 4 :=
        div_le_self (by positivity) hcardGeOne
      _ ≤ 1 := by linarith
  have hbelow : ∀ candidate ∈ candidates,
      preferenceGap candidate anchor ≤ 2 * epsilon / 3 := by
    intro candidate hcandidate
    have hbound := hanchor candidate
    rw [hantisymmetric candidate anchor] at hbound
    linarith
  have hphase := canonicalFreshFinalCheck_anchor_probability_of_all_lower
    anchor fallback candidates preferenceGap hprobability (2 * epsilon / 3) epsilon
    ((delta / 4) / (Fintype.card Arm : ℝ)) hbelow (by linarith) heta hetaLeOne
  have hcardLe : (candidates.card : ℝ) ≤ (Fintype.card Arm : ℝ) := by
    exact_mod_cast Finset.card_le_univ candidates
  have hspent : (candidates.card : ℝ) *
      ((delta / 4) / (Fintype.card Arm : ℝ)) ≤ delta / 4 := by
    calc
      (candidates.card : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) ≤
          (Fintype.card Arm : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) := by
            gcongr
      _ = delta / 4 := by field_simp
  linarith

/-- Exact-type proof endpoint for Supplement Lemma 17. -/
theorem lemma17_anchorPrune_proof : lemma17_anchorPruneSpec := by
  unfold lemma17_anchorPruneSpec
  intro Arm _ _ _ epsilon delta preferenceGap hprobability hantisymmetric hself hsst
    hepsilon hdelta hdeltaLeOne hdeltaLower
  dsimp only
  let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
  let hmaximumExists :=
    exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap hcomplete hsst
  let hrankingExists :=
    exists_preferenceRanking_of_preferenceComplete_sst preferenceGap hcomplete hsst
  constructor
  · exact canonicalOptMaximizeAnchorPruneTraceSource_success_probability_algorithm3_sourceCutoff
      (epsilon / 3) (2 * epsilon / 3) delta
      (sourceOptMaximizeAlgorithm3PruneMaxBatch
        (Arm := Arm) (epsilon / 3) (2 * epsilon / 3) delta)
      preferenceGap (Classical.choose hmaximumExists) hprobability
      (Classical.choose hrankingExists) (Classical.choose_spec hrankingExists)
      hdelta hdeltaLeOne (by linarith) hantisymmetric hself hcomplete hsst
      (by
        intro round hround
        exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
          (epsilon / 3) (2 * epsilon / 3) delta round hround)
      (by linarith) (Classical.choose_spec hmaximumExists) (by linarith) hdeltaLower
  · exact sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_sourceRateShape
      hepsilon hdelta hdeltaLeOne

/-- Exact-type proof endpoint for Supplement Lemma 18. -/
theorem lemma18_optMaximizeTail_proof : lemma18_optMaximizeTailSpec := by
  unfold lemma18_optMaximizeTailSpec
  intro Arm _ _ anchor candidates epsilon delta preferenceGap hprobability hantisymmetric hself
    hsst hepsilon hdelta hdeltaLeOne hdeltaLower hbranch
  classical
  dsimp only
  constructor
  · exact canonicalOptMaximizeTailSource_epsilonMaximum_probability anchor candidates
      preferenceGap hprobability epsilon delta hantisymmetric hself hsst hepsilon hdelta
      hdeltaLeOne hbranch
  · exact optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceEnvelope candidates
      (2 * epsilon / 3) epsilon epsilon delta hdelta hdeltaLeOne

/-- Exact-type proof endpoint for Supplement Lemma 19. -/
theorem lemma19_estimateProbability_proof : lemma19_estimateProbabilitySpec := by
  unfold lemma19_estimateProbabilitySpec
  intro Arm preferenceGap hprobability challenger incumbent epsilon delta hepsilon hdelta
    hdeltaLeOne
  constructor
  · constructor
    · simpa [estimateProbabilitySampleBudget] using
        meanEstimateSampleBudget_realTarget_le epsilon delta hepsilon
    · simpa [estimateProbabilitySampleBudget] using
        meanEstimateSampleBudget_lt_realTarget_add_one
          epsilon delta hepsilon hdelta hdeltaLeOne
  · let count := estimateProbabilitySampleBudget epsilon delta
    let law := (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent count).toMeasure
    let observation : ℕ → (Fin count → Bool) → ℝ :=
      canonicalComparisonBatchObservation count
    have hcountReal : 0 < (count : ℝ) := by
      dsimp only [count]
      exact fixedSampleBudget_pos 0 (2 * epsilon) delta (by linarith) hdelta hdeltaLeOne
    have hcount : 0 < count := by exact_mod_cast hcountReal
    have htail := bordaEmpiricalScore_nonconcentration_probability law observation count
      (1 / 2 + preferenceGap challenger incumbent) epsilon hcount
      (by
        simpa only [law, observation] using
          iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability challenger
            incumbent count)
      (by
        intro index hindex
        exact measurable_canonicalComparisonBatchObservation count index)
      (by
        intro index hindex
        exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
          challenger incumbent count index)
      (by
        intro index hindex
        exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
          challenger incumbent count index hindex)
      hepsilon.le
    have hnumeric := fixedSampleCompare_tail_le_delta_of_ceilingBudget
      0 (2 * epsilon) delta (by linarith) hdelta hdeltaLeOne
    calc
      (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent
          (estimateProbabilitySampleBudget epsilon delta)).toMeasure.real {batch | ¬
            |bordaEmpiricalScore
                (canonicalComparisonBatchObservation (estimateProbabilitySampleBudget epsilon delta))
                (estimateProbabilitySampleBudget epsilon delta) batch -
              (1 / 2 + preferenceGap challenger incumbent)| < epsilon} ≤
          2 * Real.exp (-((count : ℝ) * epsilon) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := htail
      _ ≤ delta := by
        have hhalf : 2 * epsilon / 2 = epsilon := by ring
        simpa only [count, estimateProbabilitySampleBudget, meanEstimateSampleBudget, sub_zero,
          hhalf] using hnumeric

/-- Exact-type proof endpoint for Supplement Lemma 20. -/
theorem lemma20_strongTransitivityRanking_proof : lemma20_strongTransitivityRankingSpec := by
  unfold lemma20_strongTransitivityRankingSpec
  constructor
  · intro Arm _ _
    letI : DecidableEq Arm := Classical.decEq Arm
    dsimp only
    exact lemma20_strongTransitivityRanking_canonicalUnorderedBatches_highProbability
      (Arm := Arm)
  · exact @lemma20_strongTransitivityRanking_sourceComparisonCount_real_le_sourceRateForm

/-- Exact-type proof endpoint for Supplement Lemma 21. -/
theorem lemma21_estimateBordaScore_proof : lemma21_estimateBordaScoreSpec := by
  unfold lemma21_estimateBordaScoreSpec
  intro Arm _ _ _ winProbability hprobability arm epsilon delta hepsilon hdelta hdeltaLeOne
  constructor
  · constructor
    · simpa [estimateBordaScoreSampleBudget] using
        meanEstimateSampleBudget_realTarget_le epsilon delta hepsilon
    · simpa [estimateBordaScoreSampleBudget] using
        meanEstimateSampleBudget_lt_realTarget_add_one
          epsilon delta hepsilon hdelta hdeltaLeOne
  · let count := estimateBordaScoreSampleBudget epsilon delta
    let law := (canonicalBordaBatchLaw winProbability hprobability count).toMeasure
    let observation : ℕ → (canonicalBordaBatchCoordinate Arm count → Bool) → ℝ :=
      canonicalBordaBatchObservation count arm
    have hcountReal : 0 < (count : ℝ) := by
      dsimp only [count]
      exact fixedSampleBudget_pos 0 (2 * epsilon) delta (by linarith) hdelta hdeltaLeOne
    have hcount : 0 < count := by exact_mod_cast hcountReal
    have htail := bordaEmpiricalScore_nonconcentration_probability law observation count
      (bordaScore winProbability arm) epsilon hcount
      (by
        simpa only [law, observation] using
          iIndepFun_canonicalBordaBatchObservation winProbability hprobability count arm)
      (by
        intro index hindex
        exact measurable_canonicalBordaBatchObservation count arm index)
      (by
        intro index hindex
        exact ae_canonicalBordaBatchObservation_mem_Icc winProbability hprobability count arm index)
      (by
        intro index hindex
        simpa using integral_canonicalBordaBatchObservation winProbability hprobability count arm
          ⟨index, hindex⟩)
      hepsilon.le
    have hnumeric := fixedSampleCompare_tail_le_delta_of_ceilingBudget
      0 (2 * epsilon) delta (by linarith) hdelta hdeltaLeOne
    calc
      (canonicalBordaBatchLaw winProbability hprobability
          (estimateBordaScoreSampleBudget epsilon delta)).toMeasure.real {labelTable | ¬
            |bordaEmpiricalScore
                (canonicalBordaBatchObservation (estimateBordaScoreSampleBudget epsilon delta) arm)
                (estimateBordaScoreSampleBudget epsilon delta) labelTable -
              bordaScore winProbability arm| < epsilon} ≤
          2 * Real.exp (-((count : ℝ) * epsilon) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := htail
      _ ≤ delta := by
        have hhalf : 2 * epsilon / 2 = epsilon := by ring
        simpa only [count, estimateBordaScoreSampleBudget, meanEstimateSampleBudget, sub_zero,
          hhalf] using hnumeric

/-- Exact-type proof endpoint for Supplement Theorem 22. -/
theorem theorem22_bordaRanking_proof : theorem22_bordaRankingSpec := by
  unfold theorem22_bordaRankingSpec
  constructor
  · intro Arm _ _ winProbability hprobability epsilon delta hepsilon hdelta hdeltaLeOne
    classical
    refine ⟨@empiricalBordaRanking Arm inferInstance, empiricalBordaRanking_isRule, ?_⟩
    exact theorem9_bordaRanking_uniformSampler_failure_probability
      winProbability hprobability epsilon delta hepsilon hdelta hdeltaLeOne
  · exact @theorem9_bordaRanking_sourceTotalSampleCount_real_le_sourceRateForm

end FalahatgarEtAl2017MaxingRanking
