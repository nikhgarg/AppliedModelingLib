import GolzHaghtalabYang2025Distortion.PaperInterface
import GolzHaghtalabYang2025Distortion.MainTheorems
import GolzHaghtalabYang2025Distortion.Theorem6

/-!
# Proof interface: Gölz--Haghtalab--Yang (2025)
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset

/-- Checked proof endpoint for the finite source-facing Lemma 1 target. -/
theorem lemma1_population_bradleyTerry_linearization_finite :
    lemma1_population_bradleyTerry_linearization_finiteSpec := by
  exact lemma1_population_bradleyTerry_linearization_finite_core

/-- Checked finite population-limit endpoint for source Theorem 2. -/
theorem theorem2_borda_population_limit_finite :
    theorem2_borda_population_limit_finiteSpec := by
  exact theorem2_borda_population_limit_finite_core

/-- Checked deterministic finite-score bridge for source Theorem 2. -/
theorem theorem2_borda_finiteScore_finite : theorem2_borda_finiteScore_finiteSpec := by
  intro User Alternative _ _ _ _ population utility hutility sampling btScale hbtScale empiricalScore
    winner scoreError hmax happrox alternative
  exact theorem2_welfare_square_bound_of_uniform_empirical_borda_error
    population utility hutility sampling hbtScale empiricalScore winner scoreError hmax happrox alternative

/-- Checked literal fixed-`d` iid-user strict-Borda-winner selection bridge. -/
theorem theorem2_borda_userBatch_strictSelection_finite :
    theorem2_borda_userBatch_strictSelection_finiteSpec := by
  intro Alternative _ _ responseLaw sampling preference comparisonsPerUser hcomparisons hcalibrated
    winner hsampling_pos hstrict
  exact theorem2_iidUserBatchBordaFailure_tendsto_zero_of_strictBordaWinner
    responseLaw sampling preference comparisonsPerUser hcomparisons hcalibrated winner
    hsampling_pos hstrict

/-- Checked finite literal-user welfare endpoint for source Theorem 2. -/
theorem theorem2_borda_userBatch_welfare_finite : theorem2_borda_userBatch_welfare_finiteSpec := by
  intro User Alternative _ _ _ _ population utility hutility sampling btScale hbtScale responseLaw
    hcalibrated users comparisonsPerUser husers hcomparisons minimumMass cutoff hminimumMass
    hminimumMass_lower hcutoff hsmall
  exact theorem2_iidUserBatch_empiricalBorda_welfare_failure_le_uniform_tail population utility
    hutility sampling hbtScale responseLaw hcalibrated users comparisonsPerUser husers hcomparisons
    minimumMass cutoff hminimumMass hminimumMass_lower hcutoff hsmall

/-- Checked literal source-rate finite welfare endpoint for source Theorem 2. -/
theorem theorem2_borda_userBatch_welfare_sourceRate_finite :
    theorem2_borda_userBatch_welfare_sourceRate_finiteSpec := by
  intro User Alternative _ _ _ _ _ population utility hutility sampling btScale hbtScale responseLaw
    hcalibrated users comparisonsPerUser husers hcomparisons minimumMass delta hminimumMass
    hminimumMass_lower hdelta hdelta_one hsource
  exact theorem2_iidUserBatch_empiricalBorda_welfare_failure_le_sourceRate population utility
    hutility sampling hbtScale responseLaw hcalibrated users comparisonsPerUser husers hcomparisons
    minimumMass delta hminimumMass hminimumMass_lower hdelta hdelta_one hsource

/-- Checked expected-welfare finite endpoint for every empirical-Borda tie breaker. -/
theorem theorem2_borda_userBatch_expectedWelfare_sourceRate_finite :
    theorem2_borda_userBatch_expectedWelfare_sourceRate_finiteSpec := by
  intro User Alternative _ _ _ _ _ population utility hutility sampling btScale hbtScale responseLaw
    hcalibrated users comparisonsPerUser husers hcomparisons minimumMass delta hminimumMass
    hminimumMass_lower hdelta hdelta_one hsource winner hwinner benchmark
  exact theorem2_iidUserBatch_expectedWelfare_ge_sourceRate population utility hutility sampling
    hbtScale responseLaw hcalibrated users comparisonsPerUser husers hcomparisons minimumMass delta
    hminimumMass hminimumMass_lower hdelta hdelta_one hsource winner hwinner benchmark

/-- Checked exact fixed-pair label-count second moment from Appendix D, Lemma 10. -/
theorem lemma10_fixedPairLabelCountSecondMoment_finite :
    lemma10_fixedPairLabelCountSecondMoment_finiteSpec := by
  intro Alternative _ _ sampling comparisonsPerUser first second hdistinct
  exact theorem10_pmfExp_userUnorderedPairCount_sq sampling comparisonsPerUser first second hdistinct

/-- Checked calibrated fixed-pair variance proxy from Appendix D, Lemma 10. -/
theorem lemma10_centeredPairWinVariance_finite :
    lemma10_centeredPairWinVariance_finiteSpec := by
  intro Alternative _ _ responseLaw preference sampling comparisonsPerUser first second hdistinct
    hcalibrated
  exact theorem10_pmfVariance_userCenteredPairWin_le hcalibrated sampling comparisonsPerUser
    first second hdistinct

/-- Checked fixed-pair Chernoff denominator step from Appendix D, Lemma 10. -/
theorem lemma10_fixedPairLabelCountLowerTail_finite :
    lemma10_fixedPairLabelCountLowerTail_finiteSpec := by
  intro Alternative _ _ sampling users comparisonsPerUser first second hdistinct cutoff t ht
  exact theorem10_iidLabelCount_lowerTail_exponential sampling users comparisonsPerUser
    first second hdistinct cutoff t ht

/-- Checked `ndq / 2` denominator event bound from Appendix D, Lemma 10. -/
theorem lemma10_fixedPairLabelCountHalfMean_finite :
    lemma10_fixedPairLabelCountHalfMean_finiteSpec := by
  intro Alternative _ _ sampling users comparisonsPerUser first second hdistinct
  exact theorem10_iidLabelCount_halfMean_lowerTail sampling users comparisonsPerUser
    first second hdistinct

/-- Checked fixed-pair minimum-mass radius algebra from Appendix D, Lemma 10. -/
theorem lemma10_fixedPairConfidenceRadiusMinMassEnvelope_finite :
    lemma10_fixedPairConfidenceRadiusMinMassEnvelope_finiteSpec := by
  intro Alternative _ _ sampling users comparisonsPerUser first second minimumMass logLevel
    husers hcomparisons hminimumMass hfirst hsecond hlogLevel
  exact theorem10_fixedPairConfidenceRadius_le_minMassEnvelope sampling users comparisonsPerUser
    first second minimumMass logLevel husers hcomparisons hminimumMass hfirst hsecond hlogLevel

/-- Checked literal iid-user Bernstein numerator tail from Appendix D, Lemma 10. -/
theorem lemma10_iidUserCenteredPairWinUpperTail_finite :
    lemma10_iidUserCenteredPairWinUpperTail_finiteSpec := by
  intro Alternative _ _ responseLaw preference hcalibrated sampling users comparisonsPerUser
    first second hdistinct cutoff hcutoff hden
  exact theorem10_iidUserCenteredPairWin_upperTail_bernstein hcalibrated sampling users
    comparisonsPerUser first second hdistinct cutoff hcutoff hden

/-- Checked complete fixed-pair empirical-win-rate concentration step from Appendix D. -/
theorem lemma10_iidUserEmpiricalWinRateTail_finite :
    lemma10_iidUserEmpiricalWinRateTail_finiteSpec := by
  intro Alternative _ _ responseLaw preference hcalibrated sampling users comparisonsPerUser
    first second hdistinct cutoff hcutoff hbernstein hincidence
  exact theorem10_iidUserEmpiricalWinRate_tail_bound hcalibrated sampling users
    comparisonsPerUser first second hdistinct cutoff hcutoff hbernstein hincidence

/-- Checked all-distinct-pairs union of the literal fixed-pair Lemma 10 tails. -/
theorem lemma10_iidUserEmpiricalWinRateUniformOffDiag_finite :
    lemma10_iidUserEmpiricalWinRateUniformOffDiag_finiteSpec := by
  intro Alternative _ _ responseLaw preference hcalibrated sampling users comparisonsPerUser
    husers hcomparisons hsampling epsilon hepsilon
  exact theorem10_iidUserEmpiricalWinRate_uniformOffDiag_tail_bound hcalibrated sampling users
    comparisonsPerUser husers hcomparisons hsampling epsilon hepsilon

/-- Checked all-pairs source form of the Lemma 10 finite union. -/
theorem lemma10_iidUserPaperWinRateUniform_finite :
    lemma10_iidUserPaperWinRateUniform_finiteSpec := by
  intro Alternative _ _ responseLaw preference hcalibrated sampling users comparisonsPerUser
    husers hcomparisons hsampling epsilon hepsilon
  exact theorem10_iidUserPaperWinRate_uniform_tail_bound hcalibrated sampling users
    comparisonsPerUser husers hcomparisons hsampling epsilon hepsilon

/-- Checked source-sharp centered raw-Borda tail from Appendix D, Lemma 11. -/
theorem lemma11_iidUserSharpCenteredBordaMinMassTail_finite :
    lemma11_iidUserSharpCenteredBordaMinMassTail_finiteSpec := by
  intro Alternative _ _ responseLaw preference hcalibrated sampling users comparisonsPerUser
    alternative minimumMass logLevel husers hcomparisons hminimumMass hmass hlogLevel
  exact theorem11_iidUserBordaPairwiseCentered_minMass_tail hcalibrated sampling users
    comparisonsPerUser alternative minimumMass logLevel husers hcomparisons hminimumMass hmass
    hlogLevel

/-- Checked source-sharp normalized-Borda finite tail from Appendix D, Lemma 11. -/
theorem lemma11_iidUserSharpNormalizedBordaMinMassTail_finite :
    lemma11_iidUserSharpNormalizedBordaMinMassTail_finiteSpec := by
  intro Alternative _ _ responseLaw sampling preference users comparisonsPerUser husers hcomparisons
    hcalibrated alternative minimumMass logLevel incidenceCutoff hminimumMass hmass hlogLevel
    hincidence hden
  exact theorem11_iidUserLatentBordaScore_minMass_tail responseLaw sampling preference users
    comparisonsPerUser husers hcomparisons hcalibrated alternative minimumMass logLevel
    incidenceCutoff hminimumMass hmass hlogLevel hincidence hden

/-- Checked closed-form source-rate confidence corollary for Appendix D, Lemma 11. -/
theorem lemma11_iidUserSharpNormalizedBordaSourceRateConfidence_finite :
    lemma11_iidUserSharpNormalizedBordaSourceRateConfidence_finiteSpec := by
  intro Alternative _ _ _ responseLaw sampling preference users comparisonsPerUser husers hcomparisons
    hcalibrated alternative minimumMass delta hminimumMass hmass hdelta hdelta_one hsource
  exact theorem11_iidUserLatentBordaScore_minMass_sourceRate_confidence responseLaw sampling
    preference users comparisonsPerUser husers hcomparisons hcalibrated alternative minimumMass delta
    hminimumMass hmass hdelta hdelta_one hsource

/-- Checked simultaneous source-rate confidence theorem for Appendix D, Lemma 11. -/
theorem lemma11_iidUserSharpNormalizedBordaSourceRateUniformConfidence_finite :
    lemma11_iidUserSharpNormalizedBordaSourceRateUniformConfidence_finiteSpec := by
  intro Alternative _ _ _ responseLaw sampling preference users comparisonsPerUser husers hcomparisons
    hcalibrated minimumMass delta hminimumMass hmass hdelta hdelta_one hsource
  exact theorem11_iidUserLatentBordaScore_minMass_sourceRate_uniform_confidence responseLaw sampling
    preference users comparisonsPerUser husers hcomparisons hcalibrated minimumMass delta
    hminimumMass hmass hdelta hdelta_one hsource

/-- Checked literal iid-user normalized-Borda concentration step from Appendix D, Lemma 11. -/
theorem lemma11_iidUserNormalizedBordaTail_finite :
    lemma11_iidUserNormalizedBordaTail_finiteSpec := by
  intro Alternative _ _ responseLaw sampling preference users comparisonsPerUser husers hcomparisons
    hcalibrated alternative hsampling cutoff hcutoff hsmall hden
  exact theorem11_iidBordaScore_tail_bound responseLaw sampling preference users comparisonsPerUser
    husers hcomparisons hcalibrated alternative hsampling cutoff hcutoff hsmall hden

/-- Checked uniform finite minimum-mass Borda tail from Appendix D, Lemma 11. -/
theorem lemma11_iidUserNormalizedBordaUniformMinMassTail_finite :
    lemma11_iidUserNormalizedBordaUniformMinMassTail_finiteSpec := by
  intro Alternative _ _ responseLaw sampling preference users comparisonsPerUser husers hcomparisons
    hcalibrated minimumMass cutoff hminimumMass hminimumMass_lower hcutoff hsmall
  exact theorem11_iidBordaScore_uniform_minMass_tail_bound responseLaw sampling preference users
    comparisonsPerUser husers hcomparisons hcalibrated minimumMass cutoff hminimumMass
    hminimumMass_lower hcutoff hsmall

/-- Checked literal population endpoint for source Theorem 6. -/
theorem theorem6_rlhf_population_lower_bound : theorem6_rlhf_population_lower_boundSpec := by
  intro beta hbeta_ten
  have hbeta_hundred : Real.log 100 ≤ beta :=
    theorem6_log_hundred_le_ten.trans hbeta_ten
  exact theorem6_exists_populationMLE_policies_exp_distortion_lower hbeta_ten hbeta_hundred

/-- Checked literal iid finite-MLE ordering endpoint for source Theorem 6. -/
theorem theorem6_iidFiniteMLEOrder_finite : theorem6_iidFiniteMLEOrder_finiteSpec := by
  intro beta hbeta
  exact theorem6_iidFiniteMLEBadOrderProbability_tendsto_zero hbeta

/-- Checked population-limit endpoint for source Theorem 7. -/
theorem theorem7_nlhf_population_limit : theorem7_nlhf_population_limitSpec := by
  intro User Alternative _ _ _ _ population utility hutility btScale hbtScale reference klBudget
    nlhfPolicy benchmark hnlhf hbenchmark
  exact theorem7_nlhf_population_limit_core population utility hutility hbtScale reference klBudget
    nlhfPolicy benchmark hnlhf hbenchmark

/-- Checked population-limit endpoint for source Corollary 4. -/
theorem corollary4_maximalLottery_population_limit : corollary4_maximalLottery_population_limitSpec := by
  intro User Alternative _ _ _ _ population utility hutility btScale hbtScale maximalLottery benchmark
    hmaximal
  exact corollary4_maximalLottery_population_limit_core population utility hutility hbtScale
    maximalLottery benchmark hmaximal

/-- Checked finite-real-regularization endpoint for source Corollary 8. -/
theorem corollary8_regularizedNlhf_population_limit : corollary8_regularizedNlhf_population_limitSpec := by
  intro User Alternative _ _ _ _ population utility hutility btScale hbtScale reference policy
    klRegularization hregularization hequilibrium benchmark hbenchmark
  exact corollary8_regularizedNlhf_population_limit_core population utility hutility hbtScale
    reference policy klRegularization hregularization hequilibrium benchmark hbenchmark

/-- Checked finite `d = 1` Appendix-E.3 endpoint for source Theorem 3. -/
theorem theorem3_d1_finite : theorem3_d1_finiteSpec := by
  intro Alternative _ _ _ pairSampling beta epsilon hbeta hepsilon rule
  exact theorem3_d1_finite_core pairSampling beta epsilon hbeta hepsilon rule

/-- Checked finite source-facing distortion endpoint for Theorem 3 with `d = 1`. -/
theorem theorem3_d1_finite_distortion : theorem3_d1_finite_distortionSpec := by
  intro Alternative _ _ _ hcard pairSampling beta epsilon hbeta hepsilon hepsilon_upper rule
  exact theorem3_d1_finite_distortion_core hcard pairSampling beta epsilon hbeta hepsilon
    hepsilon_upper rule

/-- Checked large-`m` source endpoint for Theorem 3 with one comparison per user. -/
theorem theorem3_d1_asymptotic : theorem3_d1_asymptoticSpec := by
  intro beta hbeta pairSampling rule delta hdelta
  exact theorem3_d1_asymptotic_lower_bound hbeta pairSampling rule delta hdelta

/-- Checked all-`m` finite-sample endpoint for Appendix-E.2's Theorem 12. -/
theorem theorem12_all_m_iidBorda_lower_bound_checked : theorem12_all_m_iidBorda_lower_boundSpec := by
  intro beta gamma q hbeta hgamma hgamma_lt_one hq m hm
  exact theorem12_all_m_iidBorda_lower_bound hbeta hgamma hgamma_lt_one hq m hm

/-! ## Source-presentation endpoints -/

/-- Proof endpoint for the source empirical normalized-Borda definition. -/
theorem empirical_borda_definition
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (rule : ∀ horizon : ℕ, (Fin horizon → Report) → PMF Alternative) :
    IsEmpiricalBordaRule wins incidences rule ↔
      empiricalBordaDefinitionSpec wins incidences rule := by
  rfl

/-- Proof endpoint for the source population-limit Borda definition. -/
theorem population_borda_definition
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (winner : Alternative) :
    IsPopulationBordaWinner sampling preference winner ↔
      populationBordaDefinitionSpec sampling preference winner := by
  rfl

/-- Proof endpoint for the source finite constrained-RLHF definition. -/
theorem rlhf_definition
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (scoreReference : Alternative) (reference policy : PMF Alternative)
    (klBudget : ℝ) (score : ScoreVector Alternative) :
    (PMFFullSupport reference ∧
      isPairwiseMLE (ofBinaryReports sample) Real.sigmoid
        scoreReference score ∧
      IsConstrainedPolicyScoreMax
        (PMF.pure PUnit.unit.{1}) (contextFreeAlternativePolicy reference)
        (fun _ => score) klBudget (contextFreeAlternativePolicy policy)) ↔
      rlhfDefinitionSpec sample scoreReference reference policy klBudget score := by
  rfl

/-- Proof endpoint for the source constrained-NLHF definition. -/
theorem nlhf_definition
    {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative) :
    (PMFFullSupport reference ∧
      IsConstrainedPopulationBradleyTerryMaximin
        population utility btScale reference klBudget policy) ↔
      nlhfDefinitionSpec population utility btScale reference klBudget policy := by
  rfl

/-- A full-support policy is recovered by tilting the reference policy with
its own policy/reference log-ratio reward. -/
theorem appendixF3_sourceDpoPolicy_recover_implicitReward
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference policy : PMF Alternative) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (href : PMFFullSupport reference)
    (hpolicy : PMFFullSupport policy) :
    sourceDpoPolicy reference
      (fun alternative =>
        dpoImplicitReward (contextFreeAlternativePolicy policy)
          (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative)
      klWeight = policy := by
  apply PMF.ext
  intro alternative
  apply (ENNReal.toReal_eq_toReal_iff'
    ((sourceDpoPolicy reference
      (fun alternative =>
        dpoImplicitReward (contextFreeAlternativePolicy policy)
          (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative)
      klWeight).apply_ne_top alternative)
    (policy.apply_ne_top alternative)).mp
  unfold sourceDpoPolicy dpoOptimalPolicy contextFreeAlternativePolicy contextExponentialTiltPolicy
  rw [exponentialTilt_apply_toReal]
  simp only [dpoImplicitReward, policyLogRatio]
  have hcancel : klWeight⁻¹ * klWeight = 1 := inv_mul_cancel₀ hweight
  have hpartition : Probability.finiteMGF reference
      (fun alternative => klWeight *
        (Real.log (policy alternative).toReal - Real.log (reference alternative).toReal))
      klWeight⁻¹ = 1 := by
    calc
      Probability.finiteMGF reference
          (fun alternative => klWeight *
            (Real.log (policy alternative).toReal - Real.log (reference alternative).toReal))
          klWeight⁻¹ = ∑ a, (reference a).toReal * Real.exp
              (klWeight⁻¹ * (klWeight *
                (Real.log (policy a).toReal - Real.log (reference a).toReal))) := rfl
      _ = ∑ a, (policy a).toReal := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show klWeight⁻¹ * (klWeight *
              (Real.log (policy a).toReal - Real.log (reference a).toReal)) =
              (klWeight⁻¹ * klWeight) *
                (Real.log (policy a).toReal - Real.log (reference a).toReal) by ring,
          hcancel, one_mul,
          Real.exp_sub, Real.exp_log (hpolicy a), Real.exp_log (href a)]
        field_simp [ne_of_gt (href a)]
      _ = 1 := pmfToRealSum policy
  rw [hpartition]
  field_simp
  rw [Real.exp_sub, Real.exp_log (hpolicy alternative), Real.exp_log (href alternative)]
  field_simp [ne_of_gt (href alternative)]

/-- A full-support minimizer of the literal DPO loss recovers a normalized
fixed-reference maximum-likelihood reward, and its normalized tilt is itself. -/
theorem appendixF3_dpoMinimizer_recoveredReward
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (scoreReference : Alternative) (reference policy : PMF Alternative) (klWeight : ℝ)
    (href : PMFFullSupport reference) (hweight : 0 < klWeight)
    (hmin : IsSourceDpoLossMinimizer sample reference klWeight policy) :
    isPairwiseMLE (ofBinaryReports sample) Real.sigmoid scoreReference
      (sourceDpoNormalizedMLEReward scoreReference reference policy klWeight) ∧
    sourceDpoPolicy reference
      (sourceDpoNormalizedMLEReward scoreReference reference policy klWeight)
      klWeight = policy := by
  let implicit : ScoreVector Alternative := fun alternative =>
    dpoImplicitReward (contextFreeAlternativePolicy policy)
      (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative
  constructor
  · constructor
    · change
        dpoImplicitReward (contextFreeAlternativePolicy policy)
            (contextFreeAlternativePolicy reference) klWeight PUnit.unit scoreReference -
          dpoImplicitReward (contextFreeAlternativePolicy policy)
            (contextFreeAlternativePolicy reference) klWeight PUnit.unit scoreReference = 0
      exact sub_self _
    · intro candidate _hcandidate
      change pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate ≤
        pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid
          (fun alternative =>
            dpoImplicitReward (contextFreeAlternativePolicy policy)
              (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative -
            dpoImplicitReward (contextFreeAlternativePolicy policy)
              (contextFreeAlternativePolicy reference) klWeight PUnit.unit scoreReference)
      let candidatePolicy : PMF Alternative := sourceDpoPolicy reference candidate klWeight
      have hweight_ne : klWeight ≠ 0 := ne_of_gt hweight
      have hrefPolicy : PolicyFullSupport (contextFreeAlternativePolicy reference) := by
        intro context alternative
        exact href alternative
      have hcandidateFull : PMFFullSupport candidatePolicy := by
        have hfull := dpoOptimalPolicy_fullSupport
          (contextFreeAlternativePolicy reference) (fun _ : PUnit => candidate) klWeight hrefPolicy
        simpa [candidatePolicy, sourceDpoPolicy] using hfull PUnit.unit
      have hminCompare := hmin.2 candidatePolicy hcandidateFull
      have hpolicyLoss : sourceDpoBinaryReportLoss sample reference policy klWeight =
          -pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid implicit := by
        rfl
      have hequivalent : RewardEquivalent
          (dpoImplicitReward
            (dpoOptimalPolicy (contextFreeAlternativePolicy reference)
              (fun (_ : PUnit) => candidate) klWeight)
            (contextFreeAlternativePolicy reference) klWeight)
          (fun (_ : PUnit) => candidate) :=
        dpoImplicitReward_tilt_equivalent (contextFreeAlternativePolicy reference)
          (fun (_ : PUnit) => candidate) klWeight hweight_ne hrefPolicy
      have hcandidateLoss : sourceDpoBinaryReportLoss sample reference candidatePolicy klWeight =
          sourceRlhfBinaryReportLoss sample candidate := by
        unfold sourceDpoBinaryReportLoss sourceRlhfBinaryReportLoss candidatePolicy sourceDpoPolicy
        change -pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid
            (fun alternative =>
              dpoImplicitReward
                (dpoOptimalPolicy (contextFreeAlternativePolicy reference)
                  (fun (_ : PUnit) => candidate) klWeight)
                (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative) =
          -pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate
        rcases hequivalent with ⟨shift, hshift⟩
        have himplicit :
            (fun alternative =>
              dpoImplicitReward
                (dpoOptimalPolicy (contextFreeAlternativePolicy reference)
                  (fun (_ : PUnit) => candidate) klWeight)
                (contextFreeAlternativePolicy reference) klWeight PUnit.unit alternative) =
              fun alternative => candidate alternative + -shift PUnit.unit := by
          funext alternative
          have h := hshift PUnit.unit alternative
          linarith
        rw [himplicit, pairwiseLogLikelihood_shift]
      have horder : pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate ≤
          pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid implicit := by
        rw [hpolicyLoss, hcandidateLoss] at hminCompare
        unfold sourceRlhfBinaryReportLoss at hminCompare
        linarith
      have hnormalized :
          pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid
            (fun alternative => implicit alternative - implicit scoreReference) =
            pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid implicit := by
        rw [show (fun alternative => implicit alternative - implicit scoreReference) =
            (fun alternative => implicit alternative + -implicit scoreReference) by
              funext alternative; ring,
          pairwiseLogLikelihood_shift]
      change pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid candidate ≤
        pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid
          (fun alternative => implicit alternative - implicit scoreReference)
      rw [hnormalized]
      exact horder
  · have hraw := appendixF3_sourceDpoPolicy_recover_implicitReward reference policy klWeight
      (ne_of_gt hweight) href hmin.1
    have hshift := contextExponentialTiltPolicy_add_context_constant
      (contextFreeAlternativePolicy reference) (fun (_ : PUnit) => implicit)
      (fun _ => -implicit scoreReference) klWeight⁻¹
    have hsame : sourceDpoPolicy reference
        (sourceDpoNormalizedMLEReward scoreReference reference policy klWeight) klWeight =
        sourceDpoPolicy reference implicit klWeight := by
      change (contextExponentialTiltPolicy (contextFreeAlternativePolicy reference)
        (fun _ alternative => implicit alternative + -implicit scoreReference) klWeight⁻¹ PUnit.unit) =
        (contextExponentialTiltPolicy (contextFreeAlternativePolicy reference)
          (fun _ alternative => implicit alternative) klWeight⁻¹ PUnit.unit)
      exact congrFun hshift PUnit.unit
    rw [hsame]
    exact hraw

/-- Checked corrected Appendix-F.3 DPO/RLHF equivalence.  The checked policy
is normalized, and the fitted reward is identified only up to its additive
constant. -/
theorem appendixF3_dpo_rlhf_equivalence : appendixF3DpoRlhfEquivalenceSpec := by
  intro Alternative _ _ horizon sample scoreReference reference reward klWeight hmle hweight hreference
  have hreferencePolicy : PolicyFullSupport (contextFreeAlternativePolicy reference) := by
    intro context alternative
    exact hreference alternative
  have hweight_ne : klWeight ≠ 0 := ne_of_gt hweight
  have hequivalent : RewardEquivalent
      (dpoImplicitReward
        (dpoOptimalPolicy (contextFreeAlternativePolicy reference)
          (fun (_ : PUnit.{1}) => reward) klWeight)
        (contextFreeAlternativePolicy reference) klWeight)
      (fun (_ : PUnit.{1}) => reward) :=
    dpoImplicitReward_tilt_equivalent (contextFreeAlternativePolicy reference)
      (fun (_ : PUnit.{1}) => reward) klWeight hweight_ne hreferencePolicy
  have hpolicy :
      contextFreeAlternativePolicy (sourceDpoPolicy reference reward klWeight) =
        dpoOptimalPolicy (contextFreeAlternativePolicy reference)
          (fun (_ : PUnit.{1}) => reward) klWeight := by
    funext context
    cases context
    rfl
  have hloss :
      sourceDpoBinaryReportLoss sample reference
          (sourceDpoPolicy reference reward klWeight) klWeight =
        sourceRlhfBinaryReportLoss sample reward := by
    unfold sourceDpoBinaryReportLoss sourceRlhfBinaryReportLoss
    rw [hpolicy]
    rcases hequivalent with ⟨shift, hshift⟩
    have himplicit :
        (fun alternative =>
          dpoImplicitReward
            (dpoOptimalPolicy (contextFreeAlternativePolicy reference)
              (fun (_ : PUnit.{1}) => reward) klWeight)
            (contextFreeAlternativePolicy reference) klWeight PUnit.unit.{1} alternative) =
          fun alternative => reward alternative + -shift PUnit.unit.{1} := by
      funext alternative
      have h := hshift PUnit.unit.{1} alternative
      linarith
    rw [himplicit, pairwiseLogLikelihood_shift]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hloss
  · simpa [sourceDpoPolicy] using hequivalent
  · constructor
    · have hfullPolicy := dpoOptimalPolicy_fullSupport
        (contextFreeAlternativePolicy reference) (fun (_ : PUnit.{1}) => reward)
        klWeight hreferencePolicy
      simpa [sourceDpoPolicy] using hfullPolicy PUnit.unit.{1}
    · intro candidate _hcandidate
      have hle := isPairwiseMLE_global_max (ofBinaryReports sample) Real.sigmoid
        scoreReference reward hmle
        (fun alternative =>
          dpoImplicitReward (contextFreeAlternativePolicy candidate)
            (contextFreeAlternativePolicy reference) klWeight PUnit.unit.{1} alternative)
      calc
        sourceDpoBinaryReportLoss sample reference
            (sourceDpoPolicy reference reward klWeight) klWeight =
            sourceRlhfBinaryReportLoss sample reward := hloss
        _ ≤ sourceDpoBinaryReportLoss sample reference candidate klWeight := by
          unfold sourceRlhfBinaryReportLoss sourceDpoBinaryReportLoss
          exact neg_le_neg hle
  · intro policy hmin
    exact appendixF3_dpoMinimizer_recoveredReward sample scoreReference reference policy klWeight
      hreference hweight hmin

/-- Proof endpoint for source Lemma 1. -/
theorem lemma1_linearization : lemma1Spec := by
  exact lemma1_population_bradleyTerry_linearization_finite

/-- Proof endpoint for the complete source Theorem 2 presentation. -/
theorem theorem2_borda_distortion : theorem2Spec := by
  constructor
  · exact theorem2_borda_population_limit_finite
  · exact theorem2_borda_userBatch_expectedWelfare_sourceRate_finite

/-- Proof endpoint for both branches of source Theorem 3. -/
theorem theorem3_voting_rule_lower_bound : theorem3Spec := by
  constructor
  · exact theorem3_d1_asymptotic
  · exact theorem3_d2_asymptotic_lower_bound_of_sourceReportMarginals

/-- Proof endpoint for source Corollary 4. -/
theorem corollary4_maximal_lottery : corollary4Spec := by
  constructor
  · exact corollary4_maximalLottery_population_limit
  · intro User Alternative _ _ _ _ _ _ _ population utility hutility btScale hbtScale
      responseLaw preference hcalibrated sampling husers_pos hcomparisons_pos
      minimumMass hminimumMass_pos hminimumMass delta hdelta_pos hdelta_le_one
      hsource_failure hpreference
    constructor
    · intro sample
      exact corollary4IidUserEmpiricalMaximalLottery_isEmpiricalMaximalLottery sample
    · exact corollary4_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceConfidence
        population utility hutility hbtScale responseLaw preference hcalibrated sampling
        husers_pos hcomparisons_pos minimumMass hminimumMass_pos hminimumMass
        delta hdelta_pos hdelta_le_one hsource_failure hpreference

/-- Proof endpoint for the informal source Theorem 5 consequence. -/
theorem theorem5_borda_lower_bound : theorem5Spec := by
  constructor
  · intro beta hbeta
    let gamma := theorem12LogChoice beta
    have hgamma : 0 < gamma := by
      dsimp [gamma, theorem12LogChoice]
      exact div_pos (Real.log_pos (by linarith)) hbeta
    have hgamma_lt_one : gamma < 1 := by
      dsimp [gamma, theorem12LogChoice]
      apply (div_lt_iff₀ hbeta).mpr
      simpa using Real.log_lt_sub_one_of_pos
        (by linarith : 0 < beta + 1) (by linarith : beta + 1 ≠ 1)
    refine ⟨hgamma, hgamma_lt_one, ?_, ?_⟩
    · exact theorem12_eq10Coefficient_gt_theorem3Coefficient
        hbeta hgamma hgamma_lt_one
    · intro q hq m hm
      exact theorem12_all_m_iidBorda_lower_bound_checked
        hbeta hgamma hgamma_lt_one hq m hm
  · exact theorem12_eq10Coefficient_logChoice_ratio_limit

/-- Proof endpoint for the complete formal Appendix Theorem 12 presentation. -/
theorem theorem12_borda_lower_bound : theorem12Spec := by
  constructor
  · exact theorem12_all_m_iidBorda_lower_bound_checked
  · constructor
    · intro beta gamma hbeta hgamma hgamma_lt_one
      exact theorem12_eq10Coefficient_gt_theorem3Coefficient hbeta hgamma hgamma_lt_one
    · exact theorem12_eq10Coefficient_logChoice_ratio_limit

/-- Proof endpoint for source Theorem 6. -/
theorem theorem6_rlhf_distortion : theorem6Spec := by
  intro beta hbeta_ten
  have hbeta_hundred : Real.log 100 ≤ beta :=
    theorem6_log_hundred_le_ten.trans hbeta_ten
  obtain ⟨eta, heta_pos, heta_le_one, hdistortion⟩ :=
    theorem6_exists_ae_eventually_finiteMLE_constrainedPolicies_exp_distortion_lower
      hbeta_ten hbeta_hundred
  refine ⟨eta, heta_pos, heta_le_one, ?_, hdistortion⟩
  have hcopies := theorem6CopyCount_pos beta
  simp only [theorem6Alternative, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Proof endpoint for the complete source Theorem 7 presentation. -/
theorem theorem7_nlhf_distortion : theorem7Spec := by
  constructor
  · intro User Alternative _ _ _ _ population utility hutility btScale hbtScale reference
      klBudget nlhfPolicy benchmark _hbudget _hreference
    exact theorem7_nlhf_population_limit population utility hutility hbtScale reference klBudget
      nlhfPolicy benchmark
  · intro User Alternative _ _ _ _ _ users comparisonsPerUser population utility hutility btScale
      hbtScale responseLaw preference hcalibrated sampling husers hcomparisons minimumMass
      hminimumMassPos hminimumMass reference klBudget hbudget _hreference
    exact theorem7_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceConfidence
      population utility hutility hbtScale responseLaw preference hcalibrated sampling husers
      hcomparisons minimumMass hminimumMassPos hminimumMass reference klBudget hbudget

/-- Proof endpoint for source Corollary 8. -/
theorem corollary8_regularized_nlhf : corollary8Spec := by
  intro User Alternative _ _ _ _ population utility hutility btScale hbtScale reference policy
    klRegularization hregularization _hreference
  exact corollary8_regularizedNlhf_population_limit population utility hutility hbtScale reference
    policy klRegularization hregularization

/-- Proof endpoint for source Theorem 9. -/
theorem theorem9_correlated_sampling_unbounded : theorem9Spec := by
  intro beta hbeta bound
  obtain ⟨n, hbound, hn⟩ :=
    ((theorem9_prefix_distortion_tendsto_atTop hbeta).eventually_gt_atTop bound).and
      (Filter.eventually_ge_atTop 2) |>.exists
  let m := n + 1
  have hm : 3 ≤ m := by dsimp [m]; omega
  obtain ⟨epsilon, hepsilon_pos, hepsilon_lt_one, hpopulationOrder⟩ :=
    theorem9_exists_epsilon_all_adjacent_order hbeta hm
  refine ⟨m, hm, epsilon, hepsilon_pos, hepsilon_lt_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem9_prefixProfile_unitInterval hbeta m
  · exact theorem9UniformReference_fullSupport m (by omega)
  · exact theorem9ComparisonSampling_isSymmetric hm epsilon
  · exact theorem9ComparisonSampling_zeroDiagonal hm epsilon
  · exact theorem9ComparisonSampling_fullOffDiagonalSupport
      hm epsilon hepsilon_pos hepsilon_lt_one
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  · letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
    have hnoBad := theorem9_ae_eventually_noFiniteMLEBadOrder_of_populationOrder
      hbeta hm epsilon hepsilon_pos hepsilon_lt_one hpopulationOrder
    have hexists := theorem9_ae_eventually_existsFiniteMLE
      (beta := beta) hm epsilon hepsilon_pos hepsilon_lt_one
    filter_upwards [hnoBad, hexists] with path hnoBadPath hexistsPath
    filter_upwards [hnoBadPath, hexistsPath] with horizon hnoBadHorizon hexistsHorizon
    refine ⟨hexistsHorizon, ?_⟩
    intro reward hmle
    have horder : ∀ edge : Fin (m - 1),
        reward (theorem9EdgeLower edge) < reward (theorem9Succ edge) := by
      intro edge
      by_contra hnot
      apply hnoBadHorizon
      exact ⟨reward, hmle, edge, le_of_not_gt hnot⟩
    let first : Fin m := ⟨0, by omega⟩
    let last : Fin m := ⟨m - 1, by omega⟩
    refine ⟨PMF.pure last, PMF.pure first, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact theorem9_every_policy_uniformKL_feasible (by omega) (PMF.pure last)
    · intro other _
      exact theorem9_pure_last_reward_maximizes_of_adjacent_order
        (by omega) reward horder other
    · exact theorem9_every_policy_uniformKL_feasible (by omega) (PMF.pure first)
    · intro other _
      simpa [AppliedModelingLib.Alignment.Welfare.policyAverageUtility,
        theorem9PrefixWelfare] using
        (theorem9_pure_first_welfare_maximizes hbeta (by omega) other)
    · rw [AppliedModelingLib.Alignment.Welfare.policyAverageUtility, pmfExp_pure]
      dsimp [last, theorem9PrefixProfile, theorem9PrefixWelfare]
      exact theorem9_prefixWelfare_last_pos hbeta (by omega)
    · have hratio := theorem9_pure_prefix_distortion_eq hbeta (m := m) (by omega)
      rw [AppliedModelingLib.Alignment.Welfare.policyAverageUtility,
        AppliedModelingLib.Alignment.Welfare.policyAverageUtility, pmfExp_pure, pmfExp_pure]
      rw [show first = (⟨0, by omega⟩ : Fin m) by rfl,
        show last = (⟨m - 1, by omega⟩ : Fin m) by rfl]
      change theorem9PrefixWelfare beta m first /
          theorem9PrefixWelfare beta m last > bound
      rw [show first = (⟨0, by omega⟩ : Fin m) by rfl,
        show last = (⟨m - 1, by omega⟩ : Fin m) by rfl]
      have hratio' : theorem9PrefixWelfare beta m (⟨0, by omega⟩ : Fin m) /
          theorem9PrefixWelfare beta m (⟨m - 1, by omega⟩ : Fin m) =
            ((1 : ℝ) / 3) / lemma15AverageUtility beta (m - 1) := by
        simpa only [pmfExp_pure] using hratio
      rw [hratio']
      simpa [m] using hbound

/-- Proof endpoint for source Lemma 10. -/
theorem lemma10_empirical_win_rate_concentration : lemma10Spec := by
  exact theorem10_iidUserPaperWinRate_uniform_source_confidence

/-- Proof endpoint for source Lemma 11. -/
theorem lemma11_borda_concentration : lemma11Spec := by
  exact lemma11_iidUserSharpNormalizedBordaSourceRateUniformConfidence_finite

/-- Proof endpoint for both directions of source Proposition 13. -/
theorem proposition13_nlhf_equivalence : proposition13Spec := by
  constructor
  · intro Alternative _ _ preference reference policy klWeight hreference hregularized
    exact AppliedModelingLib.GameTheory.PreferenceGame.contextFreeExtendedRegularizedPreferenceGameEquilibrium_is_finiteKLPreferenceMaximinAtAttainedKL
        preference reference policy klWeight hreference hregularized
  · intro Alternative _ _ preference reference policy klBudget _ hreference hmaximin
    exact AppliedModelingLib.GameTheory.PreferenceGame.finiteKLPreferenceMaximin_is_extended_regularized
      preference reference policy klBudget hreference hmaximin

/-- Proof endpoint for both directions of source Proposition 14. -/
theorem proposition14_rlhf_equivalence : proposition14Spec := by
  constructor
  · intro Alternative _ _ reference policy score klWeight hreference hregularized
    exact AppliedModelingLib.finiteKL_extendedRegularizedUtilityMax_is_constrainedAt_attainedKL
      reference policy score klWeight hreference hregularized
  · intro Alternative _ _ reference policy score klBudget _ hreference hfeasible hmax
    exact AppliedModelingLib.finiteKL_constrainedUtilityMax_is_extended_regularized
      reference policy score klBudget hreference hfeasible hmax

/-- Proof endpoint for source Lemma 15. -/
theorem lemma15_infinite_sequence : lemma15Spec := by
  intro beta hbeta
  refine ⟨lemma15Population, lemma15Profile beta,
    lemma15_profile_unitInterval hbeta, ?_, ?_⟩
  · rw [lemma15_population_average_eq]
    exact lemma15_average_zero beta
  · intro n
    have hsource := (lemma15_source_construction hbeta).2.1 n
    refine ⟨?_, ?_, ?_, lemma15_population_adjacent_preference hbeta n⟩
    · simpa only [lemma15_population_average_eq] using hsource.1
    · simpa only [lemma15_population_average_eq] using hsource.2.1
    · simpa only [lemma15_population_average_eq] using hsource.2.2.1

end GolzHaghtalabYang2025Distortion
