import KR21Monoculture.GaussianTheorem2Definition1Transport
import KR21Monoculture.LaplaceTheorem2Definition1Transport

/-!
# Appendix C Theorem 6 and Lemmas 2--3 at the literal RUM source surface

This file keeps the source experiment visible: one innovation vector is drawn
and candidate `i` receives score `x_i + epsilon_i / theta`.  It does not take
a coupling, a transition-mass comparison, or a ranking-law identification as
an assumption.  The Gaussian and Laplace Theorem-6 endpoints below transport
their literal source laws through already-proved product-measure transports.

The pointwise part of Lemma 2 is distribution free.  In particular, its
probability comparison is obtained from the literal same-noise coupling,
rather than from an input whose conclusion is the desired event inclusion.
-/

open AppliedModelingLib Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-- The literal three-candidate source score at accuracy `theta`. -/
noncomputable def appendixCSourceScore
    (value noise : Candidate 1 -> ℝ) (theta : ℝ) (i : Candidate 1) : ℝ :=
  value i + noise i / theta

/-- The literal source ranking induced by the three RUM scores. -/
noncomputable def appendixCSourceRank
    (value noise : Candidate 1 -> ℝ) (theta : ℝ) : Ranking 1 :=
  rankByScore (appendixCSourceScore value noise theta)

/--
Increasing accuracy from `thetaH` to `thetaA` is exactly the source-paper
contraction of the scores observed at `thetaH`.
-/
theorem appendixC_source_score_eq_contract_score
    {thetaA thetaH : ℝ} (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH)
    (value noise : Candidate 1 -> ℝ) (i : Candidate 1) :
    appendixCSourceScore value noise thetaA i =
      rumContractScore (thetaH / thetaA) (value i)
        (appendixCSourceScore value noise thetaH i) := by
  unfold appendixCSourceScore rumContractScore AppliedModelingLib.Probability.rumContractScore
  field_simp [ne_of_gt hthetaA, ne_of_gt hthetaH]
  ring

/--
The literal pointwise coupling behind Appendix C, Lemma 2.  If the bottom
candidate is selected from the higher-accuracy RUM score vector, it is also
selected from the lower-accuracy vector built from the same innovations.
-/
theorem appendixC_source_bottom_first_high_accuracy_imp_low_accuracy
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (noise : Candidate 1 -> ℝ) :
    firstChoice
        (appendixCSourceRank (threeCandidateValueProfile x1 x2 x3) noise thetaA) =
          (2 : Candidate 1) ->
      firstChoice
        (appendixCSourceRank (threeCandidateValueProfile x1 x2 x3) noise thetaH) =
          (2 : Candidate 1) := by
  intro hbetter
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  let t : ℝ := thetaH / thetaA
  let raw : Candidate 1 -> ℝ :=
    appendixCSourceScore (threeCandidateValueProfile x1 x2 x3) noise thetaH
  let contracted : Candidate 1 -> ℝ :=
    fun i => rumContractScore t (threeCandidateValueProfile x1 x2 x3 i) (raw i)
  have ht0 : 0 <= t := le_of_lt (div_pos hthetaH hthetaA)
  have htlt1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hthetaA).mpr hthetaHA
  have hcontract (i : Candidate 1) :
      appendixCSourceScore (threeCandidateValueProfile x1 x2 x3) noise thetaA i =
        contracted i := by
    simp only [contracted, raw, t]
    exact appendixC_source_score_eq_contract_score
      hthetaA hthetaH (threeCandidateValueProfile x1 x2 x3) noise i
  have hbetter' : firstChoice (rankByScore contracted) = (2 : Candidate 1) := by
    rw [<- show appendixCSourceScore (threeCandidateValueProfile x1 x2 x3)
        noise thetaA = contracted by
          funext i
          exact hcontract i]
    exact hbetter
  have hbottomContract :
      rum3BottomFirstByScores
        (rumContractScore t x1 (raw (0 : Candidate 1)))
        (rumContractScore t x2 (raw (1 : Candidate 1)))
        (rumContractScore t x3 (raw (2 : Candidate 1))) := by
    have hrank0 :
        rankOf (rankByScore contracted) (2 : Candidate 1) <=
          rankOf (rankByScore contracted) (0 : Candidate 1) := by
      calc
        rankOf (rankByScore contracted) (2 : Candidate 1) =
            rankOf (rankByScore contracted) (firstChoice (rankByScore contracted)) := by
              rw [hbetter']
        _ = 0 := rankOf_firstChoice (rankByScore contracted)
        _ <= rankOf (rankByScore contracted) (0 : Candidate 1) := bot_le
    have hrank1 :
        rankOf (rankByScore contracted) (2 : Candidate 1) <=
          rankOf (rankByScore contracted) (1 : Candidate 1) := by
      calc
        rankOf (rankByScore contracted) (2 : Candidate 1) =
            rankOf (rankByScore contracted) (firstChoice (rankByScore contracted)) := by
              rw [hbetter']
        _ = 0 := rankOf_firstChoice (rankByScore contracted)
        _ <= rankOf (rankByScore contracted) (1 : Candidate 1) := bot_le
    have hc0 : contracted (0 : Candidate 1) <= contracted (2 : Candidate 1) :=
      rankByScore_weaklyOrdersScores contracted hrank0
    have hc1 : contracted (1 : Candidate 1) <= contracted (2 : Candidate 1) :=
      rankByScore_weaklyOrdersScores contracted hrank1
    simpa [contracted, raw, threeCandidateValueProfile] using ⟨hc0, hc1⟩
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  rcases rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
      ht0 htlt1 hx13 hx23 hbottomContract.1 hbottomContract.2 with
    ⟨hraw0, hraw1⟩
  change firstChoice (rankByScore raw) = (2 : Candidate 1)
  rw [<- bestInSet_univ]
  apply bestInSet_rankByScore_univ_eq_of_strict_top
  intro d hd
  fin_cases d
  · exact hraw0
  · exact hraw1
  · exact (hd rfl).elim

/--
Appendix C, Lemma 2 at the literal score-PMF surface.  The innovation law can
be arbitrary here: the proof uses only the same-noise source construction and
the displayed strict value/accuracy order.
-/
theorem appendixC_source_lemma2_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (mu : Measure (Candidate 1 -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        (paper_appendixA_scaledNoiseRankingPMF mu
          (threeCandidateValueProfile x1 x2 x3) thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb
        (paper_appendixA_scaledNoiseRankingPMF mu
          (threeCandidateValueProfile x1 x2 x3) thetaH)
        (2 : Candidate 1) := by
  let rankA : (Candidate 1 -> ℝ) -> Ranking 1 := fun noise =>
    rankByScore (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / thetaA)
  let rankH : (Candidate 1 -> ℝ) -> Ranking 1 := fun noise =>
    rankByScore (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / thetaH)
  have hrankA : Measurable rankA := by
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 -> ℝ => noise)
      (fun i => measurable_pi_apply i)
      (threeCandidateValueProfile x1 x2 x3) thetaA
  have hrankH : Measurable rankH := by
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 -> ℝ => noise)
      (fun i => measurable_pi_apply i)
      (threeCandidateValueProfile x1 x2 x3) thetaH
  change firstChoiceProb
      (rankingPMFOfMeasure mu rankA hrankA)
      (2 : Candidate 1) <=
    firstChoiceProb
      (rankingPMFOfMeasure mu rankH hrankH)
      (2 : Candidate 1)
  change AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
      (rankingPMFOfMeasure mu rankA hrankA) (2 : Candidate 1) <=
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
      (rankingPMFOfMeasure mu rankH hrankH) (2 : Candidate 1)
  rw [AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure]
  refine measureProb_le_of_measure_le mu _ _ (measure_mono ?_)
  intro noise hnoise
  exact (appendixC_source_bottom_first_high_accuracy_imp_low_accuracy
    hthetaH hthetaHA hx12 hx23 noise) hnoise.symm |>.symm

/--
Appendix C, Lemma 2 for the literal iid standard-Gaussian RUM construction.
The theorem is stated at the source family rather than at its named
score-measure target.
-/
theorem appendixC_source_lemma2_gaussian_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (2 : Candidate 1) := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw theorem2GaussianBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      theorem2GaussianBaseDensity theorem2GaussianBase_w11Regularity.normalized
  simpa [theorem2GaussianScaledNoiseFamily,
    w11CorrectedScaledNoiseFamily_dist_eq_scaledNoiseRankingPMF] using
    (appendixC_source_lemma2_bottom_first_probability
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
      hthetaH hthetaHA hx12 hx23)

/--
Appendix C, Lemma 2 for the literal iid unit-variance Laplace RUM
construction.
-/
theorem appendixC_source_lemma2_laplace_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (2 : Candidate 1) := by
  letI : IsProbabilityMeasure
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      sourceUnitVarianceLaplaceBaseDensity
      sourceUnitVarianceLaplace_w11Regularity.normalized
  simpa [sourceUnitVarianceLaplaceScaledNoiseFamily,
    w11CorrectedScaledNoiseFamily_dist_eq_scaledNoiseRankingPMF] using
    (appendixC_source_lemma2_bottom_first_probability
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
      hthetaH hthetaHA hx12 hx23)

/--
The density-level `swapi` certificate used by Appendix C, Lemma 3.  Every
input is an analytic fact about the displayed iid score-density experiment:
normalization, positivity, weak well-ordering, and strict order of the values.
There is no transition-mass or coupling conclusion among the hypotheses.
-/
theorem appendixC_source_score_density_delta_certificate_of_contraction
    (f : ℝ -> ℝ) (x1 x2 x3 t : ℝ)
    (hfmeas : Measurable f)
    (hnorm :
      ∫⁻ omega,
          (rum3ScoreDensityENN f x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            omega ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (hf : WeaklyWellOrderedNoise f) (hpos : ∀ z : ℝ, 0 < f z)
    (ht0 : 0 <= t) (ht1 : t <= 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3DeltaCertificate
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)) := by
  let D : paper_theorem6_scoreSpace -> ENNReal :=
    rum3ScoreDensityENN f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
  have hD : Measurable D :=
    paper_theorem6_scoreDensity_measurable hfmeas x1 x2 x3
  haveI : IsProbabilityMeasure
      ((volume : Measure paper_theorem6_scoreSpace).withDensity D) :=
    paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 hnorm
  let better : paper_theorem6_scoreSpace -> Ranking 1 :=
    rum3ContractRankByScoreFns t x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
  let worse : paper_theorem6_scoreSpace -> Ranking 1 :=
    rum3RankByScoreFns
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
  have hbetter : Measurable better :=
    rum3ContractRankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
      t x1 x2 x3
  have hworse : Measurable worse :=
    rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
  have hbetterEvent (p : Ranking 1 -> Prop) :
      MeasurableSet {omega | p (better omega)} := by
    simpa only [Set.preimage_setOf_eq] using
      hbetter (show MeasurableSet {pi : Ranking 1 | p pi}
        from MeasurableSet.of_discrete)
  have hworseEvent (p : Ranking 1 -> Prop) :
      MeasurableSet {omega | p (worse omega)} := by
    simpa only [Set.preimage_setOf_eq] using
      hworse (show MeasurableSet {pi : Ranking 1 | p pi}
        from MeasurableSet.of_discrete)
  have hbetterTopMeas : MeasurableSet
      {omega | (0 : Candidate 1) = firstChoice (better omega)} :=
    hbetterEvent (fun pi => (0 : Candidate 1) = firstChoice pi)
  have hworseTopMeas : MeasurableSet
      {omega | (0 : Candidate 1) = firstChoice (worse omega)} :=
    hworseEvent (fun pi => (0 : Candidate 1) = firstChoice pi)
  have hworseBottomMeas : MeasurableSet
      {omega | (2 : Candidate 1) = firstChoice (worse omega)} :=
    hworseEvent (fun pi => (2 : Candidate 1) = firstChoice pi)
  have hbetterMiddleMeas : MeasurableSet
      {omega | (1 : Candidate 1) = firstChoice (better omega)} :=
    hbetterEvent (fun pi => (1 : Candidate 1) = firstChoice pi)
  have hdeltaSourceMeas : MeasurableSet
      {omega | (2 : Candidate 1) = firstChoice (worse omega) /\
        (1 : Candidate 1) = firstChoice (better omega)} :=
    hworseBottomMeas.inter hbetterMiddleMeas
  have hdeltaTargetMeas : MeasurableSet
      {omega | (2 : Candidate 1) = firstChoice (worse omega) /\
        (0 : Candidate 1) = firstChoice (better omega)} :=
    hworseBottomMeas.inter hbetterTopMeas
  have hcorrectedBase :
      (volume : Measure paper_theorem6_scoreSpace)
        ({omega | (0 : Candidate 1) = firstChoice (better omega)} ∩
          {omega | (0 : Candidate 1) = firstChoice (worse omega)}ᶜ) ≠ 0 := by
    simpa [better, worse, paper_theorem6_scoreSpace,
      paper_theorem6_score1, paper_theorem6_score2, paper_theorem6_score3] using
      rum3Score_correctedTop_volume_ne_zero_of_t_lt_one
        ht0 ht1 htlt1 hx12 hx23
  have hcorrectedPos :
      (volume : Measure paper_theorem6_scoreSpace).withDensity D
        ({omega | (0 : Candidate 1) = firstChoice (better omega)} ∩
          {omega | (0 : Candidate 1) = firstChoice (worse omega)}ᶜ) ≠ 0 :=
    paper_theorem6_scoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
      (volume : Measure paper_theorem6_scoreSpace) x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      hD hpos (hbetterTopMeas.inter hworseTopMeas.compl) hcorrectedBase
  simpa [D, better, worse, paper_theorem6_normalizedScoreRankingPMF] using
    (rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts_of_t_lt_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3 t
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      paper_theorem6_scoreSwap12
      hbetter hworse hbetterTopMeas hworseTopMeas
      hdeltaSourceMeas hdeltaTargetMeas
      paper_theorem6_scoreSwap12_measurePreserving_volume hf hpos
      (fun omega => rfl) (fun omega => rfl) (fun omega => rfl)
      ht0 ht1 htlt1 hx12 hx23 hcorrectedPos)

/--
Appendix C, Lemma 3 at the literal iid unit-variance Laplace source surface.
The proof derives the contraction and the `swapi` density comparison under the
source score law, then transports both marginals back to
`x_i + epsilon_i / theta`.

The source prints Lemma 3 for arbitrary `n` and every `i > 1`; this is only
the three-candidate, middle-candidate (`i = 2`) specialization used by Theorem 6.
-/
theorem appendixC_source_lemma3_laplace_middle_delta_le_top_delta
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (1 : Candidate 1) -
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (1 : Candidate 1) <=
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (0 : Candidate 1) -
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (0 : Candidate 1) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  let lam : ℝ := Real.sqrt 2 * thetaH
  let t : ℝ := thetaH / thetaA
  have hlam : 0 < lam := by
    dsimp [lam]
    exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaH
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hthetaH hthetaA
  have ht0 : 0 <= t := le_of_lt ht
  have htlt1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hthetaA).mpr hthetaHA
  have ht1 : t <= 1 := le_of_lt htlt1
  let hnorm := paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
    (lam := lam) hlam x1 x2 x3
  have hdeltaScore := appendixC_source_score_density_delta_certificate_of_contraction
    (theorem7LaplacePDF lam 0) x1 x2 x3 t
    (theorem7LaplacePDF_measurable lam 0) hnorm
    (theorem7LaplacePDF_zero_weaklyWellOrdered hlam.le)
    (fun z => theorem7LaplacePDF_pos (lam := lam) (μ := 0) (x := z) hlam)
    ht0 ht1 htlt1 hx12 hx23
  have hdeltaDefinition2 : RUM3DeltaCertificate
      (theorem7LaplacianDefinition2ContractRankingPMF lam t x1 x2 x3 hlam)
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) := by
    rw [<- paper_theorem6_laplacian_scoreSpace_contractRankingPMF_eq_definition2
      hlam x1 x2 x3 t,
      <- paper_theorem6_laplacian_scoreSpace_rawRankingPMF_eq_definition2
      hlam x1 x2 x3]
    exact hdeltaScore
  have hrate : lam / t = Real.sqrt 2 * thetaA := by
    dsimp [lam, t]
    field_simp [ne_of_gt hthetaH, ne_of_gt hthetaA]
  have hdeltaRate : RUM3DeltaCertificate
      (theorem7LaplacianDefinition2RankingPMF
        (Real.sqrt 2 * thetaA) x1 x2 x3
        (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaA))
      (theorem7LaplacianDefinition2RankingPMF
        (Real.sqrt 2 * thetaH) x1 x2 x3
        (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaH)) := by
    rw [theorem7LaplacianDefinition2RankingPMF_contract_eq hlam ht] at hdeltaDefinition2
    simpa [lam, hrate] using hdeltaDefinition2
  have hsourceA :
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA =
        theorem7LaplacianDefinition2RankingPMF
          (Real.sqrt 2 * thetaA) x1 x2 x3
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaA) := by
    calc
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA =
          sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaA x1 x2 x3 := by
            simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
              sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw hthetaA
      _ = laplaceThreeCandidateRankingLaw (Real.sqrt 2 * thetaA) x1 x2 x3 := rfl
      _ = theorem7LaplacianDefinition2RankingPMF
          (Real.sqrt 2 * thetaA) x1 x2 x3
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaA) :=
        laplaceThreeCandidateRankingLaw_eq_of_pos
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaA)
  have hsourceH :
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH =
        theorem7LaplacianDefinition2RankingPMF
          (Real.sqrt 2 * thetaH) x1 x2 x3
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaH) := by
    calc
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH =
          sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaH x1 x2 x3 := by
            simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
              sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw hthetaH
      _ = laplaceThreeCandidateRankingLaw (Real.sqrt 2 * thetaH) x1 x2 x3 := rfl
      _ = theorem7LaplacianDefinition2RankingPMF
          (Real.sqrt 2 * thetaH) x1 x2 x3
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaH) :=
        laplaceThreeCandidateRankingLaw_eq_of_pos
          (mul_pos (Real.sqrt_pos.2 (by norm_num)) hthetaH)
  rw [hsourceA, hsourceH]
  exact hdeltaRate.delta_middle_le_top

/--
Appendix C, Lemma 3 at the literal iid standard-Gaussian source surface.
The proof first transports the standard-deviation score law by a positive
canonical scaling, proves the density-level `swapi` certificate there, and
then transports the two source accuracies back without changing rankings.

The source prints Lemma 3 for arbitrary `n` and every `i > 1`; this is only
the three-candidate, middle-candidate (`i = 2`) specialization used by Theorem 6.
-/
theorem appendixC_source_lemma3_gaussian_middle_delta_le_top_delta
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (1 : Candidate 1) -
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (1 : Candidate 1) <=
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (0 : Candidate 1) -
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (0 : Candidate 1) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  let sigma : ℝ := 1 / thetaH
  let t : ℝ := thetaH / thetaA
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact one_div_pos.mpr hthetaH
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hthetaH hthetaA
  have ht0 : 0 <= t := le_of_lt ht
  have htlt1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hthetaA).mpr hthetaHA
  have ht1 : t <= 1 := le_of_lt htlt1
  let c : ℝ := theorem8GaussianCanonicalScale sigma
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hsigma
  have hcx12 : c * x2 < c * x1 := mul_lt_mul_of_pos_left hx12 hc
  have hcx23 : c * x3 < c * x2 := mul_lt_mul_of_pos_left hx23 hc
  let hnorm := paper_theorem6_gaussian_scoreDensity_lintegral_eq_one
    (c * x1) (c * x2) (c * x3)
  have hdeltaScore := appendixC_source_score_density_delta_certificate_of_contraction
    (theorem8GaussianPDF 0) (c * x1) (c * x2) (c * x3) t
    (theorem8GaussianPDF_measurable 0) hnorm
    theorem8GaussianPDF_zero_strictlyWellOrdered.weak
    (fun z => theorem8GaussianPDF_pos 0 z)
    ht0 ht1 htlt1 hcx12 hcx23
  have hdeltaCanonical : RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure (c * x1) (c * x2) (c * x3))
        (rum3ContractRankByScoreFns t (c * x1) (c * x2) (c * x3)
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3ContractRankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable
          t (c * x1) (c * x2) (c * x3)))
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure (c * x1) (c * x2) (c * x3))
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) := by
    rw [<- paper_theorem6_gaussian_scoreSpace_contractRankingPMF_eq_definition2
      (c * x1) (c * x2) (c * x3) t,
      <- paper_theorem6_gaussian_scoreSpace_rawRankingPMF_eq_definition2
      (c * x1) (c * x2) (c * x3)]
    exact hdeltaScore
  have hdeltaStd : RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
        (rum3ContractRankByScoreFns t x1 x2 x3
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3ContractRankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable
          t x1 x2 x3))
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) := by
    rw [theorem8GaussianDefinition2ContractRankingPMFStd_canonical_eq hsigma t,
      theorem8GaussianDefinition2RankingPMFStd_canonical_eq hsigma]
    simpa [c] using hdeltaCanonical
  have hscale : t * sigma = 1 / thetaA := by
    dsimp [t, sigma]
    field_simp [ne_of_gt hthetaH, ne_of_gt hthetaA]
  have hsourceA :
      (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA =
        rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
          (rum3ContractRankByScoreFns t x1 x2 x3
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3ContractRankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable
            t x1 x2 x3) := by
    calc
      (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA =
          gaussianThreeCandidateRankingLaw thetaA x1 x2 x3 :=
        theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw hthetaA
      _ = rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / thetaA) x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable) := rfl
      _ = rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd (t * sigma) x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable) := by
              rw [hscale]
      _ = rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
          (rum3ContractRankByScoreFns t x1 x2 x3
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3ContractRankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable
            t x1 x2 x3) :=
        (theorem8GaussianDefinition2RankingPMFStd_contract_eq t sigma x1 x2 x3).symm
  have hsourceH :
      (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH =
        rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable) := by
    calc
      (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH =
          gaussianThreeCandidateRankingLaw thetaH x1 x2 x3 :=
        theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw hthetaH
      _ = rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / thetaH) x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable) := rfl
      _ = rumRankingPMFOfMeasure
          (theorem8GaussianDefinition2ScoreMeasureStd sigma x1 x2 x3)
          (rum3RankByScoreFns
            theorem8GaussianDefinition2Score1
            theorem8GaussianDefinition2Score2
            theorem8GaussianDefinition2Score3)
          (rum3RankByScoreFns_measurable
            theorem8GaussianDefinition2Score1_measurable
            theorem8GaussianDefinition2Score2_measurable
            theorem8GaussianDefinition2Score3_measurable) := by
              rw [show 1 / thetaH = sigma by rfl]
  rw [hsourceA, hsourceH]
  exact hdeltaStd.delta_middle_le_top

/--
Theorem 6 for the literal iid standard-Gaussian source RUM.  The two PMFs are
the source rankings of `x_i + epsilon_i / theta`; their equality to the
Gaussian score laws is proved by an explicit product-law transport.
-/
theorem appendixC_source_theorem6_gaussian_prefers_weaker_competition
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
      (threeCandidateValueProfile x1 x2 x3) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  rw [theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw hthetaA,
    theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw hthetaH]
  exact gaussianThreeCandidate_prefersWeaker hthetaH hthetaHA hx12 hx23

/--
Theorem 6 for the literal iid unit-variance Laplace source RUM.  The
source-to-score transport retains the source rate `sqrt 2 * theta` explicitly.
-/
theorem appendixC_source_theorem6_laplace_prefers_weaker_competition
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
      (threeCandidateValueProfile x1 x2 x3) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  rw [show (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA =
      sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaA x1 x2 x3 by
        simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
          sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw hthetaA,
    show (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH =
      sourceUnitVarianceLaplaceThreeCandidateRankingLaw thetaH x1 x2 x3 by
        simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
          sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw hthetaH]
  exact sourceUnitVarianceLaplaceThreeCandidate_prefersWeaker
    hthetaH hthetaHA hx12 hx23

end KR21Monoculture
