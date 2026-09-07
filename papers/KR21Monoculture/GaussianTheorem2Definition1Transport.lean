import KR21Monoculture.Theorem2Definition1SourceFamilies
import KR21Monoculture.AppendixBFiniteSetDefinition1
import KR21Monoculture.OuterRUMSourceConcentration
import KR21Monoculture.OuterRUMSourceMonotonicity

/-!
# Gaussian source-law transport for KR21 Theorem 2 Definition 1

This module connects the corrected literal iid standard-Gaussian scaled-noise
family to the separately named three-score Gaussian ranking law.  The bridge
is measure-theoretic and does not rely on matching declaration names.
-/

open AppliedModelingLib Filter MeasureTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

theorem theorem2GaussianBaseDensity_eq_standardGaussianPDF (z : ℝ) :
    theorem2GaussianBaseDensity z =
      ProbabilityTheory.gaussianPDFReal 0 1 z := by
  simp [theorem2GaussianBaseDensity, finiteGaussianMixtureDensity,
    appendixBGaussianVariance]
  congr 2

theorem theorem2GaussianBaseNoiseLaw_eq_standardGaussian :
    w11BaseNoiseLaw theorem2GaussianBaseDensity =
      ProbabilityTheory.gaussianReal 0 1 := by
  unfold w11BaseNoiseLaw
  rw [show (fun z => ENNReal.ofReal (theorem2GaussianBaseDensity z)) =
      (fun z => ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal 0 1 z)) by
        funext z
        rw [theorem2GaussianBaseDensity_eq_standardGaussianPDF]]
  symm
  exact ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num)

/-- Reindexing a literal right-associated iid standard-Gaussian triple gives
the finite candidate-indexed source-noise law of the corrected family. -/
theorem theorem2GaussianStandardTriple_to_candidateNoise_measurePreserving :
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity) := by
  letI : IsFiniteMeasure (ProbabilityTheory.gaussianReal 0 1) := ⟨by simp⟩
  simpa only [w11CandidateNoiseLaw,
    theorem2GaussianBaseNoiseLaw_eq_standardGaussian] using
    (measurePreserving_rightTripleToCandidateMeasurableEquiv
      (ProbabilityTheory.gaussianReal 0 1))

/-- Add the three literal `noise / theta` perturbations to the displayed
three-candidate values, retaining the named score-space association. -/
noncomputable def theorem2GaussianSourceToNamedScoreMap
    (theta x1 x2 x3 : ℝ) : Theorem8GaussianDefinition2ScoreSpace →
      Theorem8GaussianDefinition2ScoreSpace :=
  fun z =>
    (x1 + z.1 / theta, (x2 + z.2.1 / theta, x3 + z.2.2 / theta))

theorem measurable_theorem2GaussianSourceToNamedScoreMap
    (theta x1 x2 x3 : ℝ) :
    Measurable (theorem2GaussianSourceToNamedScoreMap theta x1 x2 x3) := by
  unfold theorem2GaussianSourceToNamedScoreMap
  fun_prop

private theorem gaussianReal_zero_one_map_add_div_eq
    (theta x : ℝ) :
    (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => x + z / theta) =
      ProbabilityTheory.gaussianReal x
        (theorem8GaussianVarianceFromStd (1 / theta)) := by
  calc
    (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => x + z / theta) =
        (ProbabilityTheory.gaussianReal 0 1).map
          (fun z : ℝ => x + (1 / theta) * z) := by
      congr 1
      funext z
      ring
    _ = ProbabilityTheory.gaussianReal x
          (appendixBGaussianVariance (1 / theta)) :=
      gaussianReal_map_center_add_scaled_standard x (1 / theta)
    _ = ProbabilityTheory.gaussianReal x
          (theorem8GaussianVarianceFromStd (1 / theta)) := by
      congr 1

/-- The explicit score map transports the iid standard-Gaussian source triple
to the exact arbitrary-standard-deviation score law used by the named
Gaussian ranking PMF. -/
theorem theorem2GaussianSourceToNamedScoreMap_measurePreserving
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    MeasurePreserving
      (theorem2GaussianSourceToNamedScoreMap theta x1 x2 x3)
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))
      (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3) := by
  refine ⟨measurable_theorem2GaussianSourceToNamedScoreMap theta x1 x2 x3, ?_⟩
  let mu0 : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let f1 : ℝ → ℝ := fun z => x1 + z / theta
  let f2 : ℝ → ℝ := fun z => x2 + z / theta
  let f3 : ℝ → ℝ := fun z => x3 + z / theta
  have hf1 : Measurable f1 := by
    dsimp [f1]
    fun_prop
  have hf2 : Measurable f2 := by
    dsimp [f2]
    fun_prop
  have hf3 : Measurable f3 := by
    dsimp [f3]
    fun_prop
  have h1 : mu0.map f1 = ProbabilityTheory.gaussianReal x1
      (theorem8GaussianVarianceFromStd (1 / theta)) := by
    exact gaussianReal_zero_one_map_add_div_eq theta x1
  have h2 : mu0.map f2 = ProbabilityTheory.gaussianReal x2
      (theorem8GaussianVarianceFromStd (1 / theta)) := by
    exact gaussianReal_zero_one_map_add_div_eq theta x2
  have h3 : mu0.map f3 = ProbabilityTheory.gaussianReal x3
      (theorem8GaussianVarianceFromStd (1 / theta)) := by
    exact gaussianReal_zero_one_map_add_div_eq theta x3
  have hpair :
      (mu0.prod mu0).map (Prod.map f2 f3) =
        (mu0.map f2).prod (mu0.map f3) := by
    exact (Measure.map_prod_map mu0 mu0 hf2 hf3).symm
  have htriple :
      (mu0.prod (mu0.prod mu0)).map (Prod.map f1 (Prod.map f2 f3)) =
        (mu0.map f1).prod ((mu0.prod mu0).map (Prod.map f2 f3)) := by
    exact (Measure.map_prod_map mu0 (mu0.prod mu0) hf1 (hf2.prodMap hf3)).symm
  change (mu0.prod (mu0.prod mu0)).map (Prod.map f1 (Prod.map f2 f3)) = _
  rw [htriple, hpair, h1, h2, h3]
  rfl

/-- The named Gaussian score law as a map from the corrected family's literal
candidate-indexed source-noise vector. -/
noncomputable def theorem2GaussianCandidateNoiseToNamedScoreMap
    (theta x1 x2 x3 : ℝ) : (Candidate 1 → ℝ) →
      Theorem8GaussianDefinition2ScoreSpace :=
  theorem2GaussianSourceToNamedScoreMap theta x1 x2 x3 ∘
    (rightTripleToCandidateMeasurableEquiv ℝ).symm

theorem theorem2GaussianCandidateNoiseToNamedScoreMap_measurePreserving
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    MeasurePreserving
      (theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3)
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
      (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3) := by
  exact
    (theorem2GaussianSourceToNamedScoreMap_measurePreserving htheta).comp
      (MeasurePreserving.symm (rightTripleToCandidateMeasurableEquiv ℝ)
        theorem2GaussianStandardTriple_to_candidateNoise_measurePreserving)

/-! ## The two three-candidate ranking encodings -/

private theorem rankByScore_eq_of_strict_ranking_order
    {n : ℕ} (score : Candidate n → ℝ) (pi : Ranking n)
    (hstrict : ∀ i j : Candidate n, i < j → score (pi j) < score (pi i)) :
    rankByScore score = pi := by
  have hsort : pi = Tuple.sort (fun c : Candidate n => -score c) := by
    refine (Tuple.eq_sort_iff
      (f := fun c : Candidate n => -score c) (σ := pi)).mpr ?_
    constructor
    · intro i j hij
      rcases lt_or_eq_of_le hij with hij | rfl
      · have h := hstrict i j hij
        dsimp [Function.comp_def]
        linarith
      · rfl
    · intro i j hij heq
      exfalso
      have h := hstrict i j hij
      change -score (pi i) = -score (pi j) at heq
      linarith
  simpa [rankByScore] using hsort.symm

/-- Off the score-tie hyperplanes, the generic finite sorter and the named
three-score map choose the same ranking.  This is needed because their total
tie conventions are implemented independently; Gaussian score ties have zero
measure below. -/
private theorem rankByScore_three_eq_rum3RankByScores_of_noTies
    (s1 s2 s3 : ℝ)
    (h12 : s1 ≠ s2) (h13 : s1 ≠ s3) (h23 : s2 ≠ s3) :
    rankByScore (threeCandidateValueProfile s1 s2 s3) =
      rum3RankByScores s1 s2 s3 := by
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · by_cases h32 : s3 ≤ s2
    · have h21 : s2 < s1 := lt_of_le_of_ne h0.1 h12.symm
      have h32' : s3 < s2 := lt_of_le_of_ne h32 h23.symm
      have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
          rum3Ranking012 := by
        apply rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [threeCandidateValueProfile, rum3Ranking012] <;> linarith
      rw [hrank]
      exact (rum3RankByScores_eq012_of_adjacent_order h0.1 h32).symm
    · have h23' : s2 < s3 := lt_of_not_ge h32
      have h31 : s3 < s1 := lt_of_le_of_ne h0.2 h13.symm
      have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
          rum3Ranking021 := by
        apply rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [threeCandidateValueProfile, rum3Ranking021] <;> linarith
      rw [hrank]
      symm
      simp only [KR21Monoculture.rum3RankByScores,
        AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
        KR21Monoculture.rum3Ranking021,
        dif_pos h0, if_neg h32]
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · by_cases h31 : s3 ≤ s1
      · have h13' : s1 < s2 := h1.1
        have h31' : s3 < s1 := lt_of_le_of_ne h31 h13.symm
        have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
            rum3Ranking102 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking102] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking102,
          dif_neg h0, dif_pos h1, if_pos h31]
      · have h13' : s1 < s2 := h1.1
        have h32' : s3 < s2 := lt_of_le_of_ne h1.2 h23.symm
        have h13 : s1 < s3 := lt_of_not_ge h31
        have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
            rum3Ranking120 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking120] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking120,
          dif_neg h0, dif_pos h1, if_neg h31]
    · by_cases h21 : s2 ≤ s1
      · have h21' : s2 < s1 := lt_of_le_of_ne h21 h12.symm
        have h13 : s1 < s3 := by
          apply lt_of_not_ge
          intro h31
          exact h0 ⟨h21, h31⟩
        have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
            rum3Ranking201 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking201] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking201,
          dif_neg h0, dif_neg h1, if_pos h21]
      · have h12' : s1 < s2 := lt_of_not_ge h21
        have h23' : s2 < s3 := by
          apply lt_of_not_ge
          intro h32
          exact h1 ⟨h12', h32⟩
        have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
            rum3Ranking210 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking210] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking210,
          dif_neg h0, dif_neg h1, if_neg h21]

/-- The candidate-noise-to-score transport has the advertised first score
coordinate. -/
theorem theorem2GaussianCandidateNoiseToNamedScoreMap_score1
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem8GaussianDefinition2Score1
      (theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x1 + noise 0 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h0 := congrFun he (0 : Candidate 1)
  change (e.symm noise).1 = noise 0 at h0
  simpa [theorem2GaussianCandidateNoiseToNamedScoreMap,
    theorem2GaussianSourceToNamedScoreMap,
    theorem8GaussianDefinition2Score1, e] using
      congrArg (fun z : ℝ => x1 + z / theta) h0

/-- The candidate-noise-to-score transport has the advertised second score
coordinate. -/
theorem theorem2GaussianCandidateNoiseToNamedScoreMap_score2
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem8GaussianDefinition2Score2
      (theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x2 + noise 1 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h1 := congrFun he (1 : Candidate 1)
  change (e.symm noise).2.1 = noise 1 at h1
  simpa [theorem2GaussianCandidateNoiseToNamedScoreMap,
    theorem2GaussianSourceToNamedScoreMap,
    theorem8GaussianDefinition2Score2, e] using
      congrArg (fun z : ℝ => x2 + z / theta) h1

/-- The candidate-noise-to-score transport has the advertised third score
coordinate. -/
theorem theorem2GaussianCandidateNoiseToNamedScoreMap_score3
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem8GaussianDefinition2Score3
      (theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x3 + noise 2 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h2 := congrFun he (2 : Candidate 1)
  change (e.symm noise).2.2 = noise 2 at h2
  simpa [theorem2GaussianCandidateNoiseToNamedScoreMap,
    theorem2GaussianSourceToNamedScoreMap,
    theorem8GaussianDefinition2Score3, e] using
      congrArg (fun z : ℝ => x3 + z / theta) h2

private theorem theorem2GaussianCandidateNoise_rank_eq_namedRank_of_noTies
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ)
    (h12 : x1 + noise 0 / theta ≠ x2 + noise 1 / theta)
    (h13 : x1 + noise 0 / theta ≠ x3 + noise 2 / theta)
    (h23 : x2 + noise 1 / theta ≠ x3 + noise 2 / theta) :
    rankByScore (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta) =
      rum3RankByScoreFns theorem8GaussianDefinition2Score1
        theorem8GaussianDefinition2Score2 theorem8GaussianDefinition2Score3
        (theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) := by
  let s1 := x1 + noise 0 / theta
  let s2 := x2 + noise 1 / theta
  let s3 := x3 + noise 2 / theta
  have hscores :
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta) =
        threeCandidateValueProfile s1 s2 s3 := by
    funext i
    fin_cases i <;> simp [s1, s2, s3, threeCandidateValueProfile]
  rw [hscores, rankByScore_three_eq_rum3RankByScores_of_noTies s1 s2 s3]
  · simp only [rum3RankByScoreFns]
    rw [theorem2GaussianCandidateNoiseToNamedScoreMap_score1,
      theorem2GaussianCandidateNoiseToNamedScoreMap_score2,
      theorem2GaussianCandidateNoiseToNamedScoreMap_score3]
  · simpa [s1, s2, s3] using h12
  · simpa [s1, s2, s3] using h13
  · simpa [s1, s2, s3] using h23

/-- A measure transport also preserves a finite ranking PMF when the ranking
maps intertwine almost everywhere.  The a.e. form is essential here because
the two total ranking encodings need only agree away from Gaussian score ties. -/
private theorem rankingPMFOfMeasure_eq_of_measurePreserving_ae
    {n : ℕ} {Omega Omega' : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (nu : Measure Omega') [IsProbabilityMeasure nu]
    (e : Omega → Omega') (he : MeasurePreserving e mu nu)
    (rank : Omega → Ranking n) (hrank : Measurable rank)
    (rank' : Omega' → Ranking n) (hrank' : Measurable rank')
    (hintertwine : ∀ᵐ omega ∂mu, rank omega = rank' (e omega)) :
    rankingPMFOfMeasure mu rank hrank = rankingPMFOfMeasure nu rank' hrank' := by
  classical
  apply PMF.ext
  intro pi
  apply (ENNReal.toReal_eq_toReal_iff'
    ((rankingPMFOfMeasure mu rank hrank).apply_ne_top pi)
    ((rankingPMFOfMeasure nu rank' hrank').apply_ne_top pi)).mp
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure mu rank hrank) pi]
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure nu rank' hrank') pi]
  rw [rankingPMFOfMeasure_eventProb mu rank hrank
    (fun rho : Ranking n => rho = pi)]
  rw [rankingPMFOfMeasure_eventProb nu rank' hrank'
    (fun rho : Ranking n => rho = pi)]
  trans AppliedModelingLib.measureProb mu (fun omega => rank' (e omega) = pi)
  · unfold AppliedModelingLib.measureProb
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hintertwine] with omega homega
    apply propext
    change (rank omega = pi) ↔ (rank' (e omega) = pi)
    rw [homega]
  · exact AppliedModelingLib.measureProb_preimage_of_measurePreserving
      e he (fun omega' : Omega' => rank' omega' = pi)
      (by
        simpa only [Set.preimage_setOf_eq] using
          hrank' (show MeasurableSet {rho : Ranking n | rho = pi}
            from MeasurableSet.of_discrete))

/-- At every positive source accuracy, the corrected literal iid
standard-Gaussian scaled-noise family induces exactly the named Gaussian
three-candidate ranking law.  The proof supplies the actual product-law
transport and uses the named Gaussian no-tie fact only to reconcile the two
total ranking encodings off a null set. -/
theorem theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
      gaussianThreeCandidateRankingLaw theta x1 x2 x3 := by
  let regularity := theorem2GaussianBase_w11Regularity
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw theorem2GaussianBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      theorem2GaussianBaseDensity regularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
      (threeCandidateValueProfile x1 x2 x3) theta =
      rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)
  let transport := theorem2GaussianCandidateNoiseToNamedScoreMap theta x1 x2 x3
  have htransport : MeasurePreserving transport
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
      (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3) :=
    theorem2GaussianCandidateNoiseToNamedScoreMap_measurePreserving htheta
  refine rankingPMFOfMeasure_eq_of_measurePreserving_ae
    (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
    (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3)
    transport htransport
    (fun noise => rankByScore
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun i => noise i)
      (fun i => measurable_pi_apply i) (threeCandidateValueProfile x1 x2 x3) theta)
    (rum3RankByScoreFns theorem8GaussianDefinition2Score1
      theorem8GaussianDefinition2Score2 theorem8GaussianDefinition2Score3)
    (rum3RankByScoreFns_measurable theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable) ?_
  have hnoNamed :=
    theorem8GaussianDefinition2ScoreMeasureStd_no_score_ties_ae
      (x1 := x1) (x2 := x2) (x3 := x3)
      (one_div_ne_zero (ne_of_gt htheta))
  filter_upwards [htransport.quasiMeasurePreserving.ae hnoNamed] with noise hno
  apply theorem2GaussianCandidateNoise_rank_eq_namedRank_of_noTies
  · rw [← theorem2GaussianCandidateNoiseToNamedScoreMap_score1,
      ← theorem2GaussianCandidateNoiseToNamedScoreMap_score2]
    exact hno.1
  · rw [← theorem2GaussianCandidateNoiseToNamedScoreMap_score1,
      ← theorem2GaussianCandidateNoiseToNamedScoreMap_score3]
    exact hno.2.1
  · rw [← theorem2GaussianCandidateNoiseToNamedScoreMap_score2,
      ← theorem2GaussianCandidateNoiseToNamedScoreMap_score3]
    exact hno.2.2

/-- The named three-candidate Gaussian accuracy family satisfies every field
of the paper's Definition 1 for an ordered value profile.  Continuity,
concentration, and finite-removal monotonicity use the existing named-law
arguments; differentiability is transported from the corrected literal iid
Gaussian family through the explicit positive-accuracy PMF equality above. -/
theorem gaussianThreeCandidateAccuracyFamily_sourceDefinition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (gaussianThreeCandidateAccuracyFamily x1 x2 x3) rum3Ranking012 := by
  refine ⟨?_, ?_, ?_⟩
  · intro theta htheta pi
    constructor
    · exact AppliedModelingLib.continuousAt_of_epsilonContinuousAt
        (gaussianThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
          htheta (threeCandidateValueProfile x1 x2 x3) pi)
    · have hdiff : DifferentiableAt ℝ
          (fun theta' =>
            ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal)
          theta :=
        theorem2GaussianScaledNoiseFamily_atom_differentiable hx12 hx23 theta htheta pi
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds htheta] with theta' htheta'
      rw [theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw
        htheta']
      rfl
  · simpa [gaussianThreeCandidateAccuracyFamily] using
      (gaussianThreeCandidateRankingLaw_atomwise_tendsto_pure012 hx12 hx23
        rum3Ranking012)
  · intro thetaA thetaH hthetaH hthetaHA
    have hmono :=
      gaussianThreeCandidateDistributionalFamily_point_removalMonotonicity
        hthetaH hthetaHA (threeCandidateValueProfile x1 x2 x3)
        ⟨by simpa [threeCandidateValueProfile] using hx12,
          by simpa [threeCandidateValueProfile] using hx23⟩
    exact
      let hfinite :=
        sourceDefinition1FiniteSetMonotonicityAt_of_theorem1RemovalMonotonicityAt_three
          hmono
      ⟨hfinite.remaining_set_weak, hfinite.full_set_strict⟩

end KR21Monoculture
