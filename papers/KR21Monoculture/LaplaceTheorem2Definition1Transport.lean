import KR21Monoculture.LaplaceW11Regularity
import KR21Monoculture.LaplaceSourceNormalization
import KR21Monoculture.Theorem2Definition1SourceFamilies
import KR21Monoculture.AppendixBGaussianMixtureDefinition1
import KR21Monoculture.AppendixBFiniteSetDefinition1
import KR21Monoculture.OuterRUMSourceConcentration
import KR21Monoculture.OuterRUMSourceMonotonicity

/-!
# Source-law transport for the KR21 Laplace Definition-1 construction

The source draws iid unit-variance Laplace innovations and ranks
`x_i + epsilon_i / theta`.  The existing named three-candidate law uses
Laplace score measures parameterized by a rate.  This module proves the
correspondence explicitly, including the factor `sqrt 2 * theta`, rather than
identifying the two constructions by declaration name or a parameter slogan.
-/

open AppliedModelingLib Filter MeasureTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-- Scaling a centered Laplace innovation by a positive accuracy and then
shifting it gives the Laplace CDF at the explicitly rescaled rate. -/
theorem laplaceCDF_add_div_scale
    {lam theta x a : ℝ} (htheta : 0 < theta) :
    theorem7LaplaceCDFClosedForm lam 0 (theta * (a - x)) =
      theorem7LaplaceCDFClosedForm (lam * theta) x a := by
  by_cases hax : a < x
  · have hleft : theta * (a - x) < 0 :=
      mul_neg_of_pos_of_neg htheta (sub_neg.mpr hax)
    rw [theorem7LaplaceCDFClosedForm, if_pos hleft,
      theorem7LaplaceCDFClosedForm, if_pos hax]
    congr 2
    ring
  · have hxa : x ≤ a := le_of_not_gt hax
    have hleft : ¬ theta * (a - x) < 0 := by
      exact not_lt.mpr (mul_nonneg htheta.le (sub_nonneg.mpr hxa))
    rw [theorem7LaplaceCDFClosedForm, if_neg hleft,
      theorem7LaplaceCDFClosedForm, if_neg hax]
    congr 3
    ring

/-- The affine source-score map sends a target lower half-line to the
corresponding centered-noise lower half-line. -/
theorem preimage_add_div_Iic
    {theta x a : ℝ} (htheta : 0 < theta) :
    (fun z : ℝ => x + z / theta) ⁻¹' Set.Iic a =
      Set.Iic (theta * (a - x)) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro hz
    have hdiv : z / theta ≤ a - x := by linarith
    have hmul := (div_le_iff₀ htheta).mp hdiv
    nlinarith
  · intro hz
    have hmul : z ≤ (a - x) * theta := by
      nlinarith
    have hdiv : z / theta ≤ a - x := (div_le_iff₀ htheta).mpr hmul
    linarith

/-- The affine source-score map transports a positive-rate centered Laplace
law to the named score law at rate `lam * theta`. -/
theorem laplaceMeasure_map_add_div
    {lam theta x : ℝ} (hlam : 0 < lam) (htheta : 0 < theta) :
    (theorem7LaplaceMeasure lam 0).map (fun z : ℝ => x + z / theta) =
      theorem7LaplaceMeasure (lam * theta) x := by
  have hrate : 0 < lam * theta := mul_pos hlam htheta
  have hmeas : Measurable (fun z : ℝ => x + z / theta) := by fun_prop
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure lam 0) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam) (μ := 0) hlam⟩
  haveI : IsProbabilityMeasure
      ((theorem7LaplaceMeasure lam 0).map (fun z : ℝ => x + z / theta)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  haveI : IsProbabilityMeasure (theorem7LaplaceMeasure (lam * theta) x) :=
    ⟨theorem7LaplaceMeasure_univ (lam := lam * theta) (μ := x) hrate⟩
  apply Measure.eq_of_cdf
  ext a
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  rw [Measure.real_def, Measure.real_def]
  rw [Measure.map_apply hmeas measurableSet_Iic,
    preimage_add_div_Iic htheta]
  rw [theorem7LaplaceMeasure_Iic_eq_CDF
      (lam := lam) (μ := 0) (a := theta * (a - x)) hlam,
    theorem7LaplaceMeasure_Iic_eq_CDF
      (lam := lam * theta) (μ := x) (a := a) hrate]
  rw [ENNReal.toReal_ofReal
      (theorem7LaplaceCDFClosedForm_nonneg (lam := lam) (μ := 0)
        (a := theta * (a - x)) hlam),
    ENNReal.toReal_ofReal
      (theorem7LaplaceCDFClosedForm_nonneg (lam := lam * theta) (μ := x)
        (a := a) hrate)]
  exact laplaceCDF_add_div_scale htheta

/-- The corrected source base-noise law is definitionally the centered
Laplace law at the literal unit-variance rate `sqrt 2`. -/
theorem sourceUnitVarianceLaplaceBaseNoiseLaw_eq_centeredLaplace :
    w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity =
      theorem7LaplaceMeasure (Real.sqrt 2) 0 := by
  rfl

/-- Reindexing the literal right-associated iid source triple gives exactly
the candidate-indexed innovation law of the corrected scaled-noise family. -/
theorem sourceUnitVarianceLaplaceStandardTriple_to_candidateNoise_measurePreserving :
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity) := by
  have hrate : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  letI : IsProbabilityMeasure (theorem7LaplaceMeasure (Real.sqrt 2) 0) :=
    ⟨theorem7LaplaceMeasure_univ (lam := Real.sqrt 2) (μ := 0) hrate⟩
  letI : IsFiniteMeasure (theorem7LaplaceMeasure (Real.sqrt 2) 0) := ⟨by simp⟩
  simpa only [sourceUnitVarianceLaplaceBaseNoiseLaw_eq_centeredLaplace] using
    (measurePreserving_rightTripleToCandidateMeasurableEquiv
      (theorem7LaplaceMeasure (Real.sqrt 2) 0))

/-- The literal source score map: divide each iid base innovation by the
positive source accuracy and add the displayed value coordinate. -/
noncomputable def sourceUnitVarianceLaplaceSourceToNamedScoreMap
    (theta x1 x2 x3 : ℝ) : Theorem7LaplacianDefinition2ScoreSpace →
      Theorem7LaplacianDefinition2ScoreSpace :=
  fun z =>
    (x1 + z.1 / theta, (x2 + z.2.1 / theta, x3 + z.2.2 / theta))

theorem measurable_sourceUnitVarianceLaplaceSourceToNamedScoreMap
    (theta x1 x2 x3 : ℝ) :
    Measurable (sourceUnitVarianceLaplaceSourceToNamedScoreMap theta x1 x2 x3) := by
  unfold sourceUnitVarianceLaplaceSourceToNamedScoreMap
  fun_prop

/-- The explicit source score map transports all three iid source innovations
to the independent named Laplace score measure.  In particular, the target
rate is visibly `sqrt 2 * theta`, not a silently reparameterized accuracy. -/
theorem sourceUnitVarianceLaplaceSourceToNamedScoreMap_measurePreserving
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    MeasurePreserving
      (sourceUnitVarianceLaplaceSourceToNamedScoreMap theta x1 x2 x3)
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
      (theorem7LaplacianDefinition2ScoreMeasure
        (Real.sqrt 2 * theta) x1 x2 x3) := by
  refine ⟨measurable_sourceUnitVarianceLaplaceSourceToNamedScoreMap theta x1 x2 x3, ?_⟩
  let mu0 : Measure ℝ := theorem7LaplaceMeasure (Real.sqrt 2) 0
  let f1 : ℝ → ℝ := fun z => x1 + z / theta
  let f2 : ℝ → ℝ := fun z => x2 + z / theta
  let f3 : ℝ → ℝ := fun z => x3 + z / theta
  have hrate : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  letI : SFinite mu0 := by
    dsimp [mu0, theorem7LaplaceMeasure]
    infer_instance
  have hf1 : Measurable f1 := by
    dsimp [f1]
    fun_prop
  have hf2 : Measurable f2 := by
    dsimp [f2]
    fun_prop
  have hf3 : Measurable f3 := by
    dsimp [f3]
    fun_prop
  have h1 : mu0.map f1 = theorem7LaplaceMeasure (Real.sqrt 2 * theta) x1 := by
    exact laplaceMeasure_map_add_div hrate htheta
  have h2 : mu0.map f2 = theorem7LaplaceMeasure (Real.sqrt 2 * theta) x2 := by
    exact laplaceMeasure_map_add_div hrate htheta
  have h3 : mu0.map f3 = theorem7LaplaceMeasure (Real.sqrt 2 * theta) x3 := by
    exact laplaceMeasure_map_add_div hrate htheta
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

/-- The target score map written directly on the corrected source family's
candidate-indexed noise space. -/
noncomputable def sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap
    (theta x1 x2 x3 : ℝ) : (Candidate 1 → ℝ) →
      Theorem7LaplacianDefinition2ScoreSpace :=
  sourceUnitVarianceLaplaceSourceToNamedScoreMap theta x1 x2 x3 ∘
    (rightTripleToCandidateMeasurableEquiv ℝ).symm

theorem sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_measurePreserving
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    MeasurePreserving
      (sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3)
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
      (theorem7LaplacianDefinition2ScoreMeasure
        (Real.sqrt 2 * theta) x1 x2 x3) := by
  exact
    (sourceUnitVarianceLaplaceSourceToNamedScoreMap_measurePreserving htheta).comp
      (MeasurePreserving.symm (rightTripleToCandidateMeasurableEquiv ℝ)
        sourceUnitVarianceLaplaceStandardTriple_to_candidateNoise_measurePreserving)

/-! ## Reconciliation of the two finite ranking encodings -/

private theorem sourceLaplace_rankByScore_eq_of_strict_ranking_order
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

/-- Away from the three score-tie hyperplanes, the generic finite sorter and
the named three-score ranking map agree.  We keep this as an a.e. bridge
instead of treating their independently implemented total tie conventions as
definitionally identical. -/
private theorem sourceLaplace_rankByScore_three_eq_named_of_noTies
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
        apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [threeCandidateValueProfile, rum3Ranking012] <;> linarith
      rw [hrank]
      exact (rum3RankByScores_eq012_of_adjacent_order h0.1 h32).symm
    · have h23' : s2 < s3 := lt_of_not_ge h32
      have h31 : s3 < s1 := lt_of_le_of_ne h0.2 h13.symm
      have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
          rum3Ranking021 := by
        apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
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
          apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
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
          apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
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
          apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
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
          apply sourceLaplace_rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking210] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking210,
          dif_neg h0, dif_neg h1, if_neg h21]

theorem sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score1
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem7LaplacianDefinition2Score1
      (sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x1 + noise 0 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h0 := congrFun he (0 : Candidate 1)
  change (e.symm noise).1 = noise 0 at h0
  simpa [sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap,
    sourceUnitVarianceLaplaceSourceToNamedScoreMap,
    theorem7LaplacianDefinition2Score1, e] using
      congrArg (fun z : ℝ => x1 + z / theta) h0

theorem sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score2
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem7LaplacianDefinition2Score2
      (sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x2 + noise 1 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h1 := congrFun he (1 : Candidate 1)
  change (e.symm noise).2.1 = noise 1 at h1
  simpa [sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap,
    sourceUnitVarianceLaplaceSourceToNamedScoreMap,
    theorem7LaplacianDefinition2Score2, e] using
      congrArg (fun z : ℝ => x2 + z / theta) h1

theorem sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score3
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ) :
    theorem7LaplacianDefinition2Score3
      (sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) =
      x3 + noise 2 / theta := by
  let e := rightTripleToCandidateMeasurableEquiv ℝ
  have he : e (e.symm noise) = noise := e.apply_symm_apply noise
  have h2 := congrFun he (2 : Candidate 1)
  change (e.symm noise).2.2 = noise 2 at h2
  simpa [sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap,
    sourceUnitVarianceLaplaceSourceToNamedScoreMap,
    theorem7LaplacianDefinition2Score3, e] using
      congrArg (fun z : ℝ => x3 + z / theta) h2

private theorem sourceUnitVarianceLaplaceCandidateNoise_rank_eq_namedRank_of_noTies
    (theta x1 x2 x3 : ℝ) (noise : Candidate 1 → ℝ)
    (h12 : x1 + noise 0 / theta ≠ x2 + noise 1 / theta)
    (h13 : x1 + noise 0 / theta ≠ x3 + noise 2 / theta)
    (h23 : x2 + noise 1 / theta ≠ x3 + noise 2 / theta) :
    rankByScore (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta) =
      rum3RankByScoreFns theorem7LaplacianDefinition2Score1
        theorem7LaplacianDefinition2Score2 theorem7LaplacianDefinition2Score3
        (sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3 noise) := by
  let s1 := x1 + noise 0 / theta
  let s2 := x2 + noise 1 / theta
  let s3 := x3 + noise 2 / theta
  have hscores :
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta) =
        threeCandidateValueProfile s1 s2 s3 := by
    funext i
    fin_cases i <;> simp [s1, s2, s3, threeCandidateValueProfile]
  rw [hscores, sourceLaplace_rankByScore_three_eq_named_of_noTies s1 s2 s3]
  · simp only [rum3RankByScoreFns]
    rw [sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score1,
      sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score2,
      sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score3]
  · simpa [s1, s2, s3] using h12
  · simpa [s1, s2, s3] using h13
  · simpa [s1, s2, s3] using h23

/-- A measure transport preserves a finite ranking PMF when its two ranking
maps agree almost everywhere.  The a.e. hypothesis is essential for source
RUM transports, whose two total ranking encodings can differ only on
zero-probability score ties. -/
private theorem sourceLaplace_rankingPMFOfMeasure_eq_of_measurePreserving_ae
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

/-- At every positive source accuracy, the literal iid unit-variance Laplace
scaled-noise family induces exactly the named source-normalized three-score
ranking law.  This is an equality of finite PMFs obtained through an explicit
three-coordinate measure transport, not a name- or convention-based rewrite. -/
theorem sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (w11CorrectedScaledNoiseFamily sourceUnitVarianceLaplaceBaseDensity
      sourceUnitVarianceLaplace_w11Regularity.normalized
      (threeCandidateValueProfile x1 x2 x3)).dist theta =
      sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3 := by
  let regularity := sourceUnitVarianceLaplace_w11Regularity
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      sourceUnitVarianceLaplaceBaseDensity regularity.normalized
  have hrate : 0 < Real.sqrt 2 * theta :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  letI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure (Real.sqrt 2 * theta) x1 x2 x3) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure hrate
  rw [sourceUnitVarianceLaplaceThreeCandidateRankingLaw_eq,
    laplaceThreeCandidateRankingLaw_eq_of_pos hrate]
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
      (threeCandidateValueProfile x1 x2 x3) theta =
      rumRankingPMFOfMeasure
        (theorem7LaplacianDefinition2ScoreMeasure (Real.sqrt 2 * theta) x1 x2 x3)
        (rum3RankByScoreFns
          theorem7LaplacianDefinition2Score1
          theorem7LaplacianDefinition2Score2
          theorem7LaplacianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem7LaplacianDefinition2Score1_measurable
          theorem7LaplacianDefinition2Score2_measurable
          theorem7LaplacianDefinition2Score3_measurable)
  let transport := sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap theta x1 x2 x3
  have htransport : MeasurePreserving transport
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
      (theorem7LaplacianDefinition2ScoreMeasure (Real.sqrt 2 * theta) x1 x2 x3) :=
    sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_measurePreserving htheta
  refine sourceLaplace_rankingPMFOfMeasure_eq_of_measurePreserving_ae
    (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
    (theorem7LaplacianDefinition2ScoreMeasure (Real.sqrt 2 * theta) x1 x2 x3)
    transport htransport
    (fun noise => rankByScore
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun i => noise i)
      (fun i => measurable_pi_apply i) (threeCandidateValueProfile x1 x2 x3) theta)
    (rum3RankByScoreFns theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2 theorem7LaplacianDefinition2Score3)
    (rum3RankByScoreFns_measurable theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable) ?_
  have hnoNamed :=
    theorem7LaplacianDefinition2ScoreMeasure_no_score_ties_ae
      (lam := Real.sqrt 2 * theta) (x1 := x1) (x2 := x2) (x3 := x3)
  filter_upwards [htransport.quasiMeasurePreserving.ae hnoNamed] with noise hno
  apply sourceUnitVarianceLaplaceCandidateNoise_rank_eq_namedRank_of_noTies
  · rw [← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score1,
      ← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score2]
    exact hno.1
  · rw [← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score1,
      ← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score3]
    exact hno.2.1
  · rw [← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score2,
      ← sourceUnitVarianceLaplaceCandidateNoiseToNamedScoreMap_score3]
    exact hno.2.2

/-- The named source-normalized Laplace conditional family satisfies every
field of the paper's Definition 1 at an ordered three-candidate profile.  The
continuity, true-ranking limit, and finite-removal comparisons are proved at
the named law itself.  The sole differentiability transfer is justified by
the explicit source-to-named PMF equality above at every nearby positive
accuracy. -/
theorem sourceUnitVarianceLaplaceThreeCandidatePointFamily_sourceDefinition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.pointFamily
        (threeCandidateValueProfile x1 x2 x3)) rum3Ranking012 := by
  refine ⟨?_, ?_, ?_⟩
  · intro theta htheta pi
    constructor
    · exact AppliedModelingLib.continuousAt_of_epsilonContinuousAt
        (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
          htheta (threeCandidateValueProfile x1 x2 x3) pi)
    · have hdiff : DifferentiableAt ℝ
          (fun theta' =>
            ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal)
          theta :=
        sourceUnitVarianceLaplaceScaledNoiseFamily_atom_differentiable
          hx12 hx23 theta htheta pi
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds htheta] with theta' htheta'
      rw [show (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' =
          sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta' x1 x2 x3 by
            simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
              sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw htheta']
      rfl
  · simpa [DistributionalAccuracyFamily.pointFamily,
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily] using
      (sourceUnitVarianceLaplaceThreeCandidateRankingLaw_atomwise_tendsto_pure012
        hx12 hx23 rum3Ranking012)
  · intro thetaA thetaH hthetaH hthetaHA
    have hmono :=
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_point_removalMonotonicity
        hthetaH hthetaHA (threeCandidateValueProfile x1 x2 x3)
        ⟨by simpa [threeCandidateValueProfile] using hx12,
          by simpa [threeCandidateValueProfile] using hx23⟩
    exact
      let hfinite :=
        sourceDefinition1FiniteSetMonotonicityAt_of_theorem1RemovalMonotonicityAt_three
          hmono
      ⟨hfinite.remaining_set_weak, hfinite.full_set_strict⟩

end KR21Monoculture
