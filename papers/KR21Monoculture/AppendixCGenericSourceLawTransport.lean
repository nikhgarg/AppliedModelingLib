import KR21Monoculture.W11ArbitraryFiniteCells
import KR21Monoculture.MainTheorems
import KR21Monoculture.AppendixBGaussianMixtureDefinition1
import KR21Monoculture.ThreeCandidateValueProfile
import Mathlib.MeasureTheory.Function.JacobianOneDim

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-!
# Generic raw-RUM transport for Appendix C

This module bridges the source experiment with iid base innovations `epsilon`
and scores `x_i + epsilon_i / theta` to the score-density experiment used by
the continuous Appendix C proof.  The bridge is an actual change of variables:
the scaled innovation density is `z |-> theta * f (theta * z)`, not a
ranking-law or coupling hypothesis.
-/

/-- Density of `epsilon / theta` when `epsilon` has density `f` and
`theta > 0`. -/
noncomputable def appendixCScaledNoiseDensity (f : ℝ → ℝ) (theta : ℝ) : ℝ → ℝ :=
  fun z => theta * f (theta * z)

theorem appendixCScaledNoiseDensity_measurable
    {f : ℝ → ℝ} (hf : Measurable f) (theta : ℝ) :
    Measurable (appendixCScaledNoiseDensity f theta) := by
  exact measurable_const.mul (hf.comp (measurable_const.mul measurable_id))

theorem appendixCScaledNoiseDensity_pos
    {f : ℝ → ℝ} {theta : ℝ} (htheta : 0 < theta)
    (hpos : ∀ z : ℝ, 0 < f z) :
    ∀ z : ℝ, 0 < appendixCScaledNoiseDensity f theta z := by
  intro z
  exact mul_pos htheta (hpos _)

/-- Positive horizontal scaling preserves the strict well-ordering relation. -/
theorem StrictlyWellOrderedNoise.comp_mul_pos
    {f : ℝ → ℝ} {c : ℝ} (hf : StrictlyWellOrderedNoise f) (hc : 0 < c) :
    StrictlyWellOrderedNoise (fun z => f (c * z)) := by
  intro a b x y hab hxy
  have h := hf (mul_lt_mul_of_pos_left hab hc) (mul_lt_mul_of_pos_left hxy hc)
  simpa [mul_sub] using h

/-- For a nonnegative density, strict well-ordering itself rules out every
zero: apply the four-point inequality at two adjacent unit intervals. -/
theorem StrictlyWellOrderedNoise.pos_of_nonneg
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) :
    ∀ z : ℝ, 0 < f z := by
  intro z
  have hstrict := hf (a := z) (b := z - 1) (c := 0) (d := -1)
    (by linarith) (by linarith)
  have hstrict' : f z * f z > f (z + 1) * f (z - 1) := by
    convert hstrict using 1 <;> ring_nf
  have hsquare : 0 < f z * f z :=
    lt_of_le_of_lt (mul_nonneg (hnonneg (z + 1)) (hnonneg (z - 1))) hstrict'
  have hne : f z ≠ 0 := by
    intro hz
    simpa [hz] using hsquare
  exact lt_of_le_of_ne (hnonneg z) (Ne.symm hne)

theorem appendixCScaledNoiseDensity_strictlyWellOrdered
    {f : ℝ → ℝ} {theta : ℝ} (hf : StrictlyWellOrderedNoise f)
    (htheta : 0 < theta) :
    StrictlyWellOrderedNoise (appendixCScaledNoiseDensity f theta) := by
  exact (hf.comp_mul_pos htheta).const_mul_pos htheta

theorem appendixC_integrable_of_normalized_positive_density
    {f : ℝ → ℝ} (hfmeas : Measurable f) (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1) :
    Integrable f volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    hfmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (hpos z).le)).mp
  rw [hnorm]
  exact ENNReal.one_ne_top

theorem appendixCScaledNoiseDensity_integrable
    {f : ℝ → ℝ} {theta : ℝ} (hf : Integrable f volume)
    (htheta : 0 < theta) :
    Integrable (appendixCScaledNoiseDensity f theta) volume := by
  exact (hf.comp_mul_left' htheta.ne').const_mul theta

/--
One-dimensional source-law transport: dividing a base innovation by a positive
accuracy parameter produces the displayed scaled density.
-/
theorem w11BaseNoiseLaw_map_div_eq_appendixCScaledNoiseLaw
    (f : ℝ → ℝ) {theta : ℝ} (hf : Integrable f volume)
    (hpos : ∀ z : ℝ, 0 < f z) (htheta : 0 < theta) :
    (w11BaseNoiseLaw f).map (fun z => z / theta) =
      w11BaseNoiseLaw (appendixCScaledNoiseDensity f theta) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ theta htheta.ne').toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e theta x := fun _ => by
    simpa [e, Homeomorph.mulLeft₀] using
      (HasDerivAt.const_mul theta (hasDerivAt_id _))
  have hscaled_int : Integrable (appendixCScaledNoiseDensity f theta) volume :=
    appendixCScaledNoiseDensity_integrable hf htheta
  have he_symm : (fun z : ℝ => z / theta) = e.symm := by
    funext z
    simp [e, Homeomorph.mulLeft₀, div_eq_mul_inv, mul_comm]
  rw [he_symm]
  unfold w11BaseNoiseLaw
  change (volume.withDensity fun z => ENNReal.ofReal (f z)).map e.symm =
    volume.withDensity (fun z => ENNReal.ofReal (appendixCScaledNoiseDensity f theta z))
  ext s hs
  have hlintegral :
      ENNReal.ofReal (∫ z in s, appendixCScaledNoiseDensity f theta z ∂volume) =
        ∫⁻ z in s, ENNReal.ofReal (appendixCScaledNoiseDensity f theta z) ∂volume := by
    simpa only [IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict s) hscaled_int.integrableOn
        (Filter.Eventually.of_forall fun z =>
          (appendixCScaledNoiseDensity_pos htheta hpos z).le))
  calc
    (volume.withDensity fun z => ENNReal.ofReal (f z)).map e.symm s =
        ENNReal.ofReal (∫ z in s, |theta| * f (e z) ∂volume) := by
      exact e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
        hs he' (Filter.Eventually.of_forall fun z => (hpos z).le) hf
    _ = ENNReal.ofReal (∫ z in s, appendixCScaledNoiseDensity f theta z ∂volume) := by
      congr 1
      apply setIntegral_congr_ae
      · exact hs
      · filter_upwards with z
        simp [appendixCScaledNoiseDensity, e, Homeomorph.mulLeft₀,
          abs_of_pos htheta]
    _ = ∫⁻ z in s, ENNReal.ofReal (appendixCScaledNoiseDensity f theta z) ∂volume :=
      hlintegral
    _ = (volume.withDensity
        (fun z => ENNReal.ofReal (appendixCScaledNoiseDensity f theta z))) s := by
      rw [withDensity_apply _ hs]

/-- The Jacobian transport preserves the source density's displayed mass. -/
theorem appendixCScaledNoiseDensity_normalized
    (f : ℝ → ℝ) {theta : ℝ} (hf : Integrable f volume)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (htheta : 0 < theta) :
    ∫⁻ z, ENNReal.ofReal (appendixCScaledNoiseDensity f theta z) ∂volume = 1 := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnorm
  have htransport :=
    w11BaseNoiseLaw_map_div_eq_appendixCScaledNoiseLaw f hf hpos htheta
  have hscale : Measurable (fun z : ℝ => z / theta) :=
    measurable_id.div measurable_const
  calc
    ∫⁻ z, ENNReal.ofReal (appendixCScaledNoiseDensity f theta z) ∂volume =
        (w11BaseNoiseLaw (appendixCScaledNoiseDensity f theta)) Set.univ := by
      simp [w11BaseNoiseLaw, withDensity_apply]
    _ = ((w11BaseNoiseLaw f).map (fun z : ℝ => z / theta)) Set.univ := by
      rw [htransport]
    _ = (w11BaseNoiseLaw f) ((fun z : ℝ => z / theta) ⁻¹' Set.univ) := by
      rw [Measure.map_apply hscale MeasurableSet.univ]
    _ = 1 := by simp

/-- Coordinatewise division of a finite iid innovation vector. -/
noncomputable def appendixCScaleNoiseVector {n : ℕ} (theta : ℝ) :
    (Candidate n → ℝ) → Candidate n → ℝ :=
  fun noise i => noise i / theta

theorem measurable_appendixCScaleNoiseVector {n : ℕ} (theta : ℝ) :
    Measurable (appendixCScaleNoiseVector (n := n) theta) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i |>.div measurable_const

/--
The finite iid source law transports coordinatewise under the displayed
`epsilon / theta` map.  This is derived from the scalar Jacobian transport
above and `Measure.pi_map_pi`.
-/
theorem w11CandidateNoiseLaw_map_div_eq_appendixCScaledNoiseLaw
    {n : ℕ} (f : ℝ → ℝ) {theta : ℝ}
    (hf : Integrable f volume) (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (htheta : 0 < theta) :
    (w11CandidateNoiseLaw (n := n) f).map
      (appendixCScaleNoiseVector (n := n) theta) =
      w11CandidateNoiseLaw (n := n) (appendixCScaledNoiseDensity f theta) := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnorm
  letI : ∀ i : Candidate n,
      SigmaFinite ((w11BaseNoiseLaw f).map (fun z : ℝ => z / theta)) :=
    fun _ => inferInstance
  let scale : ℝ → ℝ := fun z => z / theta
  have hscale : Measurable scale := by
    exact measurable_id.div measurable_const
  unfold w11CandidateNoiseLaw appendixCScaleNoiseVector
  change (Measure.pi fun _ : Candidate n => w11BaseNoiseLaw f).map
      (fun noise i => scale (noise i)) =
    Measure.pi (fun _ : Candidate n =>
      w11BaseNoiseLaw (appendixCScaledNoiseDensity f theta))
  rw [Measure.pi_map_pi (fun _ : Candidate n => hscale.aemeasurable)]
  congr 1
  funext i
  exact w11BaseNoiseLaw_map_div_eq_appendixCScaledNoiseLaw f hf hpos htheta

/-- The literal source score vector `x_i + epsilon_i / theta`. -/
noncomputable def appendixCRawScoreMap {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) :
    (Candidate n → ℝ) → Candidate n → ℝ :=
  fun noise i => value i + noise i / theta

theorem measurable_appendixCRawScoreMap {n : ℕ}
    (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (appendixCRawScoreMap value theta) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.add (measurable_pi_apply i |>.div measurable_const)

/-- Increasing source accuracy contracts the realized raw score toward its
true value by the source ratio `thetaH / thetaA`. -/
theorem appendixCRawScoreMap_eq_contract
    {n : ℕ} {thetaA thetaH : ℝ}
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH)
    (value noise : Candidate n → ℝ) (i : Candidate n) :
    appendixCRawScoreMap value thetaA noise i =
      rumContractScore (thetaH / thetaA) (value i)
        (appendixCRawScoreMap value thetaH noise i) := by
  unfold appendixCRawScoreMap rumContractScore AppliedModelingLib.Probability.rumContractScore
  field_simp [ne_of_gt hthetaA, ne_of_gt hthetaH]
  ring

/--
The literal raw source scores have the finite iid score-density law for the
Jacobian-derived scaled innovation density.  This is an equality of measures,
not an assumed equality of ranking laws.
-/
theorem w11CandidateNoiseLaw_map_rawScore_eq_candidateScoreLaw
    {n : ℕ} (f : ℝ → ℝ) {theta : ℝ}
    (hf : Integrable f volume) (hfmeas : Measurable f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (htheta : 0 < theta) (value : Candidate n → ℝ) :
    (w11CandidateNoiseLaw (n := n) f).map
        (appendixCRawScoreMap value theta) =
      w11CandidateScoreLaw (appendixCScaledNoiseDensity f theta) value 1 := by
  let scale : (Candidate n → ℝ) → Candidate n → ℝ :=
    appendixCScaleNoiseVector (n := n) theta
  let add : (Candidate n → ℝ) → Candidate n → ℝ :=
    w11CandidateAdditiveScoreMap value 1
  have hscale : Measurable scale := by
    exact measurable_appendixCScaleNoiseVector theta
  have hadd : Measurable add := by
    exact measurable_w11CandidateAdditiveScoreMap value 1
  have hraw : appendixCRawScoreMap value theta = add ∘ scale := by
    funext noise i
    simp [appendixCRawScoreMap, add, scale, w11CandidateAdditiveScoreMap,
      appendixCScaleNoiseVector]
    ring
  rw [hraw, ← Measure.map_map hadd hscale,
    w11CandidateNoiseLaw_map_div_eq_appendixCScaledNoiseLaw f hf hpos hnorm htheta]
  symm
  exact w11CandidateScoreLaw_eq_map_w11CandidateNoiseLaw n
    (appendixCScaledNoiseDensity f theta)
    (appendixCScaledNoiseDensity_integrable hf htheta)
    (appendixCScaledNoiseDensity_measurable hfmeas theta)
    (fun z => (appendixCScaledNoiseDensity_pos htheta hpos z).le)
    value 1

/-- The canonical three-coordinate score carrier reassembled as candidates. -/
noncomputable abbrev appendixCScoreSpaceToCandidate :
    RUM3ScoreSpace ≃ᵐ (Candidate 1 → ℝ) :=
  tripleToCandidateMeasurableEquiv ℝ

theorem appendixCScoreSpaceToCandidate_measurePreserving_volume :
    MeasurePreserving appendixCScoreSpaceToCandidate
      (volume : Measure RUM3ScoreSpace) volume := by
  simpa [appendixCScoreSpaceToCandidate, RUM3ScoreSpace, Candidate,
    Measure.volume_eq_prod] using
    (measurePreserving_tripleToCandidateMeasurableEquiv
      (α := ℝ) (μ := volume))

theorem appendixCScoreSpaceToCandidate_symm_score1
    (score : Candidate 1 → ℝ) :
    rum3Score1 (appendixCScoreSpaceToCandidate.symm score) = score 0 := by
  have h := congrFun (appendixCScoreSpaceToCandidate.apply_symm_apply score)
    (0 : Candidate 1)
  change rum3Score1 (appendixCScoreSpaceToCandidate.symm score) = score 0 at h
  exact h

theorem appendixCScoreSpaceToCandidate_symm_score2
    (score : Candidate 1 → ℝ) :
    rum3Score2 (appendixCScoreSpaceToCandidate.symm score) = score 1 := by
  have h := congrFun (appendixCScoreSpaceToCandidate.apply_symm_apply score)
    (1 : Candidate 1)
  change rum3Score2 (appendixCScoreSpaceToCandidate.symm score) = score 1 at h
  exact h

theorem appendixCScoreSpaceToCandidate_symm_score3
    (score : Candidate 1 → ℝ) :
    rum3Score3 (appendixCScoreSpaceToCandidate.symm score) = score 2 := by
  have h := congrFun (appendixCScoreSpaceToCandidate.apply_symm_apply score)
    (2 : Candidate 1)
  change rum3Score3 (appendixCScoreSpaceToCandidate.symm score) = score 2 at h
  exact h

/-- Density transport through a volume-preserving measurable equivalence. -/
private theorem appendixC_map_withDensity_eq_withDensity_comp_symm
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (he : MeasurePreserving e μ ν) (density : α → ℝ≥0∞) :
    (μ.withDensity density).map e = ν.withDensity (density ∘ e.symm) := by
  ext s hs
  calc
    (μ.withDensity density).map e s =
        ∫⁻ x in e ⁻¹' s, density x ∂μ := by
      rw [e.map_apply, withDensity_apply density
        (e.measurableSet_preimage.mpr hs)]
    _ = ∫⁻ y in s, (density ∘ e.symm) y ∂ν := by
      simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
        he.setLIntegral_comp_preimage_emb e.measurableEmbedding
          (fun y => density (e.symm y)) s
    _ = (ν.withDensity (density ∘ e.symm)) s := by
      rw [withDensity_apply _ hs]

theorem appendixC_candidateScoreDensity_map_to_scoreSpace
    (f : ℝ → ℝ) (x1 x2 x3 : ℝ) :
    (w11CandidateScoreLaw f (threeCandidateValueProfile x1 x2 x3) 1).map
      appendixCScoreSpaceToCandidate.symm =
      (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN f x1 x2 x3 rum3Score1 rum3Score2 rum3Score3) := by
  change
    ((volume : Measure (Candidate 1 → ℝ)).withDensity
      (w11CandidateScoreDensityENN f (threeCandidateValueProfile x1 x2 x3) 1)).map
      appendixCScoreSpaceToCandidate.symm =
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN f x1 x2 x3 rum3Score1 rum3Score2 rum3Score3)
  let e : (Candidate 1 → ℝ) ≃ᵐ RUM3ScoreSpace :=
    appendixCScoreSpaceToCandidate.symm
  have he : MeasurePreserving e
      (volume : Measure (Candidate 1 → ℝ)) volume := by
    exact MeasurePreserving.symm _ appendixCScoreSpaceToCandidate_measurePreserving_volume
  have htransport := appendixC_map_withDensity_eq_withDensity_comp_symm
    e (volume : Measure (Candidate 1 → ℝ)) (volume : Measure RUM3ScoreSpace)
    he (w11CandidateScoreDensityENN f (threeCandidateValueProfile x1 x2 x3) 1)
  -- The transported finite-product density is the literal three-score product.
  have hdensity :
      w11CandidateScoreDensityENN f (threeCandidateValueProfile x1 x2 x3) 1
          ∘ appendixCScoreSpaceToCandidate =
        rum3ScoreDensityENN f x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 := by
    funext omega
    change ENNReal.ofReal
        (w11CandidateScoreDensity f (threeCandidateValueProfile x1 x2 x3) 1
          (tripleToCandidateMeasurableEquiv ℝ omega)) = _
    rw [tripleToCandidateMeasurableEquiv_apply_eq_function]
    rw [w11CandidateScoreDensity, Fin.prod_univ_three]
    simp [
      threeCandidateValueProfile,
      tripleToCandidateFunction, rum3ScoreDensityENN,
      AppliedModelingLib.Probability.rum3ScoreDensityENN,
      rum3Score1, rum3Score2, rum3Score3]
  simpa [e, hdensity] using htransport

/-! ## Reconciling the two executable three-score rankers -/

private theorem appendixC_rankByScore_eq_of_strict_ranking_order
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

/--
Off the three score-tie hyperplanes, the library's canonical finite sorter and
the Appendix-C three-score case split return the same ranking.  The two maps
have independent total tie conventions, so this lemma deliberately records
the exact no-tie condition needed for the subsequent almost-everywhere bridge.
-/
theorem appendixC_rankByScore_three_eq_rum3RankByScores_of_noTies
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
        apply appendixC_rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [threeCandidateValueProfile, rum3Ranking012] <;> linarith
      rw [hrank]
      exact (rum3RankByScores_eq012_of_adjacent_order h0.1 h32).symm
    · have h23' : s2 < s3 := lt_of_not_ge h32
      have h31 : s3 < s1 := lt_of_le_of_ne h0.2 h13.symm
      have hrank : rankByScore (threeCandidateValueProfile s1 s2 s3) =
          rum3Ranking021 := by
        apply appendixC_rankByScore_eq_of_strict_ranking_order
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
          apply appendixC_rankByScore_eq_of_strict_ranking_order
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
          apply appendixC_rankByScore_eq_of_strict_ranking_order
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
          apply appendixC_rankByScore_eq_of_strict_ranking_order
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
          apply appendixC_rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [threeCandidateValueProfile, rum3Ranking210] <;> linarith
        rw [hrank]
        symm
        simp only [KR21Monoculture.rum3RankByScores,
          AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores,
          KR21Monoculture.rum3Ranking210,
          dif_neg h0, dif_neg h1, if_neg h21]

/--
Measure transport preserves a finite ranking PMF when the two executable rank
maps agree almost everywhere.  The a.e. form is necessary only because the
two three-score rankers intentionally make independent choices on tie planes.
-/
theorem appendixC_rankingPMFOfMeasure_eq_of_measurePreserving_ae
    {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (rank' : Ω' → Ranking n) (hrank' : Measurable rank')
    (hintertwine : ∀ᵐ omega ∂μ, rank omega = rank' (e omega)) :
    rankingPMFOfMeasure μ rank hrank = rankingPMFOfMeasure ν rank' hrank' := by
  classical
  apply PMF.ext
  intro pi
  apply (ENNReal.toReal_eq_toReal_iff'
    ((rankingPMFOfMeasure μ rank hrank).apply_ne_top pi)
    ((rankingPMFOfMeasure ν rank' hrank').apply_ne_top pi)).mp
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure μ rank hrank) pi]
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure ν rank' hrank') pi]
  rw [rankingPMFOfMeasure_eventProb μ rank hrank
    (fun rho : Ranking n => rho = pi)]
  rw [rankingPMFOfMeasure_eventProb ν rank' hrank'
    (fun rho : Ranking n => rho = pi)]
  trans AppliedModelingLib.measureProb μ (fun omega => rank' (e omega) = pi)
  · unfold AppliedModelingLib.measureProb
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hintertwine] with omega homega
    apply propext
    change (rank omega = pi) ↔ (rank' (e omega) = pi)
    rw [homega]
  · exact AppliedModelingLib.measureProb_preimage_of_measurePreserving
      e he (fun omega' : Ω' => rank' omega' = pi)
      (by
        simpa only [Set.preimage_setOf_eq] using
          hrank' (show MeasurableSet {rho : Ranking n | rho = pi}
            from MeasurableSet.of_discrete))

/-- The concrete RUM3 score density is normalized whenever its iid base
innovation density is normalized. -/
theorem appendixC_candidateScoreDensity_normalized
    (g : ℝ → ℝ) (hg : Integrable g volume)
    (hgnonneg : ∀ z : ℝ, 0 ≤ g z)
    (hgnorm : ∫⁻ z, ENNReal.ofReal (g z) ∂volume = 1)
    (x1 x2 x3 : ℝ) :
    ∫⁻ omega,
        rum3ScoreDensityENN g x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 omega
        ∂(volume : Measure RUM3ScoreSpace) = 1 := by
  let value : Candidate 1 → ℝ := threeCandidateValueProfile x1 x2 x3
  letI : IsProbabilityMeasure (w11CandidateScoreLaw g value 1) :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization 1 g hg
      hgnonneg hgnorm value 1
  have htransport := appendixC_candidateScoreDensity_map_to_scoreSpace g x1 x2 x3
  have huniv :
      ((volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN g x1 x2 x3 rum3Score1 rum3Score2 rum3Score3))
        Set.univ = 1 := by
    rw [← htransport]
    rw [Measure.map_apply appendixCScoreSpaceToCandidate.symm.measurable
      MeasurableSet.univ]
    simp
  simpa [withDensity_apply] using huniv

/--
The RUM3 score density has no score ties almost everywhere.  This is derived
from absolute continuity of the finite-dimensional density law, rather than
assumed as an equality between ranking laws.
-/
theorem appendixC_candidateScoreDensity_noTies_ae
    (g : ℝ → ℝ) (hg : Integrable g volume)
    (hgnonneg : ∀ z : ℝ, 0 ≤ g z)
    (hgnorm : ∫⁻ z, ENNReal.ofReal (g z) ∂volume = 1)
    (x1 x2 x3 : ℝ) :
    ∀ᵐ omega ∂(volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN g x1 x2 x3 rum3Score1 rum3Score2 rum3Score3),
      rum3Score1 omega ≠ rum3Score2 omega ∧
        rum3Score1 omega ≠ rum3Score3 omega ∧
          rum3Score2 omega ≠ rum3Score3 omega := by
  let value : Candidate 1 → ℝ := threeCandidateValueProfile x1 x2 x3
  let μ : Measure (Candidate 1 → ℝ) := w11CandidateScoreLaw g value 1
  let ν : Measure RUM3ScoreSpace :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN g x1 x2 x3 rum3Score1 rum3Score2 rum3Score3)
  letI : IsProbabilityMeasure μ :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization 1 g hg
      hgnonneg hgnorm value 1
  have hcandidate :
      ∀ᵐ score ∂μ, ∀ i j : Candidate 1, i ≠ j → score i ≠ score j := by
    simpa [μ, value, w11CandidateScoreLaw] using
      (paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
        (μ := μ) (D := w11CandidateScoreDensityENN g value 1)
        (by rfl) (fun _ : Candidate 1 => 0) (by norm_num : (0 : ℝ) < 1))
  have htransport : MeasurePreserving appendixCScoreSpaceToCandidate.symm μ ν := by
    refine ⟨appendixCScoreSpaceToCandidate.symm.measurable, ?_⟩
    simpa [μ, ν, value] using
      (appendixC_candidateScoreDensity_map_to_scoreSpace g x1 x2 x3)
  have hback : MeasurePreserving appendixCScoreSpaceToCandidate ν μ :=
    MeasurePreserving.symm _ htransport
  have hscore := hback.quasiMeasurePreserving.tendsto_ae hcandidate
  change ∀ᵐ omega ∂ν,
      rum3Score1 omega ≠ rum3Score2 omega ∧
        rum3Score1 omega ≠ rum3Score3 omega ∧
          rum3Score2 omega ≠ rum3Score3 omega
  filter_upwards [hscore] with omega homega
  have h12 := homega (0 : Candidate 1) (1 : Candidate 1) (by decide)
  have h13 := homega (0 : Candidate 1) (2 : Candidate 1) (by decide)
  have h23 := homega (1 : Candidate 1) (2 : Candidate 1) (by decide)
  change (tripleToCandidateMeasurableEquiv ℝ omega) 0 ≠
      (tripleToCandidateMeasurableEquiv ℝ omega) 1 at h12
  change (tripleToCandidateMeasurableEquiv ℝ omega) 0 ≠
      (tripleToCandidateMeasurableEquiv ℝ omega) 2 at h13
  change (tripleToCandidateMeasurableEquiv ℝ omega) 1 ≠
      (tripleToCandidateMeasurableEquiv ℝ omega) 2 at h23
  rw [tripleToCandidateMeasurableEquiv_apply_eq_function] at h12 h13 h23
  simpa [tripleToCandidateFunction, rum3Score1, rum3Score2, rum3Score3] using
    ⟨h12, h13, h23⟩

/--
At a fixed positive accuracy, the literal source ranking PMF is the raw
three-score ranking PMF under the score-density experiment obtained by the
Jacobian transport.  The only a.e. step reconciles the two concrete tie
conventions, and its no-tie fact is derived from the density law.
-/
theorem appendixC_sourceRawRankingPMF_eq_scoreSpaceRaw
    (f : ℝ → ℝ) {theta : ℝ}
    (hf : Integrable f volume) (hfmeas : Measurable f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (htheta : 0 < theta) (x1 x2 x3 : ℝ)
    (hscoreNorm :
      ∫⁻ omega,
          rum3ScoreDensityENN (appendixCScaledNoiseDensity f theta) x1 x2 x3
            rum3Score1 rum3Score2 rum3Score3 omega
          ∂(volume : Measure RUM3ScoreSpace) = 1) :
    @paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) theta =
      paper_theorem6_normalizedScoreRankingPMF
        (appendixCScaledNoiseDensity f theta) x1 x2 x3 hscoreNorm
        (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable) := by
  let value : Candidate 1 → ℝ := threeCandidateValueProfile x1 x2 x3
  let g : ℝ → ℝ := appendixCScaledNoiseDensity f theta
  let μ : Measure (Candidate 1 → ℝ) := w11CandidateNoiseLaw f
  let νcandidate : Measure (Candidate 1 → ℝ) :=
    w11CandidateScoreLaw g value 1
  let ν : Measure RUM3ScoreSpace :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN g x1 x2 x3 rum3Score1 rum3Score2 rum3Score3)
  let raw : (Candidate 1 → ℝ) → Candidate 1 → ℝ :=
    appendixCRawScoreMap value theta
  let e : (Candidate 1 → ℝ) → RUM3ScoreSpace :=
    appendixCScoreSpaceToCandidate.symm ∘ raw
  have hg : Integrable g volume :=
    appendixCScaledNoiseDensity_integrable hf htheta
  have hgnonneg : ∀ z : ℝ, 0 ≤ g z :=
    fun z => (appendixCScaledNoiseDensity_pos htheta hpos z).le
  have hgnorm : ∫⁻ z, ENNReal.ofReal (g z) ∂volume = 1 :=
    appendixCScaledNoiseDensity_normalized f hf hpos hnorm htheta
  letI : IsProbabilityMeasure μ :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm
  letI : IsProbabilityMeasure νcandidate :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization 1 g hg
      hgnonneg hgnorm value 1
  letI : IsProbabilityMeasure ν :=
    paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
      (volume : Measure RUM3ScoreSpace) g x1 x2 x3
      rum3Score1 rum3Score2 rum3Score3 (by simpa [ν, g] using hscoreNorm)
  have hraw : Measurable raw := by
    simpa [raw] using (measurable_appendixCRawScoreMap value theta)
  have hrawMap : μ.map raw = νcandidate := by
    simpa [μ, raw, νcandidate, g] using
      (w11CandidateNoiseLaw_map_rawScore_eq_candidateScoreLaw
        (n := 1) f hf hfmeas hpos hnorm htheta value)
  have hscoreMap : νcandidate.map appendixCScoreSpaceToCandidate.symm = ν := by
    simpa [νcandidate, ν, g, value] using
      (appendixC_candidateScoreDensity_map_to_scoreSpace g x1 x2 x3)
  have he : MeasurePreserving e μ ν := by
    refine ⟨appendixCScoreSpaceToCandidate.symm.measurable.comp hraw, ?_⟩
    calc
      μ.map e = (μ.map raw).map appendixCScoreSpaceToCandidate.symm := by
        exact (Measure.map_map appendixCScoreSpaceToCandidate.symm.measurable hraw).symm
      _ = νcandidate.map appendixCScoreSpaceToCandidate.symm := by rw [hrawMap]
      _ = ν := hscoreMap
  have hcandidateNoTie :
      ∀ᵐ score ∂νcandidate,
        ∀ i j : Candidate 1, i ≠ j → score i ≠ score j := by
    simpa [νcandidate, value] using
      (paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
        (μ := νcandidate) (D := w11CandidateScoreDensityENN g value 1)
        (by rfl) (fun _ : Candidate 1 => 0) (by norm_num : (0 : ℝ) < 1))
  have hrawPreserving : MeasurePreserving raw μ νcandidate := ⟨hraw, hrawMap⟩
  have hsourceNoTie :=
    hrawPreserving.quasiMeasurePreserving.tendsto_ae hcandidateNoTie
  have hsourceRank : Measurable (fun noise => rankByScore (raw noise)) :=
    measurable_rankByScore (fun noise i => raw noise i)
      (fun i => (measurable_pi_apply i).comp hraw)
  have htargetRank : Measurable
      (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3) :=
    rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
  change rankingPMFOfMeasure μ (fun noise => rankByScore (raw noise)) hsourceRank =
    rankingPMFOfMeasure ν
      (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3) htargetRank
  refine appendixC_rankingPMFOfMeasure_eq_of_measurePreserving_ae
    μ ν e he
    (fun noise => rankByScore (raw noise))
    hsourceRank
    (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
    htargetRank ?_
  filter_upwards [hsourceNoTie] with noise hnoise
  have h12 := hnoise (0 : Candidate 1) (1 : Candidate 1) (by decide)
  have h13 := hnoise (0 : Candidate 1) (2 : Candidate 1) (by decide)
  have h23 := hnoise (1 : Candidate 1) (2 : Candidate 1) (by decide)
  have htriple : raw noise =
      threeCandidateValueProfile (raw noise 0) (raw noise 1) (raw noise 2) := by
    funext i
    fin_cases i <;> rfl
  calc
    rankByScore (raw noise) =
        rum3RankByScores (raw noise 0) (raw noise 1) (raw noise 2) := by
      rw [htriple]
      exact appendixC_rankByScore_three_eq_rum3RankByScores_of_noTies
        (raw noise 0) (raw noise 1) (raw noise 2) h12 h13 h23
    _ = rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 (e noise) := by
      simp only [rum3RankByScoreFns, e, Function.comp_apply]
      rw [appendixCScoreSpaceToCandidate_symm_score1,
        appendixCScoreSpaceToCandidate_symm_score2,
        appendixCScoreSpaceToCandidate_symm_score3]

/--
The higher-accuracy literal source ranking law is the contracted ranking law
of the lower-accuracy score-density experiment.  This uses the same base
innovation vector through an explicit measure transport; it does not posit a
coupling or a ranking-law equality.
-/
theorem appendixC_sourceHighRankingPMF_eq_scoreSpaceContracted
    (f : ℝ → ℝ) {thetaH thetaA : ℝ}
    (hf : Integrable f volume) (hfmeas : Measurable f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (x1 x2 x3 : ℝ)
    (hscoreNorm :
      ∫⁻ omega,
          rum3ScoreDensityENN (appendixCScaledNoiseDensity f thetaH) x1 x2 x3
            rum3Score1 rum3Score2 rum3Score3 omega
          ∂(volume : Measure RUM3ScoreSpace) = 1) :
    @paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) thetaA =
      paper_theorem6_normalizedScoreRankingPMF
        (appendixCScaledNoiseDensity f thetaH) x1 x2 x3 hscoreNorm
        (rum3ContractRankByScoreFns (thetaH / thetaA) x1 x2 x3
          rum3Score1 rum3Score2 rum3Score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          (thetaH / thetaA) x1 x2 x3) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  let value : Candidate 1 → ℝ := threeCandidateValueProfile x1 x2 x3
  let gH : ℝ → ℝ := appendixCScaledNoiseDensity f thetaH
  let gA : ℝ → ℝ := appendixCScaledNoiseDensity f thetaA
  let μ : Measure (Candidate 1 → ℝ) := w11CandidateNoiseLaw f
  let νHcandidate : Measure (Candidate 1 → ℝ) :=
    w11CandidateScoreLaw gH value 1
  let νAcandidate : Measure (Candidate 1 → ℝ) :=
    w11CandidateScoreLaw gA value 1
  let νH : Measure RUM3ScoreSpace :=
    (volume : Measure RUM3ScoreSpace).withDensity
      (rum3ScoreDensityENN gH x1 x2 x3 rum3Score1 rum3Score2 rum3Score3)
  let rawH : (Candidate 1 → ℝ) → Candidate 1 → ℝ :=
    appendixCRawScoreMap value thetaH
  let rawA : (Candidate 1 → ℝ) → Candidate 1 → ℝ :=
    appendixCRawScoreMap value thetaA
  let e : (Candidate 1 → ℝ) → RUM3ScoreSpace :=
    appendixCScoreSpaceToCandidate.symm ∘ rawH
  have hgH : Integrable gH volume :=
    appendixCScaledNoiseDensity_integrable hf hthetaH
  have hgA : Integrable gA volume :=
    appendixCScaledNoiseDensity_integrable hf hthetaA
  have hgHnonneg : ∀ z : ℝ, 0 ≤ gH z :=
    fun z => (appendixCScaledNoiseDensity_pos hthetaH hpos z).le
  have hgAnonneg : ∀ z : ℝ, 0 ≤ gA z :=
    fun z => (appendixCScaledNoiseDensity_pos hthetaA hpos z).le
  have hgHnorm : ∫⁻ z, ENNReal.ofReal (gH z) ∂volume = 1 :=
    appendixCScaledNoiseDensity_normalized f hf hpos hnorm hthetaH
  have hgAnorm : ∫⁻ z, ENNReal.ofReal (gA z) ∂volume = 1 :=
    appendixCScaledNoiseDensity_normalized f hf hpos hnorm hthetaA
  letI : IsProbabilityMeasure μ :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm
  letI : IsProbabilityMeasure νHcandidate :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization 1 gH hgH
      hgHnonneg hgHnorm value 1
  letI : IsProbabilityMeasure νAcandidate :=
    w11CandidateScoreLaw_isProbabilityMeasure_of_base_normalization 1 gA hgA
      hgAnonneg hgAnorm value 1
  letI : IsProbabilityMeasure νH :=
    paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
      (volume : Measure RUM3ScoreSpace) gH x1 x2 x3
      rum3Score1 rum3Score2 rum3Score3 (by simpa [νH, gH] using hscoreNorm)
  have hrawH : Measurable rawH := by
    simpa [rawH] using (measurable_appendixCRawScoreMap value thetaH)
  have hrawA : Measurable rawA := by
    simpa [rawA] using (measurable_appendixCRawScoreMap value thetaA)
  have hrawHMap : μ.map rawH = νHcandidate := by
    simpa [μ, rawH, νHcandidate, gH] using
      (w11CandidateNoiseLaw_map_rawScore_eq_candidateScoreLaw
        (n := 1) f hf hfmeas hpos hnorm hthetaH value)
  have hrawAMap : μ.map rawA = νAcandidate := by
    simpa [μ, rawA, νAcandidate, gA] using
      (w11CandidateNoiseLaw_map_rawScore_eq_candidateScoreLaw
        (n := 1) f hf hfmeas hpos hnorm hthetaA value)
  have hscoreHMap : νHcandidate.map appendixCScoreSpaceToCandidate.symm = νH := by
    simpa [νHcandidate, νH, gH, value] using
      (appendixC_candidateScoreDensity_map_to_scoreSpace gH x1 x2 x3)
  have he : MeasurePreserving e μ νH := by
    refine ⟨appendixCScoreSpaceToCandidate.symm.measurable.comp hrawH, ?_⟩
    calc
      μ.map e = (μ.map rawH).map appendixCScoreSpaceToCandidate.symm := by
        exact (Measure.map_map appendixCScoreSpaceToCandidate.symm.measurable hrawH).symm
      _ = νHcandidate.map appendixCScoreSpaceToCandidate.symm := by rw [hrawHMap]
      _ = νH := hscoreHMap
  have hcandidateANoTie :
      ∀ᵐ score ∂νAcandidate,
        ∀ i j : Candidate 1, i ≠ j → score i ≠ score j := by
    simpa [νAcandidate, value] using
      (paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
        (μ := νAcandidate) (D := w11CandidateScoreDensityENN gA value 1)
        (by rfl) (fun _ : Candidate 1 => 0) (by norm_num : (0 : ℝ) < 1))
  have hrawAPreserving : MeasurePreserving rawA μ νAcandidate :=
    ⟨hrawA, hrawAMap⟩
  have hsourceNoTie :=
    hrawAPreserving.quasiMeasurePreserving.tendsto_ae hcandidateANoTie
  have hsourceRank : Measurable (fun noise => rankByScore (rawA noise)) :=
    measurable_rankByScore (fun noise i => rawA noise i)
      (fun i => (measurable_pi_apply i).comp hrawA)
  have htargetRank : Measurable
      (rum3ContractRankByScoreFns (thetaH / thetaA) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3) :=
    rum3ContractRankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
      (thetaH / thetaA) x1 x2 x3
  change rankingPMFOfMeasure μ (fun noise => rankByScore (rawA noise)) hsourceRank =
    rankingPMFOfMeasure νH
      (rum3ContractRankByScoreFns (thetaH / thetaA) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3) htargetRank
  refine appendixC_rankingPMFOfMeasure_eq_of_measurePreserving_ae
    μ νH e he
    (fun noise => rankByScore (rawA noise)) hsourceRank
    (rum3ContractRankByScoreFns (thetaH / thetaA) x1 x2 x3
      rum3Score1 rum3Score2 rum3Score3) htargetRank ?_
  filter_upwards [hsourceNoTie] with noise hnoise
  have h12 := hnoise (0 : Candidate 1) (1 : Candidate 1) (by decide)
  have h13 := hnoise (0 : Candidate 1) (2 : Candidate 1) (by decide)
  have h23 := hnoise (1 : Candidate 1) (2 : Candidate 1) (by decide)
  have htriple : rawA noise =
      threeCandidateValueProfile (rawA noise 0) (rawA noise 1) (rawA noise 2) := by
    funext i
    fin_cases i <;> rfl
  have hc0 : rawA noise 0 =
      rumContractScore (thetaH / thetaA) x1 (rawH noise 0) := by
    simpa [rawA, rawH, value, threeCandidateValueProfile] using
      (appendixCRawScoreMap_eq_contract hthetaA hthetaH value noise
        (0 : Candidate 1))
  have hc1 : rawA noise 1 =
      rumContractScore (thetaH / thetaA) x2 (rawH noise 1) := by
    simpa [rawA, rawH, value, threeCandidateValueProfile] using
      (appendixCRawScoreMap_eq_contract hthetaA hthetaH value noise
        (1 : Candidate 1))
  have hc2 : rawA noise 2 =
      rumContractScore (thetaH / thetaA) x3 (rawH noise 2) := by
    simpa [rawA, rawH, value, threeCandidateValueProfile] using
      (appendixCRawScoreMap_eq_contract hthetaA hthetaH value noise
        (2 : Candidate 1))
  calc
    rankByScore (rawA noise) =
        rum3RankByScores (rawA noise 0) (rawA noise 1) (rawA noise 2) := by
      rw [htriple]
      exact appendixC_rankByScore_three_eq_rum3RankByScores_of_noTies
        (rawA noise 0) (rawA noise 1) (rawA noise 2) h12 h13 h23
    _ = rum3ContractRankByScoreFns (thetaH / thetaA) x1 x2 x3
        rum3Score1 rum3Score2 rum3Score3 (e noise) := by
      simp only [rum3ContractRankByScoreFns, e, Function.comp_apply]
      rw [appendixCScoreSpaceToCandidate_symm_score1,
        appendixCScoreSpaceToCandidate_symm_score2,
        appendixCScoreSpaceToCandidate_symm_score3]
      rw [hc0, hc1, hc2]

/--
Appendix C, Theorem 6 at the literal source RUM surface.  Starting from iid
innovations with density `f`, it compares the two actual source laws induced
by `x_i + epsilon_i / theta`; the score-density contraction law is derived
inside the proof by the Jacobian and finite-product transports above.
-/
theorem appendixC_source_rawRUM_theorem6_prefersWeakerCompetition
    (f : ℝ → ℝ) {thetaH thetaA : ℝ}
    (hfmeas : Measurable f) (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (x1 x2 x3 : ℝ) (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) thetaA)
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) thetaH)
      (threeCandidateValueProfile x1 x2 x3) := by
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  have hf_integrable : Integrable f volume :=
    appendixC_integrable_of_normalized_positive_density hfmeas hpos hnorm
  let gH : ℝ → ℝ := appendixCScaledNoiseDensity f thetaH
  let t : ℝ := thetaH / thetaA
  have hgH_integrable : Integrable gH volume :=
    appendixCScaledNoiseDensity_integrable hf_integrable hthetaH
  have hgH_nonneg : ∀ z : ℝ, 0 ≤ gH z :=
    fun z => (appendixCScaledNoiseDensity_pos hthetaH hpos z).le
  have hgH_norm : ∫⁻ z, ENNReal.ofReal (gH z) ∂volume = 1 :=
    appendixCScaledNoiseDensity_normalized f hf_integrable hpos hnorm hthetaH
  have hscoreNorm :
      ∫⁻ omega,
          rum3ScoreDensityENN gH x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 omega
          ∂(volume : Measure RUM3ScoreSpace) = 1 :=
    appendixC_candidateScoreDensity_normalized gH hgH_integrable hgH_nonneg
      hgH_norm x1 x2 x3
  have ht0 : 0 ≤ t := le_of_lt (div_pos hthetaH hthetaA)
  have htlt1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hthetaA).mpr hthetaHA
  have ht1 : t ≤ 1 := le_of_lt htlt1
  have hscore :=
    paper_theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one
      gH x1 x2 x3 t (value := threeCandidateValueProfile x1 x2 x3)
      (by rfl) (by rfl) (by rfl)
      (appendixCScaledNoiseDensity_measurable hfmeas thetaH)
      (appendixCScaledNoiseDensity_strictlyWellOrdered hf hthetaH)
      (appendixCScaledNoiseDensity_pos hthetaH hpos)
      hscoreNorm ht0 ht1 htlt1 hx12 hx23
  have hraw := appendixC_sourceRawRankingPMF_eq_scoreSpaceRaw
    f hf_integrable hfmeas hpos hnorm hthetaH x1 x2 x3 hscoreNorm
  have hcontract := appendixC_sourceHighRankingPMF_eq_scoreSpaceContracted
    f hf_integrable hfmeas hpos hnorm hthetaH hthetaHA x1 x2 x3 hscoreNorm
  rw [hcontract, hraw]
  exact hscore

/--
Source-facing variant of the raw-RUM Theorem 6 endpoint.  A probability
density's nonnegativity is the only density-sign premise: strict
well-ordering derives the pointwise positivity needed by the continuous
score-density argument.
-/
theorem appendixC_source_rawRUM_theorem6_prefersWeakerCompetition_of_nonneg
    (f : ℝ → ℝ) {thetaH thetaA : ℝ}
    (hfmeas : Measurable f) (hf : StrictlyWellOrderedNoise f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnorm : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (x1 x2 x3 : ℝ) (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) thetaA)
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnorm)
        (threeCandidateValueProfile x1 x2 x3) thetaH)
      (threeCandidateValueProfile x1 x2 x3) := by
  exact appendixC_source_rawRUM_theorem6_prefersWeakerCompetition
    f hfmeas hf (hf.pos_of_nonneg hnonneg) hnorm hthetaH hthetaHA
    x1 x2 x3 hx12 hx23

end KR21Monoculture
