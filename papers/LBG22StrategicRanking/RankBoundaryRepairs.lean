import LBG22StrategicRanking.IndependentSkillUtility
import LBG22StrategicRanking.GammaRank

/-!
# Reward cutoffs and off-equilibrium score gaps

Inclusive numeric-percentile admission gives the higher reward at a rank
cutoff even when the score lies in an empty gap. The following example checks
that implementation's profitable deviation using the population contour
measure. It is not a refutation of the author's clarified stated model, which
uses the known score-priority order at the actual admission boundary.
`rankBoundary_gap_not_scorePriorityAboveCutoff` in `OrderBoundaryEquilibrium`
checks that the gap deviation is not admitted by that order boundary.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Counterfactual rank under the fixed score population, with the source's
tie-prefix construction at atoms. It agrees with the on-profile rank at the
applicant's current score. -/
noncomputable def counterfactualTieBrokenRank
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (score tie : α → ℝ)
    (x : α) (newScore : ℝ) : ℝ :=
  (μ {y | score y < newScore ∨ score y = newScore ∧ tie y ≤ tie x}).toReal

theorem counterfactualTieBrokenRank_at_current_score
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (score tie : α → ℝ) (x : α) :
    counterfactualTieBrokenRank μ score tie x (score x) = tieBrokenRank μ score tie x := rfl

/-- Half the population is admitted deterministically. The printed policy
awards the high reward at the cutoff itself. -/
noncomputable def rankBoundaryPolicy : TwoLevelPolicy where
  rho := 1 / 2
  c := 1 / 2
  rho_pos := by norm_num
  rho_lt_one := by norm_num
  c_pos := by norm_num
  c_le_capacity_complement := by norm_num

/-- The two-level source profile for linear production, quadratic cost, and
uniform skill. Its value at the single cutoff rank is immaterial to the
score distribution and is set to the low-band effort. -/
noncomputable def rankBoundaryEffort (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 0 else (1 / 2) / t

noncomputable def rankBoundaryScore (t : ℝ) : ℝ := rankBoundaryEffort t * t

theorem rankBoundaryScore_eq (t : ℝ) :
    rankBoundaryScore t = if t ≤ 1 / 2 then 0 else 1 / 2 := by
  unfold rankBoundaryScore rankBoundaryEffort
  split_ifs with ht
  · simp
  · exact div_mul_cancel₀ _ (by linarith : t ≠ 0)

/-- The source policy admits any rank at least one half with probability one. -/
theorem rankBoundaryPolicy_admission {r : ℝ} (hr : 1 / 2 ≤ r) :
    twoLevelAdmission rankBoundaryPolicy r = 1 := by
  change (if (1 / 2 : ℝ) ≤ r then twoLevelHighProb rankBoundaryPolicy else 0) = 1
  rw [if_pos hr]
  norm_num [rankBoundaryPolicy, twoLevelHighProb]

theorem rankBoundaryPolicy_admission_le_one (r : ℝ) :
    twoLevelAdmission rankBoundaryPolicy r ≤ 1 := by
  unfold twoLevelAdmission
  split_ifs <;> norm_num [rankBoundaryPolicy, twoLevelHighProb]

theorem unitRankMeasure_Iic_half : (unitRankMeasure (Iic (1 / 2 : ℝ))).toReal = 1 / 2 := by
  have hset : Iic (1 / 2 : ℝ) ∩ Ioc 0 1 = Ioc 0 (1 / 2 : ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hx, hl, _⟩
      exact ⟨hl, hx⟩
    · rintro ⟨hl, hx⟩
      exact ⟨hx, hl, by linarith⟩
  rw [unitRankMeasure, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Ioc]
  norm_num

/-- Every score strictly inside the gap `(0,1/2)` has rank exactly `1/2`,
independently of the tie key: no population member has that score. -/
theorem rankBoundary_gap_rank (tie : ℝ → ℝ) (t : ℝ) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) :
    counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t v = 1 / 2 := by
  have hset : {y | rankBoundaryScore y < v ∨
      rankBoundaryScore y = v ∧ tie y ≤ tie t} = Iic (1 / 2 : ℝ) := by
    ext y
    simp only [mem_setOf_eq, mem_Iic]
    rw [rankBoundaryScore_eq]
    by_cases hy : y ≤ 1 / 2
    · rw [if_pos hy]
      exact iff_of_true (Or.inl hv) hy
    · rw [if_neg hy]
      constructor
      · rintro (h | ⟨h, _⟩) <;> exfalso <;> linarith
      · intro h
        exact (hy h).elim
  unfold counterfactualTieBrokenRank
  rw [hset, unitRankMeasure_Iic_half]

/-- The high-band effort in the example is exactly the actual compact-inverse
source formula, not a separately supplied equilibrium-shaped profile. -/
theorem rankBoundaryEffort_eq_source {t : ℝ} (ht : t ∈ Ioc (1 / 2 : ℝ) 1) :
    rankBoundaryEffort t = sourceTwoLevelEffort (fun e => e ^ 2) id id 1 (1 / 2) (1 / 2) t := by
  have hpinv : effortIntervalInverse (fun e : ℝ => e ^ 2) 1 1 = 1 := by
    have hm : StrictMonoOn (fun e : ℝ => e ^ 2) (Icc 0 1) :=
      fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0)
    simpa using hm.injOn.leftInvOn_invFunOn (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have ha : sourceScoreScale (fun e => e ^ 2) id 1 (1 / 2) (1 / 2) = 1 := by
    norm_num [sourceScoreScale, hpinv]
  have he := sourceTwoLevelEffort_uniform_eq_inverse (by norm_num : (0 : ℝ) ≤ 1)
    continuousOn_id (by rfl : id (0 : ℝ) = 0)
    (show sourceScoreScale (fun e => e ^ 2) id 1 (1 / 2) (1 / 2) ∈ Ioc (0 : ℝ) (id 1) by
      rw [ha]; norm_num) (by norm_num : (0 : ℝ) < 1 / 2) ⟨ht.1.le, ht.2⟩
  rw [he, ha]
  have hz : (1 : ℝ) * (1 / 2) / t ∈ Icc (id 0) (id 1) := by
    have htpos : 0 < t := by linarith [ht.1]
    exact ⟨(div_pos (by norm_num) htpos).le, (div_le_one htpos).mpr (by linarith [ht.1])⟩
  have hi := (effortIntervalInverse_spec (by norm_num : (0 : ℝ) ≤ 1) continuousOn_id hz).2
  simpa only [rankBoundaryEffort, if_neg (not_le.mpr ht.1), id_eq, one_mul] using hi.symm

/-- Every positive-mass high-band applicant can halve the prescribed effort,
land in the score gap, retain the high reward, and strictly reduce cost.
Consequently the printed two-level effort profile is not a best response
under the printed inclusive-cutoff/CDF conventions, for any tie function. -/
theorem rankBoundary_source_profile_profitable_deviation
    (tie : ℝ → ℝ) {t : ℝ} (ht : t ∈ Ioc (1 / 2 : ℝ) 1) :
    ∃ d : ℝ, 0 ≤ d ∧
      twoLevelAdmission rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t
          (rankBoundaryScore t)) - (rankBoundaryEffort t) ^ 2 <
      twoLevelAdmission rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t (d * t)) - d ^ 2 := by
  let d := (1 / 4 : ℝ) / t
  have htpos : 0 < t := by linarith [ht.1]
  have hepos : 0 < rankBoundaryEffort t := by
    rw [rankBoundaryEffort, if_neg (not_le.mpr ht.1)]
    exact div_pos (by norm_num) htpos
  have hdpos : 0 < d := div_pos (by norm_num) htpos
  have hde : d < rankBoundaryEffort t := by
    rw [rankBoundaryEffort, if_neg (not_le.mpr ht.1)]
    exact (div_lt_div_iff_of_pos_right htpos).mpr (by norm_num)
  have hscore : d * t = 1 / 4 := div_mul_cancel₀ _ htpos.ne'
  have hrank : counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t (d * t) = 1 / 2 := by
    rw [hscore]
    exact rankBoundary_gap_rank tie t (by norm_num) (by norm_num)
  have hreward := rankBoundaryPolicy_admission_le_one
    (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t (rankBoundaryScore t))
  refine ⟨d, hdpos.le, ?_⟩
  rw [hrank, rankBoundaryPolicy_admission (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)]
  nlinarith

/-- Failure holds on a set of population mass one half, so excluding a null
set of cutoff applicants cannot rescue the displayed profile. -/
theorem rankBoundary_source_profile_not_bestResponseAE (tie : ℝ → ℝ) :
    ¬ ∀ᵐ t ∂unitRankMeasure, ∀ d : ℝ, 0 ≤ d →
      twoLevelAdmission rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t (d * t)) - d ^ 2 ≤
      twoLevelAdmission rankBoundaryPolicy
        (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t
          (rankBoundaryScore t)) - (rankBoundaryEffort t) ^ 2 := by
  intro h
  have hnull : unitRankMeasure (Ioc (1 / 2 : ℝ) 1) = 0 := by
    apply measure_mono_null _ (ae_iff.mp h)
    intro t ht hbest
    obtain ⟨d, hd, hprofit⟩ := rankBoundary_source_profile_profitable_deviation tie ht
    exact (not_lt_of_ge (hbest d hd)) hprofit
  have hsub : Ioc (1 / 2 : ℝ) 1 ⊆ Ioc 0 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  rw [unitRankMeasure, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub, Real.volume_Ioc] at hnull
  norm_num at hnull

/-- The lower-reward convention at an exact rank cutoff. This changes only
one rank value, but it changes the incentives of deviations into score gaps. -/
noncomputable def twoLevelAdmissionLowerBoundary (P : TwoLevelPolicy) (r : ℝ) : ℝ :=
  if P.c < r then twoLevelHighProb P else 0

/-- The two cutoff conventions agree at almost every uniform rank, without
asserting that their counterfactual ranking games are equivalent. -/
theorem twoLevelAdmissionLowerBoundary_ae_eq (P : TwoLevelPolicy) :
    twoLevelAdmissionLowerBoundary P =ᵐ[unitRankMeasure] twoLevelAdmission P := by
  have hne : ∀ᵐ r ∂unitRankMeasure, r ≠ P.c := (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne P.c
  filter_upwards [hne] with r hr
  unfold twoLevelAdmissionLowerBoundary twoLevelAdmission
  by_cases hlt : P.c < r
  · rw [if_pos hlt, if_pos hlt.le]
  · have hnle : ¬ P.c ≤ r := fun h => hlt (lt_of_le_of_ne h (Ne.symm hr))
    rw [if_neg hlt, if_neg hnle]

/-- With the lower-reward cutoff convention, every score inside the same
off-equilibrium gap receives the lower reward, eliminating this deviation's
source of free admission. A general equilibrium theorem is a separate claim. -/
theorem rankBoundary_gap_lower_reward (tie : ℝ → ℝ) (t : ℝ) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) :
    twoLevelAdmissionLowerBoundary rankBoundaryPolicy
      (counterfactualTieBrokenRank unitRankMeasure rankBoundaryScore tie t v) = 0 := by
  rw [rankBoundary_gap_rank tie t hv hvhalf]
  unfold twoLevelAdmissionLowerBoundary
  exact if_neg (lt_irrefl (1 / 2 : ℝ))

end LBG22StrategicRanking
