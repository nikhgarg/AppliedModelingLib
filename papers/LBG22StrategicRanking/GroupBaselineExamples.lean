import LBG22StrategicRanking.PopulationRankPrimitiveRepairs
import LBG22StrategicRanking.GroupWelfarePrimitiveRepairs
import LBG22StrategicRanking.ThreeLevelPrimitiveRepairs

/-!
# Two-group equilibria with baseline qualification

Latent skill is uniform on `[0,1]`, and environment factors are two and one.
Cost is quadratic and production is `1+e`. The population cutoff associated
with effective skill `a` is `3*a/4` for `0<a≤1`. An admitted reward `δ²`
supports a score threshold `(1+δ)*a`, with baseline clipping above it.
-/

namespace LBG22StrategicRanking.BaselineGroupExample

open Set MeasureTheory ProbabilityTheory

noncomputable def effectiveSkill : Bool × ℝ → ℝ := sourceEnvironmentSkill (fun t => t) 2 1

theorem effectiveSkill_meas : Measurable effectiveSkill := sourceEnvironmentSkill_measurable continuous_id.continuousOn

theorem effectiveSkill_pos_ae : ∀ᵐ x ∂sourceTwoGroupMeasure, 0 < effectiveSkill x :=
  sourceEnvironmentSkill_positive_ae (fun _ _ _ _ h => h) (by norm_num) (by norm_num) (by norm_num)

theorem effectiveSkill_eq {x : Bool × ℝ} (hx : x.2 ∈ Icc (0 : ℝ) 1) :
    effectiveSkill x = (if x.1 then 2 else 1) * x.2 :=
  sourceEnvironmentSkill_eq_on_support hx

theorem mixtureCDF_at {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    sourceEnvironmentCDF (fun t => t) 2 1 a = 3 * a / 4 := by
  rw [sourceEnvironmentCDF_eq_mixture (skill := fun t : ℝ => t) continuous_id.continuousOn (by norm_num) (by norm_num)]
  rw [sourceSkillCDF_at_quantile (skill := fun t : ℝ => t) continuous_id.continuousOn (fun _ _ _ _ h => h)
      (show a / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩), div_one,
    sourceSkillCDF_at_quantile (skill := fun t : ℝ => t) continuous_id.continuousOn (fun _ _ _ _ h => h) ha]
  ring

theorem lower_group_mass {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    sourceTwoGroupMeasure.real {x | effectiveSkill x ≤ a} = 3 * a / 4 := by
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure) effectiveSkill_meas.aemeasurable
  have h := mixtureCDF_at ha
  change cdf (Measure.map effectiveSkill sourceTwoGroupMeasure) a = _ at h
  rw [cdf_eq_real, measureReal_def, Measure.map_apply effectiveSkill_meas measurableSet_Iic] at h
  exact h

/-- The explicit best-response effort, including baseline qualification. -/
noncomputable def effortAt (a delta s : ℝ) : ℝ :=
  if s ≤ a then 0 else max ((1 + delta) * a / s - 1) 0

noncomputable def scoreAt (a delta s : ℝ) : ℝ :=
  if s ≤ a then s else max ((1 + delta) * a) s

noncomputable def effort (a delta : ℝ) (x : Bool × ℝ) : ℝ := effortAt a delta (effectiveSkill x)
noncomputable def score (a delta : ℝ) (x : Bool × ℝ) : ℝ := scoreAt a delta (effectiveSkill x)

theorem score_meas (a delta : ℝ) : Measurable (score a delta) :=
  effectiveSkill_meas.ite (measurableSet_le effectiveSkill_meas measurable_const)
    (measurable_const.max effectiveSkill_meas)

theorem effortAt_properties {a delta s : ℝ} (hd : 0 ≤ delta) (hs : 0 < s) :
    0 ≤ effortAt a delta s ∧ effortAt a delta s ≤ delta ∧
      (1 + effortAt a delta s) * s = scoreAt a delta s := by
  by_cases hsa : s ≤ a
  · simp only [effortAt, scoreAt, if_pos hsa, add_zero, one_mul, le_refl, and_true, true_and]
    exact hd
  · have has : a ≤ s := (lt_of_not_ge hsa).le
    simp only [effortAt, scoreAt, if_neg hsa]
    have hbound : (1 + delta) * a / s - 1 ≤ delta := by
      have h := (div_le_iff₀ hs).mpr (mul_le_mul_of_nonneg_left has (by linarith : 0 ≤ 1 + delta))
      linarith
    refine ⟨?_, ?_, ?_⟩
    · exact le_max_right _ _
    · exact max_le hbound hd
    · by_cases htop : (1 + delta) * a ≤ s
      · have hzero : (1 + delta) * a / s - 1 ≤ 0 := by
          have h := (div_le_one hs).mpr htop
          linarith
        rw [max_eq_right hzero, max_eq_right htop]
        ring
      · have hpos : 0 ≤ (1 + delta) * a / s - 1 := by
          have h := (one_le_div hs).mpr (le_of_not_ge htop)
          linarith
        rw [max_eq_left hpos, max_eq_left (le_of_not_ge htop)]
        field_simp
        ring

theorem effortAt_zero_of_threshold_le {a delta s : ℝ} (hs : 0 < s)
    (hthreshold : (1 + delta) * a ≤ s) : effortAt a delta s = 0 := by
  unfold effortAt
  split
  · rfl
  · apply max_eq_right
    have h := (div_le_one hs).mpr hthreshold
    linarith

/-- All nonnegative deviations are unprofitable against the explicit
score threshold, both below and above the effective-skill cutoff. -/
theorem scoreMenu_bestResponse {a delta s d : ℝ}
    (ha : 0 < a) (hdelta : 0 ≤ delta) (hs : 0 < s) (hd : 0 ≤ d) :
    (if (1 + delta) * a ≤ (1 + d) * s then delta ^ 2 else 0) - d ^ 2 ≤
      (if a < s then delta ^ 2 else 0) - (effortAt a delta s) ^ 2 := by
  have he := effortAt_properties (a := a) hdelta hs
  by_cases hsa : s ≤ a
  · rw [if_neg (not_lt_of_ge hsa)]
    simp only [effortAt, if_pos hsa]
    split_ifs with hreach
    · have hprod : (1 + delta) * a ≤ (1 + d) * a :=
        hreach.trans (mul_le_mul_of_nonneg_left hsa (by linarith))
      have hdd : delta ≤ d := by
        by_contra hn
        have h := mul_lt_mul_of_pos_right (show 1 + d < 1 + delta by linarith) ha
        exact (not_lt_of_ge hprod) h
      nlinarith [mul_self_le_mul_self hdelta hdd]
    · nlinarith [sq_nonneg d]
  · rw [if_pos (lt_of_not_ge hsa)]
    split_ifs with hreach
    · have hed : effortAt a delta s ≤ d := by
        unfold effortAt
        rw [if_neg hsa]
        apply max_le _ hd
        have h := (div_le_iff₀ hs).mpr hreach
        linarith
      nlinarith [mul_self_le_mul_self he.1 hed]
    · nlinarith [mul_self_le_mul_self he.1 he.2.1, sq_nonneg d]

/-- Capacity equals the admitted reward times its population share. -/
noncomputable def capacity (a delta : ℝ) : ℝ := delta ^ 2 * (1 - 3 * a / 4)

theorem capacity_feasible {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : delta ∈ Ioc (0 : ℝ) 1) :
    0 < capacity a delta ∧ 3 * a / 4 ∈ Ioc (0 : ℝ) (1 - capacity a delta) := by
  have hden : 0 < 1 - 3 * a / 4 := by linarith [ha.2]
  have hd2 : delta ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self hd.1.le hd.2]
  have hbound := mul_le_mul_of_nonneg_right hd2 hden.le
  refine ⟨mul_pos (sq_pos_of_pos hd.1) hden, ?_, ?_⟩
  · linarith [ha.1]
  · unfold capacity
    linarith

theorem reward_eq {a delta r : ℝ} (ha : a ≤ 1) :
    sourceTwoLevelReward (capacity a delta) (3 * a / 4)
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i) r).val =
        if 3 * a / 4 < r then delta ^ 2 else 0 := by
  have hden : 1 - 3 * a / 4 ≠ 0 := by linarith
  have hq : capacity a delta / (1 - 3 * a / 4) = delta ^ 2 := by
    unfold capacity
    exact mul_div_cancel_right₀ _ hden
  rw [finiteLowerRankBand_twoLevel]
  split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero, hq]

theorem rank_realization {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : 0 < delta)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    (∀ x v, v < (1 + delta) * a →
      counterfactualTieBrokenRank sourceTwoGroupMeasure (score a delta) tie x v ≤ 3 * a / 4) ∧
      (∀ᵐ x ∂sourceTwoGroupMeasure,
        3 * a / 4 < tieBrokenRank sourceTwoGroupMeasure (score a delta) tie x ↔ a < effectiveSkill x) := by
  haveI := noAtoms_map_sourceTwoGroup_of_injOn htie hinj
  apply sourcePopulation_twoLevelRank_of_score_separation sourceTwoGroupMeasure
    (score_meas a delta) htie (lower_group_mass ⟨ha.1.le, ha.2⟩)
    (show a < (1 + delta) * a by nlinarith [mul_pos hd ha.1])
  apply ae_of_all
  intro x
  constructor
  · intro hlow
    change scoreAt a delta (effectiveSkill x) ≤ a
    simpa only [scoreAt, if_pos hlow] using hlow
  · intro hhigh
    change (1 + delta) * a ≤ scoreAt a delta (effectiveSkill x)
    rw [scoreAt, if_neg (not_le_of_gt hhigh)]
    exact le_max_left _ _

theorem actual_admission {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : 0 < delta)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      sourceTwoLevelReward (capacity a delta) (3 * a / 4)
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
          (tieBrokenRank sourceTwoGroupMeasure (score a delta) tie x)).val =
            if a < effectiveSkill x then delta ^ 2 else 0 := by
  filter_upwards [(rank_realization ha hd htie hinj).2] with x hx
  rw [reward_eq ha.2]
  simp only [hx]

/-- A source-admissible two-level equilibrium for every positive cutoff
skill at most one and every admitted reward `δ²` in `(0,1]`. The actual
population law, all nonnegative deviations, and both rank bands are proved. -/
theorem source_equilibrium {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : delta ∈ Ioc (0 : ℝ) 1)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    0 < capacity a delta ∧ 3 * a / 4 ∈ Ioc (0 : ℝ) (1 - capacity a delta) ∧
      (∀ᵐ x ∂sourceTwoGroupMeasure,
        SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) (fun e => 1 + e)
          effectiveSkill (score a delta) tie
          (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
          (sourceTwoLevelReward (capacity a delta) (3 * a / 4)) x (effort a delta x)) := by
  have hfeasible := capacity_feasible ha hd
  have hrank := rank_realization ha hd.1 htie hinj
  have hcounter (x : Bool × ℝ) (v : ℝ) :
      sourceTwoLevelReward (capacity a delta) (3 * a / 4)
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
          (counterfactualTieBrokenRank sourceTwoGroupMeasure (score a delta) tie x v)).val ≤
            if (1 + delta) * a ≤ v then delta ^ 2 else 0 := by
    rw [reward_eq ha.2]
    by_cases hv : (1 + delta) * a ≤ v
    · rw [if_pos hv]
      split <;> nlinarith [sq_nonneg delta]
    · rw [if_neg hv, if_neg (not_lt_of_ge (hrank.1 x v (lt_of_not_ge hv)))]
  refine ⟨hfeasible.1, hfeasible.2, ?_⟩
  filter_upwards [actual_admission ha hd.1 htie hinj, effectiveSkill_pos_ae] with x hx hs
  have he := effortAt_properties (a := a) hd.1.le hs
  refine ⟨he.1, he.2.2.symm, ?_⟩
  intro d hde
  rw [hx]
  exact (sub_le_sub_right (hcounter x ((1 + d) * effectiveSkill x)) (d ^ 2)).trans
    (scoreMenu_bestResponse ha.1 hd.1.le hs hde)

theorem groupThreshold_eq {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (group : Bool) :
    sourceGroupThreshold (fun t => t) 2 1 group (3 * a / 4) = if group then a / 2 else a := by
  have h := sourceGroupThreshold_at_mixtureCDF (skill := fun t : ℝ => t) continuous_id.continuousOn
    (fun _ _ _ _ h => h) (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1) group (z := a)
  rw [mixtureCDF_at ha] at h
  cases group
  · simpa only [Bool.false_eq_true, ↓reduceIte, div_one,
      sourceSkillCDF_at_quantile (skill := fun t : ℝ => t) continuous_id.continuousOn (fun _ _ _ _ h => h) ha] using h
  · simpa only [↓reduceIte, sourceSkillCDF_at_quantile (skill := fun t : ℝ => t)
      continuous_id.continuousOn (fun _ _ _ _ h => h)
        (show a / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)] using h

theorem effort_high_zero {a delta t : ℝ} (ha : 0 < a) (hd : 0 ≤ delta)
    (ht : t ∈ Ioc ((1 + delta) * a) 1) (group : Bool) : effort a delta (group, t) = 0 := by
  have hT : 0 < (1 + delta) * a := mul_pos (by linarith) ha
  have ht0 := hT.trans ht.1
  have hs : 0 < effectiveSkill (group, t) := by
    rw [effectiveSkill_eq ⟨ht0.le, ht.2⟩]
    exact mul_pos (by cases group <;> norm_num) ht0
  apply effortAt_zero_of_threshold_le hs
  rw [effectiveSkill_eq ⟨ht0.le, ht.2⟩]
  cases group <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul] <;> linarith [ht.1]

/-- The actual source welfare gap for this constructed equilibrium. -/
noncomputable def welfareGap (a delta : ℝ) (tie : Bool × ℝ → ℝ) (t : ℝ) : ℝ :=
  sourceActualGroupWelfareGap (fun e => e ^ 2) (effort a delta) (score a delta) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
    (sourceTwoLevelReward (capacity a delta) (3 * a / 4)) t

theorem rank_ge_of_score_above_prefix {a delta z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1)
    (tie : Bool × ℝ → ℝ) (x : Bool × ℝ)
    (hx : max ((1 + delta) * a) z < score a delta x) :
    3 * z / 4 ≤ tieBrokenRank sourceTwoGroupMeasure (score a delta) tie x := by
  have hsubset : {y | effectiveSkill y ≤ z} ⊆ tieBrokenLowerContour (score a delta) tie x := by
    intro y hy
    left
    apply lt_of_le_of_lt _ hx
    change scoreAt a delta (effectiveSkill y) ≤ max ((1 + delta) * a) z
    unfold scoreAt
    split
    · exact hy.trans (le_max_right _ _)
    · exact max_le_max_left _ hy
  have h := ENNReal.toReal_mono
    (measure_ne_top sourceTwoGroupMeasure (tieBrokenLowerContour (score a delta) tie x))
    (measure_mono hsubset)
  change sourceTwoGroupMeasure.real {y | effectiveSkill y ≤ z} ≤
    tieBrokenRank sourceTwoGroupMeasure (score a delta) tie x at h
  rwa [lower_group_mass hz] at h

/-- Baseline qualification above the score threshold gives zero welfare
gap pointwise, for every tie key. A positive-mass skill prefix lies strictly
below each applicant's score, so no exceptional rank-cutoff tie occurs here. -/
theorem welfareGap_zero_above_threshold {a delta t : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) (hd : 0 < delta)
    (tie : Bool × ℝ → ℝ) (ht : t ∈ Ioc ((1 + delta) * a) 1) : welfareGap a delta tie t = 0 := by
  have haT : a < (1 + delta) * a := by nlinarith [mul_pos hd ha.1]
  have hat := haT.trans ht.1
  have ht0 := ha.1.trans hat
  have hz : (a + t) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2, ht.2]⟩
  have hreward (group : Bool) :
      sourceTwoLevelReward (capacity a delta) (3 * a / 4)
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
          (tieBrokenRank sourceTwoGroupMeasure (score a delta) tie (group, t))).val = delta ^ 2 := by
    have hskill : t ≤ effectiveSkill (group, t) := by
      rw [effectiveSkill_eq ⟨ht0.le, ht.2⟩]
      cases group <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul] <;> linarith
    have hscore : t ≤ score a delta (group, t) := by
      have hp := (effortAt_properties (a := a) hd.le (ht0.trans_le hskill)).2.2
      change (1 + effort a delta (group, t)) * effectiveSkill (group, t) = score a delta (group, t) at hp
      rw [effort_high_zero ha.1 hd.le ht group, add_zero, one_mul] at hp
      exact hskill.trans_eq hp
    have hprefix := rank_ge_of_score_above_prefix hz tie (group, t)
      ((max_lt ht.1 (by linarith : (a + t) / 2 < t)).trans_le hscore)
    have hrank : 3 * a / 4 < tieBrokenRank sourceTwoGroupMeasure (score a delta) tie (group, t) := by
      linarith
    rw [reward_eq ha.2, if_pos hrank]
  unfold welfareGap sourceActualGroupWelfareGap sourceActualGroupWelfare
  rw [hreward true, hreward false, effort_high_zero ha.1 hd.le ht true, effort_high_zero ha.1 hd.le ht false]
  ring

/-- Above the baseline-qualification threshold, both groups receive the
same positive admission reward and incur zero cost. This is an assertion
about actual population ranks, not only the displayed score menu. -/
theorem zero_gap_region {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : 0 < delta)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc ((1 + delta) * a) 1 →
      sourceGroupThreshold (fun t => t) 2 1 false (3 * a / 4) < t ∧
        sourceTwoLevelReward (capacity a delta) (3 * a / 4)
          (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
            (tieBrokenRank sourceTwoGroupMeasure (score a delta) tie (true, t))).val = delta ^ 2 ∧
        sourceTwoLevelReward (capacity a delta) (3 * a / 4)
          (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
            (tieBrokenRank sourceTwoGroupMeasure (score a delta) tie (false, t))).val = delta ^ 2 ∧
        welfareGap a delta tie t = 0 := by
  have hadmission := actual_admission ha hd htie hinj
  filter_upwards [sourceTwoGroupMeasure_ae_branch hadmission true,
    sourceTwoGroupMeasure_ae_branch hadmission false] with t hA hB
  intro ht
  have haT : a < (1 + delta) * a := by nlinarith [mul_pos hd ha.1]
  have hat := haT.trans ht.1
  have ht0 := ha.1.trans hat
  have hsA : a < effectiveSkill (true, t) := by
    rw [effectiveSkill_eq ⟨ht0.le, ht.2⟩]
    simp only [↓reduceIte]
    linarith
  have hsB : a < effectiveSkill (false, t) := by
    rw [effectiveSkill_eq ⟨ht0.le, ht.2⟩]
    simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using hat
  rw [if_pos hsA] at hA
  rw [if_pos hsB] at hB
  refine ⟨?_, hA, hB, ?_⟩
  · simpa only [groupThreshold_eq ⟨ha.1.le, ha.2⟩ false, Bool.false_eq_true, ↓reduceIte] using hat
  · unfold welfareGap sourceActualGroupWelfareGap sourceActualGroupWelfare
    rw [hA, hB, effort_high_zero ha.1 hd.le ht true, effort_high_zero ha.1 hd.le ht false]
    ring

/-- The region of admitted applicants with zero welfare gap has positive
population mass whenever the score threshold is below maximum latent skill. -/
theorem zero_gap_positive_mass {a delta : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hd : 0 < delta)
    (hT : (1 + delta) * a < 1)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    0 < unitRankMeasure {t | sourceGroupThreshold (fun t => t) 2 1 false (3 * a / 4) < t ∧
      welfareGap a delta tie t = 0} := by
  have hT0 : 0 < (1 + delta) * a := mul_pos (by linarith) ha.1
  have hmass : 0 < unitRankMeasure (Ioc ((1 + delta) * a) 1) := by
    rw [unitRankMeasure, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc ((1 + delta) * a) 1 ⊆ Ioc (0 : ℝ) 1 from
        fun _ ht => ⟨hT0.trans ht.1, ht.2⟩), Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hT)
  have hsubset : Ioc ((1 + delta) * a) 1 ≤ᵐ[unitRankMeasure]
      {t | sourceGroupThreshold (fun t => t) 2 1 false (3 * a / 4) < t ∧ welfareGap a delta tie t = 0} := by
    filter_upwards [zero_gap_region ha hd htie hinj] with t ht hmem
    exact ⟨(ht hmem).1, (ht hmem).2.2.2⟩
  exact hmass.trans_le (measure_mono_ae hsubset)

/-- The strict-high-region welfare claim fails even almost everywhere
for this source-admissible family. Its nonnegative counterpart and exact
baseline equality case remain valid. -/
theorem strict_high_gap_claim_fails {a delta : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) (hd : delta ∈ Ioc (0 : ℝ) 1) (hT : (1 + delta) * a < 1)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    0 < capacity a delta ∧ 3 * a / 4 ∈ Ioc (0 : ℝ) (1 - capacity a delta) ∧
      (∀ᵐ x ∂sourceTwoGroupMeasure,
        SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) (fun e => 1 + e)
          effectiveSkill (score a delta) tie
          (fun i : Fin 2 => sourceTwoLevelCutoff (3 * a / 4) i)
          (sourceTwoLevelReward (capacity a delta) (3 * a / 4)) x (effort a delta x)) ∧
      ¬ (∀ᵐ t ∂unitRankMeasure,
        sourceGroupThreshold (fun t => t) 2 1 false (3 * a / 4) < t → 0 < welfareGap a delta tie t) := by
  have heq := source_equilibrium ha hd htie hinj
  refine ⟨heq.1, heq.2.1, heq.2.2, ?_⟩
  intro hstrict
  have hzero : unitRankMeasure {t | sourceGroupThreshold (fun t => t) 2 1 false (3 * a / 4) < t ∧
      welfareGap a delta tie t = 0} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hstrict)
    intro t ht hpos
    have h := hpos ht.1
    rw [ht.2] at h
    exact (lt_irrefl _) h
  have hpos := zero_gap_positive_mass ha hd.1 hT htie hinj
  rw [hzero] at hpos
  exact (lt_irrefl _) hpos

end LBG22StrategicRanking.BaselineGroupExample
