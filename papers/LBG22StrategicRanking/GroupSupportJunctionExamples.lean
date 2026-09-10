import LBG22StrategicRanking.GroupProfilePrimitiveRepairs
import LBG22StrategicRanking.PopulationRankPrimitiveRepairs
import LBG22StrategicRanking.EnvironmentExamples
import LBG22StrategicRanking.SocietalUtilityPrimitiveRepairs

/-!+# A junction between smooth group skill supports

Latent skill is uniform on `[1,2]`. Environment factors `3/2` and `1`
give overlapping effective-skill supports whose density changes at `3/2`.
The associated rank cutoff is `1/4`. Cost is quadratic, production is
linear, and capacity is fixed at `1/4` throughout the policy comparison.
-/

namespace LBG22StrategicRanking.SupportJunctionExample

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
open SeparatedEnvironmentExample (latentSkill latent_cont latent_mono latent_cdf_eq)

noncomputable def effectiveSkill : Bool × ℝ → ℝ := sourceEnvironmentSkill latentSkill (3 / 2) 1

/-- The effective-skill quantile on a neighborhood of the support junction. -/
noncomputable def boundarySkill (c : ℝ) : ℝ := if c ≤ 1 / 4 then 1 + 2 * c else 6 / 5 * (1 + c)

theorem boundarySkill_mem {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    boundarySkill c ∈ Icc (7 / 5 : ℝ) (39 / 25) := by
  unfold boundarySkill
  split <;> constructor <;> linarith [hc.1, hc.2]

theorem mixtureCDF_boundary {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    sourceEnvironmentCDF latentSkill (3 / 2) 1 (boundarySkill c) = c := by
  rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num), div_one]
  have ha := boundarySkill_mem hc
  rw [latent_cdf_eq (show boundarySkill c ∈ Icc (1 : ℝ) 2 by constructor <;> linarith [ha.1, ha.2])]
  by_cases h : c ≤ 1 / 4
  · rw [sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono
      (by simp only [boundarySkill, if_pos h, latentSkill]; linarith)]
    simp only [boundarySkill, if_pos h]
    ring
  · rw [latent_cdf_eq (show boundarySkill c / (3 / 2) ∈ Icc (1 : ℝ) 2 by
      simp only [boundarySkill, if_neg h]
      constructor <;> linarith [hc.2])]
    simp only [boundarySkill, if_neg h]
    ring

theorem disadvantagedThreshold_eq {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    sourceDisadvantagedThreshold latentSkill (3 / 2) 1 c = boundarySkill c - 1 := by
  have h := sourceDisadvantagedThreshold_at_mixtureCDF latent_cont latent_mono
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 1) (z := boundarySkill c)
  have ha := boundarySkill_mem hc
  rw [mixtureCDF_boundary hc, div_one,
    latent_cdf_eq (show boundarySkill c ∈ Icc (1 : ℝ) 2 by constructor <;> linarith [ha.1, ha.2])] at h
  exact h

noncomputable def boundaryEffort (c : ℝ) : ℝ := Real.sqrt ((1 / 4) / (1 - c))
noncomputable def effort (c : ℝ) (x : Bool × ℝ) : ℝ :=
  if effectiveSkill x ≤ boundarySkill c then 0 else boundaryEffort c * boundarySkill c / effectiveSkill x
noncomputable def score (c : ℝ) (x : Bool × ℝ) : ℝ :=
  if effectiveSkill x ≤ boundarySkill c then 0 else boundaryEffort c * boundarySkill c

theorem score_meas (c : ℝ) : Measurable (score c) :=
  measurable_const.ite (measurableSet_le (sourceEnvironmentSkill_measurable latent_cont) measurable_const)
    measurable_const

theorem boundaryEffort_properties {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    0 < boundaryEffort c ∧ boundaryEffort c ≤ 1 ∧ (boundaryEffort c) ^ 2 = (1 / 4) / (1 - c) := by
  have hd : 0 < 1 - c := by linarith [hc.2]
  have hq : 0 < (1 / 4 : ℝ) / (1 - c) := div_pos (by norm_num) hd
  exact ⟨Real.sqrt_pos.mpr hq, Real.sqrt_le_one.mpr ((div_le_one hd).mpr (by linarith [hc.2])),
    Real.sq_sqrt hq.le⟩

theorem lower_group_mass {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    sourceTwoGroupMeasure.real {x | effectiveSkill x ≤ boundarySkill c} = c := by
  have hm : Measurable effectiveSkill := sourceEnvironmentSkill_measurable latent_cont
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure) hm.aemeasurable
  have h := mixtureCDF_boundary hc
  change cdf (Measure.map effectiveSkill sourceTwoGroupMeasure) (boundarySkill c) = c at h
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hm measurableSet_Iic] at h
  exact h

theorem reward_eq {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) (r : ℝ) :
    sourceTwoLevelReward (1 / 4) c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val =
        if c < r then (boundaryEffort c) ^ 2 else 0 := by
  rw [finiteLowerRankBand_twoLevel]
  split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero, (boundaryEffort_properties hc).2.2]

/-- Quadratic-cost, linear-production effort at a supplied effective-skill
cutoff. The population-mass condition is proved separately. -/
noncomputable def boundaryEffortProfile (c a : ℝ) (x : Bool × ℝ) : ℝ :=
  if effectiveSkill x ≤ a then 0 else boundaryEffort c * a / effectiveSkill x

noncomputable def boundaryScoreProfile (c a : ℝ) (x : Bool × ℝ) : ℝ :=
  if effectiveSkill x ≤ a then 0 else boundaryEffort c * a

theorem boundaryScoreProfile_meas (c a : ℝ) : Measurable (boundaryScoreProfile c a) :=
  measurable_const.ite (measurableSet_le (sourceEnvironmentSkill_measurable latent_cont) measurable_const)
    measurable_const

/-- Every positive skill cutoff with the prescribed population mass
constructs an actual equilibrium, against every nonnegative deviation. -/
theorem source_equilibrium_of_cutoff {c a : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) (ha : 0 < a)
    (hmass : sourceTwoGroupMeasure.real {x | effectiveSkill x ≤ a} = c)
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) id
        effectiveSkill (boundaryScoreProfile c a) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward (1 / 4) c) x (boundaryEffortProfile c a x) := by
  haveI := noAtoms_map_sourceTwoGroup_of_injOn htie hinj
  have hd : 0 < 1 - c := by linarith [hc.2]
  have hq : 0 < (1 / 4 : ℝ) / (1 - c) := div_pos (by norm_num) hd
  have hdelta : 0 < boundaryEffort c := Real.sqrt_pos.mpr hq
  have hdeltaSq : boundaryEffort c ^ 2 = (1 / 4) / (1 - c) := Real.sq_sqrt hq.le
  have hReward (r : ℝ) : sourceTwoLevelReward (1 / 4) c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val =
        if c < r then boundaryEffort c ^ 2 else 0 := by
    rw [finiteLowerRankBand_twoLevel]
    split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero, hdeltaSq]
  have hT : 0 < boundaryEffort c * a := mul_pos hdelta ha
  have hrank := sourcePopulation_twoLevelRank_of_score_separation sourceTwoGroupMeasure
    (boundaryScoreProfile_meas c a) htie hmass hT (ae_of_all _ (fun x => by
      constructor
      · intro hx
        simp only [boundaryScoreProfile, if_pos hx, le_refl]
      · intro hx
        simp only [boundaryScoreProfile, if_neg (not_le_of_gt hx), le_refl]))
  have hcounter (x : Bool × ℝ) (v : ℝ) :
      sourceTwoLevelReward (1 / 4) c
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (counterfactualTieBrokenRank sourceTwoGroupMeasure (boundaryScoreProfile c a) tie x v)).val ≤
            if boundaryEffort c * a ≤ v then (boundaryEffort c) ^ 2 else 0 := by
    rw [hReward]
    by_cases hv : boundaryEffort c * a ≤ v
    · rw [if_pos hv]
      split <;> nlinarith [sq_nonneg (boundaryEffort c)]
    · rw [if_neg hv, if_neg (not_lt_of_ge (hrank.1 x v (lt_of_not_ge hv)))]
  have hs := sourceEnvironmentSkill_positive_ae latent_mono
    (by norm_num [latentSkill]) (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hrank.2, hs] with x hx hsp
  change 0 < effectiveSkill x at hsp
  have hown : sourceTwoLevelReward (1 / 4) c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure (boundaryScoreProfile c a) tie x)).val =
          if a < effectiveSkill x then (boundaryEffort c) ^ 2 else 0 := by
    rw [hReward]
    simp only [hx]
  by_cases hlow : effectiveSkill x ≤ a
  · refine ⟨by simp only [boundaryEffortProfile, if_pos hlow, le_refl], ?_, ?_⟩
    · simp only [boundaryScoreProfile, boundaryEffortProfile, if_pos hlow, id_eq, zero_mul]
    · intro d hd
      rw [hown, if_neg (not_lt_of_ge hlow)]
      simp only [boundaryEffortProfile, if_pos hlow, id_eq]
      apply (sub_le_sub_right (hcounter x (d * effectiveSkill x)) (d ^ 2)).trans
      split_ifs with hreach
      · have hdd : boundaryEffort c ≤ d := by
          have h := hreach.trans (mul_le_mul_of_nonneg_left hlow hd)
          exact (mul_le_mul_iff_left₀ ha).mp h
        nlinarith [mul_self_le_mul_self hdelta.le hdd]
      · nlinarith [sq_nonneg d]
  · have he0 : 0 ≤ boundaryEffort c * a / effectiveSkill x := (div_pos hT hsp).le
    have hecap : boundaryEffort c * a / effectiveSkill x ≤ boundaryEffort c :=
      (div_le_iff₀ hsp).mpr (mul_le_mul_of_nonneg_left (lt_of_not_ge hlow).le hdelta.le)
    refine ⟨by simpa only [boundaryEffortProfile, if_neg hlow] using he0, ?_, ?_⟩
    · simp only [boundaryScoreProfile, boundaryEffortProfile, if_neg hlow, id_eq, div_mul_cancel₀ _ hsp.ne']
    · intro d hd
      rw [hown, if_pos (lt_of_not_ge hlow)]
      simp only [boundaryEffortProfile, if_neg hlow, id_eq]
      apply (sub_le_sub_right (hcounter x (d * effectiveSkill x)) (d ^ 2)).trans
      split_ifs with hreach
      · have hed : boundaryEffort c * a / effectiveSkill x ≤ d :=
          (div_le_iff₀ hsp).mpr hreach
        nlinarith [mul_self_le_mul_self he0 hed]
      · nlinarith [mul_self_le_mul_self he0 hecap, sq_nonneg d]

/-- The fixed population, tie order, and every nonnegative effort deviation
are respected by this equilibrium family on both sides of the junction. -/
theorem source_equilibrium {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10))
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) id
        effectiveSkill (score c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward (1 / 4) c) x (effort c x) :=
  source_equilibrium_of_cutoff ⟨by linarith [hc.1], by linarith [hc.2]⟩
    (by linarith [(boundarySkill_mem hc).1]) (lower_group_mass hc) htie hinj

/-- The effective-skill quantile over the full feasible policy range. Above
rank `2/3`, the disadvantaged support is exhausted and only group A remains. -/
noncomputable def fullBoundarySkill (c : ℝ) : ℝ :=
  if c ≤ 2 / 3 then boundarySkill c else 3 * c

theorem fullBoundarySkill_pos {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) :
    0 < fullBoundarySkill c := by
  unfold fullBoundarySkill boundarySkill
  split_ifs <;> linarith [hc.1]

theorem fullBoundarySkill_eq_local {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    fullBoundarySkill c = boundarySkill c :=
  if_pos (by linarith [hc.2])

theorem mixtureCDF_fullBoundary {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) :
    sourceEnvironmentCDF latentSkill (3 / 2) 1 (fullBoundarySkill c) = c := by
  rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num), div_one]
  by_cases hmid : c ≤ 2 / 3
  · rw [fullBoundarySkill, if_pos hmid]
    by_cases hlo : c ≤ 1 / 4
    · rw [boundarySkill, if_pos hlo,
        sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono
          (by dsimp only [latentSkill]; linarith),
        latent_cdf_eq (show 1 + 2 * c ∈ Icc (1 : ℝ) 2 by constructor <;> linarith [hc.1])]
      ring
    · rw [boundarySkill, if_neg hlo,
        latent_cdf_eq (show (6 / 5 * (1 + c)) / (3 / 2) ∈ Icc (1 : ℝ) 2 by
          constructor <;> linarith),
        latent_cdf_eq (show 6 / 5 * (1 + c) ∈ Icc (1 : ℝ) 2 by
          constructor <;> linarith)]
      ring
  · rw [fullBoundarySkill, if_neg hmid,
      latent_cdf_eq (show (3 * c) / (3 / 2) ∈ Icc (1 : ℝ) 2 by
        constructor <;> linarith [hc.2]),
      sourceSkillCDF_eq_one_of_top_le latent_cont latent_mono
        (by dsimp only [latentSkill]; linarith)]
    ring

theorem full_lower_group_mass {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) :
    sourceTwoGroupMeasure.real {x | effectiveSkill x ≤ fullBoundarySkill c} = c := by
  have hm : Measurable effectiveSkill := sourceEnvironmentSkill_measurable latent_cont
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure) hm.aemeasurable
  have h := mixtureCDF_fullBoundary hc
  change cdf (Measure.map effectiveSkill sourceTwoGroupMeasure) (fullBoundarySkill c) = c at h
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hm measurableSet_Iic] at h
  exact h

noncomputable def fullEffort (c : ℝ) : Bool × ℝ → ℝ :=
  boundaryEffortProfile c (fullBoundarySkill c)

noncomputable def fullScore (c : ℝ) : Bool × ℝ → ℝ :=
  boundaryScoreProfile c (fullBoundarySkill c)

theorem fullScore_meas (c : ℝ) : Measurable (fullScore c) := boundaryScoreProfile_meas _ _

/-- The same fixed environment admits this equilibrium at every feasible
cutoff, including deterministic admission and the exhausted-support region. -/
theorem full_source_equilibrium {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4))
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) id
        effectiveSkill (fullScore c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward (1 / 4) c) x (fullEffort c x) :=
  source_equilibrium_of_cutoff hc (fullBoundarySkill_pos hc) (full_lower_group_mass hc) htie hinj

theorem fullEffort_eq_local {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    fullEffort c = effort c := by
  unfold fullEffort
  rw [fullBoundarySkill_eq_local hc]
  rfl

theorem fullScore_eq_local {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10)) :
    fullScore c = score c := by
  unfold fullScore
  rw [fullBoundarySkill_eq_local hc]
  rfl

/-- The welfare gap after cancellation of the common admitted reward. -/
noncomputable def gapFormula (t c : ℝ) : ℝ :=
  (5 / 36) * (boundarySkill c) ^ 2 / ((1 - c) * (1 + t) ^ 2)

theorem canonicalGap_eq {c t : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10))
    (ht : t ∈ Ioc (3 / 4 : ℝ) 1) :
    sourceCanonicalGroupWelfareGap (fun e => e ^ 2) id latentSkill (3 / 2) 1 (1 / 4) t c =
      gapFormula t c := by
  have hcap : sourceUnitCostEffort (fun e : ℝ => e ^ 2) = 1 :=
    sourceUnitCostEffort_eq quadraticCost_strictMono (by norm_num) (by norm_num)
  have hd : 0 < 1 - c := by linarith [hc.2]
  have hq : (1 / 4 : ℝ) / (1 - c) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos (by norm_num) hd).le, (div_le_one hd).mpr (by linarith [hc.2])⟩
  have hT : sourceCanonicalGroupScoreThreshold (fun e => e ^ 2) id latentSkill (3 / 2) 1 (1 / 4) c =
      boundaryEffort c * boundarySkill c := by
    simp only [sourceCanonicalGroupScoreThreshold, hcap, sourceScoreScale, disadvantagedThreshold_eq hc,
      effortIntervalInverse_quadratic_one hq, id_eq, latentSkill, one_mul, boundaryEffort]
    ring
  have ha := boundarySkill_mem hc
  have hdelta := boundaryEffort_properties hc
  have hskill : 0 < 1 + t := by linarith [ht.1]
  have hT0 : 0 ≤ boundaryEffort c * boundarySkill c := mul_nonneg hdelta.1.le (by linarith [ha.1])
  have hBcap : boundaryEffort c * boundarySkill c / (1 + t) ≤ 1 := by
    apply (div_le_one hskill).mpr
    have h := mul_le_mul_of_nonneg_right hdelta.2.1 (show 0 ≤ boundarySkill c by linarith [ha.1])
    nlinarith [ha.2, ht.1]
  have hAcap : boundaryEffort c * boundarySkill c / ((3 / 2) * (1 + t)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have h := (div_le_one hskill).mp hBcap
    nlinarith [ht.1]
  have heB := sourceEffortAtScore_at_production (production := id)
    (fun _ _ _ _ h => h) (show boundaryEffort c * boundarySkill c / (1 + t) ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg hT0 hskill.le, hBcap⟩)
  have heA := sourceEffortAtScore_at_production (production := id)
    (fun _ _ _ _ h => h) (show boundaryEffort c * boundarySkill c / ((3 / 2) * (1 + t)) ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg hT0 (by positivity), hAcap⟩)
  simp only [id_eq] at heA heB
  simp only [sourceCanonicalGroupWelfareGap, hcap, hT, latentSkill, one_mul, sourceCostAtScore, heA, heB]
  rw [div_pow, div_pow, mul_pow, hdelta.2.2]
  unfold gapFormula
  field_simp [hd.ne', hskill.ne']
  ring

noncomputable def actualGap (tie : Bool × ℝ → ℝ) (t c : ℝ) : ℝ :=
  sourceActualGroupWelfareGap (fun e => e ^ 2) (effort c) (score c) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (1 / 4) c) t

theorem actualGap_eq {c : ℝ} (hc : c ∈ Icc (1 / 5 : ℝ) (3 / 10))
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc (3 / 4 : ℝ) 1 → actualGap tie t c = gapFormula t c := by
  have h := sourceActualGroupWelfareGap_eq_canonical_of_sourcePrimitives
    (cost := fun e => e ^ 2) (production := id) (skill := latentSkill)
    (psiA := 3 / 2) (psiB := 1) (rho := 1 / 4) (effort := effort c) (score := score c)
    (by norm_num) ⟨by linarith [hc.1], by linarith [hc.2]⟩
    (continuous_pow 2).continuousOn quadraticCost_strictConvex (fun _ _ => sq_nonneg _) (by norm_num)
    continuous_id.continuousOn (fun _ _ _ _ h => h) (concaveOn_id (convex_Ici _)) (by norm_num)
    latent_cont latent_mono (by norm_num [latentSkill]) (by norm_num) (by norm_num)
    (score_meas c) htie hinj (source_equilibrium hc htie hinj)
  filter_upwards [h] with t ht
  intro htI
  have hhigh : sourceGroupThreshold latentSkill (3 / 2) 1 false c < t := by
    change sourceDisadvantagedThreshold latentSkill (3 / 2) 1 c < t
    rw [disadvantagedThreshold_eq hc]
    linarith [(boundarySkill_mem hc).2, htI.1]
  exact (ht hhigh).trans (canonicalGap_eq hc htI)

/-- The one-sided derivatives at the support junction are unequal even
though all three economic primitives are smooth. -/
theorem gapFormula_oneSidedDerivatives {t : ℝ} (ht : 3 / 4 < t) :
    HasDerivWithinAt (gapFormula t) (5 / (3 * (1 + t) ^ 2)) (Iic (1 / 4)) (1 / 4) ∧
    HasDerivWithinAt (gapFormula t) (11 / (9 * (1 + t) ^ 2)) (Ici (1 / 4)) (1 / 4) := by
  have hskill : 0 < 1 + t := by linarith
  have hleft : HasDerivAt (fun c : ℝ => (5 / 36) * (1 + 2 * c) ^ 2 / ((1 - c) * (1 + t) ^ 2))
      (5 / (3 * (1 + t) ^ 2)) (1 / 4) := by
    have h := ((((hasDerivAt_const (1 / 4 : ℝ) 1).add ((hasDerivAt_id (1 / 4)).const_mul 2)).pow 2).const_mul
      (5 / 36)).div (((hasDerivAt_const (1 / 4 : ℝ) 1).sub (hasDerivAt_id (1 / 4))).mul_const ((1 + t) ^ 2))
      (by change (1 - (1 / 4 : ℝ)) * (1 + t) ^ 2 ≠ 0
          exact mul_ne_zero (by norm_num) (pow_ne_zero _ hskill.ne'))
    convert h using 1
    norm_num
    field_simp [hskill.ne']
    ring
  have hright : HasDerivAt (fun c : ℝ => (5 / 36) * (6 / 5 * (1 + c)) ^ 2 / ((1 - c) * (1 + t) ^ 2))
      (11 / (9 * (1 + t) ^ 2)) (1 / 4) := by
    have h := (((((hasDerivAt_const (1 / 4 : ℝ) 1).add (hasDerivAt_id (1 / 4))).const_mul (6 / 5)).pow 2).const_mul
      (5 / 36)).div (((hasDerivAt_const (1 / 4 : ℝ) 1).sub (hasDerivAt_id (1 / 4))).mul_const ((1 + t) ^ 2))
      (by change (1 - (1 / 4 : ℝ)) * (1 + t) ^ 2 ≠ 0
          exact mul_ne_zero (by norm_num) (pow_ne_zero _ hskill.ne'))
    convert h using 1
    norm_num
    field_simp [hskill.ne']
    ring
  constructor
  · apply hleft.hasDerivWithinAt.congr_of_mem _ (show (1 / 4 : ℝ) ∈ Iic (1 / 4) by norm_num)
    intro c hc
    simp only [mem_Iic] at hc
    simp only [gapFormula, boundarySkill, if_pos hc]
  · apply hright.hasDerivWithinAt.congr_of_mem _ (show (1 / 4 : ℝ) ∈ Ici (1 / 4) by norm_num)
    intro c hc
    simp only [mem_Ici] at hc
    rcases eq_or_lt_of_le hc with rfl | hlt
    · norm_num [gapFormula, boundarySkill]
    · simp only [gapFormula, boundarySkill, if_neg (not_le_of_gt hlt)]

theorem gapFormula_not_differentiableAt {t : ℝ} (ht : 3 / 4 < t) :
    ¬ DifferentiableAt ℝ (gapFormula t) (1 / 4) := by
  intro hd
  have h := gapFormula_oneSidedDerivatives ht
  have hl := (uniqueDiffWithinAt_Iic (1 / 4 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h.1
  have hr := (uniqueDiffWithinAt_Ici (1 / 4 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h.2
  have heq := hl.symm.trans hr
  have hskill : 1 + t ≠ 0 := by linarith
  field_simp [hskill] at heq
  norm_num at heq

/-- Almost every high applicant in the actual fixed-capacity equilibrium
family has no two-sided welfare-gap derivative at the support junction.
Only countably many policy-specific null sets are intersected. -/
theorem actualGap_not_differentiableAt
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc (3 / 4 : ℝ) 1 →
      ¬ DifferentiableAt ℝ (actualGap tie t) (1 / 4) := by
  let step := fun n : ℕ => (1 / 20 : ℝ) / ((n : ℝ) + 2)
  let left := fun n : ℕ => (1 / 4 : ℝ) - step n
  let right := fun n : ℕ => (1 / 4 : ℝ) + step n
  have hs (n : ℕ) : 0 < step n ∧ step n ≤ 1 / 20 := by
    have hn : 0 < (n : ℝ) + 2 := by positivity
    exact ⟨div_pos (by norm_num) hn, (div_le_iff₀ hn).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hl (n : ℕ) : left n ∈ Icc (1 / 5 : ℝ) (3 / 10) := by
    dsimp only [left]
    constructor <;> linarith [(hs n).1, (hs n).2]
  have hr (n : ℕ) : right n ∈ Icc (1 / 5 : ℝ) (3 / 10) := by
    dsimp only [right]
    constructor <;> linarith [(hs n).1, (hs n).2]
  have hs0 : Tendsto step atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 20 : ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa only [step, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h
  have hl0 : Tendsto left atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa only [left, sub_zero] using hs0.const_sub (1 / 4)
  have hr0 : Tendsto right atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa only [right, add_zero] using tendsto_const_nhds.add hs0
  have hlwithin : Tendsto left atTop (𝓝[Iic (1 / 4 : ℝ) \ {1 / 4}] (1 / 4)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl0, Eventually.of_forall (fun n => by
      have hlt : left n < 1 / 4 := by dsimp only [left]; linarith [(hs n).1]
      exact ⟨hlt.le, by simpa only [mem_singleton_iff] using hlt.ne⟩)⟩
  have hrwithin : Tendsto right atTop (𝓝[Ici (1 / 4 : ℝ) \ {1 / 4}] (1 / 4)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Eventually.of_forall (fun n => by
      have hlt : 1 / 4 < right n := by dsimp only [right]; linarith [(hs n).1]
      exact ⟨hlt.le, by simpa only [mem_singleton_iff] using hlt.ne'⟩)⟩
  have heq : ∀ᵐ t ∂unitRankMeasure, ∀ n : ℕ, t ∈ Ioc (3 / 4 : ℝ) 1 →
      actualGap tie t (left n) = gapFormula t (left n) ∧
      actualGap tie t (right n) = gapFormula t (right n) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [actualGap_eq (hl n) htie hinj, actualGap_eq (hr n) htie hinj] with t hl' hr'
    exact fun ht => ⟨hl' ht, hr' ht⟩
  filter_upwards [heq, actualGap_eq (by norm_num : (1 / 4 : ℝ) ∈ Icc (1 / 5) (3 / 10)) htie hinj]
    with t heq hbase
  intro ht hd
  have hcanonical := gapFormula_oneSidedDerivatives ht.1
  have hal : Tendsto (fun n => slope (actualGap tie t) (1 / 4) (left n)) atTop
      (𝓝 (deriv (actualGap tie t) (1 / 4))) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hd.hasDerivAt.hasDerivWithinAt).comp hlwithin
  have har : Tendsto (fun n => slope (actualGap tie t) (1 / 4) (right n)) atTop
      (𝓝 (deriv (actualGap tie t) (1 / 4))) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hd.hasDerivAt.hasDerivWithinAt).comp hrwithin
  have hcl := (hasDerivWithinAt_iff_tendsto_slope.mp hcanonical.1).comp hlwithin
  have hcr := (hasDerivWithinAt_iff_tendsto_slope.mp hcanonical.2).comp hrwithin
  have hel : (fun n => slope (actualGap tie t) (1 / 4) (left n)) =ᶠ[atTop]
      (fun n => slope (gapFormula t) (1 / 4) (left n)) := Eventually.of_forall (fun n => by
    simp only [slope_def_field, hbase ht, (heq n ht).1])
  have her : (fun n => slope (actualGap tie t) (1 / 4) (right n)) =ᶠ[atTop]
      (fun n => slope (gapFormula t) (1 / 4) (right n)) := Eventually.of_forall (fun n => by
    simp only [slope_def_field, hbase ht, (heq n ht).2])
  have hleft := tendsto_nhds_unique (hal.congr' hel) hcl
  have hright := tendsto_nhds_unique (har.congr' her) hcr
  have hbad := hleft.symm.trans hright
  have hskill : 1 + t ≠ 0 := by linarith [ht.1]
  field_simp [hskill] at hbad
  norm_num at hbad

/-- The nondifferentiability occurs on a positive-mass common-admission
region with positive effort in both groups, not at a baseline-clipping
transition or an applicant-rank boundary. -/
theorem nondifferentiability_positive_mass
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    0 < unitRankMeasure {t | sourceGroupThreshold latentSkill (3 / 2) 1 false (1 / 4) < t ∧
      (∀ group : Bool, 0 < effort (1 / 4) (group, t)) ∧
      ¬ DifferentiableAt ℝ (actualGap tie t) (1 / 4)} := by
  have hmass : 0 < unitRankMeasure (Ioc (3 / 4 : ℝ) 1) := by
    rw [unitRankMeasure, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc (3 / 4 : ℝ) 1 ⊆ Ioc (0 : ℝ) 1 from
        fun _ ht => ⟨by linarith [ht.1], ht.2⟩), Real.volume_Ioc]
    norm_num
  have hsubset : Ioc (3 / 4 : ℝ) 1 ≤ᵐ[unitRankMeasure]
      {t | sourceGroupThreshold latentSkill (3 / 2) 1 false (1 / 4) < t ∧
        (∀ group : Bool, 0 < effort (1 / 4) (group, t)) ∧
        ¬ DifferentiableAt ℝ (actualGap tie t) (1 / 4)} := by
    filter_upwards [actualGap_not_differentiableAt htie hinj] with t ht hmem
    refine ⟨?_, ?_, ht hmem⟩
    · change sourceDisadvantagedThreshold latentSkill (3 / 2) 1 (1 / 4) < t
      rw [disadvantagedThreshold_eq (by norm_num)]
      norm_num [boundarySkill]
      linarith [hmem.1]
    · intro group
      have hs : boundarySkill (1 / 4) < effectiveSkill (group, t) := by
        rw [effectiveSkill, sourceEnvironmentSkill_eq_on_support (x := (group, t))
          (show t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hmem.1], hmem.2⟩)]
        cases group <;> norm_num [boundarySkill, latentSkill] <;> linarith [hmem.1]
      have ha : 0 < boundarySkill (1 / 4) := by norm_num [boundarySkill]
      simp only [effort, if_neg (not_le_of_gt hs)]
      exact div_pos (mul_pos (boundaryEffort_properties (by norm_num)).1 ha) (ha.trans hs)
  exact hmass.trans_le (measure_mono_ae hsubset)

/-- The source derivative-existence claim fails inside its stated cutoff
range, for smooth primitives and actual equilibria at fixed capacity. -/
theorem source_derivative_existence_counterexample
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    (1 / 4 : ℝ) ≤ sourceEnvironmentCDF latentSkill (3 / 2) 1 (latentSkill 1) ∧
      (∀ c ∈ Icc (1 / 5 : ℝ) (3 / 10), c ∈ Ioc (0 : ℝ) (1 - 1 / 4) ∧
        ∀ᵐ x ∂sourceTwoGroupMeasure,
          SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) id
            effectiveSkill (score c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward (1 / 4) c) x (effort c x)) ∧
      ¬ (∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold latentSkill (3 / 2) 1 false (1 / 4) < t →
        DifferentiableAt ℝ (actualGap tie t) (1 / 4)) := by
  refine ⟨?_, fun c hc => ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, source_equilibrium hc htie hinj⟩, ?_⟩
  · rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num)]
    norm_num only [latentSkill]
    rw [latent_cdf_eq (by norm_num), latent_cdf_eq (by norm_num)]
    norm_num
  · intro hdiff
    have hzero : unitRankMeasure {t | sourceGroupThreshold latentSkill (3 / 2) 1 false (1 / 4) < t ∧
        (∀ group : Bool, 0 < effort (1 / 4) (group, t)) ∧
        ¬ DifferentiableAt ℝ (actualGap tie t) (1 / 4)} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hdiff)
      intro t ht h
      exact ht.2.2 (h ht.1)
    have hpos := nondifferentiability_positive_mass htie hinj
    rw [hzero] at hpos
    exact (lt_irrefl _) hpos

/-- Actual welfare under the full feasible equilibrium family. -/
noncomputable def fullActualGap (tie : Bool × ℝ → ℝ) (t c : ℝ) : ℝ :=
  sourceActualGroupWelfareGap (fun e => e ^ 2) (fullEffort c) (fullScore c) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (1 / 4) c) t

theorem fullActualGap_eq_near (tie : Bool × ℝ → ℝ) (t : ℝ) :
    fullActualGap tie t =ᶠ[𝓝 (1 / 4)] actualGap tie t := by
  filter_upwards [Icc_mem_nhds (by norm_num : (1 / 5 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 3 / 10)] with c hc
  simp only [fullActualGap, actualGap, fullEffort_eq_local hc, fullScore_eq_local hc]

/-- Smooth source primitives and a full actual equilibrium family still
give nondifferentiability at an interior cutoff satisfying the source's
top-disadvantaged-rank restriction. -/
theorem full_source_derivative_existence_counterexample
    {tie : Bool × ℝ → ℝ} (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1}) :
    (1 / 4 : ℝ) ≤ sourceEnvironmentCDF latentSkill (3 / 2) 1 (latentSkill 1) ∧
      (∀ c ∈ Ioc (0 : ℝ) (1 - 1 / 4), Measurable (fullScore c) ∧
        ∀ᵐ x ∂sourceTwoGroupMeasure,
          SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure (fun e => e ^ 2) id
            effectiveSkill (fullScore c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward (1 / 4) c) x (fullEffort c x)) ∧
      ¬ (∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold latentSkill (3 / 2) 1 false (1 / 4) < t →
        DifferentiableAt ℝ (fullActualGap tie t) (1 / 4)) := by
  have h := source_derivative_existence_counterexample htie hinj
  refine ⟨h.1, fun c hc => ⟨fullScore_meas c, full_source_equilibrium hc htie hinj⟩, ?_⟩
  intro hfull
  apply h.2.2
  filter_upwards [hfull] with t ht hhigh
  exact (ht hhigh).congr_of_eventuallyEq (fullActualGap_eq_near tie t).symm

end LBG22StrategicRanking.SupportJunctionExample
