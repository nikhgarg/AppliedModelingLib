import LBG22StrategicRanking.EnvironmentPrimitiveRepairs
import LBG22StrategicRanking.ThreeLevelPrimitiveRepairs
import LBG22StrategicRanking.AccessPrimitiveRepairs
import LBG22StrategicRanking.GroupWelfarePrimitiveRepairs

/-!
# An equilibrium with separated group supports

Latent skills range from one to two. Environment factors three and one,
quadratic cost, and production `10 + e` admit a zero-effort equilibrium
under deterministic admission of the advantaged half of the population.
The population score distribution has no atoms, so the construction works
for every tie order.
-/

namespace LBG22StrategicRanking.SeparatedEnvironmentExample

open Set MeasureTheory ProbabilityTheory

def latentSkill (t : ℝ) : ℝ := 1 + t
theorem latent_cont : ContinuousOn latentSkill (Icc (0 : ℝ) 1) :=
  (continuous_const.add continuous_id).continuousOn
theorem latent_mono : StrictMonoOn latentSkill (Icc (0 : ℝ) 1) := by
  intro a _ b _ hab
  change 1 + a < 1 + b
  linarith

/-- The effective-skill CDF is constant throughout the gap between the
disadvantaged support `[1,2]` and advantaged support `[3,6]`. -/
theorem mixtureCDF_gap {z : ℝ} (hz : z ∈ Icc (2 : ℝ) 3) :
    sourceEnvironmentCDF latentSkill 3 1 z = 1 / 2 := by
  rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num),
    sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono
      (by change z / 3 ≤ 1 + 0; linarith [hz.2]),
    sourceSkillCDF_eq_one_of_top_le latent_cont latent_mono
      (by change 1 + 1 ≤ z / 1; linarith [hz.1])]
  norm_num

noncomputable def labelTie (x : Bool × ℝ) : ℝ :=
  ((if x.1 then 1 else 0) + x.2) / 2

theorem label_meas : Measurable labelTie :=
  (((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp measurable_fst).add
    measurable_snd).div_const 2

theorem label_inj : InjOn labelTie {x | x.2 ∈ Ioc (0 : ℝ) 1} := by
  rintro ⟨b, t⟩ ht ⟨d, s⟩ hs heq
  have ht0 := ht.1
  have ht1 := ht.2
  have hs0 := hs.1
  have hs1 := hs.2
  cases b <;> cases d <;> simp only [labelTie, Bool.false_eq_true, ↓reduceIte, zero_add] at heq ⊢
  all_goals congr 1 <;> linarith

noncomputable def baselineScore : Bool × ℝ → ℝ := sourceEnvironmentSkill latentSkill 30 10
theorem baselineScore_meas : Measurable baselineScore := sourceEnvironmentSkill_measurable latent_cont

theorem deviation_rank (tie : Bool × ℝ → ℝ) (x : Bool × ℝ) (v : ℝ) :
    counterfactualTieBrokenRank sourceTwoGroupMeasure baselineScore tie x v =
      sourceEnvironmentCDF latentSkill 30 10 v := by
  haveI : NoAtoms (Measure.map baselineScore sourceTwoGroupMeasure) :=
    noAtoms_map_sourceEnvironmentSkill latent_cont latent_mono
    (by norm_num : (0 : ℝ) < 30) (by norm_num : (0 : ℝ) < 10)
  apply counterfactualTieBrokenRank_eq_cdf_of_score_atom_null sourceTwoGroupMeasure baselineScore_meas
  have h : (Measure.map baselineScore sourceTwoGroupMeasure) {v} = 0 := measure_singleton v
  rw [Measure.map_apply baselineScore_meas (measurableSet_singleton v)] at h
  exact h

theorem own_rank (tie : Bool × ℝ → ℝ) {x : Bool × ℝ} (hx : x.2 ∈ Ioc (0 : ℝ) 1) :
    tieBrokenRank sourceTwoGroupMeasure baselineScore tie x =
      if x.1 then (1 + x.2) / 2 else x.2 / 2 := by
  rw [← counterfactualTieBrokenRank_at_current_score]
  rw [deviation_rank]
  unfold baselineScore
  rw [sourceEnvironmentSkill_eq_on_support ⟨hx.1.le, hx.2⟩]
  rcases x with ⟨b, t⟩
  have ht0 := hx.1
  have ht1 := hx.2
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num),
      sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono (by dsimp [latentSkill]; linarith)]
    have heq : 10 * latentSkill t / 10 = latentSkill t := by ring
    rw [heq, sourceSkillCDF_at_quantile latent_cont latent_mono ⟨ht0.le, ht1⟩]
    ring
  · simp only [↓reduceIte]
    rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num),
      sourceSkillCDF_eq_one_of_top_le latent_cont latent_mono (z := 30 * latentSkill t / 10)
        (by dsimp [latentSkill]; linarith)]
    have heq : 30 * latentSkill t / 30 = latentSkill t := by ring
    rw [heq, sourceSkillCDF_at_quantile latent_cont latent_mono ⟨ht0.le, ht1⟩]
    ring

noncomputable def admission (r : ℝ) : ℝ := if 1 / 2 < r then 1 else 0
theorem admission_le_one (r : ℝ) : admission r ≤ 1 := by
  unfold admission
  split <;> norm_num
theorem reward_eq_admission (r : ℝ) :
    sourceTwoLevelReward (1 / 2) (1 / 2)
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i) r).val = admission r := by
  rw [finiteLowerRankBand_twoLevel]
  unfold admission
  split <;> norm_num [sourceTwoLevelReward]

/-- With separated baseline scores, zero effort is an equilibrium under
deterministic admission of group A. A group B deviation capable of reaching
the admitted scores costs at least its possible reward. -/
theorem baseline_equilibrium (tie : Bool × ℝ → ℝ) :
    ∀ᵐ x ∂sourceTwoGroupMeasure, SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure
      (fun e => e ^ 2) (fun e => 10 + e) (sourceEnvironmentSkill latentSkill 3 1)
      baselineScore tie (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i)
      (sourceTwoLevelReward (1 / 2) (1 / 2)) x 0 := by
  filter_upwards [sourceTwoGroupMeasure_ae_latent_mem] with x hx
  refine ⟨by norm_num, ?_, ?_⟩
  · unfold baselineScore
    rw [sourceEnvironmentSkill_eq_on_support ⟨hx.1.le, hx.2⟩,
      sourceEnvironmentSkill_eq_on_support ⟨hx.1.le, hx.2⟩]
    split <;> ring
  · intro d hd
    rw [reward_eq_admission, reward_eq_admission, own_rank tie hx]
    norm_num only [zero_pow, sub_zero]
    rcases x with ⟨b, t⟩
    have ht0 := hx.1
    have ht1 := hx.2
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hown : admission (t / 2) = 0 := by
        unfold admission
        rw [if_neg (by linarith)]
      rw [hown]
      by_cases hd1 : 1 ≤ d
      · have hbound := admission_le_one (counterfactualTieBrokenRank sourceTwoGroupMeasure baselineScore tie
          (false, t) ((10 + d) * sourceEnvironmentSkill latentSkill 3 1 (false, t)))
        nlinarith
      · have hrank : counterfactualTieBrokenRank sourceTwoGroupMeasure baselineScore tie
            (false, t) ((10 + d) * sourceEnvironmentSkill latentSkill 3 1 (false, t)) ≤ 1 / 2 := by
          rw [deviation_rank, sourceEnvironmentSkill_eq_on_support ⟨ht0.le, ht1⟩]
          simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
          rw [sourceEnvironmentCDF_eq_mixture latent_cont (by norm_num) (by norm_num),
            sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono
              (by dsimp [latentSkill]; nlinarith)]
          have hbound := cdf_le_one (Measure.map (sourceClampedSkill latentSkill) unitRankMeasure)
            ((10 + d) * latentSkill t / 10)
          change sourceSkillCDF latentSkill ((10 + d) * latentSkill t / 10) ≤ 1 at hbound
          linarith
        unfold admission
        rw [if_neg (not_lt_of_ge hrank)]
        nlinarith [sq_nonneg d]
    · simp only [↓reduceIte]
      have hown : admission ((1 + t) / 2) = 1 := by
        unfold admission
        rw [if_pos (by linarith)]
      rw [hown]
      have hbound := admission_le_one (counterfactualTieBrokenRank sourceTwoGroupMeasure baselineScore tie
        (true, t) ((10 + d) * sourceEnvironmentSkill latentSkill 3 1 (true, t)))
      nlinarith [sq_nonneg d]

/-- The latent CDF is affine on its own support and therefore satisfies
the convexity premise of the access comparison. -/
theorem latent_cdf_eq {z : ℝ} (hz : z ∈ Icc (1 : ℝ) 2) :
    sourceSkillCDF latentSkill z = z - 1 := by
  have ht : z - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h := sourceSkillCDF_at_quantile latent_cont latent_mono ht
  have heq : latentSkill (z - 1) = z := by unfold latentSkill; ring
  rwa [heq] at h

theorem latent_cdf_convex :
    ConvexOn ℝ (Icc (latentSkill 0) (latentSkill 1)) (sourceSkillCDF latentSkill) := by
  have haffine : ConvexOn ℝ (Icc (1 : ℝ) 2) (fun z : ℝ => z + (-1)) :=
    (convexOn_id (convex_Icc _ _)).add (convexOn_const (-1) (convex_Icc _ _))
  have h := haffine.congr (fun z hz => by simpa only [sub_eq_add_neg] using (latent_cdf_eq hz).symm)
  simpa only [latentSkill, add_zero, one_add_one_eq_two] using h

theorem disadvantagedRank_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceDisadvantagedRank latentSkill 3 1 t = t / 2 := by
  rw [sourceDisadvantagedRank_eq latent_cont latent_mono (by norm_num) (by norm_num) ht,
    sourceSkillCDF_eq_zero_of_le_bottom latent_cont latent_mono
      (by dsimp [latentSkill]; linarith [ht.2])]
  ring

/-- Below exhaustion, twice the population cutoff is the rejected
fraction within group B. -/
theorem disadvantagedThreshold_eq {c : ℝ} (hc : c ∈ Icc (0 : ℝ) (1 / 2)) :
    sourceDisadvantagedThreshold latentSkill 3 1 c = 2 * c := by
  have ht : 2 * c ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have h := sourceSkillCDF_at_quantile
    (sourceDisadvantagedRank_continuous latent_cont latent_mono (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 1)).continuousOn
    (sourceDisadvantagedRank_strictMono latent_cont latent_mono (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 1)) ht
  rw [disadvantagedRank_eq ht, mul_div_cancel_left₀ c (by norm_num : (2 : ℝ) ≠ 0)] at h
  exact h

theorem disadvantagedThreshold_exhausted {c : ℝ} (hc : (1 / 2 : ℝ) ≤ c) :
    sourceDisadvantagedThreshold latentSkill 3 1 c = 1 := by
  apply sourceDisadvantagedThreshold_eq_one latent_cont latent_mono (by norm_num) (by norm_num)
  simpa only [disadvantagedRank_eq (by norm_num : (1 : ℝ) ∈ Icc 0 1)] using hc

/-- Complete exclusion occurs at and above the disadvantaged support's
top rank; access remains zero beyond that boundary. -/
theorem access_exhausted {rho c : ℝ} (hc : (1 / 2 : ℝ) ≤ c) :
    twoLevelDisadvantagedAccess rho c (sourceDisadvantagedThreshold latentSkill 3 1 c) = 0 := by
  rw [disadvantagedThreshold_exhausted hc]
  simp only [twoLevelDisadvantagedAccess, sub_self, mul_zero]

theorem baseline_access_eq_zero :
    sourceActualDisadvantagedAccess baselineScore labelTie
      (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i) (sourceTwoLevelReward (1 / 2) (1 / 2)) = 0 := by
  have h := sourceActualDisadvantagedAccess_lt_pureRandomization_of_sourcePrimitives
    (effort := fun _ => 0) (baseline := 0)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 (1 - 1 / 2))
    (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex
    (fun _ _ => sq_nonneg _) (by norm_num)
    (continuous_const.add continuous_id).continuousOn
    (by intro a _ b _ hab; change (10 : ℝ) + a < 10 + b; linarith)
    ((concaveOn_const _ (convex_Ici _)).add (concaveOn_id (convex_Ici _))) (by norm_num)
    latent_cont latent_mono (by norm_num [latentSkill]) (by norm_num) (by norm_num)
    baselineScore_meas label_meas label_inj (baseline_equilibrium labelTie)
  rw [h.2.1, disadvantagedThreshold_exhausted (by norm_num)]
  norm_num

/-- The separated-support equilibrium has a unit welfare gap: group A
receives reward one, group B receives zero, and both incur zero cost. -/
theorem baseline_welfare_gap_eq_one :
    ∀ᵐ t ∂unitRankMeasure, sourceActualGroupWelfareGap (fun e => e ^ 2) (fun _ => 0)
      baselineScore labelTie (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i)
      (sourceTwoLevelReward (1 / 2) (1 / 2)) t = 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold sourceActualGroupWelfareGap sourceActualGroupWelfare
  rw [reward_eq_admission, reward_eq_admission, own_rank labelTie ht, own_rank labelTie ht]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [admission, admission, if_pos (by linarith [ht.1]), if_neg (by linarith [ht.2])]
  norm_num

end LBG22StrategicRanking.SeparatedEnvironmentExample
