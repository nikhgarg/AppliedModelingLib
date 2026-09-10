import LBG22StrategicRanking.AccessPrimitiveRepairs

/-!
# Actual group welfare comparisons

Higher effective skill permits imitation of every lower-skill score at
weakly lower cost. When the lower-skill applicant invests above the cost
minimum, a strictly cheaper imitation gives strictly higher welfare.
These comparisons use actual fixed-population counterfactual ranks.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

/-- A higher-skill best responder obtains at least the welfare of a
lower-skill applicant's actual action. Approaching the target score from
above removes any dependence on the relative tie keys. -/
theorem sourceBestResponse_welfare_mono_skill
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {skillX skillY effortX effortY : ℝ}
    (hpcont : ContinuousOn cost (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hr : Monotone reward)
    (hskillY : 0 < skillY) (hskill : skillX ≤ skillY) (heX : 0 ≤ effortX)
    (hactualX : score x = production effortX * skillX)
    (hbestY : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie y (production d * skillY)) - cost d ≤
        reward (tieBrokenRank μ score tie y) - cost effortY) :
    reward (tieBrokenRank μ score tie x) - cost effortX ≤
      reward (tieBrokenRank μ score tie y) - cost effortY := by
  apply sourceBestResponse_imitation_inequality μ score tie y x hpcont hgm hr hskillY heX
  · rw [hactualX]
    exact mul_le_mul_of_nonneg_left hskill (hg0.trans (hgm.monotoneOn (by simp) heX heX))
  · exact hbestY

/-- An above-baseline action at lower skill can be imitated strictly more
cheaply at higher skill. Therefore a higher-skill best responder has
strictly higher welfare, even if exact score matching loses the tie. -/
theorem sourceBestResponse_welfare_strict_of_effort_gt_baseline
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x y : α) {cost production reward : ℝ → ℝ}
    {baseline skillX skillY effortX effortY : ℝ} (hb : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hr : Monotone reward)
    (hskillX : 0 < skillX) (hskill : skillX < skillY) (heX : baseline < effortX)
    (hactualX : score x = production effortX * skillX)
    (hbestY : ∀ d : ℝ, 0 ≤ d →
      reward (counterfactualTieBrokenRank μ score tie y (production d * skillY)) - cost d ≤
        reward (tieBrokenRank μ score tie y) - cost effortY) :
    reward (tieBrokenRank μ score tie x) - cost effortX <
      reward (tieBrokenRank μ score tie y) - cost effortY := by
  have he0 : 0 < effortX := hb.trans_lt heX
  have hgpos : 0 < production effortX := hg0.trans_lt (hgm (by simp) he0.le he0)
  have htop : score x < production effortX * skillY := by
    rw [hactualX]
    exact mul_lt_mul_of_pos_left hskill hgpos
  obtain ⟨d, hbd, hde, hdscore⟩ : ∃ d : ℝ, baseline ≤ d ∧ d < effortX ∧ score x ≤ production d * skillY := by
    by_cases hbase : score x ≤ production baseline * skillY
    · exact ⟨baseline, le_rfl, heX, hbase⟩
    have hgI : ContinuousOn (fun d => production d * skillY) (Icc baseline effortX) :=
      (hgcont.mono (fun _ hd => hb.trans hd.1)).mul_const skillY
    obtain ⟨d, hd, hdz⟩ := intermediate_value_Icc heX.le hgI
      (show score x ∈ Icc (production baseline * skillY) (production effortX * skillY) from
        ⟨(lt_of_not_ge hbase).le, htop.le⟩)
    refine ⟨d, hd.1, lt_of_le_of_ne hd.2 ?_, hdz.symm.le⟩
    intro heq
    rw [heq] at hdz
    exact htop.ne hdz.symm
  have hcost := (sourceCost_strictMonoOn_above_baseline hb hpconv hpnonneg hpzero) hbd heX.le hde
  have h := sourceBestResponse_imitation_inequality μ score tie y x
    hpcont hgm hr (hskillX.trans hskill) (hb.trans hbd) hdscore hbestY
  linarith

/-- Actual individual welfare in one group at a given latent rank. -/
noncomputable def sourceActualGroupWelfare {n : ℕ}
    (cost : ℝ → ℝ) (effort score tie : Bool × ℝ → ℝ)
    (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (group : Bool) (t : ℝ) : ℝ :=
  reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie (group, t))).val -
    cost (effort (group, t))

/-- Welfare difference between groups at the same latent rank. -/
noncomputable def sourceActualGroupWelfareGap {n : ℕ}
    (cost : ℝ → ℝ) (effort score tie : Bool × ℝ → ℝ)
    (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) (t : ℝ) : ℝ :=
  sourceActualGroupWelfare cost effort score tie cutoff reward true t -
    sourceActualGroupWelfare cost effort score tie cutoff reward false t

/-- Actual equilibrium welfare favors the better environment. Strictness
holds whenever the disadvantaged applicant invests above baseline. When
both applicants receive the same reward, equality holds exactly when the
disadvantaged applicant invests only the zero-cost baseline.

This statement retains baseline clipping and applies to every finite-level
policy. It does not assume a canonical effort profile or a mixture inverse. -/
theorem sourceActualGroupWelfareGap_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB : ℝ} {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hb : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hg0 : 0 ≤ production 0) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) (hr : MonotoneOn reward (Icc (0 : ℕ) n))
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie cutoff reward x (effort x)) :
    ∀ᵐ t ∂unitRankMeasure,
      0 ≤ sourceActualGroupWelfareGap cost effort score tie cutoff reward t ∧
      (baseline < effort (false, t) → 0 < sourceActualGroupWelfareGap cost effort score tie cutoff reward t) ∧
      (reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie (true, t))).val =
        reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie (false, t))).val →
        (sourceActualGroupWelfareGap cost effort score tie cutoff reward t = 0 ↔ effort (false, t) = baseline)) := by
  let R := fun r => reward (finiteLowerRankBand cutoff r).val
  have hR : Monotone R := monotone_finiteLowerRankReward cutoff hr
  filter_upwards [sourceTwoGroupMeasure_ae_branch hbest true,
    sourceTwoGroupMeasure_ae_branch hbest false, ae_restrict_mem measurableSet_Ioc] with t hA hBbest ht
  have hfpos : 0 < skill t := hf0.trans_lt (hf (by norm_num) ⟨ht.1.le, ht.2⟩ ht.1)
  have hsB : 0 < sourceEnvironmentSkill skill psiA psiB (false, t) := by
    rw [sourceEnvironmentSkill_eq_on_support ⟨ht.1.le, ht.2⟩]
    simpa only [Bool.false_eq_true, ↓reduceIte] using mul_pos hB hfpos
  have hsBA : sourceEnvironmentSkill skill psiA psiB (false, t) <
      sourceEnvironmentSkill skill psiA psiB (true, t) := by
    rw [sourceEnvironmentSkill_eq_on_support ⟨ht.1.le, ht.2⟩,
      sourceEnvironmentSkill_eq_on_support ⟨ht.1.le, ht.2⟩]
    simpa only [Bool.false_eq_true, ↓reduceIte] using mul_lt_mul_of_pos_right hBA hfpos
  have hw := sourceBestResponse_welfare_mono_skill sourceTwoGroupMeasure score tie (false, t) (true, t)
    (reward := R) hpcont hgm hg0 hR (hsB.trans hsBA) hsBA.le hBbest.1 hBbest.2.1 hA.2.2
  have hnonneg : 0 ≤ sourceActualGroupWelfareGap cost effort score tie cutoff reward t := sub_nonneg.mpr hw
  have hstrict (he : baseline < effort (false, t)) :
      0 < sourceActualGroupWelfareGap cost effort score tie cutoff reward t := by
    apply sub_pos.mpr
    exact sourceBestResponse_welfare_strict_of_effort_gt_baseline sourceTwoGroupMeasure score tie
      (false, t) (true, t) (reward := R) hb hpcont hpconv hpnonneg hpzero hgcont hgm hg0 hR
      hsB hsBA he hBbest.2.1 hA.2.2
  refine ⟨hnonneg, hstrict, ?_⟩
  intro hequal
  constructor
  · intro hzero
    have hbase := sourceBestResponse_effort_ge_baseline sourceTwoGroupMeasure score tie (false, t)
      (reward := R) hb hsB.le hgm.monotoneOn hR hpconv hpnonneg hpzero hBbest.1 hBbest.2.1 hBbest.2.2
    apply le_antisymm _ hbase
    by_contra hn
    have h := hstrict (lt_of_not_ge hn)
    rw [hzero] at h
    exact (lt_irrefl _) h
  · intro heB
    apply le_antisymm _ hnonneg
    unfold sourceActualGroupWelfareGap sourceActualGroupWelfare
    rw [hequal, heB, hpzero]
    linarith [hpnonneg _ hA.1]

/-- Every equilibrium under constant rewards has zero group welfare gap.
Best response against the zero-cost action forces each applicant's cost
to vanish; no equilibrium selection or effort formula is assumed. -/
theorem sourceActualGroupWelfareGap_pureRandomization
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB rho : ℝ} {n : ℕ} (cutoff : Fin (n + 1) → ℝ)
    (hb : 0 ≤ baseline) (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie cutoff (fun _ => rho) x (effort x)) :
    ∀ᵐ t ∂unitRankMeasure,
      sourceActualGroupWelfareGap cost effort score tie cutoff (fun _ => rho) t = 0 := by
  filter_upwards [sourceTwoGroupMeasure_ae_branch hbest true,
    sourceTwoGroupMeasure_ae_branch hbest false] with t hA hB
  have hcostA : cost (effort (true, t)) = 0 := by
    have h := hA.2.2 baseline hb
    change rho - cost baseline ≤ rho - cost (effort (true, t)) at h
    rw [hpzero] at h
    exact le_antisymm (by linarith) (hpnonneg _ hA.1)
  have hcostB : cost (effort (false, t)) = 0 := by
    have h := hB.2.2 baseline hb
    change rho - cost baseline ≤ rho - cost (effort (false, t)) at h
    rw [hpzero] at h
    exact le_antisymm (by linarith) (hpnonneg _ hB.1)
  simp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare, hcostA, hcostB, sub_self]

/-- Below an applicant's quantile, the CDF is strictly below their rank,
and conversely. Both clipped tails are included. -/
theorem sourceSkillCDF_lt_rank_iff {skill : ℝ → ℝ} {z t : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (ht : t ∈ Ioc (0 : ℝ) 1) :
    sourceSkillCDF skill z < t ↔ z < skill t := by
  constructor
  · intro h
    by_contra hn
    have hmono := (monotone_cdf (Measure.map (sourceClampedSkill skill) unitRankMeasure)) (le_of_not_gt hn)
    change sourceSkillCDF skill (skill t) ≤ sourceSkillCDF skill z at hmono
    rw [sourceSkillCDF_at_quantile hfcont hf ⟨ht.1.le, ht.2⟩] at hmono
    exact (not_le_of_gt h) hmono
  · exact sourceSkillCDF_lt_rank_of_lt_quantile hfcont hf ht

theorem sourceEnvironmentCDF_swap {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) (z : ℝ) :
    sourceEnvironmentCDF skill psiA psiB z = sourceEnvironmentCDF skill psiB psiA z := by
  rw [sourceEnvironmentCDF_eq_mixture hfcont hA hB, sourceEnvironmentCDF_eq_mixture hfcont hB hA]
  ring

theorem sourceEnvironmentRank_advantaged_eq_swapped {skill : ℝ → ℝ} {psiA psiB t : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    sourceEnvironmentRank skill psiA psiB (true, t) = sourceDisadvantagedRank skill psiB psiA t := by
  unfold sourceDisadvantagedRank sourceEnvironmentRank sourceEnvironmentSkill
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact sourceEnvironmentCDF_swap hfcont hA hB _

/-- The conditional rank-CDF threshold for either population group.
Swapping the environment parameters exchanges the two group labels. -/
noncomputable def sourceGroupThreshold (skill : ℝ → ℝ) (psiA psiB : ℝ) (group : Bool) (c : ℝ) : ℝ :=
  if group then sourceDisadvantagedThreshold skill psiB psiA c
  else sourceDisadvantagedThreshold skill psiA psiB c

theorem sourceGroupThreshold_at_mixtureCDF {skill : ℝ → ℝ} {psiA psiB z : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) (group : Bool) :
    sourceGroupThreshold skill psiA psiB group (sourceEnvironmentCDF skill psiA psiB z) =
      sourceSkillCDF skill (z / (if group then psiA else psiB)) := by
  cases group
  · exact sourceDisadvantagedThreshold_at_mixtureCDF hfcont hf hA hB
  · change sourceDisadvantagedThreshold skill psiB psiA (sourceEnvironmentCDF skill psiA psiB z) = _
    rw [sourceEnvironmentCDF_swap hfcont hA hB]
    exact sourceDisadvantagedThreshold_at_mixtureCDF hfcont hf hB hA

theorem sourceGroupThreshold_lt_iff {skill : ℝ → ℝ} {psiA psiB c t : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB)
    (group : Bool) (ht : t ∈ Ioc (0 : ℝ) 1) :
    sourceGroupThreshold skill psiA psiB group c < t ↔
      c < sourceEnvironmentRank skill psiA psiB (group, t) := by
  cases group
  · exact sourceSkillCDF_lt_rank_iff
      (sourceDisadvantagedRank_continuous hfcont hf hA hB).continuousOn
      (sourceDisadvantagedRank_strictMono hfcont hf hA hB) ht
  · rw [sourceEnvironmentRank_advantaged_eq_swapped hfcont hA hB]
    exact sourceSkillCDF_lt_rank_iff
      (sourceDisadvantagedRank_continuous hfcont hf hB hA).continuousOn
      (sourceDisadvantagedRank_strictMono hfcont hf hB hA) ht

/-- The advantaged group's admission threshold never exceeds the
disadvantaged group's threshold, including clipped-support cases. -/
theorem sourceGroupThreshold_order {skill : ℝ → ℝ} {psiA psiB c : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) :
    sourceGroupThreshold skill psiA psiB true c ≤ sourceGroupThreshold skill psiA psiB false c := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hmem : sourceGroupThreshold skill psiA psiB true c ∈ Ioc (0 : ℝ) 1 :=
    ⟨sourceDisadvantagedThreshold_mem.1.trans_lt hlt, sourceDisadvantagedThreshold_mem.2⟩
  have hrB := (sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB false hmem).mp hlt
  have horder := (sourceEnvironmentRank_group_order hfcont hf hf0 hB hBA hmem).2.2
  have hrA := (sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB true hmem).mpr (hrB.trans horder)
  exact (lt_irrefl _) hrA

/-- Proposition 4.2's admission characterization for both groups under
every actual equilibrium. The group thresholds are derived conditional
CDFs; no inverse-CDF or rank-preservation equation is an input. -/
theorem sourceActualGroupAdmission_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hb : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ group : Bool, ∀ᵐ t ∂unitRankMeasure,
      sourceTwoLevelReward rho c (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure score tie (group, t))).val =
          if sourceGroupThreshold skill psiA psiB group c < t then rho / (1 - c) else 0 := by
  have hc1 : c < 1 := by linarith [hc.2]
  have h := sourceEnvironmentEquilibrium_reward_preservation_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) hb hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0
    hfcont hf hf0 (hB.trans hBA) hB (sourceTwoLevelReward_strictMono hrho hc1) hscore htie hinj hbest
  intro group
  filter_upwards [sourceTwoGroupMeasure_ae_branch h.2.2.2 group,
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht, finiteLowerRankBand_twoLevel]
  simp only [sourceGroupThreshold_lt_iff hfcont hf (hB.trans hBA) hB group hmem]
  split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero]

/-- In the common-admission region of Proposition 4.2, the welfare gap
vanishes exactly at a disadvantaged applicant's zero-cost baseline.
Every other case in that region has a strictly positive gap. -/
theorem sourceActualGroupWelfareGap_high_region_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hb : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ᵐ t ∂unitRankMeasure,
      sourceGroupThreshold skill psiA psiB false c < t →
        (sourceActualGroupWelfareGap cost effort score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (sourceTwoLevelReward rho c) t = 0 ↔ effort (false, t) = baseline) := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hadmission := sourceActualGroupAdmission_of_sourcePrimitives hrho hc hb hpcont hpconv hpnonneg hpzero
    hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscore htie hinj hbest
  have hw := sourceActualGroupWelfareGap_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) hb hpcont hpconv hpnonneg hpzero hgcont hgm hg0 hf hf0
    hB hBA (sourceTwoLevelReward_strictMono hrho hc1).monotoneOn hbest
  filter_upwards [hadmission true, hadmission false, hw] with t hA hBrew hwt
  intro ht
  have hAt := (sourceGroupThreshold_order (c := c) hfcont hf hf0 hB hBA).trans_lt ht
  apply hwt.2.2
  rw [hA, hBrew, if_pos hAt, if_pos ht]

end LBG22StrategicRanking
