import LBG22StrategicRanking.EnvironmentPrimitiveRepairs
import LBG22StrategicRanking.ApplicantWelfarePrimitiveRepairs

/-!
# Disadvantaged-group access in the actual population

The disadvantaged group's mixture rank is a continuous increasing function
of its latent rank. Its distribution function gives the rejected fraction
at each policy cutoff, including cutoffs above the group's entire support.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- An almost-everywhere population assertion holds almost everywhere
within each positive-mass group. -/
theorem sourceTwoGroupMeasure_ae_branch {P : Bool × ℝ → Prop}
    (h : ∀ᵐ x ∂sourceTwoGroupMeasure, P x) (b : Bool) :
    ∀ᵐ t ∂unitRankMeasure, P (b, t) := by
  rw [sourceTwoGroupMeasure, ae_add_measure_iff,
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0),
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)] at h
  have hm : Measurable (fun t : ℝ => (b, t)) := measurable_const.prodMk measurable_id
  apply ae_of_ae_map hm.aemeasurable
  cases b
  · exact h.2
  · exact h.1

/-- The disadvantaged group's pre-effort rank in the mixture population. -/
noncomputable def sourceDisadvantagedRank (skill : ℝ → ℝ) (psiA psiB : ℝ) (t : ℝ) : ℝ :=
  sourceEnvironmentRank skill psiA psiB (false, t)

theorem sourceDisadvantagedRank_eq {skill : ℝ → ℝ} {psiA psiB t : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hA : 0 < psiA) (hB : 0 < psiB) (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceDisadvantagedRank skill psiA psiB t =
      (t + sourceSkillCDF skill (psiB / psiA * skill t)) / 2 := by
  unfold sourceDisadvantagedRank sourceEnvironmentRank
  rw [sourceEnvironmentSkill_eq_on_support ht, sourceEnvironmentCDF_eq_mixture hfcont hA hB]
  have hdiag : psiB * skill t / psiB = skill t := by field_simp
  have hcross : psiB * skill t / psiA = psiB / psiA * skill t := by ring
  simp only [Bool.false_eq_true, ↓reduceIte, hdiag, hcross,
    sourceSkillCDF_at_quantile hfcont hf ht]
  ring

theorem sourceDisadvantagedRank_continuous {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    Continuous (sourceDisadvantagedRank skill psiA psiB) := by
  haveI := Measure.isProbabilityMeasure_map (μ := sourceTwoGroupMeasure)
    (sourceEnvironmentSkill_measurable (psiA := psiA) (psiB := psiB) hfcont).aemeasurable
  haveI := noAtoms_map_sourceEnvironmentSkill hfcont hf hA hB
  have hc := AppliedModelingLib.Probability.continuous_cdf_of_noAtoms
    (Measure.map (sourceEnvironmentSkill skill psiA psiB) sourceTwoGroupMeasure)
  simpa only [sourceDisadvantagedRank, sourceEnvironmentRank, sourceEnvironmentCDF,
    sourceEnvironmentSkill, Bool.false_eq_true, ↓reduceIte] using
    hc.comp (continuous_const.mul (continuous_sourceClampedSkill hfcont))

theorem sourceDisadvantagedRank_strictMono {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    StrictMonoOn (sourceDisadvantagedRank skill psiA psiB) (Icc (0 : ℝ) 1) := by
  intro t ht u hu htu
  rw [sourceDisadvantagedRank_eq hfcont hf hA hB ht,
    sourceDisadvantagedRank_eq hfcont hf hA hB hu]
  have h := (monotone_cdf (Measure.map (sourceClampedSkill skill) unitRankMeasure))
    (mul_le_mul_of_nonneg_left (hf.monotoneOn ht hu htu.le) (div_pos hB hA).le)
  change sourceSkillCDF skill (psiB / psiA * skill t) ≤
    sourceSkillCDF skill (psiB / psiA * skill u) at h
  linarith

theorem sourceDisadvantagedRank_zero {skill : ℝ → ℝ} {psiA psiB : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) : sourceDisadvantagedRank skill psiA psiB 0 = 0 := by
  have hA := hB.trans hBA
  rw [sourceDisadvantagedRank_eq hfcont hf hA hB (by norm_num)]
  have hz : psiB / psiA * skill 0 ≤ skill 0 := by
    have hratio : psiB / psiA ≤ 1 := (div_le_one hA).mpr hBA.le
    nlinarith
  rw [sourceSkillCDF_eq_zero_of_le_bottom hfcont hf hz]
  norm_num

theorem sourceDisadvantagedRank_lt_latent {skill : ℝ → ℝ} {psiA psiB t : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) (ht : t ∈ Ioc (0 : ℝ) 1) :
    sourceDisadvantagedRank skill psiA psiB t < t :=
  (sourceEnvironmentRank_group_order hfcont hf hf0 hB hBA ht).1

/-- The quantile and its CDF are inverse on the actual skill interval. -/
theorem sourceSkillCDF_quantile_spec {skill : ℝ → ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) {z : ℝ} (hz : z ∈ Icc (skill 0) (skill 1)) :
    sourceSkillCDF skill z ∈ Icc (0 : ℝ) 1 ∧ skill (sourceSkillCDF skill z) = z := by
  obtain ⟨t, ht, htz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfcont hz
  rw [← htz, sourceSkillCDF_at_quantile hfcont hf ht]
  exact ⟨ht, rfl⟩

/-- Fraction of disadvantaged applicants whose mixture rank is at most
the policy cutoff. This threshold is clipped at one above their support. -/
noncomputable def sourceDisadvantagedThreshold (skill : ℝ → ℝ) (psiA psiB c : ℝ) : ℝ :=
  sourceSkillCDF (sourceDisadvantagedRank skill psiA psiB) c

theorem sourceDisadvantagedThreshold_mem {skill : ℝ → ℝ} {psiA psiB c : ℝ} :
    sourceDisadvantagedThreshold skill psiA psiB c ∈ Icc (0 : ℝ) 1 :=
  ⟨cdf_nonneg _ _, cdf_le_one _ _⟩

theorem sourceDisadvantagedThreshold_eq_one {skill : ℝ → ℝ} {psiA psiB c : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB)
    (hc : sourceDisadvantagedRank skill psiA psiB 1 ≤ c) :
    sourceDisadvantagedThreshold skill psiA psiB c = 1 :=
  sourceSkillCDF_eq_one_of_top_le (sourceDisadvantagedRank_continuous hfcont hf hA hB).continuousOn
    (sourceDisadvantagedRank_strictMono hfcont hf hA hB) hc

theorem sourceDisadvantagedThreshold_inverse {skill : ℝ → ℝ} {psiA psiB c : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA)
    (hc : c ∈ Icc (0 : ℝ) (sourceDisadvantagedRank skill psiA psiB 1)) :
    sourceDisadvantagedRank skill psiA psiB (sourceDisadvantagedThreshold skill psiA psiB c) = c := by
  apply (sourceSkillCDF_quantile_spec
    (sourceDisadvantagedRank_continuous hfcont hf (hB.trans hBA) hB).continuousOn
    (sourceDisadvantagedRank_strictMono hfcont hf (hB.trans hBA) hB) ?_).2
  simpa only [sourceDisadvantagedRank_zero hfcont hf hf0 hB hBA] using hc

/-- Every positive interior policy cutoff rejects a strictly greater
fraction of the disadvantaged group than of the whole population. -/
theorem sourceDisadvantagedThreshold_gt_cutoff {skill : ℝ → ℝ} {psiA psiB c : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hB : 0 < psiB) (hBA : psiB < psiA) (hc : c ∈ Ioo (0 : ℝ) 1) :
    c < sourceDisadvantagedThreshold skill psiA psiB c := by
  by_cases htop : sourceDisadvantagedRank skill psiA psiB 1 ≤ c
  · rw [sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB htop]
    exact hc.2
  have hi := sourceDisadvantagedThreshold_inverse hfcont hf hf0 hB hBA
    ⟨hc.1.le, (lt_of_not_ge htop).le⟩
  have ht := sourceDisadvantagedThreshold_mem (skill := skill) (psiA := psiA) (psiB := psiB) (c := c)
  have htpos : 0 < sourceDisadvantagedThreshold skill psiA psiB c := by
    by_contra hn
    have htzero := le_antisymm (le_of_not_gt hn) ht.1
    rw [htzero, sourceDisadvantagedRank_zero hfcont hf hf0 hB hBA] at hi
    exact (ne_of_gt hc.1) hi.symm
  have h := sourceDisadvantagedRank_lt_latent hfcont hf hf0 hB hBA ⟨htpos, ht.2⟩
  rwa [hi] at h

/-- The threshold is the actual conditional CDF of mixture rank. -/
theorem sourceDisadvantagedThreshold_eq_cdf {skill : ℝ → ℝ} {psiA psiB c : ℝ} :
    sourceDisadvantagedThreshold skill psiA psiB c =
      cdf (Measure.map (sourceDisadvantagedRank skill psiA psiB) unitRankMeasure) c := by
  unfold sourceDisadvantagedThreshold sourceSkillCDF
  congr 1
  apply congrArg cdf
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact sourceClampedSkill_eq ⟨ht.1.le, ht.2⟩

/-- Evaluating the rejected fraction at a mixture-CDF cutoff gives exactly
the source's conditional-CDF threshold. This identity includes both tails
and does not require a globally invertible mixture CDF. -/
theorem sourceDisadvantagedThreshold_at_mixtureCDF {skill : ℝ → ℝ} {psiA psiB z : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    sourceDisadvantagedThreshold skill psiA psiB (sourceEnvironmentCDF skill psiA psiB z) =
      sourceSkillCDF skill (z / psiB) := by
  have hcont : ContinuousOn (sourceDisadvantagedRank skill psiA psiB) (Icc (0 : ℝ) 1) :=
    (sourceDisadvantagedRank_continuous hfcont hf hA hB).continuousOn
  have hmono := sourceDisadvantagedRank_strictMono hfcont hf hA hB
  have hrank (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      sourceDisadvantagedRank skill psiA psiB t = sourceEnvironmentCDF skill psiA psiB (psiB * skill t) := by
    unfold sourceDisadvantagedRank sourceEnvironmentRank
    rw [sourceEnvironmentSkill_eq_on_support ht]
    simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hbottom : z / psiB ≤ skill 0
  · have hz : z ≤ psiB * skill 0 := by
      simpa only [mul_comm] using (div_le_iff₀ hB).mp hbottom
    have hc : sourceEnvironmentCDF skill psiA psiB z ≤ sourceDisadvantagedRank skill psiA psiB 0 := by
      rw [hrank 0 (by norm_num)]
      exact (monotone_cdf _) hz
    rw [sourceDisadvantagedThreshold, sourceSkillCDF_eq_zero_of_le_bottom hcont hmono hc,
      sourceSkillCDF_eq_zero_of_le_bottom hfcont hf hbottom]
  by_cases htop : skill 1 ≤ z / psiB
  · have hz : psiB * skill 1 ≤ z := by
      simpa only [mul_comm] using (le_div_iff₀ hB).mp htop
    have hc : sourceDisadvantagedRank skill psiA psiB 1 ≤ sourceEnvironmentCDF skill psiA psiB z := by
      rw [hrank 1 (by norm_num)]
      exact (monotone_cdf _) hz
    rw [sourceDisadvantagedThreshold_eq_one hfcont hf hA hB hc,
      sourceSkillCDF_eq_one_of_top_le hfcont hf htop]
  have ht := sourceSkillCDF_quantile_spec hfcont hf
    (show z / psiB ∈ Icc (skill 0) (skill 1) from ⟨(lt_of_not_ge hbottom).le, (lt_of_not_ge htop).le⟩)
  have hscore : psiB * skill (sourceSkillCDF skill (z / psiB)) = z := by
    rw [ht.2, mul_div_cancel₀ _ hB.ne']
  have hr := hrank (sourceSkillCDF skill (z / psiB)) ht.1
  rw [hscore] at hr
  rw [← hr, sourceDisadvantagedThreshold, sourceSkillCDF_at_quantile hcont hmono ht.1]

/-- Integrating the admission probability within group B gives its access,
with all support clipping supplied by the actual rank distribution. -/
theorem sourceDisadvantagedAdmission_integral {skill : ℝ → ℝ} {psiA psiB c q : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hA : 0 < psiA) (hB : 0 < psiB) :
    Integrable (fun t => if c < sourceDisadvantagedRank skill psiA psiB t then q else 0) unitRankMeasure ∧
      (∫ t, (if c < sourceDisadvantagedRank skill psiA psiB t then q else 0) ∂unitRankMeasure) =
        q * (1 - sourceDisadvantagedThreshold skill psiA psiB c) := by
  classical
  have hm := (sourceDisadvantagedRank_continuous hfcont hf hA hB).measurable
  have hset : MeasurableSet {t | c < sourceDisadvantagedRank skill psiA psiB t} :=
    hm measurableSet_Ioi
  haveI := Measure.isProbabilityMeasure_map (μ := unitRankMeasure) hm.aemeasurable
  have htail : unitRankMeasure.real {t | c < sourceDisadvantagedRank skill psiA psiB t} =
      1 - sourceDisadvantagedThreshold skill psiA psiB c := by
    have hmap : (Measure.map (sourceDisadvantagedRank skill psiA psiB) unitRankMeasure).real (Ioi c) =
        unitRankMeasure.real {t | c < sourceDisadvantagedRank skill psiA psiB t} := by
      rw [measureReal_def, Measure.map_apply hm measurableSet_Ioi]
      rfl
    rw [← hmap, sourceDisadvantagedThreshold_eq_cdf, cdf_eq_real,
      ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  constructor
  · exact (integrable_const q).indicator hset
  · change (∫ t, ({t | c < sourceDisadvantagedRank skill psiA psiB t}.indicator (fun _ => q)) t
        ∂unitRankMeasure) = _
    rw [integral_indicator_const q hset, htail, smul_eq_mul, mul_comm]

/-- Actual group-B access averages post-effort admission probabilities over
that group's latent population, not over the entire mixture. -/
noncomputable def sourceActualDisadvantagedAccess {n : ℕ}
    (score tie : Bool × ℝ → ℝ) (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) : ℝ :=
  ∫ t, reward (finiteLowerRankBand cutoff (tieBrokenRank sourceTwoGroupMeasure score tie (false, t))).val
    ∂unitRankMeasure

theorem sourceActualDisadvantagedAccess_pureRandomization
    {n : ℕ} (score tie : Bool × ℝ → ℝ) (cutoff : Fin (n + 1) → ℝ) (rho : ℝ) :
    sourceActualDisadvantagedAccess score tie cutoff (fun _ => rho) = rho := by
  simp [sourceActualDisadvantagedAccess]

/-- Constant admission rewards admit the zero-cost effort as a best
response for every applicant and against every nonnegative deviation. -/
theorem sourcePopulation_pureRandomization_bestResponse
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (cost production : ℝ → ℝ) (skill tie : α → ℝ) {n : ℕ}
    (cutoff : Fin (n + 1) → ℝ) (rho : ℝ) {baseline : ℝ}
    (hb : 0 ≤ baseline) (hp : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpb : cost baseline = 0) (x : α) :
    SourcePopulationFiniteBestResponseAt μ cost production skill
      (fun y => production baseline * skill y) tie cutoff (fun _ => rho) x baseline := by
  refine ⟨hb, rfl, ?_⟩
  intro d hd
  change rho - cost d ≤ rho - cost baseline
  rw [hpb]
  linarith [hp d hd]

/-- Proposition 4.4's pure-randomization optimum for every actual two-level
equilibrium in the source two-group population. The admission integral and
its strict comparison are derived from primitives and all deviations. -/
theorem sourceActualDisadvantagedAccess_lt_pureRandomization_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {baseline psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie)
    (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    Integrable (fun t => sourceTwoLevelReward rho c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure score tie (false, t))).val) unitRankMeasure ∧
      sourceActualDisadvantagedAccess score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) =
          rho / (1 - c) * (1 - sourceDisadvantagedThreshold skill psiA psiB c) ∧
      sourceActualDisadvantagedAccess score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) < rho := by
  have hc1 : c < 1 := by linarith [hc.2]
  have h := sourceEnvironmentEquilibrium_reward_preservation_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) hbaseline hpcont hpconv hpnonneg hpzero
    hgcont hgm hgconc hg0 hfcont hf hf0 (hB.trans hBA) hB
    (sourceTwoLevelReward_strictMono hrho hc1) hscore htie hinj hbest
  have heq : (fun t => sourceTwoLevelReward rho c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure score tie (false, t))).val) =ᵐ[unitRankMeasure]
      (fun t => if c < sourceDisadvantagedRank skill psiA psiB t then rho / (1 - c) else 0) := by
    filter_upwards [sourceTwoGroupMeasure_ae_branch h.2.2.2 false] with t ht
    rw [ht, finiteLowerRankBand_twoLevel]
    change sourceTwoLevelReward rho c (if c < sourceDisadvantagedRank skill psiA psiB t then 1 else 0) = _
    split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero]
  have hi := sourceDisadvantagedAdmission_integral (c := c) (q := rho / (1 - c)) hfcont hf (hB.trans hBA) hB
  have hformula := (integral_congr_ae heq).trans hi.2
  refine ⟨hi.1.congr heq.symm, hformula, ?_⟩
  change (∫ t, _ ∂unitRankMeasure) < rho
  rw [hformula]
  have htheta := sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hc.1, hc1⟩
  have hstrict := mul_lt_mul_of_pos_left (show 1 - sourceDisadvantagedThreshold skill psiA psiB c < 1 - c
    by linarith) (div_pos hrho (sub_pos.mpr hc1))
  simpa only [div_mul_cancel₀ _ (sub_pos.mpr hc1).ne'] using hstrict

private theorem convex_gap_le_on_set {C : ℝ → ℝ} {s : Set ℝ} {a b c d : ℝ}
    (hconv : ConvexOn ℝ s C) (hmono : MonotoneOn C s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a < b) (hcd : c < d) (hac : a ≤ c) (hbd : b ≤ d)
    (hlen : b - a ≤ d - c) : C b - C a ≤ C d - C c := by
  have had : a < d := hac.trans_lt hcd
  have hs1 := hconv.slope_mono ha
    (show b ∈ s \ {a} from ⟨hb, by simpa using hab.ne'⟩)
    (show d ∈ s \ {a} from ⟨hd, by simpa using had.ne'⟩) hbd
  have hs2 := hconv.slope_mono hd
    (show a ∈ s \ {d} from ⟨ha, by simpa using had.ne⟩)
    (show c ∈ s \ {d} from ⟨hc, by simpa using hcd.ne⟩) hac
  have hslope : slope C a b ≤ slope C c d :=
    hs1.trans (by simpa only [slope_comm] using hs2)
  have hsnonneg : 0 ≤ slope C c d := by
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono hc hd hcd.le)) (sub_nonneg.mpr hcd.le)
  have hprod := (mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hab.le)).trans
    (mul_le_mul_of_nonneg_right hlen hsnonneg)
  have hleft : (b - a) * slope C a b = C b - C a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hright : (d - c) * slope C c d = C d - C c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  simpa only [hleft, hright] using hprod

/-- Convexity of the latent CDF on its skill support bounds the CDF
increment after downward scaling. The zero-CDF region is handled explicitly;
no global convexity of a bounded nonconstant CDF is assumed. -/
theorem sourceSkillCDF_scaled_increment_le {skill : ℝ → ℝ} {beta u v : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hconv : ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill))
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    sourceSkillCDF skill (beta * skill v) - sourceSkillCDF skill (beta * skill u) ≤ v - u := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · simp
  have hfu0 : skill 0 ≤ skill u := hf.monotoneOn (by norm_num) hu hu.1
  have hfv1 : skill v ≤ skill 1 := hf.monotoneOn hv (by norm_num) hv.2
  have hfuv := hf hu hv huv
  have hfuN : 0 ≤ skill u := hf0.trans hfu0
  have hfvN : 0 ≤ skill v := hfuN.trans hfuv.le
  have hbu : beta * skill u ≤ skill u := by nlinarith [hbeta.2]
  have hbv : beta * skill v ≤ skill v := by nlinarith [hbeta.2]
  have hbuv : beta * skill u < beta * skill v := mul_lt_mul_of_pos_left hfuv hbeta.1
  by_cases hbottom : beta * skill v ≤ skill 0
  · rw [sourceSkillCDF_eq_zero_of_le_bottom hfcont hf hbottom,
      sourceSkillCDF_eq_zero_of_le_bottom hfcont hf (hbuv.le.trans hbottom)]
    linarith
  have hb0 := lt_of_not_ge hbottom
  have hmaxu : max (beta * skill u) (skill 0) ≤ skill u := max_le hbu hfu0
  have hmaxb : max (beta * skill u) (skill 0) < beta * skill v := max_lt hbuv hb0
  have hlen : beta * skill v - max (beta * skill u) (skill 0) ≤ skill v - skill u := by
    have hmax := le_max_left (beta * skill u) (skill 0)
    nlinarith [mul_nonneg (sub_nonneg.mpr hbeta.2) (sub_nonneg.mpr hfuv.le)]
  have hgap := convex_gap_le_on_set hconv ((monotone_cdf _).monotoneOn _)
    (show max (beta * skill u) (skill 0) ∈ Icc (skill 0) (skill 1) from
      ⟨le_max_right _ _, hmaxu.trans (hfuv.le.trans hfv1)⟩)
    (show beta * skill v ∈ Icc (skill 0) (skill 1) from ⟨hb0.le, hbv.trans hfv1⟩)
    (show skill u ∈ Icc (skill 0) (skill 1) from ⟨hfu0, hfuv.le.trans hfv1⟩)
    (show skill v ∈ Icc (skill 0) (skill 1) from ⟨hfu0.trans hfuv.le, hfv1⟩)
    hmaxb hfuv hmaxu hbv hlen
  have hclip : sourceSkillCDF skill (max (beta * skill u) (skill 0)) =
      sourceSkillCDF skill (beta * skill u) := by
    by_cases hb : beta * skill u ≤ skill 0
    · rw [max_eq_right hb, sourceSkillCDF_at_quantile hfcont hf (by norm_num),
        sourceSkillCDF_eq_zero_of_le_bottom hfcont hf hb]
    · rw [max_eq_left (le_of_not_ge hb)]
  simpa only [hclip, sourceSkillCDF_at_quantile hfcont hf hu,
    sourceSkillCDF_at_quantile hfcont hf hv] using hgap

/-- Under the source's convex inverse-skill condition, disadvantaged
mixture rank expands no faster than latent rank. -/
theorem sourceDisadvantagedRank_increment_le {skill : ℝ → ℝ} {psiA psiB u v : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hconv : ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill))
    (hB : 0 < psiB) (hBA : psiB < psiA)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    sourceDisadvantagedRank skill psiA psiB v - sourceDisadvantagedRank skill psiA psiB u ≤ v - u := by
  have hA := hB.trans hBA
  have hbeta : psiB / psiA ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hB hA, (div_le_one hA).mpr hBA.le⟩
  have h := sourceSkillCDF_scaled_increment_le hfcont hf hf0 hconv hbeta hu hv huv
  rw [sourceDisadvantagedRank_eq hfcont hf hA hB hu, sourceDisadvantagedRank_eq hfcont hf hA hB hv]
  linarith

/-- The inverse threshold's excess over the policy cutoff increases while
the disadvantaged group is not exhausted. No derivative is required. -/
theorem sourceDisadvantagedThreshold_gap_mono_on_support {skill : ℝ → ℝ} {psiA psiB c d : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hconv : ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill))
    (hB : 0 < psiB) (hBA : psiB < psiA)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ sourceDisadvantagedRank skill psiA psiB 1) :
    sourceDisadvantagedThreshold skill psiA psiB c - c ≤
      sourceDisadvantagedThreshold skill psiA psiB d - d := by
  have htheta : sourceDisadvantagedThreshold skill psiA psiB c ≤
      sourceDisadvantagedThreshold skill psiA psiB d := (monotone_cdf _) hcd
  have h := sourceDisadvantagedRank_increment_le hfcont hf hf0 hconv hB hBA
    sourceDisadvantagedThreshold_mem sourceDisadvantagedThreshold_mem htheta
  rw [sourceDisadvantagedThreshold_inverse hfcont hf hf0 hB hBA ⟨hc, hcd.trans hd⟩,
    sourceDisadvantagedThreshold_inverse hfcont hf hf0 hB hBA ⟨hc.trans hcd, hd⟩] at h
  linarith

/-- The source access comparison, including thresholds beyond the group's
support. Convexity is required only on the latent skill interval. -/
theorem sourceDisadvantagedAccess_antitone_of_convex_cdf {skill : ℝ → ℝ} {psiA psiB rho : ℝ}
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hconv : ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill))
    (hB : 0 < psiB) (hBA : psiB < psiA) (hrho : 0 ≤ rho) :
    AntitoneOn (fun c => twoLevelDisadvantagedAccess rho c
      (sourceDisadvantagedThreshold skill psiA psiB c)) (Ico (0 : ℝ) 1) := by
  intro c hc d hd hcd
  dsimp only
  by_cases htop : sourceDisadvantagedRank skill psiA psiB 1 ≤ d
  · rw [sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB htop]
    unfold twoLevelDisadvantagedAccess
    simp only [sub_self, mul_zero]
    exact mul_nonneg (div_nonneg hrho (sub_pos.mpr hc.2).le)
      (sub_nonneg.mpr sourceDisadvantagedThreshold_mem.2)
  have hgap := sourceDisadvantagedThreshold_gap_mono_on_support hfcont hf hf0 hconv hB hBA
    hc.1 hcd (lt_of_not_ge htop).le
  have hlow : c ≤ sourceDisadvantagedThreshold skill psiA psiB c := by
    rcases eq_or_lt_of_le hc.1 with heq | hpos
    · rw [← heq]
      exact sourceDisadvantagedThreshold_mem.1
    · exact (sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hpos, hc.2⟩).le
  exact twoLevel_access_nonincreasing_of_threshold_gap_monotone hrho hcd
    (sub_pos.mpr hc.2) (sub_pos.mpr hd.2) (sub_nonneg.mpr hlow) hgap

/-- Proposition 4.4's monotonicity statement for every selection of actual
equilibria across feasible two-level policies in one fixed population.
The only distributional shape premise is the source's convex latent CDF
on its support. Neither differentiability nor overlapping supports is needed. -/
theorem sourceActualDisadvantagedAccess_antitone_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score : ℝ → Bool × ℝ → ℝ} {tie : Bool × ℝ → ℝ}
    {baseline psiA psiB rho : ℝ}
    (hrho : 0 < rho) (hbaseline : 0 ≤ baseline)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost baseline = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0)
    (hconv : ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill))
    (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c)) (htie : Measurable tie)
    (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort c x)) :
    AntitoneOn (fun c => sourceActualDisadvantagedAccess (score c) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c)) (Ioc (0 : ℝ) (1 - rho)) := by
  have hformula (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    (sourceActualDisadvantagedAccess_lt_pureRandomization_of_sourcePrimitives hrho hc hbaseline
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA
      (hscore c hc) htie hinj (hbest c hc)).2.1
  have hm := sourceDisadvantagedAccess_antitone_of_convex_cdf hfcont hf hf0 hconv hB hBA hrho.le
  intro c hc d hd hcd
  dsimp only
  rw [hformula c hc, hformula d hd]
  exact hm ⟨hc.1.le, by linarith [hc.2]⟩ ⟨hd.1.le, by linarith [hd.2]⟩ hcd

end LBG22StrategicRanking
