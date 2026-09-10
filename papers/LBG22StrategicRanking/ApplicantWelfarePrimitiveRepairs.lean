import LBG22StrategicRanking.FinitePopulationUtilityPrimitiveRepairs

/-!
# Applicant welfare under actual rank policies

The expected admission reward is fixed by capacity. Best response bounds
effort cost by the reward range, so the actual welfare integral equals
capacity minus expected cost. A constant-reward policy attains capacity at
the cost-minimizing effort, including a positive effort baseline.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Population mean of the actual admission reward minus individual effort cost. -/
noncomputable def sourceFiniteApplicantWelfare {n : ℕ}
    (cost effort score tie : ℝ → ℝ) (cutoff : Fin (n + 1) → ℝ) (reward : ℕ → ℝ) : ℝ :=
  ∫ t, reward (finiteLowerRankBand cutoff (tieBrokenRank unitRankMeasure score tie t)).val -
    cost (effort t) ∂unitRankMeasure

/-- The capacity formula holds for every measurable score profile. It uses
the uniform law of actual tie-broken ranks, not an equilibrium-band premise. -/
theorem sourceFiniteAdmission_mean_of_measurable_score
    {score tie : ℝ → ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1) (hscore : Measurable score)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    Integrable (fun t => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val) unitRankMeasure ∧
    (∫ t, reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val ∂unitRankMeasure) =
      ∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * reward i.val := by
  let rank := tieBrokenRank unitRankMeasure score tie
  let R := fun r => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) r).val
  haveI := noAtoms_map_tie_of_injOn_unitRank htie hinj
  have hd : Measure.map rank unitRankMeasure = unitRankMeasure :=
    (tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure hscore htie).trans
      restrict_Ioc_eq_restrict_Icc.symm
  have hrank : Measurable rank := measurable_tieBrokenRank hscore htie
  have h := integral_finiteLowerRankBand (fun i : Fin (n + 1) => reward i.val) hc hc0 hcn
  have hi : Integrable R (Measure.map rank unitRankMeasure) := by
    rw [hd]
    exact h.1
  refine ⟨hi.comp_measurable hrank, ?_⟩
  calc
    (∫ t, R (rank t) ∂unitRankMeasure) = ∫ r, R r ∂Measure.map rank unitRankMeasure :=
      (integral_map hrank.aemeasurable hi.aestronglyMeasurable).symm
    _ = ∫ r, R r ∂unitRankMeasure := by rw [hd]
    _ = _ := h.2

/-- Best response and the bounded admission reward imply integrability of
effort cost. No bounded-action assumption is imposed on deviations. -/
theorem sourceFiniteBestResponse_cost_integrable
    {cost production skill effort score tie : ℝ → ℝ} {baseline : ℝ}
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hb : 0 ≤ baseline) (hp : ContinuousOn cost (Ici 0))
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost baseline = 0)
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (heffort : AEMeasurable effort unitRankMeasure)
    (hbest : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill score tie cutoff reward t (effort t)) :
    Integrable (fun t => cost (effort t)) unitRankMeasure ∧
      ∀ᵐ t ∂unitRankMeasure, cost (effort t) ∈ Icc (0 : ℝ) 1 := by
  let R := fun r => reward (finiteLowerRankBand cutoff r).val
  have hlo (r : ℝ) : reward 0 ≤ R r := hr ⟨le_rfl, Nat.zero_le _⟩
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt⟩ (Nat.zero_le _)
  have hhi (r : ℝ) : R r ≤ reward n := hr
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt⟩
    ⟨Nat.zero_le _, le_rfl⟩ (Nat.le_of_lt_succ (finiteLowerRankBand cutoff r).isLt)
  have hbound : ∀ᵐ t ∂unitRankMeasure, cost (effort t) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hbest] with t ht
    refine ⟨hpN _ ht.1, ?_⟩
    have h := sourceBestResponse_cost_le_reward_range unitRankMeasure score tie t hb hp0 hlo
      (hhi (tieBrokenRank unitRankMeasure score tie t)) ht.2.2
    linarith
  have hpc : Continuous (fun e : ℝ => cost (max 0 e)) :=
    hp.comp_continuous (continuous_const.max continuous_id) (fun e => (show 0 ≤ max 0 e from le_max_left _ _))
  have hm : AEStronglyMeasurable (fun t => cost (effort t)) unitRankMeasure := by
    apply (hpc.comp_aestronglyMeasurable heffort.aestronglyMeasurable).congr
    filter_upwards [hbest] with t ht
    simp only [max_eq_right ht.1]
  refine ⟨(integrable_const (1 : ℝ)).mono' hm ?_, hbound⟩
  filter_upwards [hbound] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

/-- Actual welfare is capacity minus expected effort cost. This identity and
the upper bound use proved reward and cost integrability. -/
theorem sourceFiniteApplicantWelfare_eq_capacity_sub_cost
    {cost production skill effort score tie : ℝ → ℝ} {baseline rho : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hb : 0 ≤ baseline) (hp : ContinuousOn cost (Ici 0))
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost baseline = 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hcap : (∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * reward i.val) = rho)
    (heffort : AEMeasurable effort unitRankMeasure) (hscore : Measurable score)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) :
    Integrable (fun t => cost (effort t)) unitRankMeasure ∧
    Integrable (fun t => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (tieBrokenRank unitRankMeasure score tie t)).val - cost (effort t)) unitRankMeasure ∧
    sourceFiniteApplicantWelfare cost effort score tie (fun i : Fin (n + 1) => cutoff i) reward =
      rho - ∫ t, cost (effort t) ∂unitRankMeasure ∧
    sourceFiniteApplicantWelfare cost effort score tie (fun i : Fin (n + 1) => cutoff i) reward ≤ rho := by
  have hi := sourceFiniteAdmission_mean_of_measurable_score (reward := reward) hc hc0 hcn hscore htie hinj
  have hpI := sourceFiniteBestResponse_cost_integrable (fun i : Fin (n + 1) => cutoff i)
    hb hp hpN hp0 hr hr0 hrn heffort hbest
  have heq : sourceFiniteApplicantWelfare cost effort score tie (fun i : Fin (n + 1) => cutoff i) reward =
      rho - ∫ t, cost (effort t) ∂unitRankMeasure := by
    unfold sourceFiniteApplicantWelfare
    rw [integral_sub hi.1 hpI.1, hi.2, hcap]
  refine ⟨hpI.1, hi.1.sub hpI.1, heq, ?_⟩
  rw [heq]
  exact sub_le_self _ (integral_nonneg_of_ae (hpI.2.mono (fun _ h => h.1)))

/-- The score profile of pure randomization at the cost-minimizing effort. -/
noncomputable def sourcePureRandomizationScore (production skill : ℝ → ℝ) (baseline : ℝ) : ℝ → ℝ :=
  fun t => production baseline * sourceClampedSkill skill t

/-- Constant admission reward makes the cost-minimizing effort an actual
equilibrium and gives welfare equal to capacity, even with positive baseline
production. Neither technology curvature nor zero baseline effort is needed. -/
theorem sourcePureRandomization_equilibrium_and_welfare
    {cost production skill tie : ℝ → ℝ} {baseline rho : ℝ}
    (hb : 0 ≤ baseline) (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost baseline = 0)
    (hf : ContinuousOn skill (Icc (0 : ℝ) 1)) :
    let score := sourcePureRandomizationScore production skill baseline
    Measurable score ∧
    (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun _ : Fin 1 => 0) (fun _ => rho) t baseline) ∧
    (∫ t, (fun _ : ℕ => rho) (finiteLowerRankBand (fun _ : Fin 1 => 0)
      (tieBrokenRank unitRankMeasure score tie t)).val ∂unitRankMeasure) = rho ∧
    sourceFiniteApplicantWelfare cost (fun _ => baseline) score tie (fun _ : Fin 1 => 0) (fun _ => rho) = rho := by
  refine ⟨(continuous_const.mul (continuous_sourceClampedSkill hf)).measurable, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine ⟨hb, ?_, ?_⟩
    · change production baseline * sourceClampedSkill skill t = production baseline * skill t
      rw [sourceClampedSkill_eq ⟨ht.1.le, ht.2⟩]
    · intro d hd
      change rho - cost d ≤ rho - cost baseline
      rw [hp0]
      linarith [hpN d hd]
  · simp
  · simp [sourceFiniteApplicantWelfare, hp0]

/-- The source primitives and measurable equilibrium scores already force
measurable efforts; effort measurability is not an extra welfare hypothesis. -/
theorem sourceFiniteBaselineEquilibrium_effort_aemeasurable
    {cost production skill effort score tie : ℝ → ℝ} {baseline : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ} (hb : 0 ≤ baseline)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) : AEMeasurable effort unitRankMeasure := by
  obtain ⟨E, hE, hpE, hm, _, _, _, huniq⟩ :=
    exists_unique_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
      hb hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfcont hf hf0 hr hr0 hrn htie hinj
  exact hm.congr (huniq effort score hscore hbest).symm

/-- Proposition 3.1's pure-randomization optimum for actual finite-policy
equilibria. All cost, reward, and welfare integrability follows from the
source primitives. The same population, technology, and tie key are used by
the competing policy and the constructed pure-randomization equilibrium. -/
theorem sourceFiniteApplicantWelfare_maximized_by_pureRandomization_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {baseline rho : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ} (hb : 0 ≤ baseline)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hcap : (∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * reward i.val) = rho)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) :
    let pureScore := sourcePureRandomizationScore production skill baseline
    rho ∈ Icc (0 : ℝ) 1 ∧ Measurable pureScore ∧
    (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill pureScore tie
      (fun _ : Fin 1 => 0) (fun _ => rho) t baseline) ∧
    Integrable (fun t => cost (effort t)) unitRankMeasure ∧
    sourceFiniteApplicantWelfare cost (fun _ => baseline) pureScore tie (fun _ : Fin 1 => 0) (fun _ => rho) = rho ∧
    sourceFiniteApplicantWelfare cost effort score tie (fun i : Fin (n + 1) => cutoff i) reward ≤
      sourceFiniteApplicantWelfare cost (fun _ => baseline) pureScore tie (fun _ : Fin 1 => 0) (fun _ => rho) := by
  have hm := sourceFiniteBaselineEquilibrium_effort_aemeasurable
    hb hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfcont hf hf0 hr hr0 hrn hscore htie hinj hbest
  have hw := sourceFiniteApplicantWelfare_eq_capacity_sub_cost
    hb hp hpN hp0 hc hc0 hcn hr.monotoneOn hr0 hrn hcap hm hscore htie hinj hbest
  have hP := sourcePureRandomization_equilibrium_and_welfare
    (production := production) (tie := tie) (rho := rho) hb hpN hp0 hfcont
  have hwN (i : Fin (n + 1)) : 0 ≤ cutoff (i.val + 1) - cutoff i.val :=
    sub_nonneg.mpr (hc.monotoneOn ⟨Nat.zero_le _, Nat.le_of_lt i.isLt⟩
      ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩ (Nat.le_succ _))
  have hrI (i : Fin (n + 1)) : reward i.val ∈ Icc (0 : ℝ) 1 :=
    ⟨hr0.trans (hr.monotoneOn ⟨le_rfl, Nat.zero_le _⟩
      ⟨Nat.zero_le _, Nat.le_of_lt_succ i.isLt⟩ (Nat.zero_le _)),
      (hr.monotoneOn ⟨Nat.zero_le _, Nat.le_of_lt_succ i.isLt⟩
        ⟨Nat.zero_le _, le_rfl⟩ (Nat.le_of_lt_succ i.isLt)).trans hrn⟩
  have hsum : (∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val)) = 1 := by
    simpa using (integral_finiteLowerRankBand (fun _ : Fin (n + 1) => (1 : ℝ)) hc hc0 hcn).2.symm
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    rw [← hcap]
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hwN i) (hrI i).1), ?_⟩
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hwN i) (hrI i).2)
  exact ⟨hrho, hP.1, hP.2.1, hw.1, hP.2.2.2, by rw [hP.2.2.2]; exact hw.2.2.2⟩

/-- Every actual two-level equilibrium has the primitive applicant-welfare
formula, including the zero-effort region below the cutoff. -/
theorem sourceActualTwoLevelApplicantWelfare_eq_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort t)) :
    sourceFiniteApplicantWelfare cost effort score tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) =
      sourceTwoLevelApplicantWelfare cost production skill E rho c := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hcut := sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩
  have hrew := sourceTwoLevelReward_strictMono hrho hc1
  have hr0 : 0 ≤ sourceTwoLevelReward rho c 0 := by simp [sourceTwoLevelReward]
  have hr1 : sourceTwoLevelReward rho c 1 ≤ 1 := by
    simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
    exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])
  have hcut0 : sourceTwoLevelCutoff c 0 = 0 := by simp [sourceTwoLevelCutoff]
  have hcut2 : sourceTwoLevelCutoff c 2 = 1 := by norm_num [sourceTwoLevelCutoff]
  have hcap : (∑ i : Fin 2, (sourceTwoLevelCutoff c (i.val + 1) - sourceTwoLevelCutoff c i.val) *
      sourceTwoLevelReward rho c i.val) = rho := by
    norm_num [Fin.sum_univ_succ, sourceTwoLevelCutoff, sourceTwoLevelReward]
    field_simp [(sub_pos.mpr hc1).ne']
  have hm := sourceFiniteBaselineEquilibrium_effort_aemeasurable
    (baseline := 0) le_rfl hp hpC hpN hp0 hg hgM hgC hg0 hcut hcut0 hcut2 hfcont hf hf0 hrew hr0 hr1 hscore htie hinj hbest
  have hw := sourceFiniteApplicantWelfare_eq_capacity_sub_cost
    (baseline := 0) le_rfl hp hpN hp0 hcut hcut0 hcut2 hrew.monotoneOn hr0 hr1 hcap hm hscore htie hinj hbest
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0
  have hgEc : ContinuousOn production (Icc 0 E) := hg.mono Icc_subset_Ici_self
  have hgEm : StrictMonoOn production (Icc 0 E) := hgM.mono Icc_subset_Ici_self
  obtain ⟨F, hF, hpF, heffort⟩ := sourceFiniteEquilibrium_effort_unique_of_sourcePrimitives
    hp hpC hpN hp0 hg hgM hgC hg0 hcut hcut0 hcut2 hfcont hf hf0 hrew hr0 hr1 hscore htie hinj hbest
  have hFE : F = E := hpm.injOn hF.le hE (hpF.trans hpE.symm)
  rw [hFE] at heffort
  have ha := (sourceScoreScale_mem_and_strictMono hrho hE (hp.mono Icc_subset_Ici_self)
    (hpm.mono Icc_subset_Ici_self) hp0 hpE hgEm).1 c hc
  have hfpos (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < skill t :=
    hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  have hcostAE : (fun t => cost (effort t)) =ᵐ[unitRankMeasure]
      (Ioc c 1).indicator (fun t => cost (sourceTwoLevelEffort cost production skill E rho c t)) := by
    filter_upwards [heffort, ae_restrict_mem measurableSet_Ioc] with t htE ht
    rw [htE]
    by_cases hct : c < t
    · rw [indicator_of_mem (show t ∈ Ioc c 1 from ⟨hct, ht.2⟩)]
      congr 1
      unfold sourceFiniteRankEffort
      rw [finiteLowerRankBand_twoLevel, if_pos hct, sourceRecursiveBandScore_twoLevel hE hp0 hgEm hg0,
        sourceClampedSkill_eq ⟨ht.1.le, ht.2⟩, mul_div_assoc]
      have htarget : sourceScoreScale cost production E rho c * (skill c / skill t) ≤ production E :=
        (mul_le_of_le_one_right (hg0.trans ha.1.le)
          ((div_le_one (hfpos t ht)).mpr (hf.monotoneOn ⟨hc.1.le, hc1.le⟩ ⟨ht.1.le, ht.2⟩ hct.le))).trans ha.2
      exact (max_eq_left (sourceEffortAtScore_spec hE hgEc hgEm.monotoneOn htarget).1.1).symm
    · rw [indicator_of_notMem (show t ∉ Ioc c 1 from fun h => hct h.1)]
      unfold sourceFiniteRankEffort
      rw [finiteLowerRankBand_twoLevel, if_neg hct]
      simp only [sourceRecursiveBandScore, zero_div, sourceEffortAtScore_zero hE hgEm hg0, hp0]
  have hcostIntegral : (∫ t, cost (effort t) ∂unitRankMeasure) =
      ∫ t in c..1, cost (sourceTwoLevelEffort cost production skill E rho c t) := by
    rw [integral_congr_ae hcostAE, integral_indicator measurableSet_Ioc]
    change (∫ t, cost (sourceTwoLevelEffort cost production skill E rho c t)
      ∂(volume.restrict (Ioc (0 : ℝ) 1)).restrict (Ioc c 1)) = _
    rw [Measure.restrict_restrict_of_subset (show Ioc c 1 ⊆ Ioc (0 : ℝ) 1 from
      fun _ ht => ⟨hc.1.trans ht.1, ht.2⟩), intervalIntegral.integral_of_le hc1.le]
  rw [hw.2.2.1, hcostIntegral]
  rfl

/-- The two-level welfare comparison for arbitrary actual
equilibria, under increasing upper-tail skill ratios and geometric concavity of effort cost
in produced-score units. These quantitative shape restrictions are local to
this monotonicity claim; they are not needed for pure randomization's optimum. -/
theorem sourceActualTwoLevelApplicantWelfare_antitone_of_skillRatio
    {cost production skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ} {E rho : ℝ}
    (hrho : 0 < rho) (hE : 0 < E) (hpE : cost E = 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hfRatio : ∀ s ∈ Icc (0 : ℝ) 1,
      MonotoneOn (fun c => skill c / skill (admittedTailRank c s)) (Ioc (0 : ℝ) 1))
    (hscoreCost : ConcaveOn ℝ {z | production 0 < Real.exp z ∧ Real.exp z ≤ production E}
      (fun z => Real.log (cost (effortIntervalInverse production E (Real.exp z)))))
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c))
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t)) :
    AntitoneOn (fun c => sourceFiniteApplicantWelfare cost (effort c) (score c) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c)) (Ioc (0 : ℝ) (1 - rho)) := by
  have heq (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceActualTwoLevelApplicantWelfare_eq_of_sourcePrimitives hrho hc hE.le hpE
      hp hpC hpN hp0 hg hgM hgC hg0 hfcont hf hf0 (hscore c hc) htie hinj (hbest c hc)
  have hm := sourceTwoLevelApplicantWelfare_antitone_of_skillRatio hrho hE (hp.mono Icc_subset_Ici_self)
    ((sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0).mono Icc_subset_Ici_self) hp0 hpE
    (hg.mono Icc_subset_Ici_self) (hgM.mono Icc_subset_Ici_self) hg0
    (hfcont.mono Ioc_subset_Icc_self)
    (fun t ht => hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1))
    (hf.monotoneOn.mono Ioc_subset_Icc_self) hfRatio hscoreCost
  intro c hc d hd hcd
  dsimp only
  rw [heq c hc, heq d hd]
  exact hm hc hd hcd

/-- Log-concave skills give the sufficient upper-tail ratio condition for
monotonicity of welfare in every actual equilibrium. -/
theorem sourceActualTwoLevelApplicantWelfare_antitone_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ} {E rho : ℝ}
    (hrho : 0 < rho) (hE : 0 < E) (hpE : cost E = 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hfLog : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (skill t)))
    (hscoreCost : ConcaveOn ℝ {z | production 0 < Real.exp z ∧ Real.exp z ≤ production E}
      (fun z => Real.log (cost (effortIntervalInverse production E (Real.exp z)))))
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c))
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t)) :
    AntitoneOn (fun c => sourceFiniteApplicantWelfare cost (effort c) (score c) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c)) (Ioc (0 : ℝ) (1 - rho)) := by
  have hfpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t := fun t ht =>
    hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  exact sourceActualTwoLevelApplicantWelfare_antitone_of_skillRatio hrho hE hpE hp hpC hpN hp0
    hg hgM hgC hg0 hfcont hf hf0
    (fun _ hs => admittedTail_skill_ratio_monotone hfpos
      (hf.monotoneOn.mono Ioc_subset_Icc_self) hfLog hs) hscoreCost htie hinj hscore hbest

end LBG22StrategicRanking
