import LBG22StrategicRanking.MultitaskPrimitiveRepairs
import LBG22StrategicRanking.GroupProfilePrimitiveRepairs

/-!
# Selection-independent multitask equilibrium profiles

An arbitrary measurable score profile and almost-everywhere best responses
determine the same admission bands and admitted efforts as the canonical
construction. The unmeasurable skill coordinate need not be observable to
the school and the fixed tie key may depend on both skill coordinates.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped Topology

/-- Additional independent skill coordinates do not change the measurable
task's pre-effort rank. Actual best responses therefore preserve the two
admission bands, without assuming a rank or effort formula. -/
theorem sourceMultitaskScalarEquilibrium_rank_preservation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {effort score tie : ℝ × α → ℝ} {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hbest : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourcePopulationFiniteBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ᵐ x ∂unitRankMeasure.prod μ,
      c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1 := by
  let f := fun x : ℝ × α => sourceClampedSkill skill x.1
  have hfc := (continuous_sourceClampedSkill hfcont).measurable
  have hfm : Measurable f := hfc.comp measurable_fst
  have hmem : ∀ᵐ x ∂unitRankMeasure.prod μ, x.1 ∈ Ioc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := unitRankMeasure) (ν := μ)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc)
  have hfmap : Measure.map f (unitRankMeasure.prod μ) =
      Measure.map (sourceClampedSkill skill) unitRankMeasure := by
    change Measure.map (sourceClampedSkill skill ∘ Prod.fst) _ = _
    rw [← Measure.map_map hfc measurable_fst,
      (measurePreserving_fst (μ := unitRankMeasure) (ν := μ)).map_eq]
  haveI : NoAtoms (Measure.map f (unitRankMeasure.prod μ)) := by
    rw [hfmap]
    apply noAtoms_map_tie_of_injOn_unitRank hfc
    intro x hx y hy hxy
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩, sourceClampedSkill_eq ⟨hy.1.le, hy.2⟩] at hxy
    exact hf.injOn ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy
  have hpositive : ∀ᵐ x ∂unitRankMeasure.prod μ, 0 < f x := by
    filter_upwards [hmem] with x hx
    change 0 < sourceClampedSkill skill x.1
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩]
    exact hf0.trans_lt (hf (by norm_num) ⟨hx.1.le, hx.2⟩ hx.1)
  have hbest' : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourcePopulationFiniteBestResponseAt (unitRankMeasure.prod μ) cost production f score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x) := by
    filter_upwards [hmem, hbest] with x hx hb
    simpa only [SourcePopulationFiniteBestResponseAt, f,
      sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩] using hb
  have hpres := sourcePopulationFiniteEquilibrium_rank_preservation (unitRankMeasure.prod μ)
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (by norm_num : (0 : ℝ) ≤ 0)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfm hpositive
    (sourceTwoLevelReward_strictMono hrho (by linarith [hc.2])) hscore htie hbest'
  filter_upwards [hmem, hpres] with x hx hr
  have hpre : cdf (Measure.map f (unitRankMeasure.prod μ)) (f x) = x.1 := by
    rw [hfmap]
    change sourceSkillCDF skill (sourceClampedSkill skill x.1) = x.1
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩, sourceSkillCDF_at_quantile hfcont hf ⟨hx.1.le, hx.2⟩]
  rw [hpre] at hr
  have hv := congrArg Fin.val hr
  rw [finiteLowerRankBand_twoLevel, finiteLowerRankBand_twoLevel] at hv
  by_cases hpost : c < tieBrokenRank (unitRankMeasure.prod μ) score tie x <;>
    by_cases hlatent : c < x.1 <;> simp [hpost, hlatent] at hv ⊢

/-- Every scalar equilibrium on the joint skill population has the canonical
two-level effort profile. A full-measure skill fiber supplies applicants
approaching the cutoff from both sides; their deviations still face the
entire population. Boundary indifference then pins down the common score,
and same-reward deviations extend that score to all other fibers. -/
theorem sourceMultitaskScalarEquilibrium_profile
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {effort score tie : ℝ × α → ℝ} {E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hbest : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourcePopulationFiniteBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) x (effort x)) :
    ∀ᵐ x ∂unitRankMeasure.prod μ,
      (c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1) ∧
      (x.1 ≤ c → effort x = 0) ∧
      (c < x.1 → effort x = sourceTwoLevelEffort cost production skill E rho c x.1 ∧
        score x = max (sourceScoreScale cost production E rho c * skill c)
          (production 0 * skill x.1)) := by
  let ν := unitRankMeasure.prod μ
  let q := rho / (1 - c)
  let R := fun r => sourceTwoLevelReward rho c
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val
  have hc1 : c < 1 := by linarith [hc.2]
  have hq : 0 < q := div_pos hrho (sub_pos.mpr hc1)
  have hq1 : q ≤ 1 := (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])
  have hR : Monotone R := monotone_finiteLowerRankReward _
    (sourceTwoLevelReward_strictMono hrho hc1).monotoneOn
  have hReq (r : ℝ) : R r = if c < r then q else 0 := by
    dsimp only [R]
    rw [finiteLowerRankBand_twoLevel]
    split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero, q]
  have hR0 (r : ℝ) : 0 ≤ R r := by rw [hReq]; split <;> positivity
  have hR1 (r : ℝ) : R r ≤ 1 := by rw [hReq]; split <;> linarith
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hfp : 0 < skill c := hf0.trans_lt (hf (by norm_num) ⟨hc.1.le, hc1.le⟩ hc.1)
  have hfat : ContinuousAt skill c := hfcont.continuousAt (Icc_mem_nhds hc.1 hc1)
  have hadmit := sourceMultitaskScalarEquilibrium_rank_preservation μ hrho hc hpcont hpconv hpnonneg
    hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hscore htie hbest
  have hmem : ∀ᵐ x ∂ν, x.1 ∈ Ioc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := unitRankMeasure) (ν := μ)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc)
  let goodPop := fun x : ℝ × α => x.1 ∈ Ioc (0 : ℝ) 1 ∧ effort x ∈ Icc (0 : ℝ) E ∧
    score x = production (effort x) * skill x.1 ∧
    R (tieBrokenRank ν score tie x) = (if c < x.1 then q else 0) ∧
    ∀ d : ℝ, 0 ≤ d →
      R (counterfactualTieBrokenRank ν score tie x (production d * skill x.1)) - cost d ≤
        R (tieBrokenRank ν score tie x) - cost (effort x)
  have hgoodPop : ∀ᵐ x ∂ν, goodPop x := by
    filter_upwards [hmem, hbest, hadmit] with x hx hb hr
    have hcost := sourceBestResponse_cost_le_reward_range ν score tie x
      (baseline := 0) (by norm_num) hpzero hR0 (hR1 _) hb.2.2
    have heE : effort x ≤ E := by
      by_contra hn
      have hlt := hpm hE hb.1 (lt_of_not_ge hn)
      rw [hpE] at hlt
      linarith
    exact ⟨hx, ⟨hb.1, heE⟩, hb.2.1, by simpa only [ν, hReq, hr], hb.2.2⟩
  have hfibers : ∀ᵐ u ∂μ, ∀ᵐ t ∂unitRankMeasure, goodPop (t, u) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hgoodPop)
  obtain ⟨u, hu⟩ := hfibers.exists
  let e := fun t => effort (t, u)
  let good := {t : ℝ | goodPop (t, u)}
  have hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good := hu
  let T := sourceEquilibriumBandThreshold (fun t => score (t, u)) good c 1
  have hprops := sourceEquilibriumBandThreshold_properties ν (fun t => (t, u))
    score tie skill e hgood hc.1.le le_rfl hc1 hE hpconv hpnonneg hpzero hgcont hgm hg0 hR
    hfcont hf hf0 (fun x hx => hx.2.2.1) (fun x hx => hx.2.2.2.1)
    (fun x hx => by rw [hx.2.2.2.2.1, if_pos hx.1.1]) (fun x hx => hx.2.2.2.2.2)
  change 0 ≤ T ∧ production 0 * skill c ≤ T ∧ T ≤ production E * skill c ∧
    ∀ x ∈ Ioo c 1 ∩ good, score (x, u) = max T (production 0 * skill x) ∧
      sourceEffortAtScore production E (T / skill x) = e x at hprops
  have hlow (x : ℝ × α) (hx : goodPop x) (hl : x.1 ≤ c) : effort x = 0 := by
    have hrew : R (tieBrokenRank ν score tie x) = 0 := by
      rw [hx.2.2.2.1, if_neg (not_lt.mpr hl)]
    have hcost := sourceBestResponse_cost_le_reward_range ν score tie x
      (baseline := 0) (by norm_num) hpzero hR0 hrew.le hx.2.2.2.2
    have hz : cost (effort x) = cost 0 := by rw [hpzero]; linarith [hpnonneg _ hx.2.1.1]
    exact hpm.injOn hx.2.1.1 (by simp) hz
  have hgE : production 0 ≤ production E := hgm.monotoneOn (by simp) hE hE
  have hgap := sourceBestResponses_adjacent_boundary_cost_gap ν (fun t => (t, u))
    score tie skill e (lowScore := fun t => production 0 * skill t)
    (highScore := fun t => max T (production 0 * skill t))
    (a := 0) (b := 1) (lowReward := 0) (highReward := q)
    hgood (by norm_num) le_rfl hc.1 hc1 hE hpcont hgcont hgm hR hfat hfp
    (continuousAt_const.mul hfat) (continuousAt_const.max (continuousAt_const.mul hfat))
    (by simpa only [mul_div_cancel_right₀ _ hfp.ne'] using hgE)
    (by dsimp only; rw [max_eq_left hprops.2.1]; exact (div_le_iff₀ hfp).mpr hprops.2.2.1)
    (fun x hx => hx.2.2.1) (fun x hx => hx.2.2.2.1)
    (fun x hx => by rw [hx.2.2.2.1, hlow (x, u) hx.2 hx.1.2.le])
    (fun x hx => (hprops.2.2.2 x hx).1)
    (fun x hx => by rw [hx.2.2.2.2.1, if_neg (not_lt.mpr hx.1.2.le)])
    (fun x hx => by rw [hx.2.2.2.2.1, if_pos hx.1.1]) (fun x hx => hx.2.2.2.2.2)
  have hzero : sourceCostAtScore cost production E (production 0 * skill c / skill c) = 0 := by
    rw [mul_div_cancel_right₀ _ hfp.ne']
    change cost (sourceEffortAtScore production E (production 0)) = 0
    rw [sourceEffortAtScore_at_production (hgm.mono Icc_subset_Ici_self) ⟨le_rfl, hE⟩, hpzero]
  rw [sourceCostAtScore_max_baseline hfp, hzero, sub_zero, sub_zero] at hgap
  have hTcanonical := sourceBoundaryThreshold_eq_scoreScale hE (hpm.mono Icc_subset_Ici_self)
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self).monotoneOn
    hfp hprops.2.1 hprops.2.2.1 hgap
  have hTstrict : production 0 * skill c < T := by
    by_contra hn
    have hbase : T = production 0 * skill c := le_antisymm (le_of_not_gt hn) hprops.2.1
    rw [hbase, hzero] at hgap
    exact hq.ne' hgap.symm
  have hclosure : c ∈ closure (Ioo c 1 ∩ good) := by
    rw [sourceFullMeasure_closure_band hgood hc.1.le le_rfl hc1]
    exact ⟨le_rfl, hc1.le⟩
  have hnear : ∀ᶠ t in nhds c, production 0 * skill t < T :=
    (continuousAt_const.mul hfat).eventually (Iio_mem_nhds hTstrict)
  obtain ⟨w, hw, hwfloor⟩ := ((mem_closure_iff_frequently.mp hclosure).and_eventually hnear).exists
  have hwscore : score (w, u) = T := by rw [(hprops.2.2.2 w hw).1, max_eq_left hwfloor.le]
  have hwpos : 0 < e w := by
    apply lt_of_le_of_ne hw.2.2.1.1
    intro hz
    have h := hw.2.2.2.1
    rw [← hz, hwscore] at h
    exact hwfloor.ne h.symm
  have hwreward : R (tieBrokenRank ν score tie (w, u)) = q := by
    rw [hw.2.2.2.2.1, if_pos hw.1.1]
  filter_upwards [hgoodPop, hadmit] with x hx hr
  refine ⟨hr, hlow x hx, ?_⟩
  intro hhigh
  have hsp : 0 < skill x.1 := hf0.trans_lt (hf (by norm_num) ⟨hx.1.1.le, hx.1.2⟩ hx.1.1)
  have hactual := hx.2.2.1
  have hreward : R (tieBrokenRank ν score tie x) = q := by rw [hx.2.2.2.1, if_pos hhigh]
  have hTle : T ≤ score x := by
    rw [← hwscore]
    exact sourceBestResponse_score_le_of_same_reward ν score tie (w, u) x
      (baseline := 0) (by norm_num) hpm hgcont hR hwpos hw.2.2.2.1
      (hreward.trans hwreward.symm) hw.2.2.2.2.2
  have hshape : score x = max T (production 0 * skill x.1) := by
    rcases eq_or_lt_of_le hx.2.1.1 with he0 | he0
    · have heq : score x = production 0 * skill x.1 := by rw [hactual, ← he0]
      rw [← heq, max_eq_right hTle]
    · have hle : score x ≤ T := by
        rw [← hwscore]
        exact sourceBestResponse_score_le_of_same_reward ν score tie x (w, u)
          (baseline := 0) (by norm_num) hpm hgcont hR he0 hactual
          (hwreward.trans hreward.symm) hx.2.2.2.2
      have hfloor : production 0 * skill x.1 ≤ score x := by
        rw [hactual]
        exact mul_le_mul_of_nonneg_right (hgm.monotoneOn (by simp) hx.2.1.1 hx.2.1.1) hsp.le
      rw [le_antisymm hTle hle, max_eq_left hfloor]
  have hprod : production (effort x) = max (T / skill x.1) (production 0) := by
    have h := congrArg (fun z => z / skill x.1) hshape
    dsimp only at h
    rw [hactual, mul_div_cancel_right₀ _ hsp.ne', ← max_div_div_right hsp.le,
      mul_div_cancel_right₀ _ hsp.ne'] at h
    exact h
  have hcap : T / skill x.1 ≤ production E := (div_le_iff₀ hsp).mpr (hTle.trans (by
    rw [hactual]
    exact mul_le_mul_of_nonneg_right (hgm.monotoneOn hx.2.1.1 hE hx.2.1.2) hsp.le))
  have hi := sourceEffortAtScore_spec hE (hgcont.mono Icc_subset_Ici_self)
    (hgm.mono Icc_subset_Ici_self).monotoneOn hcap
  have heffort : sourceEffortAtScore production E (T / skill x.1) = effort x :=
    hgm.injOn hi.1.1 hx.2.1.1 (hi.2.trans hprod.symm)
  have hformula : sourceTwoLevelEffort cost production skill E rho c x.1 = effort x := by
    change max (sourceEffortAtScore production E
      (sourceScoreScale cost production E rho c * (skill c / skill x.1))) 0 = effort x
    rw [← mul_div_assoc, ← hTcanonical, heffort, max_eq_left hx.2.1.1]
  exact ⟨hformula.symm, by rwa [← hTcanonical]⟩

/-- Hard-budget equilibria inherit the canonical measurable effort profile;
the other task's effort is then determined by feasibility. The unit-cost cap
is only a normalization parameter, specified by `cost E = 1`. -/
theorem sourceHardBudgetEquilibrium_profile
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {effortM effortU score tie : ℝ × α → ℝ} {B E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hB : 0 ≤ B) (hpB : 1 ≤ cost B) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hbest : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie B rho c x (effortM x) (effortU x)) :
    ∀ᵐ x ∂unitRankMeasure.prod μ,
      (c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1) ∧
      effortU x = B - effortM x ∧ (x.1 ≤ c → effortM x = 0) ∧
      (c < x.1 → effortM x = sourceTwoLevelEffort cost production skill E rho c x.1 ∧
        score x = max (sourceScoreScale cost production E rho c * skill c)
          (production 0 * skill x.1)) := by
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hscalar : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourcePopulationFiniteBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (sourceTwoLevelReward rho c) x (effortM x) := by
    filter_upwards [hbest] with x hx
    exact sourceScalarBestResponseAt_of_hardBudget _ hrho hc hB hpm.monotoneOn hpzero hpB hx
  have hprofile := sourceMultitaskScalarEquilibrium_profile μ hrho hc hE hpE hpcont hpconv hpnonneg
    hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hscore htie hscalar
  filter_upwards [hprofile, hbest] with x hx hb
  exact ⟨hx.1, by linarith [hb.2.2.1], hx.2⟩

/-- Any two actual hard-budget equilibria agree almost everywhere in both
task efforts and the measurable score, under the original scalar primitives. -/
theorem sourceHardBudgetEquilibria_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ}
    {effortM effortU score effortM' effortU' score' tie : ℝ × α → ℝ} {B E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hB : 0 ≤ B) (hpB : 1 ≤ cost B) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hscore : Measurable score) (hscore' : Measurable score') (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hbest : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie B rho c x (effortM x) (effortU x))
    (hbest' : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score' tie B rho c x (effortM' x) (effortU' x)) :
    ∀ᵐ x ∂unitRankMeasure.prod μ,
      effortM x = effortM' x ∧ effortU x = effortU' x ∧ score x = score' x := by
  have h := sourceHardBudgetEquilibrium_profile μ hrho hc hB hpB hE hpE hpcont hpconv hpnonneg
    hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hscore htie hbest
  have h' := sourceHardBudgetEquilibrium_profile μ hrho hc hB hpB hE hpE hpcont hpconv hpnonneg
    hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hscore' htie hbest'
  filter_upwards [h, h', hbest, hbest'] with x hx hx' hb hb'
  have he : effortM x = effortM' x := by
    by_cases ha : c < x.1
    · exact (hx.2.2.2 ha).1.trans (hx'.2.2.2 ha).1.symm
    · exact (hx.2.2.1 (le_of_not_gt ha)).trans (hx'.2.2.1 (le_of_not_gt ha)).symm
  exact ⟨he, by rw [hx.2.1, hx'.2.1, he], by rw [hb.2.2.2.1, hb'.2.2.2.1, he]⟩

/-- Conditional school utility is independent of which actual hard-budget
equilibrium is selected. The equality is derived from best responses, not
assumed as an implementation or an equilibrium-selection condition. -/
theorem sourceHardBudgetEquilibrium_utility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {effortM effortU score tie : ℝ × α → ℝ} {B E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hB : 0 ≤ B) (hpB : 1 ≤ cost B) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hscore : Measurable score) (htie : Measurable tie)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hbest : ∀ᵐ x ∂unitRankMeasure.prod μ,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
        (fun x => skill x.1) score tie B rho c x (effortM x) (effortU x))
    (skillU : α → ℝ) (beta : ℝ) :
    sourceActualMultitaskSchoolUtility μ production skill skillU effortM effortU score tie rho beta c =
      sourceSkillConditionalSchoolUtility μ skillU cost production skill B E rho beta c := by
  have hp := sourceHardBudgetEquilibrium_profile μ hrho hc hB hpB hE hpE hpcont hpconv hpnonneg
    hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hscore htie hbest
  apply sourceActualMultitaskSchoolUtility_eq_of_profile μ (hp.mono fun _ hx => hx.1)
  filter_upwards [hp] with x hx
  intro ht
  exact ⟨(hx.2.2.2 ht.1).1, by rw [hx.2.1, (hx.2.2.2 ht.1).1]⟩

/-- The affine-skill supportability recovery holds for every equilibrium
selection across policies. The weight is chosen from the source primitives
before any equilibrium family is supplied. Original strict cost convexity
and global technology conditions give uniqueness; the additional affine
skill and curvature conditions are the documented local supportability
repair, not restrictions on the general equilibrium theorem. -/
theorem sourceHardBudget_supportability_independent_of_equilibrium_selection
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skillU : α → ℝ} (hskillU : Integrable skillU μ) (hmean : 0 < ∫ u, skillU u ∂μ)
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {tie : ℝ × α → ℝ} {B E rho lowerSkill skillWidth : ℝ}
    (htie : Measurable tie) [NoAtoms (Measure.map tie (unitRankMeasure.prod μ))]
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hE : 0 < E) (hB : 0 ≤ B)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e)
    (hp0 : cost 0 = 0) (hpE : cost E = 1) (hpB : 1 ≤ cost B)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) E, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) E, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hg0 : production 0 = 0) (hgC : ConcaveOn ℝ (Ici 0) production)
    (hgSq : ConcaveOn ℝ (Ioo 0 B) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) B, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) B, HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''cont : ContinuousOn productionSecondDeriv (Ioo 0 B))
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost E rho)) (production E))
      (fun a => a / cost (effortIntervalInverse production E a)))
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    let skillM := fun t => lowerSkill + skillWidth * t
    ∃ beta ∈ Ioo (0 : ℝ) 1,
      ∀ effortM effortU score : ℝ → ℝ × α → ℝ,
        (∀ d ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score d)) →
        (∀ d ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ x ∂unitRankMeasure.prod μ,
          SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
            (fun x => skillM x.1) (score d) tie B rho d x (effortM d x) (effortU d x)) →
        ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
          sourceActualMultitaskSchoolUtility μ production skillM skillU
            (effortM d) (effortU d) (score d) tie rho beta d ≤
          sourceActualMultitaskSchoolUtility μ production skillM skillU
            (effortM c) (effortU c) (score c) tie rho beta c := by
  let skillM := fun t => lowerSkill + skillWidth * t
  have hfcont : ContinuousOn skillM (Icc (0 : ℝ) 1) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hf : StrictMonoOn skillM (Icc (0 : ℝ) 1) :=
    fun _ _ _ _ hab => add_lt_add_right (mul_lt_mul_of_pos_left hab hwidth) _
  have hf0 : 0 ≤ skillM 0 := by simpa only [skillM, mul_zero, add_zero] using hlower
  have hpM := sourceCost_strictMonoOn_of_strictConvex hpC hpnonneg hp0
  have hcap := sourceUnitCostCap_le_budget hpM hE.le hB hpE hpB
  obtain ⟨beta, hbeta, hopt⟩ := sourceSkillConditionalSchoolUtility_exists_optimal_weight_of_affineSkill
    μ hskillU hmean hrho hrho1 hlower hwidth hE hcap (hp.mono Icc_subset_Ici_self)
    (hpM.mono Icc_subset_Ici_self) hp0 hpE hp' hp'' (hg.mono Icc_subset_Ici_self)
    (hgM.mono Icc_subset_Ici_self) hg0
    (hgC.subset (Ioo_subset_Icc_self.trans Icc_subset_Ici_self) (convex_Ioo _ _))
    hgSq hg' hg'' hg''cont hcostRatio hc
  refine ⟨beta, hbeta, ?_⟩
  intro effortM effortU score hscore hbest d hd
  have hutility (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceHardBudgetEquilibrium_utility μ hrho ha hB hpB hE.le hpE hp hpC hpnonneg hp0
      hg hgM hgC hg0.ge hfcont hf hf0 (hscore a ha) htie (hbest a ha) skillU beta
  rw [hutility d hd, hutility c ⟨hc.1, hc.2.le⟩]
  exact hopt d hd

end LBG22StrategicRanking
