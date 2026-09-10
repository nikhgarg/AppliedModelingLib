import LBG22StrategicRanking.GroupWelfarePrimitiveRepairs

/-!
# Two-group boundary indifference

The disadvantaged conditional population approaches its interior admission
boundary from both sides. Actual best responses therefore identify the
boundary effort cost, even when the mixture skill distribution has gaps.
Baseline production is retained in the score and effort formulas.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped Topology

/-- In every two-level equilibrium whose cutoff lies below the top of the
disadvantaged rank support, that group's admitted score threshold satisfies
the source boundary indifference equation. Both its common effort cap and
the threshold are derived from actual population best responses. The cost
minimum is zero, as in the source's comparative-statics section. -/
theorem sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score tie : Bool × ℝ → ℝ}
    {psiA psiB rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hcB : c < sourceDisadvantagedRank skill psiA psiB 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effort x)) :
    let theta := sourceDisadvantagedThreshold skill psiA psiB c
    ∃ E T : ℝ, 0 < E ∧ cost E = 1 ∧
      production 0 * (psiB * skill theta) ≤ T ∧ T ≤ production E * (psiB * skill theta) ∧
      sourceCostAtScore cost production E (T / (psiB * skill theta)) = rho / (1 - c) ∧
      ∀ group : Bool, ∀ᵐ t ∂unitRankMeasure,
        sourceGroupThreshold skill psiA psiB group c < t →
          score (group, t) = max T (production 0 * ((if group then psiA else psiB) * skill t)) ∧
          sourceEffortAtScore production E (T / ((if group then psiA else psiB) * skill t)) = effort (group, t) := by
  let theta := sourceDisadvantagedThreshold skill psiA psiB c
  let f := fun t => psiB * skill t
  let e := fun t => effort (false, t)
  let q := rho / (1 - c)
  let R := fun r => sourceTwoLevelReward rho c
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val
  have hc1 : c < 1 := by linarith [hc.2]
  have hq : 0 < q := div_pos hrho (sub_pos.mpr hc1)
  have hq1 : q ≤ 1 := (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])
  have hR : Monotone R := monotone_finiteLowerRankReward _ (sourceTwoLevelReward_strictMono hrho hc1).monotoneOn
  have hReq (r : ℝ) : R r = if c < r then q else 0 := by
    dsimp only [R]
    rw [finiteLowerRankBand_twoLevel]
    split <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero, q]
  have hR0 (r : ℝ) : 0 ≤ R r := by rw [hReq]; split <;> positivity
  have hR1 (r : ℝ) : R r ≤ 1 := by rw [hReq]; split <;> linarith
  have htheta : theta ∈ Icc (0 : ℝ) 1 := sourceDisadvantagedThreshold_mem
  have htheta0 : 0 < theta := hc.1.trans
    (sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hc.1, hc1⟩)
  have htheta1 : theta < 1 := by
    apply lt_of_le_of_ne htheta.2
    intro ht
    have hi := sourceDisadvantagedThreshold_inverse hfcont hf hf0 hB hBA ⟨hc.1.le, hcB.le⟩
    change sourceDisadvantagedRank skill psiA psiB theta = c at hi
    rw [ht] at hi
    exact hcB.ne hi.symm
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := continuousOn_const.mul hfcont
  have hfm : StrictMonoOn f (Icc (0 : ℝ) 1) := fun x hx y hy hxy =>
    mul_lt_mul_of_pos_left (hf hx hy hxy) hB
  have hfz : 0 ≤ f 0 := mul_nonneg hB.le hf0
  have hfp : 0 < f theta := hfz.trans_lt (hfm (by norm_num) htheta htheta0)
  have hfat : ContinuousAt f theta := hfc.continuousAt (Icc_mem_nhds htheta0 htheta1)
  obtain ⟨E, hE, hpE, hpm⟩ := exists_unitCost_effort_of_sourcePrimitives hpcont hpconv hpnonneg hpzero
  have hadmit := sourceActualGroupAdmission_of_sourcePrimitives hrho hc (by norm_num) hpcont hpconv hpnonneg hpzero
    hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscore htie hinj hbest
  let good := {t : ℝ | t ∈ Ioc (0 : ℝ) 1 ∧ e t ∈ Icc (0 : ℝ) E ∧
    score (false, t) = production (e t) * f t ∧
    R (tieBrokenRank sourceTwoGroupMeasure score tie (false, t)) = (if theta < t then q else 0) ∧
    ∀ d : ℝ, 0 ≤ d →
      R (counterfactualTieBrokenRank sourceTwoGroupMeasure score tie (false, t) (production d * f t)) - cost d ≤
        R (tieBrokenRank sourceTwoGroupMeasure score tie (false, t)) - cost (e t)}
  have hgood : ∀ᵐ t ∂unitRankMeasure, t ∈ good := by
    filter_upwards [sourceTwoGroupMeasure_ae_branch hbest false, hadmit false,
      ae_restrict_mem measurableSet_Ioc] with t ht hrew hmem
    have hs : sourceEnvironmentSkill skill psiA psiB (false, t) = f t := by
      rw [sourceEnvironmentSkill_eq_on_support (x := (false, t)) ⟨hmem.1.le, hmem.2⟩]
      rfl
    have hcost := sourceBestResponse_cost_le_reward_range sourceTwoGroupMeasure score tie (false, t)
      (baseline := 0) (by norm_num) hpzero hR0 (hR1 _) ht.2.2
    have heE : e t ≤ E := by
      by_contra hn
      have hlt := hpm hE.le ht.1 (lt_of_not_ge hn)
      rw [hpE] at hlt
      linarith
    refine ⟨hmem, ⟨ht.1, heE⟩, ?_, ?_, ?_⟩
    · simpa only [hs] using ht.2.1
    · simpa only [sourceGroupThreshold, Bool.false_eq_true, ↓reduceIte] using hrew
    · simpa only [hs] using ht.2.2
  let T := sourceEquilibriumBandThreshold (fun t => score (false, t)) good theta 1
  have hprops := sourceEquilibriumBandThreshold_properties sourceTwoGroupMeasure (fun t => (false, t))
    score tie f e hgood htheta.1 le_rfl htheta1 hE.le hpconv hpnonneg hpzero hgcont hgm hg0 hR hfc hfm hfz
    (fun x hx => hx.2.2.1) (fun x hx => hx.2.2.2.1)
    (fun x hx => by rw [hx.2.2.2.2.1, if_pos hx.1.1]) (fun x hx => hx.2.2.2.2.2)
  change 0 ≤ T ∧ production 0 * f theta ≤ T ∧ T ≤ production E * f theta ∧
    ∀ x ∈ Ioo theta 1 ∩ good,
      score (false, x) = max T (production 0 * f x) ∧
      sourceEffortAtScore production E (T / f x) = e x at hprops
  have hlow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) theta ∩ good) : e x = 0 := by
    have hrew : R (tieBrokenRank sourceTwoGroupMeasure score tie (false, x)) = 0 := by
      rw [hx.2.2.2.2.1, if_neg (not_lt.mpr hx.1.2.le)]
    have hcost := sourceBestResponse_cost_le_reward_range sourceTwoGroupMeasure score tie (false, x)
      (baseline := 0) (by norm_num) hpzero hR0 hrew.le hx.2.2.2.2.2
    have hc0 : cost (e x) = cost 0 := by rw [hpzero]; linarith [hpnonneg _ hx.2.2.1.1]
    exact hpm.injOn hx.2.2.1.1 (by simp) hc0
  have hgE : production 0 ≤ production E := hgm.monotoneOn (by simp) hE.le hE.le
  have hgap := sourceBestResponses_adjacent_boundary_cost_gap sourceTwoGroupMeasure (fun t => (false, t))
    score tie f e (lowScore := fun t => production 0 * f t)
    (highScore := fun t => max T (production 0 * f t))
    (a := 0) (b := 1) (lowReward := 0) (highReward := q)
    hgood (by norm_num) le_rfl htheta0 htheta1 hE.le hpcont hgcont hgm hR hfat hfp
    (continuousAt_const.mul hfat) (continuousAt_const.max (continuousAt_const.mul hfat))
    (by simpa only [mul_div_cancel_right₀ _ hfp.ne'] using hgE)
    (by dsimp only; rw [max_eq_left hprops.2.1]; exact (div_le_iff₀ hfp).mpr hprops.2.2.1)
    (fun x hx => hx.2.2.1) (fun x hx => hx.2.2.2.1)
    (fun x hx => by rw [hx.2.2.2.1, hlow x hx])
    (fun x hx => (hprops.2.2.2 x hx).1)
    (fun x hx => by rw [hx.2.2.2.2.1, if_neg (not_lt.mpr hx.1.2.le)])
    (fun x hx => by rw [hx.2.2.2.2.1, if_pos hx.1.1])
    (fun x hx => hx.2.2.2.2.2)
  have hzero : sourceCostAtScore cost production E (production 0 * f theta / f theta) = 0 := by
    rw [mul_div_cancel_right₀ _ hfp.ne']
    change cost (sourceEffortAtScore production E (production 0)) = 0
    rw [sourceEffortAtScore_at_production (hgm.mono Icc_subset_Ici_self) ⟨le_rfl, hE.le⟩, hpzero]
  rw [sourceCostAtScore_max_baseline hfp, hzero, sub_zero, sub_zero] at hgap
  have hTstrict : production 0 * f theta < T := by
    by_contra hn
    have hbase : T = production 0 * f theta := le_antisymm (le_of_not_gt hn) hprops.2.1
    rw [hbase, hzero] at hgap
    exact hq.ne' hgap.symm
  have hclosure : theta ∈ closure (Ioo theta 1 ∩ good) := by
    rw [sourceFullMeasure_closure_band hgood htheta.1 le_rfl htheta1]
    exact ⟨le_rfl, htheta1.le⟩
  have hnear : ∀ᶠ t in nhds theta, production 0 * f t < T :=
    (continuousAt_const.mul hfat).eventually (Iio_mem_nhds hTstrict)
  obtain ⟨w, hw, hwfloor⟩ := ((mem_closure_iff_frequently.mp hclosure).and_eventually hnear).exists
  have hwscore : score (false, w) = T := by rw [(hprops.2.2.2 w hw).1, max_eq_left hwfloor.le]
  have hwpos : 0 < e w := by
    apply lt_of_le_of_ne hw.2.2.1.1
    intro hz
    have h := hw.2.2.2.1
    rw [← hz, hwscore] at h
    exact hwfloor.ne h.symm
  have hwreward : R (tieBrokenRank sourceTwoGroupMeasure score tie (false, w)) = q := by
    rw [hw.2.2.2.2.1, if_pos hw.1.1]
  refine ⟨E, T, hE, hpE, hprops.2.1, hprops.2.2.1, hgap, ?_⟩
  intro group
  filter_upwards [sourceTwoGroupMeasure_ae_branch hbest group, hadmit group,
    ae_restrict_mem measurableSet_Ioc] with t ht hrew hmem
  intro hhigh
  let s := (if group then psiA else psiB) * skill t
  have hs : sourceEnvironmentSkill skill psiA psiB (group, t) = s :=
    sourceEnvironmentSkill_eq_on_support (x := (group, t)) ⟨hmem.1.le, hmem.2⟩
  have hpsi : 0 < (if group then psiA else psiB) := by
    cases group
    · exact hB
    · exact hB.trans hBA
  have hsp : 0 < s := mul_pos hpsi (hf0.trans_lt (hf (by norm_num) ⟨hmem.1.le, hmem.2⟩ hmem.1))
  have hactual : score (group, t) = production (effort (group, t)) * s := by simpa only [hs] using ht.2.1
  have hreward : R (tieBrokenRank sourceTwoGroupMeasure score tie (group, t)) = q := by
    dsimp only [R]
    rw [hrew, if_pos hhigh]
  have hTle : T ≤ score (group, t) := by
    rw [← hwscore]
    exact sourceBestResponse_score_le_of_same_reward sourceTwoGroupMeasure score tie (false, w) (group, t)
      (baseline := 0) (by norm_num) hpm hgcont hR hwpos hw.2.2.2.1
      (hreward.trans hwreward.symm) hw.2.2.2.2.2
  have hshape : score (group, t) = max T (production 0 * s) := by
    rcases eq_or_lt_of_le ht.1 with he0 | he0
    · have heq : score (group, t) = production 0 * s := by rw [hactual, ← he0]
      rw [← heq, max_eq_right hTle]
    · have hle : score (group, t) ≤ T := by
        rw [← hwscore]
        exact sourceBestResponse_score_le_of_same_reward sourceTwoGroupMeasure score tie (group, t) (false, w)
          (baseline := 0) (by norm_num) hpm hgcont hR he0 ht.2.1
          (hwreward.trans hreward.symm) ht.2.2
      have hfloor : production 0 * s ≤ score (group, t) := by
        rw [hactual]
        exact mul_le_mul_of_nonneg_right (hgm.monotoneOn (by simp) ht.1 ht.1) hsp.le
      rw [le_antisymm hTle hle, max_eq_left hfloor]
  have hcost := sourceBestResponse_cost_le_reward_range sourceTwoGroupMeasure score tie (group, t)
    (baseline := 0) (by norm_num) hpzero hR0 (hR1 _) ht.2.2
  have heE : effort (group, t) ≤ E := by
    by_contra hn
    have hlt := hpm hE.le ht.1 (lt_of_not_ge hn)
    rw [hpE] at hlt
    linarith
  have hprod : production (effort (group, t)) = max (T / s) (production 0) := by
    have h := congrArg (fun z => z / s) hshape
    dsimp only at h
    rw [hactual, mul_div_cancel_right₀ _ hsp.ne', ← max_div_div_right hsp.le,
      mul_div_cancel_right₀ _ hsp.ne'] at h
    exact h
  have hcap : T / s ≤ production E := (div_le_iff₀ hsp).mpr (hTle.trans (by
    rw [hactual]
    exact mul_le_mul_of_nonneg_right (hgm.monotoneOn ht.1 hE.le heE) hsp.le))
  have hi := sourceEffortAtScore_spec hE.le (hgcont.mono Icc_subset_Ici_self)
    (hgm.mono Icc_subset_Ici_self).monotoneOn hcap
  exact ⟨hshape, hgm.injOn hi.1.1 ht.1 (hi.2.trans hprod.symm)⟩

/-- Higher boundary skill and a weakly higher boundary reward raise the
score threshold. The score-cost equations determine the boundary efforts;
neither threshold monotonicity nor inverse differentiability is assumed. -/
theorem sourceBoundaryThreshold_mono
    {cost production : ℝ → ℝ} {E T U s t q r : ℝ}
    (hE : 0 ≤ E) (hp : StrictMonoOn cost (Icc 0 E))
    (hg : ContinuousOn production (Icc 0 E)) (hgm : StrictMonoOn production (Icc 0 E))
    (hg0 : 0 ≤ production 0) (hs : 0 < s) (hst : s ≤ t) (hqr : q ≤ r)
    (hbaseT : production 0 * s ≤ T) (hbaseU : production 0 * t ≤ U)
    (hcapT : T ≤ production E * s) (hcapU : U ≤ production E * t)
    (hcostT : sourceCostAtScore cost production E (T / s) = q)
    (hcostU : sourceCostAtScore cost production E (U / t) = r) : T ≤ U := by
  have ht : 0 < t := hs.trans_le hst
  have hi := sourceEffortAtScore_spec hE hg hgm.monotoneOn ((div_le_iff₀ hs).mpr hcapT)
  have hj := sourceEffortAtScore_spec hE hg hgm.monotoneOn ((div_le_iff₀ ht).mpr hcapU)
  have he : sourceEffortAtScore production E (T / s) ≤ sourceEffortAtScore production E (U / t) := by
    by_contra hn
    have h := hp hj.1 hi.1 (lt_of_not_ge hn)
    change sourceCostAtScore cost production E (U / t) < sourceCostAtScore cost production E (T / s) at h
    rw [hcostT, hcostU] at h
    exact (not_lt_of_ge hqr) h
  have hratio := hgm.monotoneOn hi.1 hj.1 he
  rw [hi.2, hj.2, max_eq_left ((le_div_iff₀ hs).mpr hbaseT),
    max_eq_left ((le_div_iff₀ ht).mpr hbaseU)] at hratio
  have hU0 : 0 ≤ U / t := div_nonneg ((mul_nonneg hg0 ht.le).trans hbaseU) ht.le
  calc
    T = (T / s) * s := (div_mul_cancel₀ _ hs.ne').symm
    _ ≤ (U / t) * s := mul_le_mul_of_nonneg_right hratio hs.le
    _ ≤ (U / t) * t := mul_le_mul_of_nonneg_left hst hU0
    _ = U := div_mul_cancel₀ _ ht.ne'

/-- Raising a two-level admission cutoff weakly increases the actual welfare
gap at latent ranks admitted from both groups under both policies. The
comparison is strict whenever the disadvantaged applicant's effort cost
increases. It holds for arbitrary equilibria of the same source population,
capacity, primitives, and tie order, retaining positive baseline production. -/
theorem sourceActualGroupWelfareGap_mono_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effortC scoreC effortD scoreD tie : Bool × ℝ → ℝ}
    {psiA psiB rho c d : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hd : d ∈ Ioc (0 : ℝ) (1 - rho))
    (hcd : c ≤ d)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscoreC : Measurable scoreC) (hscoreD : Measurable scoreD)
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbestC : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) scoreC tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x (effortC x))
    (hbestD : ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) scoreD tie
        (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) x (effortD x)) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false d < t →
      sourceActualGroupWelfareGap cost effortC scoreC tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (sourceTwoLevelReward rho c) t ≤
        sourceActualGroupWelfareGap cost effortD scoreD tie (fun i : Fin 2 => sourceTwoLevelCutoff d i)
          (sourceTwoLevelReward rho d) t ∧
      (cost (effortC (false, t)) < cost (effortD (false, t)) →
        sourceActualGroupWelfareGap cost effortC scoreC tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward rho c) t <
          sourceActualGroupWelfareGap cost effortD scoreD tie (fun i : Fin 2 => sourceTwoLevelCutoff d i)
            (sourceTwoLevelReward rho d) t) := by
  by_cases hdB : d < sourceDisadvantagedRank skill psiA psiB 1
  swap
  · have htheta := sourceDisadvantagedThreshold_eq_one hfcont hf (hB.trans hBA) hB (le_of_not_gt hdB)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro hhigh
    change sourceDisadvantagedThreshold skill psiA psiB d < t at hhigh
    rw [htheta] at hhigh
    exact False.elim ((not_lt_of_ge ht.2) hhigh)
  obtain ⟨E, T, hE, hpE, hbaseT, hcapT, hcostT, hprofileC⟩ :=
    sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives hrho hc (hcd.trans_lt hdB)
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  obtain ⟨F, U, hF, hpF, hbaseU, hcapU, hcostU, hprofileD⟩ :=
    sourceDisadvantagedEquilibrium_boundary_of_sourcePrimitives hrho hd hdB
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreD htie hinj hbestD
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpconv hpnonneg hpzero
  have hFE : F = E := hpm.injOn hF.le hE.le (hpF.trans hpE.symm)
  subst F
  let tc := sourceDisadvantagedThreshold skill psiA psiB c
  let td := sourceDisadvantagedThreshold skill psiA psiB d
  have htc : tc ∈ Icc (0 : ℝ) 1 := sourceDisadvantagedThreshold_mem
  have htd : td ∈ Icc (0 : ℝ) 1 := sourceDisadvantagedThreshold_mem
  have hc1 : c < 1 := by linarith [hc.2]
  have hd1 : d < 1 := by linarith [hd.2]
  have htc0 : 0 < tc := hc.1.trans
    (sourceDisadvantagedThreshold_gt_cutoff hfcont hf hf0 hB hBA ⟨hc.1, hc1⟩)
  have htheta : tc ≤ td := (monotone_cdf _) hcd
  have hskillc : 0 < psiB * skill tc := mul_pos hB (hf0.trans_lt (hf (by norm_num) htc htc0))
  have hskillcd : psiB * skill tc ≤ psiB * skill td :=
    mul_le_mul_of_nonneg_left (hf.monotoneOn htc htd htheta) hB.le
  have hreward : rho / (1 - c) ≤ rho / (1 - d) :=
    (div_le_div_iff₀ (sub_pos.mpr hc1) (sub_pos.mpr hd1)).mpr (by nlinarith)
  have hTU := sourceBoundaryThreshold_mono hE.le (hpm.mono Icc_subset_Ici_self)
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self) hg0 hskillc hskillcd hreward
    hbaseT hbaseU hcapT hcapU hcostT hcostU
  have hT0 : 0 ≤ T := (mul_nonneg hg0 hskillc.le).trans hbaseT
  have hU0 : 0 ≤ U := hT0.trans hTU
  have hadmitC := sourceActualGroupAdmission_of_sourcePrimitives hrho hc (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  have hadmitD := sourceActualGroupAdmission_of_sourcePrimitives hrho hd (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreD htie hinj hbestD
  filter_upwards [hprofileC true, hprofileC false, hprofileD true, hprofileD false,
    hadmitC true, hadmitC false, hadmitD true, hadmitD false,
    ae_restrict_mem measurableSet_Ioc] with t hpCA hpCB hpDA hpDB haCA haCB haDA haDB ht
  intro hhighD
  have hhighC : sourceGroupThreshold skill psiA psiB false c < t := htheta.trans_lt hhighD
  have hhighCA := (sourceGroupThreshold_order (c := c) hfcont hf hf0 hB hBA).trans_lt hhighC
  have hhighDA := (sourceGroupThreshold_order (c := d) hfcont hf hf0 hB hBA).trans_lt hhighD
  have heCA := (hpCA hhighCA).2
  have heCB := (hpCB hhighC).2
  have heDA := (hpDA hhighDA).2
  have heDB := (hpDB hhighD).2
  simp only [Bool.false_eq_true, ↓reduceIte] at heCA heCB heDA heDB
  have hWC : sourceActualGroupWelfareGap cost effortC scoreC tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t =
      sourceCostAtScore cost production E (T / (psiB * skill t)) -
        sourceCostAtScore cost production E (T / (psiA * skill t)) := by
    dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
    rw [haCA, haCB, if_pos hhighCA, if_pos hhighC, ← heCA, ← heCB]
    dsimp only [sourceCostAtScore]
    ring
  have hWD : sourceActualGroupWelfareGap cost effortD scoreD tie
      (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t =
      sourceCostAtScore cost production E (U / (psiB * skill t)) -
        sourceCostAtScore cost production E (U / (psiA * skill t)) := by
    dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
    rw [haDA, haDB, if_pos hhighDA, if_pos hhighD, ← heDA, ← heDB]
    dsimp only [sourceCostAtScore]
    ring
  have hft : 0 < skill t := hf0.trans_lt (hf (by norm_num) ⟨ht.1.le, ht.2⟩ ht.1)
  have hst : 0 < psiB * skill t := mul_pos hB hft
  have hskill : psiB * skill t < psiA * skill t := mul_lt_mul_of_pos_right hBA hft
  have hgE0 : 0 ≤ production E := hg0.trans (hgm.monotoneOn (by simp) hE.le hE.le)
  have hcap : U / (psiB * skill t) ≤ production E := (div_le_iff₀ hst).mpr (hcapU.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hf.monotoneOn htd ⟨ht.1.le, ht.2⟩ hhighD.le) hB.le) hgE0))
  have hweak := sourceCostAtScore_gap_antitone_skill hE.le (hpm.monotoneOn.mono Icc_subset_Ici_self)
    (hpconv.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
    (hgconc.subset Icc_subset_Ici_self (convex_Icc _ _)) hT0 hTU hst hskill.le hcap
  rw [hWC, hWD]
  refine ⟨by linarith, ?_⟩
  intro hcost
  have hcost' : sourceCostAtScore cost production E (T / (psiB * skill t)) <
      sourceCostAtScore cost production E (U / (psiB * skill t)) := by
    simpa only [sourceCostAtScore, heCB, heDB] using hcost
  have hTUstrict : T < U := lt_of_le_of_ne hTU (by intro h; rw [h] at hcost'; exact (lt_irrefl _) hcost')
  have hstrict := sourceCostAtScore_gap_strict_antitone_skill_of_cost_lt hE.le
    (hpm.monotoneOn.mono Icc_subset_Ici_self)
    (hpconv.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    (hgcont.mono Icc_subset_Ici_self) (hgm.mono Icc_subset_Ici_self)
    (hgconc.subset Icc_subset_Ici_self (convex_Icc _ _)) hT0 hTUstrict hst hskill hcap hcost'
  linarith

end LBG22StrategicRanking
