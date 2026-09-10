import LBG22StrategicRanking.GroupQuantitativePrimitiveRepairs

/-!
# Welfare-gap growth at feasible policy endpoints

A source-primitive coefficient controls the gap increase uniformly across
policies. Passing to a sequence of less selective policies gives the sign
of every existing left derivative, including at deterministic admission.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The welfare gap grows at least linearly at a rate proportional to its
initial level. The proportionality coefficient depends only on source
primitives, not on either policy or its selected actual equilibrium. -/
theorem sourceActualGroupWelfareGap_growth_of_sourcePrimitives
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
      sourceGroupGapGrowthRate cost production psiA psiB rho *
          sourceActualGroupWelfareGap cost effortC scoreC tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward rho c) t * (d - c) ≤
        sourceActualGroupWelfareGap cost effortD scoreD tie (fun i : Fin 2 => sourceTwoLevelCutoff d i)
            (sourceTwoLevelReward rho d) t -
          sourceActualGroupWelfareGap cost effortC scoreC tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (sourceTwoLevelReward rho c) t := by
  obtain ⟨K, hK, _, _, hbound⟩ := sourceActualGroupWelfareGap_quantitative_of_sourcePrimitives hrho hc
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  have hrate := sourceGroupGapGrowthRate_pos hpcont hpconv hpnonneg hpzero hgm hg0 hB hBA hrho
  have hadmit := sourceActualGroupAdmission_of_sourcePrimitives hrho hc (by norm_num)
    hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA hscoreC htie hinj hbestC
  have htheta : sourceGroupThreshold skill psiA psiB false c ≤
      sourceGroupThreshold skill psiA psiB false d := (monotone_cdf _) hcd
  filter_upwards [hbound d hd hcd effortD scoreD hscoreD hbestD, hadmit true, hadmit false,
    sourceTwoGroupMeasure_ae_branch hbestC true] with t ht hA hBrew hbestA
  intro hhighD
  have hhighC := htheta.trans_lt hhighD
  have hhighA := (sourceGroupThreshold_order (c := c) hfcont hf hf0 hB hBA).trans_lt hhighC
  have hgap : sourceActualGroupWelfareGap cost effortC scoreC tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ≤ cost (effortC (false, t)) := by
    dsimp only [sourceActualGroupWelfareGap, sourceActualGroupWelfare]
    rw [hA, hBrew, if_pos hhighA, if_pos hhighC]
    linarith [hpnonneg _ hbestA.1]
  have h := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hrate.le) (sub_nonneg.mpr hcd))
  exact h.trans (by simpa only [hK] using ht hhighD)

/-- At every feasible positive cutoff, including the maximum cutoff,
every existing left derivative of the actual welfare gap is nonnegative.
It is bounded below by the primitive growth rate times the current gap,
and is strictly positive at positive disadvantaged effort. Only equilibria
of feasible less selective policies are used. -/
theorem sourceActualGroupWelfareGap_leftDeriv_of_sourcePrimitives
    {cost production skill : ℝ → ℝ} {effort score : ℝ → Bool × ℝ → ℝ} {tie : Bool × ℝ → ℝ}
    {psiA psiB rho a c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (ha : 0 < a) (hac : a < c)
    (hpcont : ContinuousOn cost (Ici 0)) (hpconv : StrictConvexOn ℝ (Ici 0) cost)
    (hpnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hpzero : cost 0 = 0)
    (hgcont : ContinuousOn production (Ici 0)) (hgm : StrictMonoOn production (Ici 0))
    (hgconc : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1))
    (hf0 : 0 ≤ skill 0) (hB : 0 < psiB) (hBA : psiB < psiA)
    (hscore : ∀ d ∈ Icc a c, Measurable (score d))
    (htie : Measurable tie) (hinj : InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ d ∈ Icc a c, ∀ᵐ x ∂sourceTwoGroupMeasure,
      SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
        (sourceEnvironmentSkill skill psiA psiB) (score d) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) x (effort d x)) :
    ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t → ∀ v : ℝ,
      HasDerivWithinAt (fun d => sourceActualGroupWelfareGap cost (effort d) (score d) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t) v (Iic c) c →
        sourceGroupGapGrowthRate cost production psiA psiB rho *
          sourceActualGroupWelfareGap cost (effort c) (score c) tie
            (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ≤ v ∧
        0 ≤ v ∧ (0 < effort c (false, t) → 0 < v) := by
  have hcI : c ∈ Icc a c := ⟨hac.le, le_rfl⟩
  have hc1 : c < 1 := by linarith [hc.2]
  let rate := sourceGroupGapGrowthRate cost production psiA psiB rho
  have hrate : 0 < rate := sourceGroupGapGrowthRate_pos hpcont hpconv hpnonneg hpzero hgm hg0 hB hBA hrho
  let d := fun n : ℕ => c - (c - a) / ((n : ℝ) + 2)
  have hd (n : ℕ) : d n ∈ Ico a c := by
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hpos := div_pos (sub_pos.mpr hac) hn
    have hle : (c - a) / ((n : ℝ) + 2) ≤ c - a := (div_le_iff₀ hn).mpr (by
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hdlim : Tendsto d atTop (𝓝 c) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (c - a)).comp (tendsto_add_atTop_nat 2)).const_sub c
    simpa only [d, Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, sub_zero] using h
  have hdwithin : Tendsto d atTop (𝓝[Iic c] c) := tendsto_nhdsWithin_iff.mpr
    ⟨hdlim, Eventually.of_forall (fun n => (hd n).2.le)⟩
  have hdpunct : Tendsto d atTop (𝓝[Iic c \ {c}] c) := tendsto_nhdsWithin_iff.mpr
    ⟨hdlim, Eventually.of_forall (fun n => ⟨(hd n).2.le, by simpa only [mem_singleton_iff] using (hd n).2.ne⟩)⟩
  have hcomparisons : ∀ᵐ t ∂unitRankMeasure, ∀ n : ℕ,
      sourceGroupThreshold skill psiA psiB false c < t →
        rate * sourceActualGroupWelfareGap cost (effort (d n)) (score (d n)) tie
            (fun i : Fin 2 => sourceTwoLevelCutoff (d n) i) (sourceTwoLevelReward rho (d n)) t * (c - d n) ≤
          sourceActualGroupWelfareGap cost (effort c) (score c) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t -
            sourceActualGroupWelfareGap cost (effort (d n)) (score (d n)) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff (d n) i) (sourceTwoLevelReward rho (d n)) t := by
    rw [ae_all_iff]
    intro n
    exact sourceActualGroupWelfareGap_growth_of_sourcePrimitives hrho
      ⟨ha.trans_le (hd n).1, (hd n).2.le.trans hc.2⟩ hc (hd n).2.le
      hpcont hpconv hpnonneg hpzero hgcont hgm hgconc hg0 hfcont hf hf0 hB hBA
      (hscore _ ⟨(hd n).1, (hd n).2.le⟩) (hscore c hcI) htie hinj
      (hbest _ ⟨(hd n).1, (hd n).2.le⟩) (hbest c hcI)
  have hwelfare := sourceActualGroupWelfareGap_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (baseline := 0)
    (by norm_num) hpcont hpconv hpnonneg hpzero hgcont hgm hg0 hf hf0 hB hBA
    (sourceTwoLevelReward_strictMono hrho hc1).monotoneOn (hbest c hcI)
  filter_upwards [hcomparisons, hwelfare] with t ht hwt
  intro hhigh v hv
  let W := fun z => sourceActualGroupWelfareGap cost (effort z) (score z) tie
    (fun i : Fin 2 => sourceTwoLevelCutoff z i) (sourceTwoLevelReward rho z) t
  have hWlim : Tendsto (fun n => W (d n)) atTop (𝓝 (W c)) :=
    hv.continuousWithinAt.tendsto.comp hdwithin
  have hslopelim : Tendsto (fun n => slope W c (d n)) atTop (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hv).comp hdpunct
  have hslope : ∀ᶠ n in atTop, rate * W (d n) ≤ slope W c (d n) := by
    apply Eventually.of_forall
    intro n
    rw [slope_comm, slope_def_field]
    exact (le_div_iff₀ (sub_pos.mpr (hd n).2)).mpr (ht n hhigh)
  have hbound : rate * W c ≤ v := le_of_tendsto_of_tendsto (hWlim.const_mul rate) hslopelim hslope
  exact ⟨hbound, (mul_nonneg hrate.le hwt.1).trans hbound,
    fun he => (mul_pos hrate (hwt.2.1 he)).trans_le hbound⟩

end LBG22StrategicRanking
