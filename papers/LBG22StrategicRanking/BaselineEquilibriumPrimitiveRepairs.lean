import LBG22StrategicRanking.UniformRankPrimitiveRepairs

/-!
# Finite-band equilibrium with a positive cost-minimizing effort

Translating effort by its cost-minimizing baseline preserves the source
convexity and concavity assumptions. Efforts below that baseline are
dominated: they weakly lower score and cannot reduce cost. The resulting
equilibrium therefore covers the entire nonnegative action space.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- With the population and tie key fixed, increasing a counterfactual score
can only increase the applicant's contour-measure rank. -/
theorem counterfactualTieBrokenRank_monotone
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) :
    Monotone (counterfactualTieBrokenRank μ score tie x) := by
  intro v w hvw
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro y hy
  rcases lt_or_eq_of_le hvw with hlt | rfl
  · left
    rcases hy with hy | ⟨hy, _⟩
    · exact hy.trans hlt
    · exact hy ▸ hlt
  · exact hy

theorem monotone_finiteLowerRankReward
    {n : ℕ} (cutoff : Fin (n + 1) → ℝ) {reward : ℕ → ℝ}
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) :
    Monotone (fun r => reward (finiteLowerRankBand cutoff r).val) := by
  intro a b hab
  exact hr ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff a).isLt⟩
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand cutoff b).isLt⟩
    ((finiteLowerRankBand_monotone cutoff) hab)

/-- The cost-minimizing effort weakly dominates every smaller effort under
any nondecreasing rank reward, against the fixed population score law. -/
theorem sourceEffortBelowBaseline_dominated
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) {cost production reward : ℝ → ℝ}
    {baseline skill d : ℝ} (hbaseline : 0 ≤ baseline) (hskill : 0 ≤ skill)
    (hg : MonotoneOn production (Ici 0)) (hr : Monotone reward)
    (hp : cost baseline = 0) (hpd : 0 ≤ cost d) (hd : 0 ≤ d) (hdb : d ≤ baseline) :
    reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d ≤
      reward (counterfactualTieBrokenRank μ score tie x (production baseline * skill)) - cost baseline := by
  have hscore := mul_le_mul_of_nonneg_right (hg hd hbaseline hdb) hskill
  have hrew := hr ((counterfactualTieBrokenRank_monotone μ score tie x) hscore)
  rw [hp]
  linarith

/-- Under strict convexity and nonnegative cost, every effort other than
the zero-cost minimum has strictly positive cost. -/
theorem sourceCost_pos_away_from_baseline
    {cost : ℝ → ℝ} {baseline d : ℝ} (hbaseline : 0 ≤ baseline) (hd : 0 ≤ d)
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hzero : cost baseline = 0)
    (hne : d ≠ baseline) : 0 < cost d := by
  have hmin : IsMinOn cost (Ici 0) baseline := by
    intro e he
    simpa only [hzero] using hnonneg e he
  by_contra hn
  have hdzero : cost d = 0 := le_antisymm (le_of_not_gt hn) (hnonneg d hd)
  have hdmin : IsMinOn cost (Ici 0) d := by
    intro e he
    simpa only [hdzero] using hnonneg e he
  exact hne (hcost.eq_of_isMinOn hdmin hmin hd hbaseline)

/-- Source cost is strictly increasing above its possibly nonzero minimum. -/
theorem sourceCost_strictMonoOn_above_baseline
    {cost : ℝ → ℝ} {baseline : ℝ} (hbaseline : 0 ≤ baseline)
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hzero : cost baseline = 0) :
    StrictMonoOn cost (Ici baseline) := by
  have hshift : MapsTo (fun e => baseline + e) (Ici (0 : ℝ)) (Ici 0) :=
    fun _ he => add_nonneg hbaseline he
  have hpc : StrictConvexOn ℝ (Ici 0) (fun e => cost (baseline + e)) :=
    (hcost.translate_right baseline).subset hshift (convex_Ici _)
  have hp := sourceCost_strictMonoOn_of_strictConvex hpc
    (fun e he => hnonneg _ (hshift he)) (by simpa only [add_zero] using hzero)
  intro a ha b hb hab
  have ha' : a - baseline ∈ Ici (0 : ℝ) := by simpa only [mem_Ici, sub_nonneg] using ha
  have hb' : b - baseline ∈ Ici (0 : ℝ) := by simpa only [mem_Ici, sub_nonneg] using hb
  have h := hp ha' hb'
    (sub_lt_sub_right hab baseline)
  have hA : baseline + (a - baseline) = a := by ring
  have hB : baseline + (b - baseline) = b := by ring
  simpa only [hA, hB] using h

/-- Below-baseline effort is strictly dominated, even when increasing its
score leaves the reward unchanged. Hence it cannot occur at a best response. -/
theorem sourceEffortBelowBaseline_strictly_dominated
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (score tie : α → ℝ) (x : α) {cost production reward : ℝ → ℝ}
    {baseline skill d : ℝ} (hbaseline : 0 ≤ baseline) (hskill : 0 ≤ skill)
    (hg : MonotoneOn production (Ici 0)) (hr : Monotone reward)
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp : cost baseline = 0)
    (hd : 0 ≤ d) (hdb : d < baseline) :
    reward (counterfactualTieBrokenRank μ score tie x (production d * skill)) - cost d <
      reward (counterfactualTieBrokenRank μ score tie x (production baseline * skill)) - cost baseline := by
  have hscore := mul_le_mul_of_nonneg_right (hg hd hbaseline hdb.le) hskill
  have hrew := hr ((counterfactualTieBrokenRank_monotone μ score tie x) hscore)
  have hpositive := sourceCost_pos_away_from_baseline hbaseline hd hcost hnonneg hp hdb.ne
  rw [hp]
  linarith

/-- Effort in original source units, translating the recursively constructed
profile by the actual cost-minimizing effort. -/
noncomputable def sourceFiniteBaselineEffort (cost production skill : ℝ → ℝ)
    (baseline effortMax : ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ) (t : ℝ) : ℝ :=
  baseline + sourceFiniteRankEffort (fun e => cost (baseline + e))
    (fun e => production (baseline + e)) skill effortMax n cutoff reward t

noncomputable def sourceFiniteBaselineScore (cost production skill : ℝ → ℝ)
    (baseline effortMax : ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ) : ℝ → ℝ :=
  sourceFiniteRankScore (fun e => cost (baseline + e))
    (fun e => production (baseline + e)) skill effortMax n cutoff reward

/-- Existence in the source's general nonnegative effort model. The baseline
may be positive; all nonnegative deviations, including efforts below the
baseline, are compared with the constructed profile. -/
theorem exists_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {baseline : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hbaseline : 0 ≤ baseline) (hcost_cont : ContinuousOn cost (Ici 0))
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hcost_nonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hcost_zero : cost baseline = 0)
    (hg : ContinuousOn production (Ici 0)) (hg_mono : StrictMonoOn production (Ici 0))
    (hg_zero : 0 ≤ production 0) (hg_conc : ConcaveOn ℝ (Ici 0) production)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc_zero : cutoff 0 = 0)
    (hc_top : cutoff (n + 1) = 1) (hf_cont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf_zero : 0 ≤ skill 0)
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    (htie : Measurable tie) (htie_inj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ effortMax : ℝ, 0 < effortMax ∧ cost (baseline + effortMax) = 1 ∧
      let effort := sourceFiniteBaselineEffort cost production skill baseline effortMax n cutoff reward
      let score := sourceFiniteBaselineScore cost production skill baseline effortMax n cutoff reward
      let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      let rank := fun t d => counterfactualTieBrokenRank unitRankMeasure score tie t
        (production d * skill t)
      AEMeasurable effort unitRankMeasure ∧
      Measure.map (tieBrokenRank unitRankMeasure score tie) unitRankMeasure =
        volume.restrict (Icc (0 : ℝ) 1) ∧
      ∀ᵐ t ∂unitRankMeasure,
        effort t ∈ Icc baseline (baseline + effortMax) ∧ score t = production (effort t) * skill t ∧
        band (rank t (effort t)) = band t ∧
        ∀ d : ℝ, 0 ≤ d → reward (band (rank t d)).val - cost d ≤
          reward (band (rank t (effort t))).val - cost (effort t) := by
  let shiftedCost := fun e => cost (baseline + e)
  let shiftedProduction := fun e => production (baseline + e)
  have hshift : MapsTo (fun e => baseline + e) (Ici (0 : ℝ)) (Ici 0) :=
    fun _ he => add_nonneg hbaseline he
  have hpc : ContinuousOn shiftedCost (Ici 0) := hcost_cont.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hpconv : StrictConvexOn ℝ (Ici 0) shiftedCost :=
    (hcost.translate_right baseline).subset hshift (convex_Ici _)
  have hpn (e : ℝ) (he : e ∈ Ici (0 : ℝ)) : 0 ≤ shiftedCost e := hcost_nonneg _ (hshift he)
  have hp0 : shiftedCost 0 = 0 := by simpa only [shiftedCost, add_zero] using hcost_zero
  have hgc : ContinuousOn shiftedProduction (Ici 0) := hg.comp
    (continuous_const.add continuous_id).continuousOn hshift
  have hgm : StrictMonoOn shiftedProduction (Ici 0) :=
    fun a ha b hb hab => hg_mono (hshift ha) (hshift hb) (by dsimp only; linarith)
  have hg0 : 0 ≤ shiftedProduction 0 := by
    simpa only [shiftedProduction, add_zero] using
      hg_zero.trans (hg_mono.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) hbaseline hbaseline)
  have hgconc : ConcaveOn ℝ (Ici 0) shiftedProduction :=
    (hg_conc.translate_right baseline).subset hshift (convex_Ici _)
  obtain ⟨effortMax, hmax, hcap, hmeas, huniform, hbest⟩ :=
    exists_sourceFiniteRankEquilibrium_of_sourcePrimitives hpc hpconv hpn hp0 hgc hgm hg0 hgconc
      hc hc_zero hc_top hf_cont hf hf_zero hreward hreward_zero hreward_top htie htie_inj
  let effort := sourceFiniteBaselineEffort cost production skill baseline effortMax n cutoff reward
  let score := sourceFiniteBaselineScore cost production skill baseline effortMax n cutoff reward
  let band := finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
  let rank := fun t d => counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t)
  refine ⟨effortMax, hmax, hcap, measurable_const.aemeasurable.add hmeas, huniform, ?_⟩
  filter_upwards [hbest, ae_restrict_mem measurableSet_Ioc] with t ht htmem
  have hbounds : effort t ∈ Icc baseline (baseline + effortMax) :=
    ⟨le_add_of_nonneg_right ht.1.1, add_le_add le_rfl ht.1.2⟩
  refine ⟨hbounds, ht.2.1, ht.2.2.1, ?_⟩
  intro d hd
  change reward (band (rank t d)).val - cost d ≤ reward (band (rank t (effort t))).val - cost (effort t)
  have habove (d : ℝ) (hdb : baseline ≤ d) :
      reward (band (rank t d)).val - cost d ≤
        reward (band (rank t (effort t))).val - cost (effort t) := by
    have h := ht.2.2.2 (d - baseline) (sub_nonneg.mpr hdb)
    change reward (band (rank t (baseline + (d - baseline)))).val - cost (baseline + (d - baseline)) ≤
      reward (band (rank t (effort t))).val - cost (effort t) at h
    have heq : baseline + (d - baseline) = d := by ring
    simpa only [heq] using h
  by_cases hdb : baseline ≤ d
  · exact habove d hdb
  · have hskill : 0 ≤ skill t := hf_zero.trans
      (hf.monotoneOn ⟨le_rfl, by norm_num⟩ ⟨htmem.1.le, htmem.2⟩ htmem.1.le)
    have hdom := sourceEffortBelowBaseline_dominated unitRankMeasure score tie t hbaseline hskill
      hg_mono.monotoneOn
      (monotone_finiteLowerRankReward (fun i : Fin (n + 1) => cutoff i) hreward.monotoneOn)
      hcost_zero (hcost_nonneg d hd) hd (le_of_not_ge hdb)
    exact hdom.trans (habove baseline le_rfl)

end LBG22StrategicRanking
