import LBG22StrategicRanking.PaperInterface
import LBG22StrategicRanking.MultitaskUniqueness

namespace LBG22StrategicRanking.SourceProofs

open Set MeasureTheory

/-- Proposition B.2 under the approved affine-skill primitive curvature conditions. -/
theorem weightedPrivateUtility : WeightedPrivateUtilitySpec := by
  intro cost production skillU B E rho lower width tie hP hrho hlower hwidth hE hpE hEB
    hskillU hskillUM hskillU0 hg0 hgSq hcostRatio hp' hp'' hg' hg'' hg''cont htie hinj
    c hc
  rcases hP with ⟨_, hp, hpC, hpnonneg, hp0, hg, hgM, hgC, hg0', _, _, _⟩
  have hskill := unitRankMeasure_skill_integrable_and_mean_pos hskillU hskillUM hskillU0
  have hpM := sourceCost_strictMonoOn_of_strictConvex hpC hpnonneg hp0
  have hB : 0 ≤ B := hE.le.trans hEB
  have hpB : 1 ≤ cost B := by
    rw [← hpE]
    exact hpM.monotoneOn hE.le hB hEB
  have hmem : ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      x.1 ∈ Ioc (0 : ℝ) 1 ∧ x.2 ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [
      (measurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae
        (ae_restrict_mem measurableSet_Ioc),
      (measurePreserving_snd (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae
        (ae_restrict_mem measurableSet_Ioc)] with x hx hy
    exact ⟨hx, hy⟩
  haveI : NoAtoms unitRankMeasure := by
    unfold unitRankMeasure
    infer_instance
  letI : NoAtoms (Measure.map tie (unitRankMeasure.prod unitRankMeasure)) :=
    noAtoms_map_tie_of_injOn_fullMeasure htie hinj hmem
  have hpDeriv : ∀ e ∈ Ioo (0 : ℝ) E, HasDerivAt cost (deriv cost e) e := by
    intro e he
    exact ((hp' e he).differentiableAt (isOpen_Ioo.mem_nhds he)).hasDerivAt
  have hpSecondDeriv : ∀ e ∈ Ioo (0 : ℝ) E,
      HasDerivAt (deriv cost) (deriv (deriv cost) e) e := by
    intro e he
    exact ((hp'' e he).differentiableAt (isOpen_Ioo.mem_nhds he)).hasDerivAt
  have hgDeriv : ∀ e ∈ Ioo (0 : ℝ) B, HasDerivAt production (deriv production e) e := by
    intro e he
    exact ((hg' e he).differentiableAt (isOpen_Ioo.mem_nhds he)).hasDerivAt
  have hgSecondDeriv : ∀ e ∈ Ioo (0 : ℝ) B,
      HasDerivAt (deriv production) (deriv (deriv production) e) e := by
    intro e he
    exact ((hg'' e he).differentiableAt (isOpen_Ioo.mem_nhds he)).hasDerivAt
  obtain ⟨beta, hbeta, hopt⟩ :=
    sourceHardBudget_supportability_independent_of_equilibrium_selection
      (cost := cost) (costDeriv := deriv cost) (costSecondDeriv := deriv (deriv cost))
      (production := production) (productionDeriv := deriv production)
      (productionSecondDeriv := deriv (deriv production)) (tie := tie)
      (B := B) (E := E) (rho := rho) (lowerSkill := lower) (skillWidth := width)
      (c := c) unitRankMeasure hskill.1 hskill.2 htie hrho.1 hrho.2 hlower hwidth hE hB
      hp hpC hpnonneg hp0 hpE hpB hpDeriv hpSecondDeriv hg hgM hg0 hgC hgSq hgDeriv
      hgSecondDeriv hg''cont hcostRatio hc
  refine ⟨beta, hbeta, ?_⟩
  intro effortM effortU score hEq d hd
  exact hopt effortM effortU score (fun a ha => (hEq a ha).1)
    (fun a ha => (hEq a ha).2) d hd

end LBG22StrategicRanking.SourceProofs
