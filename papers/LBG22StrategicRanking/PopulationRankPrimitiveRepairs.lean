import LBG22StrategicRanking.EnvironmentPrimitiveRepairs

/-!
# Score separation and actual two-level population ranks

A score gap separating two measurable population groups realizes their
prescribed rank cutoff. Scores below the admitted group's lower bound
cannot reach the upper reward, including counterfactual scores in the gap.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

/-- A two-band score separation realizes a population rank cutoff and
bounds every off-path rank below the admitted score threshold. The mass of
the lower group fixes the cutoff; uniform actual ranks remove its null
boundary. No alignment between skill and tie keys is required. -/
theorem sourcePopulation_twoLevelRank_of_score_separation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill score tie : α → ℝ} {a lowerScore upperScore c : ℝ}
    (hscore : Measurable score) (htie : Measurable tie) [NoAtoms (Measure.map tie μ)]
    (hmass : μ.real {x | skill x ≤ a} = c) (hsep : lowerScore < upperScore)
    (hprofile : ∀ᵐ x ∂μ,
      (skill x ≤ a → score x ≤ lowerScore) ∧ (a < skill x → upperScore ≤ score x)) :
    (∀ x v, v < upperScore → counterfactualTieBrokenRank μ score tie x v ≤ c) ∧
      (∀ᵐ x ∂μ, c < tieBrokenRank μ score tie x ↔ a < skill x) := by
  have hcounter (x : α) (v : ℝ) (hv : v < upperScore) :
      counterfactualTieBrokenRank μ score tie x v ≤ c := by
    have hsubset : {y | score y < v ∨ score y = v ∧ tie y ≤ tie x} ≤ᵐ[μ] {y | skill y ≤ a} := by
      filter_upwards [hprofile] with y hy hcontour
      by_contra hn
      have hhigh := hy.2 (lt_of_not_ge hn)
      rcases hcontour with hlt | ⟨heq, _⟩ <;> linarith
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)).trans_eq hmass
  have hnull : μ {x | tieBrokenRank μ score tie x = c} = 0 := by
    have hu := congrArg (fun ν : Measure ℝ => ν {c})
      (tieBrokenRank_map_eq_uniform_of_noAtoms_tie μ hscore htie)
    dsimp only at hu
    rw [Measure.map_apply (measurable_tieBrokenRank hscore htie) (measurableSet_singleton c),
      measure_singleton] at hu
    exact hu
  have hneq : ∀ᵐ x ∂μ, tieBrokenRank μ score tie x ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  refine ⟨hcounter, ?_⟩
  filter_upwards [hprofile, hneq] with x hx hxc
  constructor
  · intro hrank
    by_contra hn
    have hs := (hx.1 (le_of_not_gt hn)).trans_lt hsep
    have h := hcounter x (score x) hs
    rw [counterfactualTieBrokenRank_at_current_score] at h
    exact (not_le_of_gt hrank) h
  · intro hskill
    have hsubset : {y | skill y ≤ a} ≤ᵐ[μ] tieBrokenLowerContour score tie x := by
      filter_upwards [hprofile] with y hy hyskill
      exact Or.inl ((hy.1 hyskill).trans_lt (hsep.trans_le (hx.2 hskill)))
    have hbound := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
    change μ.real {y | skill y ≤ a} ≤ tieBrokenRank μ score tie x at hbound
    rw [hmass] at hbound
    exact lt_of_le_of_ne hbound hxc.symm

end LBG22StrategicRanking
