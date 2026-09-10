import LBG22StrategicRanking.MultitaskExamples
import LBG22StrategicRanking.WeightedPrivateUtility

/-!
# An unsupported cutoff in the actual hard-budget game

The two skill ranks are independent and uniform. The measurable quantile is
`1/(2-t)`, production is linear, and effort cost is quadratic. Actual
equilibria realize the three utility vectors used in the strict chord
comparison, with the same fixed applicant tie rule at every policy.
-/

namespace LBG22StrategicRanking.MultitaskCounterexample

open Set MeasureTheory ProbabilityTheory

noncomputable def effortM (c : ℝ) (x : ℝ × ℝ) : ℝ :=
  sourceFiniteRankEffort b2CounterexampleCost b2CounterexampleScoreTechnology
    b2CounterexampleMeasurableSkill 1 1 (sourceTwoLevelCutoff c)
    (sourceTwoLevelReward b2CounterexampleRho c) x.1

noncomputable def effortU (c : ℝ) (x : ℝ × ℝ) : ℝ := b2CounterexampleBudget - effortM c x

noncomputable def score (c : ℝ) (x : ℝ × ℝ) : ℝ :=
  sourceFiniteRankScore b2CounterexampleCost b2CounterexampleScoreTechnology
    b2CounterexampleMeasurableSkill 1 1 (sourceTwoLevelCutoff c)
    (sourceTwoLevelReward b2CounterexampleRho c) x.1

noncomputable def utility (tie : ℝ × ℝ → ℝ) (beta c : ℝ) : ℝ :=
  sourceActualMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
    b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
    (effortM c) (effortU c) (score c) tie b2CounterexampleRho beta c

/-- At every feasible cutoff, the canonical source formulas solve the
two-task game and fill exactly the prescribed admission capacity. -/
theorem equilibrium_and_canonical_utility
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho))
    {tie : ℝ × ℝ → ℝ} (htie : Measurable tie)
    (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1}) :
    (Measurable (score c) ∧ AEMeasurable (effortM c) (unitRankMeasure.prod unitRankMeasure) ∧
      AEMeasurable (effortU c) (unitRankMeasure.prod unitRankMeasure)) ∧
    (∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
        b2CounterexampleCost b2CounterexampleScoreTechnology
        (fun x => b2CounterexampleMeasurableSkill x.1) (score c) tie
        b2CounterexampleBudget b2CounterexampleRho c x (effortM c x) (effortU c x)) ∧
    independentSkillPopulation unitRankMeasure
      (sourceMultitaskAdmissionEvent unitRankMeasure (score c) tie b2CounterexampleRho c) =
        ENNReal.ofReal b2CounterexampleRho ∧
    ∀ beta : ℝ, utility tie beta c = sourceSkillConditionalSchoolUtility unitRankMeasure
      b2CounterexampleUnmeasurableSkill b2CounterexampleCost b2CounterexampleScoreTechnology
      b2CounterexampleMeasurableSkill b2CounterexampleBudget 1 b2CounterexampleRho beta c := by
  have h := sourceHardBudgetEquilibrium_and_utility_of_sourcePrimitives
    (E := 1) (B := b2CounterexampleBudget) unitRankMeasure htie hinj (by norm_num [b2CounterexampleRho]) hc
    (by norm_num) (by norm_num [b2CounterexampleBudget])
    (continuous_pow 2).continuousOn b2CounterexampleCost_strictMonoOn
    (by norm_num [b2CounterexampleCost]) (by norm_num [b2CounterexampleCost])
    (by norm_num [b2CounterexampleCost, b2CounterexampleBudget])
    (b2CounterexampleCost_strictConvexOn.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    b2CounterexampleScoreTechnology_continuous.continuousOn
    (b2CounterexampleScoreTechnology_strictMono.strictMonoOn _) (by norm_num [b2CounterexampleScoreTechnology])
    (concaveOn_id (convex_Icc _ _)) b2CounterexampleMeasurableSkill_continuousOn
    b2CounterexampleMeasurableSkill_strictMonoOn (by norm_num [b2CounterexampleMeasurableSkill])
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 b2CounterexampleUnmeasurableSkill⟩

theorem scoreScale_eq_thresholdEffort
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) :
    sourceScoreScale b2CounterexampleCost b2CounterexampleScoreTechnology 1 b2CounterexampleRho c =
      b2CounterexampleThresholdEffort c := by
  have hc1 : c < 1 := by norm_num [b2CounterexampleRho] at hc; linarith [hc.2]
  have hmem := (b2CounterexampleEfforts_mem_unit_interval hc.1 hc.2 ⟨le_rfl, hc1.le⟩).1
  have hδ : b2CounterexampleThresholdEffort c ∈ Icc (0 : ℝ) 1 := by
    simpa only [b2CounterexampleMeasurableEffort, mul_div_cancel_right₀ _
      (show 2 - c ≠ 0 by linarith)] using hmem
  change effortIntervalInverse b2CounterexampleCost 1 (b2CounterexampleRho / (1 - c)) = _
  rw [← b2CounterexampleThresholdEffort_cost_eq_highProbability hc1]
  exact (b2CounterexampleCost_strictMonoOn.mono Icc_subset_Ici_self).injOn.leftInvOn_invFunOn hδ

/-- The admitted source effort is exactly the retained elementary formula. -/
theorem canonical_effort_eq
    {c t : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) (ht : t ∈ Icc c 1) :
    sourceTwoLevelEffort b2CounterexampleCost b2CounterexampleScoreTechnology
      b2CounterexampleMeasurableSkill 1 b2CounterexampleRho c t = b2CounterexampleMeasurableEffort c t := by
  have hc1 : c < 1 := by norm_num [b2CounterexampleRho] at hc; linarith [hc.2]
  have he := (b2CounterexampleEfforts_mem_unit_interval hc.1 hc.2 ht).1
  have harg : sourceScoreScale b2CounterexampleCost b2CounterexampleScoreTechnology 1 b2CounterexampleRho c *
      (b2CounterexampleMeasurableSkill c / b2CounterexampleMeasurableSkill t) =
        b2CounterexampleMeasurableEffort c t := by
    rw [scoreScale_eq_thresholdEffort hc,
      b2CounterexampleMeasurableEffort_eq_source_ratio ⟨hc.1.le, hc1.le⟩ ⟨(hc.1.le.trans ht.1), ht.2⟩]
    ring
  unfold sourceTwoLevelEffort
  rw [harg]
  change max (effortIntervalInverse id 1 (max (b2CounterexampleMeasurableEffort c t) 0)) 0 = _
  rw [max_eq_left he.1]
  have hi := (effortIntervalInverse_spec (f := id) (by norm_num : (0 : ℝ) ≤ 1)
    continuousOn_id he).2
  change effortIntervalInverse id 1 (b2CounterexampleMeasurableEffort c t) = _ at hi
  rw [hi, max_eq_left he.1]

/-- The canonical conditional integral equals the two elementary utility
coordinates; independence and the admission normalization are derived. -/
theorem canonical_utility_eq_weighted
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho)) (beta : ℝ) :
    sourceSkillConditionalSchoolUtility unitRankMeasure b2CounterexampleUnmeasurableSkill
      b2CounterexampleCost b2CounterexampleScoreTechnology b2CounterexampleMeasurableSkill
      b2CounterexampleBudget 1 b2CounterexampleRho beta c =
      weightedPrivateUtility beta b2CounterexampleMeasurableUtility b2CounterexampleUnmeasurableUtility c := by
  have hc1 : c < 1 := by norm_num [b2CounterexampleRho] at hc; linarith [hc.2]
  have hrho : 0 < b2CounterexampleRho := by norm_num [b2CounterexampleRho]
  have hden : 1 - c ≠ 0 := (sub_pos.mpr hc1).ne'
  have hRcont : Continuous (b2CounterexampleUnmeasurableEffort c) :=
    continuous_const.sub ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _)
  have hRint : IntegrableOn (b2CounterexampleUnmeasurableEffort c) (Ioc c 1) volume :=
    hRcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hskill := (unitRankMeasure_skill_integrable_and_mean_pos
    b2CounterexampleUnmeasurableSkill_continuousOn b2CounterexampleUnmeasurableSkill_strictMonoOn
    (by norm_num [b2CounterexampleUnmeasurableSkill])).1
  have hmean : (∫ u, b2CounterexampleUnmeasurableSkill u ∂unitRankMeasure) = (1 : ℝ) / 2 := by
    change (∫ u in Ioc (0 : ℝ) 1, b2CounterexampleUnmeasurableSkill u) = _
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact b2CounterexampleUnmeasurableSkill_mean
  have hM := independentSkillPopulation_conditional_utility unitRankMeasure hrho hc
    (R := fun _ => b2CounterexampleMeasurableUtility c)
    (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) unitRankMeasure)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul,
    intervalIntegral.integral_const, mul_div_cancel_left₀ _ hden] at hM
  have hR := independentSkillPopulation_conditional_utility unitRankMeasure hrho hc hRint hskill
  have hRvalue : (∫ z : (ℝ × ℝ) × ℝ,
      b2CounterexampleUnmeasurableEffort c z.1.1 * b2CounterexampleUnmeasurableSkill z.2
      ∂ProbabilityTheory.cond (independentSkillPopulation unitRankMeasure)
        (twoLevelAdmissionEvent b2CounterexampleRho c)) = b2CounterexampleUnmeasurableUtility c := by
    rw [hR.2, hmean, b2CounterexampleUnmeasurableEffort_tailIntegral hc1,
      mul_div_cancel_left₀ _ hden]
    rfl
  have heq : sourceSkillConditionalSchoolUtility unitRankMeasure b2CounterexampleUnmeasurableSkill
      b2CounterexampleCost b2CounterexampleScoreTechnology b2CounterexampleMeasurableSkill
      b2CounterexampleBudget 1 b2CounterexampleRho beta c =
      ∫ z : (ℝ × ℝ) × ℝ,
        beta * b2CounterexampleMeasurableUtility c + (1 - beta) *
          (b2CounterexampleUnmeasurableEffort c z.1.1 * b2CounterexampleUnmeasurableSkill z.2)
        ∂ProbabilityTheory.cond (independentSkillPopulation unitRankMeasure)
          (twoLevelAdmissionEvent b2CounterexampleRho c) := by
    unfold sourceSkillConditionalSchoolUtility
    apply integral_congr_ae
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (twoLevelAdmissionEvent_measurable (α := ℝ) b2CounterexampleRho c)] with z hz
    have ht : z.1.1 ∈ Icc c 1 := ⟨hz.1.1.1.le, hz.1.1.2⟩
    rw [canonical_effort_eq hc ht,
      b2CounterexampleMeasurableScore_eq_utility ⟨hc.1.le, hc1.le⟩ ⟨hc.1.le.trans ht.1, ht.2⟩]
    rfl
  rw [heq, integral_add (hM.1.const_mul beta) (hR.1.const_mul (1 - beta)),
    integral_const_mul, integral_const_mul, integral_const, smul_eq_mul, hM.2, hRvalue]
  rfl

/-- Actual equilibrium utility, not merely a prescribed effort formula,
has the retained weighted-coordinate expression for every feasible cutoff. -/
theorem actual_utility_eq_weighted
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho))
    {tie : ℝ × ℝ → ℝ} (htie : Measurable tie)
    (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1}) (beta : ℝ) :
    utility tie beta c =
      weightedPrivateUtility beta b2CounterexampleMeasurableUtility b2CounterexampleUnmeasurableUtility c := by
  rw [(equilibrium_and_canonical_utility hc htie hinj).2.2.2 beta]
  exact canonical_utility_eq_weighted hc beta

/-- The target cutoff is not supported by any interior school weight, even
when comparisons are restricted to two other interior policies and their
actual equilibria in the same population. -/
theorem actual_target_strictly_dominated_for_every_weight
    {tie : ℝ × ℝ → ℝ} (htie : Measurable tie)
    (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1})
    {beta : ℝ} (hbeta : beta ∈ Ioo (0 : ℝ) 1) :
    ∃ d ∈ Ioo (0 : ℝ) (1 - b2CounterexampleRho),
      (d = b2CounterexampleLeftCutoff ∨ d = b2CounterexampleRightCutoff) ∧
      utility tie beta b2CounterexampleTargetCutoff < utility tie beta d := by
  have hleft : b2CounterexampleLeftCutoff ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho) := by
    norm_num [b2CounterexampleLeftCutoff, b2CounterexampleRho]
  have hright : b2CounterexampleRightCutoff ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho) := by
    norm_num [b2CounterexampleRightCutoff, b2CounterexampleRho]
  have htarget : b2CounterexampleTargetCutoff ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho) := by
    norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho]
  have hbetter : utility tie beta b2CounterexampleTargetCutoff < utility tie beta b2CounterexampleLeftCutoff ∨
      utility tie beta b2CounterexampleTargetCutoff < utility tie beta b2CounterexampleRightCutoff := by
    rw [actual_utility_eq_weighted htarget htie hinj beta, actual_utility_eq_weighted hleft htie hinj beta,
      actual_utility_eq_weighted hright htie hinj beta]
    by_contra hn
    push Not at hn
    norm_num [weightedPrivateUtility, b2CounterexampleMeasurableUtility,
      b2CounterexampleUnmeasurableUtility, b2CounterexampleUnmeasurableEffortTailMean,
      b2CounterexampleLeftCutoff, b2CounterexampleTargetCutoff, b2CounterexampleRightCutoff] at hn
    linarith [hbeta.2]
  rcases hbetter with hleftBetter | hrightBetter
  · exact ⟨b2CounterexampleLeftCutoff, by norm_num [b2CounterexampleLeftCutoff, b2CounterexampleRho],
      Or.inl rfl, hleftBetter⟩
  · exact ⟨b2CounterexampleRightCutoff, by norm_num [b2CounterexampleRightCutoff, b2CounterexampleRho],
      Or.inr rfl, hrightBetter⟩

/-- A concrete collision-free unit-interval tie rule, source-admissible
primitives, and a full actual-equilibrium family refute universal interior
cutoff supportability. No population, effort, or utility identity is assumed. -/
theorem source_hardBudget_supportability_counterexample :
    B2SourcePrimitiveRegularity b2CounterexampleRho b2CounterexampleBudget
      b2CounterexampleScoreTechnology b2CounterexampleCost
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill ∧
    (Measurable MultitaskExample.tie ∧ Function.Injective MultitaskExample.tie ∧
      ∀ x, MultitaskExample.tie x ∈ Ioo (0 : ℝ) 1) ∧
    (∀ c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho),
      (∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
        SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
          b2CounterexampleCost b2CounterexampleScoreTechnology
          (fun x => b2CounterexampleMeasurableSkill x.1) (score c) MultitaskExample.tie
          b2CounterexampleBudget b2CounterexampleRho c x (effortM c x) (effortU c x)) ∧
      independentSkillPopulation unitRankMeasure
        (sourceMultitaskAdmissionEvent unitRankMeasure (score c) MultitaskExample.tie b2CounterexampleRho c) =
          ENNReal.ofReal b2CounterexampleRho) ∧
    b2CounterexampleTargetCutoff ∈ Ioo (0 : ℝ) (1 - b2CounterexampleRho) ∧
    ∀ beta ∈ Ioo (0 : ℝ) 1, ∃ d ∈ Ioo (0 : ℝ) (1 - b2CounterexampleRho),
      utility MultitaskExample.tie beta b2CounterexampleTargetCutoff < utility MultitaskExample.tie beta d := by
  refine ⟨b2Counterexample_sourcePrimitiveRegularity, MultitaskExample.tie_spec, ?_,
    by norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho], ?_⟩
  · intro c hc
    have h := equilibrium_and_canonical_utility hc MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn
    exact ⟨h.2.1, h.2.2.1⟩
  · intro beta hb
    obtain ⟨d, hd, _, hbetter⟩ := actual_target_strictly_dominated_for_every_weight
      MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn hb
    exact ⟨d, hd, hbetter⟩

/-- Every actual equilibrium of the counterexample, including profiles
depending on both skill coordinates, realizes the same utility vector. -/
theorem arbitrary_equilibrium_utility_eq_weighted
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho))
    {tie eM eU s : ℝ × ℝ → ℝ} (htie : Measurable tie) (hs : Measurable s)
    [NoAtoms (Measure.map tie (unitRankMeasure.prod unitRankMeasure))]
    (hb : ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
        b2CounterexampleCost b2CounterexampleScoreTechnology
        (fun x => b2CounterexampleMeasurableSkill x.1) s tie
        b2CounterexampleBudget b2CounterexampleRho c x (eM x) (eU x)) (beta : ℝ) :
    sourceActualMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
      eM eU s tie b2CounterexampleRho beta c =
      weightedPrivateUtility beta b2CounterexampleMeasurableUtility b2CounterexampleUnmeasurableUtility c := by
  have h := sourceHardBudgetEquilibrium_utility (E := 1) unitRankMeasure
    (by norm_num [b2CounterexampleRho]) hc
    (by norm_num [b2CounterexampleBudget])
    (by norm_num [b2CounterexampleBudget, b2CounterexampleCost])
    (by norm_num) (by norm_num [b2CounterexampleCost])
    (continuous_pow 2).continuousOn b2CounterexampleCost_strictConvexOn
    (fun e _ => sq_nonneg e) (by norm_num [b2CounterexampleCost])
    b2CounterexampleScoreTechnology_continuous.continuousOn
    (b2CounterexampleScoreTechnology_strictMono.strictMonoOn _) (concaveOn_id (convex_Ici _))
    (by norm_num [b2CounterexampleScoreTechnology]) b2CounterexampleMeasurableSkill_continuousOn
    b2CounterexampleMeasurableSkill_strictMonoOn (by norm_num [b2CounterexampleMeasurableSkill])
    hs htie hb b2CounterexampleUnmeasurableSkill beta
  exact h.trans (canonical_utility_eq_weighted hc beta)

/-- The unsupported cutoff cannot be rescued by another equilibrium
selection. The concrete fixed tie rule and all model primitives are the
same as in the nonvacuous equilibrium family above. -/
theorem target_unsupported_in_every_equilibrium_selection
    (eM eU s : ℝ → ℝ × ℝ → ℝ)
    (hs : ∀ d ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho), Measurable (s d))
    (hb : ∀ d ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho), ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
        b2CounterexampleCost b2CounterexampleScoreTechnology
        (fun x => b2CounterexampleMeasurableSkill x.1) (s d) MultitaskExample.tie
        b2CounterexampleBudget b2CounterexampleRho d x (eM d x) (eU d x))
    {beta : ℝ} (hbeta : beta ∈ Ioo (0 : ℝ) 1) :
    ∃ d ∈ Ioo (0 : ℝ) (1 - b2CounterexampleRho),
      sourceActualMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
        (eM b2CounterexampleTargetCutoff) (eU b2CounterexampleTargetCutoff)
        (s b2CounterexampleTargetCutoff) MultitaskExample.tie b2CounterexampleRho beta b2CounterexampleTargetCutoff <
      sourceActualMultitaskSchoolUtility unitRankMeasure b2CounterexampleScoreTechnology
        b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill
        (eM d) (eU d) (s d) MultitaskExample.tie b2CounterexampleRho beta d := by
  haveI := MultitaskExample.tie_noAtoms
  have ht : b2CounterexampleTargetCutoff ∈ Ioc (0 : ℝ) (1 - b2CounterexampleRho) := by
    norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho]
  obtain ⟨d, hd, _, hbetter⟩ := actual_target_strictly_dominated_for_every_weight
    MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn hbeta
  rw [actual_utility_eq_weighted ht MultitaskExample.tie_spec.1 MultitaskExample.tie_spec.2.1.injOn beta,
    actual_utility_eq_weighted ⟨hd.1, hd.2.le⟩ MultitaskExample.tie_spec.1
      MultitaskExample.tie_spec.2.1.injOn beta] at hbetter
  refine ⟨d, hd, ?_⟩
  rw [arbitrary_equilibrium_utility_eq_weighted ht MultitaskExample.tie_spec.1
      (hs _ ht) (hb _ ht) beta,
    arbitrary_equilibrium_utility_eq_weighted ⟨hd.1, hd.2.le⟩ MultitaskExample.tie_spec.1
      (hs _ ⟨hd.1, hd.2.le⟩) (hb _ ⟨hd.1, hd.2.le⟩) beta]
  exact hbetter

end LBG22StrategicRanking.MultitaskCounterexample
