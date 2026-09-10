import LBG22StrategicRanking.MultitaskPrimitiveRepairs
import LBG22StrategicRanking.MultitaskUniqueness
import LBG22StrategicRanking.SquareRootPrimitiveRepairs
import LBG22StrategicRanking.ThreeLevelPrimitiveRepairs
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# A nondegenerate hard-budget multitask example

Both skills vary independently. Quadratic cost and square-root production
support every interior cutoff in an actual equilibrium family. A bounded
measurable injection of the full applicant type supplies a valid fixed tie
rule, independently of the admission lottery.
-/

open Set MeasureTheory ProbabilityTheory

namespace LBG22StrategicRanking.MultitaskExample

noncomputable def squash (a : ℝ) : ℝ := Real.exp a / (1 + Real.exp a)
noncomputable def tie (x : ℝ × ℝ) : ℝ := squash (embeddingReal (ℝ × ℝ) x)

theorem squash_strictMono : StrictMono squash := by
  intro a b hab
  have ha := Real.exp_pos a
  have hb := Real.exp_pos b
  have he := Real.exp_lt_exp.mpr hab
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + Real.exp a)
    (by linarith : 0 < 1 + Real.exp b)).mpr
  nlinarith

/-- The fixed tie rule is measurable, collision-free, and valued in the unit interval. -/
theorem tie_spec : Measurable tie ∧ Function.Injective tie ∧ ∀ x, tie x ∈ Ioo (0 : ℝ) 1 := by
  have hm := Real.continuous_exp.measurable.comp (measurable_embeddingReal (ℝ × ℝ))
  refine ⟨hm.div (measurable_const.add hm),
    squash_strictMono.injective.comp (measurableEmbedding_embeddingReal (ℝ × ℝ)).injective, ?_⟩
  intro x
  have h := Real.exp_pos (embeddingReal (ℝ × ℝ) x)
  constructor
  · exact div_pos h (by linarith)
  · exact (div_lt_one (by linarith : 0 < 1 + Real.exp (embeddingReal (ℝ × ℝ) x))).mpr (by linarith)

noncomputable def effortM (d : ℝ) (x : ℝ × ℝ) : ℝ :=
  sourceFiniteRankEffort (fun e => e ^ 2) Real.sqrt (fun t => 1 + t) 1 1
    (sourceTwoLevelCutoff d) (sourceTwoLevelReward (1 / 4) d) x.1
noncomputable def effortU (d : ℝ) (x : ℝ × ℝ) : ℝ := 1 - effortM d x
noncomputable def score (d : ℝ) (x : ℝ × ℝ) : ℝ :=
  sourceFiniteRankScore (fun e => e ^ 2) Real.sqrt (fun t => 1 + t) 1 1
    (sourceTwoLevelCutoff d) (sourceTwoLevelReward (1 / 4) d) x.1

/-- Actual two-task best responses and capacity hold at every feasible cutoff;
each interior cutoff maximizes conditional school utility for some interior weight. -/
theorem actual_equilibrium_family_and_supportability :
    (∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4),
      (Measurable (score d) ∧ AEMeasurable (effortM d) (unitRankMeasure.prod unitRankMeasure) ∧
        AEMeasurable (effortU d) (unitRankMeasure.prod unitRankMeasure)) ∧
      (∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
        SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure) (fun e => e ^ 2) Real.sqrt
          (fun x => 1 + x.1) (score d) tie 1 (1 / 4) d x (effortM d x) (effortU d x)) ∧
      independentSkillPopulation unitRankMeasure
        (sourceMultitaskAdmissionEvent unitRankMeasure (score d) tie (1 / 4) d) = ENNReal.ofReal (1 / 4)) ∧
    ∀ c ∈ Ioo (0 : ℝ) (1 - 1 / 4), ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4),
      sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
        (effortM d) (effortU d) (score d) tie (1 / 4) beta d ≤
      sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
        (effortM c) (effortU c) (score c) tie (1 / 4) beta c := by
  have hmean := unitRankMeasure_skill_integrable_and_mean_pos (skill := id)
    continuous_id.continuousOn (strictMono_id.strictMonoOn _) (by norm_num)
  have hsq : ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun e => (Real.sqrt e) ^ 2) :=
    (concaveOn_id (convex_Ioo _ _)).congr (fun e he => (Real.sq_sqrt he.1.le).symm)
  have hsecond : ContinuousOn (fun e => -1 / (4 * (Real.sqrt e) ^ 3)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.div (continuousOn_const.mul (Real.continuous_sqrt.continuousOn.pow 3))
      (fun e he => mul_ne_zero (by norm_num) (pow_ne_zero 3 (Real.sqrt_pos.mpr he.1).ne'))
  have h := sourceHardBudgetEquilibria_support_all_interior_cutoffs_of_affineSkill
    (costDeriv := fun e => 2 * e) (costSecondDeriv := fun _ => 2)
    (productionDeriv := fun e => 1 / (2 * Real.sqrt e))
    (productionSecondDeriv := fun e => -1 / (4 * (Real.sqrt e) ^ 3))
    (lowerSkill := 1) (skillWidth := 1) (E := 1) (B := 1) (rho := 1 / 4)
    unitRankMeasure hmean.1 hmean.2 tie_spec.1 tie_spec.2.1.injOn
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (continuous_pow 2).continuousOn quadraticCost_strictMono (by norm_num) (by norm_num) (by norm_num)
    ((convexOn_pow 2).subset Icc_subset_Ici_self (convex_Icc _ _))
    (fun e _ => by convert (hasDerivAt_id e).pow 2 using 1; norm_num [id_eq])
    (fun e _ => by simpa using (hasDerivAt_id e).const_mul 2)
    Real.continuous_sqrt.continuousOn (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)
    (Real.strictConcaveOn_sqrt.concaveOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    hsq (fun e he => Real.hasDerivAt_sqrt he.1.ne') (fun e he => sqrt_marginal_hasDerivAt he.1)
    hsecond (sqrt_quadratic_costRatio_convexOn (by norm_num) (by norm_num))
  simpa only [one_mul] using h

theorem deterministic_budget_feasibility : ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
    0 ≤ effortM (3 / 4) x ∧ 0 ≤ effortU (3 / 4) x ∧
      effortM (3 / 4) x + effortU (3 / 4) x = 1 := by
  filter_upwards [(actual_equilibrium_family_and_supportability.1 (3 / 4) (by norm_num)).2.1] with x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

theorem interior_cutoff_supportability : ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4),
    sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
      (effortM d) (effortU d) (score d) tie (1 / 4) beta d ≤
    sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
      (effortM (1 / 2)) (effortU (1 / 2)) (score (1 / 2)) tie (1 / 4) beta (1 / 2) :=
  actual_equilibrium_family_and_supportability.2 (1 / 2) (by norm_num)

theorem fixed_budget_cost : sourceMultitaskCost (fun e : ℝ => e ^ 2) 1 (3 / 4) (1 / 4) = 9 / 16 := by
  rw [sourceMultitaskCost_eq_of_budget (by norm_num)]
  norm_num

theorem tie_noAtoms : NoAtoms (Measure.map tie (unitRankMeasure.prod unitRankMeasure)) := by
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  exact noAtoms_map_tie_of_injOn_fullMeasure tie_spec.1 tie_spec.2.1.injOn
    ((measurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioc))

/-- The nondegenerate instance has the same utility in every actual
equilibrium, not only in the explicitly constructed family above. -/
theorem arbitrary_equilibrium_utility
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4))
    {eM eU s : ℝ × ℝ → ℝ} (hs : Measurable s)
    (hb : ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
      SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
        (fun e => e ^ 2) Real.sqrt (fun x => 1 + x.1) s tie 1 (1 / 4) c x (eM x) (eU x))
    (beta : ℝ) :
    sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
      eM eU s tie (1 / 4) beta c =
    sourceSkillConditionalSchoolUtility unitRankMeasure id (fun e => e ^ 2) Real.sqrt
      (fun t => 1 + t) 1 1 (1 / 4) beta c := by
  haveI := tie_noAtoms
  exact sourceHardBudgetEquilibrium_utility unitRankMeasure (by norm_num) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (continuous_pow 2).continuousOn quadraticCost_strictConvex (fun e _ => sq_nonneg e) (by norm_num)
    Real.continuous_sqrt.continuousOn Real.strictMonoOn_sqrt Real.strictConcaveOn_sqrt.concaveOn (by norm_num)
    (continuous_const.add continuous_id).continuousOn
    (fun _ _ _ _ hab => add_lt_add_right hab 1) (by norm_num) hs tie_spec.1 hb id beta

/-- The supporting weight is valid before choosing any equilibrium family. -/
theorem every_equilibrium_selection_supports_interior_cutoffs
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) (1 - 1 / 4)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ eM eU s : ℝ → ℝ × ℝ → ℝ,
      (∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4), Measurable (s d)) →
      (∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4), ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
        SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure)
          (fun e => e ^ 2) Real.sqrt (fun x => 1 + x.1) (s d) tie 1 (1 / 4) d x (eM d x) (eU d x)) →
      ∀ d ∈ Ioc (0 : ℝ) (1 - 1 / 4),
        sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
          (eM d) (eU d) (s d) tie (1 / 4) beta d ≤
        sourceActualMultitaskSchoolUtility unitRankMeasure Real.sqrt (fun t => 1 + t) id
          (eM c) (eU c) (s c) tie (1 / 4) beta c := by
  obtain ⟨beta, hbeta, hopt⟩ := actual_equilibrium_family_and_supportability.2 c hc
  refine ⟨beta, hbeta, ?_⟩
  intro eM eU s hs hb d hd
  have heq (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1 - 1 / 4)) := arbitrary_equilibrium_utility ha
    (actual_equilibrium_family_and_supportability.1 a ha).1.1
    (actual_equilibrium_family_and_supportability.1 a ha).2.1 beta
  have h := hopt d hd
  rw [heq d hd, heq c ⟨hc.1, hc.2.le⟩] at h
  rw [arbitrary_equilibrium_utility hd (hs d hd) (hb d hd) beta,
    arbitrary_equilibrium_utility ⟨hc.1, hc.2.le⟩ (hs c ⟨hc.1, hc.2.le⟩) (hb c ⟨hc.1, hc.2.le⟩) beta]
  exact h

end LBG22StrategicRanking.MultitaskExample
