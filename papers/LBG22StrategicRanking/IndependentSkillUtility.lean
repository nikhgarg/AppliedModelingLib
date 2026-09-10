import LBG22StrategicRanking.WeightedPrimitiveRepairs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability

/-!
# Conditional utilities under independent skill and admission randomization

The population consists of an independent uniform measurable rank, uniform
admission lottery, and an arbitrary unmeasurable-skill law. Restricting this
fixed population to the two-level admission event derives both its capacity
and its conditional utility; no candidate policy chooses a new population law.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Uniform probability on the unit rank interval, with a null lower boundary. -/
noncomputable def unitRankMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

instance unitRankMeasure_isProbabilityMeasure : IsProbabilityMeasure unitRankMeasure := by
  constructor
  simp [unitRankMeasure, Real.volume_Ioc]

/-- A fixed joint population: measurable rank, independent admission lottery,
and independent unmeasurable skill. -/
noncomputable def independentSkillPopulation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : Measure ((ℝ × ℝ) × α) :=
  (unitRankMeasure.prod unitRankMeasure).prod μ

instance independentSkillPopulation_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (independentSkillPopulation μ) := by
  unfold independentSkillPopulation
  infer_instance

/-- A two-level policy admits the upper rank band with probability
`rho/(1-c)`, independently of the unmeasurable skill coordinate. -/
def twoLevelAdmissionEvent {α : Type*} (rho c : ℝ) : Set ((ℝ × ℝ) × α) :=
  (Ioc c 1 ×ˢ Ioc 0 (rho / (1 - c))) ×ˢ univ

theorem twoLevelAdmissionEvent_measurable {α : Type*} [MeasurableSpace α] (rho c : ℝ) :
    MeasurableSet (twoLevelAdmissionEvent (α := α) rho c) :=
  (measurableSet_Ioc.prod measurableSet_Ioc).prod MeasurableSet.univ

/-- Conditioning restricts only the measurable-rank and lottery coordinates. -/
theorem independentSkillPopulation_restrict_admission
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {rho c : ℝ} (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    (independentSkillPopulation μ).restrict (twoLevelAdmissionEvent rho c) =
      ((volume.restrict (Ioc c 1)).prod (volume.restrict (Ioc 0 (rho / (1 - c))))).prod μ := by
  have hden : 0 < 1 - c := by linarith [hc.2]
  have hq : rho / (1 - c) ≤ 1 := (div_le_one hden).mpr (by linarith [hc.2])
  unfold independentSkillPopulation twoLevelAdmissionEvent
  rw [← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_restrict]
  unfold unitRankMeasure
  rw [Measure.restrict_restrict_of_subset (show Ioc c (1 : ℝ) ⊆ Ioc 0 1 from
      fun _ ht => ⟨hc.1.trans ht.1, ht.2⟩),
    Measure.restrict_restrict_of_subset (show Ioc (0 : ℝ) (rho / (1 - c)) ⊆ Ioc 0 1 from
      fun _ ht => ⟨ht.1, ht.2.trans hq⟩)]

/-- The actual randomized admission event has the prescribed capacity. -/
theorem independentSkillPopulation_admission_mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {rho c : ℝ} (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    independentSkillPopulation μ (twoLevelAdmissionEvent rho c) = ENNReal.ofReal rho := by
  have hden : 0 < 1 - c := by linarith [hc.2]
  rw [← Measure.restrict_apply_univ,
    independentSkillPopulation_restrict_admission μ hrho hc]
  rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := μ), mul_one,
    ← univ_prod_univ, Measure.prod_prod]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [← ENNReal.ofReal_mul hden.le]
  congr 1
  field_simp

/-- Conditional residual output times independent unmeasurable skill is
integrable and factors into the skill mean times the admitted rank average.
The admission lottery cancels through its proved positive capacity. -/
theorem independentSkillPopulation_conditional_utility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {R : ℝ → ℝ} {skill : α → ℝ} {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hR : IntegrableOn R (Ioc c 1) volume) (hskill : Integrable skill μ) :
    Integrable (fun z : (ℝ × ℝ) × α => R z.1.1 * skill z.2)
      (ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)) ∧
    (∫ z : (ℝ × ℝ) × α, R z.1.1 * skill z.2
      ∂ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)) =
      (∫ u, skill u ∂μ) * ((∫ t in c..1, R t) / (1 - c)) := by
  have hden : 0 < 1 - c := by linarith [hc.2]
  have hq : 0 < rho / (1 - c) := div_pos hrho hden
  have hmass := independentSkillPopulation_admission_mass μ hrho hc
  have hrestrict := independentSkillPopulation_restrict_admission μ hrho hc
  have hprod : Integrable (fun z : (ℝ × ℝ) × α => R z.1.1 * skill z.2)
      (((volume.restrict (Ioc c 1)).prod
        (volume.restrict (Ioc 0 (rho / (1 - c))))).prod μ) :=
    (hR.comp_fst (ν := volume.restrict (Ioc 0 (rho / (1 - c))))).mul_prod hskill
  unfold ProbabilityTheory.cond
  rw [hmass, hrestrict]
  refine ⟨hprod.smul_measure (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hrho)), ?_⟩
  rw [integral_smul_measure, integral_prod_mul (fun p : ℝ × ℝ => R p.1) skill,
    integral_fun_fst R]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hrho.le, smul_eq_mul,
    measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hq.le]
  rw [intervalIntegral.integral_of_le (by linarith [hc.2] : c ≤ 1)]
  field_simp

/-- The source's admitted effort is continuous and remains in its feasible
compact interval. These facts provide population integrability directly. -/
theorem sourceTwoLevelEffort_uniform_continuousOn_and_mem
    {cost production : ℝ → ℝ} {effortMax rho c : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (hc : 0 < c) :
    ContinuousOn (sourceTwoLevelEffort cost production id effortMax rho c) (Icc c 1) ∧
      ∀ t ∈ Icc c 1, sourceTwoLevelEffort cost production id effortMax rho c t ∈ Icc 0 effortMax := by
  let a := sourceScoreScale cost production effortMax rho c
  have hs (t : ℝ) (ht : t ∈ Icc c 1) : a * c / t ∈ Icc (production 0) (production effortMax) := by
    have htpos : 0 < t := hc.trans_le ht.1
    rw [hg_zero]
    refine ⟨(div_pos (mul_pos ha.1 hc) htpos).le, ?_⟩
    exact ((div_le_iff₀ htpos).mpr (mul_le_mul_of_nonneg_left ht.1 ha.1.le)).trans ha.2
  have hscont : ContinuousOn (fun t => a * c / t) (Icc c 1) :=
    continuousOn_const.div continuousOn_id (fun _ ht => (hc.trans_le ht.1).ne')
  have hi := (effortIntervalInverse_continuousOn hmax hg hg_mono).comp hscont hs
  have heq (t : ℝ) (ht : t ∈ Icc c 1) :=
    sourceTwoLevelEffort_uniform_eq_inverse hmax hg hg_zero ha hc ht
  refine ⟨hi.congr heq, ?_⟩
  intro t ht
  rw [heq t ht]
  exact (effortIntervalInverse_spec hmax hg (hs t ht)).1

/-- The school's conditional weighted utility under the fixed independent
population law and the actual two-level admission event. -/
noncomputable def sourceTwoLevelConditionalSchoolUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (skill : α → ℝ)
    (cost production : ℝ → ℝ) (budget effortMax rho beta c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α,
    beta * (production (sourceTwoLevelEffort cost production id effortMax rho c z.1.1) * z.1.1) +
    (1 - beta) * (production (budget -
      sourceTwoLevelEffort cost production id effortMax rho c z.1.1) * skill z.2)
    ∂ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)

/-- The two component integrals in the weighted-optimality theorem equal the
school's genuine conditional expectation, with integrability proved from the
source effort primitives and the unmeasurable skill's finite first moment. -/
theorem sourceTwoLevelConditionalSchoolUtility_eq_weighted
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill : α → ℝ} (hskill : Integrable skill μ)
    {cost production : ℝ → ℝ} {budget effortMax rho beta c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    sourceTwoLevelConditionalSchoolUtility μ skill cost production budget effortMax rho beta c =
      weightedPrivateUtility beta (sourceTwoLevelMeasurableUtility cost production effortMax rho)
        (fun t => (∫ u, skill u ∂μ) * sourceTwoLevelResidualUtility cost production budget effortMax rho t) c := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have ha := (uniformSkillOutputInverse_at_sourceCutoff hrho hrho_one hmax hcost hcost_mono
    hcost_zero hcost_max hgE hmonoE hg_zero hc).1
  have he := sourceTwoLevelEffort_uniform_continuousOn_and_mem hmax.le hgE hmonoE hg_zero ha hc.1
  let M := fun t => production (sourceTwoLevelEffort cost production id effortMax rho c t) * t
  let R := fun t => production (budget - sourceTwoLevelEffort cost production id effortMax rho c t)
  have hMcont : ContinuousOn M (Icc c 1) := (hgE.comp he.1 he.2).mul continuousOn_id
  have hRcont : ContinuousOn R (Icc c 1) := by
    apply hg.comp (continuousOn_const.sub he.1)
    intro t ht
    exact ⟨by linarith [(he.2 t ht).2], by linarith [(he.2 t ht).1]⟩
  have hMint : IntegrableOn M (Ioc c 1) volume := hMcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hRint : IntegrableOn R (Ioc c 1) volume := hRcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hM := independentSkillPopulation_conditional_utility μ hrho hc hMint
    (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] at hM
  have hR := independentSkillPopulation_conditional_utility μ hrho hc hRint hskill
  unfold sourceTwoLevelConditionalSchoolUtility
  rw [integral_add (hM.1.const_mul beta) (hR.1.const_mul (1 - beta)),
    integral_const_mul, integral_const_mul, hM.2, hR.2]
  rfl

/-- Increasing nonnegative skill has a finite positive mean under a uniform
rank law. Strict positivity need not be assumed at the lowest rank. -/
theorem unitRankMeasure_skill_integrable_and_mean_pos
    {skill : ℝ → ℝ} (hcont : ContinuousOn skill (Icc 0 1))
    (hmono : StrictMonoOn skill (Icc 0 1)) (hzero : 0 ≤ skill 0) :
    Integrable skill unitRankMeasure ∧ 0 < ∫ u, skill u ∂unitRankMeasure := by
  refine ⟨hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self, ?_⟩
  change 0 < ∫ u in Ioc (0 : ℝ) 1, skill u
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply intervalIntegral.integral_pos (by norm_num) hcont
  · intro u hu
    exact hzero.trans (hmono.monotoneOn ⟨le_rfl, by norm_num⟩ ⟨hu.1.le, hu.2⟩ hu.1.le)
  · exact ⟨1, ⟨by norm_num, le_rfl⟩,
      hzero.trans_lt (hmono ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num))⟩

/-- Primitive curvature conditions support each interior two-level policy in
the actual conditional school expectation. The independent population law is
fixed across all candidate policies, and the lottery realizes their common
capacity rather than supplying a policy-dependent skill distribution. -/
theorem sourceTwoLevelConditionalSchoolUtility_exists_optimal_weight_of_effortPrimitives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill : α → ℝ} (hskill : Integrable skill μ) (hmean : 0 < ∫ u, skill u ∂μ)
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget))
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a)))
    (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceTwoLevelConditionalSchoolUtility μ skill cost production budget effortMax rho beta d ≤
        sourceTwoLevelConditionalSchoolUtility μ skill cost production budget effortMax rho beta c := by
  obtain ⟨beta, hbeta, hopt⟩ := sourceTwoLevelWeightedUtility_exists_optimal_weight_of_effortPrimitives
    hrho hrho_one hmax hbudget hcost hcost_mono hcost_zero hcost_max hp' hp''
    hg hg_mono hg_zero hg_conc hg_sq hg' hg'' hg''_cont hcostRatio hmean hc
  refine ⟨beta, hbeta, ?_⟩
  intro d hd
  rw [sourceTwoLevelConditionalSchoolUtility_eq_weighted μ hskill hrho hrho_one hmax hbudget
      hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero hd,
    sourceTwoLevelConditionalSchoolUtility_eq_weighted μ hskill hrho hrho_one hmax hbudget
      hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero ⟨hc.1, hc.2.le⟩]
  exact hopt d hd

end LBG22StrategicRanking
