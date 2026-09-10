import LBG22StrategicRanking.PopulationRankPrimitiveRepairs
import LBG22StrategicRanking.PopulationUtilityPrimitiveRepairs
import LBG22StrategicRanking.AffineSkillPrimitiveRepairs

/-!
# Hard-budget multitask equilibria

The measurable task determines admission; the other task receives residual
effort. The population may carry additional skill coordinates and any fixed
nonatomic tie key. All feasible two-task deviations are compared in the same
population, using its actual score-contour ranks.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

/-- The displayed multitask cost, evaluated on the hard-budget action space
specified in the source prose. The formula alone does not enforce that space. -/
def sourceMultitaskCost (cost : ℝ → ℝ) (B eM eU : ℝ) : ℝ :=
  cost eM - (max 0 (B - (eM + eU))) ^ 2

theorem sourceMultitaskCost_eq_of_budget {cost : ℝ → ℝ} {B eM eU : ℝ}
    (hbudget : eM + eU = B) : sourceMultitaskCost cost B eM eU = cost eM := by
  simp only [sourceMultitaskCost, hbudget, sub_self, max_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

/-- Best response against every nonnegative effort pair exhausting the fixed
budget. Admission depends only on measurable production and its actual rank. -/
def SourceHardBudgetBestResponseAt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (cost production : ℝ → ℝ) (skill score tie : α → ℝ)
    (B rho c : ℝ) (x : α) (eM eU : ℝ) : Prop :=
  0 ≤ eM ∧ 0 ≤ eU ∧ eM + eU = B ∧ score x = production eM * skill x ∧
    ∀ dM dU : ℝ, 0 ≤ dM → 0 ≤ dU → dM + dU = B →
      sourceTwoLevelReward rho c
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (counterfactualTieBrokenRank μ score tie x (production dM * skill x))).val -
            sourceMultitaskCost cost B dM dU ≤
      sourceTwoLevelReward rho c
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (tieBrokenRank μ score tie x)).val - sourceMultitaskCost cost B eM eU

/-- A feasible scalar best response remains optimal when every unit not used
on the measurable task is assigned to the unmeasurable task. -/
theorem sourceHardBudgetBestResponseAt_of_scalar
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ} {B rho c e : ℝ} {x : α}
    (he : e ≤ B)
    (hbest : SourcePopulationFiniteBestResponseAt μ cost production skill score tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x e) :
    SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c x e (B - e) := by
  have hbudget : e + (B - e) = B := by ring
  refine ⟨hbest.1, sub_nonneg.mpr he, hbudget, hbest.2.1, ?_⟩
  intro dM dU hdM _hdU hd
  rw [sourceMultitaskCost_eq_of_budget hd, sourceMultitaskCost_eq_of_budget hbudget]
  exact hbest.2.2 dM hdM

/-- A hard-budget best response also solves the scalar game when efforts
beyond the budget cost at least the largest possible admission reward.
The feasible zero-effort action guarantees nonnegative current utility;
therefore no omitted scalar deviation can be profitable. -/
theorem sourceScalarBestResponseAt_of_hardBudget
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ} {B rho c eM eU : ℝ} {x : α}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 ≤ B)
    (hpM : MonotoneOn cost (Ici 0)) (hp0 : cost 0 = 0) (hpB : 1 ≤ cost B)
    (hbest : SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c x eM eU) :
    SourcePopulationFiniteBestResponseAt μ cost production skill score tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x eM := by
  let R := fun r => sourceTwoLevelReward rho c
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val
  have hc1 : c < 1 := by linarith [hc.2]
  have hq : rho / (1 - c) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hrho (sub_pos.mpr hc1)).le, (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])⟩
  have hR (r : ℝ) : R r ∈ Icc (0 : ℝ) 1 := by
    dsimp only [R]
    rw [finiteLowerRankBand_twoLevel]
    split_ifs <;> simp only [sourceTwoLevelReward, ↓reduceIte, Nat.one_ne_zero]
    · exact hq
    · exact ⟨le_rfl, zero_le_one⟩
  have hbudget := hbest.2.2.1
  have hzero := hbest.2.2.2.2 0 B le_rfl hB (zero_add B)
  rw [sourceMultitaskCost_eq_of_budget (zero_add B), sourceMultitaskCost_eq_of_budget hbudget, hp0,
    sub_zero] at hzero
  have hown : 0 ≤ R (tieBrokenRank μ score tie x) - cost eM :=
    (hR _).1.trans hzero
  refine ⟨hbest.1, hbest.2.2.2.1, ?_⟩
  intro d hd
  by_cases hdB : d ≤ B
  · have h := hbest.2.2.2.2 d (B - d) hd (sub_nonneg.mpr hdB) (by ring)
    rw [sourceMultitaskCost_eq_of_budget (show d + (B - d) = B by ring),
      sourceMultitaskCost_eq_of_budget hbudget] at h
    exact h
  · have hcost : 1 ≤ cost d := hpB.trans (hpM hB hd (le_of_not_ge hdB))
    change R (counterfactualTieBrokenRank μ score tie x (production d * skill x)) - cost d ≤
      R (tieBrokenRank μ score tie x) - cost eM
    exact (sub_nonpos.mpr ((hR _).2.trans hcost)).trans hown

/-- On feasible effort pairs, the hard-budget and scalar best-response
conditions are equivalent. This applies to arbitrary equilibrium profiles,
not only the canonical construction. -/
theorem sourceHardBudgetBestResponseAt_iff_scalar
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {cost production : ℝ → ℝ} {skill score tie : α → ℝ} {B rho c eM eU : ℝ} {x : α}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hB : 0 ≤ B)
    (hpM : MonotoneOn cost (Ici 0)) (hp0 : cost 0 = 0) (hpB : 1 ≤ cost B) :
    SourceHardBudgetBestResponseAt μ cost production skill score tie B rho c x eM eU ↔
      eM ≤ B ∧ eU = B - eM ∧
        SourcePopulationFiniteBestResponseAt μ cost production skill score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) x eM := by
  constructor
  · intro h
    exact ⟨by linarith [h.2.1, h.2.2.1], by linarith [h.2.2.1],
      sourceScalarBestResponseAt_of_hardBudget μ hrho hc hB hpM hp0 hpB h⟩
  · rintro ⟨he, rfl, h⟩
    exact sourceHardBudgetBestResponseAt_of_scalar μ he h

/-- The source two-band profile is an actual equilibrium on any population
whose measurable-task rank is uniform. No alignment with the tie key, and no
independence of that key from either skill coordinate, is assumed. -/
theorem sourcePopulationTwoLevelEquilibrium_of_uniform_preRank
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {preRank tie : α → ℝ} {E rho c : ℝ}
    (hR : Measurable preRank) (hRlaw : Measure.map preRank μ = unitRankMeasure)
    (htie : Measurable tie) [NoAtoms (Measure.map tie μ)]
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hE : 0 ≤ E)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Ici 0))
    (hp0 : cost 0 = 0) (hpE : cost E = 1) (hpC : ConvexOn ℝ (Icc 0 E) cost)
    (hg : ContinuousOn production (Icc 0 E)) (hgM : StrictMonoOn production (Icc 0 E))
    (hg0 : 0 ≤ production 0) (hgC : ConcaveOn ℝ (Icc 0 E) production)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0) :
    let effort := fun x => sourceFiniteRankEffort cost production skill E 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (preRank x)
    let score := fun x => sourceFiniteRankScore cost production skill E 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (preRank x)
    Measurable score ∧ ∀ᵐ x ∂μ, effort x ∈ Icc (0 : ℝ) E ∧
      SourcePopulationFiniteBestResponseAt μ cost production (fun x => skill (preRank x))
        score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c)
        x (effort x) ∧ (c < tieBrokenRank μ score tie x ↔ c < preRank x) := by
  let effort := fun x => sourceFiniteRankEffort cost production skill E 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (preRank x)
  let score := fun x => sourceFiniteRankScore cost production skill E 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (preRank x)
  let targets := fun i : Fin 2 => sourceRecursiveBandScore cost production E
    (fun k => skill (sourceTwoLevelCutoff c k)) (sourceTwoLevelReward rho c) i
  let T := sourceScoreScale cost production E rho c * skill c
  have hc1 : c < 1 := by linarith [hc.2]
  have hcut := sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩
  have hrew := sourceTwoLevelReward_strictMono hrho hc1
  have hr0 : 0 ≤ sourceTwoLevelReward rho c 0 := by simp only [sourceTwoLevelReward, if_pos, le_refl]
  have hr1 : sourceTwoLevelReward rho c 1 ≤ 1 := by
    simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
    apply (div_le_one (sub_pos.mpr hc1)).mpr
    linarith [hc.2]
  have hcut0 : sourceTwoLevelCutoff c 0 = 0 := by simp only [sourceTwoLevelCutoff, if_pos]
  have hcut2 : sourceTwoLevelCutoff c 2 = 1 := by norm_num [sourceTwoLevelCutoff]
  have hcanonical (x : α) (hx : preRank x ∈ Ioc (0 : ℝ) 1) :=
    sourceFiniteRankEffort_score_and_incentives hE hp hpM hp0 hpE hpC hg hgM hg0 hgC
      hcut hcut0 hcut2 hf hf0 hrew hr0 hr1 hx
  have hs : Measurable score := (measurable_sourceFiniteRankScore hfcont).comp hR
  have hmem : ∀ᵐ x ∂μ, preRank x ∈ Ioc (0 : ℝ) 1 := by
    apply (ae_map_iff hR.aemeasurable measurableSet_Ioc).mp
    rw [hRlaw]
    exact ae_restrict_mem measurableSet_Ioc
  have hmass : μ.real {x | preRank x ≤ c} = c := by
    have h := congrArg (fun ν : Measure ℝ => (ν (Iic c)).toReal) hRlaw
    dsimp only at h
    rw [Measure.map_apply hR measurableSet_Iic] at h
    exact h.trans (unitRankMeasure_Iic ⟨hc.1.le, hc1.le⟩)
  have hfc : 0 < skill c := hf0.trans_lt
    (hf ⟨le_rfl, by norm_num⟩ ⟨hc.1.le, hc1.le⟩ hc.1)
  have ha := (sourceScoreScale_mem_and_strictMono hrho hE hp
    (hpM.mono Icc_subset_Ici_self) hp0 hpE hgM).1 c hc
  have hT : production 0 * skill c < T := mul_lt_mul_of_pos_right ha.1 hfc
  have ht1 : targets 1 = T := sourceRecursiveBandScore_twoLevel hE hp0 hgM hg0
  have hprofile : ∀ᵐ x ∂μ,
      (preRank x ≤ c → score x ≤ production 0 * skill c) ∧
      (c < preRank x → T ≤ score x) := by
    filter_upwards [hmem] with x hx
    have hsx : score x = max
        (if c < preRank x then T else 0) (production 0 * skill (preRank x)) := by
      change max (targets (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) (preRank x)))
        (production 0 * sourceClampedSkill skill (preRank x)) = _
      rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩]
      change max (sourceRecursiveBandScore cost production E
        (fun k => skill (sourceTwoLevelCutoff c k)) (sourceTwoLevelReward rho c)
          (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) (preRank x)).val) _ = _
      rw [finiteLowerRankBand_twoLevel]
      split_ifs with h
      · rw [sourceRecursiveBandScore_twoLevel hE hp0 hgM hg0]
      · rfl
    constructor
    · intro hlow
      rw [hsx, if_neg (not_lt_of_ge hlow)]
      exact max_le (mul_nonneg hg0 hfc.le)
        (mul_le_mul_of_nonneg_left (hf.monotoneOn ⟨hx.1.le, hx.2⟩ ⟨hc.1.le, hc1.le⟩ hlow) hg0)
    · intro hhigh
      rw [hsx, if_pos hhigh]
      exact le_max_left _ _
  have hrank := sourcePopulation_twoLevelRank_of_score_separation μ hs htie hmass hT hprofile
  have hcounter (x : α) (v : ℝ) :
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (counterfactualTieBrokenRank μ score tie x v) ≤ finiteScoreBand targets v := by
    change (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (counterfactualTieBrokenRank μ score tie x v)).val ≤ (finiteScoreBand targets v).val
    rw [finiteLowerRankBand_twoLevel]
    split_ifs with hpost
    · have hv : T ≤ v := by
        by_contra hn
        exact (not_le_of_gt hpost) (hrank.1 x v (lt_of_not_ge hn))
      have h := le_finiteScoreBand_of_target_le (target := targets) (i := (1 : Fin 2)) (ht1.trans_le hv)
      exact h
    · exact Nat.zero_le _
  refine ⟨hs, ?_⟩
  filter_upwards [hmem, hrank.2] with x hx hband
  have he := hcanonical x hx
  refine ⟨he.1, ⟨he.1.1, he.2.1, ?_⟩, hband⟩
  intro d hd
  have hbd := hcounter x (production d * skill (preRank x))
  have hreward := hrew.monotoneOn
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteLowerRankBand
      (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (counterfactualTieBrokenRank μ score tie x (production d * skill (preRank x)))).isLt⟩
    ⟨Nat.zero_le _, Nat.le_of_lt_succ (finiteScoreBand targets (production d * skill (preRank x))).isLt⟩ hbd
  have hown : (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (tieBrokenRank μ score tie x)).val =
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) (preRank x)).val := by
    simp only [finiteLowerRankBand_twoLevel, hband]
  rw [hown]
  exact (sub_le_sub_right hreward (cost d)).trans (he.2.2.2 d hd)

/-- Injectivity need only hold on the realized applicant population. -/
theorem noAtoms_map_tie_of_injOn_fullMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    {tie : α → ℝ} {S : Set α} (htie : Measurable tie) (hinj : InjOn tie S)
    (hS : ∀ᵐ x ∂μ, x ∈ S) : NoAtoms (Measure.map tie μ) := by
  constructor
  intro r
  rw [Measure.map_apply htie (measurableSet_singleton r)]
  have heq : tie ⁻¹' {r} =ᵐ[μ] (tie ⁻¹' {r} ∩ S : Set α) := by
    filter_upwards [hS] with x hx
    apply propext
    change (tie x = r) ↔ (tie x = r ∧ x ∈ S)
    simp only [hx, and_true]
  rw [measure_congr heq]
  have hsub : (tie ⁻¹' {r} ∩ S).Subsingleton := by
    intro x hx y hy
    exact hinj hx.2 hy.2 (hx.1.trans hy.1.symm)
  exact hsub.measure_zero μ

/-- The independent lottery augments the applicant law without changing its
joint measurable-rank and unmeasurable-skill distribution. -/
theorem independentSkillPopulation_applicant_measurePreserving
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : (ℝ × ℝ) × α => (z.1.1, z.2))
      (independentSkillPopulation μ) (unitRankMeasure.prod μ) :=
  (measurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).prod
    (MeasurePreserving.id μ)

/-- Admission in the full two-skill population, followed by an independent
admission lottery. The tie key belongs to the applicant, not the lottery. -/
def sourceMultitaskAdmissionEvent
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (score tie : ℝ × α → ℝ) (rho c : ℝ) : Set ((ℝ × ℝ) × α) :=
  {z | c < tieBrokenRank (unitRankMeasure.prod μ) score tie (z.1.1, z.2) ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))}

/-- School utility conditional on admission, using actual effort choices and
the joint-population ranking rule. -/
noncomputable def sourceActualMultitaskSchoolUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (production skillM : ℝ → ℝ) (skillU : α → ℝ)
    (effortM effortU score tie : ℝ × α → ℝ) (rho beta c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α,
    beta * (production (effortM (z.1.1, z.2)) * skillM z.1.1) +
      (1 - beta) * (production (effortU (z.1.1, z.2)) * skillU z.2)
    ∂ProbabilityTheory.cond (independentSkillPopulation μ)
      (sourceMultitaskAdmissionEvent μ score tie rho c)

theorem sourceMultitaskAdmissionEvent_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ × α → ℝ} {rho c : ℝ}
    (hband : ∀ᵐ x ∂unitRankMeasure.prod μ,
      c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1) :
    sourceMultitaskAdmissionEvent μ score tie rho c =ᵐ[independentSkillPopulation μ]
      twoLevelAdmissionEvent rho c := by
  have hmem : ∀ᵐ x : ℝ × α ∂unitRankMeasure.prod μ, x.1 ∈ Ioc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := unitRankMeasure) (ν := μ)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hproj := (independentSkillPopulation_applicant_measurePreserving μ).quasiMeasurePreserving
  filter_upwards [hproj.ae hband, hproj.ae hmem] with z hz ht
  apply propext
  change (c < tieBrokenRank (unitRankMeasure.prod μ) score tie (z.1.1, z.2) ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))) ↔
    ((z.1.1 ∈ Ioc c 1 ∧ z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))) ∧ z.2 ∈ univ)
  simp only [hz, mem_Ioc, ht.2, and_true, mem_univ]

theorem sourceActualMultitaskSchoolUtility_eq_of_profile
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skillM : ℝ → ℝ} {skillU : α → ℝ}
    {effortM effortU score tie : ℝ × α → ℝ} {B E rho beta c : ℝ}
    (hband : ∀ᵐ x ∂unitRankMeasure.prod μ,
      c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1)
    (heffort : ∀ᵐ x ∂unitRankMeasure.prod μ, x.1 ∈ Ioc c 1 →
      effortM x = sourceTwoLevelEffort cost production skillM E rho c x.1 ∧
        effortU x = B - sourceTwoLevelEffort cost production skillM E rho c x.1) :
    sourceActualMultitaskSchoolUtility μ production skillM skillU effortM effortU score tie rho beta c =
      sourceSkillConditionalSchoolUtility μ skillU cost production skillM B E rho beta c := by
  have hevent := sourceMultitaskAdmissionEvent_ae_eq μ (rho := rho) hband
  have hcond : ProbabilityTheory.cond (independentSkillPopulation μ)
      (sourceMultitaskAdmissionEvent μ score tie rho c) =
      ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c) := by
    unfold ProbabilityTheory.cond
    rw [measure_congr hevent, Measure.restrict_congr_set hevent]
  unfold sourceActualMultitaskSchoolUtility sourceSkillConditionalSchoolUtility
  rw [hcond]
  apply integral_congr_ae
  apply Measure.ae_smul_measure
  have hproj := (independentSkillPopulation_applicant_measurePreserving μ).quasiMeasurePreserving
  filter_upwards [ae_restrict_of_ae (hproj.ae heffort),
    ae_restrict_mem (twoLevelAdmissionEvent_measurable (α := α) rho c)] with z hz ht
  have h := hz ht.1.1
  rw [h.1, h.2]

/-- The unit-cost cap is feasible whenever exhausting the budget costs at
least the maximal possible admission reward. -/
theorem sourceUnitCostCap_le_budget {cost : ℝ → ℝ} {E B : ℝ}
    (hpM : StrictMonoOn cost (Ici 0)) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hpE : cost E = 1) (hpB : 1 ≤ cost B) : E ≤ B := by
  by_contra hn
  have h := hpM hB hE (lt_of_not_ge hn)
  rw [hpE] at h
  exact (not_lt_of_ge hpB) h

/-- Strictly increasing technology recovers measurable effort from the
observed score and positive skill on any applicant probability space. -/
theorem aemeasurable_population_effort_of_measurable_score
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {production : ℝ → ℝ} {skill effort score : α → ℝ} {E : ℝ}
    (hE : 0 ≤ E) (hg : ContinuousOn production (Icc 0 E))
    (hgM : StrictMonoOn production (Icc 0 E))
    (hskill : Measurable skill) (hscore : Measurable score)
    (hprofile : ∀ᵐ x ∂μ, 0 < skill x ∧ effort x ∈ Icc (0 : ℝ) E ∧
      score x = production (effort x) * skill x) : AEMeasurable effort μ := by
  let inv := fun z => effortIntervalInverse production E
    (max (production 0) (min z (production E)))
  have hinv : Continuous inv := by
    apply (effortIntervalInverse_continuousOn hE hg hgM).comp_continuous
      (continuous_const.max (continuous_id.min continuous_const))
    intro z
    exact ⟨le_max_left _ _, max_le (hgM.monotoneOn ⟨le_rfl, hE⟩ ⟨hE, le_rfl⟩ hE)
      (min_le_right _ _)⟩
  apply (hinv.measurable.comp (hscore.div hskill)).aemeasurable.congr
  filter_upwards [hprofile] with x hx
  change inv (score x / skill x) = effort x
  rw [hx.2.2, mul_div_cancel_right₀ _ hx.1.ne']
  change effortIntervalInverse production E
    (max (production 0) (min (production (effort x)) (production E))) = effort x
  rw [min_eq_left (hgM.monotoneOn hx.2.1 ⟨hE, le_rfl⟩ hx.2.1.2),
    max_eq_right (hgM.monotoneOn ⟨le_rfl, hE⟩ hx.2.1 hx.2.1.1)]
  exact hgM.injOn.leftInvOn_invFunOn hx.2.1

/-- The hard-budget game realizes the scalar effort formulas, the prescribed
admission capacity, and the conditional school utility in one fixed joint
population. Budget feasibility is stated on cost, not as an assumed bound
on an unproved equilibrium profile. -/
theorem sourceHardBudgetEquilibrium_and_utility_of_sourcePrimitives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skillM : ℝ → ℝ} {tie : ℝ × α → ℝ} {B E rho c : ℝ}
    (htie : Measurable tie) (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1})
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Ici 0))
    (hp0 : cost 0 = 0) (hpE : cost E = 1) (hpB : 1 ≤ cost B)
    (hpC : ConvexOn ℝ (Icc 0 E) cost)
    (hg : ContinuousOn production (Icc 0 E)) (hgM : StrictMonoOn production (Icc 0 E))
    (hg0 : 0 ≤ production 0) (hgC : ConcaveOn ℝ (Icc 0 E) production)
    (hfcont : ContinuousOn skillM (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skillM (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skillM 0) :
    let effortM := fun x : ℝ × α => sourceFiniteRankEffort cost production skillM E 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) x.1
    let effortU := fun x => B - effortM x
    let score := fun x : ℝ × α => sourceFiniteRankScore cost production skillM E 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) x.1
    (Measurable score ∧ AEMeasurable effortM (unitRankMeasure.prod μ) ∧
      AEMeasurable effortU (unitRankMeasure.prod μ)) ∧
      (∀ᵐ x ∂unitRankMeasure.prod μ,
        SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
          (fun x => skillM x.1) score tie B rho c x (effortM x) (effortU x)) ∧
      independentSkillPopulation μ (sourceMultitaskAdmissionEvent μ score tie rho c) = ENNReal.ofReal rho ∧
      ∀ (skillU : α → ℝ) (beta : ℝ),
        sourceActualMultitaskSchoolUtility μ production skillM skillU effortM effortU score tie rho beta c =
          sourceSkillConditionalSchoolUtility μ skillU cost production skillM B E rho beta c := by
  let effortM := fun x : ℝ × α => sourceFiniteRankEffort cost production skillM E 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) x.1
  let effortU := fun x => B - effortM x
  let score := fun x : ℝ × α => sourceFiniteRankScore cost production skillM E 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) x.1
  have hmem : ∀ᵐ x : ℝ × α ∂unitRankMeasure.prod μ, x.1 ∈ Ioc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := unitRankMeasure) (ν := μ)).ae
      (ae_restrict_mem measurableSet_Ioc)
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  haveI := noAtoms_map_tie_of_injOn_fullMeasure htie hinj hmem
  have hscalar := sourcePopulationTwoLevelEquilibrium_of_uniform_preRank (unitRankMeasure.prod μ)
    measurable_fst measurePreserving_fst.map_eq htie hrho hc hE hp hpM hp0 hpE hpC hg hgM hg0 hgC
    hfcont hf hf0
  have hcap := sourceUnitCostCap_le_budget hpM hE hB hpE hpB
  have hband : ∀ᵐ x ∂unitRankMeasure.prod μ,
      c < tieBrokenRank (unitRankMeasure.prod μ) score tie x ↔ c < x.1 :=
    hscalar.2.mono (fun _ hx => hx.2.2)
  have heMeas : AEMeasurable effortM (unitRankMeasure.prod μ) := by
    apply aemeasurable_population_effort_of_measurable_score (unitRankMeasure.prod μ)
      hE hg hgM ((continuous_sourceClampedSkill hfcont).measurable.comp measurable_fst) hscalar.1
    filter_upwards [hmem, hscalar.2] with x hx he
    simp only [Function.comp_apply]
    rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩]
    exact ⟨hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1), he.1, he.2.1.2.1⟩
  refine ⟨⟨hscalar.1, heMeas, aemeasurable_const.sub heMeas⟩, ?_, ?_, ?_⟩
  · filter_upwards [hscalar.2] with x hx
    exact sourceHardBudgetBestResponseAt_of_scalar (unitRankMeasure.prod μ)
      (hx.1.2.trans hcap) hx.2.1
  · rw [measure_congr (sourceMultitaskAdmissionEvent_ae_eq μ (rho := rho) hband)]
    exact independentSkillPopulation_admission_mass μ hrho hc
  · intro skillU beta
    apply sourceActualMultitaskSchoolUtility_eq_of_profile μ hband
    filter_upwards [hscalar.2] with x hx
    intro ht
    have heq : effortM x = sourceEffortAtScore production E
        (sourceScoreScale cost production E rho c * (skillM c / skillM x.1)) := by
      dsimp only [effortM, sourceFiniteRankEffort]
      rw [sourceClampedSkill_eq ⟨(hc.1.trans ht.1).le, ht.2⟩,
        finiteLowerRankBand_twoLevel, if_pos ht.1,
        sourceRecursiveBandScore_twoLevel hE hp0 hgM hg0]
      congr 1
      ring
    have hformula : sourceTwoLevelEffort cost production skillM E rho c x.1 = effortM x := by
      change max (sourceEffortAtScore production E
        (sourceScoreScale cost production E rho c * (skillM c / skillM x.1))) 0 = effortM x
      rw [← heq, max_eq_left hx.1.1]
    exact ⟨hformula.symm, congrArg (fun e => B - e) hformula.symm⟩

/-- Under the affine-skill primitive shape conditions, every interior cutoff
is optimal for some strictly positive weight on each task, among the actual
hard-budget equilibria at all feasible two-level policies. The population,
tie rule, budget, cost, and production are fixed throughout the comparison.
The affine distribution and curvature conditions are local sufficient
conditions for supportability, not assumptions of the general equilibrium
construction. -/
theorem sourceHardBudgetEquilibria_support_all_interior_cutoffs_of_affineSkill
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skillU : α → ℝ} (hskillU : Integrable skillU μ) (hmean : 0 < ∫ u, skillU u ∂μ)
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {tie : ℝ × α → ℝ} {B E rho lowerSkill skillWidth : ℝ}
    (htie : Measurable tie) (hinj : InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1})
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hE : 0 < E) (hB : 0 ≤ B)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Ici 0))
    (hp0 : cost 0 = 0) (hpE : cost E = 1) (hpB : 1 ≤ cost B)
    (hpC : ConvexOn ℝ (Icc 0 E) cost)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) E, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) E, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 B)) (hgM : StrictMonoOn production (Icc 0 B))
    (hg0 : production 0 = 0) (hgC : ConcaveOn ℝ (Icc 0 B) production)
    (hgSq : ConcaveOn ℝ (Ioo 0 B) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) B, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) B, HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''cont : ContinuousOn productionSecondDeriv (Ioo 0 B))
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost E rho)) (production E))
      (fun a => a / cost (effortIntervalInverse production E a))) :
    let skillM := fun t => lowerSkill + skillWidth * t
    let effortM := fun d (x : ℝ × α) => sourceFiniteRankEffort cost production skillM E 1
      (sourceTwoLevelCutoff d) (sourceTwoLevelReward rho d) x.1
    let effortU := fun d x => B - effortM d x
    let score := fun d (x : ℝ × α) => sourceFiniteRankScore cost production skillM E 1
      (sourceTwoLevelCutoff d) (sourceTwoLevelReward rho d) x.1
    (∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      (Measurable (score d) ∧ AEMeasurable (effortM d) (unitRankMeasure.prod μ) ∧
        AEMeasurable (effortU d) (unitRankMeasure.prod μ)) ∧
      (∀ᵐ x ∂unitRankMeasure.prod μ,
        SourceHardBudgetBestResponseAt (unitRankMeasure.prod μ) cost production
          (fun x => skillM x.1) (score d) tie B rho d x (effortM d x) (effortU d x)) ∧
      independentSkillPopulation μ (sourceMultitaskAdmissionEvent μ (score d) tie rho d) = ENNReal.ofReal rho) ∧
    ∀ c ∈ Ioo (0 : ℝ) (1 - rho), ∃ beta ∈ Ioo (0 : ℝ) 1,
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
  have hcap := sourceUnitCostCap_le_budget hpM hE.le hB hpE hpB
  have hsub : Icc (0 : ℝ) E ⊆ Icc 0 B := Icc_subset_Icc_right hcap
  have hfamily (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceHardBudgetEquilibrium_and_utility_of_sourcePrimitives μ htie hinj hrho hd hE.le hB
      hp hpM hp0 hpE hpB hpC (hg.mono hsub) (hgM.mono hsub) hg0.ge
      (hgC.subset hsub (convex_Icc _ _)) hfcont hf hf0
  constructor
  · intro d hd
    exact ⟨(hfamily d hd).1, (hfamily d hd).2.1, (hfamily d hd).2.2.1⟩
  · intro c hc
    obtain ⟨beta, hbeta, hopt⟩ := sourceSkillConditionalSchoolUtility_exists_optimal_weight_of_affineSkill
      μ hskillU hmean hrho hrho1 hlower hwidth hE hcap hp (hpM.mono Icc_subset_Ici_self)
      hp0 hpE hp' hp'' hg hgM hg0 (hgC.subset Ioo_subset_Icc_self (convex_Ioo _ _))
      hgSq hg' hg'' hg''cont hcostRatio hc
    refine ⟨beta, hbeta, ?_⟩
    intro d hd
    rw [(hfamily d hd).2.2.2 skillU beta, (hfamily c ⟨hc.1, hc.2.le⟩).2.2.2 skillU beta]
    exact hopt d hd

end LBG22StrategicRanking
