import LBG22StrategicRanking.FiniteUniquenessPrimitiveRepairs

/-!
# Population utility from the two-level effort primitives

Admitted scores are the maximum of the endogenous score threshold and
baseline production times skill. Normalizing the admitted ranks to a fixed
unit interval proves school-utility monotonicity without setting baseline
production to zero or differentiating a moving conditional expectation.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory

/-- The cutoff production is feasible and strictly increases with selectivity. -/
theorem sourceScoreScale_mem_and_strictMono
    {cost production : ℝ → ℝ} {E rho : ℝ}
    (hrho : 0 < rho) (hE : 0 ≤ E)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Icc 0 E))
    (hp0 : cost 0 = 0) (hpE : cost E = 1)
    (hgM : StrictMonoOn production (Icc 0 E)) :
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      sourceScoreScale cost production E rho c ∈ Ioc (production 0) (production E)) ∧
    StrictMonoOn (sourceScoreScale cost production E rho) (Ioc (0 : ℝ) (1 - rho)) := by
  have hq (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      rho / (1 - c) ∈ Ioc (cost 0) (cost E) := by
    have hd : 0 < 1 - c := by linarith [hc.2]
    rw [hp0, hpE]
    refine ⟨div_pos hrho hd, (div_le_one hd).mpr ?_⟩
    linarith [hc.2]
  have he (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    effortIntervalInverse_spec hE hp ⟨(hq c hc).1.le, (hq c hc).2⟩
  have hi := effortIntervalInverse_strictMonoOn hE hp hpM
  refine ⟨?_, ?_⟩
  · intro c hc
    have hpos : 0 < effortIntervalInverse cost E (rho / (1 - c)) := by
      apply (hpM.lt_iff_lt ⟨le_rfl, hE⟩ (he c hc).1).mp
      rw [(he c hc).2]
      exact (hq c hc).1
    exact ⟨hgM ⟨le_rfl, hE⟩ (he c hc).1 hpos,
      hgM.monotoneOn (he c hc).1 ⟨hE, le_rfl⟩ (he c hc).1.2⟩
  · intro a ha b hb hab
    apply hgM (he a ha).1 (he b hb).1
    apply hi ⟨(hq a ha).1.le, (hq a ha).2⟩ ⟨(hq b hb).1.le, (hq b hb).2⟩
    apply (div_lt_div_iff₀ (by linarith [ha.2] : 0 < 1 - a)
      (by linarith [hb.2] : 0 < 1 - b)).mpr
    nlinarith

/-- The admitted effort is feasible, continuous, and produces the actual
baseline-clipped score. Skill need only be positive above rank zero. -/
theorem sourceTwoLevelEffort_continuousOn_mem_and_score
    {cost production skill : ℝ → ℝ} {E rho c : ℝ}
    (hE : 0 ≤ E) (hg : ContinuousOn production (Icc 0 E))
    (hgM : StrictMonoOn production (Icc 0 E)) (hg0 : 0 ≤ production 0)
    (hf : ContinuousOn skill (Ioc (0 : ℝ) 1))
    (hfpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t)
    (hfM : MonotoneOn skill (Ioc (0 : ℝ) 1))
    (hc : c ∈ Ioc (0 : ℝ) 1)
    (ha : sourceScoreScale cost production E rho c ∈ Icc (production 0) (production E)) :
    ContinuousOn (sourceTwoLevelEffort cost production skill E rho c) (Icc c 1) ∧
    ∀ t ∈ Icc c 1,
      sourceTwoLevelEffort cost production skill E rho c t ∈ Icc (0 : ℝ) E ∧
      production (sourceTwoLevelEffort cost production skill E rho c t) * skill t =
        max (sourceScoreScale cost production E rho c * skill c) (production 0 * skill t) := by
  let a := sourceScoreScale cost production E rho c
  have hsub : Icc c 1 ⊆ Ioc (0 : ℝ) 1 := fun _ ht => ⟨hc.1.trans_le ht.1, ht.2⟩
  have htarget (t : ℝ) (ht : t ∈ Icc c 1) :
      a * (skill c / skill t) ≤ production E :=
    (mul_le_of_le_one_right (hg0.trans ha.1)
      ((div_le_one (hfpos t (hsub ht))).mpr (hfM hc (hsub ht) ht.1))).trans ha.2
  have hi (t : ℝ) (ht : t ∈ Icc c 1) := sourceEffortAtScore_spec hE hg hgM.monotoneOn (htarget t ht)
  have heq (t : ℝ) (ht : t ∈ Icc c 1) :
      sourceTwoLevelEffort cost production skill E rho c t =
        sourceEffortAtScore production E (a * (skill c / skill t)) := by
    exact max_eq_left (hi t ht).1.1
  have harg : ContinuousOn (fun t => a * (skill c / skill t)) (Icc c 1) :=
    continuousOn_const.mul (continuousOn_const.div (hf.mono hsub)
      (fun t ht => (hfpos t (hsub ht)).ne'))
  have hcont := (sourceEffortAtScore_continuousOn hE hg hgM).comp harg htarget
  refine ⟨hcont.congr heq, ?_⟩
  intro t ht
  rw [heq t ht]
  refine ⟨(hi t ht).1, ?_⟩
  rw [(hi t ht).2, max_mul_of_nonneg _ _ (hfpos t (hsub ht)).le]
  congr 1
  dsimp [a]
  field_simp [(hfpos t (hsub ht)).ne']

/-- A normalized upper-tail average is an integral over a fixed quantile law. -/
theorem admittedRankAverage_eq_normalized (F : ℝ → ℝ) {c : ℝ} (hc : c < 1) :
    (∫ t in c..1, F t) / (1 - c) =
      ∫ s in (0 : ℝ)..1, F (admittedTailRank c s) := by
  have h := intervalIntegral.smul_integral_comp_add_mul F (a := 0) (b := 1) (1 - c) c
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at h
  change (1 - c) * (∫ s in (0 : ℝ)..1, F (admittedTailRank c s)) = _ at h
  rw [← h, mul_div_cancel_left₀ _ (sub_pos.mpr hc).ne']

/-- The school's private utility is the conditional expected actual score
under the fixed population and its independent admission lottery. The last
population coordinate is immaterial for this measurable-score utility. -/
noncomputable def sourceTwoLevelConditionalScoreUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (cost production skill : ℝ → ℝ) (E rho c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α,
    production (sourceTwoLevelEffort cost production skill E rho c z.1.1) * skill z.1.1
    ∂ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)

/-- The actual conditional utility equals the average baseline-clipped score.
The normalization is derived from the admission event's positive mass. -/
theorem sourceTwoLevelConditionalScoreUtility_eq_normalized
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {E rho c : ℝ}
    (hrho : 0 < rho) (hE : 0 ≤ E)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Icc 0 E))
    (hp0 : cost 0 = 0) (hpE : cost E = 1)
    (hg : ContinuousOn production (Icc 0 E))
    (hgM : StrictMonoOn production (Icc 0 E)) (hg0 : 0 ≤ production 0)
    (hf : ContinuousOn skill (Ioc (0 : ℝ) 1))
    (hfpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t)
    (hfM : MonotoneOn skill (Ioc (0 : ℝ) 1))
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    sourceTwoLevelConditionalScoreUtility μ cost production skill E rho c =
      ∫ s in (0 : ℝ)..1,
        max (sourceScoreScale cost production E rho c * skill c)
          (production 0 * skill (admittedTailRank c s)) := by
  have hc1 : c < 1 := by linarith [hc.2]
  have ha := (sourceScoreScale_mem_and_strictMono hrho hE hp hpM hp0 hpE hgM).1 c hc
  have he := sourceTwoLevelEffort_continuousOn_mem_and_score hE hg hgM hg0 hf hfpos hfM
    ⟨hc.1, hc1.le⟩ ⟨ha.1.le, ha.2⟩
  let F := fun t => production (sourceTwoLevelEffort cost production skill E rho c t) * skill t
  have hF : ContinuousOn F (Icc c 1) :=
    (hg.comp he.1 (fun _ ht => (he.2 _ ht).1)).mul
      (hf.mono (fun _ ht => ⟨hc.1.trans_le ht.1, ht.2⟩))
  have hu := independentSkillPopulation_conditional_utility μ hrho hc
    (hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] at hu
  change (∫ z : (ℝ × ℝ) × α, F z.1.1 ∂ProbabilityTheory.cond
    (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)) = _
  rw [hu.2, admittedRankAverage_eq_normalized F hc1]
  apply intervalIntegral.integral_congr
  intro s hs
  exact (he.2 _ (admittedTailRank_mem_Icc ⟨hc.1.le, hc1.le⟩
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))).2

/-- Proposition 3.2: conditional school utility increases with the cutoff,
including when positive baseline production makes admitted scores unequal.
No derivative or extra cost/skill shape condition is needed. -/
theorem sourceTwoLevelConditionalScoreUtility_monotone
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill : ℝ → ℝ} {E rho : ℝ}
    (hrho : 0 < rho) (hE : 0 ≤ E)
    (hp : ContinuousOn cost (Icc 0 E)) (hpM : StrictMonoOn cost (Icc 0 E))
    (hp0 : cost 0 = 0) (hpE : cost E = 1)
    (hg : ContinuousOn production (Icc 0 E))
    (hgM : StrictMonoOn production (Icc 0 E)) (hg0 : 0 ≤ production 0)
    (hf : ContinuousOn skill (Ioc (0 : ℝ) 1))
    (hfpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < skill t)
    (hfM : MonotoneOn skill (Ioc (0 : ℝ) 1)) :
    MonotoneOn (sourceTwoLevelConditionalScoreUtility μ cost production skill E rho)
      (Ioc (0 : ℝ) (1 - rho)) := by
  have hscale := sourceScoreScale_mem_and_strictMono hrho hE hp hpM hp0 hpE hgM
  have htail (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      admittedTailRank c s ∈ Ioc (0 : ℝ) 1 := by
    have ht := admittedTailRank_mem_Icc ⟨hc.1.le, by linarith [hc.2]⟩ hs
    exact ⟨hc.1.trans_le ht.1, ht.2⟩
  have hcont (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      ContinuousOn (fun s => max (sourceScoreScale cost production E rho c * skill c)
        (production 0 * skill (admittedTailRank c s))) (Icc (0 : ℝ) 1) := by
    have ht : ContinuousOn (admittedTailRank c) (Icc (0 : ℝ) 1) := by
      unfold admittedTailRank
      fun_prop
    exact (continuousOn_const.sup (continuousOn_const.mul (hf.comp ht (htail c hc))))
  intro a ha b hb hab
  rw [sourceTwoLevelConditionalScoreUtility_eq_normalized μ hrho hE hp hpM hp0 hpE hg hgM hg0 hf hfpos hfM ha,
    sourceTwoLevelConditionalScoreUtility_eq_normalized μ hrho hE hp hpM hp0 hpE hg hgM hg0 hf hfpos hfM hb]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((hcont a ha).intervalIntegrable_of_Icc (by norm_num))
    ((hcont b hb).intervalIntegrable_of_Icc (by norm_num))
  intro s hs
  apply max_le_max
  · exact mul_le_mul (hscale.2.monotoneOn ha hb hab)
      (hfM ⟨ha.1, by linarith [ha.2]⟩ ⟨hb.1, by linarith [hb.2]⟩ hab)
      (hfpos a ⟨ha.1, by linarith [ha.2]⟩).le (hg0.trans (hscale.1 b hb).1.le)
  · apply mul_le_mul_of_nonneg_left (hfM (htail a ha s hs) (htail b hb s hs) ?_) hg0
    dsimp [admittedTailRank]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hs.2)]

/-- The two-level policy's three rank endpoints. -/
def sourceTwoLevelCutoff (c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then c else 1

/-- Rejected and admitted reward levels, with the prescribed capacity. -/
noncomputable def sourceTwoLevelReward (rho c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else rho / (1 - c)

theorem sourceTwoLevelCutoff_strictMono {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (sourceTwoLevelCutoff c) (Icc (0 : ℕ) 2) := by
  intro i hi j hj hij
  simp only [mem_Icc] at hi hj
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 1 ∨ j = 2 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · simpa only [sourceTwoLevelCutoff, if_pos, if_false, Nat.one_ne_zero] using hc.1
  · norm_num [sourceTwoLevelCutoff]
  · omega
  · simpa only [sourceTwoLevelCutoff, if_pos, if_false, Nat.one_ne_zero,
      show ¬ (2 : ℕ) = 0 by decide, show ¬ (2 : ℕ) = 1 by decide] using hc.2

theorem sourceTwoLevelReward_strictMono {rho c : ℝ} (hrho : 0 < rho) (hc : c < 1) :
    StrictMonoOn (sourceTwoLevelReward rho c) (Icc (0 : ℕ) 1) := by
  intro i hi j hj hij
  simp only [mem_Icc] at hi hj
  have hi0 : i = 0 := by omega
  have hj1 : j = 1 := by omega
  simpa only [hi0, hj1, sourceTwoLevelReward, if_pos, if_false, Nat.one_ne_zero]
    using div_pos hrho (sub_pos.mpr hc)

theorem finiteLowerRankBand_twoLevel {c t : ℝ} :
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) t).val =
      if c < t then 1 else 0 := by
  classical
  by_cases hct : c < t
  · have h := finiteLowerRankBand_eq_of_interval (i := (1 : Fin 2))
      (cutoff := fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (by simpa [sourceTwoLevelCutoff] using hct)
      (fun j hj => by have := j.isLt; change 1 < j.val at hj; omega)
    simp only [h, Fin.val_one, if_pos hct]
  · have h : finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) t ≤ 0 := by
      apply finiteLowerRankBand_le_of_upper
      intro j hj
      have hj1 : j.val = 1 := by have := j.isLt; change 0 < j.val at hj; omega
      simpa only [hj1, sourceTwoLevelCutoff, if_false, Nat.one_ne_zero, if_pos]
        using le_of_not_gt hct
    rw [le_antisymm h (Fin.zero_le _), if_neg hct]
    rfl

/-- For two bands, the recursive boundary is exactly the cutoff-indifference score. -/
theorem sourceRecursiveBandScore_twoLevel
    {cost production skill : ℝ → ℝ} {E rho c : ℝ}
    (hE : 0 ≤ E) (hp0 : cost 0 = 0)
    (hgM : StrictMonoOn production (Icc 0 E)) (hg0 : 0 ≤ production 0) :
    sourceRecursiveBandScore cost production E (fun k => skill (sourceTwoLevelCutoff c k))
      (sourceTwoLevelReward rho c) 1 = sourceScoreScale cost production E rho c * skill c := by
  simp only [sourceRecursiveBandScore, sourceTwoLevelCutoff, sourceTwoLevelReward,
    if_pos, if_false, Nat.one_ne_zero, sub_zero, sourceBoundaryStepScore,
    sourceBoundaryStepEffort, zero_div, sourceCostAtScore_zero hE hp0 hgM hg0, zero_add]
  rfl

/-- Admission is defined using the actual post-effort rank and an independent
lottery, with the lower reward at the exact rank cutoff. -/
def sourceActualTwoLevelAdmissionEvent {α : Type*}
    (score tie : ℝ → ℝ) (rho c : ℝ) : Set ((ℝ × ℝ) × α) :=
  {z | c < tieBrokenRank unitRankMeasure score tie z.1.1 ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))}

/-- Conditional score utility evaluated at the actual admission event. -/
noncomputable def sourceActualTwoLevelConditionalScoreUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (score tie : ℝ → ℝ) (rho c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α, score z.1.1
    ∂ProbabilityTheory.cond (independentSkillPopulation μ)
      (sourceActualTwoLevelAdmissionEvent score tie rho c)

private theorem independentSkillPopulation_ae_rank
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {P : ℝ → Prop} (hP : ∀ᵐ t ∂unitRankMeasure, P t) :
    ∀ᵐ z : (ℝ × ℝ) × α ∂independentSkillPopulation μ, P z.1.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := unitRankMeasure.prod unitRankMeasure) (ν := μ)).ae
    ((Measure.quasiMeasurePreserving_fst (μ := unitRankMeasure) (ν := unitRankMeasure)).ae hP)

/-- Reward-band preservation identifies the actual admission event with the
pre-rank tail lottery, up to a null set of the same fixed population. -/
theorem sourceActualTwoLevelAdmissionEvent_ae_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} {rho c : ℝ}
    (hband : (fun t => finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)) :
    sourceActualTwoLevelAdmissionEvent score tie rho c =ᵐ[independentSkillPopulation μ]
      twoLevelAdmissionEvent rho c := by
  have ht : ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [independentSkillPopulation_ae_rank μ hband,
    independentSkillPopulation_ae_rank μ ht] with z hz ht
  have hv := congrArg Fin.val hz
  simp only [finiteLowerRankBand_twoLevel] at hv
  have hi : c < tieBrokenRank unitRankMeasure score tie z.1.1 ↔ c < z.1.1 := by
    by_cases hpost : c < tieBrokenRank unitRankMeasure score tie z.1.1 <;>
      by_cases hpre : c < z.1.1 <;> simp [hpost, hpre] at hv ⊢
  apply propext
  change (c < tieBrokenRank unitRankMeasure score tie z.1.1 ∧
    z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))) ↔
    ((z.1.1 ∈ Ioc c 1 ∧ z.1.2 ∈ Ioc (0 : ℝ) (rho / (1 - c))) ∧ z.2 ∈ univ)
  simp only [hi, mem_Ioc, ht.2, and_true, mem_univ]

/-- Conditional score expectations can use the source effort formula once
actual admission bands and admitted scores have been identified almost everywhere. -/
theorem sourceActualTwoLevelConditionalScoreUtility_eq_of_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill score tie : ℝ → ℝ} {E rho c : ℝ}
    (hband : (fun t => finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i))
    (hscore : ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc c 1 →
      score t = production (sourceTwoLevelEffort cost production skill E rho c t) * skill t) :
    sourceActualTwoLevelConditionalScoreUtility μ score tie rho c =
      sourceTwoLevelConditionalScoreUtility μ cost production skill E rho c := by
  have hevent := sourceActualTwoLevelAdmissionEvent_ae_eq μ (rho := rho) hband
  have hcond : ProbabilityTheory.cond (independentSkillPopulation μ)
      (sourceActualTwoLevelAdmissionEvent score tie rho c) =
      ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c) := by
    unfold ProbabilityTheory.cond
    rw [measure_congr hevent, Measure.restrict_congr_set hevent]
  unfold sourceActualTwoLevelConditionalScoreUtility sourceTwoLevelConditionalScoreUtility
  rw [hcond]
  apply integral_congr_ae
  apply Measure.ae_smul_measure
  have hs := ae_restrict_of_ae (independentSkillPopulation_ae_rank μ hscore)
    (s := twoLevelAdmissionEvent rho c)
  have hm : MeasurableSet (twoLevelAdmissionEvent (α := α) rho c) :=
    (measurableSet_Ioc.prod measurableSet_Ioc).prod MeasurableSet.univ
  filter_upwards [hs, ae_restrict_mem hm] with z hz hmem
  exact hz hmem.1.1

/-- The actual post-rank admission event fills the prescribed capacity. -/
theorem sourceActualTwoLevelAdmissionEvent_mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hband : (fun t => finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)) :
    independentSkillPopulation μ (sourceActualTwoLevelAdmissionEvent score tie rho c) =
      ENNReal.ofReal rho := by
  rw [measure_congr (sourceActualTwoLevelAdmissionEvent_ae_eq μ (rho := rho) hband)]
  exact independentSkillPopulation_admission_mass μ hrho hc

/-- Every admissible two-level policy has an equilibrium against all
nonnegative deviations. This supplies a nonvacuous domain for the conditional
utility comparison at every cutoff, including deterministic admission. -/
theorem exists_sourceTwoLevelEquilibrium_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ effort score : ℝ → ℝ, AEMeasurable effort unitRankMeasure ∧ Measurable score ∧
      ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort t) := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hr1 : sourceTwoLevelReward rho c 1 ≤ 1 := by
    simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
    apply (div_le_one (sub_pos.mpr hc1)).mpr
    linarith [hc.2]
  obtain ⟨E, _, _, hm, hs, _, hb, _⟩ :=
    exists_unique_sourceFiniteBaselineEquilibrium_of_sourcePrimitives
      (baseline := 0) (n := 1) (cutoff := sourceTwoLevelCutoff c) (reward := sourceTwoLevelReward rho c)
      le_rfl hp hpC hpN hp0 hg hgM hgC hg0 (sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩)
      (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff])
      hfcont hf hf0 (sourceTwoLevelReward_strictMono hrho hc1)
      (by simp [sourceTwoLevelReward]) hr1 htie hinj
  exact ⟨_, _, hm, hs, hb⟩

/-- Every two-level equilibrium has the primitive conditional utility. This
derives both admitted score shape and the actual admission event from
incentives, rather than assuming either formula. -/
theorem sourceActualTwoLevelConditionalScoreUtility_eq_of_sourcePrimitives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill effort score tie : ℝ → ℝ} {E rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hE : 0 ≤ E) (hpE : cost E = 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort t)) :
    sourceActualTwoLevelConditionalScoreUtility μ score tie rho c =
      sourceTwoLevelConditionalScoreUtility μ cost production skill E rho c := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hcut := sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩
  have hrew := sourceTwoLevelReward_strictMono hrho hc1
  have hr0 : 0 ≤ sourceTwoLevelReward rho c 0 := by simp [sourceTwoLevelReward]
  have hr1 : sourceTwoLevelReward rho c 1 ≤ 1 := by
    simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
    apply (div_le_one (sub_pos.mpr hc1)).mpr
    linarith [hc.2]
  have hcut0 : sourceTwoLevelCutoff c 0 = 0 := by simp [sourceTwoLevelCutoff]
  have hcut2 : sourceTwoLevelCutoff c 2 = 1 := by norm_num [sourceTwoLevelCutoff]
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0
  have hpEc : ContinuousOn cost (Icc 0 E) := hp.mono Icc_subset_Ici_self
  have hpEm : StrictMonoOn cost (Icc 0 E) := hpm.mono Icc_subset_Ici_self
  have hgEc : ContinuousOn production (Icc 0 E) := hg.mono Icc_subset_Ici_self
  have hgEm : StrictMonoOn production (Icc 0 E) := hgM.mono Icc_subset_Ici_self
  have hfpos (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < skill t :=
    hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1)
  have hband := sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives
    (fun i : Fin 2 => sourceTwoLevelCutoff c i) (baseline := 0) le_rfl
    hp hpC hpN hp0 hg hgM hgC hg0 hf hf0 hrew hscore htie hinj hbest
  obtain ⟨F, hF, hpF, heffort⟩ := sourceFiniteEquilibrium_effort_unique_of_sourcePrimitives
    hp hpC hpN hp0 hg hgM hgC hg0 hcut hcut0 hcut2 hfcont hf hf0 hrew hr0 hr1 hscore htie hinj hbest
  have hFE : F = E := hpm.injOn hF.le hE (hpF.trans hpE.symm)
  rw [hFE] at heffort
  apply sourceActualTwoLevelConditionalScoreUtility_eq_of_ae μ hband
  filter_upwards [heffort, hbest] with t htE htB
  intro ht
  have ht0 : t ∈ Ioc (0 : ℝ) 1 := ⟨hc.1.trans ht.1, ht.2⟩
  have hcanonical := sourceFiniteRankEffort_score_and_incentives hE hpEc hpm hp0 hpE
    (hpC.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _)) hgEc hgEm hg0
    (hgC.subset Icc_subset_Ici_self (convex_Icc _ _)) hcut hcut0 hcut2 hf hf0 hrew hr0 hr1 ht0
  have ha := (sourceScoreScale_mem_and_strictMono hrho hE hpEc hpEm hp0 hpE hgEm).1 c hc
  have htwo := sourceTwoLevelEffort_continuousOn_mem_and_score hE hgEc hgEm hg0
    (hfcont.mono Ioc_subset_Icc_self) hfpos (hf.monotoneOn.mono Ioc_subset_Icc_self)
    ⟨hc.1, hc1.le⟩ ⟨ha.1.le, ha.2⟩
  calc
    score t = production (effort t) * skill t := htB.2.1
    _ = production (sourceFiniteRankEffort cost production skill E 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) t) * skill t := by rw [htE]
    _ = sourceFiniteRankScore cost production skill E 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) t := hcanonical.2.1.symm
    _ = max (sourceScoreScale cost production E rho c * skill c) (production 0 * skill t) := by
      unfold sourceFiniteRankScore
      rw [finiteLowerRankBand_twoLevel, if_pos ht.1,
        sourceRecursiveBandScore_twoLevel hE hp0 hgEm hg0, sourceClampedSkill_eq ⟨ht0.1.le, ht0.2⟩]
    _ = production (sourceTwoLevelEffort cost production skill E rho c t) * skill t :=
      (htwo.2 t ⟨ht.1.le, ht.2⟩).2.symm

/-- Proposition 3.2 for actual equilibria and actual rank-based admission:
every choice of equilibrium at each cutoff gives nondecreasing school utility,
with deterministic admission attaining the maximum. Positive baseline
production and arbitrary injective measurable tie orders are retained. -/
theorem sourceActualTwoLevelConditionalScoreUtility_monotone_of_sourcePrimitives
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {cost production skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ} {rho : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c))
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t)) :
    MonotoneOn (fun c => sourceActualTwoLevelConditionalScoreUtility μ (score c) tie rho c)
      (Ioc (0 : ℝ) (1 - rho)) ∧
    ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      sourceActualTwoLevelConditionalScoreUtility μ (score c) tie rho c ≤
        sourceActualTwoLevelConditionalScoreUtility μ (score (1 - rho)) tie rho (1 - rho) := by
  obtain ⟨E, hE, hpE, hpm⟩ := exists_unitCost_effort_of_sourcePrimitives hp hpC hpN hp0
  have heq (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceActualTwoLevelConditionalScoreUtility_eq_of_sourcePrimitives μ hrho hc hE.le hpE
      hp hpC hpN hp0 hg hgM hgC hg0 hfcont hf hf0 (hscore c hc) htie hinj (hbest c hc)
  have hmono := sourceTwoLevelConditionalScoreUtility_monotone μ hrho hE.le
    (hp.mono Icc_subset_Ici_self) (hpm.mono Icc_subset_Ici_self) hp0 hpE
    (hg.mono Icc_subset_Ici_self) (hgM.mono Icc_subset_Ici_self) hg0
    (hfcont.mono Ioc_subset_Icc_self)
    (fun t ht => hf0.trans_lt (hf ⟨le_rfl, by norm_num⟩ ⟨ht.1.le, ht.2⟩ ht.1))
    (hf.monotoneOn.mono Ioc_subset_Icc_self)
  have hactual : MonotoneOn
      (fun c => sourceActualTwoLevelConditionalScoreUtility μ (score c) tie rho c)
      (Ioc (0 : ℝ) (1 - rho)) := by
    intro a ha b hb hab
    dsimp only
    rw [heq a ha, heq b hb]
    exact hmono ha hb hab
  exact ⟨hactual, fun c hc => hactual hc ⟨sub_pos.mpr hrho1, le_rfl⟩ hc.2⟩

/-- The source model's unnormalized private utility: population expected
score weighted by the actual post-rank admission probability. -/
noncomputable def sourceActualTwoLevelSchoolUtility
    (score tie : ℝ → ℝ) (rho c : ℝ) : ℝ :=
  ∫ t, score t * sourceTwoLevelReward rho c
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (tieBrokenRank unitRankMeasure score tie t)).val ∂unitRankMeasure

/-- The source's private utility is capacity times the genuine conditional
mean. This proves the normalization bridge for the same score profile,
endogenous ranks, and admission lottery. -/
theorem sourceActualTwoLevelSchoolUtility_eq_scaled_conditional
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {score tie : ℝ → ℝ} {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (hband : (fun t => finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank unitRankMeasure score tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)) :
    sourceActualTwoLevelSchoolUtility score tie rho c =
      rho * sourceActualTwoLevelConditionalScoreUtility μ score tie rho c := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hden : 0 < 1 - c := sub_pos.mpr hc1
  have hq : 0 < rho / (1 - c) := div_pos hrho hden
  have hevent := sourceActualTwoLevelAdmissionEvent_ae_eq μ (rho := rho) hband
  have hmean : sourceActualTwoLevelConditionalScoreUtility μ score tie rho c =
      (∫ t in c..1, score t) / (1 - c) := by
    unfold sourceActualTwoLevelConditionalScoreUtility ProbabilityTheory.cond
    rw [measure_congr hevent, Measure.restrict_congr_set hevent,
      independentSkillPopulation_admission_mass μ hrho hc,
      independentSkillPopulation_restrict_admission μ hrho hc,
      integral_smul_measure, integral_fun_fst (fun p : ℝ × ℝ => score p.1), integral_fun_fst score]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hrho.le,
      smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hq.le,
      measure_univ, ENNReal.toReal_one, one_mul]
    rw [intervalIntegral.integral_of_le hc1.le]
    field_simp
  have ht : ∀ᵐ t ∂unitRankMeasure, t ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hweight : (fun t => score t * sourceTwoLevelReward rho c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank unitRankMeasure score tie t)).val) =ᵐ[unitRankMeasure]
      (Ioc c 1).indicator (fun t => (rho / (1 - c)) * score t) := by
    filter_upwards [hband, ht] with t hb ht
    rw [hb, finiteLowerRankBand_twoLevel]
    by_cases hct : c < t
    · rw [if_pos hct, indicator_of_mem (show t ∈ Ioc c 1 from ⟨hct, ht.2⟩)]
      simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
      ring
    · rw [if_neg hct, indicator_of_notMem (show t ∉ Ioc c 1 from fun h => hct h.1)]
      simp only [sourceTwoLevelReward, if_pos, mul_zero]
  unfold sourceActualTwoLevelSchoolUtility
  rw [integral_congr_ae hweight, integral_indicator measurableSet_Ioc]
  change (∫ t, (rho / (1 - c)) * score t
    ∂(volume.restrict (Ioc (0 : ℝ) 1)).restrict (Ioc c 1)) = _
  rw [Measure.restrict_restrict_of_subset (show Ioc c 1 ⊆ Ioc (0 : ℝ) 1 from
    fun _ ht => ⟨hc.1.trans ht.1, ht.2⟩), integral_const_mul,
    ← intervalIntegral.integral_of_le hc1.le, hmean]
  ring

/-- Proposition 3.2 in the source model's exact utility normalization:
population score weighted by endogenous admission probability increases
with selectivity and is maximized by deterministic admission. -/
theorem sourceActualTwoLevelSchoolUtility_monotone_of_sourcePrimitives
    {cost production skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ} {rho : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c))
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt cost production skill (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t)) :
    MonotoneOn (fun c => sourceActualTwoLevelSchoolUtility (score c) tie rho c)
      (Ioc (0 : ℝ) (1 - rho)) ∧
    ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      sourceActualTwoLevelSchoolUtility (score c) tie rho c ≤
        sourceActualTwoLevelSchoolUtility (score (1 - rho)) tie rho (1 - rho) := by
  have hconditional := sourceActualTwoLevelConditionalScoreUtility_monotone_of_sourcePrimitives
    unitRankMeasure hrho hrho1 hp hpC hpN hp0 hg hgM hgC hg0 hfcont hf hf0 htie hinj hscore hbest
  have heq (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      sourceActualTwoLevelSchoolUtility (score c) tie rho c =
        rho * sourceActualTwoLevelConditionalScoreUtility unitRankMeasure (score c) tie rho c := by
    apply sourceActualTwoLevelSchoolUtility_eq_scaled_conditional unitRankMeasure hrho hc
    exact sourceFiniteEquilibrium_rank_preservation_of_sourcePrimitives
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (baseline := 0) le_rfl
      hp hpC hpN hp0 hg hgM hgC hg0 hf hf0 (sourceTwoLevelReward_strictMono hrho (by linarith [hc.2]))
      (hscore c hc) htie hinj (hbest c hc)
  have hmono : MonotoneOn (fun c => sourceActualTwoLevelSchoolUtility (score c) tie rho c)
      (Ioc (0 : ℝ) (1 - rho)) := by
    intro a ha b hb hab
    dsimp only
    rw [heq a ha, heq b hb]
    exact mul_le_mul_of_nonneg_left (hconditional.1 ha hb hab) hrho.le
  exact ⟨hmono, fun c hc => hmono hc ⟨sub_pos.mpr hrho1, le_rfl⟩ hc.2⟩

end LBG22StrategicRanking
