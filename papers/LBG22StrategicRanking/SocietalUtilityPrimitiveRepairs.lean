import LBG22StrategicRanking.ApplicantWelfarePrimitiveRepairs
import LBG22StrategicRanking.ThreeLevelPrimitiveRepairs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Societal utility and an interior optimum

Societal utility is the population mean of all post-effort scores. For
square-root production, quadratic cost, and uniform skill, its fourth power
is proportional to `c^4 * (1-c)^3`. The maximum is at `4/7`, and is interior
to the capacity-constrained policy interval precisely when capacity is less
than `3/7`.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Society values the scores of all applicants, regardless of admission. -/
noncomputable def sourceSocietalUtility (score : ℝ → ℝ) : ℝ :=
  ∫ t, score t ∂unitRankMeasure

/-- Zero baseline production makes the canonical score constant on each
pre-rank band. Actual population integration supplies the band widths. -/
theorem sourceFiniteSocietalUtility_eq_sum_of_zero_baseline
    {cost production skill : ℝ → ℝ} {E : ℝ} {n : ℕ} {cutoff reward : ℕ → ℝ}
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0)
    (hcn : cutoff (n + 1) = 1) (hg0 : production 0 = 0) :
    Integrable (sourceFiniteRankScore cost production skill E n cutoff reward) unitRankMeasure ∧
    sourceSocietalUtility (sourceFiniteRankScore cost production skill E n cutoff reward) =
      ∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) *
        max (sourceRecursiveBandScore cost production E (fun k => skill (cutoff k)) reward i.val) 0 := by
  have h := integral_finiteLowerRankBand (fun i : Fin (n + 1) =>
    max (sourceRecursiveBandScore cost production E (fun k => skill (cutoff k)) reward i.val) 0) hc hc0 hcn
  change Integrable (fun t => sourceFiniteRankScore cost production skill E n cutoff reward t) unitRankMeasure ∧ _
  simpa only [sourceFiniteRankScore, sourceSocietalUtility, hg0, zero_mul] using h

/-- Every actual equilibrium has the canonical score profile almost
everywhere. The result derives the score identity from effort uniqueness,
rather than assuming a formula for the population being compared. -/
theorem sourceFiniteEquilibrium_score_ae_eq_of_sourcePrimitives
    {cost production skill effort score tie : ℝ → ℝ} {E : ℝ}
    {n : ℕ} {cutoff reward : ℕ → ℝ} (hE : 0 ≤ E) (hpE : cost E = 1)
    (hp : ContinuousOn cost (Ici 0)) (hpC : StrictConvexOn ℝ (Ici 0) cost)
    (hpN : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hp0 : cost 0 = 0)
    (hg : ContinuousOn production (Ici 0)) (hgM : StrictMonoOn production (Ici 0))
    (hgC : ConcaveOn ℝ (Ici 0) production) (hg0 : 0 ≤ production 0)
    (hc : StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1))) (hc0 : cutoff 0 = 0) (hcn : cutoff (n + 1) = 1)
    (hfcont : ContinuousOn skill (Icc (0 : ℝ) 1)) (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hr0 : 0 ≤ reward 0) (hrn : reward n ≤ 1)
    (hscore : Measurable score) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)) :
    score =ᵐ[unitRankMeasure] sourceFiniteRankScore cost production skill E n cutoff reward := by
  obtain ⟨F, hF, hpF, heffort⟩ := sourceFiniteEquilibrium_effort_unique_of_sourcePrimitives
    hp hpC hpN hp0 hg hgM hgC hg0 hc hc0 hcn hfcont hf hf0 hr hr0 hrn hscore htie hinj hbest
  have hpm := sourceCost_strictMonoOn_of_strictConvex hpC hpN hp0
  have hFE : F = E := hpm.injOn hF.le hE (hpF.trans hpE.symm)
  rw [hFE] at heffort
  filter_upwards [heffort, hbest, ae_restrict_mem measurableSet_Ioc] with t htE htB ht
  have hcan := sourceFiniteRankEffort_score_and_incentives hE (hp.mono Icc_subset_Ici_self) hpm hp0 hpE
    (hpC.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _)) (hg.mono Icc_subset_Ici_self)
    (hgM.mono Icc_subset_Ici_self) hg0 (hgC.subset Icc_subset_Ici_self (convex_Icc _ _))
    hc hc0 hcn hf hf0 hr hr0 hrn ht
  rw [htB.2.1, htE]
  exact hcan.2.1.symm

/-- Population utility of the square-root-production, quadratic-cost example. -/
noncomputable def sqrtQuadraticSocietalUtility (rho c : ℝ) : ℝ :=
  (1 - c) * Real.sqrt (Real.sqrt (rho / (1 - c))) * c

/-- The smooth polynomial controlling the source example's optimum. -/
def sqrtQuadraticSocietalPolynomial (c : ℝ) : ℝ := c ^ 4 * (1 - c) ^ 3

theorem sqrtQuadraticSocietalUtility_nonneg {rho c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    0 ≤ sqrtQuadraticSocietalUtility rho c :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hc.2) (Real.sqrt_nonneg _)) hc.1

theorem sqrtQuadraticSocietalUtility_fourth {rho c : ℝ} (hrho : 0 ≤ rho) (hc : c < 1) :
    sqrtQuadraticSocietalUtility rho c ^ 4 = rho * sqrtQuadraticSocietalPolynomial c := by
  have hq : 0 ≤ rho / (1 - c) := div_nonneg hrho (sub_pos.mpr hc).le
  have hs : Real.sqrt (Real.sqrt (rho / (1 - c))) ^ 4 = rho / (1 - c) := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hq]
  unfold sqrtQuadraticSocietalUtility sqrtQuadraticSocietalPolynomial
  rw [mul_pow, mul_pow, hs]
  field_simp [(sub_pos.mpr hc).ne']

theorem sqrtQuadraticSocietalPolynomial_hasDerivAt (c : ℝ) :
    HasDerivAt sqrtQuadraticSocietalPolynomial (c ^ 3 * (1 - c) ^ 2 * (4 - 7 * c)) c := by
  convert ((hasDerivAt_id c).pow 4).mul (((hasDerivAt_const c (1 : ℝ)).sub (hasDerivAt_id c)).pow 3) using 1
  dsimp [sqrtQuadraticSocietalPolynomial]
  ring

theorem sqrtQuadraticSocietalPolynomial_strictMono :
    StrictMonoOn sqrtQuadraticSocietalPolynomial (Icc (0 : ℝ) (4 / 7)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((continuous_id.pow 4).mul ((continuous_const.sub continuous_id).pow 3)).continuousOn
  intro c hc
  rw [interior_Icc] at hc
  change 0 < deriv sqrtQuadraticSocietalPolynomial c
  rw [(sqrtQuadraticSocietalPolynomial_hasDerivAt c).deriv]
  exact mul_pos (mul_pos (pow_pos hc.1 _) (pow_pos (by linarith [hc.2]) _)) (by linarith [hc.2])

theorem sqrtQuadraticSocietalPolynomial_strictAnti :
    StrictAntiOn sqrtQuadraticSocietalPolynomial (Icc (4 / 7 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    ((continuous_id.pow 4).mul ((continuous_const.sub continuous_id).pow 3)).continuousOn
  intro c hc
  rw [interior_Icc] at hc
  change deriv sqrtQuadraticSocietalPolynomial c < 0
  rw [(sqrtQuadraticSocietalPolynomial_hasDerivAt c).deriv]
  exact mul_neg_of_pos_of_neg (mul_pos (pow_pos (by linarith [hc.1]) _) (pow_pos (sub_pos.mpr hc.2) _))
    (by linarith [hc.1])

theorem sqrtQuadraticSocietalPolynomial_lt_at_four_sevenths {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hne : c ≠ 4 / 7) :
    sqrtQuadraticSocietalPolynomial c < sqrtQuadraticSocietalPolynomial (4 / 7) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact sqrtQuadraticSocietalPolynomial_strictMono ⟨hc.1, hlt.le⟩ (by norm_num) hlt
  · exact sqrtQuadraticSocietalPolynomial_strictAnti (by norm_num) ⟨hgt.le, hc.2⟩ hgt

theorem sqrtQuadraticSocietalUtility_lt_at_four_sevenths {rho c : ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ico (0 : ℝ) 1) (hne : c ≠ 4 / 7) :
    sqrtQuadraticSocietalUtility rho c < sqrtQuadraticSocietalUtility rho (4 / 7) := by
  apply (pow_lt_pow_iff_left₀ (sqrtQuadraticSocietalUtility_nonneg ⟨hc.1, hc.2.le⟩)
    (sqrtQuadraticSocietalUtility_nonneg (by norm_num : (4 / 7 : ℝ) ∈ Icc 0 1))
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [sqrtQuadraticSocietalUtility_fourth hrho.le hc.2,
    sqrtQuadraticSocietalUtility_fourth hrho.le (by norm_num)]
  exact mul_lt_mul_of_pos_left (sqrtQuadraticSocietalPolynomial_lt_at_four_sevenths ⟨hc.1, hc.2.le⟩ hne) hrho

theorem sqrtQuadraticSocietalUtility_strictMono {rho : ℝ} (hrho : 0 < rho) :
    StrictMonoOn (sqrtQuadraticSocietalUtility rho) (Icc (0 : ℝ) (4 / 7)) := by
  intro c hc d hd hcd
  apply (pow_lt_pow_iff_left₀ (sqrtQuadraticSocietalUtility_nonneg ⟨hc.1, by linarith [hc.2]⟩)
    (sqrtQuadraticSocietalUtility_nonneg ⟨hd.1, by linarith [hd.2]⟩) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [sqrtQuadraticSocietalUtility_fourth hrho.le (by linarith [hc.2]),
    sqrtQuadraticSocietalUtility_fourth hrho.le (by linarith [hd.2])]
  exact mul_lt_mul_of_pos_left (sqrtQuadraticSocietalPolynomial_strictMono hc hd hcd) hrho

/-- The exact capacity range for the source example's interior optimum. -/
theorem sqrtQuadraticSocietalUtility_interior_maximizer_iff {rho : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    (∃ c ∈ Ioo (0 : ℝ) (1 - rho), ∀ d ∈ Icc (0 : ℝ) (1 - rho),
      sqrtQuadraticSocietalUtility rho d ≤ sqrtQuadraticSocietalUtility rho c) ↔ rho < 3 / 7 := by
  constructor
  · rintro ⟨c, hc, hmax⟩
    by_contra hn
    have hcap : 1 - rho ≤ (4 / 7 : ℝ) := by linarith [le_of_not_gt hn]
    have hlt := sqrtQuadraticSocietalUtility_strictMono hrho ⟨hc.1.le, hc.2.le.trans hcap⟩
      ⟨by linarith, hcap⟩ hc.2
    exact (not_le_of_gt hlt) (hmax (1 - rho) ⟨by linarith, le_rfl⟩)
  · intro hsmall
    refine ⟨4 / 7, ⟨by norm_num, by linarith⟩, ?_⟩
    intro d hd
    by_cases heq : d = 4 / 7
    · rw [heq]
    · exact (sqrtQuadraticSocietalUtility_lt_at_four_sevenths hrho ⟨hd.1, by linarith [hd.2]⟩ heq).le

/-- The compact-interval inverse of quadratic effort cost. -/
theorem effortIntervalInverse_quadratic_one {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    effortIntervalInverse (fun e : ℝ => e ^ 2) 1 q = Real.sqrt q := by
  have hm := quadraticCost_strictMono.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self)
  have h := hm.injOn.leftInvOn_invFunOn
    (show Real.sqrt q ∈ Icc (0 : ℝ) 1 from ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hq.2⟩)
  simpa only [Real.sq_sqrt hq.1] using h

noncomputable def sourceSqrtQuadraticEffort (rho c : ℝ) : ℝ → ℝ :=
  sourceFiniteRankEffort (fun e => e ^ 2) Real.sqrt id 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c)

noncomputable def sourceSqrtQuadraticScore (rho c : ℝ) : ℝ → ℝ :=
  sourceFiniteRankScore (fun e => e ^ 2) Real.sqrt id 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c)

theorem sourceSqrtQuadraticScore_zero (rho : ℝ) : sourceSqrtQuadraticScore rho 0 = fun _ => 0 := by
  funext t
  unfold sourceSqrtQuadraticScore sourceFiniteRankScore
  rw [finiteLowerRankBand_twoLevel]
  split
  · rw [sourceRecursiveBandScore_twoLevel (by norm_num) (by norm_num)
      (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)]
    simp only [id_eq, mul_zero, Real.sqrt_zero, zero_mul, max_self]
  · simp only [sourceRecursiveBandScore, Real.sqrt_zero, zero_mul, max_self]

theorem sourceSqrtQuadraticEffort_zero (rho : ℝ) : sourceSqrtQuadraticEffort rho 0 = fun _ => 0 := by
  funext t
  unfold sourceSqrtQuadraticEffort sourceFiniteRankEffort
  rw [finiteLowerRankBand_twoLevel]
  split
  · rw [sourceRecursiveBandScore_twoLevel (by norm_num) (by norm_num)
      (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)]
    simp only [id_eq, mul_zero, zero_div]
    exact sourceEffortAtScore_zero (by norm_num) (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)
  · simp only [sourceRecursiveBandScore, zero_div]
    exact sourceEffortAtScore_zero (by norm_num) (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)

/-- The canonical profiles are actual equilibria at every positive feasible
cutoff, with capacity verified using actual admission ranks. -/
theorem sourceSqrtQuadraticEquilibrium {rho c : ℝ} {tie : ℝ → ℝ}
    (hrho : 0 < rho) (hc : c ∈ Ioc (0 : ℝ) (1 - rho))
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    AEMeasurable (sourceSqrtQuadraticEffort rho c) unitRankMeasure ∧
    Measurable (sourceSqrtQuadraticScore rho c) ∧
    (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id
      (sourceSqrtQuadraticScore rho c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (sourceTwoLevelReward rho c) t (sourceSqrtQuadraticEffort rho c t)) ∧
    Measure.map (tieBrokenRank unitRankMeasure (sourceSqrtQuadraticScore rho c) tie) unitRankMeasure = unitRankMeasure ∧
    (∫ t, sourceTwoLevelReward rho c (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (tieBrokenRank unitRankMeasure (sourceSqrtQuadraticScore rho c) tie t)).val ∂unitRankMeasure) = rho := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hcut := sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩
  have hcut0 : sourceTwoLevelCutoff c 0 = 0 := by simp [sourceTwoLevelCutoff]
  have hcut2 : sourceTwoLevelCutoff c 2 = 1 := by norm_num [sourceTwoLevelCutoff]
  have h := sourceFiniteRankEffort_equilibrium_at_unitCost
    (cost := fun e : ℝ => e ^ 2) (production := Real.sqrt) (skill := id)
    (E := 1) (n := 1) (cutoff := sourceTwoLevelCutoff c) (reward := sourceTwoLevelReward rho c)
    (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex (fun _ _ => sq_nonneg _)
    (by norm_num) (by norm_num) Real.continuous_sqrt.continuousOn Real.strictMonoOn_sqrt
    Real.strictConcaveOn_sqrt.concaveOn (by norm_num) hcut hcut0 hcut2
    continuousOn_id (strictMono_id.strictMonoOn _) (by norm_num)
    (sourceTwoLevelReward_strictMono hrho hc1) (by simp [sourceTwoLevelReward])
    (by simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero];
        exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])) htie
  haveI := noAtoms_map_tie_of_injOn_unitRank htie hinj
  have hmean := sourceFiniteAdmission_mean_of_measurable_score (reward := sourceTwoLevelReward rho c)
    hcut hcut0 hcut2 h.2.1 htie hinj
  refine ⟨h.1, h.2.1, h.2.2.mono (fun _ ht => ht.2.1),
    (tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure h.2.1 htie).trans
      restrict_Ioc_eq_restrict_Icc.symm, ?_⟩
  unfold sourceSqrtQuadraticScore
  rw [hmean.2]
  norm_num [Fin.sum_univ_succ, sourceTwoLevelCutoff, sourceTwoLevelReward]
  field_simp [(sub_pos.mpr hc1).ne']

/-- Actual societal utility of the complete canonical policy family,
including pure randomization at zero. Integrability is proved. -/
theorem sourceSqrtQuadraticSocietalUtility_eq {rho c : ℝ} (hrho : 0 < rho)
    (hc : c ∈ Icc (0 : ℝ) (1 - rho)) :
    Integrable (sourceSqrtQuadraticScore rho c) unitRankMeasure ∧
    sourceSocietalUtility (sourceSqrtQuadraticScore rho c) = sqrtQuadraticSocietalUtility rho c := by
  by_cases hc0 : c = 0
  · subst c
    rw [sourceSqrtQuadraticScore_zero]
    simp [sourceSocietalUtility, sqrtQuadraticSocietalUtility]
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
  have hc1 : c < 1 := by linarith [hc.2]
  have hq : rho / (1 - c) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hrho (sub_pos.mpr hc1)).le, (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])⟩
  have hscale : sourceScoreScale (fun e => e ^ 2) Real.sqrt 1 rho c = Real.sqrt (Real.sqrt (rho / (1 - c))) := by
    unfold sourceScoreScale
    rw [effortIntervalInverse_quadratic_one hq]
  have h := sourceFiniteSocietalUtility_eq_sum_of_zero_baseline
    (cost := fun e : ℝ => e ^ 2) (production := Real.sqrt) (skill := id) (E := 1)
    (reward := sourceTwoLevelReward rho c) (sourceTwoLevelCutoff_strictMono ⟨hcpos, hc1⟩)
    (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff]) Real.sqrt_zero
  refine ⟨h.1, ?_⟩
  rw [sourceSqrtQuadraticScore, h.2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero]
  rw [sourceRecursiveBandScore_twoLevel (by norm_num) (by norm_num)
    (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num), hscale]
  simp only [sourceRecursiveBandScore, max_self, mul_zero, zero_add, sourceTwoLevelCutoff,
    if_pos, if_false, Nat.one_ne_zero, show ¬ (2 : ℕ) = 0 by decide,
    show ¬ (2 : ℕ) = 1 by decide, id_eq, max_eq_left (mul_nonneg (Real.sqrt_nonneg _) hcpos.le)]
  unfold sqrtQuadraticSocietalUtility
  ring

/-- The source example's utility formula is independent of equilibrium
selection: every measurable-score equilibrium has the constructed scores. -/
theorem sourceSqrtQuadraticSocietalUtility_eq_of_equilibrium
    {rho c : ℝ} {effort score tie : ℝ → ℝ} (hrho : 0 < rho)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) (hscore : Measurable score)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id
      score tie (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort t)) :
    Integrable score unitRankMeasure ∧ sourceSocietalUtility score = sqrtQuadraticSocietalUtility rho c := by
  have hc1 : c < 1 := by linarith [hc.2]
  have heq := sourceFiniteEquilibrium_score_ae_eq_of_sourcePrimitives
    (E := 1) (by norm_num) (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex
    (fun _ _ => sq_nonneg _) (by norm_num) Real.continuous_sqrt.continuousOn Real.strictMonoOn_sqrt
    Real.strictConcaveOn_sqrt.concaveOn (by norm_num) (sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩)
    (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff]) continuousOn_id
    (strictMono_id.strictMonoOn _) (by norm_num) (sourceTwoLevelReward_strictMono hrho hc1)
    (by simp [sourceTwoLevelReward])
    (by simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero];
        exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])) hscore htie hinj hbest
  have h := sourceSqrtQuadraticSocietalUtility_eq hrho ⟨hc.1.le, hc.2⟩
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

/-- At the zero cutoff the comparison uses the source's one-level pure
randomization policy. The constructed effort and score are both zero. -/
theorem sourceSqrtQuadraticPureRandomizationEquilibrium (rho : ℝ) (tie : ℝ → ℝ) :
    ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id
      (sourceSqrtQuadraticScore rho 0) tie (fun _ : Fin 1 => 0) (fun _ => rho) t
      (sourceSqrtQuadraticEffort rho 0 t) := by
  rw [sourceSqrtQuadraticScore_zero, sourceSqrtQuadraticEffort_zero]
  apply Filter.Eventually.of_forall
  intro t
  refine ⟨le_rfl, by simp, ?_⟩
  intro d _
  change rho - d ^ 2 ≤ rho - (0 : ℝ) ^ 2
  nlinarith [sq_nonneg d]

/-- Every equilibrium of the constant-reward policy has zero effort and
zero score in this example. This proves the pure-randomization endpoint
without assuming its score profile. -/
theorem sourceSqrtQuadraticPureRandomization_score_zero_of_equilibrium
    {rho : ℝ} {effort score tie : ℝ → ℝ}
    (hbest : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id
      score tie (fun _ : Fin 1 => 0) (fun _ => rho) t (effort t)) :
    score =ᵐ[unitRankMeasure] (fun _ => 0) := by
  filter_upwards [hbest] with t ht
  have h := ht.2.2 0 (by norm_num)
  change rho - (0 : ℝ) ^ 2 ≤ rho - (effort t) ^ 2 at h
  have he : effort t = 0 := by nlinarith [sq_nonneg (effort t)]
  rw [ht.2.1, he]
  simp

/-- Proposition 3.4 for every actual equilibrium selection in the source's
square-root/quadratic example. The unique optimum is `4/7`; pure
randomization and deterministic admission are both strictly worse. -/
theorem sourceSqrtQuadraticSocietalUtility_unique_interior_maximum
    {rho : ℝ} {tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ}
    (hrho : 0 < rho) (hsmall : rho < 3 / 7)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hscore : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), Measurable (score c))
    (hbest : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t))
    (hpure : ∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id (score 0) tie
      (fun _ : Fin 1 => 0) (fun _ => rho) t (effort 0 t)) :
    (4 / 7 : ℝ) ∈ Ioo 0 (1 - rho) ∧ rho / (1 - 4 / 7) ∈ Ioo rho 1 ∧
    (∀ c ∈ Icc (0 : ℝ) (1 - rho), Integrable (score c) unitRankMeasure) ∧
    ∀ c ∈ Icc (0 : ℝ) (1 - rho),
      sourceSocietalUtility (score c) ≤ sourceSocietalUtility (score (4 / 7)) ∧
      (sourceSocietalUtility (score c) = sourceSocietalUtility (score (4 / 7)) ↔ c = 4 / 7) := by
  have hformula (c : ℝ) (hc : c ∈ Icc (0 : ℝ) (1 - rho)) :
      Integrable (score c) unitRankMeasure ∧ sourceSocietalUtility (score c) = sqrtQuadraticSocietalUtility rho c := by
    by_cases hc0 : c = 0
    · subst c
      have heq := sourceSqrtQuadraticPureRandomization_score_zero_of_equilibrium hpure
      refine ⟨(integrable_zero ℝ ℝ unitRankMeasure).congr heq.symm, ?_⟩
      unfold sourceSocietalUtility
      rw [integral_congr_ae heq]
      simp [sqrtQuadraticSocietalUtility]
    · have hc' : c ∈ Ioc (0 : ℝ) (1 - rho) := ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), hc.2⟩
      exact sourceSqrtQuadraticSocietalUtility_eq_of_equilibrium hrho hc' (hscore c hc') htie hinj (hbest c hc')
  have hstar : (4 / 7 : ℝ) ∈ Ioo 0 (1 - rho) := ⟨by norm_num, by linarith⟩
  have hreward : rho / (1 - 4 / 7) ∈ Ioo rho 1 := by
    constructor <;> norm_num <;> linarith
  refine ⟨hstar, hreward, fun c hc => (hformula c hc).1, ?_⟩
  intro c hc
  rw [(hformula c hc).2, (hformula (4 / 7) ⟨hstar.1.le, hstar.2.le⟩).2]
  by_cases heq : c = 4 / 7
  · subst c
    exact ⟨le_rfl, iff_of_true rfl rfl⟩
  · have hlt := sqrtQuadraticSocietalUtility_lt_at_four_sevenths hrho ⟨hc.1, by linarith [hc.2]⟩ heq
    exact ⟨hlt.le, iff_of_false hlt.ne heq⟩

/-- A nonvacuous complete policy family for Proposition 3.4. All policies
use one population, cost, production, skill quantile, and arbitrary fixed
measurable injective tie key. Their actual ranks, capacity, equilibrium
incentives, integrability, and unique interior optimum are proved. -/
theorem exists_sourceSqrtQuadraticSocietalUtility_interior_maximum
    {rho : ℝ} {tie : ℝ → ℝ} (hrho : 0 < rho) (hsmall : rho < 3 / 7)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    ∃ effort score : ℝ → ℝ → ℝ,
      (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
        AEMeasurable (effort c) unitRankMeasure ∧ Measurable (score c) ∧
        (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id
          (score c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t (effort c t)) ∧
        Measure.map (tieBrokenRank unitRankMeasure (score c) tie) unitRankMeasure = unitRankMeasure ∧
        (∫ t, sourceTwoLevelReward rho c (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (tieBrokenRank unitRankMeasure (score c) tie t)).val ∂unitRankMeasure) = rho) ∧
      (∀ᵐ t ∂unitRankMeasure, SourceFiniteBestResponseAt (fun e => e ^ 2) Real.sqrt id (score 0) tie
        (fun _ : Fin 1 => 0) (fun _ => rho) t (effort 0 t)) ∧
      (4 / 7 : ℝ) ∈ Ioo 0 (1 - rho) ∧ rho / (1 - 4 / 7) ∈ Ioo rho 1 ∧
      ∀ c ∈ Icc (0 : ℝ) (1 - rho), Integrable (score c) unitRankMeasure ∧
        sourceSocietalUtility (score c) ≤ sourceSocietalUtility (score (4 / 7)) ∧
        (sourceSocietalUtility (score c) = sourceSocietalUtility (score (4 / 7)) ↔ c = 4 / 7) := by
  have hfamily (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) := sourceSqrtQuadraticEquilibrium hrho hc htie hinj
  have hpure := sourceSqrtQuadraticPureRandomizationEquilibrium rho tie
  have hmax := sourceSqrtQuadraticSocietalUtility_unique_interior_maximum hrho hsmall htie hinj
    (fun c hc => (hfamily c hc).2.1) (fun c hc => (hfamily c hc).2.2.1) hpure
  exact ⟨sourceSqrtQuadraticEffort rho, sourceSqrtQuadraticScore rho, hfamily, hpure,
    hmax.1, hmax.2.1, fun c hc => ⟨hmax.2.2.1 c hc, hmax.2.2.2 c hc⟩⟩

/-- The appendix's capacity range is sharp for this actual equilibrium
family, with pure randomization included as the one-level endpoint. -/
theorem sourceSqrtQuadraticSocietalUtility_interior_maximizer_iff {rho : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    (∃ c ∈ Ioo (0 : ℝ) (1 - rho), ∀ d ∈ Icc (0 : ℝ) (1 - rho),
      sourceSocietalUtility (sourceSqrtQuadraticScore rho d) ≤
        sourceSocietalUtility (sourceSqrtQuadraticScore rho c)) ↔ rho < 3 / 7 := by
  have heq : (∃ c ∈ Ioo (0 : ℝ) (1 - rho), ∀ d ∈ Icc (0 : ℝ) (1 - rho),
      sourceSocietalUtility (sourceSqrtQuadraticScore rho d) ≤
        sourceSocietalUtility (sourceSqrtQuadraticScore rho c)) ↔
      (∃ c ∈ Ioo (0 : ℝ) (1 - rho), ∀ d ∈ Icc (0 : ℝ) (1 - rho),
        sqrtQuadraticSocietalUtility rho d ≤ sqrtQuadraticSocietalUtility rho c) := by
    constructor <;> rintro ⟨c, hc, hmax⟩ <;> refine ⟨c, hc, ?_⟩ <;> intro d hd
    · simpa only [(sourceSqrtQuadraticSocietalUtility_eq hrho hd).2,
        (sourceSqrtQuadraticSocietalUtility_eq hrho ⟨hc.1.le, hc.2.le⟩).2] using hmax d hd
    · simpa only [(sourceSqrtQuadraticSocietalUtility_eq hrho hd).2,
        (sourceSqrtQuadraticSocietalUtility_eq hrho ⟨hc.1.le, hc.2.le⟩).2] using hmax d hd
  exact heq.trans (sqrtQuadraticSocietalUtility_interior_maximizer_iff hrho hrho1)

end LBG22StrategicRanking
