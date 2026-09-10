import LBG22StrategicRanking.SocietalUtilityPrimitiveRepairs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An actual-equilibrium counterexample to applicant-welfare monotonicity

Quadratic effort cost and linear production give an admitted applicant cost
proportional to the squared ratio of cutoff skill to applicant skill. For
skill `1 / sqrt (1 - t² / 4)`, its population integral is elementary. At
capacity `3/10`, increasing the cutoff from `1/10` to `1/5` increases welfare.
The primitives satisfy the source conditions, including differentiability;
the comparison applies to actual equilibria with a fixed tie key.
-/

namespace LBG22StrategicRanking.ApplicantWelfareCounterexample

open Set MeasureTheory

noncomputable def skill (t : ℝ) : ℝ := 1 / Real.sqrt (1 - t ^ 2 / 4)

theorem denominator_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t ^ 2 / 4 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  linarith

theorem skill_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < skill t :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (denominator_pos ht))

theorem skill_continuous : ContinuousOn skill (Icc (0 : ℝ) 1) := by
  apply continuousOn_const.div
    (((continuous_const.sub ((continuous_id.pow 2).div_const 4)).sqrt).continuousOn)
  intro t ht
  exact (Real.sqrt_pos.mpr (denominator_pos ht)).ne'

theorem skill_strictMono : StrictMonoOn skill (Icc (0 : ℝ) 1) := by
  intro t ht s hs hts
  apply one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (denominator_pos hs))
  apply Real.sqrt_lt_sqrt (denominator_pos hs).le
  have hsq : t ^ 2 < s ^ 2 := sq_lt_sq₀ ht.1 hs.1 |>.mpr hts
  linarith

theorem skill_differentiable : DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) := by
  intro t ht
  have hd : DifferentiableAt ℝ (fun s : ℝ => 1 - s ^ 2 / 4) t := by fun_prop
  have hp := denominator_pos ⟨ht.1.le, ht.2.le⟩
  exact ((differentiableAt_const (1 : ℝ)).div (hd.sqrt hp.ne')
    (Real.sqrt_pos.mpr hp).ne').differentiableWithinAt

theorem skill_sq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    skill t ^ 2 = 1 / (1 - t ^ 2 / 4) := by
  rw [skill, div_pow, one_pow, Real.sq_sqrt (denominator_pos ht).le]

noncomputable def effort (c : ℝ) : ℝ → ℝ :=
  sourceFiniteRankEffort (fun e => e ^ 2) id skill 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward (3 / 10) c)

noncomputable def score (c : ℝ) : ℝ → ℝ :=
  sourceFiniteRankScore (fun e => e ^ 2) id skill 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward (3 / 10) c)

/-- The entire feasible policy family is realized in the same primitive
environment, with best response against every nonnegative effort deviation. -/
theorem equilibrium {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 3 / 10))
    {tie : ℝ → ℝ} (htie : Measurable tie) :
    Measurable (score c) ∧ ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt (fun e => e ^ 2) id skill (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (3 / 10) c)
        t (effort c t) := by
  have hc1 : c < 1 := by linarith [hc.2]
  have h := sourceFiniteRankEffort_equilibrium_at_unitCost
    (cost := fun e => e ^ 2) (production := id) (skill := skill) (E := 1)
    (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex
    (fun e _ => sq_nonneg e) (by norm_num) (by norm_num)
    continuous_id.continuousOn (strictMono_id.strictMonoOn _) (concaveOn_id (convex_Ici _)) (by norm_num)
    (sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩)
    (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff])
    skill_continuous skill_strictMono (by norm_num [skill])
    (sourceTwoLevelReward_strictMono (by norm_num) hc1)
    (by simp [sourceTwoLevelReward])
    (show sourceTwoLevelReward (3 / 10) c 1 ≤ 1 from by
      simp only [sourceTwoLevelReward, if_neg Nat.one_ne_zero]
      exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])) htie
  exact ⟨h.2.1, h.2.2.mono (fun _ ht => ht.2.1)⟩

/-- The admitted cost density simplifies to a quadratic polynomial times a
cutoff-dependent constant. -/
theorem admitted_cost {c t : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 3 / 10))
    (ht : t ∈ Icc c 1) :
    sourceTwoLevelEffort (fun e => e ^ 2) id skill 1 (3 / 10) c t ^ 2 =
      (3 / 10 : ℝ) / (1 - c) * (1 - t ^ 2 / 4) / (1 - c ^ 2 / 4) := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc1.le⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le.trans ht.1, ht.2⟩
  have hq : (3 / 10 : ℝ) / (1 - c) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos (by norm_num) (sub_pos.mpr hc1)).le,
      (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [hc.2])⟩
  have hscale : sourceScoreScale (fun e => e ^ 2) id 1 (3 / 10) c =
      Real.sqrt ((3 / 10 : ℝ) / (1 - c)) := by
    exact effortIntervalInverse_quadratic_one hq
  have hratio : skill c / skill t ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos (skill_pos hcI) (skill_pos htI)).le,
      (div_le_one (skill_pos htI)).mpr (skill_strictMono.monotoneOn hcI htI ht.1)⟩
  have htarget : sourceScoreScale (fun e => e ^ 2) id 1 (3 / 10) c * (skill c / skill t) ≤ 1 := by
    rw [hscale]
    exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) hratio.2).trans
      (Real.sqrt_le_one.mpr hq.2)
  have he : sourceTwoLevelEffort (fun e => e ^ 2) id skill 1 (3 / 10) c t =
      Real.sqrt ((3 / 10 : ℝ) / (1 - c)) * (skill c / skill t) := by
    have h := production_clipped_effortIntervalInverse (production := id)
      (by norm_num : (0 : ℝ) ≤ 1) continuous_id.continuousOn
      (monotone_id.monotoneOn _) htarget
    change sourceTwoLevelEffort (fun e => e ^ 2) id skill 1 (3 / 10) c t =
      max (sourceScoreScale (fun e => e ^ 2) id 1 (3 / 10) c * (skill c / skill t)) 0 at h
    rw [h, hscale, max_eq_left (mul_nonneg (Real.sqrt_nonneg _) hratio.1)]
  rw [he, mul_pow, Real.sq_sqrt hq.1, div_pow, skill_sq hcI, skill_sq htI]
  field_simp [(denominator_pos hcI).ne', (denominator_pos htI).ne']

theorem formula_welfare {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 3 / 10)) :
    sourceTwoLevelApplicantWelfare (fun e => e ^ 2) id skill 1 (3 / 10) c =
      3 / 10 - twoLevelApplicantCostCounterexample (3 / 10) c := by
  have hc1 : c ≤ 1 := by linarith [hc.2]
  have hi : (∫ t in c..1, sourceTwoLevelEffort (fun e => e ^ 2) id skill 1 (3 / 10) c t ^ 2) =
      ∫ t in c..1, (3 / 10 : ℝ) / (1 - c) * (1 - t ^ 2 / 4) / (1 - c ^ 2 / 4) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact admitted_cost hc (by simpa only [uIcc_of_le hc1] using ht)
  unfold sourceTwoLevelApplicantWelfare
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 2 / 4) volume c 1 :=
    ((continuous_pow 2).div_const 4).intervalIntegrable _ _
  rw [hi, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (intervalIntegrable_const) hint,
    intervalIntegral.integral_const, intervalIntegral.integral_div, integral_pow]
  simp only [smul_eq_mul]
  unfold twoLevelApplicantCostCounterexample
  field_simp [(show 1 - c ≠ 0 by linarith [hc.2]),
    (denominator_pos ⟨hc.1.le, hc1⟩).ne']
  ring

/-- The elementary expression is the welfare of every actual equilibrium,
not merely that of a supplied effort or admission formula. -/
theorem actual_welfare {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 3 / 10))
    {e s tie : ℝ → ℝ} (hs : Measurable s) (htie : Measurable tie)
    (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hEq : ∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt (fun a => a ^ 2) id skill s tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (3 / 10) c) t (e t)) :
    sourceFiniteApplicantWelfare (fun a => a ^ 2) e s tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (3 / 10) c) =
      3 / 10 - twoLevelApplicantCostCounterexample (3 / 10) c := by
  rw [sourceActualTwoLevelApplicantWelfare_eq_of_sourcePrimitives
    (E := 1) (by norm_num) hc (by norm_num) (by norm_num)
    (continuous_pow 2).continuousOn quadraticCost_strictConvex (fun a _ => sq_nonneg a) (by norm_num)
    continuous_id.continuousOn (strictMono_id.strictMonoOn _) (concaveOn_id (convex_Ici _)) (by norm_num)
    skill_continuous skill_strictMono (by norm_num [skill]) hs htie hinj hEq]
  exact formula_welfare hc

theorem welfare_increases {tie : ℝ → ℝ} (htie : Measurable tie)
    (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    sourceFiniteApplicantWelfare (fun e => e ^ 2) (effort (1 / 10)) (score (1 / 10)) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 10) i) (sourceTwoLevelReward (3 / 10) (1 / 10)) <
    sourceFiniteApplicantWelfare (fun e => e ^ 2) (effort (1 / 5)) (score (1 / 5)) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff (1 / 5) i) (sourceTwoLevelReward (3 / 10) (1 / 5)) := by
  have hc : (1 / 10 : ℝ) ∈ Ioc 0 (1 - 3 / 10) := by norm_num
  have hd : (1 / 5 : ℝ) ∈ Ioc 0 (1 - 3 / 10) := by norm_num
  have hec := equilibrium hc htie
  have hed := equilibrium hd htie
  rw [actual_welfare hc hec.1 htie hinj hec.2, actual_welfare hd hed.1 htie hinj hed.2]
  exact sub_lt_sub_left twoLevelApplicantCostCounterexample_decreases _

end LBG22StrategicRanking.ApplicantWelfareCounterexample
