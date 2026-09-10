import LBG22StrategicRanking.ProofInterface
import LBG22StrategicRanking.AffineSkillPrimitiveRepairs
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Applicant welfare with constant-elasticity primitives

Power effort cost and power production have constant cost elasticity in
produced-score units. Consequently the upper-tail skill condition alone
supplies the additional shape restriction for two-level welfare monotonicity.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Power cost and production give an affine log cost in log produced score.
The inverse is the actual inverse on the unit-cost effort interval. -/
theorem powerCostProduction_geometricConcavity {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    ConcaveOn ℝ {z : ℝ | (0 : ℝ) ^ s < Real.exp z ∧ Real.exp z ≤ (1 : ℝ) ^ s}
      (fun z => Real.log ((effortIntervalInverse (fun e : ℝ => e ^ s) 1 (Real.exp z)) ^ r)) := by
  have hD : {z : ℝ | (0 : ℝ) ^ s < Real.exp z ∧ Real.exp z ≤ (1 : ℝ) ^ s} = Iic 0 := by
    ext z
    simp only [Real.zero_rpow hs.ne', Real.one_rpow, Real.exp_pos, true_and,
      Real.exp_le_one_iff, mem_setOf_eq, mem_Iic]
  rw [hD]
  have hlinear : ConcaveOn ℝ (Iic (0 : ℝ)) (fun z => (r / s) * z) :=
    (concaveOn_id (convex_Iic 0)).smul (div_nonneg hr hs.le)
  apply hlinear.congr
  intro z hz
  have hi := effortIntervalInverse_spec (by norm_num : (0 : ℝ) ≤ 1)
    (Real.continuous_rpow_const hs.le).continuousOn
    (show Real.exp z ∈ Icc ((0 : ℝ) ^ s) ((1 : ℝ) ^ s) by
      simpa only [Real.zero_rpow hs.ne', Real.one_rpow] using
        And.intro (Real.exp_pos z).le (Real.exp_le_one_iff.mpr hz))
  have hpos : 0 < effortIntervalInverse (fun e : ℝ => e ^ s) 1 (Real.exp z) := by
    refine lt_of_le_of_ne hi.1.1 ?_
    intro heq
    have hzero := hi.2
    rw [← heq, Real.zero_rpow hs.ne'] at hzero
    exact (Real.exp_pos z).ne' hzero.symm
  have hlog := congrArg Real.log hi.2
  rw [Real.log_rpow hpos, Real.log_exp] at hlog
  change (r / s) * z = Real.log (effortIntervalInverse (fun e : ℝ => e ^ s) 1 (Real.exp z) ^ r)
  rw [Real.log_rpow hpos]
  calc
    (r / s) * z = (r / s) *
        (s * Real.log (effortIntervalInverse (fun e : ℝ => e ^ s) 1 (Real.exp z))) :=
      congrArg (fun w => (r / s) * w) hlog.symm
    _ = _ := by field_simp

/-- Every source-compatible positive power production and strictly convex
power cost satisfies the technology-side condition. Skills need only be
continuous and strictly increasing, with upper-tail log concavity. -/
theorem SourceProofs.applicantWelfare_power_primitives
    {r s rho : ℝ} {skill tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ}
    (hr : 1 < r) (hs : 0 < s) (hs_one : s ≤ 1)
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hfc : ContinuousOn skill (Icc (0 : ℝ) 1))
    (hf : StrictMonoOn skill (Icc (0 : ℝ) 1)) (hf0 : 0 ≤ skill 0)
    (hfTail : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x => Real.log (skill (upperTailRank x))))
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hEq : ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      RankingScorePriorityEquilibrium (fun e : ℝ => e ^ r) (fun e : ℝ => e ^ s)
        skill tie 1 (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c)
        (effort c) (score c)) :
    AntitoneOn (fun c => sourceFiniteApplicantWelfare (fun e : ℝ => e ^ r)
      (effort c) (score c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (sourceTwoLevelReward rho c)) (Ioc (0 : ℝ) (1 - rho)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hP : RankingPrimitives (fun e : ℝ => e ^ r) (fun e : ℝ => e ^ s) skill 0 := by
    refine ⟨le_rfl, (Real.continuous_rpow_const hr0.le).continuousOn,
      strictConvexOn_rpow hr, (fun e he => Real.rpow_nonneg he _),
      Real.zero_rpow hr0.ne', (Real.continuous_rpow_const hs.le).continuousOn,
      Real.strictMonoOn_rpow_Ici_of_exponent_pos hs, Real.concaveOn_rpow hs.le hs_one,
      ?_, hfc, hf, hf0⟩
    exact Real.rpow_nonneg (by norm_num) _
  exact applicantWelfare_antitone_of_upperTailConcavity hP hrho (by norm_num : (0 : ℝ) < 1)
    (Real.one_rpow r) hfTail (powerCostProduction_geometricConcavity hr0.le hs) htie hinj hEq

/-- Uniform skill on any nondegenerate nonnegative interval and all
source-compatible power technologies give decreasing applicant welfare.
The lower skill endpoint may be zero. -/
theorem SourceProofs.applicantWelfare_power_affine_primitives
    {r s rho lower width : ℝ} {tie : ℝ → ℝ} {effort score : ℝ → ℝ → ℝ}
    (hr : 1 < r) (hs : 0 < s) (hs_one : s ≤ 1)
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hlower : 0 ≤ lower) (hwidth : 0 < width)
    (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1))
    (hEq : ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      RankingScorePriorityEquilibrium (fun e : ℝ => e ^ r) (fun e : ℝ => e ^ s)
        (fun t => lower + width * t) tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) :
    AntitoneOn (fun c => sourceFiniteApplicantWelfare (fun e : ℝ => e ^ r)
      (effort c) (score c) tie (fun i : Fin 2 => sourceTwoLevelCutoff c i)
      (sourceTwoLevelReward rho c)) (Ioc (0 : ℝ) (1 - rho)) := by
  have hf : StrictMono (fun t : ℝ => lower + width * t) := by
    intro a b hab
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hab hwidth) lower
  apply applicantWelfare_power_primitives hr hs hs_one hrho
    (by fun_prop) (hf.strictMonoOn _) (by simpa using hlower) ?_ htie hinj hEq
  exact upperTail_logSkill_concaveOn_of_logConcave
    (fun t ht => add_pos_of_nonneg_of_pos hlower (mul_pos hwidth ht.1))
    (hf.monotone.monotoneOn _) (affineSkill_logConcave hlower hwidth)

end LBG22StrategicRanking
