import LBG22StrategicRanking.AffineSkillPrimitiveRepairs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root production and quadratic effort cost

This family instantiates the primitive weighted-utility repair, including the
case where the hard budget equals maximal measurable effort. The singular
production derivative at zero is outside the required interior domain.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- The inverse of square-root production on the feasible unit effort interval. -/
theorem effortIntervalInverse_sqrt_one {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    effortIntervalInverse Real.sqrt 1 z = z ^ 2 := by
  have hi := effortIntervalInverse_spec (by norm_num : (0 : ℝ) ≤ 1)
    Real.continuous_sqrt.continuousOn
    (show z ∈ Icc (Real.sqrt 0) (Real.sqrt 1) by simpa using hz)
  calc
    effortIntervalInverse Real.sqrt 1 z = (Real.sqrt (effortIntervalInverse Real.sqrt 1 z)) ^ 2 :=
      (Real.sq_sqrt hi.1.1).symm
    _ = z ^ 2 := congrArg (fun x => x ^ 2) hi.2

/-- In produced-score units, quadratic cost and square-root production give
the convex production-to-cost ratio `a⁻³` on the positive feasible interval. -/
theorem sqrt_quadratic_costRatio_convexOn {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1) :
    ConvexOn ℝ
      (Icc (Real.sqrt (effortIntervalInverse (fun e => e ^ 2) 1 rho)) (Real.sqrt 1))
      (fun a => a / (effortIntervalInverse Real.sqrt 1 a) ^ 2) := by
  have hq := effortIntervalInverse_spec (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_pow 2).continuousOn
    (show rho ∈ Icc ((0 : ℝ) ^ 2) (1 ^ 2) by simpa using And.intro hrho.le hrho_one.le)
  have hqpos : 0 < effortIntervalInverse (fun e => e ^ 2) 1 rho := by
    nlinarith [hq.1.1, hq.2]
  have hlo := Real.sqrt_pos.mpr hqpos
  have hconv := (convexOn_zpow (𝕜 := ℝ) (-3)).subset
    (show Icc (Real.sqrt (effortIntervalInverse (fun e => e ^ 2) 1 rho)) (Real.sqrt 1) ⊆
      Ioi 0 from fun _ ha => hlo.trans_le ha.1) (convex_Icc _ _)
  apply hconv.congr
  intro a ha
  have ha0 : 0 < a := hlo.trans_le ha.1
  dsimp only
  rw [effortIntervalInverse_sqrt_one ⟨ha0.le, by simpa using ha.2⟩]
  norm_num only [zpow_neg, zpow_ofNat]
  field_simp

/-- The square-root marginal production has the expected second derivative
at each strictly positive effort. -/
theorem sqrt_marginal_hasDerivAt {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun t => 1 / (2 * Real.sqrt t))
      (-1 / (4 * (Real.sqrt e) ^ 3)) e := by
  have hs := Real.hasDerivAt_sqrt he.ne'
  have hn : 2 * Real.sqrt e ≠ 0 := mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr he).ne'
  convert (hs.const_mul 2).inv hn using 1
  · funext t
    simp only [Pi.inv_apply, one_div]
  · field_simp
    norm_num

/-- A concrete nonparametric-repair instance: with `g(e)=√e`, `p(e)=e²`,
uniform measurable skill, any capacity in `(0,1)`, and any hard budget at
least one, every interior cutoff is optimal for an interior school weight. -/
theorem sourceTwoLevelWeightedUtility_exists_optimal_weight_sqrt_quadratic_uniform
    {rho budget mean c : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hbudget : 1 ≤ budget) (hmean : 0 < mean) (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      weightedPrivateUtility beta (sourceTwoLevelMeasurableUtility (fun e => e ^ 2) Real.sqrt 1 rho)
        (fun t => mean * sourceTwoLevelResidualUtility (fun e => e ^ 2) Real.sqrt budget 1 rho t) d ≤
      weightedPrivateUtility beta (sourceTwoLevelMeasurableUtility (fun e => e ^ 2) Real.sqrt 1 rho)
        (fun t => mean * sourceTwoLevelResidualUtility (fun e => e ^ 2) Real.sqrt budget 1 rho t) c := by
  have hsquare : ConcaveOn ℝ (Ioo 0 budget) (fun e => (Real.sqrt e) ^ 2) :=
    (concaveOn_id (convex_Ioo _ _)).congr (fun e he => (Real.sq_sqrt he.1.le).symm)
  have hssecond : ContinuousOn (fun e => -1 / (4 * (Real.sqrt e) ^ 3)) (Ioo 0 budget) :=
    continuousOn_const.div
      (continuousOn_const.mul (Real.continuous_sqrt.continuousOn.pow 3))
      (fun e he => mul_ne_zero (by norm_num) (pow_ne_zero 3 (Real.sqrt_pos.mpr he.1).ne'))
  apply sourceTwoLevelWeightedUtility_exists_optimal_weight_of_effortPrimitives
    (costDeriv := fun e => 2 * e) (costSecondDeriv := fun _ => 2)
    (productionDeriv := fun e => 1 / (2 * Real.sqrt e))
    (productionSecondDeriv := fun e => -1 / (4 * (Real.sqrt e) ^ 3))
    hrho hrho_one (by norm_num) hbudget (continuous_pow 2).continuousOn
    (fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0))
    (by norm_num) (by norm_num) _ _ Real.continuous_sqrt.continuousOn
    (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)
    (Real.strictConcaveOn_sqrt.concaveOn.subset (fun _ he => he.1.le) (convex_Ioo _ _))
    hsquare (fun e he => Real.hasDerivAt_sqrt he.1.ne')
    (fun e he => sqrt_marginal_hasDerivAt he.1) hssecond
    (sqrt_quadratic_costRatio_convexOn hrho hrho_one) hmean hc
  · intro e _
    convert (hasDerivAt_id e).pow 2 using 1
    norm_num [id_eq]
  · intro e _
    simpa using (hasDerivAt_id e).const_mul 2

/-- The square-root/quadratic family supports every interior cutoff in the
actual randomized-admission conditional expectation. Unmeasurable skill may
have any continuous increasing nonnegative quantile, independently of the
uniform measurable skill and admission lottery. -/
theorem sourceTwoLevelConditionalSchoolUtility_exists_optimal_weight_sqrt_quadratic
    {rho budget c : ℝ} {unmeasurableSkill : ℝ → ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hbudget : 1 ≤ budget)
    (hskill : ContinuousOn unmeasurableSkill (Icc 0 1))
    (hskill_mono : StrictMonoOn unmeasurableSkill (Icc 0 1))
    (hskill_zero : 0 ≤ unmeasurableSkill 0)
    (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceTwoLevelConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt budget 1 rho beta d ≤
      sourceTwoLevelConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt budget 1 rho beta c := by
  have hmean := unitRankMeasure_skill_integrable_and_mean_pos hskill hskill_mono hskill_zero
  obtain ⟨beta, hbeta, hopt⟩ :=
    sourceTwoLevelWeightedUtility_exists_optimal_weight_sqrt_quadratic_uniform
      hrho hrho_one hbudget hmean.2 hc
  have hbridge (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceTwoLevelConditionalSchoolUtility_eq_weighted (beta := beta) unitRankMeasure hmean.1
      hrho hrho_one (by norm_num : (0 : ℝ) < 1) hbudget (continuous_pow 2).continuousOn
      (fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0))
      (by norm_num) (by norm_num) Real.continuous_sqrt.continuousOn
      (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num) hd
  refine ⟨beta, hbeta, ?_⟩
  intro d hd
  rw [hbridge d hd, hbridge c ⟨hc.1, hc.2.le⟩]
  exact hopt d hd

/-- Square-root production and quadratic effort cost support every interior
cutoff when measurable skill is uniform on any nondegenerate nonnegative
interval. Independent unmeasurable skill may have any continuous strictly
increasing nonnegative quantile. The hard budget may equal maximal effort. -/
theorem sourceSkillConditionalSchoolUtility_exists_optimal_weight_sqrt_quadratic_affine
    {rho budget lowerSkill skillWidth c : ℝ} {unmeasurableSkill : ℝ → ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hbudget : 1 ≤ budget)
    (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hskill : ContinuousOn unmeasurableSkill (Icc 0 1))
    (hskill_mono : StrictMonoOn unmeasurableSkill (Icc 0 1))
    (hskill_zero : 0 ≤ unmeasurableSkill 0)
    (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceSkillConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt (fun t => lowerSkill + skillWidth * t) budget 1 rho beta d ≤
      sourceSkillConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt (fun t => lowerSkill + skillWidth * t) budget 1 rho beta c := by
  have hmean := unitRankMeasure_skill_integrable_and_mean_pos hskill hskill_mono hskill_zero
  have hsquare : ConcaveOn ℝ (Ioo 0 budget) (fun e => (Real.sqrt e) ^ 2) :=
    (concaveOn_id (convex_Ioo _ _)).congr (fun e he => (Real.sq_sqrt he.1.le).symm)
  have hssecond : ContinuousOn (fun e => -1 / (4 * (Real.sqrt e) ^ 3)) (Ioo 0 budget) :=
    continuousOn_const.div
      (continuousOn_const.mul (Real.continuous_sqrt.continuousOn.pow 3))
      (fun e he => mul_ne_zero (by norm_num) (pow_ne_zero 3 (Real.sqrt_pos.mpr he.1).ne'))
  apply sourceSkillConditionalSchoolUtility_exists_optimal_weight_of_affineSkill
    (costDeriv := fun e => 2 * e) (costSecondDeriv := fun _ => 2)
    (productionDeriv := fun e => 1 / (2 * Real.sqrt e))
    (productionSecondDeriv := fun e => -1 / (4 * (Real.sqrt e) ^ 3))
    unitRankMeasure hmean.1 hmean.2 hrho hrho_one hlower hwidth (by norm_num) hbudget
    (continuous_pow 2).continuousOn
    (fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0))
    (by norm_num) (by norm_num) _ _ Real.continuous_sqrt.continuousOn
    (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)
    (Real.strictConcaveOn_sqrt.concaveOn.subset (fun _ he => he.1.le) (convex_Ioo _ _))
    hsquare (fun e he => Real.hasDerivAt_sqrt he.1.ne')
    (fun e he => sqrt_marginal_hasDerivAt he.1) hssecond
    (sqrt_quadratic_costRatio_convexOn hrho hrho_one) hc
  · intro e _
    convert (hasDerivAt_id e).pow 2 using 1
    norm_num [id_eq]
  · intro e _
    simpa using (hasDerivAt_id e).const_mul 2

/-- A single nondegenerate source family realizes both repaired shape claims:
quadratic effort cost, square-root production, arbitrary affine measurable
skill with nonnegative lower endpoint, and independent unmeasurable skill.
There is no restriction on measurable-skill dispersion, capacity in `(0,1)`,
or the hard budget beyond the feasible bound `B>=1`. -/
theorem sourceAffine_welfare_and_weighted_optimality_sqrt_quadratic
    {rho budget lowerSkill skillWidth : ℝ} {unmeasurableSkill : ℝ → ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hbudget : 1 ≤ budget)
    (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hskill : ContinuousOn unmeasurableSkill (Icc 0 1))
    (hskill_mono : StrictMonoOn unmeasurableSkill (Icc 0 1))
    (hskill_zero : 0 ≤ unmeasurableSkill 0) :
    AntitoneOn (sourceTwoLevelApplicantWelfare (fun e => e ^ 2) Real.sqrt
      (fun t => lowerSkill + skillWidth * t) 1 rho) (Ioc (0 : ℝ) (1 - rho)) ∧
    ∀ c ∈ Ioo (0 : ℝ) (1 - rho), ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceSkillConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt (fun t => lowerSkill + skillWidth * t) budget 1 rho beta d ≤
      sourceSkillConditionalSchoolUtility unitRankMeasure unmeasurableSkill
        (fun e => e ^ 2) Real.sqrt (fun t => lowerSkill + skillWidth * t) budget 1 rho beta c := by
  have hmean := unitRankMeasure_skill_integrable_and_mean_pos hskill hskill_mono hskill_zero
  have hsquare : ConcaveOn ℝ (Ioo 0 budget) (fun e => (Real.sqrt e) ^ 2) :=
    (concaveOn_id (convex_Ioo _ _)).congr (fun e he => (Real.sq_sqrt he.1.le).symm)
  have hssecond : ContinuousOn (fun e => -1 / (4 * (Real.sqrt e) ^ 3)) (Ioo 0 budget) :=
    continuousOn_const.div
      (continuousOn_const.mul (Real.continuous_sqrt.continuousOn.pow 3))
      (fun e he => mul_ne_zero (by norm_num) (pow_ne_zero 3 (Real.sqrt_pos.mpr he.1).ne'))
  have hgeo : ConcaveOn ℝ {z : ℝ | 0 < Real.exp z ∧ Real.exp z ≤ Real.sqrt 1}
      (fun z => Real.log ((effortIntervalInverse Real.sqrt 1 (Real.exp z)) ^ 2)) := by
    have hD : {z : ℝ | 0 < Real.exp z ∧ Real.exp z ≤ Real.sqrt 1} = Iic 0 := by
      ext z
      simp only [Real.sqrt_one, mem_setOf_eq, Real.exp_pos, true_and,
        Real.exp_le_one_iff, mem_Iic]
    rw [hD]
    apply ((concaveOn_id (convex_Iic (0 : ℝ))).smul (by norm_num : (0 : ℝ) ≤ 4)).congr
    intro z hz
    dsimp only
    rw [effortIntervalInverse_sqrt_one ⟨(Real.exp_pos z).le, Real.exp_le_one_iff.mpr hz⟩]
    simp only [Real.log_pow, Real.log_exp, id_eq]
    ring
  apply sourceAffine_welfare_and_weighted_optimality_of_geometricCost
    (costDeriv := fun e => 2 * e) (costSecondDeriv := fun _ => 2)
    (productionDeriv := fun e => 1 / (2 * Real.sqrt e))
    (productionSecondDeriv := fun e => -1 / (4 * (Real.sqrt e) ^ 3))
    unitRankMeasure hmean.1 hmean.2 hrho hrho_one hlower hwidth (by norm_num) hbudget
    (continuous_pow 2).continuousOn
    (fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0))
    (by norm_num) (by norm_num)
    ((convexOn_pow 2).subset Icc_subset_Ici_self (convex_Icc _ _)) _ _
    Real.continuous_sqrt.continuousOn
    (Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self) (by norm_num)
    (Real.strictConcaveOn_sqrt.concaveOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    hsquare (fun e he => Real.hasDerivAt_sqrt he.1.ne')
    (fun e he => sqrt_marginal_hasDerivAt he.1) hssecond hgeo
  · intro e _
    convert (hasDerivAt_id e).pow 2 using 1
    norm_num [id_eq]
  · intro e _
    simpa using (hasDerivAt_id e).const_mul 2

end LBG22StrategicRanking
