import LBG22StrategicRanking.MultidimensionalPrimitiveRepairs
import LBG22StrategicRanking.MultitaskExamples
import LBG22StrategicRanking.FinitePopulationUtilityPrimitiveRepairs

/-!
# Two positively weighted skills with endogenous effort

Two independent uniform skills receive equal positive school weights.
The maximum index has a square CDF and square-root quantile. Linear
production and quadratic total cost give a nontrivial two-level equilibrium
family, with effort directed to whichever skill is larger.
-/

namespace LBG22StrategicRanking.MultidimensionalExample

open Set MeasureTheory ProbabilityTheory

noncomputable def weight (_ : Fin 2) : ℝ := 1 / 2
def skill (_ : Fin 2) : ℝ → ℝ := id
noncomputable def coefficient := sourceMultidimensionalCoefficient weight skill
noncomputable def index (x : Fin 2 → ℝ) := sourceCombinedSkill (coefficient x)
noncomputable def preRank := sourceMultidimensionalPreRank weight skill
noncomputable def quantile (r : ℝ) := Real.sqrt r / 2

theorem weight_spec : (∀ i, 0 ≤ weight i) ∧ ∑ i, weight i = 1 := by
  constructor <;> norm_num [weight, Fin.sum_univ_two]

theorem index_measurable : Measurable index :=
  measurable_sourceCombinedSkill (sourceMultidimensionalCoefficient_measurable
    (fun _ => continuous_id.continuousOn))

theorem preRank_measurable : Measurable preRank := (monotone_cdf _).measurable.comp index_measurable

theorem preRank_uniform : Measure.map preRank (sourceMultidimensionalPopulation (Fin 2)) = unitRankMeasure :=
  sourceMultidimensionalPreRank_uniform weight_spec.1 weight_spec.2
    (fun _ => continuous_id.continuousOn) (fun _ => strictMono_id.strictMonoOn _) (by intro i; norm_num [skill])

theorem index_eq {x : Fin 2 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    index x = max (x 0) (x 1) / 2 := by
  have hcoeff (i : Fin 2) : coefficient x i = x i / 2 := by
    rw [coefficient, sourceMultidimensionalCoefficient_eq (hx i)]
    dsimp [weight, skill]
    ring
  have hmax : index x = max (coefficient x 0) (coefficient x 1) := by
    apply le_antisymm
    · change Finset.univ.sup' Finset.univ_nonempty (coefficient x) ≤ _
      apply Finset.sup'_le Finset.univ_nonempty
      intro i _
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    · exact max_le (le_sourceCombinedSkill _ 0) (le_sourceCombinedSkill _ 1)
  rw [hmax, hcoeff, hcoeff, ← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]

/-- The actual index CDF is computed from the independent skill law. -/
theorem index_cdf {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    cdf (Measure.map index (sourceMultidimensionalPopulation (Fin 2))) (a / 2) = a ^ 2 := by
  haveI := Measure.isProbabilityMeasure_map (μ := sourceMultidimensionalPopulation (Fin 2)) index_measurable.aemeasurable
  rw [cdf_eq_real, measureReal_def, Measure.map_apply index_measurable measurableSet_Iic]
  have hset : index ⁻¹' Iic (a / 2) =ᵐ[sourceMultidimensionalPopulation (Fin 2)]
      (Set.pi Set.univ (fun _ : Fin 2 => Iic a) : Set (Fin 2 → ℝ)) := by
    filter_upwards [sourceMultidimensionalPopulation_ae_mem (Fin 2)] with x hx
    apply propext
    change index x ≤ a / 2 ↔ ∀ i ∈ (Set.univ : Set (Fin 2)), x i ∈ Iic a
    simp only [mem_univ, forall_const, mem_Iic]
    rw [index_eq (fun i => ⟨(hx i).1.le, (hx i).2⟩)]
    simp only [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2), max_le_iff, Fin.forall_fin_two]
  rw [measure_congr hset, sourceMultidimensionalPopulation, Measure.pi_pi,
    Fin.prod_univ_two, ENNReal.toReal_mul, unitRankMeasure_Iic ha]
  ring

theorem preRank_eq {x : Fin 2 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    preRank x = (max (x 0) (x 1)) ^ 2 := by
  change cdf (Measure.map index (sourceMultidimensionalPopulation (Fin 2))) (index x) = _
  rw [index_eq hx, index_cdf ⟨(hx 0).1.trans (le_max_left _ _), max_le (hx 0).2 (hx 1).2⟩]

theorem quantile_preRank {x : Fin 2 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    quantile (preRank x) = index x := by
  rw [quantile, preRank_eq hx, index_eq hx,
    Real.sqrt_sq ((hx 0).1.trans (le_max_left _ _))]

noncomputable def tie (x : Fin 2 → ℝ) := MultitaskExample.tie (x 0, x 1)
noncomputable def best (x : Fin 2 → ℝ) : Fin 2 := if x 0 ≤ x 1 then 1 else 0
noncomputable def totalEffort (c : ℝ) (x : Fin 2 → ℝ) :=
  sourceFiniteRankEffort (fun e => e ^ 2) id quantile 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward (1 / 4) c) (preRank x)
noncomputable def score (c : ℝ) (x : Fin 2 → ℝ) :=
  sourceFiniteRankScore (fun e => e ^ 2) id quantile 1 1
    (sourceTwoLevelCutoff c) (sourceTwoLevelReward (1 / 4) c) (preRank x)
noncomputable def effort (c : ℝ) (x : Fin 2 → ℝ) (i : Fin 2) :=
  if i = best x then totalEffort c x else 0

theorem tie_spec : Measurable tie ∧ Function.Injective tie ∧ ∀ x, tie x ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨MultitaskExample.tie_spec.1.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)), ?_,
    fun x => MultitaskExample.tie_spec.2.2 _⟩
  intro x y hxy
  have h := MultitaskExample.tie_spec.2.1 hxy
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem best_measurable : Measurable best :=
  measurable_const.piecewise (measurableSet_le (measurable_pi_apply 0) (measurable_pi_apply 1)) measurable_const

theorem best_coefficient {x : Fin 2 → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    coefficient x (best x) = index x := by
  rw [coefficient, sourceMultidimensionalCoefficient_eq (hx (best x)), index_eq hx]
  dsimp only [weight, skill, id_eq]
  unfold best
  split_ifs with h
  · rw [max_eq_right h]
    ring
  · rw [max_eq_left (le_of_not_ge h)]
    ring

theorem effort_sum (c : ℝ) (x : Fin 2 → ℝ) : ∑ i, effort c x i = totalEffort c x := by
  simp [effort]

/-- Every feasible two-level cutoff has an actual equilibrium in the
two-positive-weight game. All nonnegative effort-vector deviations are
checked; the total varies across types and policies. -/
theorem actual_equilibrium_family {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) :
    (Measurable (score c) ∧ AEMeasurable (totalEffort c) (sourceMultidimensionalPopulation (Fin 2)) ∧
      ∀ i, AEMeasurable (fun x => effort c x i) (sourceMultidimensionalPopulation (Fin 2))) ∧
    ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin 2),
      SourceMultidimensionalBestResponseAt (sourceMultidimensionalPopulation (Fin 2))
        (fun e => e ^ 2) coefficient (score c) tie 1
        (fun r => sourceTwoLevelReward (1 / 4) c
          (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) r).val) x (effort c x) ∧
      (c < tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie x ↔ c < preRank x) := by
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  haveI : NoAtoms (sourceMultidimensionalPopulation (Fin 2)) := by unfold sourceMultidimensionalPopulation; infer_instance
  haveI := noAtoms_map_tie_of_injOn_fullMeasure tie_spec.1 tie_spec.2.1.injOn
    (sourceMultidimensionalPopulation_ae_mem (Fin 2))
  have hqcont : ContinuousOn quantile (Icc (0 : ℝ) 1) := (Real.continuous_sqrt.div_const 2).continuousOn
  have hqmono : StrictMonoOn quantile (Icc (0 : ℝ) 1) := fun a ha b hb hab =>
    div_lt_div_of_pos_right (Real.strictMonoOn_sqrt ha.1 hb.1 hab) (by norm_num)
  have hpop := sourcePopulationTwoLevelEquilibrium_of_uniform_preRank
    (sourceMultidimensionalPopulation (Fin 2)) preRank_measurable preRank_uniform tie_spec.1
    (by norm_num : (0 : ℝ) < 1 / 4) hc (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_pow 2).continuousOn quadraticCost_strictMono (by norm_num) (by norm_num)
    (quadraticCost_strictConvex.convexOn.subset Icc_subset_Ici_self (convex_Icc _ _))
    continuous_id.continuousOn (strictMono_id.strictMonoOn _) (by norm_num)
    (concaveOn_id (convex_Icc _ _)) hqcont hqmono (by norm_num [quantile])
  have hpositive := sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos weight_spec.1 weight_spec.2
    (fun _ => strictMono_id.strictMonoOn _) (by intro i; norm_num [skill])
  have htotal : AEMeasurable (totalEffort c) (sourceMultidimensionalPopulation (Fin 2)) := by
    apply (hpop.1.div index_measurable).aemeasurable.congr
    filter_upwards [hpop.2, hpositive, sourceMultidimensionalPopulation_ae_mem (Fin 2)] with x hx hp hmem
    have hs := hx.2.1.2.1
    change score c x = totalEffort c x * quantile (preRank x) at hs
    rw [quantile_preRank (fun i => ⟨(hmem i).1.le, (hmem i).2⟩)] at hs
    change score c x / index x = totalEffort c x
    have hp' : 0 < index x := hp.2
    rw [hs, mul_div_cancel_right₀ _ hp'.ne']
  refine ⟨⟨hpop.1, htotal, ?_⟩, ?_⟩
  · intro i
    have hm := htotal.indicator (best_measurable (measurableSet_singleton i))
    apply hm.congr
    exact Filter.Eventually.of_forall (fun x => by
      change (best ⁻¹' {i}).indicator (totalEffort c) x = if i = best x then totalEffort c x else 0
      by_cases hi : i = best x
      · rw [if_pos hi, Set.indicator_of_mem (show x ∈ best ⁻¹' {i} from hi.symm)]
      · rw [if_neg hi, Set.indicator_of_notMem (show x ∉ best ⁻¹' {i} from Ne.symm hi)])
  · filter_upwards [hpop.2, sourceMultidimensionalPopulation_ae_mem (Fin 2)] with x hx hmem
    have hxx : ∀ i, x i ∈ Icc (0 : ℝ) 1 := fun i => ⟨(hmem i).1.le, (hmem i).2⟩
    have hscalar : SourcePopulationFiniteBestResponseAt (sourceMultidimensionalPopulation (Fin 2))
        (fun e => e ^ 2) (fun e => 1 * e) index (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward (1 / 4) c) x
        (∑ i, effort c x i) := by
      rw [effort_sum]
      simpa only [SourcePopulationFiniteBestResponseAt, quantile_preRank hxx, one_mul, id_eq] using hx.2.1
    refine ⟨sourceMultidimensionalBestResponseAt_of_scalar _ (by norm_num)
      (sourceTwoLevelReward_strictMono (by norm_num) (by linarith [hc.2])).monotoneOn ?_ ?_ hscalar, hx.2.2⟩
    · intro i
      dsimp [effort]
      split_ifs
      · exact hx.1.1
      · exact le_rfl
    · intro i hi
      have hib : i = best x := by
        by_contra hn
        simpa only [effort, if_neg hn, lt_self_iff_false] using hi
      rw [hib]
      exact best_coefficient hxx

/-- The actual equilibrium admission probabilities fill the prescribed
capacity, so the example is an admissible policy family for the school. -/
theorem actual_admission_capacity {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4)) :
    (∫ x, sourceTwoLevelReward (1 / 4) c
      (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie x)).val
      ∂sourceMultidimensionalPopulation (Fin 2)) = 1 / 4 := by
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  haveI : NoAtoms (sourceMultidimensionalPopulation (Fin 2)) := by unfold sourceMultidimensionalPopulation; infer_instance
  haveI := noAtoms_map_tie_of_injOn_fullMeasure tie_spec.1 tie_spec.2.1.injOn
    (sourceMultidimensionalPopulation_ae_mem (Fin 2))
  have hc1 : c < 1 := by linarith [hc.2]
  have hs := (actual_equilibrium_family hc).1.1
  have hm := measurable_tieBrokenRank (μ := sourceMultidimensionalPopulation (Fin 2)) hs tie_spec.1
  have hlaw := (tieBrokenRank_map_eq_uniform_of_noAtoms_tie (sourceMultidimensionalPopulation (Fin 2))
    hs tie_spec.1).trans restrict_Ioc_eq_restrict_Icc.symm
  have hR := monotone_finiteLowerRankReward (fun i : Fin 2 => sourceTwoLevelCutoff c i)
    (sourceTwoLevelReward_strictMono (by norm_num : (0 : ℝ) < 1 / 4) hc1).monotoneOn
  rw [← integral_map hm.aemeasurable hR.measurable.aestronglyMeasurable, hlaw]
  have hi := integral_finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelReward (1 / 4) c i.val)
    (sourceTwoLevelCutoff_strictMono ⟨hc.1, hc1⟩) (by simp [sourceTwoLevelCutoff])
    (by norm_num [sourceTwoLevelCutoff])
  have hi' := hi.2
  dsimp only at hi'
  change (∫ y, sourceTwoLevelReward (1 / 4) c
    (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i) y).val ∂unitRankMeasure) = 1 / 4
  rw [hi', Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num [sourceTwoLevelCutoff, sourceTwoLevelReward]
  field_simp [(sub_pos.mpr hc1).ne']

/-- Every positive-length pre-rank interval meets every full-measure set
of applicants. This is a property of the actual population law. -/
theorem exists_good_in_rank_interval {good : Set (Fin 2 → ℝ)}
    (hgood : ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin 2), x ∈ good)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ x ∈ good, preRank x ∈ Ioo a b := by
  by_contra hn
  push Not at hn
  have hsub : preRank ⁻¹' Ioo a b ⊆ {x | x ∉ good} := fun x hx hg => hn x hg hx
  have hzero := measure_mono_null hsub (ae_iff.mp hgood)
  have hpos : 0 < (sourceMultidimensionalPopulation (Fin 2)) (preRank ⁻¹' Ioo a b) := by
    rw [← Measure.map_apply preRank_measurable measurableSet_Ioo, preRank_uniform,
      unitRankMeasure, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (show Ioo a b ⊆ Ioc (0 : ℝ) 1 from
        fun _ hx => ⟨ha.trans_lt hx.1, hx.2.le.trans hb⟩), Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hpos.ne' hzero

/-- The printed strict reward/index equivalence fails in actual equilibria
even after discarding any null set. Distinct maximum indices in two
positive-length subintervals of the rejected band receive the same reward.
This does not contradict preservation of the reward bands. -/
theorem strict_index_reward_iff_fails_on_every_fullMeasure_set
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 - 1 / 4))
    {good : Set (Fin 2 → ℝ)} (hgood : ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin 2), x ∈ good) :
    ∃ x ∈ good, ∃ y ∈ good, index x < index y ∧
      sourceTwoLevelReward (1 / 4) c
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie x)).val =
      sourceTwoLevelReward (1 / 4) c
        (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
          (tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie y)).val := by
  let good' := {x | x ∈ good ∧
    (c < tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie x ↔ c < preRank x)}
  have hg : ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin 2), x ∈ good' := by
    filter_upwards [hgood, (actual_equilibrium_family hc).2] with x hx he
    exact ⟨hx, he.2⟩
  obtain ⟨x, hx, hxr⟩ := exists_good_in_rank_interval hg (a := 0) (b := c / 2)
    (by norm_num) (by linarith [hc.2]) (by linarith [hc.1])
  obtain ⟨y, hy, hyr⟩ := exists_good_in_rank_interval hg (a := c / 2) (b := c)
    (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.1])
  have hrank : preRank x < preRank y := hxr.2.trans hyr.1
  have hindex : index x < index y := by
    by_contra hn
    have h := (monotone_cdf (Measure.map index (sourceMultidimensionalPopulation (Fin 2)))) (le_of_not_gt hn)
    exact (not_le_of_gt hrank) h
  have hxlow : ¬c < tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie x := by
    intro h
    have h' := hx.2.mp h
    linarith [hxr.2, hc.1]
  have hylow : ¬c < tieBrokenRank (sourceMultidimensionalPopulation (Fin 2)) (score c) tie y :=
    fun h => (not_lt_of_ge hyr.2.le) (hy.2.mp h)
  refine ⟨x, hx.1, y, hy.1, hindex, ?_⟩
  rw [finiteLowerRankBand_twoLevel, finiteLowerRankBand_twoLevel, if_neg hxlow, if_neg hylow]

end LBG22StrategicRanking.MultidimensionalExample
