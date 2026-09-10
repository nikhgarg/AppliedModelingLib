import LBG22StrategicRanking.FinitePopulationUtilityPrimitiveRepairs
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# A three-level improvement under the source primitives

Quadratic effort cost, linear production, and the cubic skill quantile give
an actual three-band equilibrium that improves on deterministic admission.
Every band has positive mass. The example keeps the same population, cost,
technology, and tie order under both policies.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Three positive-mass bands, with cutoffs one quarter and three quarters. -/
noncomputable def threeLevelQuadraticCutoff : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 3 / 4
  | _ => 1

/-- Rejection, admission with probability one half, and certain admission. -/
noncomputable def threeLevelQuadraticReward (k : ℕ) : ℝ := (k : ℝ) / 2

theorem threeLevelQuadraticCutoff_strictMono :
    StrictMonoOn threeLevelQuadraticCutoff (Icc (0 : ℕ) 3) := by
  intro i hi j hj hij
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by have := hi.2; have := hj.2; omega
  have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by have := hj.2; omega
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
    first | omega | norm_num [threeLevelQuadraticCutoff]

theorem threeLevelQuadraticReward_strictMono : StrictMono threeLevelQuadraticReward := by
  intro i j hij
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr (Nat.cast_lt.mpr hij)

theorem cubicSkill_strictMono : StrictMono (fun t : ℝ => t ^ 3) :=
  (show Odd (3 : ℕ) by decide).strictMono_pow

theorem quadraticCost_strictConvex : StrictConvexOn ℝ (Ici 0) (fun e : ℝ => e ^ 2) :=
  strictConvexOn_pow (by norm_num : 2 ≤ (2 : ℕ))

theorem quadraticCost_strictMono : StrictMonoOn (fun e : ℝ => e ^ 2) (Ici 0) :=
  sourceCost_strictMonoOn_of_strictConvex quadraticCost_strictConvex
    (fun _ _ => sq_nonneg _) (by norm_num)

theorem quadraticCost_unit_inverse : effortIntervalInverse (fun e : ℝ => e ^ 2) 1 1 = 1 := by
  have hm : StrictMonoOn (fun e : ℝ => e ^ 2) (Icc 0 1) :=
    quadraticCost_strictMono.mono Icc_subset_Ici_self
  simpa using hm.injOn.leftInvOn_invFunOn (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

theorem sourceCostAtScore_quadratic_linear {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    sourceCostAtScore (fun e => e ^ 2) id 1 z = z ^ 2 := by
  have h := sourceEffortAtScore_spec (production := id) (effortMax := 1)
    (by norm_num) continuousOn_id (monotone_id.monotoneOn _) hz.2
  simp only [id_eq, max_eq_left hz.1] at h
  change (sourceEffortAtScore id 1 z) ^ 2 = z ^ 2
  rw [h.2]

/-- Recursive boundary scores for the quadratic-cost, cubic-skill witness. -/
noncomputable def threeLevelQuadraticThreshold : ℕ → ℝ :=
  sourceRecursiveBandScore (fun e => e ^ 2) id 1
    (fun k => (threeLevelQuadraticCutoff k) ^ 3) threeLevelQuadraticReward

/-- The upper band's score already suffices for the strict utility comparison.
Its boundary cost includes a reward increment of one half, hence its effort
exceeds two thirds. No exact square-root expression is required. -/
theorem threeLevelQuadraticThreshold_top_gt : 9 / 32 < threeLevelQuadraticThreshold 2 := by
  have hskill (k : ℕ) (hk : k ∈ Icc (1 : ℕ) 2) : 0 < (threeLevelQuadraticCutoff k) ^ 3 := by
    have hk' : k = 1 ∨ k = 2 := by have := hk.1; have := hk.2; omega
    rcases hk' with rfl | rfl <;> norm_num [threeLevelQuadraticCutoff]
  have hskillM : MonotoneOn (fun k => (threeLevelQuadraticCutoff k) ^ 3) (Icc (1 : ℕ) 2) := by
    intro i hi j hj hij
    exact cubicSkill_strictMono.monotone (threeLevelQuadraticCutoff_strictMono.monotoneOn
      ⟨Nat.zero_le _, by have := hi.2; omega⟩ ⟨Nat.zero_le _, by have := hj.2; omega⟩ hij)
  have hs := sourceRecursiveBandScore_properties
    (cost := fun e : ℝ => e ^ 2) (production := id) (effortMax := 1) (n := 2)
    (by norm_num) (continuous_pow 2).continuousOn
    (quadraticCost_strictMono.mono Icc_subset_Ici_self) (by norm_num) (by norm_num)
    continuousOn_id (strictMono_id.strictMonoOn _) (by norm_num) hskill hskillM
    (threeLevelQuadraticReward_strictMono.strictMonoOn _) (by norm_num [threeLevelQuadraticReward])
    (by norm_num [threeLevelQuadraticReward])
  have h1 := hs 0 (by norm_num)
  have h2 := hs 1 (by norm_num)
  have hsk2 : (threeLevelQuadraticCutoff 2) ^ 3 = (27 / 64 : ℝ) := by norm_num [threeLevelQuadraticCutoff]
  have hr1 : threeLevelQuadraticReward 1 = 1 / 2 := by norm_num [threeLevelQuadraticReward]
  have hr2 : threeLevelQuadraticReward 2 = 1 := by norm_num [threeLevelQuadraticReward]
  have hT1 : 0 < threeLevelQuadraticThreshold 1 := by
    have h := h1.1
    change max 0 (0 * (threeLevelQuadraticCutoff 1) ^ 3) < threeLevelQuadraticThreshold 1 at h
    simpa only [zero_mul, max_self] using h
  have hT2 : 0 < threeLevelQuadraticThreshold 2 :=
    hT1.trans ((le_max_left _ _).trans_lt h2.1)
  have hup : threeLevelQuadraticThreshold 2 ≤ 27 / 64 := by
    simpa only [Nat.reduceAdd, hsk2, id_eq, one_mul] using h2.2.1
  have hz : threeLevelQuadraticThreshold 2 / (27 / 64) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hT2.le (by norm_num), (div_le_one (by norm_num : (0 : ℝ) < 27 / 64)).mpr hup⟩
  have hcost : 1 / 2 ≤ (threeLevelQuadraticThreshold 2 / (27 / 64)) ^ 2 := by
    have heq := h2.2.2.1
    simp only [Nat.reduceAdd, hsk2, hr2, hr1] at heq
    change sourceCostAtScore (fun e => e ^ 2) id 1 (threeLevelQuadraticThreshold 2 / (27 / 64)) =
      sourceCostAtScore (fun e => e ^ 2) id 1 (threeLevelQuadraticThreshold 1 / (27 / 64)) + (1 - 1 / 2) at heq
    rw [sourceCostAtScore_quadratic_linear hz] at heq
    have hn : 0 ≤ sourceCostAtScore (fun e => e ^ 2) id 1 (threeLevelQuadraticThreshold 1 / (27 / 64)) := sq_nonneg _
    linarith
  have hzlarge : 2 / 3 < threeLevelQuadraticThreshold 2 / (27 / 64) := by
    by_contra hn
    have hle := le_of_not_gt hn
    have hmul := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ (2 / 3 : ℝ) + threeLevelQuadraticThreshold 2 / (27 / 64) by linarith [hz.1])
    nlinarith
  linarith

/-- Proposition 3.3 has a nondegenerate source-admissible witness. Both
policies have actual measurable equilibrium profiles, uniform post-effort
ranks, capacity one half, and integrable private utility. The three-level
policy's utility strictly exceeds deterministic admission's `1/16`. -/
theorem threeLevelQuadraticEquilibrium_improves_deterministic
    (tie : ℝ → ℝ) (htie : Measurable tie) (hinj : InjOn tie (Ioc (0 : ℝ) 1)) :
    let effort3 := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
      threeLevelQuadraticCutoff threeLevelQuadraticReward
    let score3 := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
      threeLevelQuadraticCutoff threeLevelQuadraticReward
    let effortD := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
      (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
    let scoreD := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
      (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
    let cuts3 := fun i : Fin 3 => threeLevelQuadraticCutoff i
    let cutsD := fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i
    let rewardD := sourceTwoLevelReward (1 / 2) (1 / 2)
    AEMeasurable effort3 unitRankMeasure ∧ Measurable score3 ∧
    AEMeasurable effortD unitRankMeasure ∧ Measurable scoreD ∧
    (∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt (fun e => e ^ 2) id (fun t => t ^ 3) score3 tie cuts3 threeLevelQuadraticReward t (effort3 t)) ∧
    (∀ᵐ t ∂unitRankMeasure,
      SourceFiniteBestResponseAt (fun e => e ^ 2) id (fun t => t ^ 3) scoreD tie cutsD rewardD t (effortD t)) ∧
    Measure.map (tieBrokenRank unitRankMeasure score3 tie) unitRankMeasure = volume.restrict (Icc (0 : ℝ) 1) ∧
    Measure.map (tieBrokenRank unitRankMeasure scoreD tie) unitRankMeasure = volume.restrict (Icc (0 : ℝ) 1) ∧
    (∫ t, threeLevelQuadraticReward (finiteLowerRankBand cuts3 (tieBrokenRank unitRankMeasure score3 tie t)).val
      ∂unitRankMeasure) = 1 / 2 ∧
    (∫ t, rewardD (finiteLowerRankBand cutsD (tieBrokenRank unitRankMeasure scoreD tie t)).val
      ∂unitRankMeasure) = 1 / 2 ∧
    Integrable (fun t => score3 t * threeLevelQuadraticReward
      (finiteLowerRankBand cuts3 (tieBrokenRank unitRankMeasure score3 tie t)).val) unitRankMeasure ∧
    Integrable (fun t => scoreD t * rewardD
      (finiteLowerRankBand cutsD (tieBrokenRank unitRankMeasure scoreD tie t)).val) unitRankMeasure ∧
    sourceFiniteSchoolUtility scoreD tie cutsD rewardD = 1 / 16 ∧
    sourceFiniteSchoolUtility scoreD tie cutsD rewardD < sourceFiniteSchoolUtility score3 tie cuts3 threeLevelQuadraticReward := by
  let effort3 := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
    threeLevelQuadraticCutoff threeLevelQuadraticReward
  let score3 := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 2
    threeLevelQuadraticCutoff threeLevelQuadraticReward
  let effortD := sourceFiniteRankEffort (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
    (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
  let scoreD := sourceFiniteRankScore (fun e => e ^ 2) id (fun t => t ^ 3) 1 1
    (sourceTwoLevelCutoff (1 / 2)) (sourceTwoLevelReward (1 / 2) (1 / 2))
  let cuts3 := fun i : Fin 3 => threeLevelQuadraticCutoff i
  let cutsD := fun i : Fin 2 => sourceTwoLevelCutoff (1 / 2) i
  let rewardD := sourceTwoLevelReward (1 / 2) (1 / 2)
  have hcD := sourceTwoLevelCutoff_strictMono (c := 1 / 2) (by norm_num)
  have hrD := sourceTwoLevelReward_strictMono (rho := 1 / 2) (c := 1 / 2) (by norm_num) (by norm_num)
  have h3 := sourceFiniteRankEffort_equilibrium_at_unitCost
    (cost := fun e : ℝ => e ^ 2) (production := id) (skill := fun t => t ^ 3)
    (E := 1) (n := 2) (cutoff := threeLevelQuadraticCutoff) (reward := threeLevelQuadraticReward)
    (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex
    (fun _ _ => sq_nonneg _) (by norm_num) (by norm_num)
    continuousOn_id (strictMono_id.strictMonoOn _) (concaveOn_id (convex_Ici _)) (by norm_num)
    threeLevelQuadraticCutoff_strictMono (by norm_num [threeLevelQuadraticCutoff])
    (by norm_num [threeLevelQuadraticCutoff]) (continuous_pow 3).continuousOn
    (cubicSkill_strictMono.strictMonoOn _) (by norm_num)
    (threeLevelQuadraticReward_strictMono.strictMonoOn _) (by norm_num [threeLevelQuadraticReward])
    (by norm_num [threeLevelQuadraticReward]) htie
  have hD := sourceFiniteRankEffort_equilibrium_at_unitCost
    (cost := fun e : ℝ => e ^ 2) (production := id) (skill := fun t => t ^ 3)
    (E := 1) (n := 1) (cutoff := sourceTwoLevelCutoff (1 / 2)) (reward := rewardD)
    (by norm_num) (continuous_pow 2).continuousOn quadraticCost_strictConvex
    (fun _ _ => sq_nonneg _) (by norm_num) (by norm_num)
    continuousOn_id (strictMono_id.strictMonoOn _) (concaveOn_id (convex_Ici _)) (by norm_num)
    hcD (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff])
    (continuous_pow 3).continuousOn (cubicSkill_strictMono.strictMonoOn _) (by norm_num)
    hrD (by simp [rewardD, sourceTwoLevelReward]) (by norm_num [rewardD, sourceTwoLevelReward]) htie
  have hband3 : (fun t => finiteLowerRankBand cuts3 (tieBrokenRank unitRankMeasure score3 tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand cuts3 := h3.2.2.mono (fun _ h => h.2.2)
  have hbandD : (fun t => finiteLowerRankBand cutsD (tieBrokenRank unitRankMeasure scoreD tie t)) =ᵐ[unitRankMeasure]
      finiteLowerRankBand cutsD := hD.2.2.mono (fun _ h => h.2.2)
  have hc3 := sourceFiniteAdmission_integrable_and_mean (reward := threeLevelQuadraticReward)
    threeLevelQuadraticCutoff_strictMono (by norm_num [threeLevelQuadraticCutoff])
    (by norm_num [threeLevelQuadraticCutoff]) hband3
  have hcDmean := sourceFiniteAdmission_integrable_and_mean (reward := rewardD)
    hcD (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff]) hbandD
  have hcap3 : (∫ t, threeLevelQuadraticReward (finiteLowerRankBand cuts3
      (tieBrokenRank unitRankMeasure score3 tie t)).val ∂unitRankMeasure) = 1 / 2 := by
    rw [hc3.2]
    norm_num [Fin.sum_univ_succ, threeLevelQuadraticCutoff, threeLevelQuadraticReward]
  have hcapD : (∫ t, rewardD (finiteLowerRankBand cutsD
      (tieBrokenRank unitRankMeasure scoreD tie t)).val ∂unitRankMeasure) = 1 / 2 := by
    rw [hcDmean.2]
    norm_num [Fin.sum_univ_succ, rewardD, sourceTwoLevelCutoff, sourceTwoLevelReward]
  have hu3 := sourceFiniteSchoolUtility_eq_sum_of_zero_baseline
    threeLevelQuadraticCutoff_strictMono (by norm_num [threeLevelQuadraticCutoff])
    (by norm_num [threeLevelQuadraticCutoff]) (by rfl : id (0 : ℝ) = 0) hband3
  have huD := sourceFiniteSchoolUtility_eq_sum_of_zero_baseline
    hcD (by simp [sourceTwoLevelCutoff]) (by norm_num [sourceTwoLevelCutoff]) (by rfl : id (0 : ℝ) = 0) hbandD
  have hU3 : sourceFiniteSchoolUtility score3 tie cuts3 threeLevelQuadraticReward =
      (1 / 4) * max (threeLevelQuadraticThreshold 1) 0 + (1 / 4) * max (threeLevelQuadraticThreshold 2) 0 := by
    rw [hu3.2]
    change (∑ i : Fin 3, (threeLevelQuadraticCutoff (i.val + 1) - threeLevelQuadraticCutoff i.val) *
      (max (threeLevelQuadraticThreshold i.val) 0 * threeLevelQuadraticReward i.val)) = _
    norm_num [Fin.sum_univ_succ, threeLevelQuadraticCutoff, threeLevelQuadraticReward]
    ring
  have hscale : sourceScoreScale (fun e => e ^ 2) id 1 (1 / 2) (1 / 2) = 1 := by
    unfold sourceScoreScale
    norm_num only [show (1 / 2 : ℝ) / (1 - 1 / 2) = 1 by norm_num, quadraticCost_unit_inverse, id_eq]
  have hTD : sourceRecursiveBandScore (fun e => e ^ 2) id 1
      (fun k => (sourceTwoLevelCutoff (1 / 2) k) ^ 3) rewardD 1 = 1 / 8 := by
    have h := sourceRecursiveBandScore_twoLevel (cost := fun e : ℝ => e ^ 2) (production := id)
      (skill := fun t => t ^ 3) (E := 1) (rho := 1 / 2) (c := 1 / 2)
      (by norm_num) (by norm_num) (strictMono_id.strictMonoOn _) (by norm_num)
    simpa only [hscale, one_mul, show (1 / 2 : ℝ) ^ 3 = 1 / 8 by norm_num] using h
  have hUD : sourceFiniteSchoolUtility scoreD tie cutsD rewardD = 1 / 16 := by
    rw [huD.2]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    rw [hTD]
    norm_num [sourceTwoLevelCutoff, sourceTwoLevelReward, rewardD]
  have hstrict : sourceFiniteSchoolUtility scoreD tie cutsD rewardD <
      sourceFiniteSchoolUtility score3 tie cuts3 threeLevelQuadraticReward := by
    rw [hUD, hU3]
    have htop := (threeLevelQuadraticThreshold_top_gt).trans_le (le_max_left _ 0)
    have hbottom := le_max_right (threeLevelQuadraticThreshold 1) 0
    linarith
  haveI := noAtoms_map_tie_of_injOn_unitRank htie hinj
  exact ⟨h3.1, h3.2.1, hD.1, hD.2.1, h3.2.2.mono (fun _ h => h.2.1), hD.2.2.mono (fun _ h => h.2.1),
    tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure h3.2.1 htie,
    tieBrokenRank_map_eq_uniform_of_noAtoms_tie unitRankMeasure hD.2.1 htie,
    hcap3, hcapD, hu3.1, huD.1, hUD, hstrict⟩

end LBG22StrategicRanking
