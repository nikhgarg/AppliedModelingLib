import LBG22StrategicRanking.EnvironmentPrimitiveRepairs
import LBG22StrategicRanking.MultitaskPrimitiveRepairs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Endogenous-total effort under linear multidimensional production

An applicant chooses every nonnegative effort coordinate, paying the cost
of their sum. The combined skill is the largest weighted coordinate skill.
Best responses, rather than a fixed-budget assumption, imply that positive
effort is spent only on coordinates attaining that maximum.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The source combined pre-effort index, formed from weighted skill levels. -/
noncomputable def sourceCombinedSkill {ι : Type*} [Fintype ι] [Nonempty ι]
    (coefficient : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty coefficient

theorem le_sourceCombinedSkill {ι : Type*} [Fintype ι] [Nonempty ι]
    (coefficient : ι → ℝ) (i : ι) : coefficient i ≤ sourceCombinedSkill coefficient :=
  Finset.le_sup' coefficient (Finset.mem_univ i)

theorem sourceCombinedSkill_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    (coefficient : ι → ℝ) : ∃ i, coefficient i = sourceCombinedSkill coefficient := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty coefficient
  exact ⟨i, hi.symm⟩

theorem measurable_sourceCombinedSkill
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]
    {coefficient : α → ι → ℝ} (hc : ∀ i, Measurable (fun x => coefficient x i)) :
    Measurable (fun x => sourceCombinedSkill (coefficient x)) := by
  have hcont : Continuous (fun v : ι → ℝ => sourceCombinedSkill v) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)
  exact hcont.measurable.comp (measurable_pi_lambda _ hc)

/-- Actual best response over all nonnegative effort vectors. Total effort
cost and production may depend on the vector and scalar effort respectively,
as in the general multidimensional model before the linear specialization. -/
def SourceVectorBestResponseAt
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (cost : (ι → ℝ) → ℝ)
    (production : ℝ → ℝ) (coefficient : α → ι → ℝ)
    (score tie : α → ℝ) (reward : ℝ → ℝ) (x : α) (effort : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ effort i) ∧ score x = ∑ i, production (effort i) * coefficient x i ∧
    ∀ d : ι → ℝ, (∀ i, 0 ≤ d i) →
      reward (counterfactualTieBrokenRank μ score tie x
        (∑ i, production (d i) * coefficient x i)) - cost d ≤
        reward (tieBrokenRank μ score tie x) - cost effort

/-- Actual best response over all nonnegative effort vectors. Total effort
is a choice variable, not a common budget imposed on applicants or deviations. -/
def SourceMultidimensionalBestResponseAt
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (cost : ℝ → ℝ) (coefficient : α → ι → ℝ)
    (score tie : α → ℝ) (h : ℝ) (reward : ℝ → ℝ) (x : α) (effort : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ effort i) ∧ score x = h * ∑ i, effort i * coefficient x i ∧
    ∀ d : ι → ℝ, (∀ i, 0 ≤ d i) →
      reward (counterfactualTieBrokenRank μ score tie x (h * ∑ i, d i * coefficient x i)) - cost (∑ i, d i) ≤
        reward (tieBrokenRank μ score tie x) - cost (∑ i, effort i)

/-- Linear production and exchangeable effort cost specialize the general
vector game without changing its feasible deviations, ranking, or payoffs. -/
theorem sourceMultidimensionalBestResponseAt_iff_vector
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (cost : ℝ → ℝ) (coefficient : α → ι → ℝ)
    (score tie : α → ℝ) (h : ℝ) (reward : ℝ → ℝ) (x : α) (effort : ι → ℝ) :
    SourceMultidimensionalBestResponseAt μ cost coefficient score tie h reward x effort ↔
      SourceVectorBestResponseAt μ (fun d => cost (∑ i, d i)) (fun e => h * e)
        coefficient score tie reward x effort := by
  simp only [SourceMultidimensionalBestResponseAt, SourceVectorBestResponseAt,
    Finset.mul_sum, mul_assoc]

/-- At any best response, the actual score attains the maximum available
at its chosen total effort. If it did not, concentrating a smaller total
on a best coordinate would keep exactly the same rank and strictly reduce
cost. No convexity or monotonicity of the reward is needed for this step. -/
theorem sourceMultidimensionalBestResponse_score_eq
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure α) [IsFiniteMeasure μ]
    {cost reward : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ}
    {h : ℝ} {x : α} {effort : ι → ℝ}
    (hh : 0 < h) (hp : StrictMonoOn cost (Ici 0))
    (hc : ∀ i, 0 ≤ coefficient x i) (hm : 0 < sourceCombinedSkill (coefficient x))
    (hb : SourceMultidimensionalBestResponseAt μ cost coefficient score tie h reward x effort) :
    score x = h * (∑ i, effort i) * sourceCombinedSkill (coefficient x) := by
  let m := sourceCombinedSkill (coefficient x)
  let total := ∑ i, effort i
  have ht : 0 ≤ total := Finset.sum_nonneg (fun i _ => hb.1 i)
  have hscore0 : 0 ≤ score x := by
    rw [hb.2.1]
    exact mul_nonneg hh.le (Finset.sum_nonneg (fun i _ => mul_nonneg (hb.1 i) (hc i)))
  have hscorele : score x ≤ h * total * m := by
    rw [hb.2.1]
    have hs := multidim_linear_effort_score_le_total_mul_max effort (coefficient x) hb.1 rfl
      (le_sourceCombinedSkill (coefficient x))
    exact (mul_le_mul_of_nonneg_left hs hh.le).trans_eq (mul_assoc _ _ _).symm
  apply le_antisymm hscorele
  by_contra hn
  have hlt : score x < h * total * m := lt_of_not_ge hn
  obtain ⟨best, hbest⟩ := sourceCombinedSkill_attained (coefficient x)
  let d := score x / (h * m)
  have hd : 0 ≤ d := div_nonneg hscore0 (mul_pos hh hm).le
  have hdt : d < total := (div_lt_iff₀ (mul_pos hh hm)).mpr (by nlinarith)
  let deviation := fun i => if i = best then d else 0
  have hdev : ∀ i, 0 ≤ deviation i := by intro i; dsimp [deviation]; split <;> positivity
  have hsum : (∑ i, deviation i) = d := by simp [deviation]
  have hval : h * (∑ i, deviation i * coefficient x i) = score x := by
    rw [multidim_linear_effort_single_best_attains_total_mul_max best (coefficient x) hbest]
    dsimp only [d, m]
    field_simp
  have h := hb.2.2 deviation hdev
  rw [hsum, hval, counterfactualTieBrokenRank_at_current_score] at h
  have hc := hp hd ht hdt
  linarith

/-- Positive effort is supported only on maximum weighted skills. Splitting
effort among tied maxima is permitted and has exactly the same score. -/
theorem sourceMultidimensionalBestResponse_support
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure α) [IsFiniteMeasure μ]
    {cost reward : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ}
    {h : ℝ} {x : α} {effort : ι → ℝ}
    (hh : 0 < h) (hp : StrictMonoOn cost (Ici 0))
    (hc : ∀ i, 0 ≤ coefficient x i) (hm : 0 < sourceCombinedSkill (coefficient x))
    (hb : SourceMultidimensionalBestResponseAt μ cost coefficient score tie h reward x effort) :
    ∀ i, 0 < effort i → coefficient x i = sourceCombinedSkill (coefficient x) := by
  have hs := sourceMultidimensionalBestResponse_score_eq μ hh hp hc hm hb
  rw [hb.2.1, mul_assoc] at hs
  have hsum := (mul_left_cancel₀ hh.ne') hs
  have hzero : (∑ i, effort i * (sourceCombinedSkill (coefficient x) - coefficient x i)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, sub_self]
  have hnonneg (i : ι) : 0 ≤ effort i * (sourceCombinedSkill (coefficient x) - coefficient x i) :=
    mul_nonneg (hb.1 i) (sub_nonneg.mpr (le_sourceCombinedSkill _ i))
  intro i hi
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hzero i (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hi0).resolve_left hi.ne')).symm

/-- An actual multidimensional best response induces a scalar best response
against every nonnegative total effort, with linear production and skill
equal to the maximum weighted coordinate. -/
theorem sourceScalarBestResponseAt_of_multidimensional
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure α) [IsFiniteMeasure μ]
    {cost : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ} {h : ℝ}
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ} {reward : ℕ → ℝ} {x : α} {effort : ι → ℝ}
    (hh : 0 < h) (hp : StrictMonoOn cost (Ici 0))
    (hc : ∀ i, 0 ≤ coefficient x i) (hm : 0 < sourceCombinedSkill (coefficient x))
    (hb : SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x effort) :
    SourcePopulationFiniteBestResponseAt μ cost (fun e => h * e)
      (fun x => sourceCombinedSkill (coefficient x)) score tie cutoff reward x (∑ i, effort i) := by
  refine ⟨Finset.sum_nonneg (fun i _ => hb.1 i),
    sourceMultidimensionalBestResponse_score_eq μ hh hp hc hm hb, ?_⟩
  intro d hd
  obtain ⟨best, hbest⟩ := sourceCombinedSkill_attained (coefficient x)
  have hdev : ∀ i : ι, 0 ≤ (if i = best then d else 0) := by intro i; split <;> positivity
  have h := hb.2.2 (fun i => if i = best then d else 0) hdev
  rw [multidim_linear_effort_single_best_attains_total_mul_max best (coefficient x) hbest] at h
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_pos, mul_assoc] using h

/-- Conversely, a scalar best response can be allocated in any way among
the maximum weighted coordinates. The resulting vector defeats every
nonnegative vector deviation, including those with a different total effort. -/
theorem sourceMultidimensionalBestResponseAt_of_scalar
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]
    (μ : Measure α) [IsFiniteMeasure μ]
    {cost : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ} {h : ℝ}
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ} {reward : ℕ → ℝ} {x : α} {effort : ι → ℝ}
    (hh : 0 ≤ h) (hr : MonotoneOn reward (Icc (0 : ℕ) n))
    (he : ∀ i, 0 ≤ effort i)
    (hsupport : ∀ i, 0 < effort i → coefficient x i = sourceCombinedSkill (coefficient x))
    (hb : SourcePopulationFiniteBestResponseAt μ cost (fun e => h * e)
      (fun x => sourceCombinedSkill (coefficient x)) score tie cutoff reward x (∑ i, effort i)) :
    SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x effort := by
  have hsum : (∑ i, effort i * coefficient x i) = (∑ i, effort i) * sourceCombinedSkill (coefficient x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rcases eq_or_lt_of_le (he i) with hi | hi
    · rw [← hi, zero_mul, zero_mul]
    · rw [hsupport i hi]
  refine ⟨he, by rw [hsum, ← mul_assoc]; exact hb.2.1, ?_⟩
  intro d hd
  have hbound := multidim_linear_effort_score_le_total_mul_max d (coefficient x) hd rfl
    (le_sourceCombinedSkill (coefficient x))
  have hscorebound : h * (∑ i, d i * coefficient x i) ≤ h * (∑ i, d i) * sourceCombinedSkill (coefficient x) :=
    (mul_le_mul_of_nonneg_left hbound hh).trans_eq (mul_assoc _ _ _).symm
  have hreward := (monotone_finiteLowerRankReward cutoff hr)
    (counterfactualTieBrokenRank_monotone μ score tie x hscorebound)
  exact (sub_le_sub_right hreward _).trans (hb.2.2 _ (Finset.sum_nonneg (fun i _ => hd i)))

/-- Exact reduction of the endogenous-total game: a vector is a best
response precisely when it is feasible, uses only maximal coordinates,
and its total is a best response in the scalar maximum-index game. -/
theorem sourceMultidimensionalBestResponseAt_iff_scalar
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure α) [IsFiniteMeasure μ]
    {cost : ℝ → ℝ} {coefficient : α → ι → ℝ} {score tie : α → ℝ} {h : ℝ}
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ} {reward : ℕ → ℝ} {x : α} {effort : ι → ℝ}
    (hh : 0 < h) (hp : StrictMonoOn cost (Ici 0))
    (hc : ∀ i, 0 ≤ coefficient x i) (hm : 0 < sourceCombinedSkill (coefficient x))
    (hr : MonotoneOn reward (Icc (0 : ℕ) n)) :
    SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x effort ↔
    (∀ i, 0 ≤ effort i) ∧
    (∀ i, 0 < effort i → coefficient x i = sourceCombinedSkill (coefficient x)) ∧
    SourcePopulationFiniteBestResponseAt μ cost (fun e => h * e)
      (fun x => sourceCombinedSkill (coefficient x)) score tie cutoff reward x (∑ i, effort i) := by
  constructor
  · intro hb
    exact ⟨hb.1, sourceMultidimensionalBestResponse_support μ hh hp hc hm hb,
      sourceScalarBestResponseAt_of_multidimensional μ hh hp hc hm hb⟩
  · rintro ⟨he, hs, hb⟩
    exact sourceMultidimensionalBestResponseAt_of_scalar μ hh.le hr he hs hb

/-- In any actual multidimensional equilibrium, reward bands agree with
the CDF rank of the maximum weighted skill. Both the scalar incentive
problem and the pre-rank distribution are derived; no fixed total effort,
source-ordered score profile, or desired band identity is supplied. -/
theorem sourceMultidimensionalEquilibrium_rank_preservation
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {cost : ℝ → ℝ} {coefficient effort : α → ι → ℝ} {score tie : α → ℝ} {h : ℝ}
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ} {reward : ℕ → ℝ}
    (hh : 0 < h)
    (hpcont : ContinuousOn cost (Ici 0)) (hpM : StrictMonoOn cost (Ici 0))
    (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hc : ∀ i, Measurable (fun x => coefficient x i))
    (hc0 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ coefficient x i)
    (hm : ∀ᵐ x ∂μ, 0 < sourceCombinedSkill (coefficient x))
    [NoAtoms (Measure.map (fun x => sourceCombinedSkill (coefficient x)) μ)]
    [NoAtoms (Measure.map tie μ)]
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hscore : Measurable score) (htie : Measurable tie)
    (hbest : ∀ᵐ x ∂μ, SourceMultidimensionalBestResponseAt μ cost coefficient score tie h
      (fun r => reward (finiteLowerRankBand cutoff r).val) x (effort x)) :
    (fun x => finiteLowerRankBand cutoff (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => finiteLowerRankBand cutoff
        (cdf (Measure.map (fun x => sourceCombinedSkill (coefficient x)) μ)
          (sourceCombinedSkill (coefficient x)))) := by
  have hscalar : ∀ᵐ x ∂μ, SourcePopulationFiniteBestResponseAt μ cost (fun e => h * e)
      (fun x => sourceCombinedSkill (coefficient x)) score tie cutoff reward x (∑ i, effort x i) := by
    filter_upwards [hc0, hm, hbest] with x hx hm hb
    exact sourceScalarBestResponseAt_of_multidimensional μ hh hpM hx hm hb
  exact sourcePopulationFiniteEquilibrium_rank_preservation_of_convex_cost μ cutoff
    hpcont hpM hpconv (continuous_const.mul continuous_id).continuousOn
    (fun _ _ _ _ hab => mul_lt_mul_of_pos_left hab hh)
    ((concaveOn_id (convex_Ici (0 : ℝ))).smul hh.le) (by simp)
    (measurable_sourceCombinedSkill hc) hm hr hscore htie hscalar

/-- The source draws each skill rank independently and uniformly. -/
noncomputable def sourceMultidimensionalPopulation (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => unitRankMeasure)

instance sourceMultidimensionalPopulation_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (sourceMultidimensionalPopulation ι) := by
  unfold sourceMultidimensionalPopulation
  infer_instance

theorem sourceMultidimensionalPopulation_ae_mem (ι : Type*) [Fintype ι] :
    ∀ᵐ x ∂sourceMultidimensionalPopulation ι, ∀ i, x i ∈ Ioc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : ι => unitRankMeasure) i).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ioc)

/-- Weighted source skills, extended by clamping outside their unit-rank
domain. The extension agrees with the source on the full population support. -/
noncomputable def sourceMultidimensionalCoefficient {ι : Type*}
    (weight : ι → ℝ) (skill : ι → ℝ → ℝ) (rank : ι → ℝ) (i : ι) : ℝ :=
  weight i * sourceClampedSkill (skill i) (rank i)

theorem sourceMultidimensionalCoefficient_eq {ι : Type*}
    {weight : ι → ℝ} {skill : ι → ℝ → ℝ} {rank : ι → ℝ} {i : ι}
    (hi : rank i ∈ Icc (0 : ℝ) 1) :
    sourceMultidimensionalCoefficient weight skill rank i = weight i * skill i (rank i) := by
  rw [sourceMultidimensionalCoefficient, sourceClampedSkill_eq hi]

theorem sourceMultidimensionalCoefficient_measurable {ι : Type*}
    {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hf : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1)) (i : ι) :
    Measurable (fun rank => sourceMultidimensionalCoefficient weight skill rank i) :=
  measurable_const.mul ((continuous_sourceClampedSkill (hf i)).measurable.comp (measurable_pi_apply i))

/-- Every positively weighted skill has a nonatomic marginal. Zero-weight
coordinates are allowed; they need not satisfy this statement. -/
theorem sourceMultidimensionalCoefficient_noAtoms
    {ι : Type*} [Fintype ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) {i : ι} (hi : 0 < weight i) :
    NoAtoms (Measure.map (fun rank => sourceMultidimensionalCoefficient weight skill rank i)
      (sourceMultidimensionalPopulation ι)) := by
  let f := fun t => weight i * sourceClampedSkill (skill i) t
  have hm : Measurable f := measurable_const.mul (continuous_sourceClampedSkill (hfcont i)).measurable
  have hmap : Measure.map (fun rank => sourceMultidimensionalCoefficient weight skill rank i)
      (sourceMultidimensionalPopulation ι) = Measure.map f unitRankMeasure := by
    change Measure.map (f ∘ Function.eval i) (Measure.pi (fun _ : ι => unitRankMeasure)) = _
    rw [← Measure.map_map hm (measurable_pi_apply i), (measurePreserving_eval _ i).map_eq]
  rw [hmap]
  apply noAtoms_map_tie_of_injOn_unitRank hm
  intro x hx y hy hxy
  dsimp only [f] at hxy
  rw [sourceClampedSkill_eq ⟨hx.1.le, hx.2⟩, sourceClampedSkill_eq ⟨hy.1.le, hy.2⟩] at hxy
  exact (hf i).injOn ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ ((mul_left_cancel₀ hi.ne') hxy)

/-- Simplex weights and positive source skills make the maximum weighted
skill positive almost everywhere, including weights on the simplex boundary. -/
theorem sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0) :
    ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      (∀ i, 0 ≤ sourceMultidimensionalCoefficient weight skill rank i) ∧
      0 < sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank) := by
  have hwp : ∃ i, 0 < weight i := by
    by_contra hn
    push Not at hn
    have hz : ∑ i, weight i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hn i) (hw i))
    linarith
  obtain ⟨j, hj⟩ := hwp
  filter_upwards [sourceMultidimensionalPopulation_ae_mem ι] with rank hr
  have hskill (i : ι) : 0 < skill i (rank i) :=
    (hf0 i).trans_lt (hf i (by norm_num) ⟨(hr i).1.le, (hr i).2⟩ (hr i).1)
  constructor
  · intro i
    rw [sourceMultidimensionalCoefficient_eq ⟨(hr i).1.le, (hr i).2⟩]
    exact mul_nonneg (hw i) (hskill i).le
  · have hjpos : 0 < sourceMultidimensionalCoefficient weight skill rank j := by
      rw [sourceMultidimensionalCoefficient_eq ⟨(hr j).1.le, (hr j).2⟩]
      exact mul_pos hj (hskill j)
    exact hjpos.trans_le (le_sourceCombinedSkill _ j)

/-- The maximum weighted skill has no atoms under the source population.
At a positive maximum some positively weighted coordinate attains it, and
each such equality has zero measure. No atomlessness assumption on the
combined index is added to the source primitives. -/
theorem sourceMultidimensionalIndex_noAtoms
    {ι : Type*} [Fintype ι] [Nonempty ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0) :
    NoAtoms (Measure.map (fun rank => sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank))
      (sourceMultidimensionalPopulation ι)) := by
  let coefficient := sourceMultidimensionalCoefficient weight skill
  have hm := measurable_sourceCombinedSkill (sourceMultidimensionalCoefficient_measurable (weight := weight) hfcont)
  constructor
  intro z
  rw [Measure.map_apply hm (measurableSet_singleton z)]
  have hne : ∀ᵐ rank ∂sourceMultidimensionalPopulation ι, sourceCombinedSkill (coefficient rank) ≠ z := by
    by_cases hz : 0 < z
    · have hcoordinate (i : ι) : ∀ᵐ rank ∂sourceMultidimensionalPopulation ι, coefficient rank i ≠ z := by
        by_cases hi : weight i = 0
        · exact Filter.Eventually.of_forall (fun rank => by
            simpa only [coefficient, sourceMultidimensionalCoefficient, hi, zero_mul] using hz.ne)
        · haveI := sourceMultidimensionalCoefficient_noAtoms hfcont hf (lt_of_le_of_ne (hw i) (Ne.symm hi))
          have hn := measure_singleton (μ := Measure.map (fun rank => coefficient rank i)
            (sourceMultidimensionalPopulation ι)) z
          rw [Measure.map_apply (sourceMultidimensionalCoefficient_measurable hfcont i)
            (measurableSet_singleton z)] at hn
          apply ae_iff.mpr
          simpa only [mem_preimage, mem_singleton_iff, not_not] using hn
      filter_upwards [ae_all_iff.mpr hcoordinate] with rank hr
      obtain ⟨i, hi⟩ := sourceCombinedSkill_attained (coefficient rank)
      intro heq
      exact hr i (hi.trans heq)
    · filter_upwards [sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos hw hw1 hf hf0] with rank hr
      intro heq
      exact hz (heq ▸ hr.2)
  simpa only [mem_preimage, mem_singleton_iff, not_not] using ae_iff.mp hne

/-- The rank of the combined index in the actual independent skill law. -/
noncomputable def sourceMultidimensionalPreRank
    {ι : Type*} [Fintype ι] [Nonempty ι] (weight : ι → ℝ) (skill : ι → ℝ → ℝ) (rank : ι → ℝ) : ℝ :=
  cdf (Measure.map (fun x => sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill x))
    (sourceMultidimensionalPopulation ι))
      (sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank))

theorem sourceMultidimensionalPreRank_uniform
    {ι : Type*} [Fintype ι] [Nonempty ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0) :
    Measure.map (sourceMultidimensionalPreRank weight skill) (sourceMultidimensionalPopulation ι) =
      unitRankMeasure := by
  let index := fun rank => sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank)
  have hm : Measurable index := measurable_sourceCombinedSkill (sourceMultidimensionalCoefficient_measurable hfcont)
  haveI := sourceMultidimensionalIndex_noAtoms hw hw1 hfcont hf hf0
  haveI := Measure.isProbabilityMeasure_map (μ := sourceMultidimensionalPopulation ι) hm.aemeasurable
  have h := AppliedModelingLib.Probability.map_cdf_eq_uniform_of_noAtoms
    (Measure.map index (sourceMultidimensionalPopulation ι))
  rw [Measure.map_map (monotone_cdf _).measurable hm] at h
  exact h.trans restrict_Ioc_eq_restrict_Icc.symm

/-- Source-primitive realization of the multidimensional rank-preservation
recovery. The independent uniform skill draws, simplex weights, and source
quantiles imply positivity and atomlessness of the maximum index. Every
actual best-response vector reduces to its endogenous scalar total. The
conclusion preserves reward bands, not the printed impossible strict
reward/index equivalence within a constant-reward band. -/
theorem sourceMultidimensionalEquilibrium_of_sourcePrimitives
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {weight : ι → ℝ} {skill : ι → ℝ → ℝ} {cost : ℝ → ℝ}
    {effort : (ι → ℝ) → ι → ℝ} {score tie : (ι → ℝ) → ℝ} {h : ℝ}
    {n : ℕ} {cutoff : Fin (n + 1) → ℝ} {reward : ℕ → ℝ}
    (hh : 0 < h) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hpcont : ContinuousOn cost (Ici 0)) (hpM : StrictMonoOn cost (Ici 0))
    (hpconv : ConvexOn ℝ (Ici 0) cost)
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0)
    (hr : StrictMonoOn reward (Icc (0 : ℕ) n)) (hscore : Measurable score) (htie : Measurable tie)
    (hinj : InjOn tie {rank | ∀ i, rank i ∈ Ioc (0 : ℝ) 1})
    (hbest : ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      SourceMultidimensionalBestResponseAt (sourceMultidimensionalPopulation ι) cost
        (sourceMultidimensionalCoefficient weight skill) score tie h
        (fun r => reward (finiteLowerRankBand cutoff r).val) rank (effort rank)) :
    Measure.map (sourceMultidimensionalPreRank weight skill) (sourceMultidimensionalPopulation ι) =
      unitRankMeasure ∧
    ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      (∀ i, 0 < effort rank i → sourceMultidimensionalCoefficient weight skill rank i =
        sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank)) ∧
      finiteLowerRankBand cutoff (tieBrokenRank (sourceMultidimensionalPopulation ι) score tie rank) =
        finiteLowerRankBand cutoff (sourceMultidimensionalPreRank weight skill rank) := by
  haveI : NoAtoms unitRankMeasure := by unfold unitRankMeasure; infer_instance
  haveI : NoAtoms (sourceMultidimensionalPopulation ι) := by unfold sourceMultidimensionalPopulation; infer_instance
  haveI := noAtoms_map_tie_of_injOn_fullMeasure htie hinj (sourceMultidimensionalPopulation_ae_mem ι)
  haveI := sourceMultidimensionalIndex_noAtoms hw hw1 hfcont hf hf0
  have hpositive := sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos hw hw1 hf hf0
  have hrank := sourceMultidimensionalEquilibrium_rank_preservation (sourceMultidimensionalPopulation ι)
    hh hpcont hpM hpconv (sourceMultidimensionalCoefficient_measurable hfcont)
    (hpositive.mono fun _ hx => hx.1) (hpositive.mono fun _ hx => hx.2) hr hscore htie hbest
  refine ⟨sourceMultidimensionalPreRank_uniform hw hw1 hfcont hf hf0, ?_⟩
  filter_upwards [hpositive, hbest, hrank] with rank hx hb hr
  exact ⟨sourceMultidimensionalBestResponse_support _ hh hpM hx.1 hx.2 hb, hr⟩

/-- A positively weighted coordinate almost surely differs from every
other coordinate: independence turns a possible equality into a singleton
event in its nonatomic marginal. The other weight may be zero. -/
theorem sourceMultidimensionalCoefficient_distinct_ae
    {ι : Type*} [Fintype ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1))
    {i j : ι} (hij : i ≠ j) (hi : 0 < weight i) :
    ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      sourceMultidimensionalCoefficient weight skill rank i ≠ sourceMultidimensionalCoefficient weight skill rank j := by
  let coefficient := sourceMultidimensionalCoefficient weight skill
  let μ := sourceMultidimensionalPopulation ι
  have hm (k : ι) : Measurable (fun rank => coefficient rank k) :=
    sourceMultidimensionalCoefficient_measurable hfcont k
  haveI := Measure.isProbabilityMeasure_map (μ := μ) (hm i).aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := μ) (hm j).aemeasurable
  haveI := sourceMultidimensionalCoefficient_noAtoms hfcont hf hi
  have hindep : iIndepFun (fun k rank => coefficient rank k) μ :=
    iIndepFun_pi (fun k => (measurable_const.mul (continuous_sourceClampedSkill (hfcont k)).measurable).aemeasurable)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hm i).aemeasurable (hm j).aemeasurable).mp
    (hindep.indepFun hij)
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  have hz : ((Measure.map (fun rank => coefficient rank i) μ).prod
      (Measure.map (fun rank => coefficient rank j) μ)) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply_symm hdiag]
    simp
  rw [← hmap, Measure.map_apply ((hm i).prodMk (hm j)) hdiag] at hz
  apply ae_iff.mpr
  simpa only [mem_preimage, mem_setOf_eq, not_not] using hz

/-- Under the source independent skill draws, a maximum coordinate is
unique almost everywhere. This remains true on the boundary of the weight
simplex, since zero coefficients cannot attain a positive maximum. -/
theorem sourceMultidimensionalIndex_unique_max_ae
    {ι : Type*} [Fintype ι] [Nonempty ι] {weight : ι → ℝ} {skill : ι → ℝ → ℝ}
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0) :
    ∀ᵐ rank ∂sourceMultidimensionalPopulation ι, ∃! i,
      sourceMultidimensionalCoefficient weight skill rank i =
        sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank) := by
  have hpair (i j : ι) : ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      i ≠ j → 0 < weight i → sourceMultidimensionalCoefficient weight skill rank i ≠
        sourceMultidimensionalCoefficient weight skill rank j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    by_cases hi : 0 < weight i
    · exact (sourceMultidimensionalCoefficient_distinct_ae hfcont hf hij hi).mono (fun _ h _ _ => h)
    · exact Filter.Eventually.of_forall (fun _ _ h => (hi h).elim)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i)),
    sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos hw hw1 hf hf0] with rank hr hp
  obtain ⟨best, hb⟩ := sourceCombinedSkill_attained (sourceMultidimensionalCoefficient weight skill rank)
  have hwb : 0 < weight best := by
    apply lt_of_le_of_ne (hw best)
    intro hn
    have hz : sourceMultidimensionalCoefficient weight skill rank best = 0 := by
      simp only [sourceMultidimensionalCoefficient, ← hn, zero_mul]
    exact hp.2.ne' (hb.symm.trans hz)
  refine ⟨best, hb, ?_⟩
  intro j hj
  by_contra hn
  exact hr best j (Ne.symm hn) hwb (hb.trans hj.symm)

/-- The source single-skill effort conclusion follows almost everywhere
from independent skill draws and actual vector best responses. The chosen
total is endogenous; neither a fixed budget nor a one-coordinate action
restriction is assumed. -/
theorem sourceMultidimensionalBestResponses_single_coordinate_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {weight : ι → ℝ} {skill : ι → ℝ → ℝ} {cost reward : ℝ → ℝ}
    {effort : (ι → ℝ) → ι → ℝ} {score tie : (ι → ℝ) → ℝ} {h : ℝ}
    (hh : 0 < h) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hpM : StrictMonoOn cost (Ici 0))
    (hfcont : ∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1))
    (hf : ∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) (hf0 : ∀ i, 0 ≤ skill i 0)
    (hbest : ∀ᵐ rank ∂sourceMultidimensionalPopulation ι,
      SourceMultidimensionalBestResponseAt (sourceMultidimensionalPopulation ι) cost
        (sourceMultidimensionalCoefficient weight skill) score tie h reward rank (effort rank)) :
    ∀ᵐ rank ∂sourceMultidimensionalPopulation ι, ∃ best : ι,
      sourceMultidimensionalCoefficient weight skill rank best =
        sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill rank) ∧
      ∀ i, effort rank i = if i = best then ∑ j, effort rank j else 0 := by
  filter_upwards [hbest, sourceMultidimensionalIndex_unique_max_ae hw hw1 hfcont hf hf0,
    sourceMultidimensionalCoefficient_ae_nonneg_and_max_pos hw hw1 hf hf0] with rank hb hmax hp
  obtain ⟨best, hbest, hunique⟩ := hmax
  have hsupport := sourceMultidimensionalBestResponse_support _ hh hpM hp.1 hp.2 hb
  have hzero (i : ι) (hi : i ≠ best) : effort rank i = 0 := by
    apply le_antisymm _ (hb.1 i)
    by_contra hn
    exact hi (hunique i (hsupport i (lt_of_not_ge hn)))
  have hsum : ∑ i, effort rank i = effort rank best :=
    Finset.sum_eq_single best (fun i _ hi => hzero i hi) (by simp)
  refine ⟨best, hbest, ?_⟩
  intro i
  by_cases hi : i = best
  · rw [if_pos hi, hi, hsum]
  · rw [if_neg hi, hzero i hi]

end LBG22StrategicRanking
