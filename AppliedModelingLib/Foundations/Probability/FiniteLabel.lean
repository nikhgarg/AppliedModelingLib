import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Optimization.Argmax

open MeasureTheory
open scoped BigOperators

namespace AppliedModelingLib

/-!
# Finite-Label Probability Utilities

Reusable measure-theoretic wrappers for papers with a finite label/action
space: posterior score vectors, label shares, indicator integrals, aggregate
posterior mass, and bounded finite-label integrability dischargers.
-/

/-- Finite PMF expectations satisfy the abstract finite-linearity interface. -/
theorem pmfExp_finiteLinearExpectation
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : PMF Ω) :
    Decision.FiniteLinearExpectation (pmfExp μ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g h
    exact pmfExp_le_pmfExp_of_forall_le μ f g h
  · intro c f
    exact pmfExp_const_mul μ c f
  · intro f g
    exact pmfExp_add μ f g

theorem pmfExp_monotoneExpectation
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : PMF Ω) :
    Decision.MonotoneExpectation (pmfExp μ) :=
  (pmfExp_finiteLinearExpectation μ).monotone

/-- Indicator for the event that a finite label-valued map selects `y`. -/
noncomputable def finiteLabelIndicator {α Y : Type*} [DecidableEq Y]
    (label : α → Y) (y : Y) (a : α) : ℝ :=
  if label a = y then 1 else 0

/-- Measure share of a finite label under an arbitrary measure. -/
noncomputable def finiteLabelShare {α Y : Type*} [MeasurableSpace α] [DecidableEq Y]
    (μ : Measure α) (label : α → Y) (y : Y) : ℝ :=
  ∫ a, finiteLabelIndicator label y a ∂μ

/-- Aggregate score mass for one finite label. -/
noncomputable def finiteLabelAggregateScore
    {α Y : Type*} [MeasurableSpace α]
    (μ : Measure α) (score : α → Y → ℝ) (y : Y) : ℝ :=
  ∫ a, score a y ∂μ

/-- Pointwise finite-label posterior simplex. -/
def FiniteLabelSimplex {α Y : Type*} [Fintype Y] (score : α → Y → ℝ) : Prop :=
  (∀ a, (∑ y : Y, score a y) = 1) ∧
    (∀ a y, 0 ≤ score a y)

/-- A simplex coordinate is at most one. -/
theorem finiteLabelSimplex_coord_le_one
    {α Y : Type*} [Fintype Y] (score : α → Y → ℝ)
    (a : α) (y : Y)
    (hsum : (∑ z : Y, score a z) = 1)
    (hnonneg : ∀ z : Y, 0 ≤ score a z) :
    score a y ≤ 1 := by
  have hy_mem : y ∈ (Finset.univ : Finset Y) := Finset.mem_univ y
  have hle_sum : score a y ≤ ∑ z : Y, score a z :=
    Finset.single_le_sum (fun z _ => hnonneg z) hy_mem
  simpa [hsum] using hle_sum

theorem FiniteLabelSimplex.coord_le_one
    {α Y : Type*} [Fintype Y] {score : α → Y → ℝ}
    (h : FiniteLabelSimplex score) (a : α) (y : Y) :
    score a y ≤ 1 :=
  finiteLabelSimplex_coord_le_one score a y (h.1 a) (fun z => h.2 a z)

/-- Measurability of a finite-label indicator. -/
theorem measurable_finiteLabelIndicator
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [DecidableEq Y]
    {label : α → Y} (hlabel : Measurable label) (y : Y) :
    Measurable (finiteLabelIndicator label y) := by
  classical
  let S : Set α := {a | label a = y}
  have hS : MeasurableSet S := hlabel (measurableSet_singleton y)
  have hmeas : Measurable (S.indicator (fun _ : α => (1 : ℝ))) :=
    measurable_const.indicator hS
  have hfun : S.indicator (fun _ : α => (1 : ℝ)) =
      finiteLabelIndicator label y := by
    funext a
    by_cases h : label a = y <;> simp [S, finiteLabelIndicator, Set.indicator, h]
  rw [← hfun]
  exact hmeas

/-- Finite-label indicators are integrable under finite measures. -/
theorem integrable_finiteLabelIndicator_of_measurable_finite
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [DecidableEq Y]
    (μ : Measure α) [IsFiniteMeasure μ]
    {label : α → Y} (hlabel : Measurable label) (y : Y) :
    Integrable (finiteLabelIndicator label y) μ := by
  refine Integrable.of_bound
    ((measurable_finiteLabelIndicator hlabel y).aestronglyMeasurable) 1 ?_
  filter_upwards with a
  by_cases h : label a = y <;> simp [finiteLabelIndicator, h]

/-- Label shares are event probabilities in real-measure form. -/
theorem finiteLabelShare_eq_measureProb
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [DecidableEq Y]
    (μ : Measure α) {label : α → Y} (hlabel : Measurable label) (y : Y) :
    finiteLabelShare μ label y = measureProb μ (fun a => label a = y) := by
  classical
  let S : Set α := {a | label a = y}
  have hS : MeasurableSet S := hlabel (measurableSet_singleton y)
  have hfun : S.indicator (fun _ : α => (1 : ℝ)) =
      finiteLabelIndicator label y := by
    funext a
    by_cases h : label a = y <;> simp [S, finiteLabelIndicator, Set.indicator, h]
  unfold finiteLabelShare
  rw [← hfun]
  simpa [measureProb, Measure.real, S] using
    (MeasureTheory.integral_indicator_one (μ := μ) hS)

/-- The finite-label indicators across all labels sum to one pointwise. -/
theorem sum_finiteLabelIndicator_eq_one
    {α Y : Type*} [Fintype Y] [DecidableEq Y]
    (label : α → Y) (a : α) :
    (∑ y : Y, finiteLabelIndicator label y a) = 1 := by
  classical
  rw [Finset.sum_eq_single (label a)]
  · simp [finiteLabelIndicator]
  · intro y _hy hy_ne
    simp [finiteLabelIndicator, hy_ne.symm]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ (label a)))

/-- Label shares over all finite labels sum to total real mass. -/
theorem sum_finiteLabelShare_eq_measureReal_univ
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure α) [IsFiniteMeasure μ]
    {label : α → Y} (hlabel : Measurable label) :
    (∑ y : Y, finiteLabelShare μ label y) = μ.real Set.univ := by
  classical
  calc
    (∑ y : Y, finiteLabelShare μ label y)
        = ∫ a, ∑ y : Y, finiteLabelIndicator label y a ∂μ := by
            unfold finiteLabelShare
            symm
            exact MeasureTheory.integral_finset_sum
              (s := (Finset.univ : Finset Y))
              (f := fun y a => finiteLabelIndicator label y a)
              (fun y _ => integrable_finiteLabelIndicator_of_measurable_finite μ hlabel y)
    _ = ∫ _a, (1 : ℝ) ∂μ := by
            congr 1
            funext a
            exact sum_finiteLabelIndicator_eq_one label a
    _ = μ.real Set.univ := by
            simpa using
              (MeasureTheory.setIntegral_one_eq_measureReal
                (μ := μ) (s := (Set.univ : Set α)))

/-- Bounded score coordinates are integrable under finite measures. -/
theorem integrable_finiteLabelScore_of_bounds_finite
    {α Y : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (score : α → Y → ℝ) (y : Y)
    (hmeas : AEStronglyMeasurable (fun a : α => score a y) μ)
    (hnonneg : ∀ a, 0 ≤ score a y)
    (hle_one : ∀ a, score a y ≤ 1) :
    Integrable (fun a : α => score a y) μ := by
  refine Integrable.of_bound hmeas 1 ?_
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg a)]
  exact hle_one a

/-- Measurable bounded score coordinates are integrable under finite measures. -/
theorem integrable_finiteLabelScore_of_measurable_bounds_finite
    {α Y : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (score : α → Y → ℝ) (y : Y)
    (hmeas : Measurable (fun a : α => score a y))
    (hnonneg : ∀ a, 0 ≤ score a y)
    (hle_one : ∀ a, score a y ≤ 1) :
    Integrable (fun a : α => score a y) μ :=
  integrable_finiteLabelScore_of_bounds_finite μ score y
    hmeas.aestronglyMeasurable hnonneg hle_one

/-- Aggregate score masses over a pointwise simplex sum to total real mass. -/
theorem sum_finiteLabelAggregateScore_eq_measureReal_univ_of_simplex
    {α Y : Type*} [MeasurableSpace α] [Fintype Y]
    (μ : Measure α) [IsFiniteMeasure μ]
    (score : α → Y → ℝ)
    (hscore : ∀ y : Y, Integrable (fun a : α => score a y) μ)
    (hsum : ∀ a, (∑ y : Y, score a y) = 1) :
    (∑ y : Y, finiteLabelAggregateScore μ score y) = μ.real Set.univ := by
  classical
  calc
    (∑ y : Y, finiteLabelAggregateScore μ score y)
        = ∫ a, ∑ y : Y, score a y ∂μ := by
            unfold finiteLabelAggregateScore
            symm
            exact MeasureTheory.integral_finset_sum
              (s := (Finset.univ : Finset Y))
              (f := fun y a => score a y)
              (fun y _ => hscore y)
    _ = ∫ _a, (1 : ℝ) ∂μ := by
            congr 1
            funext a
            exact hsum a
    _ = μ.real Set.univ := by
            simpa using
              (MeasureTheory.setIntegral_one_eq_measureReal
                (μ := μ) (s := (Set.univ : Set α)))

/-- Aggregate score masses over a measurable bounded simplex sum to total real mass. -/
theorem sum_finiteLabelAggregateScore_eq_measureReal_univ_of_measurable_simplex
    {α Y : Type*} [MeasurableSpace α] [Fintype Y]
    (μ : Measure α) [IsFiniteMeasure μ]
    (score : α → Y → ℝ)
    (hmeas : ∀ y : Y, Measurable (fun a : α => score a y))
    (hsimplex : FiniteLabelSimplex score) :
    (∑ y : Y, finiteLabelAggregateScore μ score y) = μ.real Set.univ :=
  sum_finiteLabelAggregateScore_eq_measureReal_univ_of_simplex μ score
    (fun y =>
      integrable_finiteLabelScore_of_measurable_bounds_finite μ score y
        (hmeas y) (fun a => hsimplex.2 a y)
        (fun a => hsimplex.coord_le_one a y))
    hsimplex.1

/-- Conditional MAE contribution of a finite-label score vector. -/
noncomputable def finiteLabelClassifierMAE {α Y : Type*} [Fintype Y]
    (score : α → Y → ℝ) (a : α) : ℝ :=
  ∑ y : Y, score a y * (1 - score a y)

/-- Finite-label MAE is nonnegative for simplex-valued scores. -/
theorem finiteLabelClassifierMAE_nonneg_of_simplex
    {α Y : Type*} [Fintype Y]
    (score : α → Y → ℝ) (a : α)
    (hsimplex : FiniteLabelSimplex score) :
    0 ≤ finiteLabelClassifierMAE score a := by
  classical
  unfold finiteLabelClassifierMAE
  refine Finset.sum_nonneg ?_
  intro y _
  exact mul_nonneg (hsimplex.2 a y)
    (sub_nonneg.mpr (hsimplex.coord_le_one a y))

/-- Finite-label MAE is bounded by the number of labels for `[0,1]` scores. -/
theorem norm_finiteLabelClassifierMAE_le_card_of_bounds
    {α Y : Type*} [Fintype Y] (score : α → Y → ℝ) (a : α)
    (hnonneg : ∀ y : Y, 0 ≤ score a y)
    (hle_one : ∀ y : Y, score a y ≤ 1) :
    ‖finiteLabelClassifierMAE score a‖ ≤ (Fintype.card Y : ℝ) := by
  classical
  have hnonneg_mae : 0 ≤ finiteLabelClassifierMAE score a := by
    unfold finiteLabelClassifierMAE
    refine Finset.sum_nonneg ?_
    intro y _
    exact mul_nonneg (hnonneg y) (sub_nonneg.mpr (hle_one y))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_mae]
  unfold finiteLabelClassifierMAE
  calc
    (∑ y : Y, score a y * (1 - score a y)) ≤ ∑ _y : Y, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro y _
      have hsub_nonneg : 0 ≤ 1 - score a y := sub_nonneg.mpr (hle_one y)
      have hsub_le_one : 1 - score a y ≤ 1 := by linarith [hnonneg y]
      simpa using
        (mul_le_mul (hle_one y) hsub_le_one hsub_nonneg
          (by norm_num : (0 : ℝ) ≤ 1))
    _ = (Fintype.card Y : ℝ) := by simp

/-- Simplex-valued finite-label MAE is bounded by one. -/
theorem norm_finiteLabelClassifierMAE_le_one_of_simplex
    {α Y : Type*} [Fintype Y] (score : α → Y → ℝ) (a : α)
    (hsimplex : FiniteLabelSimplex score) :
    ‖finiteLabelClassifierMAE score a‖ ≤ 1 := by
  classical
  have hnonneg_mae : 0 ≤ finiteLabelClassifierMAE score a :=
    finiteLabelClassifierMAE_nonneg_of_simplex score a hsimplex
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_mae]
  unfold finiteLabelClassifierMAE
  calc
    (∑ y : Y, score a y * (1 - score a y)) ≤ ∑ y : Y, score a y := by
      refine Finset.sum_le_sum ?_
      intro y _
      have hsub_le_one : 1 - score a y ≤ 1 := by linarith [hsimplex.2 a y]
      simpa using mul_le_mul_of_nonneg_left hsub_le_one (hsimplex.2 a y)
    _ = 1 := hsimplex.1 a

/-- Measurability of finite-label MAE from measurable score coordinates. -/
theorem measurable_finiteLabelClassifierMAE_of_scores
    {α Y : Type*} [MeasurableSpace α] [Fintype Y]
    (score : α → Y → ℝ)
    (hscore : ∀ y : Y, Measurable (fun a : α => score a y)) :
    Measurable (finiteLabelClassifierMAE score) := by
  classical
  unfold finiteLabelClassifierMAE
  exact Finset.measurable_sum Finset.univ (fun y _ =>
    (hscore y).mul (measurable_const.sub (hscore y)))

/-- Simplex-valued finite-label MAE is integrable under finite measures. -/
theorem integrable_finiteLabelClassifierMAE_of_measurable_simplex_finite
    {α Y : Type*} [MeasurableSpace α] [Fintype Y]
    (μ : Measure α) [IsFiniteMeasure μ]
    (score : α → Y → ℝ)
    (hscore : ∀ y : Y, Measurable (fun a : α => score a y))
    (hsimplex : FiniteLabelSimplex score) :
    Integrable (finiteLabelClassifierMAE score) μ := by
  refine Integrable.of_bound
    ((measurable_finiteLabelClassifierMAE_of_scores score hscore).aestronglyMeasurable)
    1 ?_
  filter_upwards with a
  exact norm_finiteLabelClassifierMAE_le_one_of_simplex score a hsimplex

end AppliedModelingLib
