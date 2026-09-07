import KR21Monoculture.AppendixCTheorem7Boundaries
import KR21Monoculture.LaplaceTheorem2Definition1Transport
import KR21Monoculture.GaussianTheorem2Definition1Transport

open AppliedModelingLib Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace KR21Monoculture

/-!
# Appendix C Source Pairwise Bridges

The Appendix-C text writes raw source scores as `x + epsilon / theta`.  The
analytic Theorems 7 and 8 use named score measures instead.  This module makes
the change of variables and the strict source events explicit before exposing
the C.1 inequality.  In particular, no theorem is transported merely because
two declarations have similar names.
-/

private def pairStrictWinnerEvent : Set (ℝ × ℝ) := {p | p.2 < p.1}

private theorem pairStrictWinnerEvent_measurable :
    MeasurableSet pairStrictWinnerEvent := by
  unfold pairStrictWinnerEvent
  exact measurableSet_lt measurable_snd measurable_fst

private theorem pair_real_tie_measure_zero
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] [NoAtoms ν] :
    (μ.prod ν) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  let T : Set (ℝ × ℝ) := {p | p.1 = p.2}
  have hT_meas : MeasurableSet T :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hsection : ∀ x : ℝ, ν (Prod.mk x ⁻¹' T) = 0 := by
    intro x
    have hset : Prod.mk x ⁻¹' T = ({x} : Set ℝ) := by
      ext y
      simp [T]
    rw [hset]
    simp
  calc
    (μ.prod ν) T = ∫⁻ x, ν (Prod.mk x ⁻¹' T) ∂μ := by
      rw [Measure.prod_apply hT_meas]
    _ = ∫⁻ _x, 0 ∂μ := lintegral_congr hsection
    _ = 0 := by simp

private theorem pair_strict_winner_measure_eq_weak
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] [NoAtoms ν] :
    (μ.prod ν) pairStrictWinnerEvent =
      (μ.prod ν) {p : ℝ × ℝ | p.2 ≤ p.1} := by
  have htie : (μ.prod ν) {p : ℝ × ℝ | p.1 = p.2} = 0 :=
    pair_real_tie_measure_zero μ ν
  apply measure_congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp htie] with p hp
  unfold pairStrictWinnerEvent
  apply propext
  constructor
  · exact fun h => le_of_lt h
  · intro h
    exact lt_of_le_of_ne h (Ne.symm hp)

/-! ## Unit-variance Laplace source scores -/

/-- Two iid literal unit-variance Laplace innovations. -/
noncomputable def sourceUnitVarianceLaplacePairInnovationMeasure : Measure (ℝ × ℝ) :=
  (theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
    (theorem7LaplaceMeasure (Real.sqrt 2) 0)

/-- The two source score coordinates `x + epsilon / theta`. -/
noncomputable def sourceUnitVarianceLaplacePairScoreMap
    (theta xi xj : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun epsilon => (xi + epsilon.1 / theta, xj + epsilon.2 / theta)

theorem measurable_sourceUnitVarianceLaplacePairScoreMap
    (theta xi xj : ℝ) :
    Measurable (sourceUnitVarianceLaplacePairScoreMap theta xi xj) := by
  unfold sourceUnitVarianceLaplacePairScoreMap
  fun_prop

/-- The strict numerator event in the source's own innovation coordinates. -/
def sourceUnitVarianceLaplacePairStrictNumeratorEvent
    (theta xi xj a : ℝ) : Set (ℝ × ℝ) :=
  {epsilon |
    xi + epsilon.1 / theta < a ∧
      xj + epsilon.2 / theta < xi + epsilon.1 / theta}

/-- The strict conditioning event in the source's own innovation coordinates. -/
def sourceUnitVarianceLaplacePairStrictDenominatorEvent
    (theta xi xj a : ℝ) : Set (ℝ × ℝ) :=
  {epsilon |
    xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}

/-- The strict unconditional pairwise-winner event in source coordinates. -/
def sourceUnitVarianceLaplacePairStrictWinnerEvent
    (theta xi xj : ℝ) : Set (ℝ × ℝ) :=
  {epsilon | xj + epsilon.2 / theta < xi + epsilon.1 / theta}

theorem sourceUnitVarianceLaplacePairScoreMap_preimage_strict_numerator
    (theta xi xj a : ℝ) :
    (sourceUnitVarianceLaplacePairScoreMap theta xi xj) ⁻¹'
        theorem7LaplacianPairStrictNumeratorEvent a =
      sourceUnitVarianceLaplacePairStrictNumeratorEvent theta xi xj a := by
  rfl

theorem sourceUnitVarianceLaplacePairScoreMap_preimage_strict_denominator
    (theta xi xj a : ℝ) :
    (sourceUnitVarianceLaplacePairScoreMap theta xi xj) ⁻¹'
        theorem7LaplacianPairStrictDenominatorEvent a =
      sourceUnitVarianceLaplacePairStrictDenominatorEvent theta xi xj a := by
  rfl

theorem sourceUnitVarianceLaplacePairScoreMap_preimage_strict_winner
    (theta xi xj : ℝ) :
    (sourceUnitVarianceLaplacePairScoreMap theta xi xj) ⁻¹'
        pairStrictWinnerEvent =
      sourceUnitVarianceLaplacePairStrictWinnerEvent theta xi xj := by
  rfl

private theorem sourceUnitVarianceLaplaceMeasure_map_add_div
    {theta x : ℝ} (htheta : 0 < theta) :
    (theorem7LaplaceMeasure (Real.sqrt 2) 0).map
        (fun epsilon : ℝ => x + epsilon / theta) =
      theorem7LaplaceMeasure (Real.sqrt 2 * theta) x :=
  laplaceMeasure_map_add_div (lam := Real.sqrt 2) (theta := theta) (x := x)
    (Real.sqrt_pos.2 (by norm_num)) htheta

/-- The source pair-score map has exactly the named Laplace score law. -/
theorem sourceUnitVarianceLaplacePairScoreMap_measurePreserving
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    MeasurePreserving (sourceUnitVarianceLaplacePairScoreMap theta xi xj)
      sourceUnitVarianceLaplacePairInnovationMeasure
      (theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj) := by
  refine ⟨measurable_sourceUnitVarianceLaplacePairScoreMap theta xi xj, ?_⟩
  let μ0 : Measure ℝ := theorem7LaplaceMeasure (Real.sqrt 2) 0
  let fi : ℝ → ℝ := fun epsilon => xi + epsilon / theta
  let fj : ℝ → ℝ := fun epsilon => xj + epsilon / theta
  letI : SFinite μ0 := by
    dsimp [μ0, theorem7LaplaceMeasure]
    infer_instance
  have hfi : Measurable fi := by
    dsimp [fi]
    fun_prop
  have hfj : Measurable fj := by
    dsimp [fj]
    fun_prop
  have hpair :
      (μ0.prod μ0).map (Prod.map fi fj) =
        (μ0.map fi).prod (μ0.map fj) := by
    exact (Measure.map_prod_map μ0 μ0 hfi hfj).symm
  change (μ0.prod μ0).map (Prod.map fi fj) = _
  rw [hpair,
    sourceUnitVarianceLaplaceMeasure_map_add_div htheta,
    sourceUnitVarianceLaplaceMeasure_map_add_div htheta]
  rfl

/-- Source-coordinate strict conditional probability in equation (C.1). -/
noncomputable def sourceUnitVarianceLaplacePairConditionalRatio
    (theta xi xj a : ℝ) : ℝ :=
  (sourceUnitVarianceLaplacePairInnovationMeasure
      (sourceUnitVarianceLaplacePairStrictNumeratorEvent theta xi xj a)).toReal /
    (sourceUnitVarianceLaplacePairInnovationMeasure
      (sourceUnitVarianceLaplacePairStrictDenominatorEvent theta xi xj a)).toReal

/-- Source-coordinate unconditional strict pairwise-winner probability. -/
noncomputable def sourceUnitVarianceLaplacePairWinnerProbability
    (theta xi xj : ℝ) : ℝ :=
  (sourceUnitVarianceLaplacePairInnovationMeasure
    (sourceUnitVarianceLaplacePairStrictWinnerEvent theta xi xj)).toReal

private theorem theorem7LaplacianPairStrictDenominatorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem7LaplacianPairStrictDenominatorEvent a) := by
  unfold theorem7LaplacianPairStrictDenominatorEvent
  exact measurableSet_Iio.prod measurableSet_Iio

/-- The literal source numerator has the canonical strict-event mass. -/
theorem sourceUnitVarianceLaplacePair_strict_numerator_measure_eq
    {theta xi xj a : ℝ} (htheta : 0 < theta) :
    sourceUnitVarianceLaplacePairInnovationMeasure
        (sourceUnitVarianceLaplacePairStrictNumeratorEvent theta xi xj a) =
      theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
        (theorem7LaplacianPairStrictNumeratorEvent a) := by
  let f := sourceUnitVarianceLaplacePairScoreMap theta xi xj
  let μ := sourceUnitVarianceLaplacePairInnovationMeasure
  let ν := theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
  have hf : Measurable f :=
    measurable_sourceUnitVarianceLaplacePairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceUnitVarianceLaplacePairScoreMap_measurePreserving htheta
  calc
    μ (sourceUnitVarianceLaplacePairStrictNumeratorEvent theta xi xj a) =
        μ (f ⁻¹' theorem7LaplacianPairStrictNumeratorEvent a) := by
          rw [sourceUnitVarianceLaplacePairScoreMap_preimage_strict_numerator]
    _ = (μ.map f) (theorem7LaplacianPairStrictNumeratorEvent a) :=
      (Measure.map_apply hf
        (theorem7LaplacianPairStrictNumeratorEvent_measurable a)).symm
    _ = ν (theorem7LaplacianPairStrictNumeratorEvent a) := by
      rw [hmap.map_eq]

/-- The literal source conditioning event has the canonical strict-event mass. -/
theorem sourceUnitVarianceLaplacePair_strict_denominator_measure_eq
    {theta xi xj a : ℝ} (htheta : 0 < theta) :
    sourceUnitVarianceLaplacePairInnovationMeasure
        (sourceUnitVarianceLaplacePairStrictDenominatorEvent theta xi xj a) =
      theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
        (theorem7LaplacianPairStrictDenominatorEvent a) := by
  let f := sourceUnitVarianceLaplacePairScoreMap theta xi xj
  let μ := sourceUnitVarianceLaplacePairInnovationMeasure
  let ν := theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
  have hf : Measurable f :=
    measurable_sourceUnitVarianceLaplacePairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceUnitVarianceLaplacePairScoreMap_measurePreserving htheta
  calc
    μ (sourceUnitVarianceLaplacePairStrictDenominatorEvent theta xi xj a) =
        μ (f ⁻¹' theorem7LaplacianPairStrictDenominatorEvent a) := by
          rw [sourceUnitVarianceLaplacePairScoreMap_preimage_strict_denominator]
    _ = (μ.map f) (theorem7LaplacianPairStrictDenominatorEvent a) :=
      (Measure.map_apply hf
        (theorem7LaplacianPairStrictDenominatorEvent_measurable a)).symm
    _ = ν (theorem7LaplacianPairStrictDenominatorEvent a) := by
      rw [hmap.map_eq]

/-- The literal source strict winner event has the canonical strict-event mass. -/
theorem sourceUnitVarianceLaplacePair_strict_winner_measure_eq
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    sourceUnitVarianceLaplacePairInnovationMeasure
        (sourceUnitVarianceLaplacePairStrictWinnerEvent theta xi xj) =
      theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
        pairStrictWinnerEvent := by
  let f := sourceUnitVarianceLaplacePairScoreMap theta xi xj
  let μ := sourceUnitVarianceLaplacePairInnovationMeasure
  let ν := theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
  have hf : Measurable f :=
    measurable_sourceUnitVarianceLaplacePairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceUnitVarianceLaplacePairScoreMap_measurePreserving htheta
  calc
    μ (sourceUnitVarianceLaplacePairStrictWinnerEvent theta xi xj) =
        μ (f ⁻¹' pairStrictWinnerEvent) := by
          rw [sourceUnitVarianceLaplacePairScoreMap_preimage_strict_winner]
    _ = (μ.map f) pairStrictWinnerEvent :=
      (Measure.map_apply hf pairStrictWinnerEvent_measurable).symm
    _ = ν pairStrictWinnerEvent := by
      rw [hmap.map_eq]

/-- Under the continuous Laplace score law, strict and weak pairwise wins agree. -/
theorem theorem7LaplacianPair_strict_winner_measure_eq_winner
    {lam xi xj : ℝ} :
    theorem7LaplacianPairMeasure lam xi xj pairStrictWinnerEvent =
      theorem7LaplacianPairMeasure lam xi xj theorem7LaplacianPairWinnerEvent := by
  let μi := theorem7LaplaceMeasure lam xi
  let μj := theorem7LaplaceMeasure lam xj
  letI : SFinite μi := by
    dsimp [μi, theorem7LaplaceMeasure]
    infer_instance
  letI : SFinite μj := by
    dsimp [μj, theorem7LaplaceMeasure]
    infer_instance
  letI : NoAtoms μj := theorem7LaplaceMeasure_noAtoms lam xj
  simpa [theorem7LaplacianPairMeasure, theorem7LaplacianPairWinnerEvent,
    μi, μj] using pair_strict_winner_measure_eq_weak μi μj

/-- Equation (C.1)'s literal Laplace conditional probability is the named ratio. -/
theorem sourceUnitVarianceLaplacePairConditionalRatio_eq_named
    {theta xi xj a : ℝ} (htheta : 0 < theta) :
    sourceUnitVarianceLaplacePairConditionalRatio theta xi xj a =
      theorem7LaplacianProductStrictConditionalRatioAt
        (Real.sqrt 2 * theta) xi xj a := by
  unfold sourceUnitVarianceLaplacePairConditionalRatio
    theorem7LaplacianProductStrictConditionalRatioAt
  rw [sourceUnitVarianceLaplacePair_strict_numerator_measure_eq htheta,
    sourceUnitVarianceLaplacePair_strict_denominator_measure_eq htheta]

/-- Equation (C.1)'s literal strict winner probability is the named winner mass. -/
theorem sourceUnitVarianceLaplacePairWinnerProbability_eq_named
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    sourceUnitVarianceLaplacePairWinnerProbability theta xi xj =
      (theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  unfold sourceUnitVarianceLaplacePairWinnerProbability
  rw [sourceUnitVarianceLaplacePair_strict_winner_measure_eq htheta,
    theorem7LaplacianPair_strict_winner_measure_eq_winner]

/-- Every finite literal Laplace cutoff has a strictly smaller conditional
pairwise-win probability than the unconditional one. -/
theorem theorem7LaplacianProductStrictConditionalRatioAt_lt_winner
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a <
      (theorem7LaplacianPairMeasure lam xi xj
        theorem7LaplacianPairWinnerEvent).toReal := by
  have h := theorem7LaplacianProductConditionalRatioAt_lt_winner
    (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  calc
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a =
        theorem7LaplacianPDFCDFRatioAt lam xi xj a :=
      theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf hlam
    _ = theorem7LaplacianProductConditionalRatioAt lam xi xj a :=
      (theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf hlam).symm
    _ < _ := h

/-- Source-faithful Laplace form of (C.1): scores are literally
`x + epsilon / theta` and all events remain strict. -/
theorem sourceUnitVarianceLaplacePairwiseConditional_lt_winner
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    sourceUnitVarianceLaplacePairConditionalRatio theta xi xj a <
      sourceUnitVarianceLaplacePairWinnerProbability theta xi xj := by
  have hlam : 0 < Real.sqrt 2 * theta :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  rw [sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta,
    sourceUnitVarianceLaplacePairWinnerProbability_eq_named htheta]
  exact theorem7LaplacianProductStrictConditionalRatioAt_lt_winner hlam hx

/-- Literal source-coordinate Laplace form of the right-tail equality in
Appendix C (C.2): as the cutoff tends to `+∞`, the strict conditional ratio
converges to the strict unconditional pairwise-winner probability. -/
theorem sourceUnitVarianceLaplacePairConditionalRatio_tendsto_atTop_winner
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    Filter.Tendsto
      (fun a => sourceUnitVarianceLaplacePairConditionalRatio theta xi xj a)
      Filter.atTop
      (nhds (sourceUnitVarianceLaplacePairWinnerProbability theta xi xj)) := by
  have hlam : 0 < Real.sqrt 2 * theta :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  have htail := theorem7LaplacianProductConditionalRatioAt_tendsto_atTop_winner
    (lam := Real.sqrt 2 * theta) (xi := xi) (xj := xj) hlam
  have hstrict :
      Filter.Tendsto
        (fun a => theorem7LaplacianProductStrictConditionalRatioAt
          (Real.sqrt 2 * theta) xi xj a)
        Filter.atTop
        (nhds ((theorem7LaplacianPairMeasure (Real.sqrt 2 * theta) xi xj
          theorem7LaplacianPairWinnerEvent).toReal)) :=
    htail.congr' (Filter.Eventually.of_forall fun a => by
      change theorem7LaplacianProductConditionalRatioAt
          (Real.sqrt 2 * theta) xi xj a =
        theorem7LaplacianProductStrictConditionalRatioAt
          (Real.sqrt 2 * theta) xi xj a
      rw [theorem7LaplacianProductConditionalRatioAt_eq_pdf_cdf hlam,
        ← theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf hlam])
  simpa only [sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta,
    sourceUnitVarianceLaplacePairWinnerProbability_eq_named htheta] using hstrict

/-! ## Standard-Gaussian source scores -/

/-- Two iid literal standard-Gaussian innovations. -/
noncomputable def sourceStandardGaussianPairInnovationMeasure : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal 0 1).prod
    (ProbabilityTheory.gaussianReal 0 1)

/-- The two source score coordinates `x + epsilon / theta`. -/
noncomputable def sourceStandardGaussianPairScoreMap
    (theta xi xj : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun epsilon => (xi + epsilon.1 / theta, xj + epsilon.2 / theta)

theorem measurable_sourceStandardGaussianPairScoreMap
    (theta xi xj : ℝ) :
    Measurable (sourceStandardGaussianPairScoreMap theta xi xj) := by
  unfold sourceStandardGaussianPairScoreMap
  fun_prop

/-- The strict numerator event in the source's own innovation coordinates. -/
def sourceStandardGaussianPairStrictNumeratorEvent
    (theta xi xj a : ℝ) : Set (ℝ × ℝ) :=
  {epsilon |
    xi + epsilon.1 / theta < a ∧
      xj + epsilon.2 / theta < xi + epsilon.1 / theta}

/-- The strict conditioning event in the source's own innovation coordinates. -/
def sourceStandardGaussianPairStrictDenominatorEvent
    (theta xi xj a : ℝ) : Set (ℝ × ℝ) :=
  {epsilon |
    xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}

/-- The strict unconditional pairwise-winner event in source coordinates. -/
def sourceStandardGaussianPairStrictWinnerEvent
    (theta xi xj : ℝ) : Set (ℝ × ℝ) :=
  {epsilon | xj + epsilon.2 / theta < xi + epsilon.1 / theta}

theorem sourceStandardGaussianPairScoreMap_preimage_strict_numerator
    (theta xi xj a : ℝ) :
    (sourceStandardGaussianPairScoreMap theta xi xj) ⁻¹'
        theorem8GaussianPairStrictNumeratorEvent a =
      sourceStandardGaussianPairStrictNumeratorEvent theta xi xj a := by
  rfl

theorem sourceStandardGaussianPairScoreMap_preimage_strict_denominator
    (theta xi xj a : ℝ) :
    (sourceStandardGaussianPairScoreMap theta xi xj) ⁻¹'
        theorem8GaussianPairStrictDenominatorEvent a =
      sourceStandardGaussianPairStrictDenominatorEvent theta xi xj a := by
  rfl

theorem sourceStandardGaussianPairScoreMap_preimage_strict_winner
    (theta xi xj : ℝ) :
    (sourceStandardGaussianPairScoreMap theta xi xj) ⁻¹'
        pairStrictWinnerEvent =
      sourceStandardGaussianPairStrictWinnerEvent theta xi xj := by
  rfl

private theorem sourceStandardGaussianMeasure_map_add_div
    (theta x : ℝ) :
    (ProbabilityTheory.gaussianReal 0 1).map
        (fun epsilon : ℝ => x + epsilon / theta) =
      ProbabilityTheory.gaussianReal x
        (theorem8GaussianVarianceFromStd (1 / theta)) := by
  calc
    (ProbabilityTheory.gaussianReal 0 1).map
        (fun epsilon : ℝ => x + epsilon / theta) =
      (ProbabilityTheory.gaussianReal 0 1).map
        (fun epsilon : ℝ => x + (1 / theta) * epsilon) := by
          congr 1
          funext epsilon
          ring
    _ = ProbabilityTheory.gaussianReal x
        (appendixBGaussianVariance (1 / theta)) :=
      gaussianReal_map_center_add_scaled_standard x (1 / theta)
    _ = ProbabilityTheory.gaussianReal x
        (theorem8GaussianVarianceFromStd (1 / theta)) := by
      congr 1

/-- The source pair-score map has exactly the named arbitrary-variance
Gaussian score law. -/
theorem sourceStandardGaussianPairScoreMap_measurePreserving
    (theta xi xj : ℝ) :
    MeasurePreserving (sourceStandardGaussianPairScoreMap theta xi xj)
      sourceStandardGaussianPairInnovationMeasure
      (theorem8GaussianPairMeasureStd (1 / theta) xi xj) := by
  refine ⟨measurable_sourceStandardGaussianPairScoreMap theta xi xj, ?_⟩
  let μ0 : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let fi : ℝ → ℝ := fun epsilon => xi + epsilon / theta
  let fj : ℝ → ℝ := fun epsilon => xj + epsilon / theta
  have hfi : Measurable fi := by
    dsimp [fi]
    fun_prop
  have hfj : Measurable fj := by
    dsimp [fj]
    fun_prop
  have hpair :
      (μ0.prod μ0).map (Prod.map fi fj) =
        (μ0.map fi).prod (μ0.map fj) := by
    exact (Measure.map_prod_map μ0 μ0 hfi hfj).symm
  change (μ0.prod μ0).map (Prod.map fi fj) = _
  rw [hpair, sourceStandardGaussianMeasure_map_add_div,
    sourceStandardGaussianMeasure_map_add_div]
  rfl

/-- Source-coordinate strict conditional probability in equation (C.1). -/
noncomputable def sourceStandardGaussianPairConditionalRatio
    (theta xi xj a : ℝ) : ℝ :=
  (sourceStandardGaussianPairInnovationMeasure
      (sourceStandardGaussianPairStrictNumeratorEvent theta xi xj a)).toReal /
    (sourceStandardGaussianPairInnovationMeasure
      (sourceStandardGaussianPairStrictDenominatorEvent theta xi xj a)).toReal

/-- Source-coordinate unconditional strict pairwise-winner probability. -/
noncomputable def sourceStandardGaussianPairWinnerProbability
    (theta xi xj : ℝ) : ℝ :=
  (sourceStandardGaussianPairInnovationMeasure
    (sourceStandardGaussianPairStrictWinnerEvent theta xi xj)).toReal

private theorem theorem8GaussianPairStrictDenominatorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem8GaussianPairStrictDenominatorEvent a) := by
  unfold theorem8GaussianPairStrictDenominatorEvent
  exact measurableSet_Iio.prod measurableSet_Iio

/-- The literal source numerator has the named arbitrary-standard-deviation
Gaussian strict-event mass. -/
theorem sourceStandardGaussianPair_strict_numerator_measure_eq
    (theta xi xj a : ℝ) :
    sourceStandardGaussianPairInnovationMeasure
        (sourceStandardGaussianPairStrictNumeratorEvent theta xi xj a) =
      theorem8GaussianPairMeasureStd (1 / theta) xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) := by
  let f := sourceStandardGaussianPairScoreMap theta xi xj
  let μ := sourceStandardGaussianPairInnovationMeasure
  let ν := theorem8GaussianPairMeasureStd (1 / theta) xi xj
  have hf : Measurable f :=
    measurable_sourceStandardGaussianPairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceStandardGaussianPairScoreMap_measurePreserving theta xi xj
  calc
    μ (sourceStandardGaussianPairStrictNumeratorEvent theta xi xj a) =
        μ (f ⁻¹' theorem8GaussianPairStrictNumeratorEvent a) := by
          rw [sourceStandardGaussianPairScoreMap_preimage_strict_numerator]
    _ = (μ.map f) (theorem8GaussianPairStrictNumeratorEvent a) :=
      (Measure.map_apply hf
        (theorem8GaussianPairStrictNumeratorEvent_measurable a)).symm
    _ = ν (theorem8GaussianPairStrictNumeratorEvent a) := by
      rw [hmap.map_eq]

/-- The literal source conditioning event has the named arbitrary-standard-
deviation Gaussian strict-event mass. -/
theorem sourceStandardGaussianPair_strict_denominator_measure_eq
    (theta xi xj a : ℝ) :
    sourceStandardGaussianPairInnovationMeasure
        (sourceStandardGaussianPairStrictDenominatorEvent theta xi xj a) =
      theorem8GaussianPairMeasureStd (1 / theta) xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) := by
  let f := sourceStandardGaussianPairScoreMap theta xi xj
  let μ := sourceStandardGaussianPairInnovationMeasure
  let ν := theorem8GaussianPairMeasureStd (1 / theta) xi xj
  have hf : Measurable f :=
    measurable_sourceStandardGaussianPairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceStandardGaussianPairScoreMap_measurePreserving theta xi xj
  calc
    μ (sourceStandardGaussianPairStrictDenominatorEvent theta xi xj a) =
        μ (f ⁻¹' theorem8GaussianPairStrictDenominatorEvent a) := by
          rw [sourceStandardGaussianPairScoreMap_preimage_strict_denominator]
    _ = (μ.map f) (theorem8GaussianPairStrictDenominatorEvent a) :=
      (Measure.map_apply hf
        (theorem8GaussianPairStrictDenominatorEvent_measurable a)).symm
    _ = ν (theorem8GaussianPairStrictDenominatorEvent a) := by
      rw [hmap.map_eq]

/-- The literal source strict winner event has the named arbitrary-standard-
deviation Gaussian strict-event mass. -/
theorem sourceStandardGaussianPair_strict_winner_measure_eq
    (theta xi xj : ℝ) :
    sourceStandardGaussianPairInnovationMeasure
        (sourceStandardGaussianPairStrictWinnerEvent theta xi xj) =
      theorem8GaussianPairMeasureStd (1 / theta) xi xj
        pairStrictWinnerEvent := by
  let f := sourceStandardGaussianPairScoreMap theta xi xj
  let μ := sourceStandardGaussianPairInnovationMeasure
  let ν := theorem8GaussianPairMeasureStd (1 / theta) xi xj
  have hf : Measurable f :=
    measurable_sourceStandardGaussianPairScoreMap theta xi xj
  have hmap : MeasurePreserving f μ ν :=
    sourceStandardGaussianPairScoreMap_measurePreserving theta xi xj
  calc
    μ (sourceStandardGaussianPairStrictWinnerEvent theta xi xj) =
        μ (f ⁻¹' pairStrictWinnerEvent) := by
          rw [sourceStandardGaussianPairScoreMap_preimage_strict_winner]
    _ = (μ.map f) pairStrictWinnerEvent :=
      (Measure.map_apply hf pairStrictWinnerEvent_measurable).symm
    _ = ν pairStrictWinnerEvent := by
      rw [hmap.map_eq]

/-- Under a positive standard deviation, strict and weak Gaussian pairwise
wins have identical mass. -/
theorem theorem8GaussianPairStd_strict_winner_measure_eq_winner
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) :
    theorem8GaussianPairMeasureStd sigma xi xj pairStrictWinnerEvent =
      theorem8GaussianPairMeasureStd sigma xi xj theorem8GaussianPairWinnerEvent := by
  let μi := ProbabilityTheory.gaussianReal xi (theorem8GaussianVarianceFromStd sigma)
  let μj := ProbabilityTheory.gaussianReal xj (theorem8GaussianVarianceFromStd sigma)
  letI : SFinite μi := by infer_instance
  letI : SFinite μj := by infer_instance
  letI : NoAtoms μj := ProbabilityTheory.noAtoms_gaussianReal
    (theorem8GaussianVarianceFromStd_ne_zero (ne_of_gt hsigma))
  simpa [theorem8GaussianPairMeasureStd,
    AppliedModelingLib.Probability.independentGaussianPairMeasureWithStd,
    theorem8GaussianPairWinnerEvent, μi, μj] using
      pair_strict_winner_measure_eq_weak μi μj

/-- Equation (C.1)'s literal Gaussian conditional probability is the named
arbitrary-standard-deviation ratio. -/
theorem sourceStandardGaussianPairConditionalRatio_eq_named
    (theta xi xj a : ℝ) :
    sourceStandardGaussianPairConditionalRatio theta xi xj a =
      theorem8GaussianProductStrictConditionalRatioAtStd (1 / theta) xi xj a := by
  unfold sourceStandardGaussianPairConditionalRatio
    theorem8GaussianProductStrictConditionalRatioAtStd
  rw [sourceStandardGaussianPair_strict_numerator_measure_eq,
    sourceStandardGaussianPair_strict_denominator_measure_eq]

/-- Equation (C.1)'s literal Gaussian strict winner probability is the named
arbitrary-standard-deviation weak winner mass; equality uses the proved
zero-tie bridge. -/
theorem sourceStandardGaussianPairWinnerProbability_eq_named
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    sourceStandardGaussianPairWinnerProbability theta xi xj =
      (theorem8GaussianPairMeasureStd (1 / theta) xi xj
        theorem8GaussianPairWinnerEvent).toReal := by
  unfold sourceStandardGaussianPairWinnerProbability
  rw [sourceStandardGaussianPair_strict_winner_measure_eq,
    theorem8GaussianPairStd_strict_winner_measure_eq_winner (one_div_pos.mpr htheta)]

/-- The canonical Gaussian strict conditional ratio is below the canonical
unconditional pairwise-winner probability. -/
theorem theorem8GaussianProductStrictConditionalRatioAt_lt_winner
    {xi xj a : ℝ} (hx : xj < xi) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a <
      (theorem8GaussianPairMeasure xi xj theorem8GaussianPairWinnerEvent).toReal := by
  have hnonneg :
      0 ≤ ∫ x : ℝ, theorem8GaussianPDF xi x * theorem8GaussianCDF xj x := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  rw [theorem8GaussianPairWinner_measure_eq_integral,
    ENNReal.toReal_ofReal hnonneg]
  exact theorem8GaussianProductStrictConditionalRatioAt_lt_unconditionalIntegral hx

/-- Positive canonical score scaling preserves the weak pairwise-winner event. -/
theorem theorem8GaussianPairCanonicalScaleMap_preimage_winner
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (theorem8GaussianPairCanonicalScaleMap sigma) ⁻¹'
      theorem8GaussianPairWinnerEvent = theorem8GaussianPairWinnerEvent := by
  have hc : 0 < theorem8GaussianCanonicalScale sigma :=
    theorem8GaussianCanonicalScale_pos hsigma
  ext p
  simp only [Set.mem_preimage]
  change theorem8GaussianCanonicalScale sigma * p.2 ≤
      theorem8GaussianCanonicalScale sigma * p.1 ↔ p.2 ≤ p.1
  exact mul_le_mul_iff_of_pos_left hc

/-- The arbitrary-standard-deviation Gaussian winner mass is the canonical
winner mass after the explicit positive score scaling. -/
theorem theorem8GaussianPairMeasureStd_winner_eq_scaled
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) :
    theorem8GaussianPairMeasureStd sigma xi xj theorem8GaussianPairWinnerEvent =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale sigma * xi)
        (theorem8GaussianCanonicalScale sigma * xj)
        theorem8GaussianPairWinnerEvent := by
  let f := theorem8GaussianPairCanonicalScaleMap sigma
  let μ := theorem8GaussianPairMeasureStd sigma xi xj
  let ν := theorem8GaussianPairMeasure
    (theorem8GaussianCanonicalScale sigma * xi)
    (theorem8GaussianCanonicalScale sigma * xj)
  have hf : Measurable f := theorem8GaussianPairCanonicalScaleMap_measurable sigma
  have hmap : μ.map f = ν := theorem8GaussianPairMeasureStd_map_canonicalScale hsigma
  calc
    μ theorem8GaussianPairWinnerEvent = μ (f ⁻¹' theorem8GaussianPairWinnerEvent) := by
      rw [theorem8GaussianPairCanonicalScaleMap_preimage_winner hsigma]
    _ = (μ.map f) theorem8GaussianPairWinnerEvent :=
      (Measure.map_apply hf theorem8GaussianPairWinnerEvent_measurable).symm
    _ = ν theorem8GaussianPairWinnerEvent := by
      rw [hmap]

/-- Every finite strict conditional Gaussian ratio with positive standard
deviation is below its unconditional pairwise-winner probability. -/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_lt_winner
    {sigma xi xj a : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    theorem8GaussianProductStrictConditionalRatioAtStd sigma xi xj a <
      (theorem8GaussianPairMeasureStd sigma xi xj
        theorem8GaussianPairWinnerEvent).toReal := by
  have hc : 0 < theorem8GaussianCanonicalScale sigma :=
    theorem8GaussianCanonicalScale_pos hsigma
  have hscaled : theorem8GaussianCanonicalScale sigma * xj <
      theorem8GaussianCanonicalScale sigma * xi :=
    mul_lt_mul_of_pos_left hx hc
  rw [theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled hsigma,
    theorem8GaussianPairMeasureStd_winner_eq_scaled hsigma]
  exact theorem8GaussianProductStrictConditionalRatioAt_lt_winner hscaled

/-- The arbitrary-standard-deviation strict Gaussian conditional ratio has
the canonical right-tail winner limit after the explicit positive score-scale
transport. -/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_tendsto_atTop_winner
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) :
    Filter.Tendsto
      (fun a => theorem8GaussianProductStrictConditionalRatioAtStd sigma xi xj a)
      Filter.atTop
      (nhds ((theorem8GaussianPairMeasureStd sigma xi xj
        theorem8GaussianPairWinnerEvent).toReal)) := by
  let c : ℝ := theorem8GaussianCanonicalScale sigma
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hsigma
  have hscale : Filter.Tendsto (fun a : ℝ => c * a) Filter.atTop Filter.atTop := by
    simpa [c] using
      (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id :
        Filter.Tendsto (fun a : ℝ => theorem8GaussianCanonicalScale sigma * a)
          Filter.atTop Filter.atTop)
  have hnonneg :
      0 ≤ ∫ x : ℝ,
        theorem8GaussianPDF (c * xi) x * theorem8GaussianCDF (c * xj) x := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg (c * xi) x)
      (theorem8GaussianCDF_nonneg (c * xj) x)
  have hcanonical :
      Filter.Tendsto
        (fun a => theorem8GaussianProductStrictConditionalRatioAt
          (c * xi) (c * xj) a)
        Filter.atTop
        (nhds ((theorem8GaussianPairMeasure (c * xi) (c * xj)
          theorem8GaussianPairWinnerEvent).toReal)) := by
    rw [theorem8GaussianPairWinner_measure_eq_integral,
      ENNReal.toReal_ofReal hnonneg]
    exact theorem8GaussianProductStrictConditionalRatioAt_tendsto_atTop_unconditionalIntegral
      (c * xi) (c * xj)
  have htransported := hcanonical.comp hscale
  rw [theorem8GaussianPairMeasureStd_winner_eq_scaled hsigma]
  exact htransported.congr' (Filter.Eventually.of_forall fun a => by
    simpa [c] using
      (theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled
        (σ := sigma) (xi := xi) (xj := xj) (a := a) hsigma).symm)

/-- Source-faithful Gaussian form of (C.1): scores are literally
`x + epsilon / theta` for iid standard-Gaussian innovations, and all source
events remain strict. -/
theorem sourceStandardGaussianPairwiseConditional_lt_winner
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    sourceStandardGaussianPairConditionalRatio theta xi xj a <
      sourceStandardGaussianPairWinnerProbability theta xi xj := by
  rw [sourceStandardGaussianPairConditionalRatio_eq_named,
    sourceStandardGaussianPairWinnerProbability_eq_named htheta]
  exact theorem8GaussianProductStrictConditionalRatioAtStd_lt_winner
    (one_div_pos.mpr htheta) hx

/-- Literal source-coordinate standard-Gaussian form of the right-tail
equality in Appendix C (C.2): the strict conditional ratio converges to the
strict unconditional pairwise-winner probability as the cutoff tends to
`+∞`. -/
theorem sourceStandardGaussianPairConditionalRatio_tendsto_atTop_winner
    {theta xi xj : ℝ} (htheta : 0 < theta) :
    Filter.Tendsto
      (fun a => sourceStandardGaussianPairConditionalRatio theta xi xj a)
      Filter.atTop
      (nhds (sourceStandardGaussianPairWinnerProbability theta xi xj)) := by
  simpa only [sourceStandardGaussianPairConditionalRatio_eq_named,
    sourceStandardGaussianPairWinnerProbability_eq_named htheta] using
    (theorem8GaussianProductStrictConditionalRatioAtStd_tendsto_atTop_winner
      (sigma := 1 / theta) (xi := xi) (xj := xj) (one_div_pos.mpr htheta))

end KR21Monoculture
