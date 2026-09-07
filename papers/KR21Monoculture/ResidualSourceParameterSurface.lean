import KR21Monoculture.AppendixCSourcePairwise
import KR21Monoculture.MallowsSourceSurface

open AppliedModelingLib Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal NNReal Topology BigOperators

namespace KR21Monoculture

/-!
# Residual literal source-parameter endpoints for KR21

This module closes two narrow source-surface gaps without changing the
underlying analytic developments:

* Appendix C Theorem 7 writes the unit-variance Laplace scores as
  `x + sigma * epsilon`, while the existing direct endpoint uses the equivalent
  inverse-accuracy convention `x + epsilon / theta`.
* Appendix F Lemma 8 writes Mallows accuracy as `phi > 1`, while the finite
  proof internally uses `q = phi^{-1}`.

Both conversions are proved in the theorem paths below.  No conclusion-shaped
comparison premise is introduced.
-/

/-! ## Appendix C: source scale `sigma` -/

/-- The literal Appendix-C source score map `x + sigma * epsilon`. -/
noncomputable def sourceUnitVarianceLaplacePairScoreMapSigma
    (sigma xi xj : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun epsilon => (xi + sigma * epsilon.1, xj + sigma * epsilon.2)

theorem sourceUnitVarianceLaplacePairScoreMapSigma_eq_inverseAccuracy
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) :
    sourceUnitVarianceLaplacePairScoreMapSigma sigma xi xj =
      sourceUnitVarianceLaplacePairScoreMap sigma⁻¹ xi xj := by
  funext epsilon
  unfold sourceUnitVarianceLaplacePairScoreMapSigma
    sourceUnitVarianceLaplacePairScoreMap
  field_simp [ne_of_gt hsigma]

/-- The strict numerator event in Theorem 7's literal `sigma` convention. -/
def sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent
    (sigma xi xj a : ℝ) : Set (ℝ × ℝ) :=
  (sourceUnitVarianceLaplacePairScoreMapSigma sigma xi xj) ⁻¹'
    theorem7LaplacianPairStrictNumeratorEvent a

/-- The strict conditioning event in Theorem 7's literal `sigma` convention. -/
def sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent
    (sigma xi xj a : ℝ) : Set (ℝ × ℝ) :=
  (sourceUnitVarianceLaplacePairScoreMapSigma sigma xi xj) ⁻¹'
    theorem7LaplacianPairStrictDenominatorEvent a

/-- The literal source conditional probability
`Pr[X_i > X_j | X_i < a, X_j < a]` for `X_r = x_r + sigma * epsilon_r`. -/
noncomputable def sourceUnitVarianceLaplacePairSigmaConditionalRatio
    (sigma xi xj a : ℝ) : ℝ :=
  (sourceUnitVarianceLaplacePairInnovationMeasure
      (sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent sigma xi xj a)).toReal /
    (sourceUnitVarianceLaplacePairInnovationMeasure
      (sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent sigma xi xj a)).toReal

/-- Expanded event semantics for the literal source numerator. -/
theorem mem_sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent_iff
    {sigma xi xj a : ℝ} {epsilon : ℝ × ℝ} :
    epsilon ∈ sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent sigma xi xj a ↔
      xi + sigma * epsilon.1 < a ∧
        xj + sigma * epsilon.2 < xi + sigma * epsilon.1 := by
  rfl

/-- Expanded event semantics for the literal source conditioning event. -/
theorem mem_sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent_iff
    {sigma xi xj a : ℝ} {epsilon : ℝ × ℝ} :
    epsilon ∈ sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent sigma xi xj a ↔
      xi + sigma * epsilon.1 < a ∧ xj + sigma * epsilon.2 < a := by
  rfl

theorem sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent_eq_inverseAccuracy
    {sigma xi xj a : ℝ} (hsigma : 0 < sigma) :
    sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent sigma xi xj a =
      sourceUnitVarianceLaplacePairStrictNumeratorEvent sigma⁻¹ xi xj a := by
  unfold sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent
  rw [sourceUnitVarianceLaplacePairScoreMapSigma_eq_inverseAccuracy hsigma,
    sourceUnitVarianceLaplacePairScoreMap_preimage_strict_numerator]

theorem sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent_eq_inverseAccuracy
    {sigma xi xj a : ℝ} (hsigma : 0 < sigma) :
    sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent sigma xi xj a =
      sourceUnitVarianceLaplacePairStrictDenominatorEvent sigma⁻¹ xi xj a := by
  unfold sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent
  rw [sourceUnitVarianceLaplacePairScoreMapSigma_eq_inverseAccuracy hsigma,
    sourceUnitVarianceLaplacePairScoreMap_preimage_strict_denominator]

/-- The literal `sigma` source probability equals the existing inverse-
accuracy source probability after the explicitly proved substitution
`theta = sigma^{-1}`. -/
theorem sourceUnitVarianceLaplacePairSigmaConditionalRatio_eq_inverseAccuracy
    {sigma xi xj a : ℝ} (hsigma : 0 < sigma) :
    sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj a =
      sourceUnitVarianceLaplacePairConditionalRatio sigma⁻¹ xi xj a := by
  unfold sourceUnitVarianceLaplacePairSigmaConditionalRatio
    sourceUnitVarianceLaplacePairConditionalRatio
  rw [sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent_eq_inverseAccuracy hsigma,
    sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent_eq_inverseAccuracy hsigma]

/--
Literal Theorem 7 source statement.  The iid innovation law is the centered
Laplace law of rate `sqrt 2`, whose variance-one calibration is established in
the imported source-normalization development.  Positivity of `sigma` is the
usual scale convention and makes `theta = sigma^{-1}` a positive accuracy.
-/
theorem source_theorem7_unitVarianceLaplace_sigma_conditional_derivative
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u)
        d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ =>
          sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u)
        d a ∧
      0 < d) := by
  have htheta : 0 < sigma⁻¹ := inv_pos.mpr hsigma
  have hlam : 0 < Real.sqrt 2 * sigma⁻¹ :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  obtain ⟨hnonneg, hwitness⟩ :=
    theorem7LaplacianProductStrictConditionalRatioAt_derivative_nonneg_all_and_pos_some
      (lam := Real.sqrt 2 * sigma⁻¹) (xi := xi) (xj := xj) hlam hx
  refine ⟨?_, ?_⟩
  · intro a
    obtain ⟨d, hd, hdnonneg⟩ := hnonneg a
    refine ⟨d, ?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => by
        change sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u =
          theorem7LaplacianProductStrictConditionalRatioAt
            (Real.sqrt 2 * sigma⁻¹) xi xj u
        calc
          sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u =
              sourceUnitVarianceLaplacePairConditionalRatio sigma⁻¹ xi xj u :=
            sourceUnitVarianceLaplacePairSigmaConditionalRatio_eq_inverseAccuracy hsigma
          _ = theorem7LaplacianProductStrictConditionalRatioAt
              (Real.sqrt 2 * sigma⁻¹) xi xj u :=
            sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta)
  · obtain ⟨a, d, hd, hdpos⟩ := hwitness
    refine ⟨a, d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => by
        change sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u =
          theorem7LaplacianProductStrictConditionalRatioAt
            (Real.sqrt 2 * sigma⁻¹) xi xj u
        calc
          sourceUnitVarianceLaplacePairSigmaConditionalRatio sigma xi xj u =
              sourceUnitVarianceLaplacePairConditionalRatio sigma⁻¹ xi xj u :=
            sourceUnitVarianceLaplacePairSigmaConditionalRatio_eq_inverseAccuracy hsigma
          _ = theorem7LaplacianProductStrictConditionalRatioAt
              (Real.sqrt 2 * sigma⁻¹) xi xj u :=
            sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta)

/-- Theorem 7 again with its raw iid innovation events expanded in the
conclusion.  This is the review endpoint for the source display rather than a
theorem about a merely named conditional-ratio helper. -/
theorem source_theorem7_unitVarianceLaplace_sigma_conditional_derivative_explicit
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          (sourceUnitVarianceLaplacePairInnovationMeasure
            {epsilon | xi + sigma * epsilon.1 < u ∧
              xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
            (sourceUnitVarianceLaplacePairInnovationMeasure
              {epsilon | xi + sigma * epsilon.1 < u ∧
                xj + sigma * epsilon.2 < u}).toReal)
        d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ =>
          (sourceUnitVarianceLaplacePairInnovationMeasure
            {epsilon | xi + sigma * epsilon.1 < u ∧
              xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
            (sourceUnitVarianceLaplacePairInnovationMeasure
              {epsilon | xi + sigma * epsilon.1 < u ∧
                xj + sigma * epsilon.2 < u}).toReal)
        d a ∧
      0 < d) := by
  simpa [sourceUnitVarianceLaplacePairSigmaConditionalRatio,
    sourceUnitVarianceLaplacePairSigmaStrictNumeratorEvent,
    sourceUnitVarianceLaplacePairSigmaStrictDenominatorEvent,
    sourceUnitVarianceLaplacePairScoreMapSigma,
    theorem7LaplacianPairStrictNumeratorEvent,
    theorem7LaplacianPairStrictDenominatorEvent] using
    source_theorem7_unitVarianceLaplace_sigma_conditional_derivative hsigma hx

/-! ## Appendix F: source accuracy `phi` -/

/--
Literal Lemma 8 source statement.  The paper's parameter convention is
`theta = phi - 1`, so `phiMore > phiLess > 1` becomes the strict reverse
inequality between the finite model's inverse parameters.  The conclusion is
the actual probability that the center-ordered pair is correctly ranked.
-/
theorem source_lemma8_mallows_phi_pairCorrectProb_lt
    {n : ℕ} (center : Ranking n) {phiMore phiLess : ℝ}
    (hphiLess : 1 < phiLess) (hphiOrder : phiLess < phiMore)
    {c d : Candidate n} (hcd : rankOf center c < rankOf center d) :
    (concreteMallowsSpec center (phiLess - 1)).pairCorrectProb c d <
      (concreteMallowsSpec center (phiMore - 1)).pairCorrectProb c d := by
  have hphiMore : 1 < phiMore := lt_trans hphiLess hphiOrder
  have hthetaLess : 0 < phiLess - 1 := by linarith
  have hthetaMore : 0 < phiMore - 1 := by linarith
  refine MallowsComparison.paper_lemma8_mallows_pairCorrectProb_lt
    (Mmore := concreteMallowsSpec center (phiMore - 1))
    (Mless := concreteMallowsSpec center (phiLess - 1))
    (c := c) (d := d) rfl hcd ?_
  change mallowsAccuracyQ (phiMore - 1) < mallowsAccuracyQ (phiLess - 1)
  rw [mallowsAccuracyQ_eq_of_pos hthetaMore,
    mallowsAccuracyQ_eq_of_pos hthetaLess]
  unfold mallowsInverseAccuracyQ
  convert (inv_lt_inv₀ (by linarith : 0 < phiMore)
    (by linarith : 0 < phiLess)).2 hphiOrder using 1 <;> ring

/-- Lemma 8 with the finite Mallows pair-correct event expanded.  The source
items `i < j` are represented by the displayed center-rank premise, and the
strict `phiMore > phiLess > 1` comparison is retained in the theorem inputs. -/
theorem source_lemma8_mallows_phi_pairwise_correct_probability_lt
    {n : ℕ} (center : Ranking n) {phiMore phiLess : ℝ}
    (hphiLess : 1 < phiLess) (hphiOrder : phiLess < phiMore)
    {c d : Candidate n} (hcd : rankOf center c < rankOf center d) :
    AppliedModelingLib.pmfProb (concreteMallowsSpec center (phiLess - 1)).law
      (fun pi => rankOf center c < rankOf center d ∧ rankOf pi c < rankOf pi d) <
      AppliedModelingLib.pmfProb (concreteMallowsSpec center (phiMore - 1)).law
        (fun pi => rankOf center c < rankOf center d ∧ rankOf pi c < rankOf pi d) := by
  simpa [MallowsSpec.pairCorrectProb] using
    source_lemma8_mallows_phi_pairCorrectProb_lt center hphiLess hphiOrder hcd

end KR21Monoculture
