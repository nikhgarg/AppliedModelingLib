import KR21Monoculture.UnitVarianceNormalization

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

/-!
# Finite-positive-variance normalization for KR21 RUMs

Section 3.1 of KR21 fixes iid scalar noise `E`, says (without loss of
generality) that `E` has unit variance, and ranks the scores
`value i + epsilon i / theta`. This file proves the scale transport actually
needed by that sentence. It does not infer finite positive variance from a
distribution-family name.
-/

namespace KR21Monoculture

noncomputable section

/-- The scalar noise law after division by a scale. -/
noncomputable def sourceRUMNormalizedScalarNoiseLaw
    (E : Measure ℝ) (sigma : ℝ) : Measure ℝ :=
  E.map (fun epsilon : ℝ => epsilon / sigma)

/-- The iid vector law induced by the normalized scalar law. -/
noncomputable def sourceRUMNormalizedIIDNoiseLaw
    {n : ℕ} (E : Measure ℝ) (sigma : ℝ) : Measure (Candidate n → ℝ) :=
  Measure.pi (fun _ : Candidate n => sourceRUMNormalizedScalarNoiseLaw E sigma)

theorem sourceRUMNormalizedScalarNoiseLaw_isProbabilityMeasure
    (E : Measure ℝ) [IsProbabilityMeasure E] (sigma : ℝ) :
    IsProbabilityMeasure (sourceRUMNormalizedScalarNoiseLaw E sigma) := by
  unfold sourceRUMNormalizedScalarNoiseLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_id.div_const sigma).aemeasurable)

theorem sourceRUMNormalizedIIDNoiseLaw_isProbabilityMeasure
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E] (sigma : ℝ) :
    IsProbabilityMeasure (sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma) := by
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (sourceRUMNormalizedScalarNoiseLaw E sigma) := fun _ =>
    sourceRUMNormalizedScalarNoiseLaw_isProbabilityMeasure E sigma
  unfold sourceRUMNormalizedIIDNoiseLaw
  infer_instance

/-- The normalized coordinate projections are independent under their
explicit product law. This is a semantic iid proof, not a name-based claim. -/
theorem sourceRUMNormalizedIIDNoiseLaw_iIndepFun
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E] (sigma : ℝ) :
    iIndepFun
      (fun i (epsilon : Candidate n → ℝ) => epsilon i)
      (sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma) := by
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (sourceRUMNormalizedScalarNoiseLaw E sigma) := fun _ =>
    sourceRUMNormalizedScalarNoiseLaw_isProbabilityMeasure E sigma
  unfold sourceRUMNormalizedIIDNoiseLaw
  exact @iIndepFun_pi
    (Candidate n) _
    (fun _ : Candidate n => ℝ) _
    (fun _ : Candidate n => sourceRUMNormalizedScalarNoiseLaw E sigma) this
    (fun _ : Candidate n => ℝ) _
    (fun _ : Candidate n => id)
    (fun _ => measurable_id.aemeasurable)

/-- Every normalized coordinate has the same scalar normalized law. Together
with `sourceRUMNormalizedIIDNoiseLaw_iIndepFun`, this is the explicit iid
semantics of the source noise vector. -/
theorem sourceRUMNormalizedIIDNoiseLaw_coordinate_law
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (sigma : ℝ) (i : Candidate n) :
    Measure.map (Function.eval i)
      (sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma) =
        sourceRUMNormalizedScalarNoiseLaw E sigma := by
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (sourceRUMNormalizedScalarNoiseLaw E sigma) := fun _ =>
    sourceRUMNormalizedScalarNoiseLaw_isProbabilityMeasure E sigma
  unfold sourceRUMNormalizedIIDNoiseLaw
  exact (@measurePreserving_eval
    (Candidate n)
    (fun _ : Candidate n => ℝ)
    _ _
    (fun _ : Candidate n => sourceRUMNormalizedScalarNoiseLaw E sigma) this i).map_eq

/-- Finite second moments are preserved by scalar normalization. -/
theorem sourceRUMNormalizedScalarNoiseLaw_memLp_two
    (E : Measure ℝ) {sigma : ℝ}
    (hsecond : MemLp id 2 E) :
    MemLp id 2 (sourceRUMNormalizedScalarNoiseLaw E sigma) := by
  unfold sourceRUMNormalizedScalarNoiseLaw
  have hmap : MemLp id 2 (E.map (fun epsilon : ℝ => epsilon / sigma)) ↔
      MemLp (id ∘ fun epsilon : ℝ => epsilon / sigma) 2 E := by
    simpa only [id_eq] using
      (memLp_map_measure_iff measurable_id.aestronglyMeasurable
        ((measurable_id.div_const sigma).aemeasurable) :
        MemLp id 2 (E.map (fun epsilon : ℝ => id epsilon / sigma)) ↔
          MemLp (id ∘ fun epsilon : ℝ => id epsilon / sigma) 2 E)
  apply hmap.mpr
  change MemLp (fun epsilon : ℝ => epsilon / sigma) 2 E
  have hfun : (fun epsilon : ℝ => epsilon / sigma) =
      fun epsilon => sigma⁻¹ * id epsilon := by
    funext epsilon
    change epsilon / sigma = sigma⁻¹ * epsilon
    rw [inv_mul_eq_div]
  rw [hfun]
  exact hsecond.const_mul _

/-- Dividing a scalar noise law of variance `sigma^2` by positive `sigma`
produces a literal unit-variance scalar law. -/
theorem sourceRUMNormalizedScalarNoiseLaw_variance_eq_one
    (E : Measure ℝ) [IsProbabilityMeasure E]
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hvariance : Var[id; E] = sigma ^ 2) :
    Var[id; sourceRUMNormalizedScalarNoiseLaw E sigma] = 1 := by
  unfold sourceRUMNormalizedScalarNoiseLaw
  have hmap : Var[id; E.map (fun epsilon : ℝ => epsilon / sigma)] =
      Var[(fun epsilon : ℝ => epsilon / sigma); E] := by
    simpa only [id_eq] using
      (ProbabilityTheory.variance_id_map
        ((measurable_id.div_const sigma).aemeasurable) :
        Var[id; E.map (fun epsilon : ℝ => id epsilon / sigma)] =
          Var[(fun epsilon : ℝ => id epsilon / sigma); E])
  rw [hmap]
  have hfun : (fun epsilon : ℝ => epsilon / sigma) =
      fun epsilon => sigma⁻¹ * epsilon := by
    funext epsilon
    rw [inv_mul_eq_div]
  rw [hfun, ProbabilityTheory.variance_const_mul]
  change sigma⁻¹ ^ 2 * Var[id; E] = 1
  rw [hvariance]
  field_simp [ne_of_gt hsigma]

/-- Normalizing an iid noise vector coordinatewise is exactly the product of
the normalized scalar laws. This is the semantic iid preservation fact. -/
theorem sourceRUMNormalizedIIDNoiseLaw_eq_map_scaledNoiseNormalization
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E] (sigma : ℝ) :
    sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma =
      Measure.map (scaledNoiseNormalization (n := n) sigma)
        (Measure.pi (fun _ : Candidate n => E)) := by
  unfold sourceRUMNormalizedIIDNoiseLaw sourceRUMNormalizedScalarNoiseLaw
  change Measure.pi (fun _ : Candidate n => E.map (fun epsilon : ℝ => epsilon / sigma)) =
      Measure.map (fun noise i => noise i / sigma)
        (Measure.pi (fun _ : Candidate n => E))
  symm
  simpa only using
    (Measure.pi_map_pi (μ := fun _ : Candidate n => E)
      (f := fun _ (epsilon : ℝ) => epsilon / sigma)
      (fun _ => (measurable_id.div_const sigma).aemeasurable))

/-- Every coordinate of the normalized iid product law has unit variance
under the explicit positive-variance premise. -/
theorem sourceRUMNormalizedIIDNoiseLaw_coordinate_variance_eq_one
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hvariance : Var[id; E] = sigma ^ 2)
    (i : Candidate n) :
    Var[(fun epsilon : Candidate n → ℝ => epsilon i);
      sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma] = 1 := by
  let normalizedE : Measure ℝ := sourceRUMNormalizedScalarNoiseLaw E sigma
  letI : IsProbabilityMeasure normalizedE :=
    sourceRUMNormalizedScalarNoiseLaw_isProbabilityMeasure E sigma
  have heval : MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : Candidate n => normalizedE)) normalizedE := by
    exact @measurePreserving_eval
      (Candidate n)
      (fun _ : Candidate n => ℝ)
      _ _
      (fun _ : Candidate n => normalizedE)
      (fun _ => inferInstance)
      i
  have hvariance_normalized : Var[id; normalizedE] = 1 := by
    exact sourceRUMNormalizedScalarNoiseLaw_variance_eq_one E hsigma hvariance
  have hvariance_eval := heval.variance_fun_comp measurable_id.aemeasurable
  simpa only [sourceRUMNormalizedIIDNoiseLaw, normalizedE,
    Function.comp_apply, id_eq] using hvariance_eval.trans hvariance_normalized

/-- The source score/ranking experiment is invariant under the finite positive
variance normalization: raw iid noise at `theta` gives exactly the same
ranking PMF as the unit-variance iid normalized noise at `theta / sigma`. -/
theorem sourceRUM_iidRankingPMF_scale_reparameterization
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (value : Candidate n → ℝ) {sigma theta : ℝ} (hsigma : 0 < sigma) :
    paper_appendixA_scaledNoiseRankingPMF
      (Measure.pi (fun _ : Candidate n => E)) value theta =
      @paper_appendixA_scaledNoiseRankingPMF n
        (sourceRUMNormalizedIIDNoiseLaw (n := n) E sigma)
        (sourceRUMNormalizedIIDNoiseLaw_isProbabilityMeasure E sigma)
        value (theta / sigma) := by
  have htransport := paper_appendixA_scaledNoiseRankingPMF_scale_reparameterization
    (Measure.pi (fun _ : Candidate n => E)) value
    (sigma := sigma) (theta := theta) hsigma
  simpa only [sourceRUMNormalizedIIDNoiseLaw_eq_map_scaledNoiseNormalization] using
    htransport

/-- Source-facing WLOG normalization at the actual standard-deviation scale.
For a finite positive scalar variance `v`, set `sigma = sqrt v`. Then the
normalized scalar law retains a finite second moment, its iid product has
unit coordinate variance, and scores/rankings are exactly preserved after
the parameter conversion `theta |-> theta / sqrt v`.

This is only a scale reparameterization. It neither proves the source's
full-support, differentiability, or monotonicity requirements nor identifies
an arbitrary noise family with Gaussian, Laplace, or Gumbel noise. -/
theorem sourceRUM_iidFinitePositiveVariance_normalization
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (hsecond : MemLp id 2 E)
    (hvariance_pos : 0 < Var[id; E])
    (value : Candidate n → ℝ) (theta : ℝ) :
    iIndepFun
        (fun i (epsilon : Candidate n → ℝ) => epsilon i)
        (sourceRUMNormalizedIIDNoiseLaw (n := n) E
          (Real.sqrt (Var[id; E]))) ∧
      MemLp id 2
        (sourceRUMNormalizedScalarNoiseLaw E (Real.sqrt (Var[id; E]))) ∧
      (∀ i : Candidate n,
        Var[(fun epsilon : Candidate n → ℝ => epsilon i);
          sourceRUMNormalizedIIDNoiseLaw (n := n) E
            (Real.sqrt (Var[id; E]))] = 1) ∧
      paper_appendixA_scaledNoiseRankingPMF
          (Measure.pi (fun _ : Candidate n => E)) value theta =
        @paper_appendixA_scaledNoiseRankingPMF n
          (sourceRUMNormalizedIIDNoiseLaw (n := n) E
            (Real.sqrt (Var[id; E])))
          (sourceRUMNormalizedIIDNoiseLaw_isProbabilityMeasure E
            (Real.sqrt (Var[id; E])))
          value (theta / Real.sqrt (Var[id; E])) := by
  let sigma : ℝ := Real.sqrt (Var[id; E])
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact Real.sqrt_pos.2 hvariance_pos
  have hvariance : Var[id; E] = sigma ^ 2 := by
    dsimp [sigma]
    rw [Real.sq_sqrt (le_of_lt hvariance_pos)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sourceRUMNormalizedIIDNoiseLaw_iIndepFun E sigma
  · exact sourceRUMNormalizedScalarNoiseLaw_memLp_two E hsecond
  · intro i
    exact sourceRUMNormalizedIIDNoiseLaw_coordinate_variance_eq_one
      E hsigma hvariance i
  · exact sourceRUM_iidRankingPMF_scale_reparameterization E value hsigma

end

end KR21Monoculture
