import GJ19OptimalBinaryRatingSystems.MainTheorems

open scoped BigOperators

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/--
Source-shaped local-constant convention for Lemma C.4 on an open interval.
-/
def lemmaC4LocallyConstantOnIoo
    (successProb : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo lo hi →
    ∀ y : ℝ, y ∈ Set.Ioo lo hi →
      successProb x = successProb y

/--
Source-shaped finite-step convention for Lemma C.4 on an open interval:
the Bernoulli success probabilities take only finitely many values on the
interval.  For monotone rules this captures the source's finite-level
stepwise increasing convention without choosing cutpoints in the predicate.
-/
def lemmaC4FiniteRangeOnIoo
    (successProb : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  (successProb '' Set.Ioo lo hi).Finite

/--
Paper-local finite-step convention for Lemma C.4 on an open interval.  The
first field says the rule takes finitely many values.  The second field says
each level fiber is order-convex on the interval, which is the monotone
one-dimensional shape behind a finite step rule without choosing cutpoints.
-/
def lemmaC4FiniteStepOnIoo
    (successProb : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  lemmaC4FiniteRangeOnIoo successProb lo hi ∧
    ∀ x : ℝ, x ∈ Set.Ioo lo hi →
      ∀ y : ℝ, y ∈ Set.Ioo lo hi →
        ∀ z : ℝ, z ∈ Set.Ioo lo hi →
          x ≤ y → y ≤ z →
            successProb x = successProb z →
              successProb y = successProb x

/--
Monotone finite-range rules are finite-step rules on the interval: each level
fiber is order-convex by monotonicity.
-/
theorem lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo
    {successProb : ℝ → ℝ} {lo hi : ℝ}
    (hmono : Monotone successProb)
    (hfinite : lemmaC4FiniteRangeOnIoo successProb lo hi) :
    lemmaC4FiniteStepOnIoo successProb lo hi := by
  refine ⟨hfinite, ?_⟩
  intro x _hx y _hy z _hz hxy hyz hxz
  have hxy_prob : successProb x ≤ successProb y := hmono hxy
  have hyz_prob : successProb y ≤ successProb z := hmono hyz
  have hyx_prob : successProb y ≤ successProb x := by
    simpa [hxz] using hyz_prob
  exact le_antisymm hyx_prob hxy_prob

/--
Paper-local source convention for Lemma C.4's forward implication in the
constant-weight case.  The source text says the implication follows for
piecewise-constant rules with the appropriate number of levels; in Lean this
means a nontrivial endpoint chain, strict quality cutpoints, and positive
monotone sample rates.  The large-deviation certificate is derived below, not
stored as a field of the model.
-/
structure LemmaC4AppropriateFiniteLevelsConstWeightModel
    (μ : Measure ℝ) : Type where
  m : ℕ
  hm : 1 < m
  cut : ℕ → ℝ
  hmono : Monotone cut
  hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1)
  sampleRate : Fin (m + 2) → ℝ
  hsample_pos :
    ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k
  hsample_mono :
    ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b

/--
Paper-local source convention for Lemma C.4's forward implication with a
general objective weight.  The fields are source/model regularity data:
nontrivial ordered cutpoints, positive monotone sample rates, integrable
nonnegative selected-cell weights, and positive continuous cell-midpoint
witnesses.  The exact large-deviation certificate is derived below.
-/
structure LemmaC4AppropriateFiniteLevelsWeightedModel
    (μ : Measure ℝ) : Type where
  m : ℕ
  hm : 1 < m
  cut : ℕ → ℝ
  hmono : Monotone cut
  hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1)
  sampleRate : Fin (m + 2) → ℝ
  hsample_pos :
    ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k
  hsample_mono :
    ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b
  weight : ℝ × ℝ → ℝ
  hweight_int :
    ∀ component,
      IntegrableOn weight
        ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
        (μ.prod μ)
  hweight_nonneg :
    ∀ component,
      ∀ᵐ x ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
        0 ≤ weight x
  hweight_cont : Continuous weight
  hweight_midpoint_pos :
    ∀ component : theorem31OrderedNontrivialPairComponent m,
      0 < weight
        (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
          component)

/--
Paper-local source convention for Lemma C.4's reverse branch on a supported
quality interval.  These fields are the primitive source regularity
conditions used by the proof: monotonicity and measurability of the Bernoulli
success curve, integrable nonnegative objective weights, positive diagonal
support, and an interior probability/sample-rate region.  The zero-rate and
no-positive-rate conclusions are derived below, not stored as fields.
-/
structure LemmaC4RawSourcePositiveSupportIntervalModel
    (μ : Measure ℝ) : Type where
  lo : ℝ
  hi : ℝ
  hlohi : lo < hi
  successProb : ℝ → ℝ
  sampleRate : ℝ → ℝ
  hprob_mono : Monotone successProb
  hprob0 : ∀ θ, 0 ≤ successProb θ
  hprob1 : ∀ θ, successProb θ ≤ 1
  hprob_meas : Measurable successProb
  hsample_meas : Measurable sampleRate
  weight : ℝ × ℝ → ℝ
  hsource_weight_int :
    Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
  hsource_weight_nonneg :
    ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q
  hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ)
  hweight_diag_cont :
    ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ
  hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ
  hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ)
  hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ
  hprob_interior_on :
    ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1

/--
The source `\bar P_k` kernel associated with a positive-support Lemma C.4
model. This names the paper's floor-count complement error on ordered quality
pairs; it is a definition, not an additional theorem premise.
-/
def lemmaC4RawSourcePbarKernel
    {μ : Measure ℝ}
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ) :
    ℕ → ℝ × ℝ → ℝ :=
  fun k q =>
    twoSampleFloorPkComplementErrorProb
      (binaryRatingModel R.successProb R.hprob0 R.hprob1)
      R.sampleRate q.1 q.2 k

/--
Success-probability step function induced by a finite cutpoint chain and
endpoint levels.  Points outside the displayed cutpoint support are assigned
`0`; on the source support the value is one of the finitely many endpoint
levels.  This is only a source-convention adapter for finite-range reasoning,
not the integral kernel used by `theorem31SourceWbar`.
-/
noncomputable def cutpointStepSuccessProb
    {m : ℕ} (cut : ℕ → ℝ) (levels : Fin (m + 2) → ℝ) (θ : ℝ) : ℝ :=
  if h : ∃ i : Fin (m + 2), cut i.1 < θ ∧ θ ≤ cut (i.1 + 1) then
    levels (Classical.choose h)
  else
    0

/--
Any cutpoint-induced finite step success rule has finite range on every source
interval.  This is the formal bridge from the source phrase "piecewise
constant with finitely many levels" to the finite-range predicate used in the
Lemma C.4 reverse direction.
-/
theorem lemmaC4FiniteRangeOnIoo_cutpointStepSuccessProb
    {m : ℕ} (cut : ℕ → ℝ) (levels : Fin (m + 2) → ℝ)
    (lo hi : ℝ) :
    lemmaC4FiniteRangeOnIoo (cutpointStepSuccessProb cut levels) lo hi := by
  classical
  refine
    Set.Finite.subset
      ((Set.finite_range levels).insert (0 : ℝ)) ?_
  intro value hvalue
  rcases hvalue with ⟨θ, _hθ, rfl⟩
  unfold cutpointStepSuccessProb
  by_cases hcell :
      ∃ i : Fin (m + 2), cut i.1 < θ ∧ θ ≤ cut (i.1 + 1)
  · exact Set.mem_insert_iff.mpr
      (Or.inr ⟨Classical.choose hcell, by simp [hcell]⟩)
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp [hcell]))

/--
Lemma C.4 forward branch under the explicit "appropriate finite levels" source
convention.  Strict cutpoints provide the ordered-rectangle witnesses, and the
forward-clipped endpoint construction supplies the equalized finite levels and
positive source-defined `Wbar_k` exponential-rate certificate.
-/
theorem lemmaC4_appropriate_finite_levels_const_weight_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsConstWeightModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              (fun _ : ℝ × ℝ => (1 : ℝ)))
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  exact
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_const_weight_of_cell_midpoints
      μ S.hm S.cut S.hmono S.hcut_strict S.sampleRate S.hsample_pos
      S.hsample_mono

/--
Lemma C.4 forward branch under the explicit weighted finite-level source
convention.  The selected ordered-rectangle `Wbar_k` certificate is derived
from the finite adjacent-rate optimizer and the finite-partition aggregation
theorem; it is not stored as a model field.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  exact
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
      μ S.hm S.cut S.hmono S.hcut_strict S.sampleRate S.hsample_pos
      S.hsample_mono S.weight S.hweight_int S.hweight_nonneg
      S.hweight_cont S.hweight_midpoint_pos

/--
Theorem 3.1 fixed-discretization two-stage endpoint under the weighted
finite-level source convention.  The model fields supply the source cutpoints,
sample rates, and weight regularity; Lean derives the endpoint levels, exact
`Wbar_k` rate certificate, and fixed-partition lexicographic optimality.
-/
theorem theorem31_appropriate_finite_levels_weighted_fixed_value_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (limitingValue : ℝ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (S.m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, hopt, _hpos, hcert⟩
  refine ⟨levels, hlevels, heq, hcert, ?_⟩
  refine
    theorem31_two_stage_lexicographic_optimality_of_rate_maximizer_on_value_fiber
      (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
      (fun _candidate : Fin (S.m + 2) → ℝ => limitingValue)
      (fun candidate : Fin (S.m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
      levels ?_ ?_
  · exact ⟨hlevels, by intro alt _halt; exact le_rfl⟩
  · refine ⟨⟨hlevels, rfl⟩, ?_⟩
    intro alt halt
    exact hopt.le halt.1

/--
Lemma C.4 forward branch bundled with the finite-range source predicate for
the induced step success rule.  The theorem derives both pieces from the
paper's explicit finite-level source convention: the displayed cutpoint rule is
finite range, and the selected ordered-pair `Wbar_k` has a positive exact
exponential-rate certificate.
-/
theorem lemmaC4_appropriate_finite_levels_const_weight_finiteRange_and_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsConstWeightModel μ)
    (lo hi : ℝ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        lemmaC4FiniteRangeOnIoo (cutpointStepSuccessProb S.cut levels) lo hi ∧
          BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
            AppliedModelingLib.Optimization.IsMaximizerOn
              (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
              (fun candidate : Fin (S.m + 2) → ℝ =>
                binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
              levels ∧
            0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
            ExponentialRateCertificate
              (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
                (fun _ : ℝ × ℝ => (1 : ℝ)))
              (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  rcases
      lemmaC4_appropriate_finite_levels_const_weight_rate_certificate μ S with
    ⟨levels, hlevels, heq, hopt, hpos, hcert⟩
  exact
    ⟨levels, hlevels,
      lemmaC4FiniteRangeOnIoo_cutpointStepSuccessProb S.cut levels lo hi,
      heq, hopt, hpos, hcert⟩

/--
Weighted finite-level source convention bundled with the finite-range
success-probability predicate.  This is the general-weight analogue of
`lemmaC4_appropriate_finite_levels_const_weight_finiteRange_and_rate_certificate`.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_finiteRange_and_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (lo hi : ℝ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        lemmaC4FiniteRangeOnIoo (cutpointStepSuccessProb S.cut levels) lo hi ∧
          BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
            AppliedModelingLib.Optimization.IsMaximizerOn
              (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
              (fun candidate : Fin (S.m + 2) → ℝ =>
                binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
              levels ∧
            0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
            ExponentialRateCertificate
              (theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
                S.weight)
              (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, hopt, hpos, hcert⟩
  exact
    ⟨levels, hlevels,
      lemmaC4FiniteRangeOnIoo_cutpointStepSuccessProb S.cut levels lo hi,
      heq, hopt, hpos, hcert⟩

/-- Fallback endpoint levels for the tiny endpoint-chain cases. -/
noncomputable def canonicalTinyEndpointLevels (m : ℕ) :
    Fin (m + 2) → ℝ :=
  fun i => (i.1 : ℝ) / (m + 1 : ℝ)

/--
Canonical uniform equalized endpoint levels.  For the nontrivial finite
problem this is the unique forward-clipped equalized vector; the tiny cases use
the explicit evenly spaced endpoint vector.
-/
noncomputable def canonicalUniformEqualizedEndpointLevels (m : ℕ) :
    Fin (m + 2) → ℝ :=
  if hm : 1 < m then
    Classical.choose
      (binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
        hm (fun _ : Fin (m + 2) => (1 : ℝ))
        (by
          intro k hk
          simp [binaryEndpointSampleRateNat, hk]))
  else
    canonicalTinyEndpointLevels m

theorem canonicalTinyEndpointLevels_levelVector_of_le_one
    {m : ℕ} (hm : m ≤ 1) :
    BinaryEndpointLevelVector (canonicalTinyEndpointLevels m) := by
  interval_cases m
  · simp [BinaryEndpointLevelVector, canonicalTinyEndpointLevels,
      adjacentLowIndex, adjacentHighIndex]
  · simp [BinaryEndpointLevelVector, canonicalTinyEndpointLevels,
      adjacentLowIndex, adjacentHighIndex]
    norm_num

theorem canonicalTinyEndpointLevels_equalizes_uniform_of_le_one
    {m : ℕ} (hm : m ≤ 1) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (canonicalTinyEndpointLevels m) (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  interval_cases m
  · intro i j
    fin_cases i
    fin_cases j
    rfl
  · intro i j
    have hlog_half : -Real.log ((1 : ℝ) / 2) = Real.log 2 := by
      have h := Real.log_inv (2 : ℝ)
      norm_num at h
      linarith
    have hlog_half_inv :
        -Real.log (1 - ((1 + 1 : ℝ)⁻¹)) = Real.log (1 + 1 : ℝ) := by
      norm_num
      exact hlog_half
    fin_cases i <;> fin_cases j <;>
      simp [binaryEndpointAwareAdjacentRate, canonicalTinyEndpointLevels,
        adjacentLowIndex, adjacentHighIndex] <;>
      first
      | exact hlog_half_inv
      | exact hlog_half_inv.symm

theorem canonicalUniformEqualizedEndpointLevels_levelVector (m : ℕ) :
    BinaryEndpointLevelVector (canonicalUniformEqualizedEndpointLevels m) := by
  unfold canonicalUniformEqualizedEndpointLevels
  by_cases hm : 1 < m
  · simpa [hm] using
      (Classical.choose_spec
        (binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
          hm (fun _ : Fin (m + 2) => (1 : ℝ))
          (by
            intro k hk
            simp [binaryEndpointSampleRateNat, hk]))).1.1
  · have hle : m ≤ 1 := by omega
    simpa [hm] using canonicalTinyEndpointLevels_levelVector_of_le_one hle

theorem canonicalUniformEqualizedEndpointLevels_equalizes_uniform (m : ℕ) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (canonicalUniformEqualizedEndpointLevels m)
      (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  unfold canonicalUniformEqualizedEndpointLevels
  by_cases hm : 1 < m
  · simpa [hm] using
      (Classical.choose_spec
        (binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
          hm (fun _ : Fin (m + 2) => (1 : ℝ))
          (by
            intro k hk
            simp [binaryEndpointSampleRateNat, hk]))).1.2
  · have hle : m ≤ 1 := by omega
    simpa [hm] using
      canonicalTinyEndpointLevels_equalizes_uniform_of_le_one hle

/--
The canonical uniform equalized endpoint levels are finite-rate optimal for the
uniform sample-rate endpoint-aware adjacent objective.
-/
theorem canonicalUniformEqualizedEndpointLevels_isMaximizerOn (m : ℕ) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun xs : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective xs
          (fun _ : Fin (m + 2) => (1 : ℝ)))
      (canonicalUniformEqualizedEndpointLevels m) := by
  by_cases hm : 0 < m
  · exact
      binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
        hm (fun _ : Fin (m + 2) => (1 : ℝ))
        (canonicalUniformEqualizedEndpointLevels m)
        (canonicalUniformEqualizedEndpointLevels_levelVector m)
        (by intro i; norm_num)
        (by intro i; norm_num)
        (canonicalUniformEqualizedEndpointLevels_equalizes_uniform m)
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨canonicalUniformEqualizedEndpointLevels_levelVector 0, ?_⟩
    intro alt halt
    have halt_last : alt (1 : Fin (0 + 2)) = 1 := by
      simpa [lastLevelIndex] using halt.2.1
    have halt_obj :
        binaryEndpointAwareAdjacentRateObjective alt
            (fun _ : Fin (0 + 2) => (1 : ℝ)) = 0 := by
      unfold binaryEndpointAwareAdjacentRateObjective
      exact
        AppliedModelingLib.finiteMin_eq_of_forall
          (fun i : Fin (0 + 1) =>
            binaryEndpointAwareAdjacentRate alt
              (fun _ : Fin (0 + 2) => (1 : ℝ)) i)
          0
          (by
            intro i
            fin_cases i
            simp [binaryEndpointAwareAdjacentRate, adjacentHighIndex,
              halt_last, Real.log_zero])
    have hcanonical_obj :
        binaryEndpointAwareAdjacentRateObjective
            (canonicalUniformEqualizedEndpointLevels 0)
            (fun _ : Fin (0 + 2) => (1 : ℝ)) = 0 := by
      unfold binaryEndpointAwareAdjacentRateObjective
      exact
        AppliedModelingLib.finiteMin_eq_of_forall
          (fun i : Fin (0 + 1) =>
            binaryEndpointAwareAdjacentRate
              (canonicalUniformEqualizedEndpointLevels 0)
              (fun _ : Fin (0 + 2) => (1 : ℝ)) i)
          0
          (by
            intro i
            fin_cases i
            simp [canonicalUniformEqualizedEndpointLevels,
              canonicalTinyEndpointLevels, binaryEndpointAwareAdjacentRate,
              adjacentHighIndex, Real.log_zero])
    change
      binaryEndpointAwareAdjacentRateObjective alt
          (fun _ : Fin (0 + 2) => (1 : ℝ)) ≤
        binaryEndpointAwareAdjacentRateObjective
          (canonicalUniformEqualizedEndpointLevels 0)
          (fun _ : Fin (0 + 2) => (1 : ℝ))
    rw [halt_obj, hcanonical_obj]

/--
Canonical uniform piecewise-constant Lemma C.4 forward direction with midpoint
witnesses.  For the canonical equalized endpoint levels and uniform sampling,
the ordered-rectangle continuum error integral has a positive exponential
rate whenever the source cutpoints are strictly ordered and the objective
weight is locally positive at the selected cell midpoints.
-/
theorem lemmaC4_canonical_uniform_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x *
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                  (fun component k =>
                    twoSampleFloorPkComplementErrorProb
                      (binaryRatingModel
                        (canonicalUniformEqualizedEndpointLevels m)
                        (BinaryEndpointLevelVector_nonneg
                          (canonicalUniformEqualizedEndpointLevels_levelVector m))
                        (BinaryEndpointLevelVector_le_one
                          (canonicalUniformEqualizedEndpointLevels_levelVector m)))
                      (fun _ : Fin (m + 2) => (1 : ℝ))
                      component.val.2 component.val.1 k)
                  k x ∂(μ.prod μ))
        c := by
  exact
    lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
      μ hm cut hmono (canonicalUniformEqualizedEndpointLevels m)
      (fun _ : Fin (m + 2) => (1 : ℝ))
      (canonicalUniformEqualizedEndpointLevels_levelVector m)
      (by intro idx; norm_num)
      (by intro a b _hab; norm_num)
      weight hweight_int hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos
      (canonicalUniformEqualizedEndpointLevels_equalizes_uniform m)

/--
Canonical source-defined `Wbar_k` certificate form of Lemma C.4's
piecewise-constant forward direction.  The selected ordered-rectangle integral
is identified with the paper's source-defined `Wbar_k`, and nonnegativity is
derived from the finite partition decomposition.
-/
theorem theorem31SourceWbar_canonical_uniform_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ cut hmono
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          weight)
        c := by
  rcases
    lemmaC4_canonical_uniform_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints
      μ hm cut hmono hcut_strict weight hweight_int hweight_nonneg
      hweight_cont hweight_midpoint_pos with
    ⟨c, hc, hrate⟩
  refine ⟨c, hc, ?_⟩
  have hrate_source :
      HasExponentialRate
        (theorem31SourceWbar μ cut hmono
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          weight)
        c := by
    exact
      HasExponentialRate.congr
        (theorem31SourceWbar_eventually_eq μ cut hmono
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          weight)
        hrate
  have hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ) := by
    intro component
    exact setIntegral_nonneg_of_ae_restrict (hweight_nonneg component)
  exact
    ExponentialRateCertificate.of_has_rate_of_eventually_nonneg_of_pos_rate
      hrate_source hc
      (theorem31SourceWbar_eventually_nonneg μ cut hmono
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (canonicalUniformEqualizedEndpointLevels m)
        (canonicalUniformEqualizedEndpointLevels_levelVector m)
        weight hweight_int hweight_nonneg_integral)

/--
Canonical source-defined `Wbar_k` certificate for the constant objective
weight.  This discharges the generic weight hypotheses in the source-defined
canonical C.4 forward branch.
-/
theorem theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1)) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ cut hmono
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c := by
  simpa using
    theorem31SourceWbar_canonical_uniform_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
      μ hm cut hmono hcut_strict
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      continuous_const
      (by
        intro component
        norm_num)

/--
Finite Lemma 3.1 optimizer-to-equalization bridge for uniform sample rates.
This packages the canonical equalized witness so downstream source-facing B.1
and Theorem 3.2 bridges can consume finite optimality directly.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hoptimal :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        levels) :
    BinaryEndpointAwareAdjacentRatesEqualize levels
      (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  by_cases hm : 0 < m
  · exact
      (binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_iff_pairwise_equalized
        hm (fun _ : Fin (m + 2) => (1 : ℝ))
        (canonicalUniformEqualizedEndpointLevels m) levels
        (canonicalUniformEqualizedEndpointLevels_levelVector m)
        hoptimal.1
        (by intro i; norm_num)
        (by intro i; norm_num)
        (canonicalUniformEqualizedEndpointLevels_equalizes_uniform m)).1
        hoptimal
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    intro i j
    fin_cases i
    fin_cases j
    rfl

/--
Finite uniform optimal endpoint levels are unique: any endpoint-normalized
maximizer of the uniform adjacent-rate objective is the canonical uniform
equalized endpoint vector.  This removes endpoint-level nonuniqueness from
Theorem B.1; the remaining arbitrary-source issue is the selected interval
index/quantile map, not the finite level vector.
-/
theorem canonicalUniformEqualizedEndpointLevels_eq_of_isMaximizerOn
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hoptimal :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        levels) :
    levels = canonicalUniformEqualizedEndpointLevels m := by
  by_cases hm : 0 < m
  · exact
      binaryEndpointAwareAdjacentRatesEqualize_unique
        hm (fun _ : Fin (m + 2) => (1 : ℝ))
        levels (canonicalUniformEqualizedEndpointLevels m)
        hoptimal.1
        (canonicalUniformEqualizedEndpointLevels_levelVector m)
        (by intro _i; norm_num)
        (by intro _i; norm_num)
        (binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn
          hoptimal)
        (canonicalUniformEqualizedEndpointLevels_equalizes_uniform m)
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    funext i
    fin_cases i
    · simpa [canonicalUniformEqualizedEndpointLevels,
        canonicalTinyEndpointLevels, firstLevelIndex] using hoptimal.1.1
    · simpa [canonicalUniformEqualizedEndpointLevels,
        canonicalTinyEndpointLevels] using hoptimal.1.2.1

/--
Lemma C.4 reverse-branch obstruction.  The source's non-piecewise argument
tries to show that arbitrarily close qualities keep the continuum ranking
error bounded away from zero along arbitrarily large sample sizes.  Once such a
fixed positive lower bound occurs frequently, no positive exponential-rate
certificate can exist.
-/
theorem lemmaC4_no_positive_exponential_rate_certificate_of_frequently_error_ge
    (error : ℕ → ℝ) {ε rate : ℝ}
    (hε : 0 < ε) (hrate : 0 < rate)
    (hfreq : ∃ᶠ k in atTop, ε ≤ error k) :
    ¬ ExponentialRateCertificate error rate :=
  ExponentialRateCertificate.not_of_frequently_ge_pos hrate hε hfreq

/--
Lemma C.4 reverse-branch source-shaped obstruction.  A fixed positive error
lower bound along arbitrarily large sample sizes rules out every positive
exponential-rate certificate.
-/
theorem lemmaC4_no_positive_exponential_rate_certificates_of_frequently_error_ge
    (error : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hfreq : ∃ᶠ k in atTop, ε ≤ error k) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate error rate := by
  intro rate hrate
  exact
    lemmaC4_no_positive_exponential_rate_certificate_of_frequently_error_ge
      error hε hrate hfreq

/--
Lemma C.4 reverse-branch subexponential obstruction.  The source's continuum
argument only needs errors that are frequently larger than `exp (-δ k)` for
every positive `δ`; such subexponential lower witnesses rule out every positive
large-deviation rate.
-/
theorem lemmaC4_no_positive_exponential_rate_certificates_of_subexponential_error
    (error : ℕ → ℝ)
    (hfreq : ∀ δ : ℝ, 0 < δ →
      ∃ᶠ k : ℕ in atTop, Real.exp (-(k : ℝ) * δ) ≤ error k) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate error rate := by
  intro rate hrate
  exact ExponentialRateCertificate.not_of_frequently_ge_subexponential hrate hfreq

/--
Lemma C.4 reverse-branch zero-rate obstruction.  Once the source's
non-piecewise argument has shown exact continuum error rate `0`, uniqueness of
large-deviation rates rules out every positive exact-rate certificate.
-/
theorem lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
    (error : ℕ → ℝ) (hzero : HasExponentialRate error 0) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate error rate := by
  intro rate hrate
  exact ExponentialRateCertificate.not_of_hasExponentialRate_zero hrate hzero

/--
Lemma C.4 source-shaped iff packaging.  To prove the paper's
`piecewise-constant iff positive large-deviation rate` statement, it suffices
to provide a positive-rate certificate in the piecewise-constant case and an
exact zero-rate theorem in the non-piecewise case.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
    (isPiecewiseConstant : Prop) (error : ℕ → ℝ)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate)
    (hzero_reverse : ¬ isPiecewiseConstant → HasExponentialRate error 0) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate :=
  ExponentialRateCertificate.exists_pos_rate_iff_of_forward_and_zero_reverse
    hforward hzero_reverse

/--
Lemma C.4 source-shaped iff packaging with the reverse branch stated directly
as no-positive-rate certificates.  This is the form used by subexponential
lower-bound arguments that rule out every positive exact exponential rate
without first proving an exact zero-rate theorem.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_no_positive_reverse
    (isPiecewiseConstant : Prop) (error : ℕ → ℝ)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate)
    (hno_positive_reverse :
      ¬ isPiecewiseConstant →
        ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate error rate) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate :=
  ExponentialRateCertificate.exists_pos_rate_iff_of_forward_and_no_positive_reverse
    hforward hno_positive_reverse

/--
Lemma C.4 source-shaped iff packaging with the reverse branch stated as the
paper's subexponential lower-hit condition: for every positive target exponent,
the continuum error is frequently at least `exp (-target * k)`.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_subexponential_reverse
    (isPiecewiseConstant : Prop) (error : ℕ → ℝ)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate)
    (hsubexponential_reverse :
      ¬ isPiecewiseConstant →
        ∀ δ : ℝ, 0 < δ →
          ∃ᶠ k : ℕ in atTop, Real.exp (-(k : ℝ) * δ) ≤ error k) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧ ExponentialRateCertificate error rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_no_positive_reverse
    isPiecewiseConstant error hforward
    (fun hnot =>
      lemmaC4_no_positive_exponential_rate_certificates_of_subexponential_error
        error (hsubexponential_reverse hnot))

/--
Lemma C.4 local reverse-branch analytic core.  At an interior continuity point
of the limiting success-probability curve, locally positive sample rates that
are uniformly bounded by `G` force the pairwise closed Bernoulli exponent to
vanish as both qualities approach that point.  This is the reusable finite-rate
ingredient behind the paper's zero-rate obstruction for non-piecewise
continuum rules.
-/
theorem lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
    (successProb sampleRate : ℝ → ℝ) {θ0 G : ℝ}
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G) :
    Filter.Tendsto
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      (𝓝 (θ0, θ0)) (𝓝 0) := by
  have hfst : ContinuousAt (fun q : ℝ × ℝ => q.1) (θ0, θ0) :=
    continuousAt_fst
  have hsnd : ContinuousAt (fun q : ℝ × ℝ => q.2) (θ0, θ0) :=
    continuousAt_snd
  have hβ_hi :
      Filter.Tendsto (fun q : ℝ × ℝ => successProb q.1)
        (𝓝 (θ0, θ0)) (𝓝 (successProb θ0)) :=
    hβ_cont.comp hfst
  have hβ_lo :
      Filter.Tendsto (fun q : ℝ × ℝ => successProb q.2)
        (𝓝 (θ0, θ0)) (𝓝 (successProb θ0)) :=
    hβ_cont.comp hsnd
  have hfixed :
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            G G (successProb q.1) (successProb q.2))
        (𝓝 (θ0, θ0)) (𝓝 0) :=
    weightedBernoulliClosedThresholdRate_tendsto_zero_of_pair_tendsto_same
      hG_pos hG_pos hβ0 hβ1 hβ_hi hβ_lo
  have hg_hi_pos :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), 0 < sampleRate q.1 :=
    hfst.eventually hg_pos
  have hg_lo_pos :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), 0 < sampleRate q.2 :=
    hsnd.eventually hg_pos
  have hg_hi_le :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), sampleRate q.1 ≤ G :=
    hfst.eventually hg_le
  have hg_lo_le :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), sampleRate q.2 ≤ G :=
    hsnd.eventually hg_le
  have hβ_hi_pos :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), 0 < successProb q.1 :=
    hβ_hi.eventually (Ioi_mem_nhds hβ0)
  have hβ_hi_lt :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), successProb q.1 < 1 :=
    hβ_hi.eventually (Iio_mem_nhds hβ1)
  have hβ_lo_pos :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), 0 < successProb q.2 :=
    hβ_lo.eventually (Ioi_mem_nhds hβ0)
  have hβ_lo_lt :
      ∀ᶠ q : ℝ × ℝ in 𝓝 (θ0, θ0), successProb q.2 < 1 :=
    hβ_lo.eventually (Iio_mem_nhds hβ1)
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hfixed ?_ ?_
  · filter_upwards
      [hg_hi_pos, hg_lo_pos, hβ_hi_pos, hβ_hi_lt, hβ_lo_pos, hβ_lo_lt]
      with q hgHi hgLo hpHi0 hpHi1 hpLo0 hpLo1
    exact
      weightedBernoulliClosedThresholdRate_nonneg
        hgHi hgLo hpHi0 hpHi1 hpLo0 hpLo1
  · filter_upwards
      [hg_hi_pos, hg_lo_pos, hg_hi_le, hg_lo_le,
        hβ_hi_pos, hβ_hi_lt, hβ_lo_pos, hβ_lo_lt]
      with q hgHi hgLo hgHi_le hgLo_le hpHi0 hpHi1 hpLo0 hpLo1
    exact
      weightedBernoulliClosedThresholdRate_le_of_weights_le
        hgHi hgLo hG_pos hG_pos hgHi_le hgLo_le
        hpHi0 hpHi1 hpLo0 hpLo1

/--
Continuity of the pairwise closed Bernoulli exponent when the sample-rate and
success-probability curves are continuous at the two quality coordinates.
-/
theorem lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
    (successProb sampleRate : ℝ → ℝ) (q : ℝ × ℝ)
    (hsample_hi_pos : 0 < sampleRate q.1)
    (hsample_lo_pos : 0 < sampleRate q.2)
    (hprob_hi_pos : 0 < successProb q.1)
    (hprob_hi_lt_one : successProb q.1 < 1)
    (hprob_lo_pos : 0 < successProb q.2)
    (hprob_lo_lt_one : successProb q.2 < 1)
    (hsample_hi_cont : ContinuousAt sampleRate q.1)
    (hsample_lo_cont : ContinuousAt sampleRate q.2)
    (hprob_hi_cont : ContinuousAt successProb q.1)
    (hprob_lo_cont : ContinuousAt successProb q.2) :
    ContinuousAt
      (fun r : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate r.1) (sampleRate r.2)
          (successProb r.1) (successProb r.2))
      q :=
  weightedBernoulliClosedThresholdRate_continuousAt
    hsample_hi_pos hsample_lo_pos hprob_hi_pos hprob_hi_lt_one
    hprob_lo_pos hprob_lo_lt_one
    (hsample_hi_cont.comp continuousAt_fst)
    (hsample_lo_cont.comp continuousAt_snd)
    (hprob_hi_cont.comp continuousAt_fst)
    (hprob_lo_cont.comp continuousAt_snd)

/--
Lemma C.4 compact-local uniform-log certificate constructor.  For the
continuum reverse branch, pointwise normalized-log convergence of the pairwise
error kernel to the closed Bernoulli exponent, plus local asymptotic
equicontinuity on a compact parameter superset, supplies the exact
`UniformNormalizedLogRateCertificateOn` object consumed by the Laplace bridge.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_locally_equicontinuous_on_compact_superset
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hpoint :
      ∀ q : ℝ × ℝ, q ∈ K →
        Tendsto (fun k : ℕ => normalizedLogKernelRate kernel k q)
          atTop
          (𝓝
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2))))
    (hrate_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
              |weightedBernoulliClosedThresholdRate
                  (sampleRate r.1) (sampleRate r.2)
                  (successProb r.1) (successProb r.2) -
                weightedBernoulliClosedThresholdRate
                  (sampleRate q.1) (sampleRate q.2)
                  (successProb q.1) (successProb q.2)| ≤ ε)
    (hlog_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
                |normalizedLogKernelRate kernel k r -
                  normalizedLogKernelRate kernel k q| ≤ ε) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_tendsto_locally_equicontinuous_on_compact_superset
    hKcompact hsub hpos hpoint hrate_local hlog_local

/--
Lemma C.4 compact-local uniform-log certificate constructor with the limiting
closed Bernoulli rate's local oscillation discharged by continuity on the
compact parameter superset.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hpoint :
      ∀ q : ℝ × ℝ, q ∈ K →
        Tendsto (fun k : ℕ => normalizedLogKernelRate kernel k q)
          atTop
          (𝓝
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2))))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ K →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    (hlog_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
                |normalizedLogKernelRate kernel k r -
                  normalizedLogKernelRate kernel k q| ≤ ε) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_tendsto_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos hpoint hrate_cont hlog_local

/--
Lemma C.4 compact-local uniform-log certificate constructor with the normalized
log-kernel local-equicontinuity discharged by an eventual Lipschitz bound on
the compact parameter superset.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hpoint :
      ∀ q : ℝ × ℝ, q ∈ K →
        Tendsto (fun k : ℕ => normalizedLogKernelRate kernel k q)
          atTop
          (𝓝
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2))))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ K →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ K → ∀ r : ℝ × ℝ, r ∈ K →
          |normalizedLogKernelRate kernel k r -
            normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos hpoint hrate_cont hL hlog_lipschitz

/--
Lemma C.4 compact-local uniform-log certificate constructor with the closed-rate
continuity side condition derived from global coordinate continuity and
interior probability/rate bounds.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_coordinate_continuity
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hpoint :
      ∀ q : ℝ × ℝ, q ∈ K →
        Tendsto (fun k : ℕ => normalizedLogKernelRate kernel k q)
          atTop
          (𝓝
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2))))
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ K → ∀ r : ℝ × ℝ, r ∈ K →
          |normalizedLogKernelRate kernel k r -
            normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    successProb sampleRate kernel hKcompact hsub hpos hpoint
    (fun q _hq =>
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hsample_cont q.1) (hsample_cont q.2)
        (hprob_cont q.1) (hprob_cont q.2))
    hL hlog_lipschitz

/--
Lemma C.4 compact-local uniform-log certificate constructor from fixed-pair
exact exponential-rate certificates and local asymptotic equicontinuity.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_locally_equicontinuous_on_compact_superset
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ K →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hrate_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
              |weightedBernoulliClosedThresholdRate
                  (sampleRate r.1) (sampleRate r.2)
                  (successProb r.1) (successProb r.2) -
                weightedBernoulliClosedThresholdRate
                  (sampleRate q.1) (sampleRate q.2)
                  (successProb q.1) (successProb q.2)| ≤ ε)
    (hlog_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
                |normalizedLogKernelRate kernel k r -
                  normalizedLogKernelRate kernel k q| ≤ ε) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_locally_equicontinuous_on_compact_superset
    hKcompact hsub hpos hcert hrate_local hlog_local

/--
Lemma C.4 compact-local uniform-log certificate constructor from fixed-pair
certificates, with closed-rate local oscillation discharged by continuity.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ K →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ K →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    (hlog_local :
      ∀ q : ℝ × ℝ, q ∈ K → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ q ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ r : ℝ × ℝ, r ∈ K → r ∈ U →
                |normalizedLogKernelRate kernel k r -
                  normalizedLogKernelRate kernel k q| ≤ ε) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos hcert hrate_cont hlog_local

/--
Lemma C.4 compact-local uniform-log certificate constructor from fixed-pair
certificates, with local-equicontinuity discharged by an eventual Lipschitz
bound on the normalized log-kernels.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ K →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ K →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ K → ∀ r : ℝ × ℝ, r ∈ K →
          |normalizedLogKernelRate kernel k r -
            normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    hKcompact hsub hpos hcert hrate_cont hL hlog_lipschitz

/--
Lemma C.4 compact-local uniform-log certificate constructor from fixed-pair
certificates and an eventual Lipschitz estimate, with closed-rate continuity
derived from global coordinate continuity and interior bounds.
-/
theorem lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_coordinate_continuity
    (successProb sampleRate : ℝ → ℝ)
    (kernel : ℕ → ℝ × ℝ → ℝ)
    {s K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ s → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ K →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ K → ∀ r : ℝ × ℝ, r ∈ K →
          |normalizedLogKernelRate kernel k r -
            normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    UniformNormalizedLogRateCertificateOn kernel
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate
          (sampleRate q.1) (sampleRate q.2)
          (successProb q.1) (successProb q.2))
      s :=
  lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
    successProb sampleRate kernel hKcompact hsub hpos hcert
    (fun q _hq =>
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hsample_cont q.1) (hsample_cont q.2)
        (hprob_cont q.1) (hprob_cont q.2))
    hL hlog_lipschitz

/--
Lemma C.4 reverse-branch Laplace bridge at a continuity point.  If the
source's normalized-log pairwise error kernels converge uniformly to the
closed Bernoulli exponent, then a diagonal continuity point with locally
positive bounded sample rates forces the ordered-pair weighted error integral
to have exact exponential rate `0`.

The remaining source-model work for the non-piecewise branch is to supply the
continuity point, the ordered-pair closure/interior support condition, and the
uniform-log kernel convergence hypotheses from the paper's continuum model.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)} (hcell : MeasurableSet cell)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hcell_closure : (θ0, θ0) ∈ closure (interior cell))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hrate_nonneg :
      ∀ q : ℝ × ℝ, q ∈ cell →
        0 ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcert :
      ExponentialRateCertificate
        (fun k : ℕ =>
          ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
        0 :=
    theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
      (μ.prod μ) hcell weight kernel phi hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound (θ0, θ0) hrate_nonneg hphi_x0
      hphi_cont hweight_cont hweight_x0_pos hcell_closure hkernel_pos
      (by
        intro ε hε
        exact (huniform_log ε hε).mono (by
          intro k hk q
          simpa [phi] using hk q))
  simpa using hcert.has_rate

/--
Lemma C.4 reverse-branch Laplace bridge at a continuity point, with
normalized-log convergence required only on the integration cell.  This is the
cell-local form used when the source proves uniform pairwise LDP estimates
only on the ordered comparison domain.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_on_cell
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)} (hcell : MeasurableSet cell)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hcell_closure : (θ0, θ0) ∈ closure (interior cell))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hrate_nonneg :
      ∀ q : ℝ × ℝ, q ∈ cell →
        0 ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcert :
      ExponentialRateCertificate
        (fun k : ℕ =>
          ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
        0 :=
    theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
      (μ.prod μ) hcell weight kernel phi hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound (θ0, θ0) hrate_nonneg hphi_x0
      hphi_cont hweight_cont hweight_x0_pos hcell_closure hkernel_pos
      (by
        intro ε hε
        exact (huniform_log_on ε hε).mono (by
          intro k hk q hq
          simpa [phi] using hk q hq))
  simpa using hcert.has_rate

/--
Cell-local Lemma C.4 reverse-branch zero-rate bridge for bounded kernels.  A
compact certificate set supplies the uniform normalized-log certificate via
pointwise exact-rate certificates and an eventual Lipschitz estimate; the
diagonal continuity point then supplies the weighted near-zero witness.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {cell certSet : Set (ℝ × ℝ)} (hcell : MeasurableSet cell)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G K L : ℝ}
    (hcertSet_compact : IsCompact certSet)
    (hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, q ∈ certSet)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hcell_closure : (θ0, θ0) ∈ closure (interior cell))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet →
          ∀ r : ℝ × ℝ, r ∈ certSet →
            |normalizedLogKernelRate kernel k r -
              normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcert_uniform :
      UniformNormalizedLogRateCertificateOn kernel phi certSet := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_coordinate_continuity
        successProb sampleRate kernel hcertSet_compact (fun _ hq => hq)
        hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
        hpos hcert hL hlog_lipschitz
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) hcell (θ0, θ0) hK_nonneg hweight_int
      hweight_nonneg hkernel_int hkernel_bound hcert_uniform hcertSet_ae
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos hcell_closure

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge.  For an ordered
quality-pair partition cell, the closed-rectangle compact superset and the
cell-a.e. containment certificate are supplied by the cutpoint partition
itself.
-/
theorem lemmaC4_ordered_quality_pair_piece_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G K L : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)))
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate kernel k r -
                  normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let P :=
    theorem31_ordered_quality_pair_partition μ n cut hmono selected
  let certSet :=
    theorem31_ordered_quality_pair_compactSuperset n cut component.val
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using
      theorem31_ordered_quality_pair_compactSuperset_isCompact
        n cut component.val
  have hpiece_subset :
      P.pieceSet component ⊆ certSet := by
    simpa [P, certSet] using
      theorem31_ordered_quality_pair_piece_subset_compactSuperset
        μ n cut hmono selected component
  have hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict (P.pieceSet component), q ∈ certSet := by
    filter_upwards [ae_restrict_mem (P.measurable_piece component)] with q hq
    exact hpiece_subset hq
  have hcell_closure :
      (θ0, θ0) ∈ closure (interior (P.pieceSet component)) := by
    exact
      theorem31_ordered_quality_pair_piece_mem_closure_interior
        μ n cut hmono selected component (by simpa [P] using hx0_mem)
  simpa [P, certSet] using
    lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact
      μ (P.measurable_piece component) successProb sampleRate weight kernel
      hcertSet_compact hcertSet_ae hK_nonneg hkernel_int hweight_int
      hweight_nonneg hkernel_bound hweight_cont hweight_x0_pos
      hcell_closure hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
      hpos hcert hL hlog_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for the source binary
floor-complement kernel.  The binary LDP library supplies the pointwise
exact-rate certificates and positivity; the remaining analytic input is the
eventual Lipschitz estimate for the normalized log kernel on the closed cell.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_boundedKernel_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G K L : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ =>
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component),
          0 ≤
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∧
            twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  have hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            0 < kernel k q := by
    filter_upwards with k
    intro q _hq
    simpa [kernel, binaryRatingModel] using
      realBinaryRatingLDPModel_floorPkComplementErrorProb_pos_of_lt_one
        successProb hprob0 hprob1 sampleRate q.1 q.2 k
        (hprob_lt_one q.1) (hprob_lt_one q.2)
  have hcert :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)) := by
    intro q hq
    simpa [kernel] using
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hprob_order_on_closed_cell q hq)
  simpa [kernel] using
    lemmaC4_ordered_quality_pair_piece_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate weight kernel
      hK_nonneg hkernel_int hweight_int hweight_nonneg hkernel_bound
      hweight_cont hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0
      hG_pos hg_pos hg_le hsample_pos hprob_pos hprob_lt_one
      hsample_cont hprob_cont hpos hcert hL hlog_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for the concrete
source binary floor-complement kernel, with the bounded-kernel side condition
discharged from the reusable finite-rating probability bounds.  The remaining
kernel-side analytic inputs are integrability of the weighted kernel and the
eventual Lipschitz estimate for the normalized log kernel on the closed cell.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_integrable_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ =>
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component),
          0 ≤
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∧
            twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k⟩
  exact
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_boundedKernel_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight (K := (2 : ℝ)) (θ0 := θ0) (G := G) (L := L)
      (by norm_num) hkernel_int hweight_int hweight_nonneg
      hkernel_bound hweight_cont hweight_x0_pos hx0_mem hβ_cont hβ0
      hβ1 hg0 hG_pos hg_pos hg_le hsample_pos hprob_pos hprob_lt_one
      hsample_cont hprob_cont hprob_order_on_closed_cell hL hlog_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for the concrete
source binary floor-complement kernel, with both the bounded-kernel and
weighted-kernel integrability certificates discharged from the reusable
finite-rating probability bound plus measurability of the concrete kernel.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let cell :=
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
      component
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel] using hkernel_meas k)
      hkernel_bound
  simpa [cell, kernel] using
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_integrable_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight (θ0 := θ0) (G := G) (L := L)
      (by simpa [cell, kernel] using hkernel_int)
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos hx0_mem
      hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le hsample_pos hprob_pos
      hprob_lt_one hsample_cont hprob_cont hprob_order_on_closed_cell hL
      hlog_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for the concrete
source binary floor-complement kernel from a direct uniform normalized-log
certificate on the closed-cell superset.  This is the clean formal boundary
for the remaining analytic work: once the source's pairwise floor-count error
kernel is known to converge uniformly in normalized-log rate on each closed
cell, the continuum cell integral has exact exponential rate zero.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformNormalizedLogRateCertificate_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert_uniform :
      UniformNormalizedLogRateCertificateOn
        (fun k q =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (theorem31_ordered_quality_pair_compactSuperset n cut component.val)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let P :=
    theorem31_ordered_quality_pair_partition μ n cut hmono selected
  let cell := P.pieceSet component
  let certSet :=
    theorem31_ordered_quality_pair_compactSuperset n cut component.val
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [P, cell] using hweight_int)
      (by
        intro k
        simpa [P, cell, kernel] using hkernel_meas k)
      hkernel_bound
  have hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, q ∈ certSet := by
    have hpiece_subset : P.pieceSet component ⊆ certSet := by
      simpa [P, certSet] using
        theorem31_ordered_quality_pair_piece_subset_compactSuperset
          μ n cut hmono selected component
    filter_upwards [ae_restrict_mem (P.measurable_piece component)] with q hq
    exact hpiece_subset hq
  have hcell_closure :
      (θ0, θ0) ∈ closure (interior cell) := by
    exact
      theorem31_ordered_quality_pair_piece_mem_closure_interior
        μ n cut hmono selected component (by simpa [P, cell] using hx0_mem)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  simpa [P, cell, certSet, kernel, phi] using
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ)
      (cell := cell) (certSet := certSet) (kernel := kernel) (rate := phi)
      (P.measurable_piece component) (θ0, θ0) (K := (2 : ℝ))
      (by norm_num) (by simpa [P, cell] using hweight_int)
      (by simpa [P, cell] using hweight_nonneg)
      hkernel_int hkernel_bound
      (by simpa [certSet, kernel, phi] using hcert_uniform)
      hcertSet_ae hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      hcell_closure

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for the concrete
source binary floor-complement kernel from a uniform exponential-sandwich
certificate on the closed-cell superset.  This is the Chernoff-style boundary:
the reusable library converts the uniform sandwich into the normalized-log
certificate consumed by the continuum Laplace argument.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformExponentialRateCertificate_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert_uniform :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (theorem31_ordered_quality_pair_compactSuperset n cut component.val)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 :=
  lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformNormalizedLogRateCertificate_on_closed_cell_superset
    μ cut hmono selected component successProb sampleRate hprob0 hprob1
    weight hkernel_meas hweight_int hweight_nonneg hweight_cont
    hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
    hcert_uniform.toUniformNormalizedLogRateCertificateOn

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge from a left-tail
uniform exponential-sandwich certificate.  This is the source-shaped
Chernoff/Cramér interface: prove uniform exponential envelopes for the
left-tail score-gap kernel on the closed cell, then the finite-rating
constant-factor sandwich transfers the certificate to the paper's
floor-complement kernel.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (theorem31_ordered_quality_pair_compactSuperset n cut component.val)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let M := binaryRatingModel successProb hprob0 hprob1
  have hcert_uniform :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (theorem31_ordered_quality_pair_compactSuperset n cut component.val) := by
    simpa [M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformExponentialRateCertificate_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hcert_uniform

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge from the source
left-tail normalized-log regularity hypothesis.  The binary LDP library
derives the pointwise left-tail Cramer certificates and left-tail positivity;
compactness plus the eventual Lipschitz estimate upgrade them to a uniform
exponential certificate, and the paper's `Pk` sandwich transfers that
certificate to the floor-complement kernel used in the integral.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let certSet :=
    theorem31_ordered_quality_pair_compactSuperset n cut component.val
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using
      theorem31_ordered_quality_pair_compactSuperset_isCompact
        n cut component.val
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q _hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hsample_cont q.1) (hsample_cont q.2)
        (hprob_cont q.1) (hprob_cont q.2)
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_eventually_lipschitz_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q _hq => hsample_pos q.1)
        (fun q _hq => hsample_pos q.2)
        (fun q _hq => hprob_pos q.1)
        (fun q _hq => hprob_lt_one q.1)
        (fun q _hq => hprob_pos q.2)
        (fun q _hq => hprob_lt_one q.2)
        hprob_order_on_closed_cell
        (by simpa [phi, certSet] using hrate_cont)
        hL
        (by simpa [certSet, binaryRatingModel] using hleft_tail_log_lipschitz)
  simpa [leftKernel, phi, certSet] using
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hcert_left_tail

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge from the source
left-tail normalized-log regularity hypothesis, with the binary LDP
regularity assumptions localized to the closed compact superset of the cell.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset_of_compact
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos_on :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          0 < sampleRate q.1 ∧ 0 < sampleRate q.2)
    (hprob_pos_on :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          0 < successProb q.1 ∧ 0 < successProb q.2)
    (hprob_lt_one_on :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.1 < 1 ∧ successProb q.2 < 1)
    (hsample_cont_on :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          ContinuousAt sampleRate q.1 ∧ ContinuousAt sampleRate q.2)
    (hprob_cont_on :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          ContinuousAt successProb q.1 ∧ ContinuousAt successProb q.2)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  let certSet :=
    theorem31_ordered_quality_pair_compactSuperset n cut component.val
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using
      theorem31_ordered_quality_pair_compactSuperset_isCompact
        n cut component.val
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos_on q hq).1 (hsample_pos_on q hq).2
        (hprob_pos_on q hq).1 (hprob_lt_one_on q hq).1
        (hprob_pos_on q hq).2 (hprob_lt_one_on q hq).2
        (hsample_cont_on q hq).1 (hsample_cont_on q hq).2
        (hprob_cont_on q hq).1 (hprob_cont_on q hq).2
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_eventually_lipschitz_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q hq => (hsample_pos_on q hq).1)
        (fun q hq => (hsample_pos_on q hq).2)
        (fun q hq => (hprob_pos_on q hq).1)
        (fun q hq => (hprob_lt_one_on q hq).1)
        (fun q hq => (hprob_pos_on q hq).2)
        (fun q hq => (hprob_lt_one_on q hq).2)
        (by simpa [certSet] using hprob_order_on_closed_cell)
        (by simpa [phi, certSet] using hrate_cont)
        hL
        (by simpa [certSet, binaryRatingModel] using hleft_tail_log_lipschitz)
  simpa [leftKernel, phi, certSet] using
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hcert_left_tail

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge from the source
left-tail normalized-log regularity hypothesis, with kernel measurability
discharged from global continuity of the success-probability and sample-rate
functions.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  have hprob_meas : Measurable successProb :=
    (continuous_iff_continuousAt.2 hprob_cont).measurable
  have hsample_meas : Measurable sampleRate :=
    (continuous_iff_continuousAt.2 hsample_cont).measurable
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
      hprob_order_on_closed_cell hL hleft_tail_log_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for high-low closed
cells.  This is the same left-tail Lipschitz entry point as
`..._leftTail_eventually_lipschitz_on_closed_cell_superset`, but it derives
the required probability order from monotonicity of `β` and the fact that the
second coordinate cell is below the first.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (hcomponent_order : component.val.2.val + 1 ≤ component.val.1.val)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  have hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1 :=
    theorem31_ordered_quality_pair_compactSuperset_successProb_snd_le_fst_of_mono_of_index_snd_succ_le_fst
      hmono hcomponent_order hprob_mono
  exact
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
      hprob_order_on_closed_cell hL hleft_tail_log_lipschitz

/--
Selected-cell Lemma C.4 reverse-branch zero-rate bridge for high-low closed
cells, with kernel measurability discharged from global continuity of the
success-probability and sample-rate functions.
-/
theorem lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {n : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (component : {piece : Fin n × Fin n // selected piece})
    (hcomponent_order : component.val.2.val + 1 ≤ component.val.1.val)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {θ0 G L : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
            component),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hx0_mem :
      (θ0, θ0) ∈
        (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          component)
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
            ∀ r : ℝ × ℝ,
              r ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
              component))
      0 := by
  have hprob_order_on_closed_cell :
      ∀ q : ℝ × ℝ,
        q ∈ theorem31_ordered_quality_pair_compactSuperset n cut component.val →
          successProb q.2 ≤ successProb q.1 :=
    theorem31_ordered_quality_pair_compactSuperset_successProb_snd_le_fst_of_mono_of_index_snd_succ_le_fst
      hmono hcomponent_order hprob_mono
  exact
    lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_cell_superset
      μ cut hmono selected component successProb sampleRate hprob0 hprob1
      weight hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hx0_mem hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le hsample_pos
      hprob_pos hprob_lt_one hsample_cont hprob_cont
      hprob_order_on_closed_cell hL hleft_tail_log_lipschitz

/--
Lemma C.4 reverse-branch zero-rate bridge with the analytic work isolated as
local lower envelopes.  This version avoids assuming a full uniform-log
Laplace certificate: if the weighted error integral is eventually bounded
above by a positive constant and every positive target rate has a
positive-measure local exponential lower envelope, then the reverse branch has
exact exponential rate zero.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_constant_upper_bound_and_near_minimizer_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell) ≤ B)
    (hlower_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ,
        0 < ((μ.prod μ).restrict cell).real nearMinimizers ∧
          0 < c ∧
            (∀ k : ℕ,
              IntegrableOn
                (fun q : ℝ × ℝ => weight q * kernel k q)
                nearMinimizers ((μ.prod μ).restrict cell)) ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ᵐ q ∂((μ.prod μ).restrict cell).restrict nearMinimizers,
                  c * Real.exp (-(k : ℝ) * targetRate) ≤
                    weight q * kernel k q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  theoremC1_integral_error_zero_rate_from_constant_upper_bound_and_near_minimizer_sets
    ((μ.prod μ).restrict cell)
    (fun k q => weight q * kernel k q)
    hBpos hkernel_int hkernel_nonneg hupper_const hlower_sets

/--
Lemma C.4 reverse-branch zero-rate bridge from a source-style
normalized-log certificate and local near-rate sets.  This is the restricted
ordered-pair form of the reusable C.1 zero-rate skeleton: the analytic
obligation is reduced to finding positive-measure regions where the limiting
pairwise rate is strictly below each positive target and the weight is locally
positive.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell certSet : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel phi certSet)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict cell).real nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              nearMinimizers ⊆ certSet ∧
                (∀ k : ℕ,
                  IntegrableOn
                    (fun q : ℝ × ℝ => weight q * kernel k q)
                    nearMinimizers ((μ.prod μ).restrict cell)) ∧
                  (∀ᵐ q ∂((μ.prod μ).restrict cell).restrict nearMinimizers,
                    c ≤ weight q) ∧
                    ∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                      phi q + δ ≤ targetRate) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_nearRate_sets
    ((μ.prod μ).restrict cell) weight kernel phi hBpos hkernel_int
    hkernel_nonneg hupper_const hcert hnear_sets

/--
Lemma C.4 reverse-branch zero-rate bridge with local normalized-log
certificates for probability kernels.  Compared with the preceding
constant-upper-bound version, the upper bound and nonnegativity side
conditions are derived from `0 ≤ kernel ≤ 1` and a nonnegative integrable
weight.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ)
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ 1)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict cell).real nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers ((μ.prod μ).restrict cell)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict cell).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    ((μ.prod μ).restrict cell) hweight_int hweight_nonneg hkernel_int
    hkernel_unit hnear_sets

/--
Lemma C.4 reverse-branch zero-rate bridge with local normalized-log
certificates for kernels bounded by a fixed nonnegative constant.  This
variant covers the paper's `1 - P_k` error kernel, which is bounded by `2`
rather than by `1`.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict cell).real nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers ((μ.prod μ).restrict cell)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict cell).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    ((μ.prod μ).restrict cell) hK_nonneg hweight_int hweight_nonneg
    hkernel_int hkernel_bound hnear_sets

/--
Lemma C.4 reverse-branch zero-rate bridge with local normalized-log
certificates for bounded kernels, deriving product integrability from
restricted kernel measurability and the uniform kernel bound.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable (kernel k) ((μ.prod μ).restrict cell))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict cell).real nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers ((μ.prod μ).restrict cell)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict cell).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_kernel_aestronglyMeasurable
    ((μ.prod μ).restrict cell) hK_nonneg hweight_int hweight_nonneg
    hkernel_meas hkernel_bound hnear_sets

/--
Lemma C.4 reverse-branch zero-rate bridge from compact pointwise exact-rate
certificates and an eventual Lipschitz estimate for bounded kernels.  This is
the ordered-pair specialization of the reusable compact-Lipschitz zero-rate
theorem.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact_weightedNearInf
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell certSet : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K L : ℝ}
    (hcertSet_compact : IsCompact certSet)
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ExponentialRateCertificate (fun k : ℕ => kernel k q) (phi q))
    (hphi_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet →
          ∀ r : ℝ × ℝ, r ∈ certSet →
            |normalizedLogKernelRate kernel k r -
              normalizedLogKernelRate kernel k q| ≤ L * dist r q)
    (hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, q ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((μ.prod μ).restrict cell) weight phi 0) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseCertificates_eventually_lipschitz_on_compact_weightedNearInf_of_ae_mem_certSet
    ((μ.prod μ).restrict cell) hcertSet_compact hK_nonneg hweight_int
    hweight_nonneg hkernel_int hkernel_bound hpos hcert hphi_cont hL
    hlog_lipschitz hcertSet_ae hweighted_near

/--
Lemma C.4 reverse-branch zero-rate bridge from a source-style normalized-log
certificate and the weighted near-essential-infimum interface at rate zero on
the restricted ordered-pair cell.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel phi Set.univ)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((μ.prod μ).restrict cell) weight phi 0) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf
    ((μ.prod μ).restrict cell) weight kernel phi hBpos hkernel_int
    hkernel_nonneg hupper_const hcert hweighted_near

/--
Lemma C.4 reverse-branch zero-rate bridge from a source-style normalized-log
certificate on an almost-everywhere full cell-local set and the weighted
near-essential-infimum interface at rate zero.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell certSet : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel phi certSet)
    (hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, q ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((μ.prod μ).restrict cell) weight phi 0) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    ((μ.prod μ).restrict cell) weight kernel phi hBpos hkernel_int
    hkernel_nonneg hupper_const hcert hcertSet_ae hweighted_near

/--
Lemma C.4 reverse-branch zero-rate bridge from a bounded kernel, a
source-style normalized-log certificate on an a.e. full cell-local set, and
the weighted near-essential-infimum interface.  Product integrability and the
constant upper bound are derived from kernel measurability and `0 ≤ kernel ≤ K`.
-/
theorem lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    {cell certSet : Set (ℝ × ℝ)}
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable (kernel k) ((μ.prod μ).restrict cell))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hcert : UniformNormalizedLogRateCertificateOn kernel phi certSet)
    (hcertSet_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, q ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((μ.prod μ).restrict cell) weight phi 0) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict cell)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
    ((μ.prod μ).restrict cell) hK_nonneg hweight_int hweight_nonneg
    hkernel_meas hkernel_bound hcert hcertSet_ae hweighted_near

/--
Lemma C.4 strict ordered-pair zero-rate bridge from a normalized-log
certificate on the strict ordered-pair domain and the weighted
near-essential-infimum interface for the restricted measure.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) ≤ B)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel phi
        AppliedModelingLib.strictUpperPairSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) weight phi 0) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 :=
  lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    μ weight kernel phi hBpos hkernel_int hkernel_nonneg hupper_const hcert
    (ae_restrict_mem AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet)
    hweighted_near

/--
Lemma C.4 strict ordered-pair zero-rate bridge with local normalized-log
certificates for probability kernels.  This is the cell-local source-shaped
entry point for the non-piecewise reverse branch when the pairwise comparison
kernel is known to be a probability.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ 1)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 :=
  lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_probabilityKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    μ weight kernel phi hweight_int hweight_nonneg hkernel_int
    hkernel_unit hnear_sets

/--
Lemma C.4 strict ordered-pair zero-rate bridge with local normalized-log
certificates for kernels bounded by a fixed nonnegative constant.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 :=
  lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    μ weight kernel phi hK_nonneg hweight_int hweight_nonneg hkernel_int
    hkernel_bound hnear_sets

/--
Lemma C.4 tie-erased source-`Wbar_k` zero-rate bridge with local normalized-log
certificates.  This is the source-facing near-diagonal form of the reverse
argument: the paper's tie-erased kernel is integrated over strict ordered
pairs, and each positive target rate is witnessed by a positive-measure
near-rate set with its own local uniform normalized-log certificate.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      sourcePbarKernel phi nearMinimizers)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 := by
  let integralError : ℕ → ℝ := fun k =>
    ∫ q in AppliedModelingLib.strictUpperPairSet,
      weight q * sourcePbarKernel k q ∂(μ.prod μ)
  have hintegral :
      HasExponentialRate integralError 0 := by
    simpa [integralError] using
      lemmaC4_strictUpperPair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
        μ weight sourcePbarKernel phi hK_nonneg hsource_weight_int
        hsource_weight_nonneg hsource_kernel_int hsource_kernel_bound
        hnear_sets
  have heq : integralError =ᶠ[atTop] sourceWbar := by
    filter_upwards [hsourceWbar_eq] with k hk
    exact hk.symm
  exact HasExponentialRate.congr heq hintegral

/--
Lemma C.4 tie-erased source-`Wbar_k` zero-rate bridge with local near-rate
certificates, deriving the global source-integral integrability from
AEStronglyMeasurable bounded kernels.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      sourcePbarKernel phi nearMinimizers)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 := by
  let integralError : ℕ → ℝ := fun k =>
    ∫ q in AppliedModelingLib.strictUpperPairSet,
      weight q * sourcePbarKernel k q ∂(μ.prod μ)
  have hintegral :
      HasExponentialRate integralError 0 := by
    simpa [integralError] using
      lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
        (cell := AppliedModelingLib.strictUpperPairSet)
        μ weight sourcePbarKernel phi hK_nonneg hsource_weight_int
        hsource_weight_nonneg hsource_kernel_meas hsource_kernel_bound
        hnear_sets
  have heq : integralError =ᶠ[atTop] sourceWbar := by
    filter_upwards [hsourceWbar_eq] with k hk
    exact hk.symm
  exact HasExponentialRate.congr heq hintegral

/--
Lemma C.4 tie-erased source-`Wbar_k` no-positive-rate bridge with local
near-rate certificates.  This is the exact certificate-level obstruction
needed by the source's non-piecewise reverse branch.
-/
theorem lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      sourcePbarKernel phi nearMinimizers)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate sourceWbar rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate sourceWbar
    (lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ weight sourcePbarKernel sourceWbar phi hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_int
      hsource_kernel_bound hnear_sets hsourceWbar_eq)

/--
Lemma C.4 tie-erased source-`Wbar_k` no-positive-rate bridge with local
near-rate certificates and measurable bounded kernels.
-/
theorem lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      sourcePbarKernel phi nearMinimizers)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate sourceWbar rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate sourceWbar
    (lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
      μ weight sourcePbarKernel sourceWbar phi hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_meas
      hsource_kernel_bound hnear_sets hsourceWbar_eq)

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with the reverse branch
stated as source near-rate witnesses.  The forward direction is supplied by the
piecewise-constant construction; the non-piecewise branch only needs the
paper's moving near-diagonal lower-bound data for the tie-erased kernel.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_near_sets :
      ¬ isPiecewiseConstant →
        ∀ targetRate : ℝ, 0 < targetRate →
          ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
            MeasurableSet nearMinimizers ∧
              0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
                nearMinimizers ∧
              0 < c ∧ 0 < δ ∧
                (∀ k : ℕ,
                  IntegrableOn
                    (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                    nearMinimizers
                    ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                  phi q + δ ≤ targetRate) ∧
                UniformNormalizedLogRateCertificateOn
                  sourcePbarKernel phi nearMinimizers) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWbar hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ weight sourcePbarKernel sourceWbar phi hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_int
      hsource_kernel_bound (hnonpiecewise_near_sets hnot_piecewise)
      hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with measurable bounded
source kernels.  This is the same source near-rate statement as
`..._nonpiecewise_nearRate_sets`, with the global integrability obligation
derived from the source kernel measurability and bound.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    (phi : ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_near_sets :
      ¬ isPiecewiseConstant →
        ∀ targetRate : ℝ, 0 < targetRate →
          ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
            MeasurableSet nearMinimizers ∧
              0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
                nearMinimizers ∧
              0 < c ∧ 0 < δ ∧
                (∀ k : ℕ,
                  IntegrableOn
                    (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                    nearMinimizers
                    ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                  phi q + δ ≤ targetRate) ∧
                UniformNormalizedLogRateCertificateOn
                  sourcePbarKernel phi nearMinimizers) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWbar hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel
      μ weight sourcePbarKernel sourceWbar phi hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_meas
      hsource_kernel_bound (hnonpiecewise_near_sets hnot_piecewise)
      hsourceWbar_eq

/--
Strict ordered-pair near-rate witnesses at a diagonal zero of the limiting
rate.  This exposes the local set construction used by the continuum Laplace
lower-bound proof so source-facing statements can consume explicit
near-minimizer certificates rather than redoing the measure argument.
-/
theorem lemmaC4_strictUpperPair_localUniformNormalizedLogRateCertificate_nearRate_sets_of_continuousAt_zero
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : ℝ × ℝ → ℝ) {θ0 : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hphi_x0 : phi (θ0, θ0) = 0)
    (hphi_cont : ContinuousAt phi (θ0, θ0))
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel phi
        AppliedModelingLib.strictUpperPairSet) :
    ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    phi q + δ ≤ targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel phi nearMinimizers :=
  localUniformNormalizedLogRateCertificate_nearRate_sets_of_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
    (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
    hkernel_int hcert (fun _q hq => hq) (θ0, θ0) hphi_x0
    hphi_cont hweight_cont hweight_x0_pos
    (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 strict ordered-pair near-rate witnesses for the pairwise closed
Bernoulli rate at a diagonal continuity point.  The source rate vanishes on
the diagonal, and the generic library construction supplies the positive
measure near-diagonal sets.
-/
theorem lemmaC4_strictUpperPair_pairwise_closed_rate_nearRate_sets_of_continuity_point_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
            nearMinimizers ∧
            0 < c ∧ 0 < δ ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun q : ℝ × ℝ => weight q * kernel k q)
                  nearMinimizers
                  ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                (∀ᵐ q ∂((μ.prod μ).restrict
                    AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                  c ≤ weight q) ∧
                  (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                    weightedBernoulliClosedThresholdRate
                      (sampleRate q.1) (sampleRate q.2)
                      (successProb q.1) (successProb q.2) + δ ≤
                      targetRate) ∧
                    UniformNormalizedLogRateCertificateOn
                      kernel
                      (fun q : ℝ × ℝ =>
                        weightedBernoulliClosedThresholdRate
                          (sampleRate q.1) (sampleRate q.2)
                          (successProb q.1) (successProb q.2))
                      nearMinimizers := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  simpa [phi] using
    lemmaC4_strictUpperPair_localUniformNormalizedLogRateCertificate_nearRate_sets_of_continuousAt_zero
      μ weight kernel phi hkernel_int hweight_cont hweight_x0_pos
      hphi_x0 hphi_cont hcert

/--
Lemma C.4 tie-erased source-`Wbar_k` zero-rate bridge at a diagonal
continuity point.  This removes the explicit near-rate-set premise from the
source-facing bounded-kernel wrapper: the near-diagonal positive-measure sets
are derived from continuity of the Bernoulli exponent and positivity of the
diagonal weight.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hnear_sets :
      ∀ targetRate : ℝ, 0 < targetRate →
        ∃ nearMinimizers : Set (ℝ × ℝ), ∃ c : ℝ, ∃ δ : ℝ,
          MeasurableSet nearMinimizers ∧
            0 < ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet).real
              nearMinimizers ∧
              0 < c ∧ 0 < δ ∧
                (∀ k : ℕ,
                  IntegrableOn
                    (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
                    nearMinimizers
                    ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)) ∧
                  (∀ᵐ q ∂((μ.prod μ).restrict
                      AppliedModelingLib.strictUpperPairSet).restrict nearMinimizers,
                    c ≤ weight q) ∧
                    (∀ q : ℝ × ℝ, q ∈ nearMinimizers →
                      phi q + δ ≤ targetRate) ∧
                      UniformNormalizedLogRateCertificateOn
                        sourcePbarKernel phi nearMinimizers := by
    simpa [phi] using
      lemmaC4_strictUpperPair_pairwise_closed_rate_nearRate_sets_of_continuity_point_uniformNormalizedLogRateCertificate_on_strictUpperPair
        μ successProb sampleRate weight sourcePbarKernel
        hsource_kernel_int hweight_cont hweight_x0_pos hβ_cont
        hβ0 hβ1 hg0 hG_pos hg_pos hg_le hcert
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets
      μ weight sourcePbarKernel sourceWbar phi hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_int
      hsource_kernel_bound hnear_sets hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` zero-rate bridge at a diagonal
continuity point with measurable bounded source kernels.  This version keeps
the source-facing assumptions at the paper's bounded-kernel regularity level:
global strict-pair integrability is derived from measurability and the uniform
kernel bound.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 := by
  have hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      hsource_weight_int hsource_kernel_meas hsource_kernel_bound
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight sourcePbarKernel sourceWbar
      (θ0 := θ0) (G := G) hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_int hsource_kernel_bound
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos
      hg_pos hg_le hcert hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` no-positive-rate bridge at a diagonal
continuity point.  Exact zero rate rules out every positive exponential-rate
certificate for the source `Wbar_k` sequence.
-/
theorem lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate sourceWbar rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate sourceWbar
    (lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight sourcePbarKernel sourceWbar hK_nonneg
      hsource_weight_int hsource_weight_nonneg hsource_kernel_int
      hsource_kernel_bound hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1
      hg0 hG_pos hg_pos hg_le hcert hsourceWbar_eq)

/--
Lemma C.4 tie-erased source-`Wbar_k` no-positive-rate bridge at a diagonal
continuity point with measurable bounded source kernels.
-/
theorem lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate sourceWbar rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate sourceWbar
    (lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
      μ successProb sampleRate weight sourcePbarKernel sourceWbar
      (θ0 := θ0) (G := G) hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_meas hsource_kernel_bound
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos
      hg_pos hg_le hcert hsourceWbar_eq)

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with the
non-piecewise reverse branch stated at the paper's continuity-point level.
Compared with the earlier near-rate-set interface, the local positive-measure
sets are now derived internally from the continuity point and strict-pair
normalized-log certificate.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_point :
      ¬ isPiecewiseConstant →
        ∃ θ0 G : ℝ,
          ContinuousAt weight (θ0, θ0) ∧
          0 < weight (θ0, θ0) ∧
          ContinuousAt successProb θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          0 < sampleRate θ0 ∧
          0 < G ∧
          (∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ) ∧
          (∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWbar hforward ?_
  intro hnot_piecewise
  rcases hnonpiecewise_point hnot_piecewise with
    ⟨θ0, G, hweight_cont, hweight_x0_pos, hβ_cont, hβ0, hβ1,
      hg0, hG_pos, hg_pos, hg_le⟩
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight sourcePbarKernel sourceWbar
      (θ0 := θ0) (G := G) hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_int hsource_kernel_bound
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos
      hg_pos hg_le hcert hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with the
non-piecewise reverse branch stated at the paper's continuity-point level and
measurable bounded source kernels.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_point :
      ¬ isPiecewiseConstant →
        ∃ θ0 G : ℝ,
          ContinuousAt weight (θ0, θ0) ∧
          0 < weight (θ0, θ0) ∧
          ContinuousAt successProb θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          0 < sampleRate θ0 ∧
          0 < G ∧
          (∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ) ∧
          (∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWbar hforward ?_
  intro hnot_piecewise
  rcases hnonpiecewise_point hnot_piecewise with
    ⟨θ0, G, hweight_cont, hweight_x0_pos, hβ_cont, hβ0, hβ1,
      hg0, hG_pos, hg_pos, hg_le⟩
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
      μ successProb sampleRate weight sourcePbarKernel sourceWbar
      (θ0 := θ0) (G := G) hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_meas hsource_kernel_bound
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos
      hg_pos hg_le hcert hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with the
non-piecewise reverse branch stated as a single regular continuity point.
Compared with `..._continuity_point_witness_of_measurableKernel`, this wrapper
derives the local sample-rate upper bound `G` from continuity at the point.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_regular_point_witness_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_point :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          ContinuousAt weight (θ0, θ0) ∧
          0 < weight (θ0, θ0) ∧
          ContinuousAt sampleRate θ0 ∧
          0 < sampleRate θ0 ∧
          ContinuousAt successProb θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness_of_measurableKernel
      μ isPiecewiseConstant successProb sampleRate weight sourcePbarKernel
      sourceWbar hK_nonneg hsource_weight_int hsource_weight_nonneg
      hsource_kernel_meas hsource_kernel_bound hcert hsourceWbar_eq
      hforward ?_
  intro hnot_piecewise
  rcases hnonpiecewise_point hnot_piecewise with
    ⟨θ0, hweight_cont, hweight_x0_pos, hsample_cont, hsample_pos,
      hβ_cont, hβ0, hβ1⟩
  rcases AppliedModelingLib.exists_pos_eventually_le_of_continuousAt hsample_cont with
    ⟨G, hG_pos, hg_le⟩
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    hsample_cont.eventually (Ioi_mem_nhds hsample_pos)
  exact
    ⟨θ0, G, hweight_cont, hweight_x0_pos, hβ_cont, hβ0, hβ1,
      hsample_pos, hG_pos, hg_pos, hg_le⟩

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff with a concrete
stepwise-on-interval convention and the reverse branch stated at the paper's
interior continuity-point level.  This is the `Wbar_k` analogue of the raw
source `W^k` continuity-point wrapper: positivity of the source primitives on
the ambient interval supplies the regular point required by the zero-rate
obstruction.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_interior_continuity_point_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ}
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ θ0 : ℝ,
          θ0 ∈ Set.Ioo lo hi ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_regular_point_witness_of_measurableKernel
      μ (isStepwiseConstantOn successProb lo hi) successProb sampleRate
      weight sourcePbarKernel sourceWbar hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_meas hsource_kernel_bound
      hcert hsourceWbar_eq hforward ?_
  intro hnot_step
  rcases hpoint hnot_step with
    ⟨θ0, hθ0, hβ0, hβ1, hβ_cont⟩
  exact
    ⟨θ0, hweight_cont θ0, hweight_pos_on θ0 hθ0,
      hsample_cont θ0, hsample_pos_on θ0 hθ0, hβ_cont, hβ0, hβ1⟩

/--
Lemma C.4 strict ordered-pair zero-rate bridge at a diagonal continuity point,
using only a constant upper bound, nonnegativity, and a normalized-log
certificate on the strict ordered-pair domain.  The local positive
near-minimizer sets are derived internally from continuity of the pairwise
Bernoulli rate and positivity of the objective weight at the diagonal point.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) ≤ B)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
      (θ0, θ0) hBpos hkernel_int hkernel_nonneg hupper_const hcert
      (ae_restrict_mem AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet)
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 reverse-branch monotone-interval bridge using the constant-upper-bound
zero-rate theorem.  A monotone non-piecewise success-probability curve has an
interior continuity point on every nonempty interval, and local boundedness of
sample rates is derived from continuity there.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_nonneg :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * kernel k q)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) ≤ B)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight kernel hBpos hkernel_int
      hkernel_nonneg hupper_const (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont (hprob_pos θ0)
      (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le hcert

/--
Lemma C.4 strict ordered-pair zero-rate bridge at a diagonal continuity point
for probability kernels.  The weighted integral upper bound and nonnegativity
are derived from `0 ≤ kernel ≤ 1` and nonnegative integrable weights.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_probabilityKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ 1)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_probabilityKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
      (θ0, θ0) hweight_int hweight_nonneg hkernel_int hkernel_unit hcert
      (ae_restrict_mem AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet)
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 strict ordered-pair zero-rate bridge at a diagonal continuity point
for kernels bounded by a fixed nonnegative constant.  This is the bounded
variant needed by `1 - P_k` kernels, whose natural bound is `2`.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
      (θ0, θ0) hK_nonneg hweight_int hweight_nonneg hkernel_int
      hkernel_bound hcert
      (ae_restrict_mem AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet)
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 strict ordered-pair zero-rate bridge for bounded kernels, deriving
product integrability from restricted kernel measurability and `0 ≤ kernel ≤ K`.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable (kernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
      (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
      (θ0, θ0) hK_nonneg hweight_int hweight_nonneg hkernel_meas
      hkernel_bound hcert
      (ae_restrict_mem AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet)
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 strict ordered-pair zero-rate bridge at a diagonal continuity point,
with the uniform normalized-log certificate constructed from pointwise exact
certificates and an eventual Lipschitz estimate on a compact superset of the
strict ordered-pair domain.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {certSet : Set (ℝ × ℝ)} {θ0 G K L : ℝ}
    (hcertSet_compact : IsCompact certSet)
    (hstrict_subset : AppliedModelingLib.strictUpperPairSet ⊆ certSet)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.strictUpperPairSet → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet →
          ∀ r : ℝ × ℝ, r ∈ certSet →
            |normalizedLogKernelRate kernel k r -
              normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hcert_uniform :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet :=
    UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
      hcertSet_compact hstrict_subset hpos hcert hrate_cont hL
      hlog_lipschitz
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight kernel hK_nonneg hkernel_int
      hweight_int hweight_nonneg hkernel_bound hweight_cont
      hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hcert_uniform

/--
Lemma C.4 reverse-branch monotone-interval bridge for probability kernels.
The weighted integral upper bound is derived from `0 ≤ kernel ≤ 1` and
nonnegative integrable weights; the source-model input is the uniform
normalized-log certificate for the pairwise error kernel.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_probabilityKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ 1)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
      (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_probabilityKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight kernel hkernel_int hweight_int
      hweight_nonneg hkernel_unit (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont (hprob_pos θ0)
      (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le hcert

/--
Lemma C.4 reverse-branch monotone-interval bridge for kernels bounded by a
fixed nonnegative constant.  This is the continuity-point bounded-kernel
entry point for the paper's `1 - P_k` comparison-error convention.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
      (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight kernel hK_nonneg hkernel_int
      hweight_int hweight_nonneg hkernel_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont (hprob_pos θ0)
      (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le hcert

/--
Lemma C.4 monotone-interval bridge for bounded kernels, with the uniform
normalized-log certificate derived from pointwise exact-rate certificates and
an eventual Lipschitz estimate on a compact superset.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {certSet : Set (ℝ × ℝ)} {a b K L : ℝ}
    (hcertSet_compact : IsCompact certSet)
    (hstrict_subset : AppliedModelingLib.strictUpperPairSet ⊆ certSet)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hpos :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.strictUpperPairSet → 0 < kernel k q)
    (hcert :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ExponentialRateCertificate
          (fun k : ℕ => kernel k q)
          (weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2)))
    (hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet →
        ContinuousAt
          (fun r : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate
              (sampleRate r.1) (sampleRate r.2)
              (successProb r.1) (successProb r.2))
          q)
    (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ certSet →
          ∀ r : ℝ × ℝ, r ∈ certSet →
            |normalizedLogKernelRate kernel k r -
              normalizedLogKernelRate kernel k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
      (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact
      μ successProb sampleRate weight kernel hcertSet_compact hstrict_subset
      hK_nonneg hkernel_int hweight_int hweight_nonneg hkernel_bound
      (hweight_cont θ0 hθ0) (hweight_x0_pos θ0 hθ0) hβ_cont
      (hprob_pos θ0) (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le hpos hcert hrate_cont hL
      hlog_lipschitz

/--
Lemma C.4 reverse-branch Laplace bridge specialized to the paper's strict
ordered-pair domain `θ_2 < θ_1`.  The diagonal closure/interior support
condition is discharged by the reusable ordered-pair topology lemma.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hrate_nonneg :
      ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSet →
        0 ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 :=
  lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point
    μ AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
    successProb sampleRate weight kernel hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound hweight_cont hweight_x0_pos
    (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)
    hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le hrate_nonneg hkernel_pos
    huniform_log

/--
Lemma C.4 reverse-branch strict ordered-pair bridge with normalized-log
convergence required only on the strict ordered-pair domain.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hrate_nonneg :
      ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSet →
        0 ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSet →
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 :=
  lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_on_cell
    μ AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
    successProb sampleRate weight kernel hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound hweight_cont hweight_x0_pos
    (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)
    hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le hrate_nonneg hkernel_pos
    huniform_log_on

/--
Lemma C.4 strict ordered-pair zero-rate bridge with the usual global interior
Bernoulli and positive sample-rate hypotheses.  This variant derives the
closed-rate nonnegativity and local sample positivity assumptions internally.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hβ_cont : ContinuousAt successProb θ0)
    (hG_pos : 0 < G)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  refine
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound hweight_cont hweight_x0_pos hβ_cont
      (hprob_pos θ0) (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le ?_ hkernel_pos huniform_log
  intro q _hq
  exact
    weightedBernoulliClosedThresholdRate_nonneg
      (hsample_pos q.1) (hsample_pos q.2)
      (hprob_pos q.1) (hprob_lt_one q.1)
      (hprob_pos q.2) (hprob_lt_one q.2)

/--
Lemma C.4 strict ordered-pair zero-rate bridge using the shared
`UniformNormalizedLogRateCertificateOn` interface for the source's pairwise
error kernels.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hβ_cont : ContinuousAt successProb θ0)
    (hG_pos : 0 < G)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        Set.univ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  refine
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound hweight_cont hweight_x0_pos
      hprob_pos hprob_lt_one hsample_pos hβ_cont hG_pos hg_le
      hkernel_pos ?_
  intro ε hε
  exact hcert.uniform_raw_log_univ ε hε

/--
Lemma C.4 strict ordered-pair zero-rate bridge using a
uniform-normalized-log certificate only on the strict ordered-pair domain.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {θ0 G W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hβ_cont : ContinuousAt successProb θ0)
    (hG_pos : 0 < G)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  refine
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_on_strictUpperPair
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound hweight_cont hweight_x0_pos hβ_cont
      (hprob_pos θ0) (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le ?_ hkernel_pos ?_
  · intro q _hq
    exact
      weightedBernoulliClosedThresholdRate_nonneg
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
  · intro ε hε
    exact hcert.uniform_raw_log ε hε

/--
Lemma C.4 reverse-branch strict ordered-pair bridge with the source's monotone
success-probability regularity.  A monotone Bernoulli curve has an interior
continuity point on every nonempty quality interval; if sample rates are
continuous there, the local boundedness constant required by the Laplace
bridge is derived internally.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          |(-Real.log (kernel k q) / (k : ℝ)) -
            weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hprob_pos hprob_lt_one hsample_pos
      hβ_cont hG_pos hg_le hkernel_pos huniform_log

/--
Lemma C.4 reverse-branch monotone-interval bridge with the standard
uniform-normalized-log certificate interface.  This is the most compact
source-shaped entry point for proving the non-piecewise zero-rate branch once
the paper's pairwise kernel LDP certificate is available.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        Set.univ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hprob_pos hprob_lt_one hsample_pos
      hβ_cont hG_pos hg_le hkernel_pos hcert

/--
Lemma C.4 reverse-branch monotone-interval bridge with a
uniform-normalized-log certificate only on the strict ordered-pair domain.
This is the cell-local source-shaped entry point for the non-piecewise
zero-rate branch.
-/
theorem lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate_on_strictUpperPair
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, weight q ≤ W)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hkernel_pos : ∀ k q, 0 < kernel k q)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂(μ.prod μ).restrict
          AppliedModelingLib.strictUpperPairSet)
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate_on_strictUpperPair
      μ successProb sampleRate weight kernel hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hprob_pos hprob_lt_one hsample_pos
      hβ_cont hG_pos hg_le hkernel_pos hcert

/--
Lemma C.4 raw strict ordered-pair floor-complement bridge.  For the concrete
binary floor-count complement kernel on the global strict ordered-pair domain,
monotone interior success probabilities and positive sample rates give the
pointwise Cramer certificates needed by the continuous zero-rate Laplace
bridge.  This is the raw-integral companion to the source `W^k` convention;
the paper-specific step is still to relate the source's global error to this
raw strict-pair integral on the chosen non-piecewise witness region.
-/
theorem lemmaC4_strictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSet
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    Eventually.of_forall hsample_pos
  let rate : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hrate_tendsto :
      Filter.Tendsto rate (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [rate] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont (hprob_pos θ0) (hprob_lt_one θ0)
        hG_pos hg_pos hg_le
  have hrate_x0 : rate (θ0, θ0) = 0 := by
    simp [rate, weightedBernoulliClosedThresholdRate_self
      (hsample_pos θ0) (hsample_pos θ0) (hprob_pos θ0)
      (hprob_lt_one θ0)]
  have hrate_cont : ContinuousAt rate (θ0, θ0) := by
    simpa [ContinuousAt, hrate_x0] using hrate_tendsto
  have hkernel_meas : ∀ k : ℕ, Measurable (kernel k) := by
    intro k
    simpa [kernel, M, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        exact (hkernel_meas k).aestronglyMeasurable)
      hkernel_bound
  have hcert :
      ∀ q : ℝ × ℝ, q ∈ cell →
        ExponentialRateCertificate (fun k : ℕ => kernel k q) (rate q) := by
    intro q hq
    have hqord : successProb q.2 ≤ successProb q.1 :=
      hprob_mono (le_of_lt hq)
    simpa [kernel, M, rate] using
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        hqord
  simpa [cell, kernel, M, rate] using
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
      (μ.prod μ) AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
      (cell := cell) (certSet := cell) (weight := weight) (kernel := kernel)
      (rate := rate) (K := (2 : ℝ)) (θ0, θ0) (by norm_num)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      hkernel_int hkernel_bound hkernel_meas (by intro q hq; exact hq)
      hcert hrate_x0 hrate_cont (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0)
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSet θ0)

/--
Lemma C.4 bounded strict ordered-pair bridge at a diagonal continuity point.
This is the compact-domain version matching the source's `[0,1]` quality
space: the integral is restricted to `a ≤ θ₂ < θ₁ ≤ b`, while the uniform
normalized-log certificate only needs to hold on the compact box
`[a,b] × [a,b]`.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b θ0 G K : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedPairBox a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcell_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  have hcert_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        q ∈ AppliedModelingLib.closedPairBox a b :=
    (ae_restrict_mem hcell_meas).mono fun q hq =>
      AppliedModelingLib.strictUpperPairSetOn_subset_closedPairBox a b hq
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) hcell_meas (θ0, θ0) hK_nonneg hweight_int
      hweight_nonneg hkernel_int hkernel_bound hcert hcert_ae hphi_x0
      hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSetOn hθ0)

/--
Lemma C.4 bounded strict ordered-pair bridge at a diagonal continuity point
with the uniform normalized-log certificate only on the closed upper triangle
`a ≤ θ₂ ≤ θ₁ ≤ b`. This is the certificate domain used by monotone
high-low pair models.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b θ0 G K : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcell_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  have hcert_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b :=
    (ae_restrict_mem hcell_meas).mono fun q hq =>
      AppliedModelingLib.strictUpperPairSetOn_subset_closedUpperPairSetOn a b hq
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet
      (μ.prod μ) hcell_meas (θ0, θ0) hK_nonneg hweight_int
      hweight_nonneg hkernel_int hkernel_bound hcert hcert_ae hphi_x0
      hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSetOn hθ0)

/--
Lemma C.4 bounded strict ordered-pair bridge at a diagonal continuity point
from pointwise exponential-rate certificates on the closed upper triangle.
Compared with the uniform-normalized-log version above, this lower-bound
route only needs pointwise Cramer certificates; the positive-measure
near-diagonal subset is extracted by the shared large-deviation library.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwiseExponentialRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b θ0 G K : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hkernel_meas : ∀ k : ℕ, Measurable (kernel k))
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2))) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcell_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
      (μ.prod μ) hcell_meas (θ0, θ0) hK_nonneg hweight_int
      hweight_nonneg hkernel_int hkernel_bound hkernel_meas
      (AppliedModelingLib.strictUpperPairSetOn_subset_closedUpperPairSetOn a b)
      (by simpa [phi] using hcert) hphi_x0 hphi_cont hweight_cont
      hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSetOn hθ0)

/--
Lemma C.4 bounded strict ordered-pair bridge on the closed upper triangle,
deriving product integrability from restricted kernel measurability and
`0 ≤ kernel ≤ K`.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b θ0 G K : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hK_nonneg : 0 ≤ K)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable (kernel k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hphi_tendsto :
      Filter.Tendsto phi (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hphi_x0 : phi (θ0, θ0) = 0 := by
    simp [phi, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hphi_cont : ContinuousAt phi (θ0, θ0) := by
    simpa [ContinuousAt, hphi_x0] using hphi_tendsto
  have hcell_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  have hcert_ae :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b :=
    (ae_restrict_mem hcell_meas).mono fun q hq =>
      AppliedModelingLib.strictUpperPairSetOn_subset_closedUpperPairSetOn a b hq
  exact
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_uniformNormalizedLogRateCertificateOn_continuousAt_zero_weight_pos_restrict_closure_interior_of_ae_mem_certSet_of_kernel_aestronglyMeasurable
      (μ.prod μ) hcell_meas (θ0, θ0) hK_nonneg hweight_int
      hweight_nonneg hkernel_meas hkernel_bound hcert hcert_ae
      hphi_x0 hphi_cont hweight_cont hweight_x0_pos
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSetOn hθ0)

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete source
floor-complement kernel from pointwise binary Cramer certificates.  This
removes the compact-uniform normalized-log regularity premise from the
near-diagonal lower-bound branch; the shared large-deviation library extracts
the required common lower envelope on a positive-measure subset.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  have hkernel_meas : ∀ k : ℕ, Measurable (kernel k) := by
    intro k
    simpa [kernel, M, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        exact (hkernel_meas k).aestronglyMeasurable)
      hkernel_bound
  have hcert :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)) := by
    intro q hq
    have hqord : successProb q.2 ≤ successProb q.1 :=
      hprob_mono (AppliedModelingLib.closedUpperPairSetOn_snd_le_fst hq)
    simpa [kernel, M] using
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        hqord
  simpa [cell, kernel, M] using
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwiseExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel
      (a := a) (b := b) (θ0 := θ0) (G := G) (K := (2 : ℝ))
      hθ0 (by norm_num)
      (by simpa [cell, kernel] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel] using hkernel_bound)
      hkernel_meas hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1
      hg0 hG_pos hg_pos hg_le hcert

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete
floor-complement kernel on a compact quality interval.  All rating-model
positivity assumptions are required only on `[a,b]`; the only success-curve
continuity needed is at the selected diagonal point.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  have hθ0_Icc : θ0 ∈ Set.Icc a b := ⟨hθ0.1.le, hθ0.2.le⟩
  have hβ0 : 0 < successProb θ0 :=
    hprob_pos_on θ0 hθ0_Icc
  have hβ1 : successProb θ0 < 1 :=
    hprob_lt_one_on θ0 hθ0_Icc
  have hg0 : 0 < sampleRate θ0 :=
    hsample_pos_on θ0 hθ0_Icc
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont_on θ0 hθ0_Icc)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont_on θ0 hθ0_Icc).eventually
      (isOpen_Ioi.mem_nhds hg0)
  have hkernel_meas : ∀ k : ℕ, Measurable (kernel k) := by
    intro k
    simpa [kernel, M, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        exact (hkernel_meas k).aestronglyMeasurable)
      hkernel_bound
  have hcert :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (weightedBernoulliClosedThresholdRate
              (sampleRate q.1) (sampleRate q.2)
              (successProb q.1) (successProb q.2)) := by
    intro q hq
    have hq1 : q.1 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq
    have hq2 : q.2 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq
    have hqord : successProb q.2 ≤ successProb q.1 :=
      hprob_mono (AppliedModelingLib.closedUpperPairSetOn_snd_le_fst hq)
    simpa [kernel, M] using
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2
        (hsample_pos_on q.1 hq1) (hsample_pos_on q.2 hq2)
        (hprob_pos_on q.1 hq1) (hprob_lt_one_on q.1 hq1)
        (hprob_pos_on q.2 hq2) (hprob_lt_one_on q.2 hq2)
        hqord
  simpa [cell, kernel, M] using
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwiseExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel
      (a := a) (b := b) (θ0 := θ0) (G := G) (K := (2 : ℝ))
      hθ0 (by norm_num)
      (by simpa [cell, kernel] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel] using hkernel_bound)
      hkernel_meas hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1
      hg0 hG_pos hg_pos hg_le hcert

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from pointwise
binary Cramer certificates.  Monotonicity supplies an interior continuity
point of the success curve, and the shared large-deviation library supplies
the positive-measure lower-bound extraction.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    exact ⟨hprob_pos_on θ hθ_Icc, hprob_lt_one_on θ hθ_Icc⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box_of_Icc
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight (a := a) (b := b) (θ0 := θ0)
      hθ0 hweight_int hweight_nonneg (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on

/--
Local-to-global integral monotonicity for the C.4 strict ordered-pair regions.
The bounded interval witness region `strictUpperPairSetOn a b` is a subset of
the global strict ordered-pair domain, so a nonnegative local error integral is
bounded by the corresponding global error integral.
-/
theorem lemmaC4_strictUpperPairSetOn_integral_le_strictUpperPair_integral
    (μ : Measure ℝ) (f : ℝ × ℝ → ℝ) {a b : ℝ}
    (hf_int : IntegrableOn f AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hf_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ f q) :
    ∫ q in AppliedModelingLib.strictUpperPairSetOn a b, f q ∂(μ.prod μ) ≤
      ∫ q in AppliedModelingLib.strictUpperPairSet, f q ∂(μ.prod μ) :=
  setIntegral_mono_subset_of_ae_nonneg hf_int hf_nonneg
    (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)

/--
Local-to-global C.4 source-kernel bridge.  If the paper's global error kernel
agrees with the raw floor-complement kernel on the chosen bounded witness
region, and the global source integrand is nonnegative, then the local raw
integral is a lower bound on the source global error integral.

This is the formal shape of the remaining convention check for Lemma C.4:
on the non-piecewise witness region, the source `W^k` integrand must coincide
with the raw pairwise floor-complement error used by the local LDP theorem.
-/
theorem lemmaC4_strictUpperPairSetOn_raw_integral_le_source_strictUpperPair_integral_of_eq_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ} (k : ℕ)
    (hglobal_int :
      IntegrableOn
        (fun q : ℝ × ℝ => weight q * sourceKernel k q)
        AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hglobal_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
        sourceKernel k q = rawKernel k q) :
    (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
      weight q * rawKernel k q ∂(μ.prod μ)) ≤
      ∫ q in AppliedModelingLib.strictUpperPairSet,
        weight q * sourceKernel k q ∂(μ.prod μ) := by
  have hlocal_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  exact
    setIntegral_mono_subset_of_eqOn_of_ae_nonneg
      (μ := μ.prod μ)
      (s := AppliedModelingLib.strictUpperPairSetOn a b)
      (t := AppliedModelingLib.strictUpperPairSet)
      (localF := fun q : ℝ × ℝ => weight q * rawKernel k q)
      (globalF := fun q : ℝ × ℝ => weight q * sourceKernel k q)
      hlocal_meas hglobal_int hglobal_nonneg
      (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)
      (by
        intro q hq
        dsimp
        rw [hsource_eq_raw_on q hq])

/--
Local-to-global C.4 source-kernel bridge with a one-sided witness comparison.
This weakens the equality convention: it is enough that the local raw
floor-complement integrand is bounded above by the source global integrand on
the chosen witness interval.
-/
theorem lemmaC4_strictUpperPairSetOn_raw_integral_le_source_strictUpperPair_integral_of_le_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ} (k : ℕ)
    (hlocal_int :
      IntegrableOn
        (fun q : ℝ × ℝ => weight q * rawKernel k q)
        (AppliedModelingLib.strictUpperPairSetOn a b) (μ.prod μ))
    (hglobal_int :
      IntegrableOn
        (fun q : ℝ × ℝ => weight q * sourceKernel k q)
        AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hglobal_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q * sourceKernel k q)
    (hsource_raw_le_on :
      ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
        weight q * rawKernel k q ≤ weight q * sourceKernel k q) :
    (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
      weight q * rawKernel k q ∂(μ.prod μ)) ≤
      ∫ q in AppliedModelingLib.strictUpperPairSet,
        weight q * sourceKernel k q ∂(μ.prod μ) := by
  have hlocal_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  exact
    AppliedModelingLib.Probability.setIntegral_mono_subset_of_leOn_of_ae_nonneg
      (μ := μ.prod μ)
      (s := AppliedModelingLib.strictUpperPairSetOn a b)
      (t := AppliedModelingLib.strictUpperPairSet)
      (localF := fun q : ℝ × ℝ => weight q * rawKernel k q)
      (globalF := fun q : ℝ × ℝ => weight q * sourceKernel k q)
      hlocal_meas hlocal_int hglobal_int hglobal_nonneg
      (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)
      hsource_raw_le_on

/--
Eventual source-minorant bridge for Lemma C.4.  If the source `W^k` error is
eventually the global strict ordered-pair integral of the source kernel, and
that source kernel agrees with the raw local floor-complement kernel on the
witness region, then the local raw obstruction is eventually bounded by the
source error.
-/
theorem lemmaC4_sourceWError_eventually_raw_floorPk_local_le_of_eq_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ) {a b : ℝ}
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q = rawKernel k q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ)) ≤ sourceWError k := by
  filter_upwards [hsource_int, hsource_nonneg, hsource_eq_raw_on,
      hsourceWError_eq] with k hk_int hk_nonneg hk_eq hk_source
  calc
    (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ))
        ≤ ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ) :=
      lemmaC4_strictUpperPairSetOn_raw_integral_le_source_strictUpperPair_integral_of_eq_on_witness
        μ weight rawKernel sourceKernel (a := a) (b := b) k
        hk_int hk_nonneg hk_eq
    _ = sourceWError k := hk_source.symm

/--
Eventual source-minorant bridge with a one-sided local witness comparison.
The local raw obstruction may be bounded above by, rather than equal to, the
paper's global source integrand on the witness interval.
-/
theorem lemmaC4_sourceWError_eventually_raw_floorPk_local_le_of_le_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ) {a b : ℝ}
    (hlocal_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * rawKernel k q)
          (AppliedModelingLib.strictUpperPairSetOn a b) (μ.prod μ))
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_raw_le_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          weight q * rawKernel k q ≤ weight q * sourceKernel k q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ)) ≤ sourceWError k := by
  filter_upwards [hlocal_int, hsource_int, hsource_nonneg,
      hsource_raw_le_on, hsourceWError_eq] with
    k hk_local_int hk_int hk_nonneg hk_le hk_source
  calc
    (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ))
        ≤ ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ) :=
      lemmaC4_strictUpperPairSetOn_raw_integral_le_source_strictUpperPair_integral_of_le_on_witness
        μ weight rawKernel sourceKernel (a := a) (b := b) k
        hk_local_int hk_int hk_nonneg hk_le
    _ = sourceWError k := hk_source.symm

/--
Eventual source-minorant bridge over an arbitrary witness cell.  This is the
set-local version used when the source kernel agrees with the raw kernel only
on a supplied non-piecewise witness region, rather than on the whole rectangle.
-/
theorem lemmaC4_sourceWError_eventually_raw_local_le_of_eq_on_witness_cell
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ) {cell : Set (ℝ × ℝ)}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell → sourceKernel k q = rawKernel k q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in cell, weight q * rawKernel k q ∂(μ.prod μ)) ≤
        sourceWError k := by
  filter_upwards [hsource_int, hsource_nonneg, hsource_eq_raw_on,
      hsourceWError_eq] with k hk_int hk_nonneg hk_eq hk_source
  calc
    (∫ q in cell, weight q * rawKernel k q ∂(μ.prod μ))
        ≤ ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ) :=
      setIntegral_mono_subset_of_eqOn_of_ae_nonneg
        (μ := μ.prod μ)
        (s := cell)
        (t := AppliedModelingLib.strictUpperPairSet)
        (localF := fun q : ℝ × ℝ => weight q * rawKernel k q)
        (globalF := fun q : ℝ × ℝ => weight q * sourceKernel k q)
        hcell_meas hk_int hk_nonneg hcell_subset_strict
        (by
          intro q hq
          dsimp
          rw [hk_eq q hq])
    _ = sourceWError k := hk_source.symm

/--
Eventual source-minorant bridge over an arbitrary witness cell with a one-sided
local comparison.  This is the cell-local analogue of
`lemmaC4_sourceWError_eventually_raw_floorPk_local_le_of_le_on_witness`.
-/
theorem lemmaC4_sourceWError_eventually_raw_local_le_of_le_on_witness_cell
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ) {cell : Set (ℝ × ℝ)}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hlocal_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * rawKernel k q)
          cell (μ.prod μ))
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_raw_le_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          weight q * rawKernel k q ≤ weight q * sourceKernel k q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in cell, weight q * rawKernel k q ∂(μ.prod μ)) ≤
        sourceWError k := by
  filter_upwards [hlocal_int, hsource_int, hsource_nonneg,
      hsource_raw_le_on, hsourceWError_eq] with
    k hk_local_int hk_int hk_nonneg hk_le hk_source
  calc
    (∫ q in cell, weight q * rawKernel k q ∂(μ.prod μ))
        ≤ ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ) :=
      AppliedModelingLib.Probability.setIntegral_mono_subset_of_leOn_of_ae_nonneg
        (μ := μ.prod μ)
        (s := cell)
        (t := AppliedModelingLib.strictUpperPairSet)
        (localF := fun q : ℝ × ℝ => weight q * rawKernel k q)
        (globalF := fun q : ℝ × ℝ => weight q * sourceKernel k q)
        hcell_meas hk_local_int hk_int hk_nonneg hcell_subset_strict hk_le
    _ = sourceWError k := hk_source.symm

/--
Lemma C.4 raw floor-complement zero-rate bridge over an arbitrary witness
cell.  This is closer to the source non-piecewise argument than the rectangular
version: a caller may supply exactly the near-diagonal region on which the
source `W^k` kernel coincides with the raw pairwise floor-complement error.
-/
theorem lemmaC4_witnessCell_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q in cell,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂(μ.prod μ))
      0 := by
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let rate : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hβ0 : 0 < successProb θ0 :=
    hprob_pos_on θ0 hθ0_Icc
  have hβ1 : successProb θ0 < 1 :=
    hprob_lt_one_on θ0 hθ0_Icc
  have hg0 : 0 < sampleRate θ0 :=
    hsample_pos_on θ0 hθ0_Icc
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont_on θ0 hθ0_Icc)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont_on θ0 hθ0_Icc).eventually
      (isOpen_Ioi.mem_nhds hg0)
  have hrate_tendsto :
      Filter.Tendsto rate (𝓝 (θ0, θ0)) (𝓝 0) := by
    simpa [rate] using
      lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point
        successProb sampleRate hβ_cont hβ0 hβ1 hG_pos hg_pos hg_le
  have hrate_x0 : rate (θ0, θ0) = 0 := by
    simp [rate, weightedBernoulliClosedThresholdRate_self
      hg0 hg0 hβ0 hβ1]
  have hrate_cont : ContinuousAt rate (θ0, θ0) := by
    simpa [ContinuousAt, hrate_x0] using hrate_tendsto
  have hkernel_meas : ∀ k : ℕ, Measurable (kernel k) := by
    intro k
    simpa [kernel, M, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      hweight_int
      (by
        intro k
        exact (hkernel_meas k).aestronglyMeasurable)
      hkernel_bound
  have hcert :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
          ExponentialRateCertificate
            (fun k : ℕ => kernel k q)
            (rate q) := by
    intro q hq
    have hq1 : q.1 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq
    have hq2 : q.2 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq
    have hqord : successProb q.2 ≤ successProb q.1 :=
      hprob_mono (AppliedModelingLib.closedUpperPairSetOn_snd_le_fst hq)
    simpa [kernel, M, rate] using
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2
        (hsample_pos_on q.1 hq1) (hsample_pos_on q.2 hq2)
        (hprob_pos_on q.1 hq1) (hprob_lt_one_on q.1 hq1)
        (hprob_pos_on q.2 hq2) (hprob_lt_one_on q.2 hq2)
        hqord
  simpa [kernel, M] using
    weightedKernelIntegral_hasExponentialRate_zero_of_boundedKernel_pointwiseExponentialRateCertificate_continuousAt_zero_weight_pos_restrict_closure_interior_of_cell_subset_certSet
      (μ.prod μ) hcell_meas (cell := cell)
      (certSet := AppliedModelingLib.closedUpperPairSetOn a b) (weight := weight)
      (kernel := kernel) (rate := rate) (K := (2 : ℝ)) (θ0, θ0)
      (by norm_num) hweight_int hweight_nonneg hkernel_int
      hkernel_bound hkernel_meas hcell_subset_closed_upper hcert hrate_x0
      hrate_cont hweight_cont hweight_x0_pos hθ0_closure

/--
The raw floor-complement witness integral is strictly positive on every
sample size. The weight is positive on a positive-measure subset of the
witness cell by continuity and closure/interior support, while the
floor-complement binary error has positive pointwise mass whenever both
success probabilities are below one.
-/
theorem lemmaC4_witnessCell_floorPkComplementError_integral_pos_of_weight_pos_closure_interior
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 : ℝ}
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1) :
    ∀ k : ℕ,
      0 <
        ∫ q in cell,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂(μ.prod μ) := by
  intro k
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernelFam : ℕ → ℝ × ℝ → ℝ :=
    fun n q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 n
  let kernel : ℝ × ℝ → ℝ := kernelFam k
  have hkernel_meas : Measurable kernel := by
    simpa [kernel, kernelFam, M, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernelFam_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable (kernelFam n) ((μ.prod μ).restrict cell) := by
    intro n
    exact
      ((by
        simpa [kernelFam, M, binaryRatingModel] using
          realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
            successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas n) :
        Measurable (kernelFam n)).aestronglyMeasurable
  have hkernelFam_bound :
      ∀ n : ℕ, ∀ᵐ q ∂(μ.prod μ).restrict cell,
        0 ≤ kernelFam n q ∧ kernelFam n q ≤ (2 : ℝ) := by
    intro n
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 n,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 n⟩
  have hkernel_bound :
      ∀ᵐ q ∂(μ.prod μ).restrict cell,
        0 ≤ kernel q ∧ kernel q ≤ (2 : ℝ) := by
    simpa [kernel] using hkernelFam_bound k
  have hprod_int :
      Integrable (fun q : ℝ × ℝ => weight q * kernel q)
        ((μ.prod μ).restrict cell) :=
    (integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ)) hweight_int
      hkernelFam_meas hkernelFam_bound k)
      |>.congr (by simp [kernel])
  have hprod_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q * kernel q := by
    filter_upwards [hweight_nonneg, hkernel_bound] with q hw hk
    exact mul_nonneg hw hk.1
  have htarget : {y : ℝ | 0 < y} ∈ nhds (weight (θ0, θ0)) :=
    IsOpen.mem_nhds isOpen_Ioi hweight_x0_pos
  have hpre : {q : ℝ × ℝ | 0 < weight q} ∈ 𝓝 (θ0, θ0) :=
    hweight_cont htarget
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  have hμ_pos : 0 < (μ.prod μ) (cell ∩ U) :=
    HasAEEssentialInfimum.local_pos_of_mem_closure_interior
      (μ.prod μ) hθ0_closure U hUopen hxU
  have hsupport_pos :
      0 < (μ.prod μ) (Function.support
          (fun q : ℝ × ℝ => weight q * kernel q) ∩ cell) := by
    refine lt_of_lt_of_le hμ_pos (measure_mono ?_)
    intro q hq
    have hq_closed : q ∈ AppliedModelingLib.closedUpperPairSetOn a b :=
      hcell_subset_closed_upper hq.1
    have hq1_Icc : q.1 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq_closed
    have hq2_Icc : q.2 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq_closed
    have hkpos : 0 < kernel q := by
      simpa [kernel, kernelFam, M, binaryRatingModel] using
        realBinaryRatingLDPModel_floorPkComplementErrorProb_pos_of_lt_one
          successProb hprob0 hprob1 sampleRate q.1 q.2 k
          (hprob_lt_one_on q.1 hq1_Icc)
          (hprob_lt_one_on q.2 hq2_Icc)
    exact ⟨ne_of_gt (mul_pos (hUsub hq.2) hkpos), hq.1⟩
  have hpos :
      0 < ∫ q in cell, weight q * kernel q ∂(μ.prod μ) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hprod_nonneg hprod_int).2
      hsupport_pos
  simpa [kernel, kernelFam, M] using hpos

/--
Source `W^k` zero-rate bridge over an arbitrary witness cell.  Once the
paper-specific non-piecewise argument supplies a near-diagonal cell where the
source error kernel agrees with the raw floor-complement kernel, this theorem
turns that witness into the reverse Lemma C.4 zero-rate conclusion for the
source global error sequence.
-/
theorem lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 B : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hBpos : 0 < B)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ))
    (hlocal_pos :
      ∀ᶠ k : ℕ in atTop,
        0 <
          ∫ q in cell,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hsource_upper_const : ∀ᶠ k : ℕ in atTop, sourceWError k ≤ B) :
    HasExponentialRate sourceWError 0 := by
  let rawKernel : ℕ → ℝ × ℝ → ℝ := fun k q =>
    twoSampleFloorPkComplementErrorProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  let localError : ℕ → ℝ := fun k =>
    ∫ q in cell,
      weight q *
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
      ∂(μ.prod μ)
  have hlocal_zero : HasExponentialRate localError 0 := by
    simpa [localError] using
      lemmaC4_witnessCell_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box
        μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight hcell_meas hcell_subset_closed_upper hθ0_Icc
        hθ0_closure hweight_int hweight_nonneg hweight_cont
        hweight_x0_pos hβ_cont hsample_pos_on hprob_pos_on
        hprob_lt_one_on hsample_cont_on
  have hlocal_le_source :
      ∀ᶠ k : ℕ in atTop, localError k ≤ sourceWError k := by
    simpa [localError, rawKernel] using
      lemmaC4_sourceWError_eventually_raw_local_le_of_eq_on_witness_cell
        μ weight rawKernel sourceKernel sourceWError hcell_meas
        hcell_subset_strict hsource_int hsource_nonneg hsource_eq_raw_on
        hsourceWError_eq
  exact
    hasExponentialRate_zero_of_eventually_le_const_of_zero_rate_minorant
      hBpos (by simpa [localError] using hlocal_pos) hlocal_zero
      hlocal_le_source hsource_upper_const

/--
Source `W^k` zero-rate bridge over an arbitrary witness cell, with local
positivity discharged from the witness-cell weight and the binary
floor-complement kernel. Compared with
`lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness`,
callers no longer need to separately prove that the local raw witness integral
is eventually positive.
-/
theorem lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 B : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hBpos : 0 < B)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ))
    (hsource_upper_const : ∀ᶠ k : ℕ in atTop, sourceWError k ≤ B) :
    HasExponentialRate sourceWError 0 := by
  have hlocal_pos :
      ∀ᶠ k : ℕ in atTop,
        0 <
          ∫ q in cell,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ) := by
    filter_upwards with k
    exact
      lemmaC4_witnessCell_floorPkComplementError_integral_pos_of_weight_pos_closure_interior
        μ successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas
        weight hcell_subset_closed_upper hθ0_closure hweight_int
        hweight_nonneg hweight_cont hweight_x0_pos hprob_lt_one_on k
  exact
    lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel sourceWError hcell_meas
      hcell_subset_closed_upper hcell_subset_strict hθ0_Icc hθ0_closure
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos hβ_cont
      hsample_pos_on hprob_pos_on hprob_lt_one_on hsample_cont_on hBpos
      hsource_int hsource_nonneg hsource_eq_raw_on hsourceWError_eq
      hlocal_pos hsource_upper_const

/--
Source `W^k` zero-rate bridge over an arbitrary witness cell, with both local
positivity and the global source upper bound discharged internally.  The upper
bound follows from the common source convention that `W^k` is an integral of a
nonnegative error kernel bounded by a fixed constant.
-/
theorem lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_sourceKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 K : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ K)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  have hsource_int_restrict :
      ∀ᶠ k : ℕ in atTop,
        Integrable
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) := by
    filter_upwards [hsource_int] with k hk
    simpa [IntegrableOn] using hk
  have hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q := by
    filter_upwards [hsource_kernel_bound] with k hk_bound
    filter_upwards [hsource_weight_nonneg, hk_bound] with q hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hsource_upper_const_restrict⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_eventually_ae_kernel_between_zero_const
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      (weight := weight) (kernel := sourceKernel) (K := K)
      hK_nonneg hsource_weight_int hsource_weight_nonneg
      hsource_int_restrict hsource_kernel_bound
  have hsource_upper_const :
      ∀ᶠ k : ℕ in atTop, sourceWError k ≤ B := by
    filter_upwards [hsourceWError_eq, hsource_upper_const_restrict] with
      k hk_eq hk_upper
    rw [hk_eq]
    simpa using hk_upper
  exact
    lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel sourceWError hcell_meas
      hcell_subset_closed_upper hcell_subset_strict hθ0_Icc hθ0_closure
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos hβ_cont
      hsample_pos_on hprob_pos_on hprob_lt_one_on hsample_cont_on hBpos
      hsource_int hsource_nonneg hsource_eq_raw_on hsourceWError_eq
      hsource_upper_const

/--
Source `W^k` zero-rate bridge over an arbitrary witness cell, deriving both
source product integrability and the global source upper bound from eventual
measurability and a bounded nonnegative source kernel.
-/
theorem lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 K : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourceKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ K)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  have hsource_int_restrict :
      ∀ᶠ k : ℕ in atTop,
        Integrable
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) :=
    eventually_integrable_weight_mul_kernel_of_integrable_weight_of_eventually_ae_kernel_between_zero_const
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      (weight := weight) (kernel := sourceKernel) (K := K)
      hsource_weight_int hsource_kernel_meas hsource_kernel_bound
  have hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ) := by
    filter_upwards [hsource_int_restrict] with k hk
    simpa [IntegrableOn] using hk
  exact
    lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_sourceKernel
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel sourceWError hcell_meas
      hcell_subset_closed_upper hcell_subset_strict hθ0_Icc hθ0_closure
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hβ_cont hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
      hsource_int hsource_kernel_bound hsource_eq_raw_on hsourceWError_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` reverse bridge over an arbitrary non-tie
witness cell.  This is the cell-local source convention used by the paper:
the global `Pbar_k` kernel may be tie-erased, but on the supplied witness cell
it agrees with the raw Bernoulli floor-complement kernel.  The witness cell's
near-diagonal closure supplies the zero-rate obstruction for `Wbar_k`.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_witnessCell_nonTie
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 K : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsource_eq_raw_on_nonTie_cell :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourcePbarKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 :=
  lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
    μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight sourcePbarKernel sourceWbar hcell_meas
    hcell_subset_closed_upper hcell_subset_strict hθ0_Icc hθ0_closure
    hweight_int hweight_nonneg hweight_cont hweight_x0_pos
    hsource_weight_int hsource_weight_nonneg hβ_cont hsample_pos_on
    hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
    hsource_kernel_meas hsource_kernel_bound hsource_eq_raw_on_nonTie_cell
    hsourceWbar_eq

/--
Lemma C.4 witness-cell source-error bridge for the concrete raw `1 - P_k`
kernel.  This specializes
`lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel`
to the source convention where the global `W^k` error is the strict
ordered-pair integral of the raw floor-complement comparison error.  The
binary-rating LDP library supplies measurability and the uniform `0 <= kernel
<= 2` bound, so callers no longer need a separate source-kernel equality
premise on the witness cell.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {cell : Set (ℝ × ℝ)} {a b θ0 : ℝ}
    (hcell_meas : MeasurableSet cell)
    (hcell_subset_closed_upper : cell ⊆ AppliedModelingLib.closedUpperPairSetOn a b)
    (hcell_subset_strict : cell ⊆ AppliedModelingLib.strictUpperPairSet)
    (hθ0_Icc : θ0 ∈ Set.Icc a b)
    (hθ0_closure : (θ0, θ0) ∈ closure (interior cell))
    (hweight_int : Integrable weight ((μ.prod μ).restrict cell))
    (hweight_nonneg : ∀ᵐ q ∂(μ.prod μ).restrict cell, 0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hβ_cont : ContinuousAt successProb θ0)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  let sourceKernel : ℕ → ℝ × ℝ → ℝ := fun k q =>
    twoSampleFloorPkComplementErrorProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  have hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourceKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) := by
    filter_upwards with k
    simpa [sourceKernel, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ (2 : ℝ) := by
    filter_upwards with k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k⟩
  have hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ cell →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k := by
    filter_upwards with k q hq
    rfl
  exact
    lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel sourceWError hcell_meas
      hcell_subset_closed_upper hcell_subset_strict hθ0_Icc hθ0_closure
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hβ_cont hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on (by norm_num)
      hsource_kernel_meas hsource_kernel_bound hsource_eq_raw_on
      (by
        filter_upwards [hsourceWError_eq] with k hk
        simpa [sourceKernel] using hk)

/--
Lemma C.4 global source-integral bridge from the local monotone-interval
obstruction.  This version derives the minorant relation from the paper-shaped
kernel convention: on the chosen non-piecewise witness region, the source
global `W^k` error kernel agrees with the raw floor-complement kernel used by
the local large-deviation theorem.

The remaining visible obligations are exactly the source-level ones: the
witness region gives an eventually positive obstruction, the source global
error is uniformly bounded, and the source kernel is nonnegative/integrable on
the global ordered-pair domain.
-/
theorem lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hlocal_pos :
      ∀ᶠ k : ℕ in atTop,
        0 <
          ∫ q,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k
            ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
    (hsource_upper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ)) ≤ B) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ))
      0 := by
  let rawKernel : ℕ → ℝ × ℝ → ℝ := fun k q =>
    twoSampleFloorPkComplementErrorProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  let localError : ℕ → ℝ := fun k =>
    ∫ q,
      weight q *
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k
      ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)
  have hlocal_le_global :
      ∀ᶠ k : ℕ in atTop,
        (∫ q,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k
            ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) ≤
          (∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) := by
    filter_upwards [hsource_int, hsource_nonneg, hsource_eq_raw_on] with
      k hk_int hk_nonneg hk_eq
    simpa [rawKernel] using
      lemmaC4_strictUpperPairSetOn_raw_integral_le_source_strictUpperPair_integral_of_eq_on_witness
        μ weight rawKernel sourceKernel (a := a) (b := b) k
        hk_int hk_nonneg hk_eq
  have hlocal_zero : HasExponentialRate localError 0 := by
    simpa [localError] using
      lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc
        μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight hweight_int hweight_nonneg hweight_cont
        hweight_x0_pos hab hsample_pos_on hprob_pos_on hprob_lt_one_on
        hsample_cont_on
  exact
    hasExponentialRate_zero_of_eventually_le_const_of_zero_rate_minorant
      hBpos (by simpa [localError] using hlocal_pos) hlocal_zero
      (by simpa [localError] using hlocal_le_global) hsource_upper_const

/--
Lemma C.4 global source-integral bridge from the local monotone-interval
obstruction, with the local raw witness positivity discharged internally.
The remaining visible obligations are source-level: the source kernel agrees
with the raw floor-complement kernel on the monotone witness interval, is
nonnegative/integrable globally, and the resulting source global error is
eventually bounded.
-/
theorem lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsource_upper_const :
      ∀ᶠ k : ℕ in atTop,
        (∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ)) ≤ B) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    exact ⟨hprob_pos_on θ hθ_Icc, hprob_lt_one_on θ hθ_Icc⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  have hθ0_Icc : θ0 ∈ Set.Icc a b := ⟨hθ0.1.le, hθ0.2.le⟩
  have hcell_meas :
      MeasurableSet (AppliedModelingLib.strictUpperPairSetOn a b) := by
    have hbox_closed : IsClosed (AppliedModelingLib.closedPairBox a b) :=
      (AppliedModelingLib.isCompact_closedPairBox a b).isClosed
    simpa [AppliedModelingLib.strictUpperPairSetOn] using
      AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet.inter
        hbox_closed.measurableSet
  exact
    lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel
      (fun k : ℕ =>
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ))
      hcell_meas
      (AppliedModelingLib.strictUpperPairSetOn_subset_closedUpperPairSetOn a b)
      (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)
      hθ0_Icc
      (AppliedModelingLib.diagonal_mem_closure_interior_strictUpperPairSetOn hθ0)
      hweight_int hweight_nonneg (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hBpos
      hsource_int hsource_nonneg hsource_eq_raw_on
      (by filter_upwards with k; rfl)
      hsource_upper_const

/--
Lemma C.4 monotone-interval source bridge with the source upper bound derived
from a uniformly bounded nonnegative source kernel.  This is the usual
paper-shaped form for `W^k`: after the source identifies the global error as
an integral of a nonnegative bounded error kernel, the reusable large-deviation
library supplies the eventual constant upper bound needed by the minorant
argument.
-/
theorem lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_sourceKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ K)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ))
      0 := by
  have hsource_int_restrict :
      ∀ᶠ k : ℕ in atTop,
        Integrable
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) := by
    filter_upwards [hsource_int] with k hk
    simpa [IntegrableOn] using hk
  have hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourceKernel k q := by
    filter_upwards [hsource_kernel_bound] with k hk_bound
    filter_upwards [hsource_weight_nonneg, hk_bound] with q hw hk
    exact mul_nonneg hw hk.1
  obtain ⟨B, hBpos, hsource_upper_const_restrict⟩ :=
    exists_pos_const_eventually_integral_weightedKernel_le_of_eventually_ae_kernel_between_zero_const
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      (weight := weight) (kernel := sourceKernel) (K := K)
      hK_nonneg hsource_weight_int hsource_weight_nonneg
      hsource_int_restrict hsource_kernel_bound
  exact
    lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel (a := a) (b := b) (B := B)
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos hab
      hsample_pos_on hprob_pos_on hprob_lt_one_on hsample_cont_on
      hBpos hsource_int hsource_nonneg hsource_eq_raw_on
      (by simpa using hsource_upper_const_restrict)

/--
Lemma C.4 monotone-interval source bridge deriving source product
integrability and the eventual global upper bound from eventual measurability
and a bounded nonnegative source kernel.
-/
theorem lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourceKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ K)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourceKernel k q ∂(μ.prod μ))
      0 := by
  have hsource_int_restrict :
      ∀ᶠ k : ℕ in atTop,
        Integrable
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) :=
    eventually_integrable_weight_mul_kernel_of_integrable_weight_of_eventually_ae_kernel_between_zero_const
      ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
      (weight := weight) (kernel := sourceKernel) (K := K)
      hsource_weight_int hsource_kernel_meas hsource_kernel_bound
  have hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourceKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ) := by
    filter_upwards [hsource_int_restrict] with k hk
    simpa [IntegrableOn] using hk
  exact
    lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_sourceKernel
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel (a := a) (b := b) (K := K)
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
      hsource_int hsource_kernel_bound hsource_eq_raw_on

/--
Lemma C.4 monotone-interval source-error bridge deriving source product
integrability and the global upper bound from a measurable bounded
nonnegative source kernel.  This is the `sourceWError`-valued form of
`lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel`:
after the source identifies `W^k` with the global strict-pair integral, the
same zero-rate conclusion transfers by eventual equality.
-/
theorem lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourceKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ K)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourceKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  let integralError : ℕ → ℝ := fun k =>
    ∫ q in AppliedModelingLib.strictUpperPairSet,
      weight q * sourceKernel k q ∂(μ.prod μ)
  have hintegral :
      HasExponentialRate integralError 0 := by
    simpa [integralError] using
      lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
        μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight sourceKernel (a := a) (b := b) (K := K)
        hweight_int hweight_nonneg hweight_cont hweight_x0_pos
        hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
        hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
        hsource_kernel_meas hsource_kernel_bound hsource_eq_raw_on
  have heq : integralError =ᶠ[atTop] sourceWError := by
    filter_upwards [hsourceWError_eq] with k hk
    exact hk.symm
  exact HasExponentialRate.congr heq hintegral

/--
Lemma C.4 tie-erased source-`Wbar_k` reverse bridge.  The paper's source
convention may set the pairwise complement kernel to zero on rating ties; the
reverse argument only needs a non-tie witness interval where the source kernel
agrees with the raw Bernoulli floor-complement kernel.  A bounded nonnegative
source kernel and the displayed `Wbar_k` integral identity then give exact
zero exponential rate for `Wbar_k`.
-/
theorem lemmaC4_tieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsource_eq_raw_on_nonTie_witness :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourcePbarKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ)) :
    HasExponentialRate sourceWbar 0 :=
  lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
    μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight sourcePbarKernel sourceWbar (a := a) (b := b)
    (K := K) hweight_int hweight_nonneg hweight_cont hweight_x0_pos
    hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
    hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
    hsource_kernel_meas hsource_kernel_bound
    hsource_eq_raw_on_nonTie_witness hsourceWbar_eq

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff.  The forward direction
is supplied by the piecewise-constant construction; the reverse direction uses
a non-tie interval witness on which the tie-erased source kernel agrees with
the raw Bernoulli floor-complement kernel.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ)
    {K : ℝ}
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          Integrable weight
            ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) ∧
          (∀ᵐ q ∂(μ.prod μ).restrict
              (AppliedModelingLib.strictUpperPairSetOn a b),
            0 ≤ weight q) ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) ∧
          (∀ᶠ k : ℕ in atTop,
            ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
              sourcePbarKernel k q =
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1) sampleRate
                  q.1 q.2 k)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWbar hforward ?_
  intro hnot_piecewise
  rcases hnonpiecewise_witness hnot_piecewise with
    ⟨a, b, hab, hweight_int, hweight_nonneg, hweight_cont,
      hweight_x0_pos, hsample_pos_on, hprob_pos_on, hprob_lt_one_on,
      hsample_cont_on, hsource_eq_raw_on_nonTie_witness⟩
  exact
    lemmaC4_tieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourcePbarKernel sourceWbar (a := a) (b := b)
      (K := K) hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
      hsource_kernel_meas hsource_kernel_bound
      hsource_eq_raw_on_nonTie_witness hsourceWbar_eq

/--
Lemma C.4 source-error bridge for the concrete raw `1 - P_k` kernel.  This
specializes
`lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel`
to the source convention where the global `W^k` error is the strict ordered-pair
integral of the raw floor-complement comparison error.  Measurability and the
uniform `0 ≤ kernel ≤ 2` bound are discharged from the binary-rating LDP
library, so the only remaining source-level premise is the displayed
definition of `W^k` as that integral.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  let sourceKernel : ℕ → ℝ × ℝ → ℝ := fun k q =>
    twoSampleFloorPkComplementErrorProb
      (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  have hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourceKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet) := by
    filter_upwards with k
    simpa [sourceKernel, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourceKernel k q ∧ sourceKernel k q ≤ (2 : ℝ) := by
    filter_upwards with k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k⟩
  have hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourceKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k := by
    filter_upwards with k q hq
    rfl
  exact
    lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceKernel sourceWError (a := a) (b := b)
      (K := (2 : ℝ)) hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hsource_weight_int hsource_weight_nonneg hab
      hsample_pos_on hprob_pos_on hprob_lt_one_on hsample_cont_on
      (by norm_num) hsource_kernel_meas hsource_kernel_bound
      hsource_eq_raw_on
      (by
        filter_upwards [hsourceWError_eq] with k hk
        simpa [sourceKernel] using hk)

/--
Lemma C.4 raw-source bridge with local weight side conditions derived from the
global strict ordered-pair source assumptions.  Since
`strictUpperPairSetOn a b` is a subset of the global strict ordered-pair
domain, global integrability and a.e. nonnegativity of the paper weight
restrict to the monotone witness interval automatically.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_global_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    {a b : ℝ}
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ)) :
    HasExponentialRate sourceWError 0 := by
  have hweight_int_local :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) :=
    hsource_weight_int.mono_measure
      (Measure.restrict_mono
        (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)
        le_rfl)
  have hweight_nonneg_local :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q :=
    ae_restrict_of_ae_restrict_of_subset
      (AppliedModelingLib.strictUpperPairSetOn_subset_strictUpperPairSet a b)
      hsource_weight_nonneg
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_weight_pos
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceWError hweight_int_local
      hweight_nonneg_local hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hsourceWError_eq

/--
Lemma C.4 source-facing reverse bridge isolating the non-piecewise witness
interval.  Once the source's `¬ piecewise constant` branch supplies a bounded
monotone interval with positive diagonal weight and interior Bernoulli/sample
regularity, the raw global `W^k` error has exact exponential rate zero.  The
local weight integrability and nonnegativity are inherited from the global
strict ordered-pair source assumptions.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_piecewise : ¬ isPiecewiseConstant)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)) :
    HasExponentialRate sourceWError 0 := by
  rcases hnonpiecewise_witness hnot_piecewise with
    ⟨a, b, hab, hweight_cont, hweight_x0_pos, hsample_pos_on,
      hprob_pos_on, hprob_lt_one_on, hsample_cont_on⟩
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_global_weight_pos
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourceWError hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hsourceWError_eq

/--
Source-shrink bridge for Lemma C.4's non-piecewise branch.  If the source
non-piecewise branch supplies one point around which the paper weight, sample
rate, and Bernoulli probabilities are locally regular, then a bounded closed
interval witness follows by shrinking to a closed neighborhood of that point.
-/
theorem lemmaC4_nonpiecewise_monotone_interval_witness_of_eventually_regular_continuity_point
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (hlocal :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          ∀ᶠ θ in 𝓝 θ0,
            ContinuousAt weight (θ, θ) ∧
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1 ∧
            ContinuousAt sampleRate θ) :
    ¬ isPiecewiseConstant →
      ∃ a b : ℝ,
        a < b ∧
        (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
        (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
        (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
        (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
        (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
        (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) := by
  intro hnot_piecewise
  rcases hlocal hnot_piecewise with ⟨θ0, hθ0⟩
  rcases AppliedModelingLib.exists_Icc_subset_eventually_nhds hθ0 with
    ⟨a, b, hab, _hθ0_mem, hgood⟩
  refine ⟨a, b, hab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact (hgood θ ⟨hθ.1.le, hθ.2.le⟩).1
  · intro θ hθ
    exact (hgood θ ⟨hθ.1.le, hθ.2.le⟩).2.1
  · intro θ hθ
    exact (hgood θ hθ).2.2.1
  · intro θ hθ
    exact (hgood θ hθ).2.2.2.1
  · intro θ hθ
    exact (hgood θ hθ).2.2.2.2.1
  · intro θ hθ
    exact (hgood θ hθ).2.2.2.2.2

/--
Source-shrink bridge for Lemma C.4 from a single regular continuity point.
This is closer to the paper's prose than an already-eventual local-regularity
assumption: global continuity of the sample-rate and diagonal weight functions,
together with one point where the weight, sample rate, and Bernoulli probability
are interior, supplies the eventual local witness used by the reverse branch.
-/
theorem lemmaC4_nonpiecewise_local_regularity_witness_of_continuity_point
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          0 < weight (θ0, θ0) ∧
          0 < sampleRate θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0) :
    ¬ isPiecewiseConstant →
      ∃ θ0 : ℝ,
        ∀ᶠ θ in 𝓝 θ0,
          ContinuousAt weight (θ, θ) ∧
          0 < weight (θ, θ) ∧
          0 < sampleRate θ ∧
          0 < successProb θ ∧
          successProb θ < 1 ∧
          ContinuousAt sampleRate θ := by
  intro hnot_piecewise
  rcases hpoint hnot_piecewise with
    ⟨θ0, hweight_pos, hsample_pos, hprob_pos, hprob_lt_one, hprob_cont⟩
  refine ⟨θ0, ?_⟩
  have hweight_pos_eventually :
      ∀ᶠ θ in 𝓝 θ0, 0 < weight (θ, θ) :=
    (hweight_diag_cont θ0).eventually (Ioi_mem_nhds hweight_pos)
  have hsample_pos_eventually :
      ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont θ0).eventually (Ioi_mem_nhds hsample_pos)
  have hprob_pos_eventually :
      ∀ᶠ θ in 𝓝 θ0, 0 < successProb θ :=
    hprob_cont.eventually (Ioi_mem_nhds hprob_pos)
  have hprob_lt_one_eventually :
      ∀ᶠ θ in 𝓝 θ0, successProb θ < 1 :=
    hprob_cont.eventually (Iio_mem_nhds hprob_lt_one)
  filter_upwards
    [hweight_pos_eventually, hsample_pos_eventually,
      hprob_pos_eventually, hprob_lt_one_eventually] with
    θ hweight_posθ hsample_posθ hprob_posθ hprob_lt_oneθ
  exact
    ⟨hweight_cont θ, hweight_posθ, hsample_posθ, hprob_posθ,
      hprob_lt_oneθ, hsample_cont θ⟩

/--
Monotone-continuity selector for Lemma C.4's reverse branch.  If the
non-piecewise source branch supplies a nonempty interval on which the diagonal
weight, sample rate, and Bernoulli probability are positive and the Bernoulli
probability is interior, monotonicity of `β` chooses a continuity point inside
that interval.
-/
theorem lemmaC4_nonpiecewise_continuity_point_witness_of_monotone_positive_interval
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hinterval :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1) :
    ¬ isPiecewiseConstant →
      ∃ θ0 : ℝ,
        0 < weight (θ0, θ0) ∧
        0 < sampleRate θ0 ∧
        0 < successProb θ0 ∧
        successProb θ0 < 1 ∧
        ContinuousAt successProb θ0 := by
  intro hnot_piecewise
  rcases hinterval hnot_piecewise with ⟨a, b, hab, hpos⟩
  rcases
      AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
        (f := successProb) hab hprob_mono
        (fun θ hθ => ⟨(hpos θ hθ).2.2.1, (hpos θ hθ).2.2.2⟩) with
    ⟨θ0, hθ0, hprob_cont, hprob_pos, hprob_lt_one⟩
  exact
    ⟨θ0, (hpos θ0 hθ0).1, (hpos θ0 hθ0).2.1, hprob_pos,
      hprob_lt_one, hprob_cont⟩

/--
Source-model bridge for Lemma C.4's non-piecewise branch.  If a concrete
source model turns non-stepwiseness on a quality interval into a subinterval
where the Bernoulli probability is interior, and the model primitives are
positive on the whole quality interval, then it supplies the positive interval
witness consumed by the C.4 reverse-rate wrapper.
-/
theorem lemmaC4_nonpiecewise_monotone_positive_interval_witness_of_not_stepwiseOn
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ)
    (hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    ¬ isStepwiseConstantOn successProb lo hi →
      ∃ a b : ℝ,
        a < b ∧
        ∀ θ ∈ Set.Ioo a b,
          0 < weight (θ, θ) ∧
          0 < sampleRate θ ∧
          0 < successProb θ ∧
          successProb θ < 1 := by
  intro hnot_step
  rcases hnot_step_to_prob_interval hnot_step with
    ⟨a, b, hloa, hab, hbhi, hprob_interval⟩
  refine ⟨a, b, hab, ?_⟩
  intro θ hθ
  have hθ_support : θ ∈ Set.Ioo lo hi :=
    ⟨lt_of_le_of_lt hloa hθ.1, lt_of_lt_of_le hθ.2 hbhi⟩
  exact
    ⟨hweight_pos_on θ hθ_support, hsample_pos_on θ hθ_support,
      (hprob_interval θ hθ).1, (hprob_interval θ hθ).2⟩

/--
Source-model continuity-point bridge for Lemma C.4.  Since
`isStepwiseConstantOn` is a caller-supplied predicate, the semantic content of
non-stepwiseness is the explicit interval bridge: once non-stepwiseness gives
an interior probability interval, monotonicity supplies a continuity point in
that interval.
-/
theorem lemmaC4_nonstepwise_interior_continuity_point_witness_of_monotone_prob_interval
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1) :
    ¬ isStepwiseConstantOn successProb lo hi →
      ∃ θ0 : ℝ,
        θ0 ∈ Set.Ioo lo hi ∧
        0 < successProb θ0 ∧
        successProb θ0 < 1 ∧
        ContinuousAt successProb θ0 := by
  intro hnot_step
  rcases hnot_step_to_prob_interval hnot_step with
    ⟨a, b, hloa, hab, hbhi, hprob_interval⟩
  rcases
      AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
        (f := successProb) hab hprob_mono hprob_interval with
    ⟨θ0, hθ0, hcont, hprob_pos, hprob_lt_one⟩
  exact
    ⟨θ0, ⟨lt_of_le_of_lt hloa hθ0.1, lt_of_lt_of_le hθ0.2 hbhi⟩,
      hprob_pos, hprob_lt_one, hcont⟩

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff from the paper's
monotone probability-interval source convention.  Once non-stepwiseness gives
an interval on which the Bernoulli probability is strictly interior,
monotonicity supplies the continuity point used by the tie-erased zero-rate
obstruction.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_prob_interval_of_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate :=
  lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_interior_continuity_point_of_measurableKernel
    μ isStepwiseConstantOn successProb sampleRate weight sourcePbarKernel
    sourceWbar hK_nonneg hsource_weight_int hsource_weight_nonneg
    hsource_kernel_meas hsource_kernel_bound hcert hsourceWbar_eq hforward
    hweight_cont hsample_cont
    (lemmaC4_nonstepwise_interior_continuity_point_witness_of_monotone_prob_interval
      hlohi isStepwiseConstantOn successProb hprob_mono
      hnot_step_to_prob_interval)
    hweight_pos_on hsample_pos_on

/--
Concrete C.4 source-semantics bridge from monotone variation.  If the
non-stepwise branch supplies two ordered quality points whose Bernoulli
probabilities are strictly inside the endpoint bounds, monotonicity turns them
into the interior probability interval required by the C.4 reverse wrapper.
-/
theorem lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hnot_step_to_two_values :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          0 < successProb x ∧
          successProb y < 1) :
    ¬ isStepwiseConstantOn successProb lo hi →
      ∃ a b : ℝ,
        lo ≤ a ∧ a < b ∧ b ≤ hi ∧
        ∀ θ ∈ Set.Ioo a b,
          0 < successProb θ ∧ successProb θ < 1 := by
  intro hnot_step
  rcases hnot_step_to_two_values hnot_step with
    ⟨x, y, hx, hy, hxy, hx_pos, hy_lt_one⟩
  exact
    AppliedModelingLib.exists_Ioo_subset_preimage_Ioo_of_monotone_two_points
      hprob_mono hx hy hxy hx_pos hy_lt_one

/--
Source-semantics helper for Lemma C.4.  If non-stepwiseness gives two ordered
interior points where the Bernoulli probability changes, and the whole
interval is already supported inside `(0,1)`, then the reverse C.4 wrappers get
the two interior values they need.
-/
theorem lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
    {lo hi : ℝ}
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb : ℝ → ℝ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_step_to_variation :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          successProb x < successProb y) :
    ¬ isStepwiseConstantOn successProb lo hi →
      ∃ x y : ℝ,
        x ∈ Set.Ioo lo hi ∧
        y ∈ Set.Ioo lo hi ∧
        x < y ∧
        0 < successProb x ∧
        successProb y < 1 := by
  intro hnot_step
  rcases hnot_step_to_variation hnot_step with
    ⟨x, y, hx, hy, hxy, _hxy_prob⟩
  exact ⟨x, y, hx, hy, hxy, (hprob_interior_on x hx).1,
    (hprob_interior_on y hy).2⟩

/--
Source-semantics helper for Lemma C.4.  For any concrete stepwise predicate
under which constant interval rules count as stepwise, a non-stepwise monotone
rule must have two ordered interior points with a strict Bernoulli increase.
-/
theorem lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
    {lo hi : ℝ}
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hconstant_step :
      (∀ x : ℝ, x ∈ Set.Ioo lo hi →
        ∀ y : ℝ, y ∈ Set.Ioo lo hi →
          successProb x = successProb y) →
        isStepwiseConstantOn successProb lo hi) :
    ¬ isStepwiseConstantOn successProb lo hi →
      ∃ x y : ℝ,
        x ∈ Set.Ioo lo hi ∧
        y ∈ Set.Ioo lo hi ∧
        x < y ∧
        successProb x < successProb y := by
  intro hnot_step
  exact
    AppliedModelingLib.exists_ordered_strict_value_of_monotone_not_constant_on_Ioo
      hprob_mono
      (by
        intro hconst
        exact hnot_step (hconstant_step hconst))

/--
Lemma C.4 local strict-variation witness.  If the monotone Bernoulli rule is
not constant on any neighborhood of `θ0`, then every positive-radius
neighborhood of `θ0` contains ordered qualities whose success probabilities
strictly increase.
-/
theorem lemmaC4_ordered_strict_prob_values_near_of_monotone_not_locally_constant
    (successProb : ℝ → ℝ) (hprob_mono : Monotone successProb)
    {θ0 ε : ℝ} (hε : 0 < ε)
    (hnot_const_nhds :
      ∀ a b : ℝ, a < θ0 → θ0 < b →
        ¬ ∀ x : ℝ, x ∈ Set.Ioo a b →
          ∀ y : ℝ, y ∈ Set.Ioo a b →
            successProb x = successProb y) :
    ∃ x y : ℝ,
      x ∈ Set.Ioo (θ0 - ε) (θ0 + ε) ∧
        y ∈ Set.Ioo (θ0 - ε) (θ0 + ε) ∧
          x < y ∧ successProb x < successProb y :=
  AppliedModelingLib.exists_ordered_strict_value_near_of_monotone_not_constant_on_nhds
    hprob_mono hε hnot_const_nhds

/--
Lemma C.4 source-facing reverse bridge with the non-piecewise witness interval
derived from a local regularity point.  This is closer to the source prose
than the raw interval-witness interface: the remaining obligation is to locate
one regular diagonal point in the non-piecewise monotone branch.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_local_regularity_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_piecewise : ¬ isPiecewiseConstant)
    (hlocal :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          ∀ᶠ θ in 𝓝 θ0,
            ContinuousAt weight (θ, θ) ∧
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1 ∧
            ContinuousAt sampleRate θ) :
    HasExponentialRate sourceWError 0 :=
  lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight sourceWError hsource_weight_int
    hsource_weight_nonneg hsourceWError_eq hnot_piecewise
    (lemmaC4_nonpiecewise_monotone_interval_witness_of_eventually_regular_continuity_point
      isPiecewiseConstant successProb sampleRate weight hlocal)

/--
Lemma C.4 source-facing reverse bridge with the non-piecewise local-regularity
witness derived from one regular continuity point.  The remaining source-model
obligation is now the paper's prose-level claim that a non-piecewise monotone
rating rule has such a regular point.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_continuity_point_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_piecewise : ¬ isPiecewiseConstant)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          0 < weight (θ0, θ0) ∧
          0 < sampleRate θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0) :
    HasExponentialRate sourceWError 0 :=
  lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_local_regularity_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight sourceWError hsource_weight_int
    hsource_weight_nonneg hsourceWError_eq hnot_piecewise
    (lemmaC4_nonpiecewise_local_regularity_witness_of_continuity_point
      isPiecewiseConstant successProb sampleRate weight hweight_cont
      hweight_diag_cont hsample_cont hpoint)

/--
Lemma C.4 source-facing reverse bridge with the non-piecewise continuity point
derived from a positive monotone interval.  This leaves the source-model
obligation as the interval-existence claim coming from `β` not being piecewise
constant.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_positive_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_piecewise : ¬ isPiecewiseConstant)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hinterval :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1) :
    HasExponentialRate sourceWError 0 :=
  lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_continuity_point_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight sourceWError hsource_weight_int
    hsource_weight_nonneg hsourceWError_eq hnot_piecewise hweight_cont
    hweight_diag_cont hsample_cont
    (lemmaC4_nonpiecewise_continuity_point_witness_of_monotone_positive_interval
      isPiecewiseConstant successProb sampleRate weight hprob_mono hinterval)

/--
Raw source `W^k` complement error for Lemma C.4, written as the strict
ordered-pair integral of the floor-count comparison error.
-/
def lemmaC4RawStrictUpperPairSourceWError
    (μ : Measure ℝ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ) : ℕ → ℝ :=
  fun k : ℕ =>
    ∫ q in AppliedModelingLib.strictUpperPairSet,
      weight q *
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k ∂(μ.prod μ)

theorem lemmaC4RawStrictUpperPairSourceWError_eventually_eq
    (μ : Measure ℝ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ) :
    ∀ᶠ k : ℕ in atTop,
      lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
          hprob0 hprob1 weight k =
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂(μ.prod μ) :=
  Filter.Eventually.of_forall (by
    intro k
    rfl)

/--
Lemma C.4 source-facing reverse bridge for the source-defined raw global
`W^k` error.  This removes the bookkeeping premise identifying a separate
`sourceWError` sequence with the strict ordered-pair integral.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_piecewise : ¬ isPiecewiseConstant)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight) 0 :=
  lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hnot_piecewise hnonpiecewise_witness

/--
Lemma C.4 source-facing positive-rate iff for the raw global `W^k` error.
The forward implication is the piecewise-constant positive-rate construction;
the reverse implication is discharged from the source's non-piecewise witness
interval convention and the raw strict ordered-pair integral definition of
`W^k`.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWError hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness
      μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
      hprob_meas hsample_meas weight sourceWError hsource_weight_int
      hsource_weight_nonneg hsourceWError_eq hnot_piecewise
      hnonpiecewise_witness

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error.  This packages the raw strict ordered-pair integral convention
directly, so the caller no longer supplies the definitional equality for
`sourceWError`.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hforward hnonpiecewise_witness

/--
Lemma C.4 source-facing positive-rate iff with the non-piecewise reverse
branch derived from a local regularity point rather than a prepackaged
interval witness.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_local_regularity_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hlocal :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          ∀ᶠ θ in 𝓝 θ0,
            ContinuousAt weight (θ, θ) ∧
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1 ∧
            ContinuousAt sampleRate θ) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWError hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_local_regularity_witness
      μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
      hprob_meas hsample_meas weight sourceWError hsource_weight_int
      hsource_weight_nonneg hsourceWError_eq hnot_piecewise hlocal

/--
Lemma C.4 source-facing positive-rate iff with the non-piecewise reverse
branch derived from one regular continuity point.  This keeps the remaining
non-piecewise source obligation at the level stated in the paper: find a
continuity point with positive local primitives.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_continuity_point_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          0 < weight (θ0, θ0) ∧
          0 < sampleRate θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWError hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_continuity_point_witness
      μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
      hprob_meas hsample_meas weight sourceWError hsource_weight_int
      hsource_weight_nonneg hsourceWError_eq hnot_piecewise hweight_cont
      hweight_diag_cont hsample_cont hpoint

/--
Lemma C.4 source-facing positive-rate iff with the non-piecewise reverse
branch reduced to a positive monotone interval.  The monotone-continuity
library chooses the continuity point needed by the zero-rate obstruction.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_monotone_positive_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hinterval :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant sourceWError hforward ?_
  intro hnot_piecewise
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_positive_interval_witness
      μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
      hprob_meas hsample_meas weight sourceWError hsource_weight_int
      hsource_weight_nonneg hsourceWError_eq hnot_piecewise hweight_cont
      hweight_diag_cont hsample_cont hinterval

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-piecewise reverse branch derived from a local
regularity point.  This removes the separate bookkeeping premise identifying a
caller-supplied error sequence with the raw strict ordered-pair integral.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_local_regularity_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hlocal :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          ∀ᶠ θ in 𝓝 θ0,
            ContinuousAt weight (θ, θ) ∧
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1 ∧
            ContinuousAt sampleRate θ) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_local_regularity_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hforward hlocal

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-piecewise reverse branch derived from one regular
continuity point.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_continuity_point_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isPiecewiseConstant →
        ∃ θ0 : ℝ,
          0 < weight (θ0, θ0) ∧
          0 < sampleRate θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_continuity_point_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hforward hweight_cont hweight_diag_cont hsample_cont hpoint

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-piecewise reverse branch reduced to a positive
monotone interval.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_monotone_positive_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hinterval :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < weight (θ, θ) ∧
            0 < sampleRate θ ∧
            0 < successProb θ ∧
            successProb θ < 1) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_monotone_positive_interval_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0 hprob1
    hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hforward hweight_cont hweight_diag_cont hsample_cont hinterval

/--
Lemma C.4 source-facing positive-rate iff with a concrete stepwise-on-interval
convention.  Compared with the raw interval-witness wrapper, this version
accepts the source-model fact that non-stepwiseness yields an interior
probability subinterval, plus positivity of the diagonal weight and sample
rate on the ambient quality interval.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_monotone_positive_interval_witness
      μ (isStepwiseConstantOn successProb lo hi) successProb sampleRate
      hprob_mono hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont
      (lemmaC4_nonpiecewise_monotone_positive_interval_witness_of_not_stepwiseOn
        hlohi isStepwiseConstantOn successProb sampleRate weight
        hnot_step_to_prob_interval hweight_pos_on hsample_pos_on)

/--
Lemma C.4 source-facing positive-rate iff with the non-stepwise reverse branch
stated as two ordered interior Bernoulli values.  Monotonicity fills the whole
probability interval between those values, so this is a direct source-shaped
wrapper around the interval version.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_two_interior_values
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hnot_step_to_two_values :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          0 < successProb x ∧
          successProb y < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont
      (lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
        hlohi isStepwiseConstantOn successProb hprob_mono
        hnot_step_to_two_values)
      hweight_pos_on hsample_pos_on

/--
Lemma C.4 source-facing positive-rate iff with the non-stepwise reverse branch
stated as strict variation on an already-supported interior interval.  This is
often the most natural source-model form: non-stepwiseness gives two interior
points where the Bernoulli rule changes, while support assumptions keep the
probabilities in `(0,1)`.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_variation
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_step_to_variation :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          successProb x < successProb y)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_two_interior_values
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont
      (lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
        isStepwiseConstantOn successProb hprob_interior_on
        hnot_step_to_variation)
      hweight_pos_on hsample_pos_on

/--
Lemma C.4 source-facing positive-rate iff where the non-stepwise reverse
branch uses only the semantic fact that a constant interval rule is stepwise.
For monotone rules, non-stepwiseness then supplies the strict variation needed
by the local zero-rate obstruction.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_constant_semantics
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hconstant_step :
      (∀ x : ℝ, x ∈ Set.Ioo lo hi →
        ∀ y : ℝ, y ∈ Set.Ioo lo hi →
          successProb x = successProb y) →
        isStepwiseConstantOn successProb lo hi)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_variation
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont hprob_interior_on
      (lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
        isStepwiseConstantOn successProb hprob_mono hconstant_step)
      hweight_pos_on hsample_pos_on

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-stepwise reverse branch using only the semantic
fact that a constant interval rule is stepwise.  This removes the bookkeeping
premise identifying a separate `sourceWError` sequence with the raw strict
ordered-pair integral.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonstepwise_constant_semantics
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hconstant_step :
      (∀ x : ℝ, x ∈ Set.Ioo lo hi →
        ∀ y : ℝ, y ∈ Set.Ioo lo hi →
          successProb x = successProb y) →
        isStepwiseConstantOn successProb lo hi)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_constant_semantics
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight)
      hsource_weight_int hsource_weight_nonneg
      (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
        sampleRate hprob0 hprob1 weight)
      hforward hweight_cont hweight_diag_cont hsample_cont
      hprob_interior_on hconstant_step hweight_pos_on hsample_pos_on

/--
Concrete local source convention for the C.4 reverse branch: the Bernoulli
rating rule is constant on the open quality interval under consideration.
Local constancy is a one-level finite-range convention.  This discharges the
semantic premise needed by the C.4 reverse wrappers when the stepwise predicate
is instantiated as finite range on the source interval.
-/
theorem lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo
    (successProb : ℝ → ℝ) {lo hi : ℝ} (hlohi : lo < hi)
    (hconstant : lemmaC4LocallyConstantOnIoo successProb lo hi) :
    lemmaC4FiniteRangeOnIoo successProb lo hi := by
  classical
  let mid : ℝ := (lo + hi) / 2
  have hmid : mid ∈ Set.Ioo lo hi := by
    constructor
    · dsimp [mid]
      linarith [hlohi]
    · dsimp [mid]
      linarith [hlohi]
  refine Set.Finite.subset (Set.finite_singleton (successProb mid)) ?_
  intro value hvalue
  rcases hvalue with ⟨θ, hθ, rfl⟩
  have hθmid := hconstant θ hθ mid hmid
  simpa [hθmid]

/--
Non-finite-range monotone rules have a strict local variation witness on the
same source interval.
-/
theorem lemmaC4_nonfiniteRangeOnIoo_monotone_variation
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ) (hprob_mono : Monotone successProb)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    ∃ x y : ℝ,
      x ∈ Set.Ioo lo hi ∧
      y ∈ Set.Ioo lo hi ∧
      x < y ∧
      successProb x < successProb y := by
  exact
    lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
      (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi)
      successProb hprob_mono
      (by
        intro hconstant
        exact
          lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo
            successProb hlohi hconstant)
      hnot_finite

/--
Non-finite-range monotone rules with interior Bernoulli probabilities supply
the positive probability interval used by the C.4 zero-rate obstruction.
-/
theorem lemmaC4_nonfiniteRangeOnIoo_prob_interval_witness_of_monotone
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ) (hprob_mono : Monotone successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    ∃ a b : ℝ,
      lo ≤ a ∧ a < b ∧ b ≤ hi ∧
      ∀ θ ∈ Set.Ioo a b,
        0 < successProb θ ∧ successProb θ < 1 := by
  have htwo :
      ∃ x y : ℝ,
        x ∈ Set.Ioo lo hi ∧
        y ∈ Set.Ioo lo hi ∧
        x < y ∧
        0 < successProb x ∧
        successProb y < 1 :=
    lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
      (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi)
      successProb hprob_interior_on
      (by
        intro hnot
        exact
          lemmaC4_nonfiniteRangeOnIoo_monotone_variation
            hlohi successProb hprob_mono hnot)
      hnot_finite
  exact
    lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
      hlohi (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi)
      successProb hprob_mono (by intro _; exact htwo) hnot_finite

/--
Source-defined tie-erased `Wbar_k` convention for Lemma C.4: integrate the
paper's pairwise complement kernel over strict ordered pairs.  Naming this
sequence keeps the common source convention out of theorem hypotheses.
-/
def lemmaC4TieErasedSourceWbar
    (μ : Measure ℝ) (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) : ℕ → ℝ :=
  fun k : ℕ =>
    ∫ q in AppliedModelingLib.strictUpperPairSet,
      weight q * sourcePbarKernel k q ∂(μ.prod μ)

/-- The source-defined tie-erased `Wbar_k` is eventually its displayed integral. -/
theorem lemmaC4TieErasedSourceWbar_eventually_eq
    (μ : Measure ℝ) (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) :
    ∀ᶠ k : ℕ in atTop,
      lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel k =
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          weight q * sourcePbarKernel k q ∂(μ.prod μ) := by
  filter_upwards with k
  rfl

/--
Selected-support source kernel used by the finite-level Theorem 3.1/C.4
forward branch.  It is separated from `theorem31SourceWbar` so the C.4
source-realization seam can state pointwise/a.e. kernel agreement instead of
an opaque eventual sequence equality.
-/
def theorem31SelectedSourceKernel
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels) :
    ℕ → ℝ × ℝ → ℝ :=
  fun k : ℕ => fun q : ℝ × ℝ =>
    (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
        (fun component k =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel levels
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels))
            sampleRate component.val.2 component.val.1 k)
        k q

/--
Selected-support source domain used by the finite-level Theorem 3.1/C.4
forward branch.
-/
def theorem31SelectedSourceSupport
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut) :
    Set (ℝ × ℝ) :=
  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
    (theorem31OrderedNontrivialPairSelected (m := m))).support

/--
Coordinate convention used when comparing the source integral in Lemma C.4 to
the finite-level selected-pair integral.  The source strict-pair convention is
`(high, low)`, while the selected finite partition is indexed as `(low, high)`.
-/
def theorem31SelectedSourceCoordinateMap : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodComm

/-- The selected-source coordinate convention preserves the product measure. -/
theorem theorem31SelectedSourceCoordinateMap_measurePreserving
    (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving theorem31SelectedSourceCoordinateMap (μ.prod μ)
      (μ.prod μ) := by
  simpa [theorem31SelectedSourceCoordinateMap] using
    (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- The selected finite-level source support is measurable. -/
theorem theorem31SelectedSourceSupport_measurable
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut) :
    MeasurableSet
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) := by
  simpa [theorem31SelectedSourceSupport] using
    (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))).measurable_support

/--
The selected finite-level support uses the target `(low, high)` convention; its
pullback through the coordinate map lies in the source strict-pair
`(high, low)` convention.
-/
theorem theorem31SelectedSourceCoordinateMap_preimage_selectedSourceSupport_subset_strictUpperPairSet
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut) :
    theorem31SelectedSourceCoordinateMap ⁻¹'
        theorem31SelectedSourceSupport μ (m := m) cut hmono ⊆
      AppliedModelingLib.strictUpperPairSet := by
  intro q hq
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  have hq_support : theorem31SelectedSourceCoordinateMap q ∈ P.support := by
    simpa [P, theorem31SelectedSourceSupport] using hq
  rw [← P.cover] at hq_support
  rcases Set.mem_iUnion.mp hq_support with ⟨piece, hpiece⟩
  have hprod :
      theorem31SelectedSourceCoordinateMap q ∈
        (theorem31_ordered_quality_interval_partition μ (m + 2) cut hmono).pieceSet
            piece.val.1 ×ˢ
          (theorem31_ordered_quality_interval_partition μ (m + 2) cut hmono).pieceSet
            piece.val.2 := by
    simpa [P, theorem31_ordered_quality_pair_partition,
      FiniteMeasurableSetPartition.selectedProduct,
      FiniteMeasurableSetPartition.subpartition,
      FiniteMeasurableSetPartition.prod] using hpiece
  have hlow :
      q.2 ∈ Set.Ioc (cut piece.val.1.val) (cut (piece.val.1.val + 1)) := by
    simpa [theorem31SelectedSourceCoordinateMap,
      theorem31_ordered_quality_interval_partition,
      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints] using
      hprod.1
  have hhigh :
      q.1 ∈ Set.Ioc (cut piece.val.2.val) (cut (piece.val.2.val + 1)) := by
    simpa [theorem31SelectedSourceCoordinateMap,
      theorem31_ordered_quality_interval_partition,
      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints] using
      hprod.2
  have hindex : piece.val.1.val + 1 ≤ piece.val.2.val :=
    piece.property.1
  have hcut_le : cut (piece.val.1.val + 1) ≤ cut piece.val.2.val :=
    hmono hindex
  have hstrict : q.2 < q.1 :=
    lt_of_le_of_lt (le_trans hlow.2 hcut_le) hhigh.1
  simpa [AppliedModelingLib.strictUpperPairSet] using hstrict

/--
Structured C.4 source-realization interface for identifying the paper's
tie-erased strict-pair source integral with the selected finite-level
endpoint/cutpoint integral.  The fields expose the mathematical facts that
must come from the source model: a measure-preserving coordinate convention
maps source ordered pairs to the target finite-partition convention, the
selected target support pulls back inside the strict ordered-pair source
region, and the source integrand agrees a.e. on the strict-pair source region
with the selected-support target integrand composed with that coordinate map,
extended by zero off selected support.  For GJ19's current finite partition,
the target convention is `(low, high)` while `strictUpperPairSet` is
`(high, low)`, so the intended coordinate map is `Prod.swap`.
-/
structure LemmaC4TieErasedSelectedIntegralRealization
    (μ : Measure ℝ)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel targetKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceToTarget : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
    (targetSupport : Set (ℝ × ℝ)) : Prop where
  map_preserving :
    MeasurePreserving sourceToTarget (μ.prod μ) (μ.prod μ)
  target_measurable : MeasurableSet targetSupport
  target_preimage_subset_strict :
    sourceToTarget ⁻¹' targetSupport ⊆ AppliedModelingLib.strictUpperPairSet
  integrand_indicator_ae :
    ∀ k : ℕ,
      ∀ᵐ q ∂(μ.prod μ), q ∈ AppliedModelingLib.strictUpperPairSet →
        sourceWeight q * sourceKernel k q =
          (targetSupport.indicator
            (fun r : ℝ × ℝ => targetWeight r * targetKernel k r))
            (sourceToTarget q)

/--
Pointwise constructor for the C.4 selected-integral realization.  This is the
paper-facing way to discharge the realization fields: provide the
measure-preserving source-to-target coordinate convention, prove selected
finite-level support pulls back inside the strict ordered-pair domain, prove
source and target integrands agree on selected cross-level cells after that
coordinate map, and prove the source integrand is zero on remaining strict
ordered-pair cells.
-/
theorem lemmaC4TieErasedSelectedIntegralRealization_of_pointwise
    (μ : Measure ℝ)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel targetKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceToTarget : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
    (targetSupport : Set (ℝ × ℝ))
    (hmap_preserving :
      MeasurePreserving sourceToTarget (μ.prod μ) (μ.prod μ))
    (htarget_measurable : MeasurableSet targetSupport)
    (htarget_preimage_subset_strict :
      sourceToTarget ⁻¹' targetSupport ⊆ AppliedModelingLib.strictUpperPairSet)
    (hon_target :
      ∀ k q, sourceToTarget q ∈ targetSupport →
        sourceWeight q * sourceKernel k q =
          targetWeight (sourceToTarget q) * targetKernel k (sourceToTarget q))
    (hoff_target :
      ∀ k q, q ∈ AppliedModelingLib.strictUpperPairSet →
        sourceToTarget q ∉ targetSupport →
        sourceWeight q * sourceKernel k q = 0) :
    LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight sourceKernel targetKernel sourceToTarget
      targetSupport := by
  refine
    ⟨hmap_preserving, htarget_measurable, htarget_preimage_subset_strict, ?_⟩
  intro k
  filter_upwards with q hq_strict
  by_cases hq_target : sourceToTarget q ∈ targetSupport
  · simp [Set.indicator, hq_target, hon_target k q hq_target]
  · simp [Set.indicator, hq_target, hoff_target k q hq_strict hq_target]

/--
Theorem 3.1/C.4 selected-source realization constructor with the
finite-partition coordinate and support fields discharged.  For the canonical
selected-source convention, callers only need to prove mapped integrand
agreement on selected cross-level cells and zero contribution off selected
support.
-/
theorem lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_pointwise
    (μ : Measure ℝ) [SFinite μ]
    {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (hon_target :
      ∀ k q,
        theorem31SelectedSourceCoordinateMap q ∈
          theorem31SelectedSourceSupport μ (m := m) cut hmono →
        sourceWeight q * sourceKernel k q =
          targetWeight (theorem31SelectedSourceCoordinateMap q) *
            theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate
              levels hlevels k (theorem31SelectedSourceCoordinateMap q))
    (hoff_target :
      ∀ k q, q ∈ AppliedModelingLib.strictUpperPairSet →
        theorem31SelectedSourceCoordinateMap q ∉
          theorem31SelectedSourceSupport μ (m := m) cut hmono →
        sourceWeight q * sourceKernel k q = 0) :
    LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight sourceKernel
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) :=
  lemmaC4TieErasedSelectedIntegralRealization_of_pointwise
    μ sourceWeight targetWeight sourceKernel
    (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
      hlevels)
    theorem31SelectedSourceCoordinateMap
    (theorem31SelectedSourceSupport μ (m := m) cut hmono)
    (theorem31SelectedSourceCoordinateMap_measurePreserving μ)
    (theorem31SelectedSourceSupport_measurable μ (m := m) cut hmono)
    (theorem31SelectedSourceCoordinateMap_preimage_selectedSourceSupport_subset_strictUpperPairSet
      μ (m := m) cut hmono)
    hon_target hoff_target

/-- Pull back a selected finite-level target weight to the source orientation. -/
def theorem31SelectedPullbackSourceWeight
    (targetWeight : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q : ℝ × ℝ => targetWeight (theorem31SelectedSourceCoordinateMap q)

/--
Pull back the selected finite-level target kernel to the source orientation and
erase pairs outside selected cross-level support.
-/
def theorem31SelectedPullbackSourceKernel
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels) :
    ℕ → ℝ × ℝ → ℝ :=
  fun k q => by
    classical
    exact
    if theorem31SelectedSourceCoordinateMap q ∈
        theorem31SelectedSourceSupport μ (m := m) cut hmono then
      theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels k (theorem31SelectedSourceCoordinateMap q)
    else
      0

/--
The canonical pullback source convention realizes the structured C.4
selected-source interface: the source integrand is exactly the selected target
integrand transported through the coordinate map and erased off selected
support.
-/
theorem lemmaC4TieErasedSelectedIntegralRealization_theorem31_pullback_source
    (μ : Measure ℝ) [SFinite μ]
    {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (targetWeight : ℝ × ℝ → ℝ) :
    LemmaC4TieErasedSelectedIntegralRealization μ
      (theorem31SelectedPullbackSourceWeight targetWeight)
      targetWeight
      (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
        sampleRate levels hlevels)
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) := by
  refine
    lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_pointwise
      μ (m := m) cut hmono sampleRate levels hlevels
      (theorem31SelectedPullbackSourceWeight targetWeight)
      targetWeight
      (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
        sampleRate levels hlevels)
      ?_ ?_
  · intro k q hq
    simp [theorem31SelectedPullbackSourceWeight,
      theorem31SelectedPullbackSourceKernel, hq]
  · intro k q _hq_strict hq
    simp [theorem31SelectedPullbackSourceWeight,
      theorem31SelectedPullbackSourceKernel, hq]

/--
Selected-source realization from pointwise equality with the canonical
pullback convention.  This is a useful source-model audit form: to identify a
caller-supplied strict-pair source model with the selected finite partition,
it suffices to prove that its weight and kernel are the pullbacks of the
selected finite-level weight and kernel.
-/
theorem lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_eq_pullback_source
    (μ : Measure ℝ) [SFinite μ]
    {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (hweight_eq :
      ∀ q : ℝ × ℝ,
        sourceWeight q = theorem31SelectedPullbackSourceWeight targetWeight q)
    (hkernel_eq :
      ∀ k q,
        sourceKernel k q =
          theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
            sampleRate levels hlevels k q) :
    LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight sourceKernel
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) := by
  let H :=
    lemmaC4TieErasedSelectedIntegralRealization_theorem31_pullback_source
      μ (m := m) cut hmono sampleRate levels hlevels targetWeight
  refine
    ⟨H.map_preserving, H.target_measurable,
      H.target_preimage_subset_strict, ?_⟩
  intro k
  filter_upwards [H.integrand_indicator_ae k] with q hq hq_strict
  calc
    sourceWeight q * sourceKernel k q =
        theorem31SelectedPullbackSourceWeight targetWeight q *
          theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
            sampleRate levels hlevels k q := by
          rw [hweight_eq q, hkernel_eq k q]
    _ = (theorem31SelectedSourceSupport μ (m := m) cut hmono).indicator
          (fun r : ℝ × ℝ =>
            targetWeight r *
              theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate
                levels hlevels k r)
          (theorem31SelectedSourceCoordinateMap q) := hq hq_strict

/--
Theorem 3.1/C.4 selected-source realization for the concrete raw
floor-complement source kernel, reduced to pointwise equality with the
canonical selected pullback convention.
-/
theorem lemmaC4TieErasedSelectedIntegralRealization_theorem31_raw_floorPkComplementError_of_eq_pullback_source
    (μ : Measure ℝ) [SFinite μ]
    {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (sourceSuccessProb sourceSampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ sourceSuccessProb θ)
    (hprob1 : ∀ θ, sourceSuccessProb θ ≤ 1)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (hweight_eq :
      ∀ q : ℝ × ℝ,
        sourceWeight q = theorem31SelectedPullbackSourceWeight targetWeight q)
    (hkernel_eq :
      ∀ k q,
        twoSampleFloorPkComplementErrorProb
            (binaryRatingModel sourceSuccessProb hprob0 hprob1)
            sourceSampleRate q.1 q.2 k =
          theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
            sampleRate levels hlevels k q) :
    LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight
      (fun k : ℕ => fun q : ℝ × ℝ =>
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel sourceSuccessProb hprob0 hprob1)
          sourceSampleRate q.1 q.2 k)
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) :=
  lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_eq_pullback_source
    μ (m := m) cut hmono sampleRate levels hlevels sourceWeight targetWeight
    (fun k : ℕ => fun q : ℝ × ℝ =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel sourceSuccessProb hprob0 hprob1)
        sourceSampleRate q.1 q.2 k)
    hweight_eq hkernel_eq

/--
Integral congruence for the structured C.4 selected-source realization.  This
is the non-opaque bridge from selected-support indicator agreement to eventual
equality of the source-defined tie-erased sequence and the selected-support
integral.
-/
theorem lemmaC4TieErasedSourceWbar_eventually_eq_selectedIntegral_of_realization
    (μ : Measure ℝ)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel targetKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceToTarget : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
    (targetSupport : Set (ℝ × ℝ))
    (H : LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight sourceKernel targetKernel sourceToTarget
      targetSupport) :
    lemmaC4TieErasedSourceWbar μ sourceWeight sourceKernel =ᶠ[atTop]
      (fun k : ℕ =>
        ∫ q in targetSupport,
          targetWeight q * targetKernel k q ∂(μ.prod μ)) := by
  filter_upwards with k
  have hstrict :
      (∫ q in AppliedModelingLib.strictUpperPairSet,
        sourceWeight q * sourceKernel k q ∂(μ.prod μ)) =
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          targetSupport.indicator
            (fun r : ℝ × ℝ => targetWeight r * targetKernel k r)
            (sourceToTarget q) ∂(μ.prod μ) := by
    exact
      setIntegral_congr_ae AppliedModelingLib.isOpen_strictUpperPairSet.measurableSet
        (H.integrand_indicator_ae k)
  have hsupport :
      (∫ q in AppliedModelingLib.strictUpperPairSet,
        targetSupport.indicator
          (fun r : ℝ × ℝ => targetWeight r * targetKernel k r)
          (sourceToTarget q) ∂(μ.prod μ)) =
        ∫ q in targetSupport,
          targetWeight q * targetKernel k q ∂(μ.prod μ) := by
    have hpre :
        MeasurableSet (sourceToTarget ⁻¹' targetSupport) :=
      H.target_measurable.preimage sourceToTarget.measurable
    have hcomp :
        (fun q : ℝ × ℝ =>
          (targetSupport.indicator
            (fun r : ℝ × ℝ => targetWeight r * targetKernel k r))
            (sourceToTarget q)) =
        (sourceToTarget ⁻¹' targetSupport).indicator
          (fun q : ℝ × ℝ =>
            targetWeight (sourceToTarget q) *
              targetKernel k (sourceToTarget q)) := by
      funext q
      rw [← Set.indicator_comp_right]
      rfl
    rw [hcomp]
    rw [MeasureTheory.setIntegral_indicator hpre]
    have hset :
        (AppliedModelingLib.strictUpperPairSet ∩ sourceToTarget ⁻¹' targetSupport : Set (ℝ × ℝ))
          = sourceToTarget ⁻¹' targetSupport := by
      ext q
      constructor
      · intro hq
        exact hq.2
      · intro hq
        exact ⟨H.target_preimage_subset_strict hq, hq⟩
    rw [hset]
    exact
      H.map_preserving.setIntegral_preimage_emb
        sourceToTarget.measurableEmbedding
        (fun r : ℝ × ℝ => targetWeight r * targetKernel k r)
        targetSupport
  calc
    lemmaC4TieErasedSourceWbar μ sourceWeight sourceKernel k =
        ∫ q in AppliedModelingLib.strictUpperPairSet,
          sourceWeight q * sourceKernel k q ∂(μ.prod μ) := rfl
    _ = ∫ q in AppliedModelingLib.strictUpperPairSet,
          targetSupport.indicator
            (fun r : ℝ × ℝ => targetWeight r * targetKernel k r)
            (sourceToTarget q) ∂(μ.prod μ) := hstrict
    _ = ∫ q in targetSupport,
          targetWeight q * targetKernel k q ∂(μ.prod μ) := hsupport

/--
Theorem 3.1/C.4 selected-source realization specialized to the finite-level
endpoint/cutpoint `theorem31SourceWbar` convention.
-/
theorem lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (sourceWeight targetWeight : ℝ × ℝ → ℝ)
    (sourceKernel : ℕ → ℝ × ℝ → ℝ)
    (H : LemmaC4TieErasedSelectedIntegralRealization μ
      sourceWeight targetWeight sourceKernel
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono)) :
    lemmaC4TieErasedSourceWbar μ sourceWeight sourceKernel =ᶠ[atTop]
      theorem31SourceWbar μ cut hmono sampleRate levels hlevels targetWeight := by
  have h :=
    lemmaC4TieErasedSourceWbar_eventually_eq_selectedIntegral_of_realization
      μ sourceWeight targetWeight sourceKernel
      (theorem31SelectedSourceKernel μ (m := m) cut hmono sampleRate levels
        hlevels)
      theorem31SelectedSourceCoordinateMap
      (theorem31SelectedSourceSupport μ (m := m) cut hmono) H
  filter_upwards [h] with k hk
  simpa [theorem31SourceWbar, theorem31SelectedSourceKernel,
    theorem31SelectedSourceSupport] using hk

/--
For the canonical pullback source convention, the source-defined tie-erased
sequence is eventually exactly the finite-level `theorem31SourceWbar`
sequence.
-/
theorem lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source
    (μ : Measure ℝ) [SFinite μ]
    {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (targetWeight : ℝ × ℝ → ℝ) :
    lemmaC4TieErasedSourceWbar μ
        (theorem31SelectedPullbackSourceWeight targetWeight)
        (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
          sampleRate levels hlevels)
      =ᶠ[atTop]
        theorem31SourceWbar μ cut hmono sampleRate levels hlevels
          targetWeight :=
  lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization
    μ (m := m) cut hmono sampleRate levels hlevels
    (theorem31SelectedPullbackSourceWeight targetWeight)
    targetWeight
    (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
      sampleRate levels hlevels)
    (lemmaC4TieErasedSelectedIntegralRealization_theorem31_pullback_source
      μ (m := m) cut hmono sampleRate levels hlevels targetWeight)

/--
Lemma C.4 forward branch for the canonical selected pullback source
convention.  The finite-level model derives endpoint levels and a positive
exact-rate certificate for the source-defined tie-erased pullback sequence.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_pullback_source_rate_certificate
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (theorem31SelectedPullbackSourceWeight S.weight)
              (theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut
                S.hmono S.sampleRate levels hlevels))
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, hopt, hpos, hcert⟩
  refine ⟨levels, hlevels, heq, hopt, hpos, ?_⟩
  exact
    ExponentialRateCertificate.congr
      (lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source
        μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels S.weight)
      hcert

/--
Lemma C.4 forward branch for the canonical selected pullback source convention
with constant objective weight.
-/
theorem lemmaC4_appropriate_finite_levels_const_weight_pullback_source_rate_certificate
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsConstWeightModel μ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels S.sampleRate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (theorem31SelectedPullbackSourceWeight
                (fun _ : ℝ × ℝ => (1 : ℝ)))
              (theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut
                S.hmono S.sampleRate levels hlevels))
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) := by
  rcases
      lemmaC4_appropriate_finite_levels_const_weight_rate_certificate μ S with
    ⟨levels, hlevels, heq, hopt, hpos, hcert⟩
  refine ⟨levels, hlevels, heq, hopt, hpos, ?_⟩
  exact
    ExponentialRateCertificate.congr
      (lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source
        μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels
        (fun _ : ℝ × ℝ => (1 : ℝ)))
      hcert

/--
Lemma C.4 forward-realization bridge for the paper's source `\bar P_k`
kernel.  The finite-level model derives endpoint levels and an exact
source-defined `Wbar_k` rate certificate.  If the caller's source kernel is
identified with the selected finite-level endpoint/cutpoint kernel by the
structured realization interface, the source `Wbar_k` inherits that positive
certificate.

This is the source-faithful forward route for the paper's `W-W_k` convention:
the source kernel may already erase same-bin/tie terms.  It therefore does not
require equality between a raw all-strict-pairs `1 - P_k` kernel and the
selected endpoint/cutpoint integral.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (sourceWeight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hrealization :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          LemmaC4TieErasedSelectedIntegralRealization μ sourceWeight S.weight
            sourcePbarKernel
            (theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels)
            theorem31SelectedSourceCoordinateMap
            (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ sourceWeight sourcePbarKernel) rate := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, _hopt, hpos, hcert⟩
  refine
    ⟨binaryEndpointAwareAdjacentRateObjective levels S.sampleRate, hpos, ?_⟩
  exact
    ExponentialRateCertificate.congr
      (lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization
        μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels
        sourceWeight S.weight sourcePbarKernel
        (hrealization levels hlevels heq))
      hcert

/--
Lemma C.4 forward-realization bridge for the raw strict-pair source error.
The source finite-level model derives the endpoint levels and exact
source-defined `Wbar_k` rate certificate.  If the caller's raw source error is
eventually that same selected endpoint integral, the raw source error inherits
the positive exact-rate certificate.

This is intentionally stronger than a bare finite-range premise: finite range
alone does not identify the real source sequence with the endpoint/cutpoint
construction used by Lemma C.3.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_rawSourceWError_rate_certificate_of_eventually_eq
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
          hprob0 hprob1 weight) rate := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, _hopt, hpos, hcert⟩
  exact
    ⟨binaryEndpointAwareAdjacentRateObjective levels S.sampleRate, hpos,
      ExponentialRateCertificate.congr
        (hsource_eq levels hlevels heq) hcert⟩

/--
Lemma C.4 forward-realization bridge for the tie-erased source `Wbar_k`
convention with the concrete raw floor-complement kernel.  The only source
identification needed is eventual equality with the endpoint/cutpoint
`theorem31SourceWbar` integral derived from the finite-level model.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1) sampleRate
                  q.1 q.2 k)
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)) rate := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, _hopt, hpos, hcert⟩
  exact
    ⟨binaryEndpointAwareAdjacentRateObjective levels S.sampleRate, hpos,
      ExponentialRateCertificate.congr
        (hsource_eq levels hlevels heq) hcert⟩

/--
Lemma C.4 forward-realization bridge when the source tie-erased `Wbar_k`
decomposes into the selected finite-level `theorem31SourceWbar` term plus an
eventually zero residual.  This is the safe residual-erasure form: an
off-support complement with merely zero exponential rate would not preserve a
positive-rate certificate.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq_add_eventually_zero
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    (residual :
      (levels : Fin (S.m + 2) → ℝ) →
        BinaryEndpointLevelVector levels → ℕ → ℝ)
    (hsource_decomp :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1) sampleRate
                  q.1 q.2 k)
            =ᶠ[atTop]
          fun k : ℕ =>
            theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
              S.weight k + residual levels hlevels k)
    (hresidual_zero :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          ∀ᶠ k : ℕ in atTop, residual levels hlevels k = 0) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)) rate := by
  rcases
      lemmaC4_appropriate_finite_levels_weighted_rate_certificate μ S with
    ⟨levels, hlevels, heq, _hopt, hpos, hcert⟩
  exact
    ⟨binaryEndpointAwareAdjacentRateObjective levels S.sampleRate, hpos,
      ExponentialRateCertificate.congr_add_eventually_zero
        (hsource_decomp levels hlevels heq)
        (hresidual_zero levels hlevels heq) hcert⟩

/--
Lemma C.4 forward-realization bridge in the tie-erased source convention,
using the structured selected-support realization interface.  This replaces
the opaque eventual-equality premise by selected-support containment,
on-support integrand agreement, and zero contribution off the selected support
inside the strict ordered-pair source region.
-/
theorem lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_selected_realization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hrealization :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          LemmaC4TieErasedSelectedIntegralRealization μ R.weight S.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)
            (theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels)
            theorem31SelectedSourceCoordinateMap
            (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq
    μ S R.successProb R.sampleRate R.hprob0 R.hprob1 R.weight
    (fun levels hlevels heq =>
      lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization
        μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels
        R.weight S.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k)
        (hrealization levels hlevels heq))

/--
Tie-erased `Wbar_k` source-minorant bridge.  If the source pairwise
complement kernel agrees with the raw floor-complement kernel on the local
witness interval, then that local raw obstruction is eventually bounded by the
named source-defined `Wbar_k` sequence.
-/
theorem lemmaC4TieErasedSourceWbar_eventually_floorPk_local_le_of_eq_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourcePbarKernel k q)
    (hsource_eq_raw_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourcePbarKernel k q = rawKernel k q) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ)) ≤
        lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel k :=
  lemmaC4_sourceWError_eventually_raw_floorPk_local_le_of_eq_on_witness
    μ weight rawKernel sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel)
    hsource_int hsource_nonneg hsource_eq_raw_on
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)

/--
Tie-erased `Wbar_k` source-minorant bridge with a one-sided local comparison.
This is useful for source conventions that erase ties or otherwise dominate
the raw local floor-complement integrand on the non-tie witness interval.
-/
theorem lemmaC4TieErasedSourceWbar_eventually_floorPk_local_le_of_le_on_witness
    (μ : Measure ℝ)
    (weight : ℝ × ℝ → ℝ)
    (rawKernel sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hlocal_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * rawKernel k q)
          (AppliedModelingLib.strictUpperPairSetOn a b) (μ.prod μ))
    (hsource_int :
      ∀ᶠ k : ℕ in atTop,
        IntegrableOn
          (fun q : ℝ × ℝ => weight q * sourcePbarKernel k q)
          AppliedModelingLib.strictUpperPairSet (μ.prod μ))
    (hsource_nonneg :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ weight q * sourcePbarKernel k q)
    (hsource_raw_le_on :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          weight q * rawKernel k q ≤ weight q * sourcePbarKernel k q) :
    ∀ᶠ k : ℕ in atTop,
      (∫ q in AppliedModelingLib.strictUpperPairSetOn a b,
        weight q * rawKernel k q ∂(μ.prod μ)) ≤
        lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel k :=
  lemmaC4_sourceWError_eventually_raw_floorPk_local_le_of_le_on_witness
    μ weight rawKernel sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel)
    hlocal_int hsource_int hsource_nonneg hsource_raw_le_on
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)

/--
Source-defined form of the tie-erased `Wbar_k` non-tie witness bridge.  This
packages the displayed strict ordered-pair integral convention into the
sequence itself, leaving only the source-kernel non-tie equality and bounded
measurability hypotheses visible.
-/
theorem lemmaC4TieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsource_eq_raw_on_nonTie_witness :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourcePbarKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) 0 :=
  lemmaC4_tieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness
    μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel)
    (a := a) (b := b) (K := K) hweight_int hweight_nonneg
    hweight_cont hweight_x0_pos hsource_weight_int hsource_weight_nonneg
    hab hsample_pos_on hprob_pos_on hprob_lt_one_on hsample_cont_on
    hK_nonneg hsource_kernel_meas hsource_kernel_bound
    hsource_eq_raw_on_nonTie_witness
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)

/--
No-positive-rate form of the source-defined tie-erased `Wbar_k` non-tie
witness bridge.
-/
theorem lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_monotone_interval_nonTie_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hsource_eq_raw_on_nonTie_witness :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
          sourcePbarKernel k q =
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel)
    (lemmaC4TieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight sourcePbarKernel (a := a) (b := b) (K := K)
      hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hsource_weight_int hsource_weight_nonneg hab hsample_pos_on
      hprob_pos_on hprob_lt_one_on hsample_cont_on hK_nonneg
      hsource_kernel_meas hsource_kernel_bound
      hsource_eq_raw_on_nonTie_witness)

/--
Source-defined version of the tie-erased `Wbar_k` positive-rate iff.  This
uses `lemmaC4TieErasedSourceWbar` as the source sequence, so the displayed
integral identity is no longer a caller premise.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    {K : ℝ}
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ᶠ k : ℕ in atTop,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ᶠ k : ℕ in atTop,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate)
    (hnonpiecewise_witness :
      ¬ isPiecewiseConstant →
        ∃ a b : ℝ,
          a < b ∧
          Integrable weight
            ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) ∧
          (∀ᵐ q ∂(μ.prod μ).restrict
              (AppliedModelingLib.strictUpperPairSetOn a b),
            0 ≤ weight q) ∧
          (∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ)) ∧
          (∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ)) ∧
          (∀ θ ∈ Set.Icc a b, 0 < sampleRate θ) ∧
          (∀ θ ∈ Set.Icc a b, 0 < successProb θ) ∧
          (∀ θ ∈ Set.Icc a b, successProb θ < 1) ∧
          (∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ) ∧
          (∀ᶠ k : ℕ in atTop,
            ∀ q : ℝ × ℝ, q ∈ AppliedModelingLib.strictUpperPairSetOn a b →
              sourcePbarKernel k q =
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1) sampleRate
                  q.1 q.2 k)) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate :=
  lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness
    μ isPiecewiseConstant successProb sampleRate hprob_mono hprob0
    hprob1 hprob_meas hsample_meas weight sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) hsource_weight_int
    hsource_weight_nonneg hK_nonneg hsource_kernel_meas
    hsource_kernel_bound
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)
    hforward hnonpiecewise_witness

/--
Lemma C.4 tie-erased source-`Wbar_k` positive-rate iff under the concrete
local-constant interval convention.  This is the source-facing `Wbar_k`
counterpart of `lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError`:
for monotone Bernoulli rules, non-local-constancy on a supported interval
supplies the interior probability variation needed by the tie-erased reverse
zero-rate bridge.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  refine
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_prob_interval_of_measurableKernel
      μ hlohi (fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi)
      successProb sampleRate hprob_mono weight sourcePbarKernel sourceWbar
      hK_nonneg hsource_weight_int hsource_weight_nonneg
      hsource_kernel_meas hsource_kernel_bound hcert hsourceWbar_eq
      hforward hweight_cont hsample_cont ?_ hweight_pos_on hsample_pos_on
  intro hnot_local
  exact
    lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
      hlohi (fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi)
      successProb hprob_mono
      (lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
        (fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi)
        successProb hprob_interior_on
        (lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
          (fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi)
          successProb hprob_mono
          (by
            intro hconstant
            simpa [lemmaC4LocallyConstantOnIoo] using hconstant)))
      hnot_local

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under the
paper's local-constancy interval convention.  This is the same theorem as the
generic `sourceWbar` wrapper, with the displayed strict-pair integral
definition of `Wbar_k` built into the sequence itself.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate :=
  lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_measurableKernel
    μ hlohi successProb sampleRate hprob_mono weight sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) hK_nonneg
    hsource_weight_int hsource_weight_nonneg hsource_kernel_meas
    hsource_kernel_bound hcert
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)
    hforward hweight_cont hsample_cont hprob_interior_on hweight_pos_on
    hsample_pos_on

/--
Lemma C.4 tie-erased source-`Wbar_k` reverse obstruction under the concrete
local-constancy interval convention.  This is the source-facing reverse
branch alone: for monotone Bernoulli rules, non-local-constancy on a supported
interval supplies a continuity point where the diagonal closed rate is zero,
so no strictly positive exponential-rate certificate can hold.
-/
theorem lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q * sourcePbarKernel k q ∂(μ.prod μ))
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate sourceWbar rate := by
  let isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop :=
    fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi
  have hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1 := by
    exact
      lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
        hlohi isStepwiseConstantOn successProb hprob_mono
        (lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
          isStepwiseConstantOn successProb hprob_interior_on
          (lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
            isStepwiseConstantOn successProb hprob_mono
            (by
              intro hconstant
              simpa [isStepwiseConstantOn, lemmaC4LocallyConstantOnIoo]
                using hconstant)))
  rcases
      lemmaC4_nonstepwise_interior_continuity_point_witness_of_monotone_prob_interval
        hlohi isStepwiseConstantOn successProb hprob_mono
        hnot_step_to_prob_interval hnot_local with
    ⟨θ0, hθ0, hβ0, hβ1, hβ_cont⟩
  rcases AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0) with
    ⟨G, hG_pos, hg_le⟩
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont θ0).eventually
      (Ioi_mem_nhds (hsample_pos_on θ0 hθ0))
  exact
    lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel
      μ successProb sampleRate weight sourcePbarKernel sourceWbar
      (θ0 := θ0) (G := G) hK_nonneg hsource_weight_int
      hsource_weight_nonneg hsource_kernel_meas hsource_kernel_bound
      (hweight_cont θ0) (hweight_pos_on θ0 hθ0) hβ_cont hβ0 hβ1
      (hsample_pos_on θ0 hθ0) hG_pos hg_pos hg_le hcert hsourceWbar_eq

/--
Lemma C.4 source-defined tie-erased `Wbar_k` reverse obstruction under the
paper's local-constancy interval convention.
-/
theorem lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate :=
  lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    μ hlohi successProb sampleRate hprob_mono weight sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) hK_nonneg
    hsource_weight_int hsource_weight_nonneg hsource_kernel_meas
    hsource_kernel_bound hcert
    (lemmaC4TieErasedSourceWbar_eventually_eq μ weight sourcePbarKernel)
    hnot_local hweight_cont hsample_cont hprob_interior_on
    hweight_pos_on hsample_pos_on

/--
Lemma C.4 source-defined tie-erased `Wbar_k` reverse obstruction under the
finite-range source convention.  Non-finite-range rules are not locally
constant on the same witness interval, so the existing tie-erased obstruction
applies.
-/
theorem lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate :=
  lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    μ hlohi successProb sampleRate hprob_mono weight sourcePbarKernel
    hK_nonneg hsource_weight_int hsource_weight_nonneg hsource_kernel_meas
    hsource_kernel_bound hcert
    (by
      intro hlocal
      exact hnot_finite
        (lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo
          successProb hlohi hlocal))
    hweight_cont hsample_cont hprob_interior_on hweight_pos_on
    hsample_pos_on

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
reverse obstruction under the finite-range source convention.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate := by
  simpa using
    lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel hK_nonneg
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hsource_kernel_meas hsource_kernel_bound hcert hnot_finite
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
reverse obstruction for probability kernels under the finite-range source
convention.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate :=
  lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel
    μ hlohi successProb hprob_mono sourcePbarKernel (K := (1 : ℝ))
    (by norm_num) hsource_kernel_meas hsource_kernel_unit hcert
    hnot_finite hprob_interior_on

/--
Probability-kernel finite-range reverse obstruction, accepting the source's
uniform exponential-rate certificate format.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel_uniformExponentialRateCertificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformExponentialRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate :=
  lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel
    μ hlohi successProb hprob_mono sourcePbarKernel hsource_kernel_meas
    hsource_kernel_unit hcert.toUniformNormalizedLogRateCertificateOn
    hnot_finite hprob_interior_on

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under the
finite-range source convention.  The forward direction is the finite-step
positive-rate construction; the reverse direction is derived from monotone
non-finite-range variation.
-/
theorem lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (weight : ℝ × ℝ → ℝ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_weight_int :
      Integrable weight
        ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hforward :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4FiniteRangeOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel) rate := by
  exact
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_no_positive_reverse
      (lemmaC4FiniteRangeOnIoo successProb lo hi)
      (lemmaC4TieErasedSourceWbar μ weight sourcePbarKernel)
      hforward
      (fun hnot_finite =>
        lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel
          μ hlohi successProb sampleRate hprob_mono weight sourcePbarKernel
          hK_nonneg hsource_weight_int hsource_weight_nonneg
          hsource_kernel_meas hsource_kernel_bound hcert hnot_finite
          hweight_cont hsample_cont hprob_interior_on hweight_pos_on
          hsample_pos_on)

/--
Constant-weight, uniform-sampling specialization of the tie-erased
`Wbar_k` reverse obstruction.  This is the clean no-positive-rate form of
the C.4 non-local-constancy branch under the common normalized source
convention.
-/
theorem lemmaC4_tieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            (1 : ℝ) * sourcePbarKernel k q ∂(μ.prod μ))
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate sourceWbar rate := by
  simpa using
    lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel sourceWbar
      hK_nonneg
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hsource_kernel_meas hsource_kernel_bound hcert hsourceWbar_eq
      hnot_local
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
reverse obstruction for non-local-constant rules.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate :=
  lemmaC4_tieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    μ hlohi successProb hprob_mono sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
      sourcePbarKernel)
    hK_nonneg hsource_kernel_meas hsource_kernel_bound hcert
    (lemmaC4TieErasedSourceWbar_eventually_eq μ
      (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel)
    hnot_local hprob_interior_on

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
reverse obstruction for probability kernels.  This specializes the bounded
kernel wrapper to `0 ≤ Pbar_k ≤ 1`, matching the paper's probabilistic
source convention.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate :=
  lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel
    μ hlohi successProb hprob_mono sourcePbarKernel (K := (1 : ℝ))
    (by norm_num) hsource_kernel_meas hsource_kernel_unit hcert
    hnot_local hprob_interior_on

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
reverse obstruction for probability kernels, accepting a uniform exponential
rate certificate and converting it to the normalized-log interface internally.
-/
theorem lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel_uniformExponentialRateCertificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformExponentialRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          sourcePbarKernel) rate :=
  lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel
    μ hlohi successProb hprob_mono sourcePbarKernel hsource_kernel_meas
    hsource_kernel_unit hcert.toUniformNormalizedLogRateCertificateOn
    hnot_local hprob_interior_on

/--
Constant-weight, uniform-sampling specialization of the tie-erased source
`Wbar_k` local-constancy C.4 wrapper.  This discharges the generic weight and
sample-rate regularity hypotheses for the common normalized source convention,
leaving only the source kernel certificate, the displayed `Wbar_k` integral
identity, the forward positive-rate construction, and interior Bernoulli
probabilities on the witness interval.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (sourceWbar : ℕ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hsourceWbar_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWbar k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            (1 : ℝ) * sourcePbarKernel k q ∂(μ.prod μ))
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWbar rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWbar rate := by
  simpa using
    lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_measurableKernel
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel sourceWbar
      hK_nonneg
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hsource_kernel_meas hsource_kernel_bound hcert hsourceWbar_eq
      hforward
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
local-constancy positive-rate iff.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ
            (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate :=
  lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel
    μ hlohi successProb hprob_mono sourcePbarKernel
    (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
      sourcePbarKernel)
    hK_nonneg hsource_kernel_meas hsource_kernel_bound hcert
    (lemmaC4TieErasedSourceWbar_eventually_eq μ
      (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel)
    hforward hprob_interior_on

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
local-constancy positive-rate iff for probability kernels.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ
            (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate :=
  lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel
    μ hlohi successProb hprob_mono sourcePbarKernel (K := (1 : ℝ))
    (by norm_num) hsource_kernel_meas hsource_kernel_unit hcert hforward
    hprob_interior_on

/--
Source-defined, constant-weight, uniform-sampling tie-erased `Wbar_k`
local-constancy positive-rate iff for probability kernels, accepting the
source's uniform exponential-rate certificate format.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel_uniformExponentialRateCertificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_unit :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ (1 : ℝ))
    (hcert :
      UniformExponentialRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (successProb q.1) (successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ
              (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ
            (fun _ : ℝ × ℝ => (1 : ℝ)) sourcePbarKernel) rate :=
  lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel
    μ hlohi successProb hprob_mono sourcePbarKernel hsource_kernel_meas
    hsource_kernel_unit hcert.toUniformNormalizedLogRateCertificateOn
    hforward hprob_interior_on

/--
Lemma C.4 reverse branch for the source-defined raw global `W^k` error under
the concrete local-constant interval convention.  If a monotone Bernoulli rule
is not locally constant on an interval where the model primitives are positive,
then the continuum error has exact exponential rate zero.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_locallyConstantOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight) 0 := by
  let isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop :=
    fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi
  have hnot_step_to_variation :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          successProb x < successProb y :=
    lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise
      isStepwiseConstantOn successProb hprob_mono
      (by
        intro hconstant
        simpa [isStepwiseConstantOn, lemmaC4LocallyConstantOnIoo] using
          hconstant)
  have hnot_step_to_two_values :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ x y : ℝ,
          x ∈ Set.Ioo lo hi ∧
          y ∈ Set.Ioo lo hi ∧
          x < y ∧
          0 < successProb x ∧
          successProb y < 1 :=
    lemmaC4_nonstepwise_two_interior_values_of_monotone_variation
      isStepwiseConstantOn successProb hprob_interior_on
      hnot_step_to_variation
  have hnot_step_to_prob_interval :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ a b : ℝ,
          lo ≤ a ∧ a < b ∧ b ≤ hi ∧
          ∀ θ ∈ Set.Ioo a b,
            0 < successProb θ ∧ successProb θ < 1 :=
    lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values
      hlohi isStepwiseConstantOn successProb hprob_mono
      hnot_step_to_two_values
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_positive_interval_witness
      μ (lemmaC4LocallyConstantOnIoo successProb lo hi)
      successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight)
      hsource_weight_int hsource_weight_nonneg
      (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
        sampleRate hprob0 hprob1 weight)
      hnot_local hweight_cont hweight_diag_cont hsample_cont
      (lemmaC4_nonpiecewise_monotone_positive_interval_witness_of_not_stepwiseOn
        hlohi isStepwiseConstantOn successProb sampleRate weight
        hnot_step_to_prob_interval hweight_pos_on hsample_pos_on)

/--
Lemma C.4 reverse branch for the source-defined raw global `W^k` error under
the finite-range source convention.  A monotone rule with infinitely many
success-probability values on the source interval cannot have a positive
exponential rate.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight) 0 := by
  exact
    lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_locallyConstantOnIoo
      μ hlohi successProb sampleRate hprob_mono hprob0 hprob1
      hprob_meas hsample_meas weight hsource_weight_int
      hsource_weight_nonneg
      (by
        intro hlocal
        exact hnot_finite
          (lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo
            successProb hlohi hlocal))
      hweight_cont hweight_diag_cont hsample_cont hprob_interior_on
      hweight_pos_on hsample_pos_on

/--
No-positive-rate form of the finite-range C.4 reverse branch for the
source-defined raw global `W^k` error.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_not_finiteRangeOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
          hprob0 hprob1 weight) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight)
      (lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo
        μ hlohi successProb sampleRate hprob_mono hprob0 hprob1
        hprob_meas hsample_meas weight hsource_weight_int
        hsource_weight_nonneg hnot_finite hweight_cont hweight_diag_cont
        hsample_cont hprob_interior_on hweight_pos_on hsample_pos_on)

/--
Constant-weight, uniform-sampling specialization of the C.4 reverse branch.
For the Kendall-style source normalization, the only remaining analytic
conditions are monotonicity, measurability, local nonconstancy, and interior
Bernoulli probabilities on the witness interval.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_locallyConstantOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb
        (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
        (fun _ : ℝ × ℝ => (1 : ℝ))) 0 := by
  simpa using
    lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_locallyConstantOnIoo
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hnot_local
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Constant-weight, uniform-sampling C.4 reverse branch in no-positive-rate
form.  This is the direct source consequence of the zero-rate obstruction.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hnot_local :
      ¬ lemmaC4LocallyConstantOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ successProb
          (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
          (fun _ : ℝ × ℝ => (1 : ℝ))) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb
        (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
        (fun _ : ℝ × ℝ => (1 : ℝ)))
      (lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_locallyConstantOnIoo
        μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
        hnot_local hprob_interior_on)

/--
Constant-weight, uniform-sampling specialization of the finite-range C.4
reverse branch.  This is the source-shaped obstruction used for the
Kendall/Spearman normalization when the rating rule has infinitely many
success-probability values on the witness interval.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_finiteRangeOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb
        (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
        (fun _ : ℝ × ℝ => (1 : ℝ))) 0 := by
  simpa using
    lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hnot_finite
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
No-positive-rate form of the constant-weight, uniform-sampling finite-range
C.4 reverse branch.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ successProb
          (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
          (fun _ : ℝ × ℝ => (1 : ℝ))) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb
        (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
        (fun _ : ℝ × ℝ => (1 : ℝ)))
      (lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_finiteRangeOnIoo
        μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
        hnot_finite hprob_interior_on)

/--
Lemma C.4 source-facing positive-rate iff with the finite-range source
convention.  The reverse direction is derived from monotone non-finite-range
variation; the forward direction remains the source finite-step positive-rate
construction.
-/
theorem lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4FiniteRangeOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate := by
  exact
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      (lemmaC4FiniteRangeOnIoo successProb lo hi)
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight)
      hforward
      (fun hnot_finite =>
        lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo
          μ hlohi successProb sampleRate hprob_mono hprob0 hprob1
          hprob_meas hsample_meas weight hsource_weight_int
          hsource_weight_nonneg hnot_finite hweight_cont hweight_diag_cont
          hsample_cont hprob_interior_on hweight_pos_on hsample_pos_on)

/--
The source-defined `Wbar_k` sequence with the concrete raw strict-pair
floor-complement kernel is exactly the raw source error used by the C.4
reverse proof.  This equality is useful when the source convention writes the
same quantity as an abstract pairwise complement kernel before specializing it
to `1 - P_k`.
-/
theorem lemmaC4TieErasedSourceWbar_raw_floorPkComplementError_eq_rawStrictUpperPairSourceWError
    (μ : Measure ℝ)
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ) :
    lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k) =
      lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight := by
  funext k
  rfl

/--
Lemma C.4 finite-range positive-rate iff for the source-defined `Wbar_k`
sequence under the concrete raw strict-pair `1 - P_k` convention.  The reverse
direction is inherited from the fully derived raw-source theorem, so this form
does not require a separate pairwise-kernel certificate premise.
-/
theorem lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1) sampleRate
                  q.1 q.2 k)) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4FiniteRangeOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k)) rate := by
  let rawKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate q.1 q.2 k
  have hseq :
      lemmaC4TieErasedSourceWbar μ weight rawKernel =
        lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
          hprob0 hprob1 weight := by
    simpa [rawKernel] using
      lemmaC4TieErasedSourceWbar_raw_floorPkComplementError_eq_rawStrictUpperPairSourceWError
        μ successProb sampleRate hprob0 hprob1 weight
  have hforward_raw :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate := by
    intro hfinite
    rcases hforward hfinite with ⟨rate, hrate, hcert⟩
    refine ⟨rate, hrate, ?_⟩
    simpa [rawKernel, hseq] using hcert
  have hraw :
      lemmaC4FiniteRangeOnIoo successProb lo hi ↔
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate :=
    lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError
      μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight hsource_weight_int hsource_weight_nonneg
      hforward_raw hweight_cont hweight_diag_cont hsample_cont
      hprob_interior_on hweight_pos_on hsample_pos_on
  constructor
  · intro hfinite
    rcases hraw.mp hfinite with ⟨rate, hrate, hcert⟩
    refine ⟨rate, hrate, ?_⟩
    simpa [rawKernel, hseq] using hcert
  · intro hcerts
    rcases hcerts with ⟨rate, hrate, hcert⟩
    apply hraw.mpr
    refine ⟨rate, hrate, ?_⟩
    simpa [rawKernel, hseq] using hcert

/--
Constant-weight, uniform-sampling specialization of the source-defined raw
`Wbar_k` finite-range C.4 positive-rate iff.  This is the closest source shape
for the normalized Kendall/Spearman convention: weights and sample rates are
fixed at one, and the reverse branch has no pairwise-kernel certificate
premise.
-/
theorem lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError_const_weight_uniform_sampleRate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hforward :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1)
                  (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4FiniteRangeOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1)
                (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) rate := by
  simpa using
    lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hforward
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Constant-weight, uniform-sampling specialization of the finite-range C.4
positive-rate iff.
-/
theorem lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hforward :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb
              (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
              (fun _ : ℝ × ℝ => (1 : ℝ))) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4FiniteRangeOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb
            (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
            (fun _ : ℝ × ℝ => (1 : ℝ))) rate := by
  exact
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      (lemmaC4FiniteRangeOnIoo successProb lo hi)
      (lemmaC4RawStrictUpperPairSourceWError μ successProb
        (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
        (fun _ : ℝ × ℝ => (1 : ℝ)))
      hforward
      (fun hnot_finite =>
        lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_finiteRangeOnIoo
          μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
          hnot_finite hprob_interior_on)

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error with a concrete local-constant interval convention.  This is the
same monotone non-stepwise reverse argument as the generic stepwise wrapper,
but the semantic premise that constant interval rules count as stepwise is
discharged by definition.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
              hprob0 hprob1 weight) rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
            hprob0 hprob1 weight) rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonstepwise_constant_semantics
      μ hlohi (fun f lo hi => lemmaC4LocallyConstantOnIoo f lo hi)
      successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight hsource_weight_int hsource_weight_nonneg
      hforward hweight_cont hweight_diag_cont hsample_cont
      hprob_interior_on
      (by
        intro hconstant
        simpa [lemmaC4LocallyConstantOnIoo] using hconstant)
      hweight_pos_on hsample_pos_on

/--
Constant-weight, uniform-sampling specialization of the local-constancy C.4
positive-rate iff.  The generic weight integrability, nonnegativity,
continuity, positive diagonal support, sample-rate continuity, and sample-rate
positivity premises are discharged internally.
-/
theorem lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hforward :
      lemmaC4LocallyConstantOnIoo successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ successProb
              (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
              (fun _ : ℝ × ℝ => (1 : ℝ))) rate)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    lemmaC4LocallyConstantOnIoo successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ successProb
            (fun _ : ℝ => (1 : ℝ)) hprob0 hprob1
            (fun _ : ℝ × ℝ => (1 : ℝ))) rate := by
  simpa using
    lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      hforward
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      hprob_interior_on
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)

/--
Lemma C.4 source-facing positive-rate iff with a concrete stepwise-on-interval
convention and the reverse branch stated at the paper's continuity-point
level.  This packages the source prose claim that a non-piecewise monotone
rating rule has a regular diagonal continuity point with interior Bernoulli
probability into the existing zero-rate obstruction.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_continuity_point
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ}
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ θ0 : ℝ,
          0 < weight (θ0, θ0) ∧
          0 < sampleRate θ0 ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_continuity_point_witness
      μ (isStepwiseConstantOn successProb lo hi) successProb sampleRate
      hprob_mono hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont hpoint

/--
Lemma C.4 source-facing positive-rate iff where the reverse branch starts from
an interior continuity point of the monotone Bernoulli rule.  The shared
continuity-shrink lemma turns that point into the probability subinterval used
by the local zero-rate obstruction, while positivity of the source weight and
sample rate is checked on the ambient quality interval.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_interior_continuity_point
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hpoint :
      ¬ isStepwiseConstantOn successProb lo hi →
        ∃ θ0 : ℝ,
          θ0 ∈ Set.Ioo lo hi ∧
          0 < successProb θ0 ∧
          successProb θ0 < 1 ∧
          ContinuousAt successProb θ0)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  refine
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont ?_ hweight_pos_on
      hsample_pos_on
  intro hnot_step
  rcases hpoint hnot_step with
    ⟨θ0, hθ0_mem, hprob_pos, hprob_lt_one, hprob_cont⟩
  exact
    AppliedModelingLib.exists_Ioo_subset_preimage_Ioo_of_continuousAt_interior
      hθ0_mem hprob_cont hprob_pos hprob_lt_one

/--
Lemma C.4 source-facing positive-rate iff on an already-supported quality
interval.  If the source model supplies a nonempty quality interval on which
the diagonal weight, sample rate, and Bernoulli probability are all positive
and the Bernoulli probability is strictly interior, then the non-stepwise
reverse branch uses that interval directly.
-/
theorem lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_positive_support_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hforward :
      isStepwiseConstantOn successProb lo hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate sourceWError rate)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    isStepwiseConstantOn successProb lo hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate sourceWError rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono
      hprob0 hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hforward
      hweight_cont hweight_diag_cont hsample_cont
      (by
        intro _hnot_step
        exact ⟨lo, hi, le_rfl, hlohi, le_rfl, hprob_interior_on⟩)
      hweight_pos_on hsample_pos_on

/--
Lemma C.4 reverse branch on a supported source interval.  If a monotone
Bernoulli rule is not stepwise under a concrete source convention, and the
whole witness interval has positive diagonal weight, positive sample rate, and
interior Bernoulli probabilities, then the raw source `W^k` error has exact
exponential rate zero.
-/
theorem lemmaC4_rawSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_step : ¬ isStepwiseConstantOn successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    HasExponentialRate sourceWError 0 := by
  exact
    lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_positive_interval_witness
      μ (isStepwiseConstantOn successProb lo hi) successProb sampleRate
      hprob_mono hprob0 hprob1 hprob_meas hsample_meas weight
      sourceWError hsource_weight_int hsource_weight_nonneg
      hsourceWError_eq hnot_step hweight_cont hweight_diag_cont
      hsample_cont
      (by
        intro _hnot_step
        exact
          ⟨lo, hi, hlohi, fun θ hθ =>
            ⟨hweight_pos_on θ hθ, hsample_pos_on θ hθ,
              (hprob_interior_on θ hθ).1,
              (hprob_interior_on θ hθ).2⟩⟩)

/--
Lemma C.4 reverse branch on a supported source interval, in the paper's
no-positive-rate form.
-/
theorem lemmaC4_rawSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (sourceWError : ℕ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hsourceWError_eq :
      ∀ᶠ k : ℕ in atTop,
        sourceWError k =
          ∫ q in AppliedModelingLib.strictUpperPairSet,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k ∂(μ.prod μ))
    (hnot_step : ¬ isStepwiseConstantOn successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate → ¬ ExponentialRateCertificate sourceWError rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate sourceWError
    (lemmaC4_rawSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono hprob0
      hprob1 hprob_meas hsample_meas weight sourceWError
      hsource_weight_int hsource_weight_nonneg hsourceWError_eq hnot_step
      hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
      hsample_pos_on hprob_interior_on)

/--
Lemma C.4 reverse branch for the source-defined raw `W^k` error on a supported
interval.  This discharges the bookkeeping equality between a caller-supplied
source sequence and the strict ordered-pair integral.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_step : ¬ isStepwiseConstantOn successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
        hprob0 hprob1 weight) 0 :=
  lemmaC4_rawSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
    μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono hprob0
    hprob1 hprob_meas hsample_meas weight
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    hsource_weight_int hsource_weight_nonneg
    (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ successProb
      sampleRate hprob0 hprob1 weight)
    hnot_step hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on

/--
Lemma C.4 reverse branch for the source-defined raw `W^k` error on a supported
interval, in the paper's no-positive-rate form.
-/
theorem lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
        0 ≤ weight q)
    (hnot_step : ¬ isStepwiseConstantOn successProb lo hi)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate
          hprob0 hprob1 weight) rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
    (lemmaC4RawStrictUpperPairSourceWError μ successProb sampleRate hprob0
      hprob1 weight)
    (lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
      μ hlohi isStepwiseConstantOn successProb sampleRate hprob_mono hprob0
      hprob1 hprob_meas hsample_meas weight hsource_weight_int
      hsource_weight_nonneg hnot_step hweight_cont hweight_diag_cont
      hsample_cont hweight_pos_on hsample_pos_on hprob_interior_on)

/--
Lemma C.4 reverse branch from the paper-local positive-support source model.
The model contains only primitive regularity and support facts; the exact
zero-rate conclusion for the raw source `W^k` error is derived from the
monotone nonstepwise interval obstruction.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_has_zero_rate_of_nonstepwise
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hnot_step : ¬ isStepwiseConstantOn S.successProb S.lo S.hi) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
        S.hprob0 S.hprob1 S.weight) 0 :=
  lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval
    μ S.hlohi isStepwiseConstantOn S.successProb S.sampleRate S.hprob_mono
    S.hprob0 S.hprob1 S.hprob_meas S.hsample_meas S.weight
    S.hsource_weight_int S.hsource_weight_nonneg hnot_step
    S.hweight_cont S.hweight_diag_cont S.hsample_cont S.hweight_pos_on
    S.hsample_pos_on S.hprob_interior_on

/--
Lemma C.4 no-positive-rate reverse branch from the paper-local
positive-support source model.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_no_positive_exponential_rate_of_nonstepwise
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hnot_step : ¬ isStepwiseConstantOn S.successProb S.lo S.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
          S.hprob0 S.hprob1 S.weight) rate :=
  lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
    (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
      S.hprob0 S.hprob1 S.weight)
    (lemmaC4_rawSourcePositiveSupportIntervalModel_has_zero_rate_of_nonstepwise
      μ S isStepwiseConstantOn hnot_step)

/--
Lemma C.4 no-positive-rate reverse branch from the positive-support source
model under the paper's finite-range reading of piecewise constancy.  This
direction does not require a finite-level forward realization theorem.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_no_positive_exponential_rate_of_not_finiteRange
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
          S.hprob0 S.hprob1 S.weight) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_no_positive_exponential_rate_of_nonstepwise
    μ S (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi) hnot_finite

/--
Lemma C.4 exact-zero-rate reverse branch from the positive-support source
model under the paper's finite-range reading of piecewise constancy.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_has_zero_rate_of_not_finiteRange
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi) :
    HasExponentialRate
      (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
        S.hprob0 S.hprob1 S.weight) 0 :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_has_zero_rate_of_nonstepwise
    μ S (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi) hnot_finite

/--
Lemma C.4 no-positive-rate reverse branch for the source-defined tie-erased
`Wbar_k` sequence with the concrete raw strict-pair floor-complement kernel.
Unlike the positive-rate iff theorem, this reverse-only form does not require
the finite-level forward model or eventual equality with `theorem31SourceWbar`.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRange_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ S.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel S.successProb S.hprob0 S.hprob1)
              S.sampleRate q.1 q.2 k)) rate := by
  have hseq :
      lemmaC4TieErasedSourceWbar μ S.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel S.successProb S.hprob0 S.hprob1)
              S.sampleRate q.1 q.2 k) =
        lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
          S.hprob0 S.hprob1 S.weight := by
    exact
      lemmaC4TieErasedSourceWbar_raw_floorPkComplementError_eq_rawStrictUpperPairSourceWError
        μ S.successProb S.sampleRate S.hprob0 S.hprob1 S.weight
  intro rate hrate hcert
  exact
    (lemmaC4_rawSourcePositiveSupportIntervalModel_no_positive_exponential_rate_of_not_finiteRange
      μ S hnot_finite rate hrate)
      (by simpa [hseq] using hcert)

/--
Lemma C.4 exact-zero-rate reverse branch for the source-defined tie-erased
`Wbar_k` sequence with the concrete raw strict-pair floor-complement kernel.
This is the exact-rate strengthening of the corresponding no-positive-rate
theorem.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_has_zero_rate_of_not_finiteRange_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ S.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel S.successProb S.hprob0 S.hprob1)
            S.sampleRate q.1 q.2 k)) 0 := by
  have hseq :
      lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
          S.hprob0 S.hprob1 S.weight =ᶠ[atTop]
        lemmaC4TieErasedSourceWbar μ S.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel S.successProb S.hprob0 S.hprob1)
              S.sampleRate q.1 q.2 k) := by
    filter_upwards with k
    rw [
      lemmaC4TieErasedSourceWbar_raw_floorPkComplementError_eq_rawStrictUpperPairSourceWError
        μ S.successProb S.sampleRate S.hprob0 S.hprob1 S.weight]
  exact
    HasExponentialRate.congr hseq
      (lemmaC4_rawSourcePositiveSupportIntervalModel_has_zero_rate_of_not_finiteRange
        μ S hnot_finite)

/--
Lemma C.4 source-model constructor for the non-piecewise reverse branch.
If the paper's piecewise-constant predicate includes every finite-range rule
on the supported interval, then a non-piecewise source rule supplies the
positive-support interval model together with the non-finite-range witness
used by the reverse C.4 theorem.
-/
theorem lemmaC4_exists_positiveSupportIntervalModel_and_not_finiteRange_of_nonpiecewise_monotone_beta
    (μ : Measure ℝ)
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    ∃ R : LemmaC4RawSourcePositiveSupportIntervalModel μ,
      R.successProb = successProb ∧
        R.sampleRate = sampleRate ∧
          R.weight = weight ∧
            R.lo = lo ∧
              R.hi = hi ∧
                ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi := by
  let R : LemmaC4RawSourcePositiveSupportIntervalModel μ :=
    { lo := lo
      hi := hi
      hlohi := hlohi
      successProb := successProb
      sampleRate := sampleRate
      hprob_mono := hprob_mono
      hprob0 := hprob0
      hprob1 := hprob1
      hprob_meas := hprob_meas
      hsample_meas := hsample_meas
      weight := weight
      hsource_weight_int := hsource_weight_int
      hsource_weight_nonneg := hsource_weight_nonneg
      hweight_cont := hweight_cont
      hweight_diag_cont := hweight_diag_cont
      hsample_cont := hsample_cont
      hweight_pos_on := hweight_pos_on
      hsample_pos_on := hsample_pos_on
      hprob_interior_on := hprob_interior_on }
  refine ⟨R, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hfinite
  exact hnot_piecewise (hfinite_to_piecewise hfinite)

/--
Lemma C.4 no-positive-rate reverse branch from the paper's non-piecewise
source predicate.  The only semantic source bridge is that finite-range rules
count as piecewise constant on the supported interval.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_piecewise_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi →
        isPiecewiseConstantOn S.successProb S.lo S.hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn S.successProb S.lo S.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ S.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel S.successProb S.hprob0 S.hprob1)
              S.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRange_raw_floorPkComplementError
    μ S (fun hfinite => hnot_piecewise (hfinite_to_piecewise hfinite))

/--
Lemma C.4 source-model positive-rate iff for the raw strict-pair `W^k`
convention.  The forward implication is the finite-step positive-rate
construction; the reverse implication is derived from the source model's
monotone positive-support interval, not assumed as a certificate.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_stepwise_iff_exists_positive_exponential_rate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (isStepwiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hforward :
      isStepwiseConstantOn S.successProb S.lo S.hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ S.successProb
              S.sampleRate S.hprob0 S.hprob1 S.weight) rate) :
    isStepwiseConstantOn S.successProb S.lo S.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ S.successProb
            S.sampleRate S.hprob0 S.hprob1 S.weight) rate := by
  exact
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_positive_support_interval
      μ S.hlohi isStepwiseConstantOn S.successProb S.sampleRate
      S.hprob_mono S.hprob0 S.hprob1 S.hprob_meas S.hsample_meas S.weight
      (lemmaC4RawStrictUpperPairSourceWError μ S.successProb S.sampleRate
        S.hprob0 S.hprob1 S.weight)
      S.hsource_weight_int S.hsource_weight_nonneg
      (lemmaC4RawStrictUpperPairSourceWError_eventually_eq μ S.successProb
        S.sampleRate S.hprob0 S.hprob1 S.weight)
      hforward S.hweight_cont S.hweight_diag_cont S.hsample_cont
      S.hweight_pos_on S.hsample_pos_on S.hprob_interior_on

/--
Lemma C.4 source-model finite-range form for the raw strict-pair `W^k`
convention.  This specializes the source-model iff theorem to the paper's
finite-level/finite-range reading of "piecewise constant" on the supported
quality interval.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hforward :
      lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4RawStrictUpperPairSourceWError μ S.successProb
              S.sampleRate S.hprob0 S.hprob1 S.weight) rate) :
    lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ S.successProb
            S.sampleRate S.hprob0 S.hprob1 S.weight) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_stepwise_iff_exists_positive_exponential_rate
    μ S (fun f lo hi => lemmaC4FiniteRangeOnIoo f lo hi) hforward

/--
Lemma C.4 positive-support source model in the source-defined tie-erased
`Wbar_k` convention for the concrete raw strict-pair `1 - P_k` kernel.  This
packages the field-by-field raw-floor bridge under
`LemmaC4RawSourcePositiveSupportIntervalModel`, so callers do not have to
thread the monotonicity, measurability, support, and diagonal-positivity
fields manually.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (hforward :
      lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ S.weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel S.successProb S.hprob0 S.hprob1)
                  S.sampleRate q.1 q.2 k)) rate) :
    lemmaC4FiniteRangeOnIoo S.successProb S.lo S.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ S.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel S.successProb S.hprob0 S.hprob1)
                S.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError
    μ S.hlohi S.successProb S.sampleRate S.hprob_mono S.hprob0 S.hprob1
    S.hprob_meas S.hsample_meas S.weight S.hsource_weight_int
    S.hsource_weight_nonneg hforward S.hweight_cont S.hweight_diag_cont
    S.hsample_cont S.hprob_interior_on S.hweight_pos_on S.hsample_pos_on

/--
Lemma C.4 positive-support source model with the finite-level forward branch
realized explicitly.  The forward implication no longer appears as an opaque
certificate assumption: it is derived from the weighted finite-level source
model plus eventual equality between the caller's raw source error and the
endpoint/cutpoint `theorem31SourceWbar` integral.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_appropriate_finite_levels_rawSourceWError_eq
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4RawStrictUpperPairSourceWError μ R.successProb R.sampleRate
              R.hprob0 R.hprob1 R.weight
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4RawStrictUpperPairSourceWError μ R.successProb R.sampleRate
            R.hprob0 R.hprob1 R.weight) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate
    μ R
    (fun _hfinite =>
      lemmaC4_appropriate_finite_levels_weighted_rawSourceWError_rate_certificate_of_eventually_eq
        μ S R.successProb R.sampleRate R.hprob0 R.hprob1 R.weight
        hsource_eq)

/--
Lemma C.4 positive-support source model in the source-defined tie-erased
`Wbar_k` convention, with the finite-level forward branch realized explicitly.
The only source-specific forward datum is eventual equality with the
endpoint/cutpoint `theorem31SourceWbar` integral.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ R.weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                  R.sampleRate q.1 q.2 k)
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_floorPkComplementError
    μ R
    (fun _hfinite =>
      lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq
        μ S R.successProb R.sampleRate R.hprob0 R.hprob1 R.weight
        hsource_eq)

/--
Lemma C.4 positive-support source model in the tie-erased `Wbar_k`
convention, with the finite-level forward branch realized by the structured
selected-support source interface.  The forward branch now exposes the support
and integrand a.e. facts required to identify the paper source integral with
the endpoint/cutpoint `theorem31SourceWbar` integral.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hrealization :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          LemmaC4TieErasedSelectedIntegralRealization μ R.weight S.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)
            (theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels)
            theorem31SelectedSourceCoordinateMap
            (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_floorPkComplementError
    μ R
    (fun _hfinite =>
      lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_selected_realization
        μ R S hrealization)

/--
Lemma C.4 positive-support source model in the tie-erased `Wbar_k`
convention, with the selected-source realization reduced to two pointwise
source equalities: the raw source weight is the selected pullback weight, and
the raw floor-complement kernel is the selected pullback kernel.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hweight_eq :
      ∀ q : ℝ × ℝ,
        R.weight q = theorem31SelectedPullbackSourceWeight S.weight q)
    (hkernel_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels)
        (k : ℕ) (q : ℝ × ℝ),
        twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k =
          theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut S.hmono
            S.sampleRate levels hlevels k q) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization
    μ R S
    (fun levels hlevels _heq =>
      lemmaC4TieErasedSelectedIntegralRealization_theorem31_raw_floorPkComplementError_of_eq_pullback_source
        μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels
        R.successProb R.sampleRate R.hprob0 R.hprob1 R.weight S.weight
        hweight_eq (hkernel_eq levels hlevels))

/--
Source convention identifying a raw continuum source model with the selected
finite-level pullback convention used by Lemma C.4.  The kernel equality
includes the tie-erasure/off-selected-support convention: outside selected
cross-level cells, the selected pullback kernel is zero.
-/
structure LemmaC4RawSourceSelectedPullbackConvention
    (μ : Measure ℝ) [SFinite μ]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) : Prop where
  weight_eq :
    ∀ q : ℝ × ℝ,
      R.weight q = theorem31SelectedPullbackSourceWeight S.weight q
  kernel_eq :
    ∀ (levels : Fin (S.m + 2) → ℝ)
      (hlevels : BinaryEndpointLevelVector levels)
      (k : ℕ) (q : ℝ × ℝ),
      twoSampleFloorPkComplementErrorProb
          (binaryRatingModel R.successProb R.hprob0 R.hprob1)
          R.sampleRate q.1 q.2 k =
        theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut S.hmono
          S.sampleRate levels hlevels k q

/--
Lemma C.4 positive-support source model under the named selected-pullback
source convention.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : LemmaC4RawSourceSelectedPullbackConvention μ R S) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source
    μ R S H.weight_eq H.kernel_eq

/--
Lemma C.4 positive-support source model in the paper-local finite-step
convention.  This is the finite-step restatement of the finite-range iff above:
monotonicity turns finite range on the support interval into convex finite
level fibers, while the source-specific forward branch uses eventual equality
with the endpoint/cutpoint `theorem31SourceWbar` integral.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ R.weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                  R.sampleRate q.1 q.2 k)
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate := by
  have hiff :=
    lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq
      μ R S hsource_eq
  constructor
  · intro hstep
    exact hiff.mp hstep.1
  · intro hcert
    exact lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo R.hprob_mono
      (hiff.mpr hcert)

/--
Lemma C.4 positive-support source model in the paper-local finite-step
convention, with selected-source realization reduced to pointwise equality
with the canonical pullback source convention.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hweight_eq :
      ∀ q : ℝ × ℝ,
        R.weight q = theorem31SelectedPullbackSourceWeight S.weight q)
    (hkernel_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels)
        (k : ℕ) (q : ℝ × ℝ),
        twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k =
          theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut S.hmono
            S.sampleRate levels hlevels k q) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate := by
  have hiff :=
    lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source
      μ R S hweight_eq hkernel_eq
  constructor
  · intro hstep
    exact hiff.mp hstep.1
  · intro hcert
    exact lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo R.hprob_mono
      (hiff.mpr hcert)

/--
Lemma C.4 finite-step positive-support source model under the named
selected-pullback source convention.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : LemmaC4RawSourceSelectedPullbackConvention μ R S) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source
    μ R S H.weight_eq H.kernel_eq

/--
Lemma C.4 positive-support source model in the paper-local finite-step
convention, with the finite-level forward branch realized by the structured
selected-support source interface.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hrealization :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          LemmaC4TieErasedSelectedIntegralRealization μ R.weight S.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)
            (theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels)
            theorem31SelectedSourceCoordinateMap
            (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate := by
  have hiff :=
    lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization
      μ R S hrealization
  constructor
  · intro hstep
    exact hiff.mp hstep.1
  · intro hcert
    exact lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo R.hprob_mono
      (hiff.mpr hcert)

/--
Lemma C.4 source-kernel form of the finite-step iff.  The forward direction
uses the selected finite-level realization of the paper's `\bar P_k` kernel,
while the reverse direction uses the paper-level continuity-point obstruction
for bounded source kernels.  This is the C.4 bridge matching the source proof:
`W-W_k` is represented by a source `\bar P_k` kernel, not by a raw
all-strict-pairs complement kernel that would retain same-bin/tie terms.
-/
theorem lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (sourcePbarKernel : ℕ → ℝ × ℝ → ℝ) {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hsource_kernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (sourcePbarKernel k)
          ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_kernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet,
          0 ≤ sourcePbarKernel k q ∧ sourcePbarKernel k q ≤ K)
    (hcert :
      UniformNormalizedLogRateCertificateOn sourcePbarKernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (R.sampleRate q.1) (R.sampleRate q.2)
            (R.successProb q.1) (R.successProb q.2))
        AppliedModelingLib.strictUpperPairSet)
    (hrealization :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          LemmaC4TieErasedSelectedIntegralRealization μ R.weight S.weight
            sourcePbarKernel
            (theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels)
            theorem31SelectedSourceCoordinateMap
            (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight sourcePbarKernel) rate := by
  refine
    lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_prob_interval_of_measurableKernel
      μ R.hlohi
      (fun f lo hi => lemmaC4FiniteStepOnIoo f lo hi)
      R.successProb R.sampleRate R.hprob_mono R.weight sourcePbarKernel
      (lemmaC4TieErasedSourceWbar μ R.weight sourcePbarKernel) hK_nonneg
      R.hsource_weight_int R.hsource_weight_nonneg hsource_kernel_meas
      hsource_kernel_bound hcert
      (lemmaC4TieErasedSourceWbar_eventually_eq μ R.weight sourcePbarKernel)
      ?_ R.hweight_cont R.hsample_cont ?_ R.hweight_pos_on
      R.hsample_pos_on
  · intro _hfiniteStep
    exact
      lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization
        μ S R.weight sourcePbarKernel hrealization
  · intro _hnot_step
    exact ⟨R.lo, R.hi, le_rfl, R.hlohi, le_rfl, R.hprob_interior_on⟩

/--
Lemma C.4 global monotone reverse consequence in no-positive-rate form.  Under
the finite-level forward source realization, a source rule that is not finite
range on the positive-support interval cannot have any positive exponential
rate certificate for the tie-erased `Wbar_k` convention.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : LemmaC4RawSourcePositiveSupportIntervalModel μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ R.weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                  R.sampleRate q.1 q.2 k)
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate := by
  have hiff :=
    lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq
      μ R S hsource_eq
  intro rate hrate hcert
  exact hnot_finite (hiff.mpr ⟨rate, hrate, hcert⟩)

/--
Lemma C.4 no-positive-rate reverse branch from explicit positive-support
source fields.  This is the field-level version of
`lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate`: it
builds the local source model record from the displayed regularity,
positivity, and non-finite-range hypotheses.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi)
    (hsource_eq :
      ∀ (levels : Fin (S.m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
          lemmaC4TieErasedSourceWbar μ weight
              (fun k : ℕ => fun q : ℝ × ℝ =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1)
                  sampleRate q.1 q.2 k)
            =ᶠ[atTop]
          theorem31SourceWbar μ S.cut S.hmono S.sampleRate levels hlevels
            S.weight) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate := by
  let R : LemmaC4RawSourcePositiveSupportIntervalModel μ :=
    { lo := lo
      hi := hi
      hlohi := hlohi
      successProb := successProb
      sampleRate := sampleRate
      hprob_mono := hprob_mono
      hprob0 := hprob0
      hprob1 := hprob1
      hprob_meas := hprob_meas
      hsample_meas := hsample_meas
      weight := weight
      hsource_weight_int := hsource_weight_int
      hsource_weight_nonneg := hsource_weight_nonneg
      hweight_cont := hweight_cont
      hweight_diag_cont := hweight_diag_cont
      hsample_cont := hsample_cont
      hweight_pos_on := hweight_pos_on
      hsample_pos_on := hsample_pos_on
      hprob_interior_on := hprob_interior_on }
  simpa [R] using
    (lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate
      μ R S hnot_finite hsource_eq)

/--
Lemma C.4 no-positive-rate reverse branch from explicit positive-support
fields for the concrete tie-erased raw floor-complement source convention.
This reverse-only theorem removes the finite-level forward model and
`theorem31SourceWbar` equality premises from the no-positive-rate conclusion.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate := by
  let R : LemmaC4RawSourcePositiveSupportIntervalModel μ :=
    { lo := lo
      hi := hi
      hlohi := hlohi
      successProb := successProb
      sampleRate := sampleRate
      hprob_mono := hprob_mono
      hprob0 := hprob0
      hprob1 := hprob1
      hprob_meas := hprob_meas
      hsample_meas := hsample_meas
      weight := weight
      hsource_weight_int := hsource_weight_int
      hsource_weight_nonneg := hsource_weight_nonneg
      hweight_cont := hweight_cont
      hweight_diag_cont := hweight_diag_cont
      hsample_cont := hsample_cont
      hweight_pos_on := hweight_pos_on
      hsample_pos_on := hsample_pos_on
      hprob_interior_on := hprob_interior_on }
  simpa [R] using
    (lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRange_raw_floorPkComplementError
      μ R hnot_finite)

/--
Lemma C.4 exact-zero-rate reverse branch from explicit positive-support
fields for the concrete tie-erased raw floor-complement source convention.
This is the field-level exact-rate version of the finite-range reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 := by
  let R : LemmaC4RawSourcePositiveSupportIntervalModel μ :=
    { lo := lo
      hi := hi
      hlohi := hlohi
      successProb := successProb
      sampleRate := sampleRate
      hprob_mono := hprob_mono
      hprob0 := hprob0
      hprob1 := hprob1
      hprob_meas := hprob_meas
      hsample_meas := hsample_meas
      weight := weight
      hsource_weight_int := hsource_weight_int
      hsource_weight_nonneg := hsource_weight_nonneg
      hweight_cont := hweight_cont
      hweight_diag_cont := hweight_diag_cont
      hsample_cont := hsample_cont
      hweight_pos_on := hweight_pos_on
      hsample_pos_on := hsample_pos_on
      hprob_interior_on := hprob_interior_on }
  simpa [R] using
    (lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_has_zero_rate_of_not_finiteRange_raw_floorPkComplementError
      μ R hnot_finite)

/--
Lemma C.4 finite-step reverse branch from explicit positive-support fields.
For monotone source rules, finite range implies the finite-step/order-convex
fiber convention, so a non-finite-step source rule has exact zero rate under
the concrete tie-erased raw floor-complement `Wbar_k`.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 := by
  have hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi := by
    intro hfinite
    exact hnot_finiteStep
      (lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo hprob_mono hfinite)
  exact
    lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
      μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight hsource_weight_int hsource_weight_nonneg
      hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
      hsample_pos_on hprob_interior_on hnot_finite

/--
No-positive-rate form of the finite-step positive-support C.4 reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k))
      (lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
        μ hlohi successProb sampleRate hprob_mono hprob0 hprob1
        hprob_meas hsample_meas weight hsource_weight_int
        hsource_weight_nonneg hweight_cont hweight_diag_cont hsample_cont
        hweight_pos_on hsample_pos_on hprob_interior_on hnot_finiteStep)

/--
Lemma C.4 exact-zero-rate reverse branch from non-finite range, using the
primitive one-dimensional positive-mass convention for the `θ` distribution.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 :=
  lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on hnot_finite

/--
No-positive-rate companion to the one-dimensional positive-mass non-finite
range reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate :=
  lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on hnot_finite

/--
Constant-weight, uniform-sampling specialization of the one-dimensional
positive-mass Lemma C.4 reverse branch from non-finite range.  This removes
the integrability, nonnegativity, continuity, and positivity fields that are
automatic for the source normalization `w ≡ 1` and `g ≡ 1`.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) 0 := by
  simpa using
    lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)
      hprob_interior_on hnot_finite

/--
No-positive-rate companion to the constant-weight, uniform-sampling
one-dimensional positive-mass Lemma C.4 reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finite : ¬ lemmaC4FiniteRangeOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k))
      (lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
        μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
        hprob_interior_on hnot_finite)

/--
Lemma C.4 exact-zero-rate reverse branch from non-finite-stepness, using the
primitive one-dimensional positive-mass convention for the `θ` distribution.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 :=
  lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on hnot_finiteStep

/--
No-positive-rate companion to the one-dimensional positive-mass
non-finite-step reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate :=
  lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on hnot_finiteStep

/--
Constant-weight, uniform-sampling specialization of the one-dimensional
positive-mass Lemma C.4 reverse branch from non-finite-stepness.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) 0 := by
  simpa using
    lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)
      hprob_interior_on hnot_finiteStep

/--
No-positive-rate companion to the constant-weight, uniform-sampling
one-dimensional positive-mass non-finite-step reverse branch.
-/
theorem lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (hnot_finiteStep : ¬ lemmaC4FiniteStepOnIoo successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k))
      (lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
        μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
        hprob_interior_on hnot_finiteStep)

/--
Lemma C.4 no-positive-rate reverse branch from explicit positive-support
fields and the paper's non-piecewise source predicate.  This is the
field-level non-piecewise form: finite-range source rules are first routed
through the source's piecewise-constant convention, then the raw floor
tie-erased `Wbar_k` reverse theorem rules out positive rates.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate := by
  rcases
      lemmaC4_exists_positiveSupportIntervalModel_and_not_finiteRange_of_nonpiecewise_monotone_beta
        μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight hsource_weight_int hsource_weight_nonneg
        hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
        hsample_pos_on hprob_interior_on isPiecewiseConstantOn
        hfinite_to_piecewise hnot_piecewise with
    ⟨R, rfl, rfl, rfl, rfl, rfl, hnot_finite⟩
  exact
    lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRange_raw_floorPkComplementError
      μ R hnot_finite

/--
Lemma C.4 exact-zero-rate reverse branch from explicit positive-support
fields and the paper's non-piecewise source predicate.  This is the exact-rate
companion to the no-positive-rate source bridge above.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 := by
  rcases
      lemmaC4_exists_positiveSupportIntervalModel_and_not_finiteRange_of_nonpiecewise_monotone_beta
        μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight hsource_weight_int hsource_weight_nonneg
        hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
        hsample_pos_on hprob_interior_on isPiecewiseConstantOn
        hfinite_to_piecewise hnot_piecewise with
    ⟨R, rfl, rfl, rfl, rfl, rfl, hnot_finite⟩
  exact
    lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_has_zero_rate_of_not_finiteRange_raw_floorPkComplementError
      μ R hnot_finite

/--
Lemma C.4 exact-zero-rate reverse branch with the paper's primitive
one-dimensional positive-mass convention.  Instead of assuming open-positive
mass directly for the product distribution, this wrapper assumes the
one-dimensional `θ` distribution charges every nonempty open interval; mathlib
then supplies the corresponding product open-positive measure instance.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            sampleRate q.1 q.2 k)) 0 :=
  lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on isPiecewiseConstantOn
    hfinite_to_piecewise hnot_piecewise

/--
No-positive-rate companion to
`lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError`.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    (hsource_weight_int :
      Integrable weight ((μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet))
    (hsource_weight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet, 0 ≤ weight q)
    (hweight_cont : ∀ θ : ℝ, ContinuousAt weight (θ, θ))
    (hweight_diag_cont :
      ∀ θ : ℝ, ContinuousAt (fun x : ℝ => weight (x, x)) θ)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hweight_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < weight (θ, θ))
    (hsample_pos_on : ∀ θ ∈ Set.Ioo lo hi, 0 < sampleRate θ)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k)) rate :=
  lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError
    μ hlohi successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
    hsample_meas weight hsource_weight_int hsource_weight_nonneg
    hweight_cont hweight_diag_cont hsample_cont hweight_pos_on
    hsample_pos_on hprob_interior_on isPiecewiseConstantOn
    hfinite_to_piecewise hnot_piecewise

/--
Constant-weight, uniform-sampling specialization of the one-dimensional
positive-mass Lemma C.4 reverse branch from the paper's non-piecewise source
predicate.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) 0 := by
  simpa using
    lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError
      μ hlohi successProb (fun _ : ℝ => (1 : ℝ)) hprob_mono
      hprob0 hprob1 hprob_meas measurable_const
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        simpa using
          (integrable_const (μ :=
            (μ.prod μ).restrict AppliedModelingLib.strictUpperPairSet)
            (c := (1 : ℝ))))
      (by
        filter_upwards with q
        norm_num)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ
        simpa using
          (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousAt)
      (by
        intro θ hθ
        norm_num)
      (by
        intro θ hθ
        norm_num)
      hprob_interior_on isPiecewiseConstantOn hfinite_to_piecewise
      hnot_piecewise

/--
No-positive-rate companion to the constant-weight, uniform-sampling
one-dimensional positive-mass non-piecewise C.4 reverse branch.
-/
theorem lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {lo hi : ℝ} (hlohi : lo < hi)
    (successProb : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hprob_interior_on :
      ∀ θ ∈ Set.Ioo lo hi, 0 < successProb θ ∧ successProb θ < 1)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo successProb lo hi →
        isPiecewiseConstantOn successProb lo hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn successProb lo hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k)) rate := by
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ (fun _ : ℝ × ℝ => (1 : ℝ))
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1)
            (fun _ : ℝ => (1 : ℝ)) q.1 q.2 k))
      (lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError
        μ hlohi successProb hprob_mono hprob0 hprob1 hprob_meas
        hprob_interior_on isPiecewiseConstantOn hfinite_to_piecewise
        hnot_piecewise)

/--
Lemma C.4 global-error bridge from a local monotone-interval obstruction.  If
the local strict ordered-pair floor-complement integral supplied by the
monotone-continuity argument is an eventually positive minorant of the source's
global `W - W_k` error sequence, and the global error is eventually bounded by
a fixed constant, then the global error has exact exponential rate zero.

This records the reusable reverse-direction interface: derive the minorant
relation from a global `W - W_k` error sequence and the chosen
non-piecewise-continuity interval.
-/
theorem lemmaC4_global_floorPkComplementError_has_zero_rate_of_monotone_interval_minorant
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (globalError : ℕ → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (hlocal_pos :
      ∀ᶠ k : ℕ in atTop,
        0 <
          ∫ q,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k
            ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
    (hlocal_le_global :
      ∀ᶠ k : ℕ in atTop,
        (∫ q,
            weight q *
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k
            ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) ≤
          globalError k)
    (hglobal_upper_const : ∀ᶠ k : ℕ in atTop, globalError k ≤ B) :
    HasExponentialRate globalError 0 := by
  let localError : ℕ → ℝ := fun k =>
    ∫ q,
      weight q *
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          q.1 q.2 k
      ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)
  have hlocal_zero : HasExponentialRate localError 0 := by
    simpa [localError] using
      lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc
        μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
        hsample_meas weight hweight_int hweight_nonneg hweight_cont
        hweight_x0_pos hab hsample_pos_on hprob_pos_on hprob_lt_one_on
        hsample_cont_on
  exact
    hasExponentialRate_zero_of_eventually_le_const_of_zero_rate_minorant
      hBpos (by simpa [localError] using hlocal_pos) hlocal_zero
      (by simpa [localError] using hlocal_le_global) hglobal_upper_const

/--
Lemma C.4 source-shaped iff packaging for the concrete floor-complement error
on a compact quality interval.  The forward piecewise-constant side remains the
paper's positive-rate construction, while the reverse side is derived here from
monotone success probabilities, interval positivity, and pointwise binary
Cramer certificates supplied by the shared LDP library.
-/
theorem lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_monotone_interval_floorPkComplementError
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (isPiecewiseConstant : Prop)
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hforward :
      isPiecewiseConstant →
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (fun k : ℕ =>
              ∫ q,
                weight q *
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb hprob0 hprob1)
                    sampleRate q.1 q.2 k
                ∂(μ.prod μ).restrict
                  (AppliedModelingLib.strictUpperPairSetOn a b))
            rate) :
    isPiecewiseConstant ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (fun k : ℕ =>
            ∫ q,
              weight q *
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel successProb hprob0 hprob1)
                  sampleRate q.1 q.2 k
              ∂(μ.prod μ).restrict
                (AppliedModelingLib.strictUpperPairSetOn a b))
          rate := by
  refine
    lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse
      isPiecewiseConstant
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k
          ∂(μ.prod μ).restrict
            (AppliedModelingLib.strictUpperPairSetOn a b))
      hforward ?_
  intro _hnot_piecewise
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hab hsample_pos_on hprob_pos_on hprob_lt_one_on
      hsample_cont_on

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete source
floor-complement kernel on a compact quality interval.  The binary LDP library
builds the left-tail Cramer certificates on the closed upper triangle, and the
finite-rating sandwich transfers them to the `1 - P_k` kernel.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G L : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let certSet := AppliedModelingLib.closedUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorScoreGapLeftTailProb M sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel, M] using hkernel_meas k)
      hkernel_bound
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using AppliedModelingLib.isCompact_closedUpperPairSetOn a b
  have hprob_order :
      ∀ q : ℝ × ℝ, q ∈ certSet → successProb q.2 ≤ successProb q.1 := by
    intro q hq
    have hqset : q ∈ AppliedModelingLib.closedUpperPairSetOn a b := by
      simpa [certSet] using hq
    have hqord : q ∈ AppliedModelingLib.closedUpperPairSet := hqset.1
    exact hprob_mono (by simpa [AppliedModelingLib.closedUpperPairSet] using hqord)
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q _hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hsample_cont q.1) (hsample_cont q.2)
        (hprob_cont q.1) (hprob_cont q.2)
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, M, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_eventually_lipschitz_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q _hq => hsample_pos q.1)
        (fun q _hq => hsample_pos q.2)
        (fun q _hq => hprob_pos q.1)
        (fun q _hq => hprob_lt_one q.1)
        (fun q _hq => hprob_pos q.2)
        (fun q _hq => hprob_lt_one q.2)
        hprob_order
        (by simpa [phi] using hrate_cont)
        hL
        (by simpa [leftKernel, certSet, M, binaryRatingModel] using
          hleft_tail_log_lipschitz)
  have hcert_uniform_exp :
      UniformExponentialRateCertificateOn kernel phi certSet := by
    simpa [kernel, leftKernel, phi, certSet, M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel (a := a) (b := b) (θ0 := θ0)
      (G := G) (K := (2 : ℝ)) hθ0 (by norm_num)
      (by simpa [cell, kernel, M] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel, M] using hkernel_bound)
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos
      hg_le hcert_uniform_exp.toUniformNormalizedLogRateCertificateOn

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete source
floor-complement kernel from local asymptotic equicontinuity on the closed
upper triangle.  This weakens the global Lipschitz regularity premise in the
neighboring theorem while keeping the binary Cramer and `1 - P_k` transfer
steps derived from the shared library.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_locally_equicontinuous_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let certSet := AppliedModelingLib.closedUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorScoreGapLeftTailProb M sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel, M] using hkernel_meas k)
      hkernel_bound
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using AppliedModelingLib.isCompact_closedUpperPairSetOn a b
  have hprob_order :
      ∀ q : ℝ × ℝ, q ∈ certSet → successProb q.2 ≤ successProb q.1 := by
    intro q hq
    have hqset : q ∈ AppliedModelingLib.closedUpperPairSetOn a b := by
      simpa [certSet] using hq
    have hqord : q ∈ AppliedModelingLib.closedUpperPairSet := hqset.1
    exact hprob_mono (by simpa [AppliedModelingLib.closedUpperPairSet] using hqord)
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q _hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos q.1) (hsample_pos q.2)
        (hprob_pos q.1) (hprob_lt_one q.1)
        (hprob_pos q.2) (hprob_lt_one q.2)
        (hsample_cont q.1) (hsample_cont q.2)
        (hprob_cont q.1) (hprob_cont q.2)
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, M, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_locally_equicontinuous_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q _hq => hsample_pos q.1)
        (fun q _hq => hsample_pos q.2)
        (fun q _hq => hprob_pos q.1)
        (fun q _hq => hprob_lt_one q.1)
        (fun q _hq => hprob_pos q.2)
        (fun q _hq => hprob_lt_one q.2)
        hprob_order
        (by simpa [phi] using hrate_cont)
        (by simpa [leftKernel, certSet, M, binaryRatingModel] using
          hleft_tail_log_local)
  have hcert_uniform_exp :
      UniformExponentialRateCertificateOn kernel phi certSet := by
    simpa [kernel, leftKernel, phi, certSet, M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel (a := a) (b := b) (θ0 := θ0)
      (G := G) (K := (2 : ℝ)) hθ0 (by norm_num)
      (by simpa [cell, kernel, M] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel, M] using hkernel_bound)
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos
      hg_le hcert_uniform_exp.toUniformNormalizedLogRateCertificateOn

/--
Lemma C.4 bounded strict ordered-pair bridge from local left-tail
equicontinuity on the closed upper triangle, with kernel measurability
discharged from global continuity of the success-probability and sample-rate
functions.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_locally_equicontinuous_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hprob_meas : Measurable successProb :=
    (continuous_iff_continuousAt.2 hprob_cont).measurable
  have hsample_meas : Measurable sampleRate :=
    (continuous_iff_continuousAt.2 hsample_cont).measurable
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_locally_equicontinuous_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G)
      hθ0 hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
      hleft_tail_log_local

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete
floor-complement kernel on a nonempty compact quality interval.  Monotonicity
of `β` supplies an interior continuity point, and the remaining analytic input
is local left-tail equicontinuity on the closed upper triangle.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_locally_equicontinuous_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0)
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_locally_equicontinuous_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G)
      hθ0 hkernel_meas hweight_int hweight_nonneg
      (hweight_cont θ0 hθ0) (hweight_x0_pos θ0 hθ0)
      hβ_cont (hprob_pos θ0) (hprob_lt_one θ0) (hsample_pos θ0)
      hG_pos (Eventually.of_forall hsample_pos) hg_le hsample_pos
      hprob_pos hprob_lt_one hsample_cont hprob_cont hleft_tail_log_local

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from local
left-tail equicontinuity on the closed upper triangle, with kernel
measurability discharged from global continuity.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_locally_equicontinuous_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hprob_meas : Measurable successProb :=
    (continuous_iff_continuousAt.2 hprob_cont).measurable
  have hsample_meas : Measurable sampleRate :=
    (continuous_iff_continuousAt.2 hsample_cont).measurable
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_locally_equicontinuous_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b)
      hkernel_meas hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hab hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont
      hleft_tail_log_local

/--
Lemma C.4 bounded strict ordered-pair bridge from local left-tail
equicontinuity, with all source regularity required only on the compact
quality interval `[a,b]`.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_locally_equicontinuous_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hprob_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let certSet := AppliedModelingLib.closedUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorScoreGapLeftTailProb M sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hθ0_Icc : θ0 ∈ Set.Icc a b := ⟨hθ0.1.le, hθ0.2.le⟩
  have hβ_cont : ContinuousAt successProb θ0 :=
    hprob_cont_on θ0 hθ0_Icc
  have hβ0 : 0 < successProb θ0 :=
    hprob_pos_on θ0 hθ0_Icc
  have hβ1 : successProb θ0 < 1 :=
    hprob_lt_one_on θ0 hθ0_Icc
  have hg0 : 0 < sampleRate θ0 :=
    hsample_pos_on θ0 hθ0_Icc
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont_on θ0 hθ0_Icc)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont_on θ0 hθ0_Icc).eventually
      (isOpen_Ioi.mem_nhds hg0)
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k)
          ((μ.prod μ).restrict cell) := by
    intro k
    simpa [M, cell, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict cell)
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel] using hkernel_meas k)
      hkernel_bound
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using AppliedModelingLib.isCompact_closedUpperPairSetOn a b
  have hprob_order :
      ∀ q : ℝ × ℝ, q ∈ certSet → successProb q.2 ≤ successProb q.1 := by
    intro q hq
    exact hprob_mono (AppliedModelingLib.closedUpperPairSetOn_snd_le_fst hq)
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q hq
    have hq1 : q.1 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq
    have hq2 : q.2 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos_on q.1 hq1) (hsample_pos_on q.2 hq2)
        (hprob_pos_on q.1 hq1) (hprob_lt_one_on q.1 hq1)
        (hprob_pos_on q.2 hq2) (hprob_lt_one_on q.2 hq2)
        (hsample_cont_on q.1 hq1) (hsample_cont_on q.2 hq2)
        (hprob_cont_on q.1 hq1) (hprob_cont_on q.2 hq2)
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, M, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_locally_equicontinuous_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q hq => hsample_pos_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hsample_pos_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        (fun q hq => hprob_pos_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hprob_lt_one_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hprob_pos_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        (fun q hq => hprob_lt_one_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        hprob_order
        (by simpa [phi, certSet] using hrate_cont)
        (by simpa [leftKernel, certSet, M, binaryRatingModel] using
          hleft_tail_log_local)
  have hcert_uniform_exp :
      UniformExponentialRateCertificateOn kernel phi certSet := by
    simpa [kernel, leftKernel, phi, certSet, M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel (a := a) (b := b) (θ0 := θ0)
      (G := G) (K := (2 : ℝ)) hθ0 (by norm_num)
      (by simpa [cell, kernel] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel] using hkernel_bound)
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos
      hg_le hcert_uniform_exp.toUniformNormalizedLogRateCertificateOn

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from local
left-tail equicontinuity, with all source regularity localized to `[a,b]`.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_locally_equicontinuous_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hprob_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt successProb θ)
    (hleft_tail_log_local :
      ∀ q : ℝ × ℝ,
        q ∈ AppliedModelingLib.closedUpperPairSetOn a b → ∀ ε > 0,
          ∃ U : Set (ℝ × ℝ),
            IsOpen U ∧ q ∈ U ∧
              ∀ᶠ k : ℕ in atTop,
                ∀ r : ℝ × ℝ,
                  r ∈ AppliedModelingLib.closedUpperPairSetOn a b → r ∈ U →
                    |normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k r -
                      normalizedLogKernelRate
                        (fun k q =>
                          twoSampleFloorScoreGapLeftTailProb
                            (binaryRatingModel successProb hprob0 hprob1)
                            sampleRate q.1 q.2 k)
                        k q| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    exact ⟨hprob_pos_on θ hθ_Icc, hprob_lt_one_on θ hθ_Icc⟩
  obtain ⟨θ0, hθ0, _hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_locally_equicontinuous_on_closed_upper_box_of_Icc
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight (a := a) (b := b) (θ0 := θ0)
      hθ0 hweight_int hweight_nonneg (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hsample_pos_on hprob_pos_on
      hprob_lt_one_on hsample_cont_on hprob_cont_on hleft_tail_log_local

/--
Lemma C.4 bounded strict ordered-pair bridge from left-tail Lipschitz
regularity on the closed upper triangle, with kernel measurability discharged
from global continuity of the success-probability and sample-rate functions.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G L : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hprob_meas : Measurable successProb :=
    (continuous_iff_continuousAt.2 hprob_cont).measurable
  have hsample_meas : Measurable sampleRate :=
    (continuous_iff_continuousAt.2 hsample_cont).measurable
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G) (L := L)
      hθ0 hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont hL
      hleft_tail_log_lipschitz

/--
Lemma C.4 bounded strict ordered-pair bridge from left-tail Lipschitz
regularity on the closed upper triangle, with source regularity required only
on the compact quality interval `[a,b]`.  This is the local form needed for
continuity-point arguments inside a bounded non-piecewise interval.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 L : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hprob_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let certSet := AppliedModelingLib.closedUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let leftKernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorScoreGapLeftTailProb M sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hθ0_Icc : θ0 ∈ Set.Icc a b := ⟨hθ0.1.le, hθ0.2.le⟩
  have hβ_cont : ContinuousAt successProb θ0 :=
    hprob_cont_on θ0 hθ0_Icc
  have hβ0 : 0 < successProb θ0 :=
    hprob_pos_on θ0 hθ0_Icc
  have hβ1 : successProb θ0 < 1 :=
    hprob_lt_one_on θ0 hθ0_Icc
  have hg0 : 0 < sampleRate θ0 :=
    hsample_pos_on θ0 hθ0_Icc
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont_on θ0 hθ0_Icc)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont_on θ0 hθ0_Icc).eventually
      (isOpen_Ioi.mem_nhds hg0)
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k)
          ((μ.prod μ).restrict cell) := by
    intro k
    simpa [M, cell, binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict cell)
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel] using hkernel_meas k)
      hkernel_bound
  have hcertSet_compact : IsCompact certSet := by
    simpa [certSet] using AppliedModelingLib.isCompact_closedUpperPairSetOn a b
  have hprob_order :
      ∀ q : ℝ × ℝ, q ∈ certSet → successProb q.2 ≤ successProb q.1 := by
    intro q hq
    exact hprob_mono (AppliedModelingLib.closedUpperPairSetOn_snd_le_fst hq)
  have hrate_cont :
      ∀ q : ℝ × ℝ, q ∈ certSet → ContinuousAt phi q := by
    intro q hq
    have hq1 : q.1 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq
    have hq2 : q.2 ∈ Set.Icc a b :=
      AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq
    simpa [phi] using
      lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt
        successProb sampleRate q
        (hsample_pos_on q.1 hq1) (hsample_pos_on q.2 hq2)
        (hprob_pos_on q.1 hq1) (hprob_lt_one_on q.1 hq1)
        (hprob_pos_on q.2 hq2) (hprob_lt_one_on q.2 hq2)
        (hsample_cont_on q.1 hq1) (hsample_cont_on q.2 hq2)
        (hprob_cont_on q.1 hq1) (hprob_cont_on q.2 hq2)
  have hcert_left_tail :
      UniformExponentialRateCertificateOn leftKernel phi certSet := by
    simpa [leftKernel, phi, certSet, M, binaryRatingModel] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_eventually_lipschitz_on_compact
        successProb hprob0 hprob1 sampleRate
        (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcertSet_compact (fun _ hq => hq)
        (fun q hq => hsample_pos_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hsample_pos_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        (fun q hq => hprob_pos_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hprob_lt_one_on q.1
          (AppliedModelingLib.closedUpperPairSetOn_fst_mem_Icc hq))
        (fun q hq => hprob_pos_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        (fun q hq => hprob_lt_one_on q.2
          (AppliedModelingLib.closedUpperPairSetOn_snd_mem_Icc hq))
        hprob_order
        (by simpa [phi, certSet] using hrate_cont)
        hL
        (by simpa [leftKernel, certSet, M, binaryRatingModel] using
          hleft_tail_log_lipschitz)
  have hcert_uniform_exp :
      UniformExponentialRateCertificateOn kernel phi certSet := by
    simpa [kernel, leftKernel, phi, certSet, M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel (a := a) (b := b) (θ0 := θ0)
      (G := G) (K := (2 : ℝ)) hθ0 (by norm_num)
      (by simpa [cell, kernel] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel] using hkernel_bound)
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos
      hg_le hcert_uniform_exp.toUniformNormalizedLogRateCertificateOn

/--
Lemma C.4 bounded strict ordered-pair bridge from a left-tail uniform
exponential certificate on the closed upper triangle.  This separates the
finite-rating `Pk` sandwich from the analytic work needed to build the
left-tail certificate.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  let cell := AppliedModelingLib.strictUpperPairSetOn a b
  let certSet := AppliedModelingLib.closedUpperPairSetOn a b
  let M := binaryRatingModel successProb hprob0 hprob1
  let kernel : ℕ → ℝ × ℝ → ℝ :=
    fun k q => twoSampleFloorPkComplementErrorProb M sampleRate q.1 q.2 k
  let phi : ℝ × ℝ → ℝ := fun q =>
    weightedBernoulliClosedThresholdRate
      (sampleRate q.1) (sampleRate q.2)
      (successProb q.1) (successProb q.2)
  have hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict cell,
          0 ≤ kernel k q ∧ kernel k q ≤ (2 : ℝ) := by
    intro k
    filter_upwards with q
    exact
      ⟨twoSampleFloorPkComplementErrorProb_nonneg
          M sampleRate q.1 q.2 k,
        twoSampleFloorPkComplementErrorProb_le_two
          M sampleRate q.1 q.2 k⟩
  have hkernel_int :
      ∀ k : ℕ,
        Integrable
          (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict cell) :=
    integrable_weight_mul_kernel_of_integrable_weight_of_ae_kernel_between_zero_const
      ((μ.prod μ).restrict cell) (K := (2 : ℝ))
      (by simpa [cell] using hweight_int)
      (by
        intro k
        simpa [cell, kernel, M] using hkernel_meas k)
      hkernel_bound
  have hcert_uniform_exp :
      UniformExponentialRateCertificateOn kernel phi certSet := by
    simpa [kernel, phi, certSet, M] using
      twoSampleFloorPkComplementError_uniformExponentialRateCertificateOn_of_leftTail
        M sampleRate (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
        hcert_left_tail
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box
      μ successProb sampleRate weight kernel (a := a) (b := b) (θ0 := θ0)
      (G := G) (K := (2 : ℝ)) hθ0 (by norm_num)
      (by simpa [cell, kernel, M] using hkernel_int)
      (by simpa [cell] using hweight_int)
      (by simpa [cell] using hweight_nonneg)
      (by simpa [cell, kernel, M] using hkernel_bound)
      hweight_cont hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos
      hg_le hcert_uniform_exp.toUniformNormalizedLogRateCertificateOn

/--
Lemma C.4 bounded strict ordered-pair bridge from a left-tail uniform
exponential certificate on the closed upper triangle, with kernel
measurability discharged from measurable success-probability and sample-rate
functions.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b θ0 G : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo a b)
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont : ContinuousAt weight (θ0, θ0))
    (hweight_x0_pos : 0 < weight (θ0, θ0))
    (hβ_cont : ContinuousAt successProb θ0)
    (hβ0 : 0 < successProb θ0)
    (hβ1 : successProb θ0 < 1)
    (hg0 : 0 < sampleRate θ0)
    (hG_pos : 0 < G)
    (hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ)
    (hg_le : ∀ᶠ θ in 𝓝 θ0, sampleRate θ ≤ G)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G)
      hθ0 hkernel_meas hweight_int hweight_nonneg hweight_cont
      hweight_x0_pos hβ_cont hβ0 hβ1 hg0 hG_pos hg_pos hg_le
      hcert_left_tail

/--
Lemma C.4 bounded strict ordered-pair bridge for the concrete
floor-complement kernel on a nonempty compact quality interval.  Monotonicity
of `β` supplies an interior continuity point, so the remaining source-shaped
analytic inputs are kernel measurability and left-tail normalized-log
Lipschitz regularity on the closed upper triangle.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b L : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0)
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G) (L := L)
      hθ0 hkernel_meas hweight_int hweight_nonneg
      (hweight_cont θ0 hθ0) (hweight_x0_pos θ0 hθ0)
      hβ_cont (hprob_pos θ0) (hprob_lt_one θ0) (hsample_pos θ0)
      hG_pos (Eventually.of_forall hsample_pos) hg_le hsample_pos
      hprob_pos hprob_lt_one hsample_cont hprob_cont hL
      hleft_tail_log_lipschitz

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from left-tail
Lipschitz regularity on the closed upper triangle, with kernel measurability
discharged from global continuity of the success-probability and sample-rate
functions.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b L : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos : ∀ θ : ℝ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ : ℝ, successProb θ < 1)
    (hsample_cont : ∀ θ : ℝ, ContinuousAt sampleRate θ)
    (hprob_cont : ∀ θ : ℝ, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hprob_meas : Measurable successProb :=
    (continuous_iff_continuousAt.2 hprob_cont).measurable
  have hsample_meas : Measurable sampleRate :=
    (continuous_iff_continuousAt.2 hsample_cont).measurable
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b) (L := L)
      hkernel_meas hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hab hsample_pos hprob_pos hprob_lt_one hsample_cont hprob_cont hL
      hleft_tail_log_lipschitz

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from left-tail
Lipschitz regularity on the closed upper triangle, with all source
positivity/continuity hypotheses localized to `[a,b]`.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b L : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos_on : ∀ θ ∈ Set.Icc a b, 0 < sampleRate θ)
    (hprob_pos_on : ∀ θ ∈ Set.Icc a b, 0 < successProb θ)
    (hprob_lt_one_on : ∀ θ ∈ Set.Icc a b, successProb θ < 1)
    (hsample_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt sampleRate θ)
    (hprob_cont_on : ∀ θ ∈ Set.Icc a b, ContinuousAt successProb θ)
    (hL : 0 < L)
    (hleft_tail_log_lipschitz :
      ∀ᶠ k : ℕ in atTop,
        ∀ q : ℝ × ℝ,
          q ∈ AppliedModelingLib.closedUpperPairSetOn a b →
            ∀ r : ℝ × ℝ,
              r ∈ AppliedModelingLib.closedUpperPairSetOn a b →
                |normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k r -
                  normalizedLogKernelRate
                    (fun k q =>
                      twoSampleFloorScoreGapLeftTailProb
                        (binaryRatingModel successProb hprob0 hprob1)
                        sampleRate q.1 q.2 k)
                    k q| ≤ L * dist r q) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    exact ⟨hprob_pos_on θ hθ_Icc, hprob_lt_one_on θ hθ_Icc⟩
  obtain ⟨θ0, hθ0, _hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc
      μ successProb sampleRate hprob_mono hprob0 hprob1 hprob_meas
      hsample_meas weight (a := a) (b := b) (θ0 := θ0) (L := L)
      hθ0 hweight_int hweight_nonneg (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hsample_pos_on hprob_pos_on
      hprob_lt_one_on hsample_cont_on hprob_cont_on hL
      hleft_tail_log_lipschitz

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from a
left-tail uniform exponential certificate on the closed upper triangle.
Monotonicity supplies the diagonal continuity point; the caller supplies the
left-tail certificate.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ)
    (hprob_lt_one :
      ∀ θ ∈ Set.Ioo a b, successProb θ < 1)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    exact ⟨hprob_pos θ hθ, hprob_lt_one θ hθ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G)
      hθ0 hkernel_meas hweight_int hweight_nonneg
      (hweight_cont θ0 hθ0) (hweight_x0_pos θ0 hθ0)
      hβ_cont (hprob_pos θ0 hθ0) (hprob_lt_one θ0 hθ0)
      (hsample_pos θ0) hG_pos (Eventually.of_forall hsample_pos) hg_le
      hcert_left_tail

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from a
left-tail uniform exponential certificate on the closed upper triangle, with
kernel measurability discharged from measurable success-probability and
sample-rate functions.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ : ℝ, 0 < sampleRate θ)
    (hprob_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ)
    (hprob_lt_one :
      ∀ θ ∈ Set.Ioo a b, successProb θ < 1)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate hprob_mono hprob0 hprob1 weight
      (a := a) (b := b)
      hkernel_meas hweight_int hweight_nonneg hweight_cont hweight_x0_pos
      hab hsample_pos hprob_pos hprob_lt_one hsample_cont hcert_left_tail

/--
Lemma C.4 bounded strict ordered-pair monotone-interval bridge from a
left-tail uniform exponential certificate, with sample-rate positivity needed
only on the interior interval where the continuity point is chosen.
-/
theorem lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box_of_Ioo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (hprob_mono : Monotone successProb)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (weight : ℝ × ℝ → ℝ)
    {a b : ℝ}
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hsample_pos : ∀ θ ∈ Set.Ioo a b, 0 < sampleRate θ)
    (hprob_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ)
    (hprob_lt_one :
      ∀ θ ∈ Set.Ioo a b, successProb θ < 1)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert_left_tail :
      UniformExponentialRateCertificateOn
        (fun k q =>
          twoSampleFloorScoreGapLeftTailProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        (fun q =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedUpperPairSetOn a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q,
          weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k
          ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hkernel_meas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)) := by
    intro k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
        successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    exact ⟨hprob_pos θ hθ, hprob_lt_one θ hθ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont θ0 hθ0).eventually
      (isOpen_Ioi.mem_nhds (hsample_pos θ0 hθ0))
  exact
    lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box
      μ successProb sampleRate hprob0 hprob1 weight
      (a := a) (b := b) (θ0 := θ0) (G := G)
      hθ0 hkernel_meas hweight_int hweight_nonneg
      (hweight_cont θ0 hθ0) (hweight_x0_pos θ0 hθ0)
      hβ_cont (hprob_pos θ0 hθ0) (hprob_lt_one θ0 hθ0)
      (hsample_pos θ0 hθ0) hG_pos hg_pos hg_le hcert_left_tail

/--
Lemma C.4 bounded strict ordered-pair bridge on a nonempty quality interval.
A monotone success-probability curve supplies an interior continuity point, so
the compact-box certificate on `[a,b]²` is enough to obtain zero exponential
rate for the bounded strict-pair integral.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (hsample_pos : ∀ θ, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedPairBox a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ _hθ
    exact ⟨hprob_pos θ, hprob_lt_one θ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box
      μ successProb sampleRate weight kernel hθ0 hK_nonneg hkernel_int
      hweight_int hweight_nonneg hkernel_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont (hprob_pos θ0)
      (hprob_lt_one θ0) (hsample_pos θ0) hG_pos
      (Eventually.of_forall hsample_pos) hg_le hcert

/--
Lemma C.4 bounded strict ordered-pair bridge on a nonempty quality interval,
with probability and sample-rate positivity required only on the interval
where the monotone continuity point is chosen.
-/
theorem lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box_of_Ioo
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (successProb sampleRate : ℝ → ℝ)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    {a b K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun q : ℝ × ℝ => weight q * kernel k q)
          ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_int :
      Integrable weight
        ((μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b)))
    (hweight_nonneg :
      ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
        0 ≤ weight q)
    (hkernel_bound :
      ∀ k : ℕ,
        ∀ᵐ q ∂(μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b),
          0 ≤ kernel k q ∧ kernel k q ≤ K)
    (hweight_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt weight (θ, θ))
    (hweight_x0_pos :
      ∀ θ ∈ Set.Ioo a b, 0 < weight (θ, θ))
    (hab : a < b)
    (hprob_mono : Monotone successProb)
    (hprob_pos : ∀ θ ∈ Set.Ioo a b, 0 < successProb θ)
    (hprob_lt_one : ∀ θ ∈ Set.Ioo a b, successProb θ < 1)
    (hsample_pos : ∀ θ ∈ Set.Ioo a b, 0 < sampleRate θ)
    (hsample_cont :
      ∀ θ ∈ Set.Ioo a b, ContinuousAt sampleRate θ)
    (hcert :
      UniformNormalizedLogRateCertificateOn kernel
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (sampleRate q.1) (sampleRate q.2)
            (successProb q.1) (successProb q.2))
        (AppliedModelingLib.closedPairBox a b)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ q, weight q * kernel k q ∂
          (μ.prod μ).restrict (AppliedModelingLib.strictUpperPairSetOn a b))
      0 := by
  have hrange :
      ∀ θ ∈ Set.Ioo a b, 0 < successProb θ ∧ successProb θ < 1 := by
    intro θ hθ
    exact ⟨hprob_pos θ hθ, hprob_lt_one θ hθ⟩
  obtain ⟨θ0, hθ0, hβ_cont, _hβ0, _hβ1⟩ :=
    AppliedModelingLib.exists_interior_continuity_point_of_monotone_on_Ioo
      (f := successProb) hab hprob_mono hrange
  obtain ⟨G, hG_pos, hg_le⟩ :=
    AppliedModelingLib.exists_pos_eventually_le_of_continuousAt
      (hsample_cont θ0 hθ0)
  have hg_pos : ∀ᶠ θ in 𝓝 θ0, 0 < sampleRate θ :=
    (hsample_cont θ0 hθ0).eventually
      (isOpen_Ioi.mem_nhds (hsample_pos θ0 hθ0))
  exact
    lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box
      μ successProb sampleRate weight kernel hθ0 hK_nonneg hkernel_int
      hweight_int hweight_nonneg hkernel_bound (hweight_cont θ0 hθ0)
      (hweight_x0_pos θ0 hθ0) hβ_cont (hprob_pos θ0 hθ0)
      (hprob_lt_one θ0 hθ0) (hsample_pos θ0 hθ0) hG_pos
      hg_pos hg_le hcert

/--
Lemma C.3 ordered-rectangle positive-kernel adjacent-dominance bridge with
continuous minimizers.  For the paper's selected ordered quality rectangles,
component minimizers that lie in their rectangles automatically lie in the
closure of the rectangle interiors; hence the source-style Laplace support
condition follows from the ordered partition topology.
-/
theorem lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    {Adjacent : Type*}
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ → ℝ)
    (rate W c : {piece : Fin n × Fin n // selected piece} → ℝ)
    (selectAdjacent :
      Adjacent → {piece : Fin n × Fin n // selected piece})
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hWpos :
      ∀ component, 0 < W component)
    (hcpos :
      ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          weight x ≤ W component)
    (x0 : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component →
          rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          weight x * kernel k x ∂(μ.prod μ))
      (rate (selectAdjacent minAdjacent)) :=
  lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower
    (μ.prod μ)
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected)
    weight kernel phi rate W c selectAdjacent hkernel_int hweight_int hWpos
    hcpos hweight_lower hweight_bound x0 hmin hx0 hcont
    (fun component =>
      theorem31_ordered_quality_pair_piece_mem_closure_interior
        μ n cut hmono selected component (hx0_mem component))
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 ordered-rectangle positive-kernel adjacent-dominance bridge with
continuous minimizers and locally positive objective weights.  For selected
ordered quality rectangles, minimizers inside the rectangles automatically
satisfy the closure/interior support condition required by the Laplace step.
-/
theorem lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_weight_pos
    {Adjacent : Type*}
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ → ℝ)
    (rate W : {piece : Fin n × Fin n // selected piece} → ℝ)
    (selectAdjacent :
      Adjacent → {piece : Fin n × Fin n // selected piece})
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hWpos :
      ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          weight x ≤ W component)
    (x0 : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component →
          rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          weight x * kernel k x ∂(μ.prod μ))
      (rate (selectAdjacent minAdjacent)) :=
  lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_weight_pos
    (μ.prod μ)
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected)
    weight kernel phi rate W selectAdjacent hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound x0 hmin hx0 hphi_cont hweight_cont
    hweight_x0_pos
    (fun component =>
      theorem31_ordered_quality_pair_piece_mem_closure_interior
        μ n cut hmono selected component (hx0_mem component))
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge.  For the paper's
nontrivial ordered level-pair rectangles, the adjacent-dominance hypothesis in
the generic C.3 bridge is discharged by the finite endpoint-aware chain
dominance theorem.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
      (Adjacent := Fin (m + 1))
      μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
      weight kernel phi rate W c selectAdjacent hkernel_int hweight_int hWpos
      hcpos hweight_lower hweight_bound x0 hx0_mem
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont hkernel_pos huniform_log minAdjacent hadj_min_pair
      hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with locally positive
objective weights.  This discharges the adjacent-dominance hypothesis as in the
uniform-lower-bound version, but only requires the weight to be continuous and
positive at the component minimizers.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_weight_pos
      (Adjacent := Fin (m + 1))
      μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
      weight kernel phi rate W selectAdjacent hkernel_int hweight_int hWpos
      hweight_nonneg hweight_bound x0 hx0_mem
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hphi_cont hweight_cont hweight_x0_pos hkernel_pos huniform_log
      minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge for kernels that are
exactly exponential on each selected rectangle.  This removes the uniform-log
rate hypothesis from the corresponding positive-kernel bridge.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exact_exp_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phi component x))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_exact_exp_on_cells
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hkernel_eq
      hweight_int hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge for source-shaped
Laplace kernels.  On each selected rectangle the kernel is a.e.
`exp (-k * phiSeq_component,k x)`, and the component rate functions converge
uniformly to continuous limiting rates whose minima are the endpoint-aware
pair rates.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      theorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniform_tendsto_on_cells
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phiSeq phi rate W c selectAdjacent hkernel_int hkernel_eq
      hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge for source-shaped
Laplace kernels with eventual a.e. equality on each selected rectangle.  This
matches the source convention `phi_k = -log kernel_k / k`, where the identity
with `exp (-k * phi_k)` is only relevant for positive sample sizes.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      theorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * phiSeq component k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ component,
        ∀ᶠ k : ℕ in atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniform_tendsto_on_cells_eventually
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phiSeq phi rate W c selectAdjacent hkernel_int
      hlaplace_int hkernel_eq hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with the paper's
normalized-log convention.  If the pairwise error kernel is eventually
positive a.e. on each selected rectangle and
`-log kernel_k / k` converges uniformly on cells to continuous limiting rates,
then the ordered-rectangle integral has the adjacent-minimum exponent.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x *
              Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ component,
        ∀ᶠ k : ℕ in atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_normalizedLogRate_tendsto_on_cells_eventually
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hlaplace_int
      hkernel_pos hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with the paper's
normalized-log convention and all-index a.e. positivity.  The positivity
hypothesis identifies the normalized-log Laplace integrand with the original
pairwise error kernel for every positive sample size, so callers only provide
integrability of the original kernel and of the bounded weight.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_normalizedLogRate_tendsto_on_cells
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hweight_int
      hkernel_pos hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with local positive
objective weights.  This removes the artificial cellwise positive lower-bound
assumption from the source-facing normalized-log version: the weight is only
required to be nonnegative on each rectangle and positive at the minimizing
point.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_normalizedLogRate_tendsto_on_cells_weight_pos
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W selectAdjacent hkernel_int hweight_int
      hkernel_pos hWpos hweight_nonneg hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hphi_cont hweight_cont hweight_x0_pos
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with the paper's
normalized-log convention and piece-local uniform convergence.  This matches
the source Remark C.1 use more closely than the global-uniform wrapper: the
normalized log rate only has to converge uniformly on each selected rectangle.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_pieces_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            x ∈
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
              |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_normalizedLogRate_tendsto_on_pieces
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hweight_int
      hkernel_pos hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      huniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with compact-local
normalized-log convergence.  For each selected rectangle, it is enough to
prove local uniform convergence on a compact superset; compactness supplies
the finite subcover needed for the piece-local uniform hypothesis.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (K : theorem31OrderedNontrivialPairComponent m → Set (ℝ × ℝ))
    (hKcompact : ∀ component, IsCompact (K component))
    (hpiece_subset :
      ∀ component,
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component ⊆
            K component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_uniform :
      ∀ component, ∀ x : ℝ × ℝ, x ∈ K component → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ y : ℝ × ℝ, y ∈ K component → y ∈ U →
                |normalizedLogKernelRate kernel k y - phi component y| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_normalizedLogRate_tendsto_of_locally_on_compact_supersets
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent K hKcompact hpiece_subset
      hkernel_int hweight_int hkernel_pos hWpos hcpos hweight_lower
      hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      hlocal_uniform minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge with compact-local
normalized-log convergence, with endpoint support and monotonicity supplied by
`BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (K : theorem31OrderedNontrivialPairComponent m → Set (ℝ × ℝ))
    (hKcompact : ∀ component, IsCompact (K component))
    (hpiece_subset :
      ∀ component,
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component ⊆
            K component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_uniform :
      ∀ component, ∀ x : ℝ × ℝ, x ∈ K component → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ y : ℝ × ℝ, y ∈ K component → y ∈ U →
                |normalizedLogKernelRate kernel k y - phi component y| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c K hKcompact hpiece_subset hkernel_int hweight_int
    hkernel_pos hWpos hcpos hweight_lower hweight_bound x0 hx0_mem hmin
    hx0 hcont hlocal_uniform minAdjacent hadj_min

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from componentwise
constant-factor exponential sandwiches.  This is the natural target for
Bernoulli Chernoff/type estimates: upper and lower envelopes for each selected
rectangle imply the normalized-log convergence required by the Laplace step.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c lowerConst upperConst :
      theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hlowerConst_pos : ∀ component, 0 < lowerConst component)
    (hupperConst_pos : ∀ component, 0 < upperConst component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlower :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            lowerConst component *
                Real.exp (-(k : ℝ) * (phi component x + ε)) ≤
              kernel k x)
    (hupper :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            kernel k x ≤
              upperConst component *
                Real.exp (-(k : ℝ) * (phi component x - ε)))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_exp_sandwich_const_on_pieces
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c lowerConst upperConst selectAdjacent
      hkernel_int hweight_int hkernel_pos hWpos hcpos hlowerConst_pos
      hupperConst_pos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      hlower hupper minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from componentwise
constant-factor exponential sandwiches, with endpoint support and monotonicity
supplied by `BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c lowerConst upperConst :
      theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hlowerConst_pos : ∀ component, 0 < lowerConst component)
    (hupperConst_pos : ∀ component, 0 < upperConst component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlower :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            lowerConst component *
                Real.exp (-(k : ℝ) * (phi component x + ε)) ≤
              kernel k x)
    (hupper :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            kernel k x ≤
              upperConst component *
                Real.exp (-(k : ℝ) * (phi component x - ε)))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c lowerConst upperConst hkernel_int hweight_int
    hkernel_pos hWpos hcpos hlowerConst_pos hupperConst_pos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont hlower hupper minAdjacent
    hadj_min

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
exponential-rate certificates on the selected rectangles.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  exact
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
      hprob_mono hprob_nonneg hprob_pos_of_not_first
      hprob_lt_one_of_not_last weight kernel phi W c
      (fun component => (hcert component).lowerConst)
      (fun component => (hcert component).upperConst)
      hkernel_int hweight_int hkernel_pos hWpos hcpos
      (fun component => (hcert component).lowerConst_pos)
      (fun component => (hcert component).upperConst_pos)
      hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont
      (fun component => (hcert component).lower)
      (fun component => (hcert component).upper)
      minAdjacent hadj_min

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
exponential-rate certificates, with endpoint support and monotonicity supplied
by `BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert minAdjacent
    hadj_min

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
exponential-rate certificates, using the eventual-positive normalized-log
Laplace path.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniformExponentialRateCertificate_on_pieces_eventually
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hlaplace_int
      hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      hcert minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
exponential-rate certificates, with endpoint support and monotonicity supplied
by `BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hlaplace_int hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert
    minAdjacent hadj_min

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
normalized-log rate certificates on the selected rectangles.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformNormalizedLogRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) →
      theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hadj_min_pair :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hadj_dominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1),
          rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    FiniteMeasurableSetPartition.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniformNormalizedLogRateCertificate_on_pieces_eventually
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m)))
      weight kernel phi rate W c selectAdjacent hkernel_int hlaplace_int
      hWpos hcpos hweight_lower hweight_bound x0
      (by
        intro component x hx
        simpa [rate] using hmin component x hx)
      (by
        intro component
        simpa [rate] using hx0 component)
      hcont
      (fun component =>
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          component (hx0_mem component))
      hcert minAdjacent hadj_min_pair hadj_dominates
  simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Endpoint-aware Theorem 3.1/C.3 ordered-rectangle bridge from uniform
normalized-log rate certificates, with endpoint support and monotonicity
provided by `BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformNormalizedLogRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hlaplace_int hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert
    minAdjacent hadj_min

/--
Lemma C.4 forward direction in the source-shaped continuum setting: the
ordered-rectangle C.3 rate formula, together with a positive minimum adjacent
rate, gives a positive exponential convergence rate for the piecewise-constant
objective.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniform_tendsto_on_cells
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      theorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phiSeq phi W c hkernel_int hkernel_eq hWpos hcpos
      hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont huniform
      minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction with the paper's normalized-log convention:
eventual positivity of the pairwise error kernel and uniform convergence of
`-log kernel_k / k` on cells give a positive exponential rate whenever the
minimum adjacent exponent is positive.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x *
              Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ component,
        ∀ᶠ k : ℕ in atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W c hkernel_int hlaplace_int hkernel_pos hWpos hcpos
      hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont huniform
      minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction with the paper's normalized-log convention and
all-index a.e. positivity of the error kernel.  This is the source-facing
version once the pairwise Bernoulli kernel is known to be positive and its
normalized log rate converges uniformly on the ordered rectangles.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos
      hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont huniform
      minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction with all-index a.e. positive kernels and local
positive objective weights.  This is the source-facing C.4 endpoint after the
C.3 Laplace bridge has been stated with minimizer-local weight positivity
instead of a uniform lower bound on every selected rectangle.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_weight_pos
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W hkernel_int hweight_int hkernel_pos hWpos
      hweight_nonneg hweight_bound x0 hx0_mem hmin hx0 hphi_cont
      hweight_cont hweight_x0_pos huniform minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction with the paper's normalized-log convention and
piece-local uniform convergence of the error-kernel rate on each ordered
rectangle.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_pieces_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : ℝ × ℝ,
            x ∈
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
              |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_pieces_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos
      hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont huniform
      minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction with compact-local normalized-log convergence on
compact supersets of the selected ordered rectangles.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_of_locally_on_compact_supersets_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (K : theorem31OrderedNontrivialPairComponent m → Set (ℝ × ℝ))
    (hKcompact : ∀ component, IsCompact (K component))
    (hpiece_subset :
      ∀ component,
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component ⊆
            K component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_uniform :
      ∀ component, ∀ x : ℝ × ℝ, x ∈ K component → ∀ ε > 0,
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ y : ℝ × ℝ, y ∈ K component → y ∈ U →
                |normalizedLogKernelRate kernel k y - phi component y| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W c K hKcompact hpiece_subset hkernel_int hweight_int
      hkernel_pos hWpos hcpos hweight_lower hweight_bound x0 hx0_mem hmin
      hx0 hcont hlocal_uniform minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction from componentwise constant-factor exponential
sandwiches for the selected ordered rectangles.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_exp_sandwich_const_on_pieces_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c lowerConst upperConst :
      theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hlowerConst_pos : ∀ component, 0 < lowerConst component)
    (hupperConst_pos : ∀ component, 0 < upperConst component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlower :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            lowerConst component *
                Real.exp (-(k : ℝ) * (phi component x + ε)) ≤
              kernel k x)
    (hupper :
      ∀ component, ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
        ∀ x : ℝ × ℝ,
          x ∈
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
            kernel k x ≤
              upperConst component *
                Real.exp (-(k : ℝ) * (phi component x - ε)))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
      hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight
      kernel phi W c lowerConst upperConst hkernel_int hweight_int
      hkernel_pos hWpos hcpos hlowerConst_pos hupperConst_pos hweight_lower
      hweight_bound x0 hx0_mem hmin hx0 hcont hlower hupper minAdjacent
      hadj_min⟩

/--
Lemma C.4 forward direction from uniform exponential-rate certificates on the
selected ordered rectangles.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
      hprob_mono hprob_nonneg hprob_pos_of_not_first
      hprob_lt_one_of_not_last weight kernel phi W c hkernel_int hweight_int
      hkernel_pos hWpos hcpos hweight_lower hweight_bound x0 hx0_mem hmin
      hx0 hcont hcert minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction from uniform exponential-rate certificates, using
the eventual-positive normalized-log Laplace path.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
      hprob_mono hprob_nonneg hprob_pos_of_not_first
      hprob_lt_one_of_not_last weight kernel phi W c hkernel_int
      hlaplace_int hWpos hcpos hweight_lower hweight_bound x0 hx0_mem hmin
      hx0 hcont hcert minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction from uniform normalized-log rate certificates on
the selected ordered rectangles.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_all_positive
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformNormalizedLogRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent, hmin_pos,
    lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower
      μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
      hprob_mono hprob_nonneg hprob_pos_of_not_first
      hprob_lt_one_of_not_last weight kernel phi W c hkernel_int
      hlaplace_int hWpos hcpos hweight_lower hweight_bound x0 hx0_mem hmin
      hx0 hcont hcert minAdjacent hadj_min⟩

/--
Lemma C.4 forward direction from uniform normalized-log rate certificates on
the selected ordered rectangles, with the endpoint support and monotonicity
facts supplied by the paper's endpoint-level-vector convention.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformNormalizedLogRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_all_positive
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hlaplace_int hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert
    minAdjacent hadj_min hmin_pos

/--
Lemma C.4 forward direction from uniform exponential-rate certificates on the
selected ordered rectangles, with endpoint support and monotonicity supplied by
the paper's endpoint-level-vector convention.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_all_positive
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert
    minAdjacent hadj_min hmin_pos

/--
Lemma C.4 forward direction from uniform exponential-rate certificates, using
the eventual-positive normalized-log Laplace path, with endpoint support and
monotonicity supplied by the paper's endpoint-level-vector convention.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : theorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hcert :
      ∀ component,
        UniformExponentialRateCertificateOn kernel (phi component)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_all_positive
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight kernel phi W c hkernel_int hlaplace_int hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont hcert
    minAdjacent hadj_min hmin_pos

/--
Lemma C.4 forward-direction certificate: if the finite component decomposition
has a positive adjacent minimum exponent, then the decomposed objective has
some positive exponential rate.
-/
theorem lemmaC4_positive_rate_of_dominating_adjacent_subfamily_positive_min
    {Component Adjacent : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minAdjacent : Adjacent)
    (hweight_pos : 0 < weight (selectAdjacent minAdjacent))
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ cpt : Component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate cpt)
    (hmin_pos : 0 < rate (selectAdjacent minAdjacent)) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∑ cpt : Component, weight cpt * componentError cpt k)
        c :=
  ⟨rate (selectAdjacent minAdjacent), hmin_pos,
    lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_dominating_adjacent_subfamily
      componentError weight rate selectAdjacent hweight_nonneg hcert
      minAdjacent hweight_pos hadj_min hadj_dominates⟩

/--
Finite aggregation bridge for the finite-discretized objective after adjacent
or cross-interval pairwise LDP certificates have been supplied.
-/
theorem finiteBinaryRankingError_hasExpUpperBound_of_rate_certificates
    {ι : Type*} [Fintype ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst (C.aggregateError weight) targetRate :=
  C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight hrate

/--
Finite binary `1 - W_k` aggregation bridge in the source objective form. Once
each comparison pair has a support-safe threshold-rate LDP certificate, the
weighted finite ranking error has any exponential upper bound below all
pairwise rates.
-/
theorem finiteBinaryRankingObjective_oneSub_hasExpUpperBound_of_pairwise_rate_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (C : PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo)
    {weight : Pair → ℝ} {targetRate : ℝ}
    (hweight : ∀ p : Pair, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (hrate : ∀ p : Pair, targetRate < C.rate p) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      targetRate :=
  one_sub_finiteFloorPkObjective_hasExpUpperBoundWithConst_of_pairwiseThresholdRateTopLdpCertificate
    M sampleRate pairHi pairLo C hweight hweight_sum hrate

/--
Uniform finite binary `1 - W_k` aggregation bridge for a finite comparison
family.
-/
theorem finiteBinaryRankingObjective_oneSub_hasExpUpperBound_of_uniform_pairwise_rate_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (C : PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo)
    {targetRate : ℝ}
    (hrate : ∀ p : Pair, targetRate < C.rate p) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      targetRate :=
  one_sub_finiteUniformFloorPkObjective_hasExpUpperBoundWithConst_of_pairwiseThresholdRateTopLdpCertificate
    M sampleRate pairHi pairLo C hrate

/--
Finite binary `1 - W_k` exact-rate bridge from an explicit finite family of
pairwise `1 - P_k` error-rate certificates. This is the aggregation surface
for mixed endpoint/interior adjacent-pair proofs.
-/
theorem finiteBinaryRankingObjective_oneSub_hasExponentialRate_of_error_rate_certificate_min
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (E : FiniteErrorRateCertificate Pair)
    (herror :
      ∀ p : Pair,
        E.errorProb p =
          twoSampleFloorPkComplementErrorProb M sampleRate (pairHi p) (pairLo p))
    {weight : Pair → ℝ}
    (hweight_nonneg : ∀ p : Pair, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (pMin : Pair)
    (hweight_pos : 0 < weight pMin)
    (hrate_ge : ∀ p : Pair, E.rate pMin ≤ E.rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (E.rate pMin) :=
  one_sub_finiteFloorPkObjective_hasExponentialRate_of_finiteErrorRateCertificate_min_component
    M sampleRate pairHi pairLo E herror
    hweight_nonneg hweight_sum pMin hweight_pos hrate_ge

/--
Uniform finite binary `1 - W_k` exact-rate bridge from an explicit finite
family of pairwise error-rate certificates.
-/
theorem finiteBinaryRankingObjective_oneSub_hasExponentialRate_of_uniform_error_rate_certificate_min
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (E : FiniteErrorRateCertificate Pair)
    (herror :
      ∀ p : Pair,
        E.errorProb p =
          twoSampleFloorPkComplementErrorProb M sampleRate (pairHi p) (pairLo p))
    (pMin : Pair)
    (hrate_ge : ∀ p : Pair, E.rate pMin ≤ E.rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (E.rate pMin) :=
  one_sub_finiteUniformFloorPkObjective_hasExponentialRate_of_finiteErrorRateCertificate_min_component
    M sampleRate pairHi pairLo E herror pMin hrate_ge

/--
Adjacent-interval specialization for the source finite binary level chain:
pairwise threshold-rate certificates on adjacent intervals give an exponential
upper bound for the uniform finite adjacent objective error.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_pairwise_rate_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (C :
      PairwiseThresholdRateTopLdpCertificate M sampleRate
        (fun i : Fin (m + 1) => adjacentHighIndex i)
        (fun i : Fin (m + 1) => adjacentLowIndex i))
    {targetRate : ℝ}
    (hrate : ∀ i : Fin (m + 1), targetRate < C.rate i) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate :=
  finiteBinaryRankingObjective_oneSub_hasExpUpperBound_of_uniform_pairwise_rate_certificates
    M sampleRate
    (fun i : Fin (m + 1) => adjacentHighIndex i)
    (fun i : Fin (m + 1) => adjacentLowIndex i)
    C hrate

/--
Adjacent-interval exact-rate bridge from explicit pairwise `1 - P_k`
error-rate certificates. This is the finite aggregation surface for combining
endpoint and interior adjacent-pair LDP proofs.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_error_rate_certificate_min
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (E : FiniteErrorRateCertificate (Fin (m + 1)))
    (herror :
      ∀ i : Fin (m + 1),
        E.errorProb i =
          twoSampleFloorPkComplementErrorProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), E.rate iMin ≤ E.rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (E.rate iMin) :=
  finiteBinaryRankingObjective_oneSub_hasExponentialRate_of_uniform_error_rate_certificate_min
    M sampleRate
    (fun i : Fin (m + 1) => adjacentHighIndex i)
    (fun i : Fin (m + 1) => adjacentLowIndex i)
    E herror iMin hrate_ge

/--
Adjacent-interval exact-rate bridge directly from pairwise nonpositive
score-gap left-tail certificates.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (rate : Fin (m + 1) → ℝ)
    (leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), rate iMin ≤ rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (rate iMin) :=
  one_sub_finiteUniformFloorPkObjective_hasExponentialRate_of_leftTail_certificates_min_component
    M sampleRate
    (fun i : Fin (m + 1) => adjacentHighIndex i)
    (fun i : Fin (m + 1) => adjacentLowIndex i)
    rate leftTail iMin hrate_ge

/--
Weighted adjacent-interval exact-rate bridge directly from pairwise
nonpositive score-gap left-tail certificates.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (rate : Fin (m + 1) → ℝ)
    (leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (hrate_ge : ∀ i : Fin (m + 1), rate iMin ≤ rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (rate iMin) :=
  one_sub_finiteFloorPkObjective_hasExponentialRate_of_leftTail_certificates_min_component
    M sampleRate
    (fun i : Fin (m + 1) => adjacentHighIndex i)
    (fun i : Fin (m + 1) => adjacentLowIndex i)
    rate leftTail hweight_nonneg hweight_sum iMin hweight_pos hrate_ge

/--
Pairwise left-tail certificates for endpoint-aware adjacent binary chains.
This factors the finite Theorem 3.1 proof surface into the reusable pairwise
certificate part and the finite weighted aggregation part.
-/
theorem binaryEndpointAwareAdjacentRate_leftTail_certificates
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i)) :
    ∀ i : Fin (m + 1),
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i))
        (binaryEndpointAwareAdjacentRate successProb sampleRate i) := by
  intro i
  let M := binaryRatingModel successProb hprob0 hprob1
  let rate : Fin (m + 1) → ℝ :=
    binaryEndpointAwareAdjacentRate successProb sampleRate
  by_cases hfirst : i.val = 0
  · have hlow_first :
        adjacentLowIndex i = (firstLevelIndex : Fin (m + 2)) := by
      ext
      simp [adjacentLowIndex, hfirst]
    have hhi_not_first : (adjacentHighIndex i).val ≠ 0 := by
      have hval : (adjacentHighIndex i).val = 1 := by
        simp [adjacentHighIndex, hfirst]
      omega
    have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
      have hval : (adjacentHighIndex i).val = 1 := by
        simp [adjacentHighIndex, hfirst]
      omega
    have hpLo_zero : successProb (adjacentLowIndex i) = 0 := by
      simpa [hlow_first] using hfirst_zero
    have hcert :=
      binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_low_success_zero
        successProb hprob0 hprob1 sampleRate
        (adjacentHighIndex i) (adjacentLowIndex i)
        (hpositive_hi i)
        (hprob_pos_of_not_first (adjacentHighIndex i) hhi_not_first)
        (hprob_lt_one_of_not_last (adjacentHighIndex i) hhi_not_last)
        hpLo_zero
    simpa [M, rate, binaryEndpointAwareAdjacentRate, hfirst] using hcert
  · by_cases hlast : i.val = m
    · have hhigh_last :
          adjacentHighIndex i = (lastLevelIndex : Fin (m + 2)) := by
        ext
        simp [adjacentHighIndex, hlast]
      have hlo_not_first : (adjacentLowIndex i).val ≠ 0 := by
        have hval : (adjacentLowIndex i).val = m := by
          simp [adjacentLowIndex, hlast]
        omega
      have hlo_not_last : (adjacentLowIndex i).val ≠ m + 1 := by
        have hval : (adjacentLowIndex i).val = m := by
          simp [adjacentLowIndex, hlast]
        omega
      have hpHi_one : successProb (adjacentHighIndex i) = 1 := by
        simpa [hhigh_last] using hlast_one
      have hcert :=
        binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_high_success_one
          successProb hprob0 hprob1 sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i)
          (hpositive_hi i) (hpositive_lo i) hpHi_one
          (hprob_pos_of_not_first (adjacentLowIndex i) hlo_not_first)
          (hprob_lt_one_of_not_last (adjacentLowIndex i) hlo_not_last)
      have hm_ne : m ≠ 0 := Nat.ne_of_gt hm
      simpa [M, rate, binaryEndpointAwareAdjacentRate, hfirst, hlast, hm_ne] using hcert
    · have hlo_not_first : (adjacentLowIndex i).val ≠ 0 := by
        simpa [adjacentLowIndex] using hfirst
      have hlo_not_last : (adjacentLowIndex i).val ≠ m + 1 := by
        have hval : (adjacentLowIndex i).val = i.val := by
          simp [adjacentLowIndex]
        have hi_lt : i.val < m + 1 := i.isLt
        omega
      have hhi_not_first : (adjacentHighIndex i).val ≠ 0 := by
        have hval : (adjacentHighIndex i).val = i.val + 1 := by
          simp [adjacentHighIndex]
        omega
      have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
        have hval : (adjacentHighIndex i).val = i.val + 1 := by
          simp [adjacentHighIndex]
        omega
      have hcert :=
        binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
          successProb hprob0 hprob1 sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i)
          (hpositive_hi i) (hpositive_lo i)
          (hprob_pos_of_not_first (adjacentHighIndex i) hhi_not_first)
          (hprob_lt_one_of_not_last (adjacentHighIndex i) hhi_not_last)
          (hprob_pos_of_not_first (adjacentLowIndex i) hlo_not_first)
          (hprob_lt_one_of_not_last (adjacentLowIndex i) hlo_not_last)
          (hordered i)
      simpa [M, rate, binaryEndpointAwareAdjacentRate, hfirst, hlast] using hcert

/--
Pairwise left-tail certificates for endpoint-normalized adjacent binary chains.
The endpoint-vector invariant supplies the endpoint values, interior support
conditions, and adjacent monotonicity required by the raw certificate theorem.
-/
theorem binaryEndpointAwareAdjacentRate_leftTail_certificates_of_endpointLevelVector
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∀ i : Fin (m + 1),
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb
          (binaryRatingModel successProb
            (BinaryEndpointLevelVector_nonneg hlevels)
            (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i))
        (binaryEndpointAwareAdjacentRate successProb sampleRate i) :=
  binaryEndpointAwareAdjacentRate_leftTail_certificates
    hm successProb
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    sampleRate hpositive_hi hpositive_lo
    (BinaryEndpointLevelVector_adjacent_ordered hlevels)

/--
Endpoint-aware adjacent finite binary level-chain exact-rate theorem for
weighted adjacent-pair objectives.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) := by
  let M := binaryRatingModel successProb hprob0 hprob1
  let rate : Fin (m + 1) → ℝ :=
    binaryEndpointAwareAdjacentRate successProb sampleRate
  have leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i) :=
    binaryEndpointAwareAdjacentRate_leftTail_certificates
      hm successProb hprob0 hprob1 hfirst_zero hlast_one
      hprob_pos_of_not_first hprob_lt_one_of_not_last sampleRate
      hpositive_hi hpositive_lo hordered
  simpa [M, rate] using
    finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
      M sampleRate rate leftTail hweight_nonneg hweight_sum iMin
      hweight_pos hrate_ge

/--
Endpoint-aware adjacent finite binary weighted-objective exact-rate theorem
with the boundary and interior support facts supplied by
`BinaryEndpointLevelVector`.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpointLevelVector_min
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    hm successProb
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    sampleRate hpositive_hi hpositive_lo
    (BinaryEndpointLevelVector_adjacent_ordered hlevels)
    hweight_nonneg hweight_sum iMin hweight_pos hrate_ge

/--
Endpoint-aware adjacent finite binary level-chain exact-rate theorem.  The
first comparison uses `t_0 = 0`, the last comparison uses `t_last = 1`, and
all middle comparisons use the closed weighted Bernoulli threshold rate.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) := by
  let M := binaryRatingModel successProb hprob0 hprob1
  let rate : Fin (m + 1) → ℝ :=
    binaryEndpointAwareAdjacentRate successProb sampleRate
  have leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i) :=
    binaryEndpointAwareAdjacentRate_leftTail_certificates
      hm successProb hprob0 hprob1 hfirst_zero hlast_one
      hprob_pos_of_not_first hprob_lt_one_of_not_last sampleRate
      hpositive_hi hpositive_lo hordered
  simpa [M, rate] using
    finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
      M sampleRate rate leftTail iMin hrate_ge

/--
Endpoint-aware adjacent finite binary uniform-objective exact-rate theorem
with the boundary and interior support facts supplied by
`BinaryEndpointLevelVector`.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpointLevelVector_min
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    hm successProb
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    sampleRate hpositive_hi hpositive_lo
    (BinaryEndpointLevelVector_adjacent_ordered hlevels)
    iMin hrate_ge

/--
Finite Theorem 3.1 exact-rate bridge for equalized endpoint level vectors.  If
the paper's endpoint-normalized binary levels equalize all adjacent rates, then
the finite adjacent uniform objective has exponential rate equal to that common
adjacent rate.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      r := by
  let iMin : Fin (m + 1) := firstAdjacentIndex
  have hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i := by
    intro i
    rw [heq iMin, heq i]
  have hcert :=
    finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
      hm successProb
      (BinaryEndpointLevelVector_nonneg hlevels)
      (BinaryEndpointLevelVector_le_one hlevels)
      hlevels.1 hlevels.2.1
      (BinaryEndpointLevelVector_pos_of_not_first hlevels)
      (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
      sampleRate hpositive_hi hpositive_lo
      (BinaryEndpointLevelVector_adjacent_ordered hlevels)
      iMin hrate_ge
  rw [heq iMin] at hcert
  simpa [iMin] using hcert

/--
Weighted finite Theorem 3.1 exact-rate bridge for equalized endpoint level
vectors.  If the paper's endpoint-normalized binary levels equalize all
adjacent rates, then every positive-weight adjacent objective has exponential
rate equal to that common adjacent rate.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      r := by
  have hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i := by
    intro i
    rw [heq iMin, heq i]
  have hcert :=
    finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
      hm successProb
      (BinaryEndpointLevelVector_nonneg hlevels)
      (BinaryEndpointLevelVector_le_one hlevels)
      hlevels.1 hlevels.2.1
      (BinaryEndpointLevelVector_pos_of_not_first hlevels)
      (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
      sampleRate hpositive_hi hpositive_lo
      (BinaryEndpointLevelVector_adjacent_ordered hlevels)
      hweight_nonneg hweight_sum iMin hweight_pos hrate_ge
  rw [heq iMin] at hcert
  exact hcert

/--
Finite exact-rate bridge from the source's pairwise equalization condition:
if an endpoint-normalized binary level vector equalizes all adjacent rates,
then the finite adjacent uniform objective has exponential rate equal to its
finite worst-adjacent rate.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (binaryEndpointAwareAdjacentRateObjective successProb sampleRate) := by
  rcases heq.exists_common_rate with ⟨r, hr⟩
  have hrate :=
    finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
      hm successProb sampleRate hlevels hpositive_hi hpositive_lo hr
  have hobj :
      binaryEndpointAwareAdjacentRateObjective successProb sampleRate = r :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      successProb sampleRate r hr
  rwa [hobj]

/--
Weighted finite exact-rate bridge from the source's pairwise equalization
condition: if an endpoint-normalized binary level vector equalizes all
adjacent rates, every positive-weight adjacent objective decays at the finite
worst-adjacent rate.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (binaryEndpointAwareAdjacentRateObjective successProb sampleRate) := by
  rcases heq.exists_common_rate with ⟨r, hr⟩
  have hrate :=
    finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
      hm successProb sampleRate hlevels hpositive_hi hpositive_lo
      hweight_nonneg hweight_sum iMin hweight_pos hr
  have hobj :
      binaryEndpointAwareAdjacentRateObjective successProb sampleRate = r :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      successProb sampleRate r hr
  rwa [hobj]

/--
Lemma C.4 forward direction for the finite endpoint-aware piecewise-constant
model: an equalized endpoint-normalized level vector gives a positive
exponential rate for every positive-weight adjacent objective.
-/
theorem lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          1 -
            finiteFloorPkObjective
              (binaryRatingModel successProb
                (BinaryEndpointLevelVector_nonneg hlevels)
                (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
              (fun i : Fin (m + 1) => adjacentHighIndex i)
              (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
        c := by
  rcases heq.exists_pos_common_rate hm hlevels hpositive_hi hpositive_lo with
    ⟨r, hrpos, hr⟩
  have hrate :=
    finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
      hm successProb sampleRate hlevels hpositive_hi hpositive_lo
      hweight_nonneg hweight_sum iMin hweight_pos heq
  have hobj :
      binaryEndpointAwareAdjacentRateObjective successProb sampleRate = r :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      successProb sampleRate r hr
  exact ⟨r, hrpos, by simpa [hobj] using hrate⟩

/--
Weighted finite Theorem 3.1 for chains with more than one interior level:
positive sample rates determine an endpoint-normalized equalized binary level
vector, and every positive-weight adjacent objective has exponential rate
equal to that vector's finite worst-adjacent rate.
-/
theorem finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_from_forward_clipped_levels
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              1 -
                finiteFloorPkObjective
                  (binaryRatingModel levels
                    (BinaryEndpointLevelVector_nonneg hlevels)
                    (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                  (fun i : Fin (m + 1) => adjacentHighIndex i)
                  (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentHigh sampleRate hsample_pos
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentLow sampleRate hsample_pos
  rcases
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, _huniq⟩
  refine ⟨levels, hlevels.1, hlevels.2, ?_⟩
  exact
    finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
      (show 0 < m by omega) levels sampleRate hlevels.1
      hsample_high hsample_low hweight_nonneg hweight_sum iMin
      hweight_pos hlevels.2

/--
Lemma C.4 finite forward direction with the finite equalized levels constructed
from positive endpoint sample rates.  This packages the source's forward
piecewise-constant implication as an existence theorem for the endpoint-aware
finite model.
-/
theorem lemmaC4_forward_clipped_endpoint_piecewise_constant_has_positive_exponential_rate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ∃ c : ℝ, 0 < c ∧
            HasExponentialRate
              (fun k : ℕ =>
                1 -
                  finiteFloorPkObjective
                    (binaryRatingModel levels
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    (fun i : Fin (m + 1) => adjacentHighIndex i)
                    (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
              c := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentHigh sampleRate hsample_pos
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentLow sampleRate hsample_pos
  rcases
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, _huniq⟩
  refine ⟨levels, hlevels.1, hlevels.2, ?_⟩
  exact
    lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate
      (show 0 < m by omega) levels sampleRate hlevels.1
      hsample_high hsample_low hweight_nonneg hweight_sum iMin
      hweight_pos hlevels.2

/--
Adjacent finite binary level-chain upper-bound theorem using the weighted
geometric common threshold. If every adjacent closed weighted rate dominates
`targetRate`, then the uniform finite adjacent objective error has that
exponential upper bound.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_weighted_common_threshold
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hG :
      ∀ i : Fin (m + 1),
        sampleRate (adjacentHighIndex i) +
            sampleRate (adjacentLowIndex i) ≠ 0)
    (ha_le_hi :
      ∀ i : Fin (m + 1),
        weightedBernoulliCommonThreshold
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) ≤
          successProb (adjacentHighIndex i))
    {targetRate : ℝ}
    (hrate :
      ∀ i : Fin (m + 1),
        targetRate <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate := by
  let M := binaryRatingModel successProb hprob0 hprob1
  let C :
      PairwiseThresholdRateTopLdpCertificate M sampleRate
        (fun i : Fin (m + 1) => adjacentHighIndex i)
        (fun i : Fin (m + 1) => adjacentLowIndex i) :=
    binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
      successProb hprob0 hprob1 hprob_pos hprob_lt_one
      sampleRate
      (fun i : Fin (m + 1) => adjacentHighIndex i)
      (fun i : Fin (m + 1) => adjacentLowIndex i)
      hpositive_hi hpositive_lo hG ha_le_hi
  refine
    finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_pairwise_rate_certificates
      M sampleRate C ?_
  intro i
  have hclosed :
      pairwiseSellerThresholdRateTop M sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i) =
        (weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i))
          (successProb (adjacentLowIndex i)) : WithTop ℝ) :=
    binaryRatingModel_pairwiseThresholdRateTop_eq_closed_weighted_rate
      successProb hprob0 hprob1 hprob_pos hprob_lt_one
      sampleRate (adjacentHighIndex i) (adjacentLowIndex i)
      (hpositive_hi i) (hpositive_lo i) (hG i)
  have hC := C.threshold_rate_top_eq i
  have hrate_eq :
      C.rate i =
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i))
          (successProb (adjacentLowIndex i)) := by
    exact WithTop.coe_eq_coe.mp (hC.symm.trans hclosed)
  simpa [hrate_eq] using hrate i

/--
Adjacent finite binary level-chain upper-bound theorem from ordered adjacent
success probabilities. This derives the weighted-threshold order condition
needed by the LDP certificate.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_ordered_weighted_common_threshold
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    {targetRate : ℝ}
    (hrate :
      ∀ i : Fin (m + 1),
        targetRate <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_weighted_common_threshold
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo
    (fun i => ne_of_gt (add_pos (hpositive_hi i) (hpositive_lo i)))
    (fun i =>
      weightedBernoulliCommonThreshold_le_hi_of_le
        (hpositive_hi i).le (hpositive_lo i).le
        (add_pos (hpositive_hi i) (hpositive_lo i))
        (hprob_pos (adjacentHighIndex i))
        (hprob_lt_one (adjacentHighIndex i))
        (hprob_pos (adjacentLowIndex i))
        (hprob_lt_one (adjacentLowIndex i))
        (hordered i))
    hrate

/--
Adjacent finite binary level-chain exact-rate theorem using the weighted
geometric common threshold. If one adjacent closed weighted rate is minimal,
then the uniform finite adjacent objective error has exactly that exponential
rate.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_weighted_common_threshold_min
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hG :
      ∀ i : Fin (m + 1),
        sampleRate (adjacentHighIndex i) +
            sampleRate (adjacentLowIndex i) ≠ 0)
    (ha_le_hi :
      ∀ i : Fin (m + 1),
        weightedBernoulliCommonThreshold
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) ≤
          successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex iMin))
            (sampleRate (adjacentLowIndex iMin))
            (successProb (adjacentHighIndex iMin))
            (successProb (adjacentLowIndex iMin)) ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex iMin))
        (sampleRate (adjacentLowIndex iMin))
        (successProb (adjacentHighIndex iMin))
        (successProb (adjacentLowIndex iMin))) := by
  let M := binaryRatingModel successProb hprob0 hprob1
  let C :
      PairwiseThresholdRateTopLdpCertificate M sampleRate
        (fun i : Fin (m + 1) => adjacentHighIndex i)
        (fun i : Fin (m + 1) => adjacentLowIndex i) :=
    binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
      successProb hprob0 hprob1 hprob_pos hprob_lt_one
      sampleRate
      (fun i : Fin (m + 1) => adjacentHighIndex i)
      (fun i : Fin (m + 1) => adjacentLowIndex i)
      hpositive_hi hpositive_lo hG ha_le_hi
  have hC_rate_eq :
      ∀ i : Fin (m + 1),
        C.rate i =
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) := by
    intro i
    have hclosed :
        pairwiseSellerThresholdRateTop M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i) =
          (weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) : WithTop ℝ) :=
      binaryRatingModel_pairwiseThresholdRateTop_eq_closed_weighted_rate
        successProb hprob0 hprob1 hprob_pos hprob_lt_one
        sampleRate (adjacentHighIndex i) (adjacentLowIndex i)
        (hpositive_hi i) (hpositive_lo i) (hG i)
    have hC := C.threshold_rate_top_eq i
    exact WithTop.coe_eq_coe.mp (hC.symm.trans hclosed)
  simpa [hC_rate_eq iMin] using
    one_sub_finiteUniformFloorPkObjective_hasExponentialRate_of_pairwiseThresholdRateTopLdpCertificate_min_component
      M sampleRate
      (fun i : Fin (m + 1) => adjacentHighIndex i)
      (fun i : Fin (m + 1) => adjacentLowIndex i)
      C iMin
      (fun i => by
        rw [hC_rate_eq iMin, hC_rate_eq i]
        exact hrate_ge i)

/--
Adjacent finite binary level-chain exact-rate theorem from ordered adjacent
success probabilities. This derives the weighted-threshold order condition and
then applies the exact finite aggregate theorem.
-/
theorem finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_ordered_weighted_common_threshold_min
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex iMin))
            (sampleRate (adjacentLowIndex iMin))
            (successProb (adjacentHighIndex iMin))
            (successProb (adjacentLowIndex iMin)) ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex iMin))
        (sampleRate (adjacentLowIndex iMin))
        (successProb (adjacentHighIndex iMin))
        (successProb (adjacentLowIndex iMin))) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_weighted_common_threshold_min
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo
    (fun i => ne_of_gt (add_pos (hpositive_hi i) (hpositive_lo i)))
    (fun i =>
      weightedBernoulliCommonThreshold_le_hi_of_le
        (hpositive_hi i).le (hpositive_lo i).le
        (add_pos (hpositive_hi i) (hpositive_lo i))
        (hprob_pos (adjacentHighIndex i))
        (hprob_lt_one (adjacentHighIndex i))
        (hprob_pos (adjacentLowIndex i))
        (hprob_lt_one (adjacentLowIndex i))
        (hordered i))
    iMin hrate_ge
end

end GJ19OptimalBinaryRatingSystems
