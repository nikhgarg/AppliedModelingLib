import GJ19OptimalBinaryRatingSystems.AppendixB
import GJ19OptimalBinaryRatingSystems.SourceDefinitions

/-!
# Source matching-function assembly for Theorem 3.1

The rate development uses a finite vector of sample rates.  The paper defines
that vector from the primitive matching function by
`g_i = inf_{θ ∈ S_i} g(θ)`.  This module performs that source-model
assembly for ordered interval cells and feeds the derived vector into the
checked continuum/rate theorem.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability Filter MeasureTheory Topology

/--
Primitive source data for a fixed finite Theorem 3.1 discretization.  All
fields are model or regularity inputs from the paper; the finite sample-rate
vector, endpoint optimizer, and exponential-rate certificate are derived.
-/
structure Theorem31SourceFiniteDiscretizationWeightedModel
    (μ : Measure ℝ) : Type where
  m : ℕ
  hm : 1 < m
  cut : ℕ → ℝ
  hcut_zero : cut 0 = 0
  hcut_last : cut (m + 2) = 1
  hcut_mono : Monotone cut
  hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1)
  matchFunction : ℝ → ℝ
  hmatch : SourceMatchingFunction matchFunction
  weight : ℝ × ℝ → ℝ
  hweight_int :
    ∀ component,
      IntegrableOn weight
        ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hcut_mono
          (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
        (μ.prod μ)
  hweight_nonneg :
    ∀ component,
      ∀ᵐ x ∂(μ.prod μ).restrict
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hcut_mono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
        0 ≤ weight x
  hweight_cont : Continuous weight
  hweight_midpoint_pos :
    ∀ component : theorem31OrderedNontrivialPairComponent m,
      0 < weight
        (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
          component)

/-- The source-defined finite sample-rate vector `g_i`. -/
def Theorem31SourceFiniteDiscretizationWeightedModel.sampleRate
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ) :
    Fin (S.m + 2) → ℝ :=
  sourceCellMatchingRate S.cut S.matchFunction

/-- Every displayed source cutpoint lies in the normalized quality domain. -/
theorem Theorem31SourceFiniteDiscretizationWeightedModel.cut_mem
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (i : ℕ) (hi : i ≤ S.m + 2) : S.cut i ∈ sourceQualityDomain := by
  constructor
  · rw [← S.hcut_zero]
    exact S.hcut_mono (Nat.zero_le i)
  · rw [← S.hcut_last]
    exact S.hcut_mono hi

/-- Every source cell is contained in the normalized quality interval. -/
theorem Theorem31SourceFiniteDiscretizationWeightedModel.cell_subset_qualityDomain
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (i : Fin (S.m + 2)) :
    Set.Icc (S.cut i.val) (S.cut (i.val + 1)) ⊆ sourceQualityDomain := by
  intro θ hθ
  have hlo := S.cut_mem i.val (by omega)
  have hhi := S.cut_mem (i.val + 1) (by omega)
  exact ⟨hlo.1.trans hθ.1, hθ.2.trans hhi.2⟩

/-- The source cell-infimum vector is exactly the lower-cutpoint matching rate. -/
theorem Theorem31SourceFiniteDiscretizationWeightedModel.sampleRate_eq
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (i : Fin (S.m + 2)) :
    S.sampleRate i = S.matchFunction (S.cut i.val) := by
  apply sourceCellMatchingRate_eq_lower_cutpoint
  · exact S.hcut_mono (Nat.le_succ i.val)
  · exact S.hmatch.1.mono (S.cell_subset_qualityDomain i)

/-- The derived source sample-rate vector is positive. -/
theorem Theorem31SourceFiniteDiscretizationWeightedModel.sampleRate_pos
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (i : Fin (S.m + 2)) :
    0 < S.sampleRate i := by
  exact
    sourceCellMatchingRate_pos S.cut S.matchFunction i S.hmatch
      (S.hcut_mono (Nat.le_succ i.val))
      (S.cut_mem i.val (by omega)) (S.cell_subset_qualityDomain i)

/-- The derived source sample-rate vector is nondecreasing. -/
theorem Theorem31SourceFiniteDiscretizationWeightedModel.sampleRate_mono
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    {i j : Fin (S.m + 2)} (hij : i.val ≤ j.val) :
    S.sampleRate i ≤ S.sampleRate j := by
  rw [S.sampleRate_eq i, S.sampleRate_eq j]
  exact S.hmatch.1
    (S.cut_mem i.val (by omega)) (S.cut_mem j.val (by omega))
    (S.hcut_mono hij)

/--
Forgetful map from the primitive source matching-function model to the finite
weighted model used by the checked Theorem 3.1 rate layer.  In particular,
the finite sample-rate fields are proved here from `g`; they are not supplied
as a separate certificate.
-/
def Theorem31SourceFiniteDiscretizationWeightedModel.toFiniteWeightedModel
    {μ : Measure ℝ} (S : Theorem31SourceFiniteDiscretizationWeightedModel μ) :
    LemmaC4AppropriateFiniteLevelsWeightedModel μ where
  m := S.m
  hm := S.hm
  cut := S.cut
  hmono := S.hcut_mono
  hcut_strict := S.hcut_strict
  sampleRate := S.sampleRate
  hsample_pos := by
    intro n hn
    rw [binaryEndpointSampleRateNat_of_lt S.sampleRate hn]
    exact S.sampleRate_pos ⟨n, hn⟩
  hsample_mono := by
    intro i j hij
    exact S.sampleRate_mono hij
  weight := S.weight
  hweight_int := S.hweight_int
  hweight_nonneg := S.hweight_nonneg
  hweight_cont := S.hweight_cont
  hweight_midpoint_pos := S.hweight_midpoint_pos

/--
Source-assembled fixed-discretization Theorem 3.1.  Lean derives the paper's
cell rates from `g`, constructs the unique equalized endpoint levels, proves
their finite rate optimality, and supplies the exact selected-`Wbar_k`
exponential-rate and fixed-partition lexicographic certificates.
-/
theorem theorem31_source_matching_function_weighted_fixed_discretization
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (limitingValue : ℝ) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hcut_mono S.sampleRate levels hlevels
              S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (S.m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels := by
  simpa [Theorem31SourceFiniteDiscretizationWeightedModel.toFiniteWeightedModel]
    using
    theorem31_appropriate_finite_levels_weighted_fixed_value_lexicographic_certificate
      μ S.toFiniteWeightedModel limitingValue

/--
Source-assembled staged Theorem 3.1.  If `S*` denotes the source's selected
value-maximizing ordered discretization, Lean derives its `g_i` values from
the primitive matching function, constructs the rate-maximizing endpoint
levels, and proves the exact source `Wbar_k` exponential-rate certificate.
No rate optimizer or finite sample-rate vector is accepted as input.
-/
theorem theorem31_source_matching_function_weighted_value_argmax_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (hcut_value :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (S.m + 2))
        limitingValue S.cut) :
    ∃ levels : Fin (S.m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (S.m + 2) → ℝ) → Prop)
            (fun candidate : Fin (S.m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate S.sampleRate)
            levels ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ S.cut S.hcut_mono S.sampleRate levels
              hlevels S.weight)
            (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (monotoneIntervalCutpointsEndpointFeasible (S.m + 2))
            limitingValue S.cut := by
  simpa [Theorem31SourceFiniteDiscretizationWeightedModel.toFiniteWeightedModel]
    using
      theorem31_strict_cutpoint_value_argmax_forward_clipped_endpoint_source_certificate
        μ S.hm limitingValue S.cut S.hcut_mono S.hcut_strict hcut_value
        S.sampleRate S.toFiniteWeightedModel.hsample_pos
        S.toFiniteWeightedModel.hsample_mono S.weight S.hweight_int
        S.hweight_nonneg S.hweight_cont S.hweight_midpoint_pos


end

end GJ19OptimalBinaryRatingSystems
