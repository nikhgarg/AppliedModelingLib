import GJ19OptimalBinaryRatingSystems.AppendixB

/-!
# Paper Assumptions: GJ19 Optimal Binary Rating Systems

This file gives stable names to source-condition reducers used in the GJ19
closeout.  They are not advertised as assumptions printed in the paper.  The
source text has much shorter prose hypotheses: Appendix B.1 assumes uniform
matching and uniform convergence of the interval-quantile maps, while Lemma
C.4 argues from monotonicity, non-piecewise-constancy, and a
continuity/nearby-items obstruction.  The declarations below keep the
corresponding Lean proof interfaces auditable and reusable.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/--
Theorem B.1 representative-normalization assumption.

The paper's source argument treats `β_M` as a representative of an optimal
level function.  The Lean B.1 conclusion is uniform on source coordinates, so
the usable normalization hypothesis is exact eventual pointwise equality on
`[0,1]`, not equality merely up to measure zero.
-/
-- audit-premise: heq : assumption_theoremB1_exact_representative_normalization betaSeq referenceSeq
def assumption_theoremB1_exact_representative_normalization
    (betaSeq referenceSeq : ℕ → ℝ → ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop,
    ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      betaSeq M θ = referenceSeq M θ

/--
Canonical B.1 representative-normalization assumption, specialized to the
uniform equalized clamped-floor representative closed in `AppendixB.lean`.
-/
-- audit-premise: heq : assumption_theoremB1_canonical_exact_representative_normalization betaSeq
abbrev assumption_theoremB1_canonical_exact_representative_normalization
    (betaSeq : ℕ → ℝ → ℝ) : Prop :=
  assumption_theoremB1_exact_representative_normalization betaSeq
    canonicalUniformEqualizedClampedFloorBetaSeq

/--
Theorem B.1 value-level anchor assumption.

For each dyadic subsequence, sufficiently far tails of `β_M` are uniformly
close to an anchor `β_M` value with a subsequence-dependent mesh tending to
zero.  This is often the weakest practical selector/coherence route because it
does not require pointwise representative equality with a reference branch.
-/
-- audit-premise: hanchor : assumption_theoremB1_value_anchor_bound_by_subsequence betaSeq
def assumption_theoremB1_value_anchor_bound_by_subsequence
    (betaSeq : ℕ → ℝ → ℝ) : Prop :=
  ∃ mesh : ℕ → ℕ → ℝ,
    (∀ C : ℕ, Tendsto (mesh C) atTop (nhds 0)) ∧
    (∀ C M : ℕ, 0 ≤ mesh C M) ∧
    ∀ C : ℕ,
      ∀ᶠ M : ℕ in atTop,
        ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            dist
              (betaSeq (theoremB1SubsequenceIndex C N) θ)
              (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh C M

/--
Theorem B.1 dyadic quantile-tracking assumption.

Every positive dyadic subsequence of `β_M` tracks the corresponding quantile
subsequence up to a vanishing uniform error.  This is a selector/coherence
assumption rather than a representative-normalization assumption.
-/
-- audit-premise: htracking : assumption_theoremB1_dyadic_quantile_tracking betaSeq quantileSeq
def assumption_theoremB1_dyadic_quantile_tracking
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) : Prop :=
  ∀ C : ℕ, 0 < C →
    ∃ mesh : ℕ → ℝ,
      Tendsto mesh atTop (nhds 0) ∧
        ∀ᶠ N : ℕ in atTop,
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            dist
              (betaSeq (theoremB1SubsequenceIndex C N) θ)
              (quantileSeq (theoremB1SubsequenceIndex C N) θ) ≤ mesh N

/--
Theorem B.1 quantile-floor limit-tracking assumption.

This is the source-natural non-equispaced selector condition: the paper
quantile map remains within a bounded number of `m`-grid cells of its limiting
source coordinate.  For equispaced Kendall/Spearman intervals this is proved
with `B = 1`; for a new non-equispaced source model this is the concrete
quantile-geometry estimate to prove.
-/
-- audit-premise: hlimitTrack : assumption_theoremB1_quantile_floor_limit_dist_tracking quantileSeq quantileLimit
def assumption_theoremB1_quantile_floor_limit_dist_tracking
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ) : Prop :=
  (∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1) ∧
  ∃ B : ℕ,
    ∀ᶠ m : ℕ in atTop,
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        dist (quantileLimit θ) (quantileSeq (m + 2) θ) ≤
          (B : ℝ) / (((m + 2 : ℕ) : ℝ))

/--
Theorem B.1 variable dyadic quantile-floor tracking assumption.
-/
-- audit-premise: htrack : assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt quantileSeq quantileLimit BSeq widthSeq
def assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (BSeq widthSeq : ℕ → ℕ → ℕ) : Prop :=
  (∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileLimit θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    Tendsto
      (fun M : ℕ =>
        ((widthSeq C M : ℝ) ^ 2) /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ)))
      atTop (nhds 0)) ∧
  (∀ C : ℕ, 0 < C →
    ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    ∀ᶠ M : ℕ in atTop,
      ∀ N : ℕ, M ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                θ) ≤
            (BSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                θ) ≤
            ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ)))

theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt_of_limit_dist_tracking
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimitTrack :
      assumption_theoremB1_quantile_floor_limit_dist_tracking
        quantileSeq quantileLimit) :
    ∃ BSeq widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt
        quantileSeq quantileLimit BSeq widthSeq := by
  rcases hlimitTrack with ⟨hquantile_range, B, hdist_track⟩
  refine
    ⟨fun _ _ => B, fun _ _ => 2 + 2 * B,
      hquantile_range, hlimit_range, ?_, ?_, ?_⟩
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    have hiter :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
          atTop atTop :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    have hden_nat :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M + 1)
          atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hiter
    have hden_real :
        Tendsto
          (fun M : ℕ =>
            (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
              ℝ)))
          atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hden_nat
    simpa [endpointStart] using
      (Filter.Tendsto.const_div_atTop hden_real
        ((((2 + 2 * B : ℕ) : ℝ)) ^ 2))
  · intro C _hC
    filter_upwards with M
    rfl
  · rw [Filter.eventually_atTop] at hdist_track
    rcases hdist_track with ⟨threshold, htrack⟩
    intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    have htend :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    rw [Filter.tendsto_atTop] at htend
    have hlarge :
        ∀ᶠ M : ℕ in atTop,
          threshold ≤ uniformDoubledEndpointIndexIterate endpointStart M :=
      htend threshold
    filter_upwards [hlarge] with M hM
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
    have hcomp :
        uniformDoubledEndpointIndexIterate mOld (N - M) = mRef := by
      dsimp [mOld, mRef]
      rw [uniformDoubledEndpointIndexIterate_comp]
      rw [Nat.add_sub_of_le hN]
    have hmOld_le_ref : mOld ≤ mRef := by
      rw [← hcomp]
      exact uniformDoubledEndpointIndexIterate_self_le mOld (N - M)
    have hmRef_ge : threshold ≤ mRef := hM.trans hmOld_le_ref
    refine ⟨?_, ?_⟩
    · simpa [mOld, endpointStart] using htrack mOld hM θ hθ
    · have hbase :
          dist (quantileLimit θ) (quantileSeq (mRef + 2) θ) ≤
            (B : ℝ) / (((mRef + 2 : ℕ) : ℝ)) := by
        simpa [mRef, endpointStart] using htrack mRef hmRef_ge θ hθ
      have hpow_pos : 0 < 2 ^ (N - M) :=
        Nat.pow_pos (by norm_num : 0 < (2 : ℕ))
      have hB_scaled_nat : B ≤ 2 ^ (N - M) * B :=
        Nat.le_mul_of_pos_left B hpow_pos
      have hB_scaled_real :
          (B : ℝ) ≤ ((2 ^ (N - M) * B : ℕ) : ℝ) := by
        exact_mod_cast hB_scaled_nat
      have hden_nonneg : 0 ≤ (((mRef + 2 : ℕ) : ℝ)) := by positivity
      have hdiv :
          (B : ℝ) / (((mRef + 2 : ℕ) : ℝ)) ≤
            ((2 ^ (N - M) * B : ℕ) : ℝ) /
              (((mRef + 2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hB_scaled_real hden_nonneg
      exact hbase.trans hdiv

theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt_of_limit_dist_tracking_and_uniform_convergence
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit atTop
        (Set.Icc (0 : ℝ) 1))
    (hlimitTrack :
      assumption_theoremB1_quantile_floor_limit_dist_tracking
        quantileSeq quantileLimit) :
    ∃ BSeq widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt
        quantileSeq quantileLimit BSeq widthSeq := by
  rcases hlimitTrack with ⟨hquantile_range, B, hdist_track⟩
  exact
    assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt_of_limit_dist_tracking
      quantileSeq quantileLimit
      (theoremB1_quantileLimit_mem_Icc_of_tendstoUniformlyOn_shift
        quantileSeq quantileLimit hquantile hquantile_range)
      ⟨hquantile_range, B, hdist_track⟩

/--
Theorem B.1 optimal quantile-floor source convention.

This packages the beta representative, finite endpoint optimality,
quantile-floor index formula, range, and `O(1/m)` tracking fields in the form
consumed by the checked B.1 bridge.
-/
-- audit-premise: H : assumption_theoremB1_optimal_quantile_floor_global_dist_tracking_convention betaSeq quantileSeq levels levelIndex
abbrev assumption_theoremB1_optimal_quantile_floor_global_dist_tracking_convention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2)) : Type :=
  TheoremB1OptimalQuantileFloorGlobalDistTrackingConvention
    betaSeq quantileSeq levels levelIndex

/--
Theorem B.1 selector-coherence assumption, collecting the currently verified
routes to the B.1 conclusion.

The disjunction is intentional: a source model may close B.1 by proving
value-level anchor Cauchy tails, dyadic quantile tracking, or exact pointwise
normalization to an already-closed reference branch.
-/
-- audit-premise: hselector : assumption_theoremB1_selector_coherence betaSeq quantileSeq quantileLimit
def assumption_theoremB1_selector_coherence
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ) : Prop :=
  assumption_theoremB1_value_anchor_bound_by_subsequence betaSeq ∨
  assumption_theoremB1_dyadic_quantile_tracking betaSeq quantileSeq ∨
    ∃ referenceSeq : ℕ → ℝ → ℝ,
      theoremB1UniformOptimalSubsequencePrincipleTo
        referenceSeq quantileSeq quantileLimit ∧
      assumption_theoremB1_exact_representative_normalization
        betaSeq referenceSeq

/--
Paper-facing B.1 transfer under the named exact representative-normalization
assumption.
-/
theorem theoremB1_dyadic_subsequence_uniform_convergence_of_exact_representative_normalization
    (betaSeq referenceSeq : ℕ → ℝ → ℝ)
    (href : theoremB1DyadicSubsequenceUniformConvergence referenceSeq)
    (heq :
      assumption_theoremB1_exact_representative_normalization
        betaSeq referenceSeq) :
    theoremB1DyadicSubsequenceUniformConvergence betaSeq :=
  theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq
    betaSeq referenceSeq href heq

/--
Paper-facing B.1 general-limit transfer under the named exact
representative-normalization assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_exact_representative_normalization
    (betaSeq referenceSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (href :
      theoremB1UniformOptimalSubsequencePrincipleTo
        referenceSeq quantileSeq quantileLimit)
    (heq :
      assumption_theoremB1_exact_representative_normalization
        betaSeq referenceSeq) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_eq
    betaSeq referenceSeq quantileSeq quantileLimit href heq

/--
Paper-facing B.1 identity-limit transfer under the named exact
representative-normalization assumption.
-/
theorem theoremB1_uniform_subsequence_principle_of_exact_representative_normalization
    (betaSeq referenceSeq quantileSeq : ℕ → ℝ → ℝ)
    (href :
      theoremB1UniformOptimalSubsequencePrinciple referenceSeq quantileSeq)
    (heq :
      assumption_theoremB1_exact_representative_normalization
        betaSeq referenceSeq) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq
    betaSeq referenceSeq quantileSeq href heq

/--
Canonical B.1 source-facing transfer under the named canonical exact
representative-normalization assumption.
-/
theorem theoremB1_uniform_subsequence_principle_of_canonical_exact_representative_normalization
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (heq :
      assumption_theoremB1_canonical_exact_representative_normalization
        betaSeq) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq_canonical_uniform_equalized_clampedFloor
    betaSeq quantileSeq heq

/--
Paper-facing B.1 general-limit bridge under the named value-level anchor
assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_value_anchor_bound_by_subsequence
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (hanchor :
      assumption_theoremB1_value_anchor_bound_by_subsequence betaSeq) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases hanchor with ⟨mesh, hmesh, hmesh_nonneg, hanchor⟩
  exact
    theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound_by_subsequence
      betaSeq quantileSeq quantileLimit mesh hmesh hmesh_nonneg hanchor

/--
Paper-facing B.1 general-limit bridge under the named dyadic quantile-tracking
assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_dyadic_quantile_tracking_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (htracking :
      assumption_theoremB1_dyadic_quantile_tracking betaSeq quantileSeq) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_dyadic_quantile_tracking
    betaSeq quantileSeq quantileLimit htracking

/--
Paper-facing B.1 general-limit bridge from the named quantile-floor
limit-tracking assumption plus the source beta representation and finite
optimality fields.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_limit_dist_tracking_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hlimitTrack :
      assumption_theoremB1_quantile_floor_limit_dist_tracking
        quantileSeq quantileLimit) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases hlimitTrack with ⟨hquantile_range, B, hdist_track⟩
  exact
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking_clean
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range B hdist_track

/--
Paper-facing B.1 general-limit bridge from the named variable dyadic
quantile-floor tracking assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_subsqrt_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (BSeq widthSeq : ℕ → ℕ → ℕ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (htrack :
      assumption_theoremB1_quantile_floor_variable_dist_tracking_subsqrt
        quantileSeq quantileLimit BSeq widthSeq) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases htrack with ⟨hquantile_range, hlimit_range, hwidthSqRate,
    hwidth_absorb, hdist_track⟩
  exact
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_subsqrt
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range hlimit_range BSeq widthSeq
      hwidthSqRate hwidth_absorb hdist_track

/--
Theorem B.1 linear-mesh quantile-floor tracking assumption.

This is the source-shaped arbitrary non-equispaced route: the quantile error
induces a selected old-grid window whose width is sublinear in the old endpoint
count, and the uniform optimal endpoint grid has a linear max-gap bound.
-/
-- audit-premise: htrack : assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh quantileSeq quantileLimit levels BSeq widthSeq K
def assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (BSeq widthSeq : ℕ → ℕ → ℕ) (K : ℝ) : Prop :=
  (∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileLimit θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    Tendsto
      (fun M : ℕ =>
        (widthSeq C M : ℝ) /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
            ℝ)))
      atTop (nhds 0)) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    ∀ᶠ M : ℕ in atTop,
      binaryEndpointAdjacentMaxWidth
          (m := uniformDoubledEndpointIndexIterate endpointStart M)
          (levels (uniformDoubledEndpointIndexIterate endpointStart M)) ≤
        K /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
            ℝ))) ∧
  (∀ C : ℕ, 0 < C →
    ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    ∀ᶠ M : ℕ in atTop,
      ∀ N : ℕ, M ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                θ) ≤
            (BSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                θ) ≤
            ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ)))

/--
Paper-facing B.1 general-limit bridge from the named linear-mesh variable
dyadic quantile-floor tracking assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_linear_mesh_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (BSeq widthSeq : ℕ → ℕ → ℕ) (K : ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (htrack :
      assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh
        quantileSeq quantileLimit levels BSeq widthSeq K) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases htrack with ⟨hquantile_range, hlimit_range, hwidthRatio,
    hlinearMesh, hwidth_absorb, hdist_track⟩
  exact
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_linear_mesh
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range hlimit_range BSeq widthSeq K
      hwidthRatio hlinearMesh hwidth_absorb hdist_track

/--
Theorem B.1 geometric-mesh quantile-floor tracking assumption.

The endpoint mesh is no longer assumed: it is derived from the C.5 dyadic
refinement recurrence for uniform optimal endpoint levels.  This source-side
selector interface is kept as a reusable B.1 route.
-/
-- audit-premise: htrack : assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh quantileSeq quantileLimit BSeq widthSeq
def assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (BSeq widthSeq : ℕ → ℕ → ℕ) : Prop :=
  (∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
    quantileLimit θ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    Tendsto
      (fun M : ℕ =>
        (widthSeq C M : ℝ) /
          (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
            ℝ)))
      atTop (nhds 0)) ∧
  (∀ C : ℕ, 0 < C →
    ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M) ∧
  (∀ C : ℕ, 0 < C →
    let endpointStart : ℕ := 2 * C - 1
    ∀ᶠ M : ℕ in atTop,
      ∀ N : ℕ, M ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                θ) ≤
            (BSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
          dist (quantileLimit θ)
              (quantileSeq
                (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                θ) ≤
            ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ)))

/--
Paper-facing B.1 general-limit bridge from the named geometric-mesh variable
dyadic quantile-floor tracking assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_geometric_mesh_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (BSeq widthSeq : ℕ → ℕ → ℕ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (htrack :
      assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh
        quantileSeq quantileLimit BSeq widthSeq) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases htrack with ⟨hquantile_range, hlimit_range, hwidthRatio,
    hwidth_absorb, hdist_track⟩
  exact
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_geometric_mesh
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      hlevelIndex_val hquantile_range hlimit_range BSeq widthSeq
      hwidthRatio hwidth_absorb hdist_track

/--
A source-style tail cell-error envelope supplies the linear-mesh variable
tracking assumption.  The input `BSeq C M` is measured in old endpoint-grid
cells: every later dyadic quantile map is within `BSeq C M / (m_M+2)` of the
limit, and `BSeq C M` is sublinear in the old endpoint count.
-/
theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh_of_sublinear_tail_cells
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (BSeq : ℕ → ℕ → ℕ) (K : ℝ)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hcellRatio :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (BSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
          atTop (nhds 0))
    (hlinearMesh :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          binaryEndpointAdjacentMaxWidth
              (m := uniformDoubledEndpointIndexIterate endpointStart M)
              (levels (uniformDoubledEndpointIndexIterate endpointStart M)) ≤
            K /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
    (htail :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) :
                    ℝ))) :
    ∃ widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh
        quantileSeq quantileLimit levels BSeq widthSeq K := by
  refine
    ⟨fun C M => 2 + 2 * BSeq C M,
      hquantile_range, hlimit_range, ?_, hlinearMesh, ?_, ?_⟩
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    let den : ℕ → ℝ := fun M : ℕ =>
      (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ))
    have hiter :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
          atTop atTop :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    have hden_nat :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M + 1)
          atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hiter
    have hden_real : Tendsto den atTop atTop := by
      dsimp [den]
      exact tendsto_natCast_atTop_atTop.comp hden_nat
    have hconst_zero :
        Tendsto (fun M : ℕ => (2 : ℝ) / den M) atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hden_real (2 : ℝ)
    have hscaled_zero :
        Tendsto
          (fun M : ℕ => (2 : ℝ) * ((BSeq C M : ℝ) / den M))
          atTop (nhds 0) := by
      have hbase :
          Tendsto (fun M : ℕ => (BSeq C M : ℝ) / den M)
            atTop (nhds 0) := by
        simpa [den] using hcellRatio C hC
      have hscaled_raw :
          Tendsto
            (fun M : ℕ => (2 : ℝ) * ((BSeq C M : ℝ) / den M))
            atTop (nhds ((2 : ℝ) * 0)) :=
        (tendsto_const_nhds (x := (2 : ℝ))).mul hbase
      simpa only [mul_zero] using hscaled_raw
    have hsum_zero :
        Tendsto
          (fun M : ℕ =>
            (2 : ℝ) / den M +
              (2 : ℝ) * ((BSeq C M : ℝ) / den M))
          atTop (nhds 0) :=
      by simpa using hconst_zero.add hscaled_zero
    refine Tendsto.congr' ?_ hsum_zero
    filter_upwards with M
    have hden_ne : den M ≠ 0 := by
      dsimp [den]
      positivity
    dsimp [den, endpointStart]
    field_simp [hden_ne]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · intro C _hC
    filter_upwards with M
    omega
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    filter_upwards [htail C hC] with M hMtail
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
    let scale : ℕ := 2 ^ (N - M)
    have hold :
        dist (quantileLimit θ) (quantileSeq (mOld + 2) θ) ≤
          (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
      simpa [mOld, endpointStart] using hMtail M le_rfl θ hθ
    have href_base :
        dist (quantileLimit θ) (quantileSeq (mRef + 2) θ) ≤
          (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
      simpa [mOld, mRef, endpointStart] using hMtail N hN θ hθ
    have hden_tail_nat :
        mRef + 2 ≤ scale * (mOld + 2) := by
      simpa [mOld, mRef, scale] using
        uniformDoubledEndpointIndexIterate_add_two_le_tail_scale_add_two
          endpointStart M N hN
    have hden_tail_real :
        (((mRef + 2 : ℕ) : ℝ)) ≤
          (scale : ℝ) * (((mOld + 2 : ℕ) : ℝ)) := by
      exact_mod_cast hden_tail_nat
    have hdenOld_pos : 0 < (((mOld + 2 : ℕ) : ℝ)) := by
      positivity
    have hdenRef_pos : 0 < (((mRef + 2 : ℕ) : ℝ)) := by
      positivity
    have hB_nonneg : 0 ≤ (BSeq C M : ℝ) := by
      exact_mod_cast Nat.zero_le (BSeq C M)
    have href_div :
        (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) ≤
          ((scale * BSeq C M : ℕ) : ℝ) /
            (((mRef + 2 : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ hdenOld_pos hdenRef_pos]
      calc
        (BSeq C M : ℝ) * (((mRef + 2 : ℕ) : ℝ))
            ≤ (BSeq C M : ℝ) *
                ((scale : ℝ) * (((mOld + 2 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left hden_tail_real hB_nonneg
        _ = ((scale * BSeq C M : ℕ) : ℝ) *
              (((mOld + 2 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_mul]
              ring
    exact ⟨hold, href_base.trans href_div⟩

/--
A source-style tail cell-error envelope supplies the geometric-mesh variable
tracking assumption.  Unlike the older linear-mesh constructor, no endpoint
mesh hypothesis is required: it is derived from the uniform C.5 refinement
recurrence.
-/
theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_sublinear_tail_cells
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (BSeq : ℕ → ℕ → ℕ)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hcellRatio :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        Tendsto
          (fun M : ℕ =>
            (BSeq C M : ℝ) /
              (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) :
                ℝ)))
          atTop (nhds 0))
    (htail :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) :
                    ℝ))) :
    ∃ widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh
        quantileSeq quantileLimit BSeq widthSeq := by
  refine
    ⟨fun C M => 2 + 2 * BSeq C M,
      hquantile_range, hlimit_range, ?_, ?_, ?_⟩
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    let den : ℕ → ℝ := fun M : ℕ =>
      (((uniformDoubledEndpointIndexIterate endpointStart M + 1 : ℕ) : ℝ))
    have hiter :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
          atTop atTop :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    have hden_nat :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M + 1)
          atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hiter
    have hden_real : Tendsto den atTop atTop := by
      dsimp [den]
      exact tendsto_natCast_atTop_atTop.comp hden_nat
    have hconst_zero :
        Tendsto (fun M : ℕ => (2 : ℝ) / den M) atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hden_real (2 : ℝ)
    have hscaled_zero :
        Tendsto
          (fun M : ℕ => (2 : ℝ) * ((BSeq C M : ℝ) / den M))
          atTop (nhds 0) := by
      have hbase :
          Tendsto (fun M : ℕ => (BSeq C M : ℝ) / den M)
            atTop (nhds 0) := by
        simpa [den] using hcellRatio C hC
      have hscaled_raw :
          Tendsto
            (fun M : ℕ => (2 : ℝ) * ((BSeq C M : ℝ) / den M))
            atTop (nhds ((2 : ℝ) * 0)) :=
        (tendsto_const_nhds (x := (2 : ℝ))).mul hbase
      simpa only [mul_zero] using hscaled_raw
    have hsum_zero :
        Tendsto
          (fun M : ℕ =>
            (2 : ℝ) / den M +
              (2 : ℝ) * ((BSeq C M : ℝ) / den M))
          atTop (nhds 0) :=
      by simpa using hconst_zero.add hscaled_zero
    refine Tendsto.congr' ?_ hsum_zero
    filter_upwards with M
    have hden_ne : den M ≠ 0 := by
      dsimp [den]
      positivity
    dsimp [den, endpointStart]
    field_simp [hden_ne]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · intro C _hC
    filter_upwards with M
    omega
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    filter_upwards [htail C hC] with M hMtail
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
    let scale : ℕ := 2 ^ (N - M)
    have hold :
        dist (quantileLimit θ) (quantileSeq (mOld + 2) θ) ≤
          (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
      simpa [mOld, endpointStart] using hMtail M le_rfl θ hθ
    have href_base :
        dist (quantileLimit θ) (quantileSeq (mRef + 2) θ) ≤
          (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
      simpa [mOld, mRef, endpointStart] using hMtail N hN θ hθ
    have hden_tail_nat :
        mRef + 2 ≤ scale * (mOld + 2) := by
      simpa [mOld, mRef, scale] using
        uniformDoubledEndpointIndexIterate_add_two_le_tail_scale_add_two
          endpointStart M N hN
    have hden_tail_real :
        (((mRef + 2 : ℕ) : ℝ)) ≤
          (scale : ℝ) * (((mOld + 2 : ℕ) : ℝ)) := by
      exact_mod_cast hden_tail_nat
    have hdenOld_pos : 0 < (((mOld + 2 : ℕ) : ℝ)) := by
      positivity
    have hdenRef_pos : 0 < (((mRef + 2 : ℕ) : ℝ)) := by
      positivity
    have hB_nonneg : 0 ≤ (BSeq C M : ℝ) := by
      exact_mod_cast Nat.zero_le (BSeq C M)
    have href_div :
        (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) ≤
          ((scale * BSeq C M : ℕ) : ℝ) /
            (((mRef + 2 : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ hdenOld_pos hdenRef_pos]
      calc
        (BSeq C M : ℝ) * (((mRef + 2 : ℕ) : ℝ))
            ≤ (BSeq C M : ℝ) *
                ((scale : ℝ) * (((mOld + 2 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left hden_tail_real hB_nonneg
        _ = ((scale * BSeq C M : ℕ) : ℝ) *
              (((mOld + 2 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_mul]
              ring
    exact ⟨hold, href_base.trans href_div⟩

/--
A real-valued uniform tail error schedule supplies the geometric-mesh
old-cell tracking assumption.  This is the source-facing form of the paper's
Appendix B uniform-convergence step: if dyadic tails of the interval-quantile
maps are uniformly within `errSeq C M` of the limiting source coordinate and
`errSeq C M -> 0`, then rounding `errSeq C M * (m_M + 2)` gives a sublinear
old-grid cell envelope.
-/
theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_real_tail_error
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (errSeq : ℕ → ℕ → ℝ)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (herr_nonneg : ∀ C M : ℕ, 0 ≤ errSeq C M)
    (herr_zero :
      ∀ C : ℕ, 0 < C → Tendsto (errSeq C) atTop (nhds 0))
    (htail :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                errSeq C M) :
    ∃ BSeq widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh
        quantileSeq quantileLimit BSeq widthSeq := by
  let BSeq : ℕ → ℕ → ℕ := fun C M =>
    Nat.ceil
      (errSeq C M *
        (((uniformDoubledEndpointIndexIterate (2 * C - 1) M + 2 : ℕ) : ℝ)))
  refine ⟨BSeq, ?_⟩
  refine
    assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_sublinear_tail_cells
      quantileSeq quantileLimit BSeq hquantile_range hlimit_range ?_ ?_
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    let mSeq : ℕ → ℕ := fun M : ℕ =>
      uniformDoubledEndpointIndexIterate endpointStart M
    let den : ℕ → ℝ := fun M : ℕ => (((mSeq M + 1 : ℕ) : ℝ))
    let den2 : ℕ → ℝ := fun M : ℕ => (((mSeq M + 2 : ℕ) : ℝ))
    let ratio : ℕ → ℝ := fun M : ℕ => den2 M / den M
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    have hm_tendsto :
        Tendsto mSeq atTop atTop := by
      dsimp [mSeq]
      exact
        uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
          hendpointStart_pos
    have hden_nat :
        Tendsto (fun M : ℕ => mSeq M + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hm_tendsto
    have hden_real : Tendsto den atTop atTop := by
      dsimp [den]
      exact tendsto_natCast_atTop_atTop.comp hden_nat
    have hinv_zero :
        Tendsto (fun M : ℕ => (1 : ℝ) / den M) atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hden_real (1 : ℝ)
    have hratio_tendsto : Tendsto ratio atTop (nhds 1) := by
      have hcongr :
          ∀ M : ℕ, ratio M = 1 + (1 : ℝ) / den M := by
        intro M
        have hden_ne : den M ≠ 0 := by
          dsimp [den, mSeq]
          positivity
        dsimp [ratio, den2, den]
        field_simp [hden_ne]
        norm_num [Nat.cast_add]
        ring
      have hsum :
          Tendsto (fun M : ℕ => 1 + (1 : ℝ) / den M) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add hinv_zero
      have hsum_one : Tendsto (fun M : ℕ => 1 + (1 : ℝ) / den M)
          atTop (nhds 1) := by
        simpa using hsum
      exact
        Tendsto.congr'
          (Filter.Eventually.of_forall fun M => (hcongr M).symm)
          hsum_one
    have hmain_zero :
        Tendsto (fun M : ℕ => errSeq C M * ratio M) atTop (nhds 0) := by
      have hmul :
          Tendsto (fun M : ℕ => errSeq C M * ratio M)
            atTop (nhds (0 * 1)) :=
        (herr_zero C hC).mul hratio_tendsto
      simpa using hmul
    have hbound_zero :
        Tendsto
          (fun M : ℕ => errSeq C M * ratio M + (1 : ℝ) / den M)
          atTop (nhds 0) := by
      have hsum :
          Tendsto
            (fun M : ℕ => errSeq C M * ratio M + (1 : ℝ) / den M)
            atTop (nhds (0 + 0)) :=
        hmain_zero.add hinv_zero
      simpa using hsum
    have hcell_zero :
        AppliedModelingLib.Math.TendsToZero
          (fun M : ℕ => (BSeq C M : ℝ) / den M) := by
      refine
        AppliedModelingLib.Math.TendsToZero_of_eventually_abs_le_tendsto_zero
          (fun M : ℕ => (BSeq C M : ℝ) / den M)
          (fun M : ℕ => errSeq C M * ratio M + (1 : ℝ) / den M)
          hbound_zero ?_
      filter_upwards with M
      have hden_pos : 0 < den M := by
        dsimp [den, mSeq]
        positivity
      have hden_nonneg : 0 ≤ den M := hden_pos.le
      have hden_ne : den M ≠ 0 := ne_of_gt hden_pos
      have herrM_nonneg : 0 ≤ errSeq C M := herr_nonneg C M
      have hx_nonneg :
          0 ≤ errSeq C M * den2 M := by
        exact mul_nonneg herrM_nonneg (by dsimp [den2, mSeq]; positivity)
      have hceil_le :
          (BSeq C M : ℝ) ≤ errSeq C M * den2 M + 1 := by
        dsimp [BSeq, endpointStart, mSeq, den2]
        exact (Nat.ceil_lt_add_one hx_nonneg).le
      have hquot_le :
          (BSeq C M : ℝ) / den M ≤
            (errSeq C M * den2 M + 1) / den M :=
        div_le_div_of_nonneg_right hceil_le hden_nonneg
      have htarget :
          (errSeq C M * den2 M + 1) / den M =
            errSeq C M * ratio M + (1 : ℝ) / den M := by
        dsimp [ratio]
        field_simp [hden_ne]
      have hleft_nonneg : 0 ≤ (BSeq C M : ℝ) / den M := by
        exact div_nonneg (by positivity) hden_nonneg
      rw [abs_of_nonneg hleft_nonneg]
      exact hquot_le.trans_eq htarget
    simpa [AppliedModelingLib.Math.TendsToZero, BSeq, endpointStart, mSeq, den] using
      hcell_zero
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    filter_upwards [htail C hC] with M hMtail
    intro N hN θ hθ
    let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
    have htail_base :
        dist (quantileLimit θ)
            (quantileSeq
              (uniformDoubledEndpointIndexIterate endpointStart N + 2)
              θ) ≤
          errSeq C M :=
      hMtail N hN θ hθ
    have hden_pos : 0 < (((mOld + 2 : ℕ) : ℝ)) := by
      positivity
    have hceil_ge :
        errSeq C M * (((mOld + 2 : ℕ) : ℝ)) ≤
          (BSeq C M : ℝ) := by
      dsimp [BSeq, mOld, endpointStart]
      exact Nat.le_ceil _
    have herr_le :
        errSeq C M ≤ (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
      rw [le_div_iff₀ hden_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hceil_ge
    exact htail_base.trans herr_le

/--
Uniform convergence of the paper interval-quantile maps supplies the
geometric-mesh old-cell tracking assumption.  This is the closest Lean
statement to the source proof of Appendix B.1: uniform convergence gives one
dyadic-tail real error schedule; rounding that schedule gives the sublinear
old-grid selector window, while the endpoint mesh is derived from C.5.
-/
theorem assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_tendstoUniformlyOn
    (quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit atTop
        (Set.Icc (0 : ℝ) 1)) :
    ∃ BSeq widthSeq : ℕ → ℕ → ℕ,
      assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh
        quantileSeq quantileLimit BSeq widthSeq := by
  classical
  let threshold : ℕ → ℕ := fun k : ℕ =>
    Classical.choose
      (eventually_atTop.1
        ((Metric.tendstoUniformlyOn_iff.1 hquantile)
          (1 / (((k + 1 : ℕ) : ℝ)))
          (by positivity)))
  have hthreshold :
      ∀ k n : ℕ, threshold k ≤ n →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist (quantileLimit θ) (quantileSeq n θ) <
            1 / (((k + 1 : ℕ) : ℝ)) := by
    intro k n hn
    have hspec :=
      Classical.choose_spec
        (eventually_atTop.1
          ((Metric.tendstoUniformlyOn_iff.1 hquantile)
            (1 / (((k + 1 : ℕ) : ℝ)))
            (by positivity)))
    simpa [threshold] using hspec n hn
  let errSeq : ℕ → ℕ → ℝ := fun C M : ℕ =>
    AppliedModelingLib.Math.reciprocalThresholdError threshold
      (uniformDoubledEndpointIndexIterate (2 * C - 1) M + 2)
  have hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1 :=
    theoremB1_quantileLimit_mem_Icc_of_tendstoUniformlyOn_shift
      quantileSeq quantileLimit hquantile hquantile_range
  refine
    assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_real_tail_error
      quantileSeq quantileLimit errSeq hquantile_range hlimit_range ?_ ?_ ?_
  · intro C M
    dsimp [errSeq]
    exact AppliedModelingLib.Math.reciprocalThresholdError_nonneg threshold _
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    have hiter :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
          atTop atTop :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    have hidx :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M + 2)
          atTop atTop :=
      (tendsto_add_atTop_nat 2).comp hiter
    have hbase :
        AppliedModelingLib.Math.TendsToZero
          (AppliedModelingLib.Math.reciprocalThresholdError threshold) :=
      AppliedModelingLib.Math.reciprocalThresholdError_tendsToZero threshold
    change Tendsto (errSeq C) atTop (nhds 0)
    change
      Tendsto (AppliedModelingLib.Math.reciprocalThresholdError threshold)
        atTop (nhds 0) at hbase
    simpa [errSeq, endpointStart] using hbase.comp hidx
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart_pos : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    let idx : ℕ → ℕ := fun M : ℕ =>
      uniformDoubledEndpointIndexIterate endpointStart M + 2
    have hiter :
        Tendsto
          (fun M : ℕ => uniformDoubledEndpointIndexIterate endpointStart M)
          atTop atTop :=
      uniformDoubledEndpointIndexIterate_tendsto_atTop_of_pos
        hendpointStart_pos
    have hidx :
        Tendsto idx atTop atTop := by
      dsimp [idx]
      exact (tendsto_add_atTop_nat 2).comp hiter
    have hthreshold0_event :
        ∀ᶠ M : ℕ in atTop, threshold 0 ≤ idx M := by
      rw [Filter.tendsto_atTop] at hidx
      exact hidx (threshold 0)
    filter_upwards [hthreshold0_event] with M hMlarge
    intro N hMN θ hθ
    let qM : ℕ := idx M
    let qN : ℕ := idx N
    let kM : ℕ := Nat.findGreatest (fun k : ℕ => threshold k ≤ qM) qM
    have hk_spec : threshold kM ≤ qM := by
      dsimp [kM]
      exact
        Nat.findGreatest_spec
          (P := fun k : ℕ => threshold k ≤ qM)
          (m := 0) (n := qM) (Nat.zero_le qM)
          (by simpa [qM] using hMlarge)
    have hqM_le_qN : qM ≤ qN := by
      have hcomp :
          uniformDoubledEndpointIndexIterate
              (uniformDoubledEndpointIndexIterate endpointStart M) (N - M) =
            uniformDoubledEndpointIndexIterate endpointStart N := by
        rw [uniformDoubledEndpointIndexIterate_comp]
        rw [Nat.add_sub_of_le hMN]
      have hmono :
          uniformDoubledEndpointIndexIterate endpointStart M ≤
            uniformDoubledEndpointIndexIterate endpointStart N := by
        rw [← hcomp]
        exact
          uniformDoubledEndpointIndexIterate_self_le
            (uniformDoubledEndpointIndexIterate endpointStart M) (N - M)
      dsimp [qM, qN, idx]
      omega
    have hk_qN : threshold kM ≤ qN := hk_spec.trans hqM_le_qN
    have hdist_lt :
        dist (quantileLimit θ) (quantileSeq qN θ) <
          1 / (((kM + 1 : ℕ) : ℝ)) :=
      hthreshold kM qN hk_qN θ hθ
    have herr_eq :
        errSeq C M = 1 / (((kM + 1 : ℕ) : ℝ)) := by
      dsimp [errSeq, kM, qM, idx, endpointStart]
      rfl
    simpa [qN, herr_eq] using le_of_lt hdist_lt

/--
Paper-facing B.1 closeout route.  If the source representation uses the
paper's quantile-floor selector, the finite endpoint vectors are optimal, and
the interval-quantile maps converge uniformly to the limiting source
coordinate, then the B.1 general-limit conclusion follows.  The selector
window is derived from uniform convergence and C.5, not assumed separately.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit atTop
        (Set.Icc (0 : ℝ) 1)) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases
      assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_tendstoUniformlyOn
        quantileSeq quantileLimit hquantile_range hquantile with
    ⟨BSeq, widthSeq, htrack⟩
  exact
    theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_geometric_mesh_assumption
      betaSeq quantileSeq quantileLimit levels levelIndex BSeq widthSeq
      hrepr hoptimal hlevelIndex_val htrack

/--
Paper-facing B.1 bridge for the non-equispaced selector route using actual
metric span rather than the generic C.2 max-gap bound.  This is the route that
allows `sqrt m`-scale selector windows: the source must prove that every
selected old block of that width has vanishing level span.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_metric_span_assumption
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (BSeq widthSeq : ℕ → ℕ → ℕ) (blockWidth : ℕ → ℕ → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ))
            (m + 1))
    (hquantile_range :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hlimit_range :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
        quantileLimit θ ∈ Set.Icc (0 : ℝ) 1)
    (hblockWidth :
      ∀ C : ℕ, 0 < C →
        Tendsto (blockWidth C) atTop (nhds 0))
    (hblockWidth_nonneg :
      ∀ C : ℕ, 0 < C → ∀ M : ℕ, 0 ≤ blockWidth C M)
    (hwidth_absorb :
      ∀ C : ℕ, 0 < C →
        ∀ᶠ M : ℕ in atTop, 2 + 2 * BSeq C M ≤ widthSeq C M)
    (hlarge :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          widthSeq C M ≤
            uniformDoubledEndpointIndexIterate endpointStart M + 1)
    (hspan :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ i : ℕ,
            ∀ hi :
              i + widthSeq C M ≤
                uniformDoubledEndpointIndexIterate endpointStart M + 1,
              levels (uniformDoubledEndpointIndexIterate endpointStart M)
                  ⟨i + widthSeq C M, by omega⟩ -
                levels (uniformDoubledEndpointIndexIterate endpointStart M)
                  ⟨i, by omega⟩ ≤ blockWidth C M)
    (hdist_track :
      ∀ C : ℕ, 0 < C →
        let endpointStart : ℕ := 2 * C - 1
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) ≤
                (BSeq C M : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart M + 2 : ℕ) : ℝ)) ∧
              dist (quantileLimit θ)
                  (quantileSeq
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) ≤
                ((2 ^ (N - M) * BSeq C M : ℕ) : ℝ) /
                  (((uniformDoubledEndpointIndexIterate endpointStart N + 2 : ℕ) : ℝ))) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  refine
    theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_metric_block_window
      betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
      widthSeq blockWidth hblockWidth hblockWidth_nonneg ?_ ?_
  · intro C hC
    filter_upwards [hwidth_absorb C hC] with M hM
    omega
  · intro C hC
    let endpointStart : ℕ := 2 * C - 1
    have hendpointStart : 0 < endpointStart := by
      dsimp [endpointStart]
      omega
    have hindex :
        ∀ᶠ M : ℕ in atTop,
          ∀ N : ℕ, M ≤ N →
            ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
              ∃ i : ℕ, ∃ hi :
                i + widthSeq C M ≤
                  uniformDoubledEndpointIndexIterate endpointStart M + 1,
                i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M)
                      θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart M)
                      θ).1 ≤
                    i + widthSeq C M ∧
                  2 ^ (N - M) * i ≤
                    (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N)
                      θ).1 ∧
                  (levelIndex
                      (uniformDoubledEndpointIndexIterate endpointStart N)
                      θ).1 ≤
                    2 ^ (N - M) * (i + widthSeq C M) := by
      refine
        uniformDoubledEndpointIndexIterate_eventually_scaled_block_window_of_common_floor_coordinate_variable_bounded_error
          levelIndex hendpointStart (BSeq C) (widthSeq C)
          (hwidth_absorb C hC)
          (by simpa [endpointStart] using hlarge C hC) ?_
      filter_upwards [hdist_track C hC] with M hM
      intro N hN θ hθ
      let mOld : ℕ := uniformDoubledEndpointIndexIterate endpointStart M
      let mRef : ℕ := uniformDoubledEndpointIndexIterate endpointStart N
      let scale : ℕ := 2 ^ (N - M)
      have hold_eq :
          levelIndex mOld θ =
            clampedFloorLevelIndex mOld (quantileSeq (mOld + 2) θ) := by
        apply Fin.ext
        rw [hlevelIndex_val mOld θ hθ, clampedFloorLevelIndex_val]
      have href_eq :
          levelIndex mRef θ =
            clampedFloorLevelIndex mRef (quantileSeq (mRef + 2) θ) := by
        apply Fin.ext
        rw [hlevelIndex_val mRef θ hθ, clampedFloorLevelIndex_val]
      rcases hM N hN θ hθ with ⟨hold_dist, href_dist⟩
      refine ⟨quantileLimit θ, hlimit_range θ hθ, ?_, ?_, ?_, ?_⟩
      · have hfloor :=
          clampedFloorLevelIndex_le_add_of_dist_le_div
            mOld (BSeq C M) (hquantile_range mOld θ hθ).1 hold_dist
        simpa [mOld, hold_eq] using hfloor
      · have hold_dist_sym :
            dist (quantileSeq (mOld + 2) θ) (quantileLimit θ) ≤
              (BSeq C M : ℝ) / (((mOld + 2 : ℕ) : ℝ)) := by
          simpa [dist_comm, mOld] using hold_dist
        have hfloor :=
          clampedFloorLevelIndex_le_add_of_dist_le_div
            mOld (BSeq C M) (hlimit_range θ hθ).1 hold_dist_sym
        simpa [mOld, hold_eq] using hfloor
      · have hfloor :=
          clampedFloorLevelIndex_le_add_of_dist_le_div
            mRef (scale * BSeq C M) (hquantile_range mRef θ hθ).1
            (by simpa [mRef, scale] using href_dist)
        simpa [mRef, scale, href_eq] using hfloor
      · have href_dist_sym :
            dist (quantileSeq (mRef + 2) θ) (quantileLimit θ) ≤
              ((scale * BSeq C M : ℕ) : ℝ) /
                (((mRef + 2 : ℕ) : ℝ)) := by
          simpa [dist_comm, mRef, scale] using href_dist
        have hfloor :=
          clampedFloorLevelIndex_le_add_of_dist_le_div
            mRef (scale * BSeq C M) (hlimit_range θ hθ).1 href_dist_sym
        simpa [mRef, scale, href_eq] using hfloor
    filter_upwards [hindex, hspan C hC] with M hMindex hMspan
    intro N hN θ hθ
    rcases hMindex N hN θ hθ with
      ⟨i, hi, hold_lo, hold_hi, href_lo, href_hi⟩
    refine ⟨i, hi, ?_, hold_lo, hold_hi, href_lo, href_hi⟩
    simpa [endpointStart] using hMspan i hi

/--
Paper-facing B.1 general-limit bridge under the packaged optimal
quantile-floor tracking convention.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_optimal_quantile_floor_global_dist_tracking_convention
    (betaSeq quantileSeq : ℕ → ℝ → ℝ) (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (H :
      assumption_theoremB1_optimal_quantile_floor_global_dist_tracking_convention
        betaSeq quantileSeq levels levelIndex) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit :=
  theoremB1UniformOptimalSubsequencePrincipleTo_of_optimal_quantile_floor_global_dist_tracking_convention
    betaSeq quantileSeq quantileLimit levels levelIndex H

/--
Paper-facing B.1 general-limit bridge under the named selector-coherence
assumption.
-/
theorem theoremB1_uniform_subsequence_principle_to_of_selector_coherence
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (hselector :
      assumption_theoremB1_selector_coherence
        betaSeq quantileSeq quantileLimit) :
    theoremB1UniformOptimalSubsequencePrincipleTo
      betaSeq quantileSeq quantileLimit := by
  rcases hselector with hanchor | htracking | href
  · exact
      theoremB1_uniform_subsequence_principle_to_of_value_anchor_bound_by_subsequence
        betaSeq quantileSeq quantileLimit hanchor
  · exact
      theoremB1_uniform_subsequence_principle_to_of_dyadic_quantile_tracking_assumption
        betaSeq quantileSeq quantileLimit htracking
  · rcases href with ⟨referenceSeq, href, heq⟩
    exact
      theoremB1_uniform_subsequence_principle_to_of_exact_representative_normalization
        betaSeq referenceSeq quantileSeq quantileLimit href heq

/--
Lemma C.4 positive-support interval model assumption.

This is the source regularity package needed by the reverse branch: monotone
measurable success probabilities, nonnegative integrable weights, positive
diagonal weight and sample rate on the interval, and interior Bernoulli
probabilities.  The zero-rate/no-positive-rate conclusion is derived from
these fields elsewhere; it is not stored in this assumption.
-/
-- audit-premise: R : assumption_lemmaC4_positive_support_interval_model μ
abbrev assumption_lemmaC4_positive_support_interval_model
    (μ : Measure ℝ) : Type :=
  LemmaC4RawSourcePositiveSupportIntervalModel μ

/--
Lemma C.4 reverse branch under the named positive-support source model.

This direction does not use a finite-level selected-realization assumption:
the zero-rate obstruction follows directly from the monotone positive-support
source fields.
-/
theorem lemmaC4_nonfinite_range_has_zero_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ R.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k)) 0 :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_has_zero_rate_of_not_finiteRange_raw_floorPkComplementError
    μ R hnot_finite

/--
No-positive-rate form of the positive-support C.4 reverse branch.
-/
theorem lemmaC4_nonfinite_range_no_positive_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_rawSourcePositiveSupportIntervalModel_tieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRange_raw_floorPkComplementError
    μ R hnot_finite

/--
Finite-step reverse branch under the named positive-support source model.
For monotone success probabilities, finite range implies the finite-step
interval convention, so a non-finite-step rule is also non-finite-range.
-/
theorem lemmaC4_nonfinite_step_has_zero_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finiteStep :
      ¬ lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ R.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k)) 0 := by
  have hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi := by
    intro hfinite
    exact hnot_finiteStep
      (lemmaC4FiniteStepOnIoo_of_monotone_finiteRangeOnIoo
        R.hprob_mono hfinite)
  exact
    lemmaC4_nonfinite_range_has_zero_rate_of_positive_support_assumptions
      μ R hnot_finite

/--
No-positive-rate form of the finite-step positive-support C.4 reverse branch.
-/
theorem lemmaC4_nonfinite_step_no_positive_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finiteStep :
      ¬ lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate := by
  have hzero :=
    lemmaC4_nonfinite_step_has_zero_rate_of_positive_support_assumptions
      μ R hnot_finiteStep
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ R.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k))
      hzero

/--
Non-piecewise reverse branch under the named positive-support source model.
The only semantic input is that finite-range rules count as piecewise for the
chosen paper predicate.
-/
theorem lemmaC4_nonpiecewise_has_zero_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi →
        isPiecewiseConstantOn R.successProb R.lo R.hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn R.successProb R.lo R.hi) :
    HasExponentialRate
      (lemmaC4TieErasedSourceWbar μ R.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k)) 0 := by
  have hnot_finite :
      ¬ lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi := by
    intro hfinite
    exact hnot_piecewise (hfinite_to_piecewise hfinite)
  exact
    lemmaC4_nonfinite_range_has_zero_rate_of_positive_support_assumptions
      μ R hnot_finite

/--
No-positive-rate form of the non-piecewise positive-support C.4 reverse branch.
-/
theorem lemmaC4_nonpiecewise_no_positive_rate_of_positive_support_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (isPiecewiseConstantOn : (ℝ → ℝ) → ℝ → ℝ → Prop)
    (hfinite_to_piecewise :
      lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi →
        isPiecewiseConstantOn R.successProb R.lo R.hi)
    (hnot_piecewise :
      ¬ isPiecewiseConstantOn R.successProb R.lo R.hi) :
    ∀ rate : ℝ, 0 < rate →
      ¬ ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate := by
  have hzero :=
    lemmaC4_nonpiecewise_has_zero_rate_of_positive_support_assumptions
      μ R isPiecewiseConstantOn hfinite_to_piecewise hnot_piecewise
  exact
    lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate
      (lemmaC4TieErasedSourceWbar μ R.weight
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k))
      hzero

/--
Lemma C.4 selected-integral realization assumption.

This is weaker than pointwise equality with the canonical selected pullback
source.  It asks only for the source weighted integrand to agree with the
selected finite-level integrand on selected cross-level support, and for the
weighted source integrand to vanish off selected support inside the strict
ordered-pair source domain.
-/
-- audit-premise: H : assumption_lemmaC4_selected_integral_realization μ R S
abbrev assumption_lemmaC4_selected_integral_realization
    (μ : Measure ℝ)
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) : Prop :=
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
        (theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono)

/--
Pointwise version of the selected-integral realization assumption.

This is the preferred proof target for a concrete raw source model: prove
weighted integrand agreement on selected cross-level support and prove the
weighted source integrand is zero off selected support inside the strict
ordered-pair domain.
-/
-- audit-premise: H : assumption_lemmaC4_selected_integral_pointwise_realization μ R S
def assumption_lemmaC4_selected_integral_pointwise_realization
    (μ : Measure ℝ)
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) : Prop :=
  ∀ (levels : Fin (S.m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels),
    BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate →
      (∀ k q,
        theorem31SelectedSourceCoordinateMap q ∈
          theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono →
        R.weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k =
          S.weight (theorem31SelectedSourceCoordinateMap q) *
            theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
              S.sampleRate levels hlevels k
              (theorem31SelectedSourceCoordinateMap q)) ∧
      (∀ k q, q ∈ AppliedModelingLib.strictUpperPairSet →
        theorem31SelectedSourceCoordinateMap q ∉
          theorem31SelectedSourceSupport μ (m := S.m) S.cut S.hmono →
        R.weight q *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k = 0)

/--
The pointwise selected-realization fields imply the structured
selected-integral realization assumption.
-/
theorem assumption_lemmaC4_selected_integral_realization_of_pointwise
    (μ : Measure ℝ) [SFinite μ]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_pointwise_realization μ R S) :
    assumption_lemmaC4_selected_integral_realization μ R S := by
  intro levels hlevels heq
  rcases H levels hlevels heq with ⟨hon, hoff⟩
  exact
    lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_pointwise
      μ (m := S.m) S.cut S.hmono S.sampleRate levels hlevels
      R.weight S.weight
      (fun k : ℕ => fun q : ℝ × ℝ =>
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel R.successProb R.hprob0 R.hprob1)
          R.sampleRate q.1 q.2 k)
      hon hoff

/--
Lemma C.4 selected-pullback source convention.

This sufficient source convention identifies the raw source with the canonical
selected finite-level pullback.  It is stronger than the selected-integral
realization above because the kernel equality includes tie-erasure and
off-selected-support zeros pointwise.
-/
-- audit-premise: H : assumption_lemmaC4_selected_pullback_source_convention μ R S
abbrev assumption_lemmaC4_selected_pullback_source_convention
    (μ : Measure ℝ) [SFinite μ]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ) : Prop :=
  LemmaC4RawSourceSelectedPullbackConvention μ R S

/--
The selected-pullback source convention implies the pointwise
selected-realization fields.
-/
theorem assumption_lemmaC4_selected_integral_pointwise_realization_of_selected_pullback_source_convention
    (μ : Measure ℝ) [SFinite μ]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_pullback_source_convention μ R S) :
    assumption_lemmaC4_selected_integral_pointwise_realization μ R S := by
  intro levels hlevels _heq
  refine ⟨?_, ?_⟩
  · intro k q hq
    calc
      R.weight q *
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k =
        theorem31SelectedPullbackSourceWeight S.weight q *
          theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut S.hmono
            S.sampleRate levels hlevels k q := by
          rw [H.weight_eq q, H.kernel_eq levels hlevels k q]
      _ = S.weight (theorem31SelectedSourceCoordinateMap q) *
          theorem31SelectedSourceKernel μ (m := S.m) S.cut S.hmono
            S.sampleRate levels hlevels k
            (theorem31SelectedSourceCoordinateMap q) := by
          simp [theorem31SelectedPullbackSourceWeight,
            theorem31SelectedPullbackSourceKernel, hq]
  · intro k q _hstrict hq
    calc
      R.weight q *
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel R.successProb R.hprob0 R.hprob1)
            R.sampleRate q.1 q.2 k =
        theorem31SelectedPullbackSourceWeight S.weight q *
          theorem31SelectedPullbackSourceKernel μ (m := S.m) S.cut S.hmono
            S.sampleRate levels hlevels k q := by
          rw [H.weight_eq q, H.kernel_eq levels hlevels k q]
      _ = 0 := by
          simp [theorem31SelectedPullbackSourceWeight,
            theorem31SelectedPullbackSourceKernel, hq]

/--
The selected-pullback source convention implies the weaker selected-integral
realization assumption.
-/
theorem assumption_lemmaC4_selected_integral_realization_of_selected_pullback_source_convention
    (μ : Measure ℝ) [SFinite μ]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_pullback_source_convention μ R S) :
    assumption_lemmaC4_selected_integral_realization μ R S := by
  exact
    assumption_lemmaC4_selected_integral_realization_of_pointwise μ R S
      (assumption_lemmaC4_selected_integral_pointwise_realization_of_selected_pullback_source_convention
        μ R S H)

/--
Lemma C.4 forward branch under the named selected-integral realization
assumption.  This exposes the positive-rate construction directly, without
also packaging the reverse branch into an iff.
-/
theorem lemmaC4_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_realization μ R S) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_selected_realization
    μ R S H

/--
Lemma C.4 forward branch under the named pointwise selected-realization
fields.
-/
theorem lemmaC4_exists_positive_exponential_rate_of_pointwise_selected_realization_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_pointwise_realization μ R S) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S (assumption_lemmaC4_selected_integral_realization_of_pointwise μ R S H)

/--
Lemma C.4 forward branch under the selected-pullback source convention.
-/
theorem lemmaC4_exists_positive_exponential_rate_of_selected_pullback_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_pullback_source_convention μ R S) :
    ∃ rate : ℝ, 0 < rate ∧
      ExponentialRateCertificate
        (lemmaC4TieErasedSourceWbar μ R.weight
          (fun k : ℕ => fun q : ℝ × ℝ =>
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel R.successProb R.hprob0 R.hprob1)
              R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S
      (assumption_lemmaC4_selected_integral_realization_of_selected_pullback_source_convention
        μ R S H)

/--
Lemma C.4 finite-range bridge under the named positive-support and
selected-integral realization assumptions.
-/
theorem lemmaC4_finite_range_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_realization μ R S) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  ⟨fun _hfinite =>
      lemmaC4_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
        μ R S H,
    fun hcert => by
      by_contra hnot_finite
      rcases hcert with ⟨rate, hrate, hcert⟩
      exact
        (lemmaC4_nonfinite_range_no_positive_rate_of_positive_support_assumptions
          μ R hnot_finite rate hrate) hcert⟩

/--
Lemma C.4 finite-step bridge under the named positive-support and
selected-integral realization assumptions.
-/
theorem lemmaC4_finite_step_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_realization μ R S) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  ⟨fun _hfiniteStep =>
      lemmaC4_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
        μ R S H,
    fun hcert => by
      by_contra hnot_finiteStep
      rcases hcert with ⟨rate, hrate, hcert⟩
      exact
        (lemmaC4_nonfinite_step_no_positive_rate_of_positive_support_assumptions
          μ R hnot_finiteStep rate hrate) hcert⟩

/--
Lemma C.4 finite-range bridge under pointwise selected-realization fields.
-/
theorem lemmaC4_finite_range_iff_exists_positive_exponential_rate_of_pointwise_selected_realization_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_pointwise_realization μ R S) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_finite_range_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S (assumption_lemmaC4_selected_integral_realization_of_pointwise μ R S H)

/--
Lemma C.4 finite-step bridge under pointwise selected-realization fields.
-/
theorem lemmaC4_finite_step_iff_exists_positive_exponential_rate_of_pointwise_selected_realization_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_integral_pointwise_realization μ R S) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_finite_step_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S (assumption_lemmaC4_selected_integral_realization_of_pointwise μ R S H)

/--
Lemma C.4 finite-range bridge under the named positive-support and
selected-pullback source assumptions.
-/
theorem lemmaC4_finite_range_iff_exists_positive_exponential_rate_of_selected_pullback_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_pullback_source_convention μ R S) :
    lemmaC4FiniteRangeOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_finite_range_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S
      (assumption_lemmaC4_selected_integral_realization_of_selected_pullback_source_convention
        μ R S H)

/--
Lemma C.4 finite-step bridge under the named positive-support and
selected-pullback source assumptions.
-/
theorem lemmaC4_finite_step_iff_exists_positive_exponential_rate_of_selected_pullback_assumptions
    (μ : Measure ℝ) [SFinite μ] [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (S : LemmaC4AppropriateFiniteLevelsWeightedModel μ)
    (H : assumption_lemmaC4_selected_pullback_source_convention μ R S) :
    lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi ↔
      ∃ rate : ℝ, 0 < rate ∧
        ExponentialRateCertificate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (fun k : ℕ => fun q : ℝ × ℝ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel R.successProb R.hprob0 R.hprob1)
                R.sampleRate q.1 q.2 k)) rate :=
  lemmaC4_finite_step_iff_exists_positive_exponential_rate_of_selected_integral_realization_assumptions
    μ R S
      (assumption_lemmaC4_selected_integral_realization_of_selected_pullback_source_convention
        μ R S H)

end

end GJ19OptimalBinaryRatingSystems
