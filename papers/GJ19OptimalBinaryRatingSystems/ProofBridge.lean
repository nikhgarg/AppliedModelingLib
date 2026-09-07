import GJ19OptimalBinaryRatingSystems.AuditInterface
/-!
# Human-Facing Paper Interface: Designing Optimal Binary Rating Systems
Direct paper-facing review surface for the source-curated rows in `status.json`.
Proofs delegate to the audited GJ19 development imported above.
-/
namespace GJ19OptimalBinaryRatingSystems.ProofBridge
noncomputable section
open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/--
Paper-facing finite binary-rating design for the Theorem 3.1 example branches:
an interval cutpoint rule together with endpoint-normalized binary levels.
-/
structure Theorem31FiniteBinaryRatingDesign (M : ℕ) where
  cutpoints : ℕ → ℝ
  endpointLevels : Fin (M + 2) → ℝ

/-- The equispaced/canonical endpoint design used in the finite Theorem 3.1 examples. -/
def theorem31CanonicalUniformEndpointDesign
    (M : ℕ) : Theorem31FiniteBinaryRatingDesign M where
  cutpoints := equispacedIntervalCutpoint M
  endpointLevels := canonicalUniformEqualizedEndpointLevels M

/-- Feasible finite Kendall example designs. -/
def theorem31KendallFiniteDesignFeasible
    (M : ℕ) (design : Theorem31FiniteBinaryRatingDesign M) : Prop :=
  intervalCutpointsEndpointFeasible M design.cutpoints ∧
    BinaryEndpointLevelVector design.endpointLevels

/-- Feasible finite Spearman example designs. -/
def theorem31SpearmanFiniteDesignFeasible
    (M : ℕ) (design : Theorem31FiniteBinaryRatingDesign M) : Prop :=
  monotoneIntervalCutpointsEndpointFeasible M design.cutpoints ∧
    BinaryEndpointLevelVector design.endpointLevels

/-- Kendall primary value for a finite Theorem 3.1 design. -/
noncomputable def theorem31KendallFiniteDesignValue
    (M : ℕ) (design : Theorem31FiniteBinaryRatingDesign M) : ℝ :=
  kendallConstantWeightOrderedPairIntervalObjective M design.cutpoints

/-- Spearman primary value for a finite Theorem 3.1 design. -/
noncomputable def theorem31SpearmanFiniteDesignValue
    (M : ℕ) (design : Theorem31FiniteBinaryRatingDesign M) : ℝ :=
  spearmanLinearWeightOrderedPairIntervalObjective M design.cutpoints

/-- Endpoint large-deviation rate objective for a finite Theorem 3.1 design. -/
noncomputable def theorem31FiniteDesignEndpointRate
    (M : ℕ) (design : Theorem31FiniteBinaryRatingDesign M) : ℝ :=
  binaryEndpointAwareAdjacentRateObjective design.endpointLevels
    (fun _ : Fin (M + 2) => (1 : ℝ))

/-- KL divergence formula displayed below Theorem 3.1. -/
theorem definition_bernoulli_kl_formula (a b : ℝ) :
    paperBernoulliKL a b =
      a * Real.log (a / b) +
        (1 - a) * Real.log ((1 - a) / (1 - b)) :=
  sourceBernoulliKL_eq_formula a b
/--
Support-safe Bernoulli KL convention used when the optimization threshold is
treated as an extended finite-support rate.
-/
theorem definition_bernoulli_kl_top_formula (a b : ℝ) :
    paperBernoulliKLTop a b =
      if 0 ≤ a ∧ a ≤ 1 then
        (paperBernoulliKL a b : WithTop ℝ)
      else
        ⊤ :=
  sourceBernoulliKLTop_eq_source_formula a b
/--
Theorem 3.1 rate expression for adjacent binary-rating levels.

Source status: exact source formula, with the threshold minimization encoded as
an infimum over real thresholds.
-/
theorem theorem31_adjacent_binary_rate_formula
    (gHi gLo tHi tLo : ℝ) :
    paperAdjacentBinaryRatingRate gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        gHi * paperBernoulliKL a tHi +
          gLo * paperBernoulliKL a tLo) :=
  adjacentBinaryRatingRate_eq_source_formula gHi gLo tHi tLo
/--
Support-safe Theorem 3.1 adjacent-rate expression. This is the convention to
use for future finite-support LDP endpoints, so thresholds outside `[0,1]`
cannot create misleading real-valued rates.

Source status: support-safe Lean convention for the same source formula.
-/
theorem theorem31_adjacent_binary_rate_top_formula
    (gHi gLo tHi tLo : ℝ) :
    paperAdjacentBinaryRatingRateTop gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        withTopRealScale gHi (paperBernoulliKLTop a tHi) +
          withTopRealScale gLo (paperBernoulliKLTop a tLo)) :=
  adjacentBinaryRatingRateTop_eq_source_formula gHi gLo tHi tLo
/--
Lemma 3.1 closed-form adjacent-rate expression.

Source status: exact displayed Lemma 3.1 algebraic formula.
-/
theorem lemma31_closed_adjacent_rate_formula
    (gLo gHi tLo tHi : ℝ) :
    paperAdjacentBinaryClosedRate gLo gHi tLo tHi =
      -(gLo + gHi) *
        Real.log
          (((1 - tLo) ^ (gLo / (gLo + gHi))) *
              ((1 - tHi) ^ (gHi / (gLo + gHi))) +
            (tLo ^ (gLo / (gLo + gHi))) *
              (tHi ^ (gHi / (gLo + gHi)))) :=
  adjacentBinaryRatingClosedRate_eq_source_formula gLo gHi tLo tHi
/--
Finite Lemma 3.1 for more than one interior level: positive adjacent sample
rates determine a unique endpoint-normalized binary level vector whose adjacent
closed rates are all equal.
-/
theorem lemma31_forward_clipped_equalized_rates_exist_unique
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
    hm sampleRate hsample_pos
/--
Finite Lemma 3.1 maximin theorem: under the paper's endpoint convention and
positive adjacent sample rates, an endpoint-normalized level vector that
equalizes all adjacent rates maximizes the finite worst-adjacent rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
    hm sampleRate candidate hcandidate hsample_high hsample_low heq
/--
Finite Lemma 3.1 equalization equivalence: once an equalized endpoint vector
exists, a feasible endpoint-normalized vector maximizes the finite
worst-adjacent rate iff it pairwise equalizes all adjacent rates.

Source status: finite endpoint-normalized form of Lemma 3.1's equalization
criterion.
-/
theorem lemma31_endpoint_aware_maximizer_iff_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq_candidate :
      BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        alt ↔
      BinaryEndpointAwareAdjacentRatesEqualize alt sampleRate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_iff_pairwise_equalized
    hm sampleRate candidate alt hcandidate halt
    hsample_high hsample_low heq_candidate
/--
Theorem 3.1 two-stage optimality logic: maximizing the limiting value and then
maximizing the large-deviation rate on that limiting-value fiber gives
lexicographic optimality for the paper's asymptotic-value/rate criterion.

Source status: exact optimization-ordering logic for the Theorem 3.1
value-then-rate criterion.
-/
theorem paper_theorem31_two_stage_lexicographic_optimality
    {Design : Type*} (feasible : Design → Prop)
    (limitingValue rate : Design → ℝ) (candidate : Design)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn feasible limitingValue candidate)
    (hrate :
      ∀ alternative, feasible alternative →
        limitingValue alternative = limitingValue candidate →
          rate alternative ≤ rate candidate) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      feasible limitingValue rate candidate :=
  GJ19OptimalBinaryRatingSystems.theorem31_two_stage_lexicographic_optimality
    feasible limitingValue rate candidate hvalue hrate
/-- Lexicographic optimization of nontrivial-cell integrable weight and the uniform-matching adjacent-rate formula. -/
abbrev paper_exists_nontrivialCellWeight_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc
/--
Weighted Theorem C.1 Laplace-principle skeleton: bounded nonnegative objective
weights preserve the exponential rate of the weighted integral when the
near-essential-minimizer sets contain positive-measure regions where the
weight is uniformly positive.

Source status: conditional weighted Laplace-principle skeleton for Theorem C.1.
-/
theorem paper_theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform
/--
Lemma C.3 positive-kernel measurable-partition bridge: componentwise uniform
normalized-log rate limits imply that the weighted partitioned continuum
error integral decays at the minimum component exponent.

Source status: formalized C.3 aggregation bridge from uniform log-rate
convergence to the minimum component exponent.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component] [Nonempty Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε) :
    ∃ minComponent : Component,
      (∀ component, rate minComponent ≤ rate component) ∧
        HasExponentialRate
          (fun k : ℕ =>
            ∫ x in P.support, weight x * kernel k x ∂μ)
          (rate minComponent) := by
  obtain ⟨minComponent, hrate_ge⟩ := Finite.exists_min rate
  exact
    ⟨minComponent, hrate_ge,
      GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
        μ P weight kernel phi rate W hkernel_int hweight_int hWpos
        hweight_nonneg hweight_bound hess hweighted_near hkernel_pos
        huniform_log minComponent hrate_ge⟩
/--
Corrected Lemma C.4 content with both valid source branches and no supplied
conclusion-shaped realization.  The first conjunct treats an arbitrary finite
strict endpoint chain: Lean selects its least adjacent exponent, proves that
exponent is positive, and transports the selected-rectangle integral to the
canonical tie-erased pullback source.  The second conjunct treats an arbitrary
non-finite-step monotone positive-support source: its defined tie-erased gap
has rate zero and no positive exponential-rate certificate.

These branches intentionally quantify over their respective source objects.
The printed proof silently switches from the raw strict-pair complement to a
tie-erased selected-cell objective, so it does not justify a literal iff for
one unchanged kernel without an additional realization bridge.
-/
theorem paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate
    (μ : Measure ℝ) [SFinite μ] [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [(μ.prod μ).IsOpenPosMeasure]
    {m : ℕ} (hm : 0 < m)
    (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (levels sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
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
            component))
    (lo hi : ℝ)
    (R : assumption_lemmaC4_positive_support_interval_model μ)
    (hnot_finiteStep :
      ¬ lemmaC4FiniteStepOnIoo R.successProb R.lo R.hi) :
    ((lemmaC4FiniteRangeOnIoo (cutpointStepSuccessProb cut levels) lo hi ∧
      (∃ rate : ℝ,
          0 < rate ∧
            AppliedModelingLib.Probability.ExponentialRateCertificate
              (lemmaC4TieErasedSourceWbar μ
                (theorem31SelectedPullbackSourceWeight weight)
                (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
                  sampleRate levels hlevels)) rate)) ∧
      (HasExponentialRate
          (lemmaC4TieErasedSourceWbar μ R.weight
            (lemmaC4RawSourcePbarKernel R)) 0 ∧
        ∀ rate : ℝ, 0 < rate →
          ¬ AppliedModelingLib.Probability.ExponentialRateCertificate
            (lemmaC4TieErasedSourceWbar μ R.weight
              (lemmaC4RawSourcePbarKernel R)) rate)) := by
  obtain ⟨minAdjacent, hmin⟩ :=
    Finite.exists_min
      (binaryEndpointAwareAdjacentRate levels sampleRate)
  have hmin_pos :
      0 < binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent :=
    binaryEndpointAwareAdjacentRate_pos hm levels sampleRate hlevels
      (fun i => hsample_pos (adjacentHighIndex i))
      (fun i => hsample_pos (adjacentLowIndex i)) minAdjacent
  have hselected_rate :
      HasExponentialRate
        (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
        (binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent) := by
    simpa only [theorem31SourceWbar] using
      lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_cell_midpoints
        μ hm cut hmono hcut_strict levels sampleRate hlevels hsample_pos
        hsample_mono weight hweight_int hweight_nonneg hweight_cont
        hweight_midpoint_pos minAdjacent hmin
  have hpullback_eq :=
    lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source
      μ (m := m) cut hmono sampleRate levels hlevels weight
  have hpullback_rate :
      HasExponentialRate
        (lemmaC4TieErasedSourceWbar μ
          (theorem31SelectedPullbackSourceWeight weight)
          (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
            sampleRate levels hlevels))
        (binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent) :=
    HasExponentialRate.congr hpullback_eq.symm hselected_rate
  have hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ) := by
    intro component
    exact setIntegral_nonneg_of_ae_restrict (hweight_nonneg component)
  have hselected_nonneg :=
    theorem31SourceWbar_eventually_nonneg μ cut hmono sampleRate levels
      hlevels weight hweight_int hweight_nonneg_integral
  have hpullback_nonneg :
      ∀ᶠ k : ℕ in atTop,
        0 ≤
          lemmaC4TieErasedSourceWbar μ
            (theorem31SelectedPullbackSourceWeight weight)
            (theorem31SelectedPullbackSourceKernel μ (m := m) cut hmono
              sampleRate levels hlevels) k := by
    filter_upwards [hpullback_eq, hselected_nonneg] with k hk hnonneg
    simpa [hk] using hnonneg
  have hzero :=
    lemmaC4_nonfinite_step_has_zero_rate_of_positive_support_assumptions
      μ R hnot_finiteStep
  exact
    ⟨⟨lemmaC4FiniteRangeOnIoo_cutpointStepSuccessProb cut levels lo hi,
        ⟨binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent,
          hmin_pos,
          AppliedModelingLib.Probability.ExponentialRateCertificate.of_has_rate_of_eventually_nonneg_of_pos_rate
            hpullback_rate hmin_pos hpullback_nonneg⟩⟩,
      ⟨hzero,
        lemmaC4_nonfinite_step_no_positive_rate_of_positive_support_assumptions
          μ R hnot_finiteStep⟩⟩
/--
Corollary C.3 first-level lower bound for monotone match functions after
normalizing the first nonzero type rate to one.
-/
theorem corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1) :
    ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointAwareAdjacentRatesEqualize_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    hm hlevels heq hsample_pos hsample_mono hfirst_sample
/--
Theorem 3.2 source-grid calculated-recursion endpoint with finite grid and
depth choices, using the exact-hit early-return convention: for every positive
source tolerance, Lean constructs a positive small grid and finite bisection
depth that give the additive-rate loss and runtime certificate.
-/
theorem theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ} (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq : BinaryEndpointAwareAdjacentRatesEqualize oldLevels fun _ => (1 : ℝ)) :
    ∃ grid,
      0 < grid ∧
        grid < (1 / 5 * binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ => (1 : ℝ))) / 2 ∧
          ∃ L,
            have optimal := uniformDoubledEndpointLevels oldLevels
            have levelTarget := optimal (adjacentLowIndex lastAdjacentIndex)
            have lastLow :=
              (AppliedModelingLib.Optimization.realBisectionRun
                  (AppliedModelingLib.Optimization.realBisectionAboveTarget levelTarget)
                  (L + 1) (1 - 1 / ((2 * m + 1 + 1 : ℕ) : ℝ)) (1 - grid)).2
            have tFirst := optimal (adjacentHighIndex firstAdjacentIndex)
            have target := -Real.log lastLow
            have gridReturned :=
              theorem32BackwardGridLowBisectionLevels (2 * m + 1) L grid
                tFirst target lastLow
            have returned := if levelTarget = lastLow then optimal else gridReturned
            (binaryEndpointAwareAdjacentRateObjective optimal (fun _ => (1 : ℝ)) -
                binaryEndpointAwareAdjacentRateObjective returned (fun _ => (1 : ℝ))) ≤ eps ∧
              nestedBisectionOperationCount M (L + 1) L ≤
                AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    hm oldLevels heps holdLevels holdEq
/--
Definition C.1 source-facing Kendall/Spearman objective formulas: the Kendall
constant-weight and Spearman linear-weight population objectives reduce to the
finite interval-gap objectives used in Lemmas C.11 and C.12.
-/
theorem definitionC1_kendall_spearman_population_objectives
    (M : ℕ) (s : ℕ → ℝ) :
    kendallConstantWeightIntervalObjective M s =
        (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 2) / 2 ∧
      spearmanLinearWeightIntervalObjective M s =
        (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 3) / 6 := by
  constructor <;> rfl
/--
Lemma C.10 Spearman source-integral reduction: for a partition of `[0,1]`,
the ordered interval-pair linear-distance objective equals the cubic gap
objective used in Lemma C.12.

Source status: exact finite source reduction for Lemma C.10.
-/
theorem paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    (M : ℕ) (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s =
      spearmanLinearWeightIntervalObjective M s :=
  GJ19OptimalBinaryRatingSystems.lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    M s h0 hM
/--
Lemma C.11 source-sum form: the ordered constant-weight interval-pair sum in
equation (27) is at most the equispaced partition value.

Source status: exact finite source-sum inequality for Lemma C.11.
-/
theorem paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    (∑ i : Fin M, ∑ j : Fin M,
        if i < j then
          (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
        else 0) ≤
      (1 - (M : ℝ)⁻¹) / 2 :=
  GJ19OptimalBinaryRatingSystems.lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    s h0 hM
/--
Lemma C.12 source-sum form: the ordered linear-distance interval-pair objective
for Spearman's rho is maximized by equispaced cutpoints.
-/
theorem paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
  GJ19OptimalBinaryRatingSystems.lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    s hmono h0 hM
/--
Theorem 3.1 Kendall example branch: equispaced cutpoints and the canonical
uniform equalized endpoint levels are lexicographically optimal for the finite
constant-weight Kendall value/rate problem.

Source status: formalized finite Kendall branch of the source example.
-/
theorem paper_theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (theorem31KendallFiniteDesignFeasible M)
      (theorem31KendallFiniteDesignValue M)
      (theorem31FiniteDesignEndpointRate M)
      (theorem31CanonicalUniformEndpointDesign M) := by
  let hpair :=
    GJ19OptimalBinaryRatingSystems.theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
      hM
  constructor
  · simpa [theorem31KendallFiniteDesignFeasible,
      theorem31CanonicalUniformEndpointDesign] using hpair.1
  · intro design hdesign
    have hpair_design :
        intervalCutpointsEndpointFeasible M design.cutpoints ∧
          BinaryEndpointLevelVector design.endpointLevels := by
      simpa [theorem31KendallFiniteDesignFeasible] using hdesign
    simpa [theorem31KendallFiniteDesignValue,
      theorem31FiniteDesignEndpointRate,
      theorem31CanonicalUniformEndpointDesign] using
        hpair.2 (design.cutpoints, design.endpointLevels) hpair_design
/--
Theorem 3.1 Spearman example branch: equispaced cutpoints and the canonical
uniform equalized endpoint levels are lexicographically optimal for the finite
linear-weight Spearman value/rate problem.

Source status: formalized finite Spearman branch of the source example.
-/
theorem paper_theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (theorem31SpearmanFiniteDesignFeasible M)
      (theorem31SpearmanFiniteDesignValue M)
      (theorem31FiniteDesignEndpointRate M)
      (theorem31CanonicalUniformEndpointDesign M) := by
  let hpair :=
    GJ19OptimalBinaryRatingSystems.theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
      hM
  constructor
  · simpa [theorem31SpearmanFiniteDesignFeasible,
      theorem31CanonicalUniformEndpointDesign] using hpair.1
  · intro design hdesign
    have hpair_design :
        monotoneIntervalCutpointsEndpointFeasible M design.cutpoints ∧
          BinaryEndpointLevelVector design.endpointLevels := by
      simpa [theorem31SpearmanFiniteDesignFeasible] using hdesign
    simpa [theorem31SpearmanFiniteDesignValue,
      theorem31FiniteDesignEndpointRate,
      theorem31CanonicalUniformEndpointDesign] using
        hpair.2 (design.cutpoints, design.endpointLevels) hpair_design
/--
Theorem B.1 closeout route from the paper's quantile-floor source
representation, finite optimality, and uniform convergence of interval
quantile maps.  The selector window is derived from uniform convergence and
C.5, rather than assumed separately.
-/
theorem paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (quantileLimit : ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ (m : ℕ) (θ : ℝ), betaSeq (m + 2) θ = levels m (levelIndex m θ))
    (hoptimal :
      ∀ m : ℕ,
        AppliedModelingLib.Optimization.IsMaximizerOn BinaryEndpointLevelVector
          (fun xs => binaryEndpointAwareAdjacentRateObjective xs (fun _ => (1 : ℝ)))
          (levels m))
    (hlevelIndex_val :
      ∀ m : ℕ, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        (levelIndex m θ).val =
          min ⌊((m + 2 : ℕ) : ℝ) * quantileSeq (m + 2) θ⌋₊ (m + 1))
    (hquantile_range :
      ∀ m : ℕ, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        quantileSeq (m + 2) θ ∈ Set.Icc (0 : ℝ) 1)
    (hquantile :
      TendstoUniformlyOn quantileSeq quantileLimit Filter.atTop
        (Set.Icc (0 : ℝ) 1)) :
    theoremB1UniformOptimalSubsequencePrincipleTo betaSeq quantileSeq quantileLimit :=
  GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh
    betaSeq quantileSeq quantileLimit levels levelIndex hrepr hoptimal
    hlevelIndex_val hquantile_range hquantile
/--
Corollary C.4 canonical optimal equispaced branch: for the canonical
finite-rate-optimal Kendall/Spearman representative, every dyadic source
subsequence has a uniform limit on `[0,1]`.

Source status: formalized canonical representative of the existential
Kendall/Spearman Corollary C.4 conclusion.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector
    C
/--
Lemma B.2 with the source's two-stage limit made explicit.  Literal
random-question IID observations derive the fixed-`L` empirical tracking, and
the conclusion then quantifies `eventually L` followed by the corresponding
`eventually N`; no tracking conclusion is supplied as a premise.
-/
abbrev paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking :=
  @GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_ae_iterated_uniform_of_random_question_iid

/--
Corrected Lemma B.3 with both empirical response tracking and score-rank
recovery derived from literal IID observations.  Strict aggregate-score
identifiability is explicit, and the printed `L`-then-`N` selection order is
retained in the conclusion.
-/
abbrev paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking :=
  @GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_ae_iterated_uniform_and_rank_of_random_question_iid
/--
Theorem 3.1 / Lemma C.3 adjacent-dominance step: for monotone matching-rate
lower bounds and monotone binary levels, every wider same-low comparison is
dominated by the adjacent comparison.
-/
theorem paper_theorem31_monotone_chain_adjacent_rate_le_nonadjacent_rate
    {sampleRate successProb : ℕ → ℝ} {i j : ℕ}
    (hsample_pos : ∀ n, 0 < sampleRate n)
    (hsample_mono : Monotone sampleRate)
    (hprob_mono : Monotone successProb)
    (hprob_i_pos : 0 < successProb i)
    (hprob_j_lt_one : successProb j < 1)
    (hij : i + 1 ≤ j) :
    weightedBernoulliClosedThresholdRate (sampleRate (i + 1)) (sampleRate i)
        (successProb (i + 1)) (successProb i) ≤
      weightedBernoulliClosedThresholdRate (sampleRate j) (sampleRate i)
        (successProb j) (successProb i) :=
  GJ19OptimalBinaryRatingSystems.theorem31_monotone_chain_adjacent_rate_le_nonadjacent_rate
    hsample_pos hsample_mono hprob_mono hprob_i_pos hprob_j_lt_one hij
/--
Theorem 3.1 / Lemma C.3 endpoint-aware adjacent-dominance package: every wider
finite real-rate ordered pair, except the pure bottom-to-top source-endpoint
case, is dominated by an adjacent endpoint-aware comparison.
-/
theorem paper_theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
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
    (low high : Fin (m + 2))
    (hordered : low.val + 1 ≤ high.val)
    (hnot_bottom_to_top : low.val ≠ 0 ∨ high.val ≠ m + 1) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate low high :=
  GJ19OptimalBinaryRatingSystems.theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
    sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
    hprob_pos_of_not_first hprob_lt_one_of_not_last low high hordered
    hnot_bottom_to_top
/--
The source binary-rating model has Bernoulli MGF `(1-t)+t exp z`.

Source status: direct paper-facing binary-rating MGF formula row.
-/
theorem binary_rating_model_mgf_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).mgf θ z =
      (1 - successProb θ) + successProb θ * Real.exp z :=
  binaryRatingModel_mgf_eq successProb hprob0 hprob1 θ z
/--
The source binary-rating model has Bernoulli log-MGF formula.

Source status: direct paper-facing binary-rating log-MGF formula row.
-/
theorem binary_rating_model_log_mgf_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).logMGF θ z =
      Real.log ((1 - successProb θ) + successProb θ * Real.exp z) :=
  binaryRatingModel_logMGF_eq successProb hprob0 hprob1 θ z
/--
Derivative of the source binary-rating log-MGF.

Source status: direct paper-facing log-MGF derivative formula row.
-/
theorem binary_rating_model_log_mgf_derivative_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (binaryRatingModel successProb hprob0 hprob1).logMGF θ t)
      (successProb θ * Real.exp z /
        ((1 - successProb θ) + successProb θ * Real.exp z)) z :=
  binaryRatingModel_logMGF_hasDerivAt successProb hprob0 hprob1 θ z
/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from common log-MGF derivative witnesses.

Source status: direct paper-facing pairwise threshold-rate certificate row.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_derivatives
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz hderiv_hi hderiv_lo
/--
Interior binary-model rate function equals the Bernoulli KL formula used in
the paper.

Source status: direct paper-facing Bernoulli-KL rate-function formula row.
-/
theorem binary_rating_model_rate_function_is_bernoulli_kl
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunction θ a =
      paperBernoulliKL a (successProb θ) :=
  binaryRatingModel_rateFunction_eq_sourceBernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1
/--
Interior support-safe binary-model rate function equals the Bernoulli KL
formula used in the paper.

Source status: direct paper-facing support-safe Bernoulli-KL rate-function formula row.
-/
theorem binary_rating_model_rate_function_top_is_bernoulli_kl
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunctionTop θ a =
      (paperBernoulliKL a (successProb θ) : WithTop ℝ) :=
  binaryRatingModel_rateFunctionTop_eq_sourceBernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1
/--
Interior pairwise support-safe binary rate objective equals the weighted
two-Bernoulli KL threshold rate.

Source status: direct paper-facing pairwise threshold-rate objective formula row.
-/
theorem binary_rating_pairwise_rate_objective_top_is_threshold_kl_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).pairwiseRateObjectiveTop
        sampleRate hi lo a =
      (twoBernoulliThresholdRate (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) a : WithTop ℝ) :=
  binaryRatingModel_pairwiseRateObjectiveTop_eq_source_threshold_rate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo ha0 ha1
/--
For two interior binary-rating levels, the support-safe threshold rate equals
the closed weighted Bernoulli rate used in the adjacent-rate analysis.

Source status: direct paper-facing closed weighted threshold-rate formula row.
-/
theorem binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hG : sampleRate hi + sampleRate lo ≠ 0) :
    pairwiseSellerThresholdRateTop
        (binaryRatingModel successProb hprob0 hprob1)
        sampleRate hi lo =
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) : WithTop ℝ) :=
  binaryRatingModel_pairwiseThresholdRateTop_eq_closed_weighted_rate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo hgHi hgLo hG
/-- Lemma C.5 doubled-chain constructor for uniform matching. -/
def lemmaC5_uniform_doubled_endpoint_levels {m : ℕ}
    (oldLevels : Fin (m + 2) → ℝ) : Fin ((2 * m + 1) + 2) → ℝ :=
  uniformDoubledEndpointLevels oldLevels
/-- Lemma C.5 doubled chain: even refined indices copy old levels. -/
theorem lemmaC5_uniform_doubled_endpoint_levels_even
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        ⟨2 * i.val, by omega⟩ = oldLevels i :=
  uniformDoubledEndpointLevels_even oldLevels i
/--
Lemma C.5 doubled chain: first odd index has the endpoint split formula.

Source status: direct paper-facing Lemma C.5 first-odd endpoint formula row.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_first_odd
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (⟨1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliFirstEndpointEqualSplit
        (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :=
  uniformDoubledEndpointLevels_first_odd oldLevels
/--
Lemma C.5 doubled chain: last odd index has the endpoint split formula.

Source status: direct paper-facing Lemma C.5 last-odd endpoint formula row.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_last_odd
    {m : ℕ} (hm : 0 < m) (oldLevels : Fin (m + 2) → ℝ) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliLastEndpointEqualSplit
        (oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :=
  uniformDoubledEndpointLevels_last_odd hm oldLevels
/--
Lemma C.5 global equalization certificate: old uniform equalized adjacent rates
imply equalized adjacent rates for the explicit doubled chain.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_equalizes
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) :=
  uniformDoubledEndpointLevels_equalizes hm hold holdEq
/--
Corollary C.2 rate consequence: for endpoint-normalized uniform equalized
level vectors with `N+1` adjacent intervals, the common last adjacent rate
tends to zero.
-/
theorem paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAwareAdjacentRate (levels N)
          (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((N + 1) + 1)))
      atTop (nhds 0) :=
  GJ19OptimalBinaryRatingSystems.corollaryC2_uniform_equalized_last_rate_tendsto_zero
    levels hlevels heq
/--
Corollary C.2 mesh consequence: for endpoint-normalized uniform equalized
level vectors, the largest adjacent grid width tends to zero.
-/
theorem paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N))
      atTop (nhds 0) :=
  GJ19OptimalBinaryRatingSystems.corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    levels hlevels heq
/--
Lemma C.6 finite-chain endpoint consequence: if the last adjacent interval is
no wider than every adjacent interval, then the penultimate endpoint level is
at least `1 - 1 / (number of adjacent intervals)`.
-/
theorem lemmaC6_penultimate_level_ge_one_sub_inv_of_width_minimal
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (hlast_width :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    hlevels hlast_width
/--
Uniform-matching Lemma C.6 endpoint lower bound: equalized adjacent rates under
uniform matching imply the penultimate level is at least
`1 - 1 / (number of adjacent intervals)`.
-/
theorem lemmaC6_uniform_penultimate_level_ge_one_sub_inv_of_equalized_rates
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
    hm hlevels heq
/--
Theorem 3.2 approximation certificate with the Lemma C.6 last-level lower
bound derived from the width-minimality condition. The remaining explicit
lower-bound input is the first-level bound supplied in the source by
Corollary C.3.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_width_minimal
    {m : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar firstLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_width_minimal
    hm optimal returned sampleRate hgLast_pos heps hoptimal_levels
    hlast_width hfirstLower_pos hfirstLower hdelta hoptimal hlast hgrid
/--
Lemma C.7 algebraic endpoint-refinement step: under uniform matching, the
source's refinement endpoint `(1 + sqrt t_last) / 2` has negative-log rate at
least one fifth of the previous equalized last-adjacent rate.
-/
theorem lemmaC7_uniform_refined_last_rate_ge_one_fifth
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {refinedLastLow : ℝ}
    (hrefined :
      refinedLastLow =
        (1 +
          Real.sqrt
            (levels
              (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) ≤
      -Real.log refinedLastLow :=
  BinaryEndpointLevelVector_uniform_refined_last_rate_ge_one_fifth
    hm hlevels heq hrefined
/--
Lemma C.7 objective-rate comparison in certificate form: if a refined uniform
equalized chain has the source's refined last endpoint, its worst-adjacent
rate is at least one fifth of the old equalized worst-adjacent rate.
-/
theorem lemmaC7_uniform_refined_objective_rate_ge_one_fifth
    {mOld mNew : ℕ} (hmOld : 0 < mOld) (hmNew : 0 < mNew)
    {oldLevels : Fin (mOld + 2) → ℝ}
    {newLevels : Fin (mNew + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hnewLevels : BinaryEndpointLevelVector newLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (mOld + 2) => (1 : ℝ)))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)))
    (hrefined :
      newLevels (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1))) =
        (1 +
          Real.sqrt
            (oldLevels
              (adjacentLowIndex (lastAdjacentIndex : Fin (mOld + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)) :=
  BinaryEndpointLevelVector_uniform_refined_objective_rate_ge_one_fifth
    hmOld hmNew holdLevels hnewLevels holdEq hnewEq hrefined
/--
Lemma C.7 objective-rate comparison for the explicit C.5 doubled chain, with
the doubled-chain feasibility and equalization certificates derived internally.
-/
theorem lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) :=
  uniformDoubledEndpointLevels_objective_rate_ge_one_fifth_old_objective_closed
    hm holdLevels holdEq
/--
Lemma C.8 endpoint step: a lower bound on the first endpoint-aware rate gives
a linear lower bound on the first interior level under uniform matching.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_first_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_first :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_first_rate_lower
    hm hlevels hlower0 hlower1 hlower_le_first
/--
Lemma C.8 endpoint step in equalized form: under uniform equalized adjacent
rates, a lower bound on the last adjacent rate gives the same linear lower
bound on the first interior level.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_equalized_last_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_last :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_last_rate_lower
    hm hlevels heq hlower0 hlower1 hlower_le_last
/--
Lemma C.8 endpoint step in equalized objective form: under uniform equalized
adjacent rates, a lower bound on the finite worst-adjacent objective gives a
linear lower bound on the first interior level.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_objective :
      lower ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    hm hlevels heq hlower0 hlower1 hlower_le_objective
/--
Lemma C.9 runtime core for Algorithm 1: the source-shaped NestedBisection
operation count is bounded by the reusable nested-bisection closed form once
the outer and inner bisection iteration counts are bounded by `L + 1` and `L`.
-/
theorem lemmaC9_nested_bisection_operation_count_le_stepBound
    {M L outerSteps innerSteps : ℕ}
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  nestedBisectionOperationCount_le_stepBound houter hinner
/--
Lemma C.9 runtime core in finite quadratic form: if the outer bisection has at
most `L + 1` iterations and each inner bisection has at most `L` iterations,
then the source-shaped NestedBisection operation count is at most
`M * (L + 1)^2`.
-/
theorem lemmaC9_nested_bisection_operation_count_le_mul_succ_sq
    {M L outerSteps innerSteps : ℕ} (hM : 0 < M)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      M * (L + 1) ^ 2 :=
  nestedBisectionOperationCount_le_mul_succ_sq hM houter hinner

/-! ## Direct rows for source-visible definitions and proof steps -/

/--
Equation (1): pairwise ranking accuracy is the probability of the correct
strict ordering minus the probability of the incorrect strict ordering.
Score ties therefore contribute zero, exactly as in the printed definition.

Source status: exact source definition, with the two conditional
probabilities exposed as arguments.
-/
def source_definition_pairwise_accuracy_eq1
    (probabilityCorrect probabilityIncorrect : ℝ) : ℝ :=
  probabilityCorrect - probabilityIncorrect

/--
Equation (2): a positive normalized weight integrates pairwise ranking
accuracy on the strict upper quality triangle of the unit square to give
`W_k`.

Source status: exact source definition, including pointwise positivity and the
printed unit normalization of the weight.
-/
noncomputable def source_definition_weighted_objective_eq2
    (weight pairwiseAccuracy : ℝ → ℝ → ℝ) (Wk : ℝ) : Prop :=
  (∀ θ1 ∈ Set.Icc (0 : ℝ) 1, ∀ θ2 ∈ Set.Ico (0 : ℝ) θ1,
      0 < weight θ1 θ2) ∧
    (∫ θ1 in Set.Icc (0 : ℝ) 1,
      ∫ θ2 in Set.Ico (0 : ℝ) θ1, weight θ1 θ2) = 1 ∧
    Wk = ∫ θ1 in Set.Icc (0 : ℝ) 1,
      ∫ θ2 in Set.Ico (0 : ℝ) θ1,
        weight θ1 θ2 * pairwiseAccuracy θ1 θ2

/--
The source large-deviation rate of `W - W_k`, using the library predicate
whose expansion is `-(1/k) log (W-W_k) → rate`.

Source status: exact source definition when the displayed limit exists.
-/
abbrev source_definition_large_deviation_rate
    (W : ℝ) (Wk : ℕ → ℝ) (rate : ℝ) : Prop :=
  HasExponentialRate (fun k : ℕ => W - Wk k) rate

/--
The finite step-rule design vocabulary: ordered interval cutpoints together
with strictly ordered endpoint-normalized binary levels.

Source status: formalized with the corrected lower endpoint `t₀ = 0`; the
paper's `t₀ = 1` occurrence is the recorded C.5 endpoint typo.
-/
def source_definition_step_rule_partition_levels
    (m : ℕ) (cutpoints : Fin ((m + 2) + 1) → ℝ) (levels : Fin (m + 2) → ℝ) : Prop :=
  cutpoints ∈ sourceStrictCutpointSet (m + 2) ∧
    BinaryEndpointLevelVector levels

/--
The source value-first, convergence-rate-second definition of an optimal
rating rule.

Source status: exact definition of the lexicographic objective; the separate
Theorem 3.1 rows construct optimizers for the GJ19 design domain.
-/
abbrev source_definition_lexicographic_optimality :=
  @AppliedModelingLib.Optimization.IsLexicographicMaximizerOn

/--
Theorem 3.1 equation (3), with the source cell-rate coefficients derived from
the nondecreasing matching function and then substituted into the displayed
adjacent Bernoulli threshold formula.

Source status: exact source equation under ordered cutpoints and monotone
matching, with the two cell-infimum identities proved in the same row.
-/
theorem source_theorem31_adjacent_rate_eq3
    {m : ℕ} (cutpoints : ℕ → ℝ) (g : ℝ → ℝ)
    (j : Fin (m + 1)) (hcut : Monotone cutpoints) (hg : Monotone g)
    (tHi tLo : ℝ) :
    sourceCellMatchingRate cutpoints g (adjacentLowIndex j) =
        g (cutpoints (adjacentLowIndex j).val) ∧
      sourceCellMatchingRate cutpoints g (adjacentHighIndex j) =
        g (cutpoints (adjacentHighIndex j).val) ∧
      paperAdjacentBinaryRatingRate
          (sourceCellMatchingRate cutpoints g (adjacentHighIndex j))
          (sourceCellMatchingRate cutpoints g (adjacentLowIndex j))
          tHi tLo =
        sInf (Set.range fun a : ℝ =>
          sourceCellMatchingRate cutpoints g (adjacentHighIndex j) *
              paperBernoulliKL a tHi +
            sourceCellMatchingRate cutpoints g (adjacentLowIndex j) *
              paperBernoulliKL a tLo) := by
  refine ⟨?_, ?_, ?_⟩
  · exact sourceCellMatchingRate_eq_lower_cutpoint
      cutpoints g (adjacentLowIndex j)
      (hcut (Nat.le_succ _)) (hg.monotoneOn _)
  · exact sourceCellMatchingRate_eq_lower_cutpoint
      cutpoints g (adjacentHighIndex j)
      (hcut (Nat.le_succ _)) (hg.monotoneOn _)
  · exact theorem31_adjacent_binary_rate_formula _ _ tHi tLo

/--
Lemma 3.1 in one source-facing endpoint: positive finite matching rates have a
unique endpoint-normalized equalized vector, and that vector maximizes the
worst adjacent rate.

Source status: exact finite equalization/uniqueness/maximin conclusion, under
the paper's positive matching-rate assumptions.
-/
theorem source_lemma31_equalization_eq4
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
        AppliedModelingLib.Optimization.IsMaximizerOn
          (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
          (fun xs : Fin (m + 2) → ℝ =>
            binaryEndpointAwareAdjacentRateObjective xs sampleRate)
          levels := by
  rcases lemma31_forward_clipped_equalized_rates_exist_unique
      hm sampleRate hsample_pos with ⟨levels, hlevels, hunique⟩
  refine ⟨levels, ⟨hlevels.1, hlevels.2, ?_⟩, ?_⟩
  · apply lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn
      (m := m) (by omega) sampleRate levels hlevels.1
      (r := binaryEndpointAwareAdjacentRate levels sampleRate
        (firstAdjacentIndex : Fin (m + 1)))
    · intro i
      have hraw :=
        hsample_pos (adjacentHighIndex i).val (adjacentHighIndex i).isLt
      rw [binaryEndpointSampleRateNat_of_lt sampleRate
        (adjacentHighIndex i).isLt] at hraw
      exact hraw
    · intro i
      have hraw :=
        hsample_pos (adjacentLowIndex i).val (adjacentLowIndex i).isLt
      rw [binaryEndpointSampleRateNat_of_lt sampleRate
        (adjacentLowIndex i).isLt] at hraw
      exact hraw
    · intro i
      exact hlevels.2 i (firstAdjacentIndex : Fin (m + 1))
  · intro alternative halternative
    exact hunique alternative ⟨halternative.1, halternative.2.1⟩

/--
Theorem B.1 source vocabulary: `q_M(θ)` is the selected cell index divided
by `M`, and `β_M(θ)` is the level attached to that selected cell.

Source status: exact quantile/level representation, with the cell selector
made explicit.
-/
def source_theoremB1_quantile_representation
    (M : ℕ) (cellIndex : ℝ → Fin M) (levels : Fin M → ℝ)
    (quantile beta : ℝ → ℝ) : Prop :=
  (∀ θ : ℝ,
      quantile θ = ((cellIndex θ).val : ℝ) / (M : ℝ)) ∧
    ∀ θ : ℝ, beta θ = levels (cellIndex θ)

/--
Lemma C.1 proof endpoint: the binary log-MGF derivative witnesses construct a
pairwise floor-count threshold-rate LDP certificate.

Source status: formalized conditional only on the explicit derivative,
support, and positive-sampling hypotheses used by the source Cramér argument.
-/
theorem source_lemmaC1_pairwise_error_rate_from_derivatives
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) :
    Nonempty
      (PairwiseThresholdRateTopLdpCertificate
        (binaryRatingModel successProb hprob0 hprob1)
        sampleRate pairHi pairLo) :=
  ⟨binary_rating_pairwise_threshold_rate_certificates_from_derivatives
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    pairHi pairLo hpositive_hi hpositive_lo a z hz hderiv_hi hderiv_lo⟩

/--
Lemma C.2: the source complement ranking-error probability for an interior
ordered Bernoulli pair has the same closed weighted threshold exponent.

Source status: exact pairwise `1 - P_k` exponential-rate certificate.
-/
theorem source_lemmaC2_binary_complement_rate :
    type_of%
      (@GJ19OptimalBinaryRatingSystems.binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair) :=
  @GJ19OptimalBinaryRatingSystems.binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair

/--
Theorem C.1 source Laplace principle: uniform convergence and the
almost-everywhere essential-infimum condition identify the exponential rate
of the unweighted exponential integral.

Source status: exact source theorem in essential-infimum notation.
-/
theorem source_theoremC1_laplace_principle :
    type_of%
      (@GJ19OptimalBinaryRatingSystems.theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf) :=
  @GJ19OptimalBinaryRatingSystems.theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf

/--
Remark C.1 in its auditable form: on the full quality square, the weighted
Laplace conclusion follows once the integrability, essential-infimum,
positive-weight-near-minimizer, and uniform-convergence conditions asserted
by the remark are supplied explicitly.

Source status: formalized with the remark's omitted analytic conditions made
visible as theorem premises.
-/
theorem source_remarkC1_full_square_application_under_explicit_conditions
    (weight : (ℝ × ℝ) → ℝ)
    (phiSeq : ℕ → (ℝ × ℝ) → ℝ) (phi : (ℝ × ℝ) → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : ℝ × ℝ =>
          weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (hWpos : 0 < W)
    (hweight_nonneg :
      ∀ᵐ x ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))), 0 ≤ weight x)
    (hweight_bound :
      ∀ᵐ x ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))), weight x ≤ W)
    (hess :
      HasAEEssentialInfimum
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))) phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))) weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : ℝ × ℝ, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x))
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1))))
      rate :=
  paper_theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform

/--
Remark C.2 in the form used by Lemma 3.1: the weighted Bernoulli separation
rate is jointly continuous at every ordered interior pair, vanishes all along
the diagonal, is positive off the diagonal, and is strictly monotone in each
endpoint while the other endpoint is fixed.

Source status: exact used content.  The paper's phrase "strictly convex in
`t_i,t_{i+1}`, with minima at `t_i=t_{i+1}`" cannot be literal joint strict
convexity because the entire diagonal consists of minima; the checked
diagonal-zero clause below makes that minor prose overstatement explicit.
-/
theorem source_remarkC2_weighted_kl_separation_monotonicity
    {gHi gLo pLo pHi : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_hi : pLo < pHi) (hpHi1 : pHi < 1) :
    ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
        (pHi, pLo) ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1,
        weightedBernoulliClosedThresholdRate gHi gLo p p = 0) ∧
      0 < weightedBernoulliClosedThresholdRate gHi gLo pHi pLo ∧
      StrictMonoOn
        (fun x : ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo x pLo)
        (Set.Icc pLo pHi) ∧
      StrictAntiOn
        (fun x : ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo pHi x)
        (Set.Icc pLo pHi) := by
  have hpHi0 : 0 < pHi := hpLo0.trans hpLo_lt_hi
  have hpLo1 : pLo < 1 := hpLo_lt_hi.trans hpHi1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact weightedBernoulliClosedThresholdRate_continuousAt_pair
      hpHi0 hpHi1 hpLo0 hpLo1
  · intro p hp
    exact weightedBernoulliClosedThresholdRate_self hgHi hgLo hp.1 hp.2
  · exact weightedBernoulliClosedThresholdRate_pos_of_lt
      hgHi hgLo hpLo0 hpLo_lt_hi hpHi1
  · exact weightedBernoulliClosedThresholdRate_strictMonoOn_hi_Icc
      hgHi hgLo hpLo0 le_rfl hpHi1
  · exact weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
      hgHi hgLo hpLo0 le_rfl hpHi1

/--
Equation (23): the adjacent rate notation used by Appendix C.5 and the
Theorem 3.2 analysis, including the two endpoint branches.

Source status: exact source rate notation under the corrected endpoint
convention.
-/
abbrev source_appendixC5_rate_notation_eq23 :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRate

/--
Equation (24): a middle odd level in the doubled chain is the Hellinger split
of the surrounding old levels.

Source status: exact source refinement formula.
-/
theorem source_lemmaC5_refinement_equation24 :
    type_of%
      (@GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointLevels_middle_odd) :=
  @GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointLevels_middle_odd

/--
Equation (25): the Hellinger split equalizes its two adjacent uniform
weighted Bernoulli rates.

Source status: exact source equal-rate identity.
-/
theorem source_lemmaC5_refinement_equation25 :
    type_of%
      (@GJ19OptimalBinaryRatingSystems.lemmaC5_uniform_interiorEqualSplit_rate_eq) :=
  @GJ19OptimalBinaryRatingSystems.lemmaC5_uniform_interiorEqualSplit_rate_eq

/--
Lemma C.5 complete doubled-chain endpoint: the explicit refined vector is
feasible, equalizes every uniform adjacent rate, and maximizes the refined
worst-adjacent objective.

Source status: exact corrected doubled-chain construction and optimality
conclusion.
-/
theorem source_lemmaC5_uniform_doubled_chain
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) ∧
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ∧
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector :
          (Fin ((2 * m + 1) + 2) → ℝ) → Prop)
        (fun xs : Fin ((2 * m + 1) + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs (fun _ => (1 : ℝ)))
        (uniformDoubledEndpointLevels oldLevels) := by
  have hnewLevels :=
    uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hnewEq :=
    uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  refine ⟨hnewLevels, hnewEq, ?_⟩
  apply lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn
      (m := 2 * m + 1) (by omega)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (uniformDoubledEndpointLevels oldLevels) hnewLevels
      (r := binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    exact hnewEq i (firstAdjacentIndex : Fin ((2 * m + 1) + 1))

/--
Lemma C.8 uniform polynomial first-level bound.  The proved quadratic bound
is stronger than the supplement's asymptotic `Ω(M⁻³)` claim.

Source status: formalized strengthening of the source polynomial lower bound.
-/
theorem source_lemmaC8_uniform_first_level_polynomial_lower_bound
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  exact
    BinaryEndpointAwareAdjacentRatesEqualize_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
      hm hlevels heq (by intro i; norm_num)
      (by intro a b hab; exact le_rfl) (by norm_num)

/--
Lemma C.9 finite logarithmic runtime statement: every positive grid width has
a dyadic bisection depth meeting that width, bounded by the source logarithm,
whose concrete nested operation count is at most the corresponding
`M log²(1/δ)` expression.

Source status: exact finite unit-cost real-arithmetic interpretation of the
source big-O claim, with the harmless `max 1` and additive constant that make
the logarithmic bound valid for every positive `δ`.
-/
theorem source_lemmaC9_nested_bisection_runtime_log_squared
    {M : ℕ} (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ L : ℕ,
      (1 : ℝ) ≤ delta * (2 : ℝ) ^ L ∧
        ((L + 1 : ℕ) : ℝ) ≤
          Real.logb 2 (max 1 (1 / delta)) + 2 ∧
        ((nestedBisectionOperationCount M (L + 1) L : ℕ) : ℝ) ≤
          (M : ℝ) * (Real.logb 2 (max 1 (1 / delta)) + 2) ^ 2 := by
  rcases
      AppliedModelingLib.Optimization.exists_nat_le_delta_mul_pow_two_and_succ_le_logb_max
        (budget := (1 : ℝ)) hdelta with
    ⟨L, hwidth, hlog⟩
  refine ⟨L, hwidth, hlog, ?_⟩
  have hbound :=
    AppliedModelingLib.Optimization.nestedBisection_operation_count_real_le_mul_sq_of_depth_le
      (M := M) (L := L) (outerSteps := L + 1) (innerSteps := L)
      (R := Real.logb 2 (max 1 (1 / delta)) + 2)
      hM hlog (Nat.le_refl (L + 1)) (Nat.le_refl L)
  have hop :
      nestedBisectionOperationCount M (L + 1) L =
        (L + 1) * (1 + (M - 3) * L) := by
    simp [nestedBisectionOperationCount, Nat.mul_add]
  rw [hop]
  exact hbound

/--
Theorem B.1 proof arithmetic: the quantile-floor selector at a dyadically
refined interval count remains in the scaled window around the anchor
selector.

Source status: exact selector-nesting estimate used in the supplement proof.
-/
theorem source_theoremB1_proof_selector_nesting :
    type_of%
      (@GJ19OptimalBinaryRatingSystems.theoremB1SourceDoubledIndexIterate_floor_window) :=
  @GJ19OptimalBinaryRatingSystems.theoremB1SourceDoubledIndexIterate_floor_window

/--
Corollary C.4 bundled source endpoint: the canonical equispaced design is
lexicographically optimal for both Kendall and Spearman at every positive
finite size, and its dyadic subsequences converge uniformly.

Source status: exact canonical witness for the source existential
Kendall/Spearman subsequence conclusion.
-/
theorem source_corollaryC4_kendall_spearman_subsequence
    (C : ℕ) :
    (∀ M : ℕ, Nonempty (Fin M) → 0 < M →
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (theorem31KendallFiniteDesignFeasible M)
        (theorem31KendallFiniteDesignValue M)
        (theorem31FiniteDesignEndpointRate M)
        (theorem31CanonicalUniformEndpointDesign M)) ∧
      (∀ M : ℕ, Nonempty (Fin M) → 0 < M →
        AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
          (theorem31SpearmanFiniteDesignFeasible M)
          (theorem31SpearmanFiniteDesignValue M)
          (theorem31FiniteDesignEndpointRate M)
          (theorem31CanonicalUniformEndpointDesign M)) ∧
      ∃ betaLimit : ℝ → ℝ,
        TendstoUniformlyOn
          (fun N : ℕ => fun θ : ℝ =>
            canonicalUniformEqualizedClampedFloorBetaSeq
              (theoremB1SubsequenceIndex C N) θ)
          betaLimit atTop (Set.Icc (0 : ℝ) 1) := by
  refine ⟨?_, ?_, paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector C⟩
  · intro M hnonempty hM
    letI : Nonempty (Fin M) := hnonempty
    exact
      paper_theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
        hM
  · intro M hnonempty hM
    letI : Nonempty (Fin M) := hnonempty
    exact
      paper_theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
        hM

/-! ## Source objects and reopened source-first endpoints -/

/-- The source-normalized unit quality continuum. -/
abbrev source_quality_domain :=
  GJ19OptimalBinaryRatingSystems.sourceQualityDomain

/-- Source assumptions on the nondecreasing matching function. -/
abbrev source_matching_function :=
  GJ19OptimalBinaryRatingSystems.SourceMatchingFunction

/-- Source floor match count `n_k(θ) = floor(k g(θ))`. -/
abbrev source_matching_count :=
  GJ19OptimalBinaryRatingSystems.sourceMatchingCount

/-- Source empirical fraction of positive binary ratings. -/
abbrev source_empirical_reputation_score :=
  GJ19OptimalBinaryRatingSystems.sourceEmpiricalReputationScore

/-- Source system state as a measure on quality and empirical reputation. -/
abbrev source_system_state :=
  GJ19OptimalBinaryRatingSystems.SourceSystemState

/-- Appendix B.1 active set for the transition from time `k` to `k+1`. -/
abbrev appendixB1_active_set :=
  GJ19OptimalBinaryRatingSystems.sourceAppendixBActiveSet

/-- Appendix B.1 corrected atomic two-branch transition kernel. -/
abbrev appendixB1_transition_kernel :=
  GJ19OptimalBinaryRatingSystems.sourceAppendixBTransitionKernel

/-- Appendix B.1 corrected state-update equation. -/
abbrev appendixB1_state_update :=
  GJ19OptimalBinaryRatingSystems.sourceAppendixBStateUpdateMass

/-- Section 4 probability distribution over a finite question set. -/
abbrev section4_question_distribution :=
  @GJ19OptimalBinaryRatingSystems.SourceQuestionDistribution

/-- Section 4 induced response `betaTilde(θ) = sum_y psi(θ,y) H(y)`. -/
abbrev section4_induced_binary_response :=
  @GJ19OptimalBinaryRatingSystems.sourceInducedBinaryResponse

/-- Section 4 equation-(5) finite `L1` design objective. -/
abbrev section4_l1_design_objective :=
  @GJ19OptimalBinaryRatingSystems.sourceQuestionDesignL1Objective

/-- Section 4 probability-constrained minimizer predicate. -/
abbrev section4_question_design_solution :=
  @GJ19OptimalBinaryRatingSystems.SourceQuestionDesignSolution

/-- Literal random-question/binary-response data of Appendix B.5. -/
abbrev appendixB5_random_question_experiment :=
  @GJ19OptimalBinaryRatingSystems.SourceRandomQuestionExperiment

/-- KnownTypeExperiment representatives and empirical response table. -/
abbrev appendixB5_known_type_experiment :=
  @GJ19OptimalBinaryRatingSystems.SourceKnownTypeExperiment

/-- UnknownTypeExperiment qualities, scores, responses, and empirical ranks. -/
abbrev appendixB5_unknown_type_experiment :=
  @GJ19OptimalBinaryRatingSystems.SourceUnknownTypeExperiment

/-- Literal conditional empirical question-response frequency. -/
abbrev appendixB5_empirical_question_response :=
  @GJ19OptimalBinaryRatingSystems.sourceExperimentEmpiricalQuestionResponse

/-- Theorem 3.1 source identity `g_i = inf_{θ in S_i} g(θ) = g(s_i)`. -/
theorem theorem31_source_cell_matching_rate_eq_lower_cutpoint : type_of%
    (@GJ19OptimalBinaryRatingSystems.sourceCellMatchingRate_eq_lower_cutpoint) :=
  @GJ19OptimalBinaryRatingSystems.sourceCellMatchingRate_eq_lower_cutpoint

/--
Source-assembled Theorem 3.1 for a selected value-maximizing discretization;
the cell rates, endpoint optimizer, and `Wbar_k` rate are derived from `g`.
-/
theorem theorem31_source_matching_function_value_argmax_certificate : type_of%
    (@GJ19OptimalBinaryRatingSystems.theorem31_source_matching_function_weighted_value_argmax_certificate) :=
  @GJ19OptimalBinaryRatingSystems.theorem31_source_matching_function_weighted_value_argmax_certificate

/-- Global optimization of the full cross-cell value followed by the displayed
adjacent-rate formula. The actual `W - W_k` rate identification is separate. -/
theorem theorem31_source_matching_function_lexicographic_formula : type_of%
    (@GJ19OptimalBinaryRatingSystems.theorem31_source_matching_function_lexicographic_formula) :=
  @GJ19OptimalBinaryRatingSystems.theorem31_source_matching_function_lexicographic_formula

/-- Appendix B.3 Lemma B.1 two-optimizer matching-rate comparative statics. -/
theorem lemmaB1_matching_rate_shift : type_of%
    (@GJ19OptimalBinaryRatingSystems.lemmaB1_matching_rate_shift) :=
  @GJ19OptimalBinaryRatingSystems.lemmaB1_matching_rate_shift

/-- Literal random-question SLLN for KnownTypeExperiment. -/
theorem lemmaB2_knownTypeExperiment_random_question_slln : type_of%
    (@GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_ae_question_response_of_iid) :=
  @GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_ae_question_response_of_iid

/--
Corrected UnknownTypeExperiment response/rank theorem under explicit strict
aggregate-score order identifiability.
-/
theorem lemmaB3_unknownTypeExperiment_random_question_response_and_rank : type_of%
    (@GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid) :=
  @GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid

/-- General positive-nondecreasing-matching Lemma C.6. -/
theorem lemmaC6_monotone_matching_penultimate_level_bound : type_of%
    (@GJ19OptimalBinaryRatingSystems.BinaryEndpointLevelVector_monotone_equalized_last_low_ge_one_sub_inv) :=
  @GJ19OptimalBinaryRatingSystems.BinaryEndpointLevelVector_monotone_equalized_last_low_ge_one_sub_inv

/-- Literal optimum-independent weighted output of Algorithm 1. -/
abbrev theorem32_weighted_nested_bisection_output :=
  @GJ19OptimalBinaryRatingSystems.theorem32WeightedNestedBisectionOutput

/--
General-matching Theorem 3.2 for the literal output.  The concrete grid is the
minimum of the finite source gap scale and the epsilon loss scale, and a
finite common dyadic depth is constructed; no operational shooting premise
is exposed to the caller.
-/
theorem theorem32_weighted_nested_bisection_loss_and_runtime : type_of%
    (@GJ19OptimalBinaryRatingSystems.theorem32WeightedNestedBisectionOutput_exists_source_depth_of_eps_pos) :=
  @GJ19OptimalBinaryRatingSystems.theorem32WeightedNestedBisectionOutput_exists_source_depth_of_eps_pos

end

end GJ19OptimalBinaryRatingSystems.ProofBridge
