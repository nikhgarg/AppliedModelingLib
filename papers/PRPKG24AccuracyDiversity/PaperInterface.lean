import PRPKG24AccuracyDiversity.ProofInterface
import PRPKG24AccuracyDiversity.SourcePreferenceMixture
import PRPKG24AccuracyDiversity.AllConsumedIidSource
import PRPKG24AccuracyDiversity.Theorem1PmfSource
import PRPKG24AccuracyDiversity.Theorem2RankBernoulliSource
import PRPKG24AccuracyDiversity.BernoulliIidSource
import PRPKG24AccuracyDiversity.Corollary1SourceIid
import PRPKG24AccuracyDiversity.AppendixD1Source
import PRPKG24AccuracyDiversity.FiniteDiscreteExactTopKSource
import PRPKG24AccuracyDiversity.Definition3IidSource
import PRPKG24AccuracyDiversity.AppendixD1GenericI
import PRPKG24AccuracyDiversity.AppendixD1GenericIIFull
import PRPKG24AccuracyDiversity.AppendixD1GenericIII
import PRPKG24AccuracyDiversity.AppendixD1GenericIV
import PRPKG24AccuracyDiversity.AppendixD2DensitySource
import PRPKG24AccuracyDiversity.AppendixD3Source
import PRPKG24AccuracyDiversity.AppendixD4Source
import PRPKG24AccuracyDiversity.ContinuousSphereConcrete
import PRPKG24AccuracyDiversity.Assumptions
import PRPKG24AccuracyDiversity.GeneralRounding

/-!
# Paper Interface: Reconciling the Accuracy-Diversity Trade-off

This is the compact human-review surface for the PRPKG 2024
accuracy-diversity formalization. It exposes one representative declaration for
each paper-named definition, example, theorem part, corollary, proposition, and
appendix lemma. The larger implementation/checkpoint ledger remains in
`ProofInterface.lean`.
-/

open scoped BigOperators
open Filter MeasureTheory

namespace PRPKG24AccuracyDiversity
namespace PaperInterface

/-! ## Definitions and Example -/

/--
Definition 1 with the source probability semantics: finite real `gamma`
satisfies equation (5), while `gamma = infinity` concentrates on a selected
preferred-type PMF maximizer.
-/
theorem definition1_source_preference_law
    {T : ℕ} (a : CountAllocation T) (preferenceLaw : SourcePreferenceLaw T)
    (gamma : ℝ)
    (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) :
    ((gammaLikelihoodProfile (fun t => (preferenceLaw t).toReal) gamma).Exact a ↔
      ∀ t : ItemType T,
        CountAllocation.representation a t =
          ((preferenceLaw t).toReal) ^ gamma /
            ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ gamma) ∧
    ((infiniteLikelihoodProfile (fun t => (preferenceLaw t).toReal) best hbest).Exact a ↔
      CountAllocation.representation a best = 1 ∧
        ∀ t : ItemType T, t ≠ best →
          CountAllocation.representation a t = 0) :=
  definition1_gamma_homogeneity_complete a
    (fun t => (preferenceLaw t).toReal) gamma
    (sourcePreferenceLaw_gamma_normalizer_ne_zero preferenceLaw gamma) best hbest

abbrev definition1 := @definition1_source_preference_law

/--
Definition 1 / Equation (5), exposed as a transparent source-facing Spec.
Finite real `gamma` gives the displayed normalized-power profile; the source's
`gamma = infinity` case selects one PMF maximizer, with ties left selectable.
-/
def definition1_eq5_gamma_homogeneitySpec : Prop :=
  ∀
    {T : ℕ} (a : CountAllocation T) (preferenceLaw : SourcePreferenceLaw T)
    (gamma : ℝ) (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal),
    ((gammaLikelihoodProfile (fun t => (preferenceLaw t).toReal) gamma).Exact a ↔
      ∀ t : ItemType T,
        CountAllocation.representation a t =
          ((preferenceLaw t).toReal) ^ gamma /
            ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ gamma) ∧
    ((infiniteLikelihoodProfile (fun t => (preferenceLaw t).toReal) best hbest).Exact a ↔
      CountAllocation.representation a best = 1 ∧
        ∀ t : ItemType T, t ≠ best →
          CountAllocation.representation a t = 0)

theorem definition1_eq5_gamma_homogeneitySpec_proof :
    definition1_eq5_gamma_homogeneitySpec := by
  exact definition1_source_preference_law

/-- Definition 2 with the source preferred-type PMF in equation (6). -/
theorem definition2_source_preference_law
    {T : ℕ} (seq : AllocationSequence T) (preferenceLaw : SourcePreferenceLaw T)
    (gamma : ℝ) :
    seq.ConvergesToProfile
      (gammaLikelihoodProfile (fun t => (preferenceLaw t).toReal) gamma) ↔
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ gamma /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ gamma)) :=
  definition2_gamma_homogeneity_sequence_iff seq
    (fun t => (preferenceLaw t).toReal) gamma
    (sourcePreferenceLaw_gamma_normalizer_ne_zero preferenceLaw gamma)

abbrev definition2 := @definition2_source_preference_law

/--
Definition 2 / Equation (6), exposed as a transparent source-facing Spec for
convergence of every type's representation to the normalized-power profile.
-/
def definition2_eq6_sequence_homogeneitySpec : Prop :=
  ∀
    {T : ℕ} (seq : AllocationSequence T) (preferenceLaw : SourcePreferenceLaw T)
    (gamma : ℝ),
    seq.ConvergesToProfile
      (gammaLikelihoodProfile (fun t => (preferenceLaw t).toReal) gamma) ↔
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ gamma /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ gamma))

theorem definition2_eq6_sequence_homogeneitySpec_proof :
    definition2_eq6_sequence_homogeneitySpec := by
  exact definition2_source_preference_law

/--
Definition 3: the top-`k` oracle from one common iid base distribution with a
finite first moment, as required by Theorem 1's source model.
-/
noncomputable def definition3 (T : ℕ) (D : Measure ℝ) [IsProbabilityMeasure D]
    (_hfinite_mean : Integrable (fun x : ℝ => x) D) :
    TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T (definition3IidOrderStatisticMean D)

/--
Definition 3: `mu_D(i, a)` is the expected `i`th order statistic of `a`
independent draws from the same base law `D`.

Source status: direct source definition
-/
theorem definition3_iid_order_statistic_mean_formula
    (D : Measure ℝ) (i a : ℕ) :
    definition3IidOrderStatisticMean D i a =
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq
        (fun b : ℕ => Measure.pi (fun _ : Fin b => D)) i a := by
  rfl

/--
Definition 3, exposed as a transparent source-facing Spec: under one
probability law with the source finite-mean condition and the source-domain
rank convention `1 ≤ i ≤ a`, `mu_D(i,a)` is the expected `i`th order statistic
of `a` iid draws from that same law.  The valid-rank premise deliberately
excludes Lean's totalized values outside the paper's order-statistic domain.
-/
def definition3_order_statistic_meanSpec : Prop :=
  ∀
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (i a : ℕ)
    (hvalid_rank : 1 ≤ i ∧ i ≤ a),
    definition3IidOrderStatisticMean D i a =
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq
        (fun b : ℕ => Measure.pi (fun _ : Fin b => D)) i a

theorem definition3_order_statistic_meanSpec_proof :
    definition3_order_statistic_meanSpec := by
  intro D _ hfinite_mean i a hvalid_rank
  exact definition3_iid_order_statistic_mean_formula D i a

/-- Generic order-statistic oracle retained only for support computations. -/
noncomputable abbrev definition3_raw_order_statistic_oracle :=
  @definition3_topk_value_oracle_from_order_statistic_mean

/--
Definition 3: the expected top-`k` value from order-statistic means is the sum
of the upper `min k a` order-statistic means.
-/
theorem definition3_expectedTopSum_formula
    (T : ℕ) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D)
    (k : ℕ) (t : ItemType T) (a : ℕ) :
    (definition3 T D hfinite_mean).expectedTopSum k t a =
      ∑ i ∈ Finset.range (min k a),
        definition3IidOrderStatisticMean D (a - i) a := by
  rfl

/--
Definition 3's measure-level identity: expected upper order-statistic means
sum to the expected top-`k` sample value.  This is also the generic identity
used by source Proposition 5.  Finite mean is explicit and the iid
order-statistic integrability obligation is derived from it.
-/
theorem definition3_iid_order_statistic_topk_identity
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ) :
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (definition3IidOrderStatisticMean D) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure D a) k :=
  definition3_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
    D hfinite_mean k a

/--
Equation (3): the recommendation objective is the finite likelihood-weighted
sum of the conditional value functions evaluated at the type counts.

Source status: direct paper formula
-/
theorem equation3_consumptionObjective_formula
    {T : ℕ} (M : ConsumptionModel T) (a : CountAllocation T) :
    M.objective a =
      ∑ t : ItemType T, M.likelihood t * M.valueOfCount t (a.count t) := by
  rfl

/--
Equation (3) as an expectation over the source-selected preferred type.

Source status: direct paper formula
-/
theorem equation3_sourcePreferenceLaw_pmfExp
    {T : ℕ} (M : ConsumptionModel T) (a : CountAllocation T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hlaw : M.RealizesSourcePreferenceLaw preferenceLaw) :
    M.objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t => M.valueOfCount t (a.count t)) :=
  ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
    M a preferenceLaw hlaw

/--
Equation (4): type representation is its count divided by total slate size.

Source status: direct paper formula
-/
theorem equation4_representation_formula
    {T : ℕ} (a : CountAllocation T) (t : ItemType T)
    (htotal : AppliedModelingLib.Allocation.total a ≠ 0) :
    CountAllocation.representation a t =
      (a.count t : ℝ) / (AppliedModelingLib.Allocation.total a : ℝ) := by
  rw [CountAllocation.representation_eq_share]
  exact
    AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
      (a := a) (k := t) htotal

/--
Equation (4), exposed as a transparent source-facing Spec for representation
of a type in a nonempty finite slate.
-/
def equation4_representationSpec : Prop :=
  ∀
    {T : ℕ} (a : CountAllocation T) (t : ItemType T)
    (htotal : AppliedModelingLib.Allocation.total a ≠ 0),
    CountAllocation.representation a t =
      (a.count t : ℝ) / (AppliedModelingLib.Allocation.total a : ℝ)

theorem equation4_representationSpec_proof : equation4_representationSpec := by
  exact equation4_representation_formula

/--
Equation (10): along a sequence of `N`-item slates, representation is
eventually the type count divided by `N`, so the two displayed limits are the
same whenever either exists.

Source status: direct paper formula
-/
theorem equation10_representation_sequence_eventuallyEq_count_div
    {T : ℕ} (seq : AllocationSequence T)
    (htotal : ∀ N : ℕ,
      AppliedModelingLib.Allocation.total (seq.allocation N) = N)
    (t : ItemType T) :
    (fun N : ℕ =>
        CountAllocation.representation (seq.allocation N) t) =ᶠ[Filter.atTop]
      (fun N : ℕ => ((seq.allocation N).count t : ℝ) / (N : ℝ)) := by
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have htotal_ne :
      AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [htotal N]
    exact Nat.ne_of_gt hN
  calc
    CountAllocation.representation (seq.allocation N) t =
        ((seq.allocation N).count t : ℝ) /
          (AppliedModelingLib.Allocation.total (seq.allocation N) : ℝ) :=
      equation4_representation_formula (seq.allocation N) t htotal_ne
    _ = ((seq.allocation N).count t : ℝ) / (N : ℝ) := by
      rw [htotal N]

/--
Equation (12): the finite-`n`, arbitrary-`k` optimization objective used in the
paper's computational procedure.  Lean states the same formula for any finite
number of types; its order-statistic index is zero-based.

Source status: direct paper formula
Source note: the plotted Monte Carlo estimates are empirical and outside
theorem scope, but the mathematical objective they estimate is explicit here.
-/
theorem equation12_empiricalTopKObjective_formula
    (T : ℕ) (mu : ℕ → ℕ → ℝ) (k : ℕ)
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) :
    ((TopKValueOracle.ofOrderStatisticMean T mu).toConsumptionModel likelihood k).objective a =
      ∑ t : ItemType T,
        likelihood t *
          (∑ i ∈ Finset.range (min k (a.count t)),
            mu (a.count t - i) (a.count t)) := by
  rfl

/--
Example 1, all-consumed side: if romance is strictly more likely, every optimum
assigns zero recommendations to action.

Source status: direct paper statement
-/
abbrev example1_all_consumed_formula :=
  @example1_all_consumed_only_romance

/--
Example 1, top-one optimization: the calibrated split maximizes the source's
displayed log-relaxation objective.

Source status: direct paper statement
-/
abbrev example1_log_relaxation_optimum :=
  @example1_top_one_log_relaxation_calibrated

/--
Example 1, asymptotic conclusion: exact exponential maxima converge to the
calibrated representation shares `(p1,p2)`.

Source status: direct paper statement
-/
abbrev example1_calibrated_sequence_formula :=
  @example1_top_one_exponential_harmonic_sequence_formula

/--
Example 1's displayed continuous log-relaxation: positive two-genre
probabilities summing to one and a positive exponential rate make the
calibrated split maximize the displayed relaxed top-one objective.  This is
the source's `≈` relaxation, not a claim about a finite integer optimizer.
-/
def example1_calibrated_log_relaxationSpec : Prop :=
  ∀ {p1 p2 lambda n x y : ℝ},
    0 < p1 → 0 < p2 → 0 < lambda → 0 < n → 0 < x → 0 < y →
      p1 + p2 = 1 → x + y = n →
        example1TopOneLogObjective p1 p2 lambda x y ≤
          example1TopOneLogObjective p1 p2 lambda (p1 * n) (p2 * n)

theorem example1_calibrated_log_relaxationSpec_proof :
    example1_calibrated_log_relaxationSpec := by
  intro p1 p2 lambda n x y hp1 hp2 hlambda hn hx hy hp_sum hxy_sum
  exact example1_top_one_log_relaxation_calibrated
    hp1 hp2 hlambda hn hx hy hp_sum hxy_sum

/--
Equation (1): conditional on the two preference classes, the expected best
item value is the likelihood-weighted sum of the two expected maxima.

Source status: direct paper formula
-/
noncomputable def equation1_example1_expectedBestValue
    (p1 p2 : ℝ) (expectedMax : ℕ → ℝ) (a1 a2 : ℕ) : ℝ :=
  p1 * expectedMax a1 + p2 * expectedMax a2

/--
Equation (2): the logarithmic relaxation of Example 1's exponential-maximum
objective.

Source status: direct paper asymptotic formula
Source note: the exact finite exponential maximum is harmonic; this is the
source's large-count logarithmic relaxation used for the calibration argument.
-/
theorem equation2_example1_logRelaxedObjective_formula
    (p1 p2 lambda x y : ℝ) :
    example1TopOneLogObjective p1 p2 lambda x y =
      (p1 / lambda) * Real.log x + (p2 / lambda) * Real.log y := by
  rfl

/-! ## Main Theorems and Corollaries -/

/--
Theorem 1(i): exact-top-`k` finite-discrete iid source, equation (6).

Source clarifications: every named preferred type has strictly positive mass,
and conditional item values use the nonnegative utility scale assumed
throughout Theorem 1.  Thus the exact top-`k` finite experiment and its
monotonicity route have the intended domain.
-/
abbrev theorem1_i :=
  @theorem1_i_finiteDiscrete_iid_exact_source_formula

/--
Theorem 1(i): finite-discrete iid source, equation (6).
Source status: direct source formula
-/
theorem theorem1_i_formula
    {T : ℕ} [NeZero T] {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (preferenceLaw : SourcePreferenceLaw T)
    (itemLaw : PMF Omega) (value : Omega → ℝ) {xTop xSecond : ℝ}
    (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
              (fun t => (preferenceLaw t).toReal) k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_nonneg : ∀ omega, 0 ≤ value omega)
    (hvalue_le : ∀ omega, value omega ≤ xTop)
    (hvalue_split : ∀ omega, value omega = xTop ∨ value omega ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => value omega = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => ¬ value omega = xTop))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal) :
    (∀ a : CountAllocation T,
      ((TopKValueOracle.common T
        (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (AppliedModelingLib.pmfProduct (Fin (a.count t)) Omega itemLaw)
              (fun sample : Fin (a.count t) → Omega =>
                AppliedModelingLib.Probability.sampleTopKSum
                  (fun i => value (sample i)) k))) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ))) := by
  exact theorem1_i_finiteDiscrete_iid_exact_source_formula
    preferenceLaw itemLaw value k seq hk_pos hxTop_pos hxSecond_nonneg
    hsecond_le_top hsecond_lt_top hvalue_nonneg hvalue_le hvalue_split
    htop_mass_pos hnontop_mass_pos hpreference_pos

/--
Theorem 1(i)'s direct finite-discrete iid source-model route.  This derives
the uniform limit from the literal PMF, top-support split, and integer
optimizer, rather than invoking the generic Lemma D.1 bridge.
-/
abbrev theorem1_i_finiteDiscrete_iid_source_model :=
  @PRPKG24AccuracyDiversity.theorem1_i_finiteDiscrete_iid_exact_source_formula

/--
Theorem 1(ii): the source preferred-type PMF and bounded iid upper-endpoint
conditional model, equation (6).

The endpoint states the source's literal left-limit PDF assumption and the
outer preferred-type expectation.  It also shows the allocation proof's
explicit nonnegative-value, finite-lower-support, positive-endpoint, and
positive-width normalization assumptions; they are not claimed to follow from
merely being bounded above.
-/
abbrev theorem1_ii :=
  @PRPKG24AccuracyDiversity.theorem1_ii_bounded_iid_pmf_source_model_endpoint

/--
Theorem 1(ii): bounded iid upper-endpoint PMF source route, equation (6).

The `withDensity` model derives the local-integrability and reflected-tail
facts internally from the literal PDF representation.  The remaining support
normalization and the preferred-type PMF are explicit in the theorem type.
Source clarifications: each named preferred type has positive mass, and the
conditional item values use the nonnegative utility scale rather than an
arbitrary translated upper-bounded scale.
Source status: direct PMF outer-model and literal-PDF conditional route under
the stated source-domain clarifications
-/
theorem theorem1_ii_formula
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (preferenceLaw : SourcePreferenceLaw T)
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_finite_mean : MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure)
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun x : ℝ => f x / ((M - x) ^ (beta - 1)))
        (nhdsWithin M (Set.Iio M)) (nhds c))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k baseMeasure)) :
    (∀ a : CountAllocation T,
      (boundedIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k baseMeasure).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (definition3IidSampleMeasure baseMeasure (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (beta / (beta + 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (beta / (beta + 1)))) := by
  exact theorem1_ii_bounded_iid_pmf_source_model_endpoint
    preferenceLaw baseMeasure h_finite_mean h_base_bounds h_nonneg hM_pos f hpdf
    hf_nonneg hf_measurable hbeta_pos hc_pos hratio hpreference_pos k_pos
    hwidth_pos seq

/--
Theorem 1(iii): the source preferred-type PMF and exponential iid
order-statistic conditional model, equation (6).
-/
abbrev theorem1_iii :=
  @PRPKG24AccuracyDiversity.theorem1_iii_exponential_iid_pmf_source_model_endpoint

/--
Theorem 1(iii): exponential iid PMF source model, equation (6).
Source status: direct PMF outer-model and literal iid conditional route
-/
theorem theorem1_iii_formula
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            (fun t => (preferenceLaw t).toReal) k)) :
    (∀ a : CountAllocation T,
      ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure
                (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 : ℝ) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 : ℝ))) := by
  exact theorem1_iii_exponential_iid_pmf_source_model_endpoint
    preferenceLaw lambda k hlambda_pos hk_pos hpreference_pos seq

/--
Theorem 1(iv): the source preferred-type PMF and concrete iid Pareto
order-statistic conditional model, equation (6).
-/
abbrev theorem1_iv :=
  @PRPKG24AccuracyDiversity.theorem1_iv_pareto_iid_pmf_source_model_endpoint

/--
Theorem 1(iv): concrete iid Pareto PMF source model, equation (6).
Source status: direct PMF outer-model and literal iid conditional route
-/
theorem theorem1_iv_formula
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          paretoIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k alpha)) :
    (∀ a : CountAllocation T,
      (paretoIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (paretoIidSampleMeasure alpha (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (alpha / (alpha - 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (alpha / (alpha - 1)))) := by
  exact theorem1_iv_pareto_iid_pmf_source_model_endpoint
    preferenceLaw halpha hk hpreference_pos seq

/--
Theorem 1(v)'s literal source experiment: a preferred type is drawn from its
PMF and then receives a finite iid slate from the common conditional law.

Source status: direct source model formula
-/
theorem theorem1_v_source_experiment_formula
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D] (a : CountAllocation T) :
    (iidAllConsumedSourceModel preferenceLaw D).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          ∫ sample : Fin (a.count t) → ℝ,
            iidAllConsumedSampleValue sample
              ∂iidAllConsumedSampleLaw D (a.count t)) :=
  iidAllConsumedSourceModel_objective_eq_source_experiment preferenceLaw D a

/--
Theorem 1(v)'s selected-maximizer conclusion under the common finite-mean
source law.  A nonnegative mean is explicit because a negative common mean
would reverse the likelihood argmax direction.

Source status: approved corrected theorem target
-/
theorem theorem1_v_selected_maximizer_conclusion
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D)
    (hmean_nonneg : 0 ≤ ∫ x : ℝ, x ∂D)
    (N : ℕ) (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) :
    (iidAllConsumedSourceModel preferenceLaw D).IsOptimalAtTotal N
      (allOnTypeAllocation N best) :=
  iidAllConsumedSourceModel_allOn_max_likelihood_isOptimal
    preferenceLaw D hfinite_mean hmean_nonneg N best hbest

/--
Auxiliary combined provenance bundle for Theorem 1(v).  The source-facing
review route selects the explicit conclusion above and keeps this paired
formula only as support.
-/
theorem theorem1_v_source_model_endpoint
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D)
    (hmean_nonneg : 0 ≤ ∫ x : ℝ, x ∂D)
    (N : ℕ) (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) :
    (∀ a : CountAllocation T,
      (iidAllConsumedSourceModel preferenceLaw D).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            ∫ sample : Fin (a.count t) → ℝ,
              iidAllConsumedSampleValue sample
                ∂iidAllConsumedSampleLaw D (a.count t))) ∧
      (iidAllConsumedSourceModel preferenceLaw D).IsOptimalAtTotal N
        (allOnTypeAllocation N best) := by
  constructor
  · intro a
    exact theorem1_v_source_experiment_formula preferenceLaw D a
  · exact theorem1_v_selected_maximizer_conclusion
      preferenceLaw D hfinite_mean hmean_nonneg N best hbest

abbrev theorem1_v := @theorem1_v_source_model_endpoint

/--
Corollary 1: every nonnegative `gamma` is attained by a concrete source-iid
conditional-value model.  The witness records its source family, parameters,
and exponent identity; every optimal fixed-`k` sequence has the stated limit.

Source clarification: every named preferred type has strictly positive mass
`p_t > 0`; zero-mass labels are removed before applying the all-coordinate
homogeneity statement.  The explicit `hlike_pos` hypothesis is this source
domain clarification, alongside the positive-`k` domain.
-/
theorem corollary1
    {T : ℕ} [NeZero T] {k : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hk_pos : 0 < k) (hgamma_nonneg : 0 ≤ gamma)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∃ M : ConsumptionModel T,
      Corollary1SourceIidFamily likelihood gamma k M ∧
        ∀ seq : OptimalAllocationSequence (fun _ => M),
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                ((likelihood t) ^ gamma /
                  ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
  paper_corollary1_any_nonnegative_gamma_source_iid_model_sequence_formula
    likelihood gamma hk_pos hgamma_nonneg hlike_pos

/--
Theorem 2 top-one source-model bridge.  For the first `q` recommendations,
`Fin q` coordinate `i` represents source rank `i + 1`; its Boolean law has
the rank-varying Bernoulli parameter `c * ((i + 1) + d)^(-alpha)`.  The law is
an independent product over ranks, not an iid product when these parameters
vary.  The strict first-rank bound is the probability-domain assumption used
by the top-one asymptotic branches.
-/
theorem theorem2_top_one_rank_varying_independent_bernoulli_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (t : ItemType T) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d alpha).valueOfCount t q =
      AppliedModelingLib.pmfExp
        (decayingBernoulliFiniteLaw c d alpha q hc_nonneg hd_nonneg
          halpha_nonneg hfirst_lt_one.le)
        rankBernoulliFiniteTopOneSampleValue := by
  exact decayingBernoulliTopOneConsumptionModel_value_eq_expected_source
    likelihood c d alpha q hc_nonneg hd_nonneg halpha_nonneg hfirst_lt_one.le t

/--
Theorem 2 all-consumed source-model bridge.  Unlike the top-one asymptotic
branches, the literal finite Bernoulli law only needs the weak first-rank
probability bound.  No cross-type independence is asserted or needed here.
-/
theorem theorem2_all_consumed_rank_varying_independent_bernoulli_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (t : ItemType T) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).valueOfCount t q =
      AppliedModelingLib.pmfExp
        (decayingBernoulliFiniteLaw c d alpha q hc_nonneg hd_nonneg
          halpha_nonneg hfirst_le_one)
        rankBernoulliFiniteAllConsumedSampleValue := by
  exact decayingBernoulliAllConsumedConsumptionModel_value_eq_expected_source
    likelihood c d alpha q hc_nonneg hd_nonneg halpha_nonneg hfirst_le_one t

/-- Theorem 2(i): decaying Bernoulli top-one, `alpha = 0`. -/
abbrev theorem2_i :=
  @theorem2_i_decaying_bernoulli_top_one_uniform_formula

/--
Theorem 2(i): decaying Bernoulli top-one, `alpha = 0`.
Source status: direct source formula
-/
theorem theorem2_i_formula : type_of%
    (@theorem2_i_decaying_bernoulli_top_one_uniform_formula) :=
  @theorem2_i_decaying_bernoulli_top_one_uniform_formula

/-- Theorem 2(ii): decaying Bernoulli top-one, `alpha = 1`. -/
abbrev theorem2_ii :=
  @theorem2_ii_decaying_bernoulli_top_one_formula

/--
Theorem 2(ii): decaying Bernoulli top-one, `alpha = 1`.
Source status: direct source formula
-/
theorem theorem2_ii_formula : type_of%
    (@theorem2_ii_decaying_bernoulli_top_one_formula) :=
  @theorem2_ii_decaying_bernoulli_top_one_formula

/-- Theorem 2(iii): decaying Bernoulli top-one, `alpha > 1`. -/
abbrev theorem2_iii :=
  @theorem2_iii_decaying_bernoulli_top_one_formula

/--
Theorem 2(iii): decaying Bernoulli top-one, `alpha > 1`.
Source status: direct source formula
-/
theorem theorem2_iii_formula : type_of%
    (@theorem2_iii_decaying_bernoulli_top_one_formula) :=
  @theorem2_iii_decaying_bernoulli_top_one_formula

/-- Theorem 2(iv): decaying Bernoulli all-consumed, positive `alpha`. -/
theorem theorem2_iv_positive_alpha : type_of%
    (@theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula) :=
  @theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula

/--
Corrected Theorem 2(i) source-model endpoint.  It first identifies every
finite count value with the expectation under the literal independent,
rank-varying Bernoulli law, then gives the established uniform asymptotic
conclusion.  It is not credited as a direct archival source statement because
the source calls a rank-varying family iid.
-/
theorem theorem2_i_corrected_source_model_endpoint
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_lt_one : alpha < 1)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d alpha)) :
    (∀ t : ItemType T, ∀ q : ℕ,
      (decayingBernoulliTopOneConsumptionModel likelihood c d alpha).valueOfCount t q =
        AppliedModelingLib.pmfExp
          (decayingBernoulliFiniteLaw c d alpha q hc_pos.le hd_nonneg
            halpha_nonneg hfirst_lt_one.le)
          rankBernoulliFiniteTopOneSampleValue) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ))) := by
  constructor
  · intro t q
    exact theorem2_top_one_rank_varying_independent_bernoulli_source
      likelihood c d alpha q hc_pos.le hd_nonneg halpha_nonneg hfirst_lt_one t
  · exact theorem2_i_decaying_bernoulli_top_one_uniform_formula
      likelihood alpha c d halpha_nonneg halpha_lt_one hc_pos hd_nonneg
      hfirst_lt_one hlike_pos seq

/--
Corrected Theorem 2(ii) source-model endpoint: the alpha-one top-one
conclusion is paired with its literal finite independent rank-Bernoulli
realization.  The finite law is rank-varying, so no iid claim is used.
-/
theorem theorem2_ii_corrected_source_model_endpoint
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 1)) :
    (∀ t : ItemType T, ∀ q : ℕ,
      (decayingBernoulliTopOneConsumptionModel likelihood c d 1).valueOfCount t q =
        AppliedModelingLib.pmfExp
          (decayingBernoulliFiniteLaw c d 1 q hc_pos.le hd_nonneg
            (by norm_num) hfirst_lt_one.le)
          rankBernoulliFiniteTopOneSampleValue) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            ((likelihood t) ^ (1 / (1 + c)) /
              ∑ i : ItemType T, (likelihood i) ^ (1 / (1 + c)))) := by
  constructor
  · intro t q
    exact theorem2_top_one_rank_varying_independent_bernoulli_source
      likelihood c d 1 q hc_pos.le hd_nonneg (by norm_num) hfirst_lt_one t
  · exact theorem2_ii_decaying_bernoulli_top_one_formula
      likelihood c d hc_pos hd_nonneg hfirst_lt_one hlike_pos seq

/--
Corrected Theorem 2(iii) source-model endpoint: the superunit top-one
conclusion follows after every finite objective is tied to the literal
independent rank-varying Bernoulli product law.
-/
theorem theorem2_iii_corrected_source_model_endpoint
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_gt_one : 1 < alpha) (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d alpha)) :
    (∀ t : ItemType T, ∀ q : ℕ,
      (decayingBernoulliTopOneConsumptionModel likelihood c d alpha).valueOfCount t q =
        AppliedModelingLib.pmfExp
          (decayingBernoulliFiniteLaw c d alpha q hc_pos.le hd_nonneg
            (le_of_lt (lt_trans zero_lt_one halpha_gt_one)) hfirst_lt_one.le)
          rankBernoulliFiniteTopOneSampleValue) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            ((likelihood t) ^ (1 / alpha) /
              ∑ i : ItemType T, (likelihood i) ^ (1 / alpha))) := by
  have halpha_nonneg : 0 ≤ alpha :=
    le_of_lt (lt_trans zero_lt_one halpha_gt_one)
  constructor
  · intro t q
    exact theorem2_top_one_rank_varying_independent_bernoulli_source
      likelihood c d alpha q hc_pos.le hd_nonneg halpha_nonneg hfirst_lt_one t
  · exact theorem2_iii_decaying_bernoulli_top_one_formula
      likelihood alpha c d halpha_gt_one hc_pos hd_nonneg hfirst_lt_one
      hlike_pos seq

/--
Corrected Theorem 2(iv) positive-alpha source-model endpoint.  Its added
weak first-rank bound is required to construct the Bernoulli law; the original
all-consumed asymptotic proof itself does not need it.  The alpha-zero case
remains the separately selected-argmax correction below.
-/
theorem theorem2_iv_positive_alpha_corrected_source_model_endpoint
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_pos : 0 < alpha) (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha)) :
    (∀ t : ItemType T, ∀ q : ℕ,
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).valueOfCount t q =
        AppliedModelingLib.pmfExp
          (decayingBernoulliFiniteLaw c d alpha q hc_pos.le hd_nonneg
            halpha_pos.le hfirst_le_one)
          rankBernoulliFiniteAllConsumedSampleValue) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            ((likelihood t) ^ (1 / alpha) /
              ∑ i : ItemType T, (likelihood i) ^ (1 / alpha))) := by
  constructor
  · intro t q
    exact theorem2_all_consumed_rank_varying_independent_bernoulli_source
      likelihood c d alpha q hc_pos.le hd_nonneg halpha_pos.le hfirst_le_one t
  · exact theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula
      likelihood alpha c d halpha_pos hc_pos hd_nonneg hlike_pos seq

/--
Corrected Theorem 2(iv) source-model endpoint covering the nonnegative-alpha
domain.  The positive-alpha branch combines the literal independent
rank-varying Bernoulli realization with the power-share conclusion.  The
zero-alpha branch instead retains the selected likelihood-argmax all-on
optimality correction, together with the same literal finite-law identity.
-/
theorem theorem2_iv_corrected_source_model_endpoint
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    (0 < alpha → ∀ hc_pos : 0 < c,
      ∀ seq :
        OptimalAllocationSequence
          (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha),
        (∀ t : ItemType T, ∀ q : ℕ,
          (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).valueOfCount t q =
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha q hc_pos.le hd_nonneg
                halpha_nonneg hfirst_le_one)
              rankBernoulliFiniteAllConsumedSampleValue) ∧
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                ((likelihood t) ^ (1 / alpha) /
                  ∑ i : ItemType T, (likelihood i) ^ (1 / alpha)))) ∧
      (alpha = 0 →
        ∀ N : ℕ, ∀ best : ItemType T,
          (∀ t : ItemType T, likelihood t ≤ likelihood best) →
          (∀ t : ItemType T, ∀ q : ℕ,
            (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).valueOfCount t q =
              AppliedModelingLib.pmfExp
                (decayingBernoulliFiniteLaw c d alpha q hc_nonneg hd_nonneg
                  halpha_nonneg hfirst_le_one)
                rankBernoulliFiniteAllConsumedSampleValue) ∧
            (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).IsOptimalAtTotal
              N (allOnTypeAllocation N best)) := by
  constructor
  · intro halpha_pos hc_pos seq
    constructor
    · intro t q
      exact theorem2_all_consumed_rank_varying_independent_bernoulli_source
        likelihood c d alpha q hc_pos.le hd_nonneg halpha_nonneg hfirst_le_one t
    · exact theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula
        likelihood alpha c d halpha_pos hc_pos hd_nonneg hlike_pos seq
  · intro halpha_zero N best hbest
    subst alpha
    constructor
    · intro t q
      exact theorem2_all_consumed_rank_varying_independent_bernoulli_source
        likelihood c d 0 q hc_nonneg hd_nonneg halpha_nonneg hfirst_le_one t
    · exact theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax
        likelihood c d N best hc_nonneg hbest

/--
Corrected Theorem 2(i) with both layers of the source probability model: a
preferred type PMF and independent rank-varying Bernoulli coordinates.

Source status: approved corrected theorem target
-/
theorem theorem2_i_corrected_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_lt_one : alpha < 1)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha)) :
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                hd_nonneg halpha_nonneg hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ))) := by
  constructor
  · intro a
    exact decayingBernoulliTopOneModel_objective_eq_source_experiment
      preferenceLaw c d alpha a hc_pos.le hd_nonneg halpha_nonneg hfirst_lt_one.le
  · exact theorem2_i_decaying_bernoulli_top_one_uniform_formula
      (fun t => (preferenceLaw t).toReal) alpha c d halpha_nonneg halpha_lt_one
      hc_pos hd_nonneg hfirst_lt_one hpreference_pos seq

/--
Corrected Theorem 2(ii) with the preferred-type PMF source semantics.

Source status: approved corrected theorem target
-/
theorem theorem2_ii_corrected_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (c d : ℝ)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d 1 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 1)) :
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 1).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d 1 (a.count t) hc_pos.le hd_nonneg
                (by norm_num) hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 / (1 + c)) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / (1 + c)))) := by
  constructor
  · intro a
    exact decayingBernoulliTopOneModel_objective_eq_source_experiment
      preferenceLaw c d 1 a hc_pos.le hd_nonneg (by norm_num) hfirst_lt_one.le
  · exact theorem2_ii_decaying_bernoulli_top_one_formula
      (fun t => (preferenceLaw t).toReal) c d hc_pos hd_nonneg hfirst_lt_one
      hpreference_pos seq

/--
Corrected Theorem 2(iii) with the preferred-type PMF source semantics.

Source status: approved corrected theorem target
-/
theorem theorem2_iii_corrected_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_gt_one : 1 < alpha) (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha)) :
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                hd_nonneg (le_of_lt (lt_trans zero_lt_one halpha_gt_one))
                hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 / alpha) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / alpha))) := by
  have halpha_nonneg : 0 ≤ alpha :=
    le_of_lt (lt_trans zero_lt_one halpha_gt_one)
  constructor
  · intro a
    exact decayingBernoulliTopOneModel_objective_eq_source_experiment
      preferenceLaw c d alpha a hc_pos.le hd_nonneg halpha_nonneg hfirst_lt_one.le
  · exact theorem2_iii_decaying_bernoulli_top_one_formula
      (fun t => (preferenceLaw t).toReal) alpha c d halpha_gt_one hc_pos hd_nonneg
      hfirst_lt_one hpreference_pos seq

/-- Corrected positive-alpha Theorem 2(iv) with full PMF source semantics. -/
theorem theorem2_iv_positive_alpha_corrected_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_pos : 0 < alpha) (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliAllConsumedConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha)) :
    (∀ a : CountAllocation T,
      (decayingBernoulliAllConsumedConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                hd_nonneg halpha_pos.le hfirst_le_one)
              rankBernoulliFiniteAllConsumedSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 / alpha) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / alpha))) := by
  constructor
  · intro a
    exact decayingBernoulliAllConsumedModel_objective_eq_source_experiment
      preferenceLaw c d alpha a hc_pos.le hd_nonneg halpha_pos.le hfirst_le_one
  · exact theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula
      (fun t => (preferenceLaw t).toReal) alpha c d halpha_pos hc_pos hd_nonneg
      hpreference_pos seq

/-- Corrected alpha-zero Theorem 2(iv) selected-argmax source endpoint. -/
theorem theorem2_iv_alpha_zero_pmf_source_model_endpoint
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (c d : ℝ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d 0 0 ≤ 1)
    (N : ℕ) (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) :
    (∀ a : CountAllocation T,
      (decayingBernoulliAllConsumedConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 0).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d 0 (a.count t) hc_nonneg hd_nonneg
                (by norm_num) hfirst_le_one)
              rankBernoulliFiniteAllConsumedSampleValue)) ∧
      (decayingBernoulliAllConsumedConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 0).IsOptimalAtTotal
          N (allOnTypeAllocation N best) := by
  constructor
  · intro a
    exact decayingBernoulliAllConsumedModel_objective_eq_source_experiment
      preferenceLaw c d 0 a hc_nonneg hd_nonneg (by norm_num) hfirst_le_one
  · exact theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax
      (fun t => (preferenceLaw t).toReal) c d N best hc_nonneg hbest

/--
Corrected Theorem 2(iv) under the full preferred-type PMF experiment.  The
positive-alpha branch has the source's power-share limit; at alpha zero that
expression is undefined, and the checked repair is likelihood-argmax
all-on optimality.

Source status: approved corrected theorem target
-/
theorem theorem2_iv_corrected_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal) :
    (0 < alpha → ∀ hc_pos : 0 < c,
      ∀ seq :
        OptimalAllocationSequence
          (fun _ => decayingBernoulliAllConsumedConsumptionModel
            (fun t => (preferenceLaw t).toReal) c d alpha),
        (∀ a : CountAllocation T,
          (decayingBernoulliAllConsumedConsumptionModel
            (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
              AppliedModelingLib.pmfExp preferenceLaw
                (fun t =>
                  AppliedModelingLib.pmfExp
                    (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                      hd_nonneg halpha_nonneg hfirst_le_one)
                    rankBernoulliFiniteAllConsumedSampleValue)) ∧
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                (((preferenceLaw t).toReal) ^ (1 / alpha) /
                  ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / alpha)))) ∧
      (alpha = 0 →
        ∀ N : ℕ, ∀ best : ItemType T,
          (∀ t : ItemType T,
            (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) →
          (∀ a : CountAllocation T,
            (decayingBernoulliAllConsumedConsumptionModel
              (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
                AppliedModelingLib.pmfExp preferenceLaw
                  (fun t =>
                    AppliedModelingLib.pmfExp
                      (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
                        hd_nonneg halpha_nonneg hfirst_le_one)
                      rankBernoulliFiniteAllConsumedSampleValue)) ∧
            (decayingBernoulliAllConsumedConsumptionModel
              (fun t => (preferenceLaw t).toReal) c d alpha).IsOptimalAtTotal
                N (allOnTypeAllocation N best)) := by
  constructor
  · intro halpha_pos hc_pos seq
    exact theorem2_iv_positive_alpha_corrected_pmf_source_model_endpoint
      preferenceLaw alpha c d halpha_pos hc_pos hd_nonneg hfirst_le_one
      hpreference_pos seq
  · intro halpha_zero N best hbest
    subst alpha
    exact theorem2_iv_alpha_zero_pmf_source_model_endpoint
      preferenceLaw c d hc_nonneg hd_nonneg (by simpa using hfirst_le_one) N best hbest

/-- Theorem 2(iv): `alpha = 0` argmax endpoint. -/
abbrev theorem2_iv_alpha_zero :=
  @theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax

/--
Theorem 2(iv): `alpha = 0` argmax endpoint.
Source status: direct source condition
-/
theorem theorem2_iv_alpha_zero_condition : type_of%
    (@theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax) :=
  @theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax

/--
The shared source-model semantics for Theorem 2's top-one branches: the
outer preferred type is a PMF draw and the inner rank coordinates are the
already-checked finite independent, rank-varying Bernoulli law.
-/
theorem theorem2_top_one_source_experiment : type_of%
    (@decayingBernoulliTopOneModel_objective_eq_source_experiment) :=
  @decayingBernoulliTopOneModel_objective_eq_source_experiment

/-- The analogous PMF-plus-rank-law source experiment for Theorem 2(iv). -/
theorem theorem2_all_consumed_source_experiment : type_of%
    (@decayingBernoulliAllConsumedModel_objective_eq_source_experiment) :=
  @decayingBernoulliAllConsumedModel_objective_eq_source_experiment

/--
Theorem 3's literal top-one source experiment: a preferred type is selected
from its PMF and the conditional rank coordinates are finite iid Bernoulli
draws with that type's displayed probability.

Source status: direct source model formula
-/
theorem theorem3_top_one_source_experiment_formula
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    ∀ a : CountAllocation T,
      B.toConsumptionModel.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hprob_pos t).le (hprob_lt_one t).le)
              rankBernoulliFiniteTopOneSampleValue) := by
  have hvalid : B.SuccessProbabilitiesValid := by
    intro t
    exact ⟨(hprob_pos t).le, (hprob_lt_one t).le⟩
  intro a
  exact bernoulliSatisfactionModel_objective_eq_source_experiment
    B preferenceLaw hpreference hvalid a

/--
Theorem 3's log-share conclusion under the literal source-model assumptions.

Source status: approved corrected theorem target
-/
theorem theorem3_log_share_conclusion
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence (fun _ => B.toConsumptionModel)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          (theorem3LogShareWeight B t /
            ∑ i : ItemType T, theorem3LogShareWeight B i)) := by
  have hlike_pos : ∀ t, 0 < B.likelihood t := by
    intro t
    rw [hpreference t]
    exact hpreference_pos t
  exact theorem3_varying_success_probability_log_share_formula
    B hprob_pos hprob_lt_one hlike_pos seq

/--
Auxiliary combined provenance bundle for Theorem 3.  The source-facing review
route selects the explicit log-share conclusion and keeps the source experiment
formula as support.
-/
theorem theorem3_source_model_endpoint
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence (fun _ => B.toConsumptionModel)) :
    (∀ a : CountAllocation T,
      B.toConsumptionModel.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hprob_pos t).le (hprob_lt_one t).le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (theorem3LogShareWeight B t /
              ∑ i : ItemType T, theorem3LogShareWeight B i)) := by
  constructor
  · exact theorem3_top_one_source_experiment_formula
      B preferenceLaw hpreference hprob_pos hprob_lt_one
  · exact theorem3_log_share_conclusion
      B preferenceLaw hpreference hprob_pos hprob_lt_one hpreference_pos seq

/-- Theorem 3: varying success probabilities, log-share formula. -/
abbrev theorem3 := @theorem3_source_model_endpoint

/-- Theorem 3 source-model endpoint in its direct share-limit form. -/
theorem theorem3_formula : type_of%
    (@theorem3_source_model_endpoint) :=
  @theorem3_source_model_endpoint

/--
Theorem 3's literal all-consumed source experiment: a preferred PMF draw and
finite iid Bernoulli conditional slate induce the displayed objective.

Source status: direct source model formula
-/
theorem theorem3_all_consumed_source_experiment_formula
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_valid : assumption_bernoulli_success_probability_range B) :
    ∀ a : CountAllocation T,
      (bernoulliAllConsumedModel B).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hprob_valid t).1 (hprob_valid t).2)
              rankBernoulliFiniteAllConsumedSampleValue) := by
  have hvalid : B.SuccessProbabilitiesValid := hprob_valid
  intro a
  exact bernoulliAllConsumedModel_objective_eq_source_experiment
    B preferenceLaw hpreference hvalid a

/--
Theorem 3's selected all-consumed argmax conclusion under its literal
Bernoulli model.

Source status: direct source theorem with selected-optimizer tie convention
-/
theorem theorem3_all_consumed_argmax_conclusion
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_valid : assumption_bernoulli_success_probability_range B)
    (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best) :
    (bernoulliAllConsumedModel B).IsOptimalAtTotal
      N (allOnTypeAllocation N best) :=
  theorem3_all_consumed_argmax_optimum B N best hbest

/--
Auxiliary combined provenance bundle for Theorem 3's all-consumed branch.
The source-facing review route selects the explicit selected-optimizer
conclusion and keeps the source experiment formula as support.
-/
theorem theorem3_all_consumed_argmax_source_model
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_valid : assumption_bernoulli_success_probability_range B)
    (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best) :
    (∀ a : CountAllocation T,
      (bernoulliAllConsumedModel B).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hprob_valid t).1 (hprob_valid t).2)
              rankBernoulliFiniteAllConsumedSampleValue)) ∧
      (bernoulliAllConsumedModel B).IsOptimalAtTotal
        N (allOnTypeAllocation N best) := by
  constructor
  · exact theorem3_all_consumed_source_experiment_formula
      B preferenceLaw hpreference hprob_valid
  · exact theorem3_all_consumed_argmax_conclusion
      B preferenceLaw hpreference hprob_valid N best hbest

theorem theorem3_all_consumed_argmax_source : type_of%
    (@theorem3_all_consumed_argmax_source_model) :=
  @theorem3_all_consumed_argmax_source_model

/--
Corollary 3's universal 0-homogeneity conclusion under the literal
preferred-type PMF and finite iid Bernoulli source model.

Source status: approved corrected corollary target
-/
theorem corollary3_iid_bernoulli_conclusion
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (uniformProfile T) := by
  have hlike_pos : ∀ t, 0 < B.likelihood t := by
    intro t
    rw [hpreference t]
    exact hpreference_pos t
  exact corollary3_iid_bernoulli_asymptotic_uniform_homogeneity
    B hprob_pos hprob_lt_one hlike_pos hprob_eq

/--
Auxiliary combined provenance bundle for Corollary 3.  The direct source-model
formula is shared with Theorem 3's top-one branch.
-/
theorem corollary3_source_model_endpoint
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j) :
    (∀ a : CountAllocation T,
      B.toConsumptionModel.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hprob_pos t).le (hprob_lt_one t).le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ConsumptionModel.AsymptoticHomogeneity
        (fun _ => B.toConsumptionModel) (uniformProfile T) := by
  constructor
  · exact theorem3_top_one_source_experiment_formula
      B preferenceLaw hpreference hprob_pos hprob_lt_one
  · exact corollary3_iid_bernoulli_conclusion
      B preferenceLaw hpreference hprob_pos hprob_lt_one hpreference_pos hprob_eq

/-- Corollary 3: iid Bernoulli gives asymptotic `0`-homogeneity. -/
theorem corollary3 : type_of%
    (@corollary3_source_model_endpoint) :=
  @corollary3_source_model_endpoint

/-! ## Appendix C: Generalizations -/

/--
Equation (13): two exclusive preference classes plus the class accepting
either type.

Source status: direct paper formula
-/
def equation13_multiplePreferenceFailure
    (p1 p2 p12 q : ℝ) (a1 a2 n : ℕ) : ℝ :=
  p1 * (1 - q) ^ a1 + p2 * (1 - q) ^ a2 + p12 * (1 - q) ^ n

/--
Equation (14): the reduced two-exclusive-class failure objective.

Source status: direct paper formula
-/
def equation14_reducedMultiplePreferenceFailure
    (p1 p2 q : ℝ) (a1 a2 : ℕ) : ℝ :=
  p1 * (1 - q) ^ a1 + p2 * (1 - q) ^ a2

/--
Equations (13)--(14): for a fixed recommendation count `n`, the term for users
who accept either type is constant across feasible allocations.  Therefore the
full and reduced two-type failure objectives induce exactly the same ordering.

Source status: direct paper implication
-/
theorem equations13_14_multiple_preference_objective_order_iff
    (p1 p2 p12 q : ℝ) (a1 a2 b1 b2 n : ℕ)
    (ha : a1 + a2 = n) (hb : b1 + b2 = n) :
    p1 * (1 - q) ^ a1 + p2 * (1 - q) ^ a2 + p12 * (1 - q) ^ n ≤
        p1 * (1 - q) ^ b1 + p2 * (1 - q) ^ b2 + p12 * (1 - q) ^ n ↔
      p1 * (1 - q) ^ a1 + p2 * (1 - q) ^ a2 ≤
        p1 * (1 - q) ^ b1 + p2 * (1 - q) ^ b2 := by
  constructor <;> intro h <;> linarith

/--
Equation (15): a finite product of positive non-satisfaction probabilities is
the exponential of the corresponding sum of logarithms.  The preference
density `mu(u) du` in the source is represented here directly by the measure
`preferenceMeasure`.

Source status: direct paper formula
-/
theorem equation15_finite_failure_product_eq_exp_sum_log
    {User Item : Type*} [MeasurableSpace User] [DecidableEq Item]
    (preferenceMeasure : MeasureTheory.Measure User)
    (items : Finset Item) (p : User → Item → ℝ)
    (hp : ∀ u : User, ∀ v ∈ items, 0 < p u v) :
    (∫ u, ∏ v ∈ items, p u v ∂preferenceMeasure) =
      ∫ u, Real.exp (∑ v ∈ items, Real.log (p u v))
        ∂preferenceMeasure := by
  apply integral_congr_ae
  filter_upwards with u
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro v hv
  exact (Real.exp_log (hp u v hv)).symm

/--
Equation (16): the finite-`n` relaxed failure integral for an item profile.
The preference density is again encoded by `preferenceMeasure`, while `alpha`
is a literal probability measure on the unit sphere.

Source status: direct paper formula
-/
noncomputable def equation16_relaxed_failure_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (preferenceMeasure : MeasureTheory.Measure (Proposition4Sphere.UnitSphere E))
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E))
    (n : ℕ) : ℝ :=
  ∫ u, Real.exp
      ((n : ℝ) *
        Proposition4Sphere.logRadialDistanceProfilePayoff
          (E := E) p alpha u)
    ∂preferenceMeasure

/--
Equation (19): `rho(u; alpha)` is the item-profile integral of the log radial
non-satisfaction kernel.

Source status: direct paper formula
-/
theorem equation19_profile_payoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E))
    (u : Proposition4Sphere.UnitSphere E) :
    Proposition4Sphere.logRadialDistanceProfilePayoff
        (E := E) p alpha u =
      ∫ v, Proposition4Sphere.logRadialDistanceKernel p v u
        ∂(alpha : MeasureTheory.Measure (Proposition4Sphere.UnitSphere E)) := by
  rfl

/--
Equation (17): the normalized-log limit defining `Gamma(alpha)` exists.  The
Eq. (20) row below expands its value as the supremum of `rho`.

Source status: direct paper formula with explicit analytic regularity
Source note: continuity of the radial kernel is the minor implicit regularity
needed to make the displayed limit exact.
-/
theorem equation17_relaxed_failure_normalizedLog_tendsto_gamma
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (Proposition4Sphere.UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure
      (Proposition4Sphere.UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hp : Continuous p)
    (hp_range :
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r ∧ p r ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * Real.log
          (equation16_relaxed_failure_integral
            (E := E) preferenceMeasure p alpha n))
      atTop
      (nhds
        (Proposition4Sphere.logRadialDistanceProfileSupValue
          (E := E) p alpha)) := by
  simpa [equation16_relaxed_failure_integral] using
    Proposition4Sphere.logRadialDistanceProfile_failureIntegral_normalizedLog_tendsto_supValue
      (E := E) preferenceMeasure p alpha hopen hp
      (fun r hr => (hp_range r hr).1)

/--
Equation (20): `Gamma(alpha)` is the supremum of the profile payoff `rho`.
Together with the Eq. (17) limit theorem, this is the exact positive-Laplace
bridge. Lean retains the preference measure throughout the finite-`n`
integrals instead of treating the source's dropped `mu(u)` as an equality.

Source status: direct paper formula with a corrected intermediate display
-/
theorem equation20_gamma_eq_sup_profilePayoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E)) :
    Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p alpha =
      sSup
        (Set.range
          (Proposition4Sphere.logRadialDistanceProfilePayoff
            (E := E) p alpha)) := by
  rfl

/--
Equation (21): expand the normalized user average of `rho` using Eq. (19).

Source status: direct paper formula
-/
theorem equation21_profile_average_unfold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E)) :
    (∫ u, Proposition4Sphere.logRadialDistanceProfilePayoff
          (E := E) p alpha u
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ u, (∫ v, Proposition4Sphere.logRadialDistanceKernel p v u
          ∂(alpha : MeasureTheory.Measure
            (Proposition4Sphere.UnitSphere E)))
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E) := by
  rfl

/--
Equation (22): Fubini swaps the normalized user and item-profile integrals.

Source status: direct paper formula with explicit integrability regularity
-/
theorem equation22_profile_average_fubini
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (Proposition4Sphere.UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E))
    (hp : Continuous p)
    (hp_range :
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r ∧ p r ≤ 1) :
    (∫ u, (∫ v, Proposition4Sphere.logRadialDistanceKernel p v u
          ∂(alpha : MeasureTheory.Measure
            (Proposition4Sphere.UnitSphere E)))
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ v, (∫ u, Proposition4Sphere.logRadialDistanceKernel p v u
          ∂Proposition4Sphere.sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E))
        ∂(alpha : MeasureTheory.Measure
          (Proposition4Sphere.UnitSphere E)) := by
  simpa [Proposition4Sphere.logRadialDistanceProfilePayoff] using
    Proposition4Sphere.logRadialDistanceProfilePayoff_sphereVolume_average_swap
      (E := E) p alpha hp (fun r hr => (hp_range r hr).1)

/--
Equation (23): Eq. (25)'s radial symmetry replaces the inner user integral by
one normalized constant.

Source status: direct paper formula
-/
theorem equation23_profile_integral_of_normalized_constant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (anchor : Proposition4Sphere.UnitSphere E)
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E)) :
    (∫ v, (∫ u, Proposition4Sphere.logRadialDistanceKernel p v u
          ∂Proposition4Sphere.sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E))
        ∂(alpha : MeasureTheory.Measure
          (Proposition4Sphere.UnitSphere E))) =
      ∫ _v : Proposition4Sphere.UnitSphere E,
        (∫ u, Proposition4Sphere.logRadialDistanceKernel p anchor u
          ∂Proposition4Sphere.sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E))
        ∂(alpha : MeasureTheory.Measure
          (Proposition4Sphere.UnitSphere E)) := by
  apply integral_congr_ae
  filter_upwards with v
  exact
    Proposition4Sphere.logRadialDistanceKernel_sphereVolumeUniform_integral_eq_anchor
      (E := E) p anchor v

/--
Equation (24): a probability profile integrates the constant from Eq. (23) to
itself.

Source status: direct paper formula
-/
theorem equation24_probabilityProfile_integral_const
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (alpha : MeasureTheory.ProbabilityMeasure
      (Proposition4Sphere.UnitSphere E))
    (C : ℝ) :
    (∫ _v : Proposition4Sphere.UnitSphere E, C
      ∂(alpha : MeasureTheory.Measure
        (Proposition4Sphere.UnitSphere E))) = C := by
  simp

/--
Equation (25): the normalized radial-kernel integral is item-independent.

Source status: direct paper formula after normalized-measure translation
Source note: the source's unnormalized constant `C` is divided by sphere mass
when represented using Lean's probability-normalized Haar measure.
-/
theorem equation25_radial_kernel_integral_eq_normalized_constant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (anchor v : Proposition4Sphere.UnitSphere E) :
    (∫ u, Proposition4Sphere.logRadialDistanceKernel p v u
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) =
      ∫ u, Proposition4Sphere.logRadialDistanceKernel p anchor u
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E) :=
  Proposition4Sphere.logRadialDistanceKernel_sphereVolumeUniform_integral_eq_anchor
    (E := E) p anchor v

/--
Equation (26): under the uniform probability profile every user payoff equals
the normalized constant, the source value `C / m(S^d)`.

Source status: direct paper formula after normalized-measure translation
-/
theorem equation26_uniform_profile_payoff_eq_normalized_constant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (anchor u : Proposition4Sphere.UnitSphere E) :
    Proposition4Sphere.logRadialDistanceProfilePayoff (E := E) p
        (Proposition4Sphere.sphereVolumeUniformProbabilityMeasure (E := E)) u =
      ∫ v, Proposition4Sphere.logRadialDistanceKernel p anchor v
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E) :=
  Proposition4Sphere.logRadialDistanceProfilePayoff_sphereVolumeUniform_eq_anchorIntegral
    (E := E) p anchor u

/--
The Eq. (26) constant-payoff formula implies the uniform profile has exactly
that user-supremum value.

Source status: direct paper consequence
-/
theorem equation26_uniform_profile_sup_eq_normalized_constant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℝ → ℝ)
    (anchor : Proposition4Sphere.UnitSphere E) :
    Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p
        (Proposition4Sphere.sphereVolumeUniformProbabilityMeasure (E := E)) =
      ∫ v, Proposition4Sphere.logRadialDistanceKernel p anchor v
        ∂Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E) :=
  Proposition4Sphere.logRadialDistanceProfileSupValue_sphereVolumeUniform_eq_anchorIntegral
    (E := E) p anchor

/-! ## Propositions -/

/-- Proposition 2: corrected uniform top-`k` route sufficient for asymptotics. -/
theorem proposition2 : type_of%
    (@proposition2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound) :=
  @proposition2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound

/--
Corrected Proposition 2 source endpoint.  It keeps the finite statement and
the downstream homogeneity conclusion together: the printed `(m + 1) / n`
error is replaced by the proved `(2m + 1) / n` error, whose vanishing still
gives the advertised square-root share limit.
-/
theorem proposition2_corrected_finite_and_sequence_source
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))) :
    (∀ N, 0 < N → ∀ a : CountAllocation T,
      (uniformTopKConsumptionModel likelihood (kseq N)).IsOptimalAtTotal N a →
        (proposition2SqrtProfile likelihood).Approx a
          ((2 * (Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ))) ∧
      seq.toAllocationSequence.ConvergesToProfile
        (proposition2SqrtProfile likelihood) := by
  constructor
  · intro N hNpos a hopt
    exact proposition2_uniform_top_k_corrected_finite_of_paper_bound
      likelihood N (kseq N) hNpos (hkpos N hNpos) hlike_pos a
      (hbound N hNpos) hopt
  · exact proposition2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Proposition 4: two-measure symmetry-driven kernel endpoint with the
positive-Laplace bridge exposed.

Source status: formalized
Source note: the generic positive-Laplace step is Lean-proved through the
large-deviation library. The paper-facing endpoint is specialized to a unit
sphere and log radial-distance kernel; Lean proves the linear-isometry action,
measurable-embedding, diagonal radial-kernel invariance, sphere transitivity,
normalized Haar-sphere measure preservation, uniform-profile objective value,
and compact-sphere maximizer. The strongest endpoint fixes the ambient Haar
measure to mathlib's finite-dimensional inner-product-space volume, takes
relaxed profiles to be literal probability measures on the unit sphere, defines
the profile objective as the user supremum, and derives the needed continuity
and integrability facts from compactness plus joint continuity of the kernel.
The exposed source-shaped wrapper retains the paper's nonconstant `(0,1]`
radial-kernel condition on the realized unit-sphere distance range `[0,2]`.
Its clarified regularity domain uses a continuous radial function and a
measurable preference density, positive almost everywhere with respect to
normalized sphere volume.  The latter connects the source preference law to
the geometric averaging measure; continuity of the density is not required.
The conclusion corrects the printed type error `Gamma(pi) in inf_alpha
Gamma(alpha)` to the intended pointwise minimization inequality.  Equations
(17) and (20) are exposed separately above as the exact bridge from the source
limit to this compact-supremum objective.
-/
theorem proposition4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (Proposition4Sphere.UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (Proposition4Sphere.UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (density : Proposition4Sphere.UnitSphere E → ENNReal)
    (hdensity : AEMeasurable density
      (Proposition4Sphere.sphereUniformMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)))
    (hdensity_pos : ∀ᵐ u ∂Proposition4Sphere.sphereUniformMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E), density u ≠ 0)
    (hpreference : preferenceMeasure =
      (Proposition4Sphere.sphereUniformMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)).withDensity density)
    (hp : Continuous p)
    (hp_nonconstant :
      ∃ r ∈ Set.Icc (0 : ℝ) 2,
        ∃ s ∈ Set.Icc (0 : ℝ) 2, p r ≠ p s)
    (hp_range :
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r ∧ p r ≤ 1) :
    ∀ alpha : MeasureTheory.ProbabilityMeasure (Proposition4Sphere.UnitSphere E),
      Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p
          (Proposition4Sphere.sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p alpha :=
  by
    haveI : MeasureTheory.IsProbabilityMeasure
        (Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) :=
      Proposition4Sphere.sphereUniformMeasure_isProbabilityMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)
    haveI : MeasureTheory.Measure.IsOpenPosMeasure
        (Proposition4Sphere.sphereUniformMeasure
          (MeasureTheory.volume : MeasureTheory.Measure E)) :=
      Proposition4Sphere.sphereUniformMeasure_isOpenPosMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)
    have hvolume_preference :
        Proposition4Sphere.sphereUniformMeasure
            (MeasureTheory.volume : MeasureTheory.Measure E) ≪
          preferenceMeasure := by
      rw [hpreference]
      exact MeasureTheory.withDensity_absolutelyContinuous' hdensity hdensity_pos
    letI : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure :=
      hvolume_preference.isOpenPosMeasure
    exact
      Proposition4Sphere.radialDistanceKernel_probabilityProfile_sphereVolumeUniform_minimizes_of_continuous_positive_profileSup
        (E := E) preferenceMeasure p inferInstance
        (PRPKG24AccuracyDiversity.Proposition4Sphere.defaultUnitSpherePoint E) hp
        (fun r hr => (hp_range r hr).1)

/-- Uniform `[0,1]` specialization retained as supporting mathematics. -/
abbrev uniform_order_statistic_topk_specialization :=
  @proposition5_uniform_order_statistic_topk_sum_eq_value

/--
Uniform `[0,1]` specialization retained as supporting mathematics.

This is not source Proposition 5, which is distribution-generic.
-/
theorem uniform_order_statistic_topk_specialization_formula : type_of%
    (@proposition5_uniform_order_statistic_topk_sum_eq_value) :=
  @proposition5_uniform_order_statistic_topk_sum_eq_value

/--
Proposition 5: for an iid sample law, the expected top-`k` value is the sum of
the upper order-statistic means.  The source's finite-mean condition derives
the finite order-statistic integrability required by expectation linearity.

Source status: approved source proposition with explicit iid finite-mean domain
-/
theorem proposition5_iid_topk_identity
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ) :
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (definition3IidOrderStatisticMean D) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure D a) k :=
  proposition5_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
    D hfinite_mean k a

/-! ## Appendix Lemmas -/

/--
Supporting compactness bridge for a separately supplied unique limiting
objective.  This is not any of source Lemma D.1(i)--(iv), whose asymptotic
premises must be derived before this bridge can be applied.
-/
theorem unique_simplex_optimizer_limit_support : type_of%
    (@lemmaD1_optimizer_sequence_limit_of_unique_simplex_limit_objective) :=
  @lemmaD1_optimizer_sequence_limit_of_unique_simplex_limit_objective

/--
Corrected generic Lemma D.1(i): every all-positive type has uniform limiting
representation under raw fixed-total integer optimality, monotonicity, and
the intended exponential saturation-gap regime.

The archival signs `B > 0`, `sigma < 0` are false for this conclusion. This
endpoint visibly uses `B < 0`, `sigma > 0`, eventual positive `A - h(a)`, and
positive weight for every source type; its proof constructs the comparison
from the raw allocation problem rather than accepting a limit-objective or
optimizer-convergence certificate.

Source status: approved corrected lemma target
-/
theorem lemmaD1_i_corrected_uniform_optimizer_shares_source
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ n in atTop,
      0 < AppendixD1GenericI.saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (AppendixD1GenericI.saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile
      (fun _ : ItemType m => 1 / (m : ℝ)) := by
  exact AppendixD1GenericI.corrected_lemmaD1_i_uniform_optimizer_shares_of_log_tail
    p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog

/--
Corrected generic Lemma D.1(ii): under the all-positive finite-support branch,
monotonicity, and the literal negative-power saturation tail, raw fixed-total
integer optimizers converge to the source power profile.

The source's limiting ratio of saturation-level objective values is invalid:
both values converge to the same saturation level. This endpoint instead
derives a direct normalized deficit comparison, rounded comparator, positive
interiority bound, strict negative-power minimizer, and compact separation
inside Lean. It takes no limiting objective, convergence, or certificate as a
premise. The source's printed zero-weight scope remains visibly outside this
all-positive endpoint.

Source status: approved corrected lemma target
-/
theorem lemmaD1_ii_corrected_powerTail_optimizer_shares_source
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail : Tendsto
      (fun n : ℕ => AppendixD1GenericII.saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile (AppendixD1GenericIIFull.targetShare p sigma) := by
  exact AppendixD1GenericIIFull.corrected_lemmaD1_ii_powerTail_optimizer_shares
    p seq hp_pos hmono hB_pos hsigma_neg htail

/--
Corrected generic Lemma D.1(iii): under the source probability convention,
all-positive weights, monotonicity, and strict discrete concavity, literal
fixed-total integer optimizers converge to the probability profile.

The source proof's weighted-log variational target is a unique maximum, not a
minimum. This endpoint derives its rounded comparator, raw-to-log comparison,
and compact separation internally; `sum p = 1` is visible rather than silently
used to identify normalized weights with `p`.

Source status: approved corrected lemma target
-/
theorem lemmaD1_iii_corrected_probability_optimizer_shares_source
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hsum : (∑ i : ItemType m, p i) = 1)
    (hmono : Monotone h) (hconc : AppendixD1GenericIII.StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (AppendixD1GenericIII.logRemainder h B C) atTop (nhds 0)) :
    seq.toSequence.ConvergesToProfile p := by
  exact AppendixD1GenericIII.corrected_lemmaD1_iii_probability_optimizer_shares_of_log_remainder
    p seq hp_pos hsum hmono hconc hB_pos hrem

/--
Corrected generic Lemma D.1(iv): under positive finite type weights, strict
discrete concavity, and the sublinear power tail, literal fixed-total integer
optimizers converge to the corrected power profile.

The raw benchmark, tail comparison, strict continuous maximizer, and compact
separation are constructed in Lean. The source's nonnegative-weight wording is
not silently covered: this endpoint visibly takes the all-positive branch.

Source status: approved corrected lemma target
-/
theorem lemmaD1_iv_corrected_powerTail_optimizer_shares_source
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : AppendixD1GenericIV.StrictDiscreteConcave h)
    (htail : Tendsto (AppendixD1GenericIV.powerTailQuotient h B sigma) atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile (AppendixD1GenericIV.targetShare p sigma) := by
  exact AppendixD1GenericIV.corrected_lemmaD1_iv_powerTail_optimizer_shares
    p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail

/-- Supporting finite top-`k` loss assembly under a CDF-power certificate. -/
abbrev bounded_cdf_power_topk_loss_support :=
  @paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support

/--
Supporting finite top-`k` loss assembly under a CDF-power certificate.

This is stronger/differently packaged than the fixed-rank source Lemma D.2
integral and is not used as direct source credit.
-/
theorem bounded_cdf_power_topk_loss_support_formula : type_of%
    (@paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support) :=
  @paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support

/-- Supporting bounded-tail forward-marginal consequence. -/
abbrev bounded_tail_forward_marginal_support :=
  @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail

/--
Supporting bounded-tail forward-marginal consequence.

The source Lemma 1 is a loss asymptotic, not this adjacent-marginal result.
-/
theorem bounded_tail_forward_marginal_support_formula : type_of%
    (@lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail) :=
  @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail

/--
Lemma 1's source-shaped top-`k` loss asymptotic under an explicit
upper-endpoint tail-mass sandwich.
-/
theorem lemma1_bounded_topk_loss_of_upper_endpoint_tail : type_of%
    (@lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail) :=
  @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail

/--
Lemma D.2's source-shaped fixed-rank integral asymptotic under the checked
near-zero/tail split certificate.  Deriving that certificate from the PDF's
density notation remains a separately audited measure/density bridge.
-/
theorem lemmaD2_fixed_rank_integral_asymptotic_of_split_certificate : type_of%
    (@lemmaD2_bounded_integral_term_asymptotic_of_split_certificate) :=
  @lemmaD2_bounded_integral_term_asymptotic_of_split_certificate

/--
Lemma D.2's fixed-rank integral asymptotic under the source's literal PDF
model.  The `withDensity` law, integrability, support, and endpoint density
ratio derive the reflected-tail law internally; callers do not supply a tail
or split certificate.

Source status: approved source lemma with explicit literal-PDF model
-/
theorem lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf_source
    {beta c M L : ℝ} {j : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) j)
      (fun a =>
        boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) := by
  exact lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf
    baseMeasure h_base_bounds hwidth_pos f hpdf hf_nonneg hf_measurable
    hf_integrable hbeta_pos hc_pos hratio

/--
Lemma 1's actual iid bounded-support top-`k` loss asymptotic under the same
literal PDF model.  This is the loss conclusion stated in the source, rather
than the adjacent forward-marginal support consequence.
-/
theorem lemma1_bounded_topk_loss_asymptotic_of_pdf_source
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (k_pos : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) := by
  exact lemma1_bounded_topk_loss_asymptotic_of_pdf
    baseMeasure h_base_bounds hwidth_pos f hpdf hf_nonneg hf_measurable
    hf_integrable hbeta_pos hc_pos hratio k_pos

/--
Lemma D.3's corrected actual-iid fixed-rank exponential formula.  The source
omits the required `1 / lambda` scale factor; this endpoint retains it.
-/
theorem lemmaD3_exponential_iid_fixed_rank_mean_source : type_of%
    (@PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference) :=
  @PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference

/--
Lemma D.3's corrected logarithmic asymptotic for the actual iid source law.
The source's positive additive constant is also incorrect for every fixed
upper rank after the maximum: the checked constant is
`(EulerMascheroniConstant - H_r) / lambda` and may be negative.
-/
theorem lemmaD3_exponential_iid_fixed_rank_asymptotic_source : type_of%
    (@PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_sub_log_tendsto) :=
  @PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_sub_log_tendsto

/--
Lemma D.3's corrected eventual strict diminishing-marginal property for the
actual iid source law.  The totalized order-statistic interface makes a global
claim over invalid small ranks inappropriate.
-/
theorem lemmaD3_exponential_iid_fixed_rank_eventual_concavity_source : type_of%
    (@PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_forward_marginal_strict_antitone_eventually) :=
  @PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_forward_marginal_strict_antitone_eventually

/--
Corrected Lemma D.3 source endpoint for the actual iid exponential law.  The
source's missing `1 / lambda` factor and invalid positive-constant condition
are replaced by the exact harmonic formula and its corrected limit; the
concavity consequence is explicitly restricted to valid eventual ranks.

Source status: approved corrected lemma target
-/
theorem lemmaD3_corrected_exponential_fixed_rank_source
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (r : ℕ) :
    (∀ q : ℕ, r < q →
      expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q - r) q =
        (1 / lambda) * (harmonicReal q - harmonicReal r)) ∧
      Filter.Tendsto
        (fun q : ℕ =>
          expectedOrderStatisticMeanSeq
              (fun a =>
                (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
              (q - r) q -
            (1 / lambda) * Real.log q)
        Filter.atTop
        (nhds
          ((1 / lambda) *
            (Real.eulerMascheroniConstant - harmonicReal r))) ∧
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 2 - r) (q + 2) -
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 1 - r) (q + 1) <
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 1 - r) (q + 1) -
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q - r) q := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hrq
    exact PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
      lambda hlambda_pos hrq
  · exact PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_sub_log_tendsto
      lambda hlambda_pos r
  · exact PRPKG24AccuracyDiversity.lemmaD3_exponential_iid_fixed_rank_forward_marginal_strict_antitone_eventually
      lambda hlambda_pos r

/--
Lemma D.4's actual iid fixed-rank Pareto asymptotic.  Validity begins
eventually because the totalized order-statistic interface has invalid small
ranks; this avoids claiming the source's global statement at those ranks.
-/
theorem lemmaD4_pareto_iid_fixed_rank_value_asymptotic_source : type_of%
    (@PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_value_asymptoticEquivalent) :=
  @PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_value_asymptoticEquivalent

/--
Lemma D.4's corrected eventual strict diminishing-marginal consequence for
the actual iid Pareto source law.
-/
theorem lemmaD4_pareto_iid_fixed_rank_eventual_concavity_source : type_of%
    (@PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_forward_marginal_strict_antitone_eventually) :=
  @PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_forward_marginal_strict_antitone_eventually

/--
Corrected Lemma D.4 source endpoint for the normalized iid Pareto law.  Its
power asymptotic and strict diminishing-marginal consequence are both stated
on the valid eventual-rank domain, avoiding the source's totalized-rank claim.
-/
theorem lemmaD4_corrected_pareto_fixed_rank_source
    {alpha : ℝ} (halpha : 1 < alpha) (r : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q)
      (fun q : ℕ =>
        paretoRankValueCoeff alpha r * ((q : ℝ) ^ (1 / alpha))) ∧
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 2 - r) (q + 2) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) <
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q := by
  exact ⟨PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_value_asymptoticEquivalent
      halpha r,
    PRPKG24AccuracyDiversity.lemmaD4_pareto_iid_fixed_rank_forward_marginal_strict_antitone_eventually
      halpha r⟩

/-- Supporting exponential homogeneity endpoint, not source Lemma D.3. -/
abbrev exponential_homogeneity_support :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/--
Supporting exponential homogeneity endpoint, not source Lemma D.3.
-/
theorem exponential_homogeneity_support_formula : type_of%
    (@theorem1_iii_exponential_top_k_order_statistic_sequence_formula) :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/-- Supporting Pareto homogeneity endpoint, not source Lemma D.4. -/
abbrev pareto_homogeneity_support :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/--
Supporting Pareto homogeneity endpoint, not source Lemma D.4.
-/
theorem pareto_homogeneity_support_formula : type_of%
    (@theorem1_iv_pareto_iid_order_statistic_sequence_formula) :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/--
Lemma D.5: a fixed-sum integer maximizer of a separable strictly concave
objective lies within the number of coordinates of a real maximizer.

The source's `strictly convex` wording is corrected to `strictly concave` for
this maximization theorem. The checked proof is derivative-free, so the partial
derivatives used in the source proof require no added differentiability
assumption.

Source status: direct corrected-source theorem
-/
theorem lemmaD5
    {κ : Type*} [Fintype κ]
    (g : κ → ℝ → ℝ) (N : ℕ) (x : κ → ℝ) (a : κ → ℕ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = (N : ℝ))
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = (N : ℝ) →
        GeneralRounding.objective g z ≤ GeneralRounding.objective g x)
    (ha_sum : (∑ i : κ, a i) = N)
    (ha_opt : ∀ b : κ → ℕ, (∑ i : κ, b i) = N →
      GeneralRounding.objective g (fun i => (b i : ℝ)) ≤
        GeneralRounding.objective g (fun i => (a i : ℝ))) :
    ∀ t : κ,
      ⌊x t⌋₊ < a t + Fintype.card κ ∧
        a t < ⌊x t⌋₊ + Fintype.card κ := by
  classical
  exact GeneralRounding.floor_count_close_of_strictConcave_maximizers
    g N x a hconc hx_nonneg hx_sum hx_opt ha_sum ha_opt

/-! ## Named Result Propositions -/

/-- The exact paper-facing proposition of Theorem 1(i). -/
def theorem1_i_formulaSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T] {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (preferenceLaw : SourcePreferenceLaw T)
    (itemLaw : PMF Omega) (value : Omega → ℝ) {xTop xSecond : ℝ}
    (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
              (fun t => (preferenceLaw t).toReal) k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_nonneg : ∀ omega, 0 ≤ value omega)
    (hvalue_le : ∀ omega, value omega ≤ xTop)
    (hvalue_split : ∀ omega, value omega = xTop ∨ value omega ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => value omega = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => ¬ value omega = xTop))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal),
    (∀ a : CountAllocation T,
      ((TopKValueOracle.common T
        (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (AppliedModelingLib.pmfProduct (Fin (a.count t)) Omega itemLaw)
              (fun sample : Fin (a.count t) → Omega =>
                AppliedModelingLib.Probability.sampleTopKSum
                  (fun i => value (sample i)) k))) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ)))

theorem theorem1_i_formulaSpec_proof : theorem1_i_formulaSpec := by
  exact theorem1_i_formula

/-- The exact paper-facing proposition of Theorem 1(ii). -/
def theorem1_ii_formulaSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (preferenceLaw : SourcePreferenceLaw T)
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_finite_mean : MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure)
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun x : ℝ => f x / ((M - x) ^ (beta - 1)))
        (nhdsWithin M (Set.Iio M)) (nhds c))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k baseMeasure)),
    (∀ a : CountAllocation T,
      (boundedIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k baseMeasure).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (definition3IidSampleMeasure baseMeasure (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (beta / (beta + 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (beta / (beta + 1))))

theorem theorem1_ii_formulaSpec_proof : theorem1_ii_formulaSpec := by
  exact theorem1_ii_formula

/-- The exact paper-facing proposition of Theorem 1(iii). -/
def theorem1_iii_formulaSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            (fun t => (preferenceLaw t).toReal) k)),
    (∀ a : CountAllocation T,
      ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure
                (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 : ℝ) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 : ℝ)))

theorem theorem1_iii_formulaSpec_proof : theorem1_iii_formulaSpec := by
  exact theorem1_iii_formula

/-- The exact paper-facing proposition of Theorem 1(iv). -/
def theorem1_iv_formulaSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          paretoIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k alpha)),
    (∀ a : CountAllocation T,
      (paretoIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (paretoIidSampleMeasure alpha (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (alpha / (alpha - 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (alpha / (alpha - 1))))

theorem theorem1_iv_formulaSpec_proof : theorem1_iv_formulaSpec := by
  exact theorem1_iv_formula

/-- The exact paper-facing proposition of Theorem 1(v). -/
def theorem1_v_selected_maximizer_conclusionSpec : Prop :=
  ∀
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T) (D : Measure ℝ)
    [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D)
    (hmean_nonneg : 0 ≤ ∫ x : ℝ, x ∂D)
    (N : ℕ) (best : ItemType T)
    (hbest : ∀ t : ItemType T,
      (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal),
    (iidAllConsumedSourceModel preferenceLaw D).IsOptimalAtTotal N
      (allOnTypeAllocation N best)

theorem theorem1_v_selected_maximizer_conclusionSpec_proof : theorem1_v_selected_maximizer_conclusionSpec := by
  exact theorem1_v_selected_maximizer_conclusion

/-- The exact paper-facing proposition of Corollary 1. -/
def corollary1Spec : Prop :=
  ∀
    {T : ℕ} [NeZero T] {k : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hk_pos : 0 < k) (hgamma_nonneg : 0 ≤ gamma)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t),
    ∃ M : ConsumptionModel T,
      Corollary1SourceIidFamily likelihood gamma k M ∧
        ∀ seq : OptimalAllocationSequence (fun _ => M),
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                ((likelihood t) ^ gamma /
                  ∑ i : ItemType T, (likelihood i) ^ gamma))

theorem corollary1Spec_proof : corollary1Spec := by
  exact corollary1

/-- The corrected exact paper-facing proposition of Proposition 2. -/
def proposition2_corrected_finite_and_sequence_sourceSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))),
    (∀ N, 0 < N → ∀ a : CountAllocation T,
      (uniformTopKConsumptionModel likelihood (kseq N)).IsOptimalAtTotal N a →
        (proposition2SqrtProfile likelihood).Approx a
          ((2 * (Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ))) ∧
      seq.toAllocationSequence.ConvergesToProfile
        (proposition2SqrtProfile likelihood)

theorem proposition2_corrected_finite_and_sequence_sourceSpec_proof : proposition2_corrected_finite_and_sequence_sourceSpec := by
  exact proposition2_corrected_finite_and_sequence_source

/-- The corrected exact paper-facing proposition of Corollary 3. -/
def corollary3_iid_bernoulli_conclusionSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j),
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (uniformProfile T)

theorem corollary3_iid_bernoulli_conclusionSpec_proof : corollary3_iid_bernoulli_conclusionSpec := by
  exact corollary3_iid_bernoulli_conclusion

/-- The corrected exact paper-facing proposition of Theorem 2(i). -/
def theorem2_i_corrected_pmf_source_model_endpointSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_lt_one : alpha < 1)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha)),
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                hd_nonneg halpha_nonneg hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ)))

theorem theorem2_i_corrected_pmf_source_model_endpointSpec_proof : theorem2_i_corrected_pmf_source_model_endpointSpec := by
  exact theorem2_i_corrected_pmf_source_model_endpoint

/-- The corrected exact paper-facing proposition of Theorem 2(ii). -/
def theorem2_ii_corrected_pmf_source_model_endpointSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (c d : ℝ)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d 1 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 1)),
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d 1).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d 1 (a.count t) hc_pos.le hd_nonneg
                (by norm_num) hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 / (1 + c)) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / (1 + c))))

theorem theorem2_ii_corrected_pmf_source_model_endpointSpec_proof : theorem2_ii_corrected_pmf_source_model_endpointSpec := by
  exact theorem2_ii_corrected_pmf_source_model_endpoint

/-- The corrected exact paper-facing proposition of Theorem 2(iii). -/
def theorem2_iii_corrected_pmf_source_model_endpointSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_gt_one : 1 < alpha) (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst_lt_one : decayingBernoulliSuccess c d alpha 0 < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence
      (fun _ => decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha)),
    (∀ a : CountAllocation T,
      (decayingBernoulliTopOneConsumptionModel
        (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                hd_nonneg (le_of_lt (lt_trans zero_lt_one halpha_gt_one))
                hfirst_lt_one.le)
              rankBernoulliFiniteTopOneSampleValue)) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 / alpha) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / alpha)))

theorem theorem2_iii_corrected_pmf_source_model_endpointSpec_proof : theorem2_iii_corrected_pmf_source_model_endpointSpec := by
  exact theorem2_iii_corrected_pmf_source_model_endpoint

/-- The corrected exact paper-facing proposition of Theorem 2(iv). -/
def theorem2_iv_corrected_pmf_source_model_endpointSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal),
    (0 < alpha → ∀ hc_pos : 0 < c,
      ∀ seq :
        OptimalAllocationSequence
          (fun _ => decayingBernoulliAllConsumedConsumptionModel
            (fun t => (preferenceLaw t).toReal) c d alpha),
        (∀ a : CountAllocation T,
          (decayingBernoulliAllConsumedConsumptionModel
            (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
              AppliedModelingLib.pmfExp preferenceLaw
                (fun t =>
                  AppliedModelingLib.pmfExp
                    (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_pos.le
                      hd_nonneg halpha_nonneg hfirst_le_one)
                    rankBernoulliFiniteAllConsumedSampleValue)) ∧
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                (((preferenceLaw t).toReal) ^ (1 / alpha) /
                  ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 / alpha)))) ∧
      (alpha = 0 →
        ∀ N : ℕ, ∀ best : ItemType T,
          (∀ t : ItemType T,
            (preferenceLaw t).toReal ≤ (preferenceLaw best).toReal) →
          (∀ a : CountAllocation T,
            (decayingBernoulliAllConsumedConsumptionModel
              (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
                AppliedModelingLib.pmfExp preferenceLaw
                  (fun t =>
                    AppliedModelingLib.pmfExp
                      (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
                        hd_nonneg halpha_nonneg hfirst_le_one)
                      rankBernoulliFiniteAllConsumedSampleValue)) ∧
            (decayingBernoulliAllConsumedConsumptionModel
              (fun t => (preferenceLaw t).toReal) c d alpha).IsOptimalAtTotal
                N (allOnTypeAllocation N best))

theorem theorem2_iv_corrected_pmf_source_model_endpointSpec_proof : theorem2_iv_corrected_pmf_source_model_endpointSpec := by
  exact theorem2_iv_corrected_pmf_source_model_endpoint

/-- The corrected exact paper-facing log-share proposition of Theorem 3. -/
def theorem3_log_share_conclusionSpec : Prop :=
  ∀
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hpreference_pos : ∀ t, 0 < (preferenceLaw t).toReal)
    (seq : OptimalAllocationSequence (fun _ => B.toConsumptionModel)),
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          (theorem3LogShareWeight B t /
            ∑ i : ItemType T, theorem3LogShareWeight B i))

theorem theorem3_log_share_conclusionSpec_proof : theorem3_log_share_conclusionSpec := by
  exact theorem3_log_share_conclusion

/-- The exact all-consumed argmax proposition of Theorem 3. -/
def theorem3_all_consumed_argmax_conclusionSpec : Prop :=
  ∀
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hprob_valid : assumption_bernoulli_success_probability_range B)
    (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best),
    (bernoulliAllConsumedModel B).IsOptimalAtTotal
      N (allOnTypeAllocation N best)

theorem theorem3_all_consumed_argmax_conclusionSpec_proof : theorem3_all_consumed_argmax_conclusionSpec := by
  exact theorem3_all_consumed_argmax_conclusion

/-- The corrected exact paper-facing proposition of Lemma D.1(ii). -/
def lemmaD1_ii_corrected_powerTail_optimizer_shares_sourceSpec : Prop :=
  ∀
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail : Tendsto
      (fun n : ℕ => AppendixD1GenericII.saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1)),
    seq.toSequence.ConvergesToProfile (AppendixD1GenericIIFull.targetShare p sigma)

theorem lemmaD1_ii_corrected_powerTail_optimizer_shares_sourceSpec_proof : lemmaD1_ii_corrected_powerTail_optimizer_shares_sourceSpec := by
  exact lemmaD1_ii_corrected_powerTail_optimizer_shares_source

/-- The exact paper-facing top-k loss proposition of Lemma 1. -/
def lemma1_bounded_topk_loss_asymptotic_of_pdf_sourceSpec : Prop :=
  ∀
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (k_pos : 0 < k),
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a)

theorem lemma1_bounded_topk_loss_asymptotic_of_pdf_sourceSpec_proof : lemma1_bounded_topk_loss_asymptotic_of_pdf_sourceSpec := by
  exact lemma1_bounded_topk_loss_asymptotic_of_pdf_source

/-- The corrected exact paper-facing proposition of Proposition 4. -/
def proposition4Spec : Prop :=
  ∀
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (Proposition4Sphere.UnitSphere E)]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (preferenceMeasure : MeasureTheory.Measure (Proposition4Sphere.UnitSphere E))
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    (p : ℝ → ℝ)
    (density : Proposition4Sphere.UnitSphere E → ENNReal)
    (hdensity : AEMeasurable density
      (Proposition4Sphere.sphereUniformMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)))
    (hdensity_pos : ∀ᵐ u ∂Proposition4Sphere.sphereUniformMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E), density u ≠ 0)
    (hpreference : preferenceMeasure =
      (Proposition4Sphere.sphereUniformMeasure
        (MeasureTheory.volume : MeasureTheory.Measure E)).withDensity density)
    (hp : Continuous p)
    (hp_nonconstant :
      ∃ r ∈ Set.Icc (0 : ℝ) 2,
        ∃ s ∈ Set.Icc (0 : ℝ) 2, p r ≠ p s)
    (hp_range :
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 2 → 0 < p r ∧ p r ≤ 1),
    ∀ alpha : MeasureTheory.ProbabilityMeasure (Proposition4Sphere.UnitSphere E),
      Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p
          (Proposition4Sphere.sphereVolumeUniformProbabilityMeasure (E := E)) ≤
        Proposition4Sphere.logRadialDistanceProfileSupValue (E := E) p alpha

theorem proposition4Spec_proof : proposition4Spec := by
  exact proposition4

/-- The exact paper-facing fixed-rank integral proposition of Lemma D.2. -/
def lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf_sourceSpec : Prop :=
  ∀
    {beta c M L : ℝ} {j : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hwidth_pos : 0 < M - L)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hf_integrable : MeasureTheory.Integrable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => f (M - u) / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ))),
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) j)
      (fun a =>
        boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a)

theorem lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf_sourceSpec_proof : lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf_sourceSpec := by
  exact lemmaD2_bounded_fixed_rank_integral_asymptotic_of_pdf_source

/-- The corrected exact paper-facing proposition of Lemma D.3. -/
def lemmaD3_corrected_exponential_fixed_rank_sourceSpec : Prop :=
  ∀
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (r : ℕ),
    (∀ q : ℕ, r < q →
      expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q - r) q =
        (1 / lambda) * (harmonicReal q - harmonicReal r)) ∧
      Filter.Tendsto
        (fun q : ℕ =>
          expectedOrderStatisticMeanSeq
              (fun a =>
                (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
              (q - r) q -
            (1 / lambda) * Real.log q)
        Filter.atTop
        (nhds
          ((1 / lambda) *
            (Real.eulerMascheroniConstant - harmonicReal r))) ∧
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 2 - r) (q + 2) -
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 1 - r) (q + 1) <
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q + 1 - r) (q + 1) -
          expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q - r) q

theorem lemmaD3_corrected_exponential_fixed_rank_sourceSpec_proof : lemmaD3_corrected_exponential_fixed_rank_sourceSpec := by
  exact lemmaD3_corrected_exponential_fixed_rank_source

/-- The corrected exact paper-facing proposition of Lemma D.4. -/
def lemmaD4_corrected_pareto_fixed_rank_sourceSpec : Prop :=
  ∀
    {alpha : ℝ} (halpha : 1 < alpha) (r : ℕ),
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q)
      (fun q : ℕ =>
        paretoRankValueCoeff alpha r * ((q : ℝ) ^ (1 / alpha))) ∧
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 2 - r) (q + 2) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) <
        expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q + 1 - r) (q + 1) -
          expectedOrderStatisticMeanSeq (paretoIidSampleMeasure alpha) (q - r) q

theorem lemmaD4_corrected_pareto_fixed_rank_sourceSpec_proof : lemmaD4_corrected_pareto_fixed_rank_sourceSpec := by
  exact lemmaD4_corrected_pareto_fixed_rank_source

/-- The corrected exact paper-facing proposition of Lemma D.5. -/
def lemmaD5Spec : Prop :=
  ∀
    {κ : Type*} [Fintype κ]
    (g : κ → ℝ → ℝ) (N : ℕ) (x : κ → ℝ) (a : κ → ℕ)
    (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i))
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i : κ, x i) = (N : ℝ))
    (hx_opt : ∀ z : κ → ℝ,
      (∀ i, 0 ≤ z i) → (∑ i : κ, z i) = (N : ℝ) →
        GeneralRounding.objective g z ≤ GeneralRounding.objective g x)
    (ha_sum : (∑ i : κ, a i) = N)
    (ha_opt : ∀ b : κ → ℕ, (∑ i : κ, b i) = N →
      GeneralRounding.objective g (fun i => (b i : ℝ)) ≤
        GeneralRounding.objective g (fun i => (a i : ℝ))),
    ∀ t : κ,
      ⌊x t⌋₊ < a t + Fintype.card κ ∧
        a t < ⌊x t⌋₊ + Fintype.card κ

theorem lemmaD5Spec_proof : lemmaD5Spec := by
  exact lemmaD5

/-- The exact paper-facing iid identity of Proposition 5. -/
def proposition5_iid_topk_identitySpec : Prop :=
  ∀
    (D : Measure ℝ) [IsProbabilityMeasure D]
    (hfinite_mean : Integrable (fun x : ℝ => x) D) (k a : ℕ),
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (definition3IidOrderStatisticMean D) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure D a) k

theorem proposition5_iid_topk_identitySpec_proof : proposition5_iid_topk_identitySpec := by
  exact proposition5_iid_topk_identity

/-- The corrected exact paper-facing proposition of Appendix Lemma D.1(i). -/
def lemmaD1_i_corrected_uniform_optimizer_shares_sourceSpec : Prop :=
  ∀
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ n in atTop,
      0 < AppendixD1GenericI.saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (AppendixD1GenericI.saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1)),
    seq.toSequence.ConvergesToProfile
      (fun _ : ItemType m => 1 / (m : ℝ))

theorem lemmaD1_i_corrected_uniform_optimizer_shares_sourceSpec_proof :
    lemmaD1_i_corrected_uniform_optimizer_shares_sourceSpec := by
  exact lemmaD1_i_corrected_uniform_optimizer_shares_source

/-- The corrected exact paper-facing proposition of Appendix Lemma D.1(iii). -/
def lemmaD1_iii_corrected_probability_optimizer_shares_sourceSpec : Prop :=
  ∀
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hsum : (∑ i : ItemType m, p i) = 1)
    (hmono : Monotone h) (hconc : AppendixD1GenericIII.StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (AppendixD1GenericIII.logRemainder h B C) atTop (nhds 0)),
    seq.toSequence.ConvergesToProfile p

theorem lemmaD1_iii_corrected_probability_optimizer_shares_sourceSpec_proof :
    lemmaD1_iii_corrected_probability_optimizer_shares_sourceSpec := by
  exact lemmaD1_iii_corrected_probability_optimizer_shares_source

/-- The corrected exact paper-facing proposition of Appendix Lemma D.1(iv). -/
def lemmaD1_iv_corrected_powerTail_optimizer_shares_sourceSpec : Prop :=
  ∀
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : AppendixD1GenericIV.StrictDiscreteConcave h)
    (htail : Tendsto (AppendixD1GenericIV.powerTailQuotient h B sigma) atTop (nhds 1)),
    seq.toSequence.ConvergesToProfile (AppendixD1GenericIV.targetShare p sigma)

theorem lemmaD1_iv_corrected_powerTail_optimizer_shares_sourceSpec_proof :
    lemmaD1_iv_corrected_powerTail_optimizer_shares_sourceSpec := by
  exact lemmaD1_iv_corrected_powerTail_optimizer_shares_source

end PaperInterface
end PRPKG24AccuracyDiversity
