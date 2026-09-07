import PRPKG24AccuracyDiversity.MainTheorems

/-!
# Proof Interface: Reconciling the Accuracy-Diversity Trade-off

This file preserves the implementation-facing endpoint ledger for the PRPKG
2024 accuracy-diversity formalization.  The compact human-review surface is
`PaperInterface.lean`; this file retains the larger theorem wrappers used by
downstream proof work and older documentation.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace PaperInterface

/-! ## Paper Definitions -/

/-- Definition 1 style gamma-homogeneity profile. -/
abbrev gammaProfile {T : ℕ} := GammaHomogeneityProfile T

/-- Definition 1 `γ = ∞` complete-homogeneity profile. -/
abbrev infiniteGammaProfile {T : ℕ} := InfiniteGammaHomogeneityProfile T

/-- Definition 2 style sequence convergence to a representation profile. -/
abbrev convergesToProfile {T : ℕ} := AllocationSequence.ConvergesToProfile (T := T)

/--
Definition 1 target-share formula:
`p_t^gamma / sum_i p_i^gamma`.
-/
theorem definition1_gamma_target_share_eq
    {T : ℕ} (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (t : ItemType T)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0) :
    (gammaLikelihoodProfile likelihood gamma).targetShare t =
      (likelihood t) ^ gamma /
        ∑ i : ItemType T, (likelihood i) ^ gamma :=  gammaLikelihoodProfile_targetShare_eq likelihood gamma t hnorm

/--
Definition 1 finite γ-homogeneity, stated directly with the paper's equation
(5) target shares.
-/
theorem definition1_gamma_homogeneity_exact_iff
    {T : ℕ} (a : CountAllocation T) (likelihood : ItemType T → ℝ)
    (gamma : ℝ)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0) :
    (gammaLikelihoodProfile likelihood gamma).Exact a ↔
      ∀ t : ItemType T,
        CountAllocation.representation a t =
          (likelihood t) ^ gamma /
            ∑ i : ItemType T, (likelihood i) ^ gamma :=
    PRPKG24AccuracyDiversity.paper_definition1_gamma_homogeneity_exact_iff
      a likelihood gamma hnorm

/--
Definition 1 `γ = ∞` homogeneity, stated as complete representation of a
chosen likelihood maximizer.
-/
theorem definition1_infinite_homogeneity_exact_iff
    {T : ℕ} (a : CountAllocation T)
    (G : InfiniteGammaHomogeneityProfile T) :
    G.Exact a ↔
      CountAllocation.representation a G.best = 1 ∧
        ∀ t : ItemType T, t ≠ G.best →
          CountAllocation.representation a t = 0 :=
    PRPKG24AccuracyDiversity.paper_definition1_infinite_homogeneity_exact_iff a G

/--
Definition 1 complete source-facing theorem: finite real `γ` satisfies
equation (5), and `γ = ∞` is complete homogeneity at a likelihood maximizer.
-/
theorem definition1_gamma_homogeneity_complete
    {T : ℕ} (a : CountAllocation T) (likelihood : ItemType T → ℝ)
    (gamma : ℝ)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0)
    (best : ItemType T)
    (hbest : ∀ t : ItemType T, likelihood t ≤ likelihood best) :
    ((gammaLikelihoodProfile likelihood gamma).Exact a ↔
      ∀ t : ItemType T,
        CountAllocation.representation a t =
          (likelihood t) ^ gamma /
            ∑ i : ItemType T, (likelihood i) ^ gamma) ∧
    ((infiniteLikelihoodProfile likelihood best hbest).Exact a ↔
      CountAllocation.representation a best = 1 ∧
        ∀ t : ItemType T, t ≠ best →
          CountAllocation.representation a t = 0) :=
    PRPKG24AccuracyDiversity.paper_definition1_gamma_homogeneity_complete
      a likelihood gamma hnorm best hbest

/--
Definition 2 sequence γ-homogeneity, stated directly with the paper's equation
(6) limit target shares.
-/
theorem definition2_gamma_homogeneity_sequence_iff
    {T : ℕ} (seq : AllocationSequence T)
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0) :
    seq.ConvergesToProfile (gammaLikelihoodProfile likelihood gamma) ↔
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            ((likelihood t) ^ gamma /
              ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
    PRPKG24AccuracyDiversity.paper_definition2_gamma_homogeneity_sequence_iff
      seq likelihood gamma hnorm

/--
Definition 3 / Proposition 5 interface: the top-`k` sum induced by
bottom-indexed order-statistic means.
-/
theorem definition3_order_statistic_topk_sum_from_mean
    (mu : ℕ → ℕ → ℝ) (k a : ℕ) :
    orderStatisticTopKSumFromMean mu k a =
      ∑ i ∈ Finset.range (min k a), mu (a - i) a :=
    PRPKG24AccuracyDiversity.paper_definition3_order_statistic_topk_sum_from_mean
      mu k a

/--
Definition 3 finite-prefix bridge: for fixed `k`, after `a ≥ k`, the
bottom-indexed `μ_D` top-`k` sum is the fixed `Fin k` source-mean sum used by
the bounded-support asymptotic layer.
-/
theorem definition3_order_statistic_topk_loss_eventually_eq_fin_loss
    (M : ℝ) (mu : ℕ → ℕ → ℝ) (k : ℕ) :
    ∀ᶠ a in Filter.atTop,
      (k : ℝ) * M - orderStatisticTopKSumFromMean mu k a =
        (k : ℝ) * M - ∑ i : Fin k, mu (a - i.val) a :=
    PRPKG24AccuracyDiversity.paper_definition3_order_statistic_topk_loss_eventually_eq_fin_loss
      M mu k

/--
Pointwise source bridge for Definition 3: a concrete real sample tuple induces
the paper's bottom-indexed order-statistic top-`k` sum.
-/
theorem definition3_order_statistic_topk_sum_from_sample
    {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean
        (fun rank sampleSize =>
          if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
        k a =
      AppliedModelingLib.Probability.sampleTopKSum sample k :=
    PRPKG24AccuracyDiversity.paper_definition3_order_statistic_topk_sum_from_sample
      sample k

/--
Measurability of the paper's bottom-indexed sample order-statistic value.
-/
theorem definition3_sample_order_statistic_value_measurable
    {a : ℕ} (rank : ℕ) :
    Measurable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_order_statistic_value_measurable
      rank

/--
Pointwise bounded-support reflection for real sample tuples.
-/
theorem definition3_sample_topk_endpoint_loss_eq_reflected_bottom_sum
    (M : ℝ) {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    AppliedModelingLib.Probability.sampleTopKEndpointLoss M sample k =
      AppliedModelingLib.Probability.reflectedBottomKSum M sample k :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_topk_endpoint_loss_eq_reflected_bottom_sum
      M sample k

/--
Pointwise layer-cake form of the reflected bottom-`k` sum.
-/
theorem definition3_reflected_bottom_sum_eq_integral_rank_count_indicator
    (M : ℝ) {a : ℕ} (sample : Fin a → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    AppliedModelingLib.Probability.reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k a),
          if (Finset.univ.filter
              (fun j : Fin a =>
                AppliedModelingLib.Probability.reflectedSample M sample j ≤ x)).card ≤
              (AppliedModelingLib.Probability.topKRankEmbedding k a i).val
          then (1 : ℝ) else 0 :=
    PRPKG24AccuracyDiversity.paper_definition3_reflected_bottom_sum_eq_integral_rank_count_indicator
      M sample k hM

/--
Pointwise bounded-support envelope: if all sample values are at most the
endpoint `M`, then the reflected bottom-`k` sum is nonnegative.
-/
theorem definition3_reflected_bottom_sum_nonneg_of_forall_le
    (M : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ AppliedModelingLib.Probability.reflectedBottomKSum M sample k :=
    PRPKG24AccuracyDiversity.paper_definition3_reflected_bottom_sum_nonneg_of_forall_le
      M hM k

/--
Pointwise bounded-support envelope: if all sample values are at least `L`,
then the reflected bottom-`k` sum is bounded by `min k a * (M - L)`.
-/
theorem definition3_reflected_bottom_sum_le_of_forall_lower
    (M L : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    AppliedModelingLib.Probability.reflectedBottomKSum M sample k ≤
      (min k a : ℝ) * (M - L) :=
    PRPKG24AccuracyDiversity.paper_definition3_reflected_bottom_sum_le_of_forall_lower
      M L hL k

/--
Pointwise bounded-support envelope for the top-`k` endpoint loss.
-/
theorem definition3_sample_topk_endpoint_loss_le_of_forall_bounds
    (M L : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    AppliedModelingLib.Probability.sampleTopKEndpointLoss M sample k ≤
      (min k a : ℝ) * (M - L) :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_topk_endpoint_loss_le_of_forall_bounds
      M L hL k

/--
Bounded-support integrability of a single sample order-statistic value.
-/
theorem definition3_sample_order_statistic_value_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (rank : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) mu :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_order_statistic_value_integrable_of_ae_bounds
      L U mu rank h_bounds

/--
Bounded-support integrability for every order-statistic value in the paper's
top-`k` finite sum.
-/
theorem definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    ∀ i ∈ Finset.range (min k a),
      MeasureTheory.Integrable
        (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample (a - i)) mu :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
      L U mu k h_bounds

/--
Bounded-support integrability of the pointwise top-`k` sample sum.
-/
theorem definition3_sample_topk_sum_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => AppliedModelingLib.Probability.sampleTopKSum sample k) mu :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_topk_sum_integrable_of_ae_bounds
      L U mu k h_bounds

/--
Bounded-support integrability of the pointwise top-`k` endpoint loss.
-/
theorem definition3_sample_topk_endpoint_loss_integrable_of_ae_bounds
    (M L : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ =>
        AppliedModelingLib.Probability.sampleTopKEndpointLoss M sample k) mu :=
    PRPKG24AccuracyDiversity.paper_definition3_sample_topk_endpoint_loss_integrable_of_ae_bounds
      M L mu k h_bounds

/--
Bounded-support integrability of the reflected bottom-`k` aggregate.
-/
theorem definition3_reflected_bottom_sum_integrable_of_ae_bounds
    (M L : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ =>
        AppliedModelingLib.Probability.reflectedBottomKSum M sample k) mu :=
    PRPKG24AccuracyDiversity.paper_definition3_reflected_bottom_sum_integrable_of_ae_bounds
      M L mu k h_bounds

/--
Measure-level Definition 3 bridge from expected sample order-statistic means
to expected top-`k` sample value.
-/
theorem definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum
    {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) mu) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean mu) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum mu k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum
      mu k h_integrable

/--
Bounded-support version of the measure-level Definition 3 bridge.
-/
theorem definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
    (L U : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean mu) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum mu k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
      L U mu k h_bounds

/--
Measure-level bounded-support reflection in the paper's `μ_D` interface.
-/
theorem definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    (M : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure mu] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) mu)
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => AppliedModelingLib.Probability.sampleTopKSum sample k) mu) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean mu) k a =
      AppliedModelingLib.Probability.expectedReflectedBottomKSum M mu k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum
      M mu k h_order_integrable h_top_integrable

/--
Bounded-support version of the measure-level reflection bridge.
-/
theorem definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
    (M L : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure mu] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂mu, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean mu) k a =
      AppliedModelingLib.Probability.expectedReflectedBottomKSum M mu k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
      M L mu k h_bounds

/--
Definition 3 bridge for a family of finite real-sample laws, producing the
paper's global `μ_D(rank,a)` interface across sample sizes.
-/
theorem definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a)) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum (sampleMeasure a) k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum
      sampleMeasure k a h_integrable

/--
Bounded-support version of the varying-sample-size Definition 3 bridge.
-/
theorem definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
    (L U : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ) [MeasureTheory.IsFiniteMeasure (sampleMeasure a)]
    (h_bounds :
      ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum (sampleMeasure a) k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
      L U sampleMeasure k a h_bounds

/--
Bounded-support reflection bridge for a family of finite real-sample laws in
the paper's global `μ_D(rank,a)` interface.
-/
theorem definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    (M : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    {a : ℕ} [MeasureTheory.IsProbabilityMeasure (sampleMeasure a)] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a))
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => AppliedModelingLib.Probability.sampleTopKSum sample k)
        (sampleMeasure a)) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      AppliedModelingLib.Probability.expectedReflectedBottomKSum
        M (sampleMeasure a) k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum
      M sampleMeasure k h_order_integrable h_top_integrable

/--
Bounded-support version of the varying-sample-size reflection bridge.
-/
theorem definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
    (M L : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    {a : ℕ} [MeasureTheory.IsProbabilityMeasure (sampleMeasure a)] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      AppliedModelingLib.Probability.expectedReflectedBottomKSum
        M (sampleMeasure a) k :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
      M L sampleMeasure k h_bounds

/--
Measure-level linearity bridge for the bounded reflected endpoint term.
-/
theorem definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals
    (M : ℝ) {a : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k a),
        MeasureTheory.Integrable
          (fun sample =>
            AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample M sample)
              (AppliedModelingLib.Probability.topKRankEmbedding k a i))
          mu) :
    AppliedModelingLib.Probability.expectedReflectedBottomKSum M mu k =
      ∑ i : Fin (min k a),
        ∫ sample,
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample M sample)
            (AppliedModelingLib.Probability.topKRankEmbedding k a i) ∂mu :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals
      M mu k h_integrable

/--
Fixed-`k` version of the reflected-bottom linearity bridge for the eventual
regime `k ≤ a`.
-/
theorem definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals_of_le
    (M : ℝ) {a k : ℕ} (mu : MeasureTheory.Measure (Fin a → ℝ))
    (hka : k ≤ a)
    (h_integrable :
      ∀ i : Fin k,
        MeasureTheory.Integrable
          (fun sample =>
            AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hka⟩)
          mu) :
    AppliedModelingLib.Probability.expectedReflectedBottomKSum M mu k =
      ∑ i : Fin k,
        ∫ sample,
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂mu :=
    PRPKG24AccuracyDiversity.paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals_of_le
      M mu hka h_integrable

/-- Definition 3 oracle constructor from paper order-statistic means. -/
noncomputable def definition3_topk_value_oracle_from_order_statistic_mean
    (T : ℕ) (mu : ℕ → ℕ → ℝ) : TopKValueOracle T :=
  PRPKG24AccuracyDiversity.paper_definition3_topk_value_oracle_from_order_statistic_mean
    T mu

@[simp] theorem definition3_topk_value_oracle_expectedTopSum
    (T : ℕ) (mu : ℕ → ℕ → ℝ) (k : ℕ) (t : ItemType T) (a : ℕ) :
    (definition3_topk_value_oracle_from_order_statistic_mean T mu).expectedTopSum
        k t a =
      orderStatisticTopKSumFromMean mu k a := rfl

/--
Proposition 5, uniform `[0,1]` instance in the paper's bottom-indexed
order-statistic convention.
-/
theorem proposition5_uniform_order_statistic_topk_sum_eq_value
    (k a : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k a =
      uniformTopKValue k a :=
    PRPKG24AccuracyDiversity.paper_proposition5_uniform_order_statistic_topk_sum_eq_value
      k a

/--
Source Theorem 1(ii), uniform `[0,1]` order-statistic marginal asymptotic as
a reusable bounded-branch scaled-marginal certificate with `β = 1`.
-/
noncomputable def theorem1_ii_uniform_order_statistic_scaled_marginal_certificate
    (T : ℕ) {k : ℕ} (k_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean) k
      (boundedPowerMarginalScale 1)
      (fun _ : ItemType T => uniformTopKFactor k) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_order_statistic_scaled_marginal_certificate
    T k_pos

/--
Source Theorem 1(ii), concrete iid uniform `[0,1]` order-statistic marginal
asymptotic as a reusable bounded-branch scaled-marginal certificate with
`β = 1`.
-/
noncomputable def theorem1_ii_uniform01_iid_order_statistic_scaled_marginal_certificate
    (T : ℕ) {k : ℕ} (k_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T uniform01IidOrderStatisticMeanSeq) k
      (boundedPowerMarginalScale 1)
      (fun _ : ItemType T => uniformTopKFactor k) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform01_iid_order_statistic_scaled_marginal_certificate
    T k_pos

/--
Source Theorem 1(ii), uniform order-statistic oracle equivalence to the
closed-form uniform top-`k` consumption model.
-/
theorem theorem1_ii_uniform_order_statistic_toConsumptionModel_eq
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ) :
    (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
        likelihood k =
      uniformTopKConsumptionModel likelihood k :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_order_statistic_toConsumptionModel_eq
      likelihood k

/--
Source Theorem 1(ii), concrete iid uniform `[0,1]` order-statistic oracle
equivalence to the closed-form uniform top-`k` consumption model.
-/
theorem theorem1_ii_uniform01_iid_order_statistic_toConsumptionModel_eq
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ) :
    (TopKValueOracle.ofOrderStatisticMean T uniform01IidOrderStatisticMeanSeq).toConsumptionModel
        likelihood k =
      uniformTopKConsumptionModel likelihood k :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform01_iid_order_statistic_toConsumptionModel_eq
      likelihood k

/--
Theorem 1(i) finite-discrete proof algebra: a pure geometric tail has the
paper's logarithmic saturation ratio.
-/
theorem theorem1_i_finite_discrete_log_geometric_tail_ratio
    {C r : ℝ} (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (C * r ^ N) / (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_log_geometric_tail_ratio
    hC hr_pos hr_lt_one

/--
Theorem 1(i) finite-discrete proof algebra: a fixed polynomial factor on a
geometric tail does not change the paper's logarithmic saturation ratio.
-/
theorem theorem1_i_finite_discrete_log_polynomial_geometric_tail_ratio
    {C r : ℝ} (d : ℕ)
    (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_log_polynomial_geometric_tail_ratio
    d hC hr_pos hr_lt_one

/--
Theorem 1(i) finite-discrete proof algebra: the paper's geometric lower and
polynomial-times-geometric upper bounds squeeze the logarithmic saturation
ratio to one.
-/
theorem theorem1_i_finite_discrete_log_tail_ratio_of_geometric_bounds
    {gap : ℕ → ℝ} {lower upper r : ℝ} (d : ℕ)
    (hlower_pos : 0 < lower) (hupper_pos : 0 < upper)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hlower :
      ∀ᶠ N in Filter.atTop, lower * r ^ N ≤ gap N)
    (hupper :
      ∀ᶠ N in Filter.atTop, gap N ≤ upper * (N : ℝ) ^ d * r ^ N) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (gap N) / (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_log_tail_ratio_of_geometric_bounds
    d hlower_pos hupper_pos hr_pos hr_lt_one hlower hupper

/--
Theorem 1(i) finite-discrete proof algebra: equations (81)-(83), bounding the
probability of fewer than `k` top-support draws by a polynomial-geometric tail.
-/
theorem theorem1_i_finite_discrete_top_mass_failure_tail_bound
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_top_mass_failure_tail_bound
    hk_pos hk_le_a hq_nonneg hq_le_one hrho_nonneg hrho_le_one

/--
Theorem 1(i) finite-discrete proof algebra: the upper binomial tail after
absorbing the fixed `k-1` exponent shift into the constant.
-/
theorem theorem1_i_finite_discrete_top_mass_failure_tail_bound_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_top_mass_failure_tail_bound_at_a
    hk_pos hk_le_a hq_nonneg hq_le_one hrho_pos hrho_le_one

/--
Theorem 1(i) finite-discrete proof algebra: the upper marginal's old-sample
failure tail at `a-1` is controlled by the certificate tail at `a`.
-/
theorem theorem1_i_finite_discrete_top_mass_failure_tail_pred_le_inv_mul
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_top_mass_failure_tail_pred_le_inv_mul
    ha_pos hq_nonneg hrho_pos

/--
Theorem 1(i) finite-discrete proof algebra: the exact `k-1` top-count event
used for the lower marginal has at least the displayed single-term mass.
-/
theorem theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_pred_le_a : k - 1 ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    q ^ k * rho ^ (a + 1 - k) ≤
      finiteDiscreteTopMassPromotingEvent k a q rho :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound
    hk_pos hk_pred_le_a hq_nonneg hrho_nonneg

/--
Theorem 1(i) finite-discrete proof algebra: the lower exact-event mass after
absorbing the fixed `k-1` exponent shift into the constant.
-/
theorem theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a ≤
      finiteDiscreteTopMassPromotingEvent k a q rho :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound_at_a
    hk_pos hk_le_a hq_nonneg hrho_pos

/-! ## Example 1: Recovering Calibration -/

/--
Example 1 likelihoods: romance is Lean type `0`, action is Lean type `1`.
-/
noncomputable abbrev example1GenreLikelihood (p1 p2 : ℝ) : ItemType 2 → ℝ := example1Likelihood p1 p2

/--
Example 1 all-consumed model with common exponential mean `1/lambda`.
-/
noncomputable abbrev example1AllConsumed
    (p1 p2 lambda : ℝ) : ConsumptionModel 2 := example1AllConsumedModel p1 p2 lambda

/--
Example 1 top-one log-relaxation objective:
`(p1/lambda) log x + (p2/lambda) log y`.
-/
noncomputable abbrev example1TopOneLogObjective
    (p1 p2 lambda x y : ℝ) : ℝ := example1LogRelaxedObjective p1 p2 lambda x y

/--
Example 1 all-consumed side: when romance is at least as likely as action, a
romance-only slate is optimal.
-/
theorem example1_all_consumed_all_romance_is_optimal
    {p1 p2 lambda : ℝ} (N : ℕ)
    (hlambda : 0 < lambda) (hp2_le_p1 : p2 ≤ p1) :
    (example1AllConsumed p1 p2 lambda).IsOptimalAtTotal
      N (allOnTypeAllocation N (0 : ItemType 2)) :=
    PRPKG24AccuracyDiversity.paper_example1_all_consumed_all_romance_is_optimal
      N hlambda hp2_le_p1

/--
Example 1 all-consumed unique-argmax side: when `p1 > p2`, every all-consumed
optimum assigns zero items to the action genre.
-/
theorem example1_all_consumed_only_romance
    {p1 p2 lambda : ℝ} {N : ℕ} (a : CountAllocation 2)
    (hlambda : 0 < lambda) (hp2_lt_p1 : p2 < p1)
    (hopt : (example1AllConsumed p1 p2 lambda).IsOptimalAtTotal N a) :
    a.count (1 : ItemType 2) = 0 :=
    PRPKG24AccuracyDiversity.paper_example1_all_consumed_only_romance
      a hlambda hp2_lt_p1 hopt

/--
Example 1 feasibility check: the calibrated relaxed split has total `n`.
-/
theorem example1_calibrated_split_sum
    {p1 p2 n : ℝ} (hp_sum : p1 + p2 = 1) :
    p1 * n + p2 * n = n := PRPKG24AccuracyDiversity.paper_example1_calibrated_split_sum hp_sum

/--
Example 1 top-one side: the calibrated relaxed split maximizes the displayed
log-relaxation objective among positive relaxed splits with total `n`.
-/
theorem example1_top_one_log_relaxation_calibrated
    {p1 p2 lambda n x y : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hlambda : 0 < lambda)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y)
    (hp_sum : p1 + p2 = 1) (hxy_sum : x + y = n) :
    example1TopOneLogObjective p1 p2 lambda x y ≤
      example1TopOneLogObjective p1 p2 lambda (p1 * n) (p2 * n) :=
  PRPKG24AccuracyDiversity.paper_example1_top_one_log_relaxation_calibrated
    hp1 hp2 hlambda hn hx hy hp_sum hxy_sum

/--
Example 1 exact top-one exponential target share for the romance genre.
-/
theorem example1_gamma_one_targetShare_romance
    {p1 p2 : ℝ} (hp_sum : p1 + p2 = 1) :
    (gammaLikelihoodProfile (example1GenreLikelihood p1 p2) 1).targetShare
      (0 : ItemType 2) = p1 :=
  PRPKG24AccuracyDiversity.paper_example1_gamma_one_targetShare_romance hp_sum

/--
Example 1 exact top-one exponential target share for the action genre.
-/
theorem example1_gamma_one_targetShare_action
    {p1 p2 : ℝ} (hp_sum : p1 + p2 = 1) :
    (gammaLikelihoodProfile (example1GenreLikelihood p1 p2) 1).targetShare
      (1 : ItemType 2) = p2 :=
  PRPKG24AccuracyDiversity.paper_example1_gamma_one_targetShare_action hp_sum

/--
Example 1 exact top-one exponential side: optimal sequences for the harmonic
exponential top-one oracle converge to the `γ = 1` likelihood profile.
-/
theorem example1_top_one_exponential_harmonic_calibrated
    {p1 p2 lambda : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hlambda : 0 < lambda)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle 2 lambda).toConsumptionModel
            (example1GenreLikelihood p1 p2) 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile (example1GenreLikelihood p1 p2) 1) :=
  PRPKG24AccuracyDiversity.paper_example1_top_one_exponential_harmonic_calibrated
    hp1 hp2 hlambda seq

/--
Example 1 exact top-one exponential sequence formula: under `p1 + p2 = 1`,
the exact optimum sequence converges to the calibrated shares `(p1, p2)`.
-/
theorem example1_top_one_exponential_harmonic_sequence_formula
    {p1 p2 lambda : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hlambda : 0 < lambda)
    (hp_sum : p1 + p2 = 1)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle 2 lambda).toConsumptionModel
            (example1GenreLikelihood p1 p2) 1)) :
    Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N)
          (0 : ItemType 2))
        Filter.atTop (nhds p1) ∧
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N)
          (1 : ItemType 2))
        Filter.atTop (nhds p2) :=
  PRPKG24AccuracyDiversity.paper_example1_top_one_exponential_harmonic_sequence_formula
    hp1 hp2 hlambda hp_sum seq

/-! ## Proposition 2 Definitions -/

/--
Proposition 2 square-root target share:
`sqrt(p_t) / sum_i sqrt(p_i)`.
-/
noncomputable abbrev proposition2SqrtShare {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) : ℝ :=
  Real.sqrt (likelihood t) /
    ∑ i : ItemType T, Real.sqrt (likelihood i)

/--
Proposition 2 `1/2`-homogeneity target profile with weights `sqrt(p_t)`.
-/
noncomputable abbrev proposition2SqrtProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) : GammaHomogeneityProfile T := sqrtLikelihoodProfile likelihood

theorem proposition2_sqrt_profile_target_share_eq
    {T : ℕ} (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (proposition2SqrtProfile likelihood).targetShare t =
      proposition2SqrtShare likelihood t :=  sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm

theorem proposition2_sqrt_profile_target_share_eq_gamma_half
    {T : ℕ} (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (proposition2SqrtProfile likelihood).targetShare t =
      (gammaLikelihoodProfile likelihood (1 / 2)).targetShare t :=
    PRPKG24AccuracyDiversity.paper_uniform_sqrt_profile_targetShare_eq_gamma_half
      likelihood t hnorm

/-! ## Source Theorems -/

/-- Finite optimizer existence for a fixed slate size. -/
theorem finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)] (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a :=  PRPKG24AccuracyDiversity.ConsumptionModel.paper_finite_optimum_exists M N

/--
Source Theorem 1(v), all-consumed/no-consumption-constraint core: when every
type has the same nonnegative conditional mean, all recommendations on a
max-likelihood type are optimal.
-/
theorem theorem1_all_consumed_common_mean_argmax_optimum
    {T : ℕ} (likelihood : ItemType T → ℝ) (mean : ℝ) (N : ℕ)
    (best : ItemType T)
    (hmean_nonneg : 0 ≤ mean)
    (hbest : ∀ t, likelihood t ≤ likelihood best) :
    (ConsumptionModel.linearized likelihood (fun _ => mean)).IsOptimalAtTotal
      N (allOnTypeAllocation N best) :=
    PRPKG24AccuracyDiversity.ConsumptionModel.paper_theorem1_all_consumed_common_mean_argmax_optimum
      likelihood mean N best hmean_nonneg hbest

/--
Source Theorem 1(v), unique-argmax converse: if the common mean is positive
and one type has strictly largest likelihood, every optimum assigns zero count
to all other types.
-/
theorem theorem1_all_consumed_unique_common_mean_only_argmax
    {T : ℕ} (likelihood : ItemType T → ℝ) (mean : ℝ) (N : ℕ)
    (best : ItemType T)
    (hmean_pos : 0 < mean)
    (hbest_strict : ∀ t, t ≠ best → likelihood t < likelihood best)
    (a : CountAllocation T)
    (hopt :
      (ConsumptionModel.linearized likelihood (fun _ => mean)).IsOptimalAtTotal
        N a) :
    ∀ t, t ≠ best → a.count t = 0 :=
    PRPKG24AccuracyDiversity.ConsumptionModel.paper_theorem1_all_consumed_unique_common_mean_only_argmax
      likelihood mean N best hmean_pos hbest_strict a hopt

/--
Source Lemma D.1 endpoint / Definition 2 bridge: asymptotic homogeneity of all
finite optima implies convergence of any selected optimal allocation sequence.
-/
theorem lemmaD1_optimizer_sequence_limit_of_asymptotic_homogeneity
    {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h : ConsumptionModel.AsymptoticHomogeneity Mseq G) :
    seq.toAllocationSequence.ConvergesToProfile G :=
    PRPKG24AccuracyDiversity.paper_lemmaD1_optimizer_sequence_limit_of_asymptotic_homogeneity
      seq h

/--
Source Lemma D.1 optimizer-limit bridge from the appendix proof's limiting
objective comparison.
-/
theorem lemmaD1_optimizer_sequence_limit_of_unique_limit_objective_gap
    {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (finiteObj : ℕ → CountAllocation T → ℝ)
    (limitObj : (ItemType T → ℝ) → ℝ)
    (candidate : ℕ → CountAllocation T)
    (hopt_le :
      ∀ᶠ N in Filter.atTop, ∀ b : CountAllocation T,
        ConsumptionModel.FeasibleAtTotal N b →
          finiteObj N b ≤ finiteObj N (seq.allocation N))
    (hcand_feas :
      ∀ᶠ N in Filter.atTop, ConsumptionModel.FeasibleAtTotal N (candidate N))
    (hcand_lower :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop,
          limitObj G.targetShare - δ ≤ finiteObj N (candidate N))
    (hupper :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop, ∀ a : CountAllocation T,
          ConsumptionModel.FeasibleAtTotal N a →
            finiteObj N a ≤
              limitObj (fun t => CountAllocation.representation a t) + δ)
    (hgap :
      ∀ ε : ℝ, 0 < ε →
        ∃ η : ℝ, 0 < η ∧
          ∀ N (a : CountAllocation T),
            0 < N →
            ConsumptionModel.FeasibleAtTotal N a →
              ¬ G.Approx a ε →
                limitObj (fun t => CountAllocation.representation a t) ≤
                  limitObj G.targetShare - η) :
    seq.toAllocationSequence.ConvergesToProfile G :=
    PRPKG24AccuracyDiversity.paper_lemmaD1_optimizer_sequence_limit_of_unique_limit_objective_gap
      seq finiteObj limitObj candidate hopt_le hcand_feas hcand_lower hupper
      hgap

/--
Source Lemma D.1 optimizer-limit bridge from a strict unique maximizer of the
limiting relaxed objective on the finite simplex.
-/
theorem lemmaD1_optimizer_sequence_limit_of_unique_simplex_limit_objective
    {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (finiteObj : ℕ → CountAllocation T → ℝ)
    (limitObj : (ItemType T → ℝ) → ℝ)
    (candidate : ℕ → CountAllocation T)
    (htarget_simplex : G.targetShare ∈ stdSimplex ℝ (ItemType T))
    (hlimit_cont : ContinuousOn limitObj (stdSimplex ℝ (ItemType T)))
    (hlimit_strict :
      ∀ x : ItemType T → ℝ, x ∈ stdSimplex ℝ (ItemType T) →
        x ≠ G.targetShare → limitObj x < limitObj G.targetShare)
    (hopt_le :
      ∀ᶠ N in Filter.atTop, ∀ b : CountAllocation T,
        ConsumptionModel.FeasibleAtTotal N b →
          finiteObj N b ≤ finiteObj N (seq.allocation N))
    (hcand_feas :
      ∀ᶠ N in Filter.atTop, ConsumptionModel.FeasibleAtTotal N (candidate N))
    (hcand_lower :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop,
          limitObj G.targetShare - δ ≤ finiteObj N (candidate N))
    (hupper :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in Filter.atTop, ∀ a : CountAllocation T,
          ConsumptionModel.FeasibleAtTotal N a →
            finiteObj N a ≤
              limitObj (fun t => CountAllocation.representation a t) + δ) :
    seq.toAllocationSequence.ConvergesToProfile G :=
    PRPKG24AccuracyDiversity.paper_lemmaD1_optimizer_sequence_limit_of_unique_simplex_limit_objective
      seq finiteObj limitObj candidate htarget_simplex hlimit_cont
      hlimit_strict hopt_le hcand_feas hcand_lower hupper

/--
Source Theorem 1(i), finite-discrete i.i.d. conditional item values, exposed at
the reusable top-`k` certificate seam.
-/
theorem theorem1_i_finite_discrete_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_certificate
      O likelihood k seq hcert

/--
Source Theorem 1(i), direct equation (6) form: the finite-discrete certificate
implies convergence to equal representation.
-/
theorem theorem1_i_finite_discrete_sequence_uniform_formula_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k (uniformProfile T)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_certificate
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), finite-discrete proof seam below the abstract top-`k`
certificate: a sublinear unweighted FOC gap certificate implies
`0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k seq hcert

/--
Source Theorem 1(i), top-`k` marginal proof seam: a source-shaped sublinear
backward/forward marginal certificate implies `0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_topk_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_topk_sublinear_foc_certificate
      O likelihood k seq hcert

/--
Source Theorem 1(i), eventual count-floor bridge: a large-source/small-
destination top-`k` marginal dominance certificate forces all large finite
optima above the fixed floor in every type.
-/
theorem
    theorem1_i_finite_discrete_eventual_count_floor_of_topk_marginal_dominance
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (hcert : TopKUniformCountFloorCertificate O likelihood k) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, hcert.floor < a.count t :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_eventual_count_floor_of_topk_marginal_dominance
      O likelihood k hcert

/--
Source Theorem 1(i), eventual top-`k` marginal seam: eventual count-floor and
large-gap marginal estimates imply `0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate
      O likelihood k seq hcert

/--
Source Theorem 1(i), combined distribution-estimate seam: count-floor
marginal dominance plus a zero-convergent large-gap estimate imply
`0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_count_floor_and_large_gap
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hfloor : TopKUniformCountFloorCertificate O likelihood k)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (large_gap_backward_lt_forward_after_floor :
      ∀ᶠ N in Filter.atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hfloor.floor < qsrc →
          hfloor.floor < qdst →
          base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
          likelihood src *
              (O.expectedTopSum k src qsrc -
                O.expectedTopSum k src (qsrc - 1)) <
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_count_floor_and_large_gap
      O likelihood k seq hfloor base_error base_error_nonneg
      base_error_tends_to_zero large_gap_backward_lt_forward_after_floor

/--
Source Theorem 1(i), geometric marginal-bound seam: geometric lower tail,
polynomial-times-geometric upper tail, count-floor dominance, and a sublinear
integer gap imply `0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_marginal_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_marginal_bounds
      O likelihood k seq hcert

/--
Source Theorem 1(i), geometric tail seam: a positive finite-floor forward
lower bound plus polynomial-geometric marginal tails imply `0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_tail_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_tail_certificate
      O likelihood k seq hcert

/--
Source Theorem 1(i), deterministic top-`k` upper marginal step: adding one
bounded draw improves the top-`k` sum only on the event that the old sample has
fewer than `k` top-support draws, and the improvement is then at most
`k * xTop`.
-/
theorem theorem1_i_finite_discrete_sample_topK_upper_marginal_failure_indicator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    [Decidable (hasKTopValues k xTop v)]
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop) :
    topKSumOn k (extendSample v newValue) - topKSumOn k v ≤
      (k : ℝ) * xTop *
        (if hasKTopValues k xTop v then (0 : ℝ) else 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sample_topK_upper_marginal_failure_indicator
      k v hxTop_nonneg h_le hnew_le

/--
Source Theorem 1(i), finite-expectation lift of the upper marginal step: the
expected top-`k` marginal is bounded by `k * xTop` times the failure
probability for the old sample.
-/
theorem theorem1_i_finite_discrete_expected_topK_upper_marginal_failure_prob
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    AppliedModelingLib.pmfPairExp sampleLaw itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i)))
      ≤
        (k : ℝ) * xTop *
          AppliedModelingLib.pmfProb sampleLaw
            (fun sample =>
              ¬ hasKTopValues k xTop (fun i => value (sample i))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_expected_topK_upper_marginal_failure_prob
      sampleLaw itemLaw k value hxTop_nonneg hvalue_le

/--
Source Theorem 1(i), event/cardinality bridge for the upper marginal: the event
that a sample already contains `k` top-support draws is exactly the event that
the top-value count is at least `k`.
-/
theorem theorem1_i_finite_discrete_hasKTopValues_iff_topValueCount
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) :
    hasKTopValues k xTop v ↔ k ≤ topValueCount xTop v :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_hasKTopValues_iff_topValueCount
      k xTop v

/--
Source Theorem 1(i), deterministic promoting-event lower marginal step: if the
old sample has exactly `k-1` top-support values and the new draw is
top-support, then the top-`k` sum increases by at least `xTop - xSecond`.
-/
theorem theorem1_i_finite_discrete_sample_topK_lower_marginal_promoting_event
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond)
    (hnew_eq : newValue = xTop) :
    xTop - xSecond ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sample_topK_lower_marginal_promoting_event
      k v hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top topSet
      htop_card htop_value hnontop_le hnew_eq

/--
Source Theorem 1(i), finite-expectation lift of the promoting-event lower
marginal step.
-/
theorem theorem1_i_finite_discrete_expected_topK_lower_marginal_promoting_event
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        AppliedModelingLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            if hasPredTopValuesWithSecondBound k xTop xSecond
                (fun i => value (sample i)) ∧
              value newItem = xTop then (1 : ℝ) else 0)
      ≤
        AppliedModelingLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem)) -
              topKSumOn k (fun i => value (sample i))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_expected_topK_lower_marginal_promoting_event
      sampleLaw itemLaw k value hk_pos hxTop_nonneg hxSecond_nonneg
      hsecond_le_top

/--
Source Theorem 1(i), event/cardinality bridge for the lower marginal: under the
finite-discrete two-level support split, the promoting event is exactly that the
old sample has `k-1` top-support draws.
-/
theorem theorem1_i_finite_discrete_promoting_event_iff_topValueCount_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {xTop xSecond : ℝ} (v : ι → ℝ)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ i, v i = xTop ∨ v i ≤ xSecond) :
    hasPredTopValuesWithSecondBound k xTop xSecond v ↔
      topValueCount xTop v = k - 1 :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_promoting_event_iff_topValueCount_eq
      k v hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), finite i.i.d. bridge: a coordinate-dependent event under
the independent product PMF factors into one-coordinate probabilities.
-/
theorem theorem1_i_finite_discrete_product_forall_factorization
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (event : ι → Ω → Prop)
    [∀ i, DecidablePred (event i)] :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω => ∀ i : ι, event i (sample i)) =
      ∏ i : ι, AppliedModelingLib.pmfProb itemLaw (event i) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_product_forall_factorization
      itemLaw event

/--
Source Theorem 1(i), exact finite i.i.d. binomial lower-tail bridge: the
probability that the old sample has fewer than `k` top-support draws is exactly
`finiteDiscreteTopMassFailureTail`.
-/
theorem theorem1_i_finite_discrete_product_failure_tail_exact
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) (xTop : ℝ)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω =>
          ¬ hasKTopValues k xTop (fun i => value (sample i))) =
      finiteDiscreteTopMassFailureTail k (Fintype.card ι)
        (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
        (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_product_failure_tail_exact
      itemLaw k value xTop

/--
Source Theorem 1(i), exact finite i.i.d. promoting-event bridge: the event that
the old sample has exactly `k-1` top-support draws and the new draw is
top-support has mass `finiteDiscreteTopMassPromotingEvent`.
-/
theorem theorem1_i_finite_discrete_product_promoting_event_exact
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          if hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop then (1 : ℝ) else 0) =
      finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
        (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
        (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_product_promoting_event_exact
      itemLaw k value hk_pos hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), iid scalar marginal identity on an arbitrary finite old
sample index type: the expected top-`k` value for `Option ι` minus that for `ι`
is exactly the pair expectation of adding one independent draw.
-/
theorem theorem1_i_finite_discrete_iid_option_marginal_identity
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value =
      AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_iid_option_marginal_identity
      itemLaw k value

/--
Source Theorem 1(i), iid finite-discrete upper scalar marginal bound on an
arbitrary finite old sample index type.
-/
theorem theorem1_i_finite_discrete_iid_option_upper_marginal_failure_tail
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value ≤
      (k : ℝ) * xTop *
        finiteDiscreteTopMassFailureTail k (Fintype.card ι)
          (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_iid_option_upper_marginal_failure_tail
      itemLaw k value hxTop_nonneg hvalue_le

/--
Source Theorem 1(i), iid finite-discrete lower scalar marginal bound on an
arbitrary finite old sample index type.
-/
theorem theorem1_i_finite_discrete_iid_option_lower_marginal_promoting_event
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
          (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
      ≤
        iidTopKExpectedOn (Option ι) Ω itemLaw k value -
          iidTopKExpectedOn ι Ω itemLaw k value :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_iid_option_lower_marginal_promoting_event
      itemLaw k value hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top
      hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), scalar `h(a)` upper marginal bound for the finite-discrete
i.i.d. top-`k` expectation.
-/
theorem theorem1_i_finite_discrete_scalar_upper_marginal_failure_tail
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : Fin a → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
        finiteDiscreteIidTopKExpected Ω itemLaw k value a ≤
      (k : ℝ) * xTop *
        finiteDiscreteTopMassFailureTail k a
          (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_scalar_upper_marginal_failure_tail
      itemLaw k a value hxTop_nonneg hvalue_le

/--
Source Theorem 1(i), scalar `h(a)` lower marginal bound for the finite-discrete
i.i.d. top-`k` expectation.
-/
theorem theorem1_i_finite_discrete_scalar_lower_marginal_promoting_event
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : Fin a → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        finiteDiscreteTopMassPromotingEvent k a
          (AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
      ≤
        finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
          finiteDiscreteIidTopKExpected Ω itemLaw k value a :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_scalar_lower_marginal_promoting_event
      itemLaw k a value hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top
      hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), small-count scalar lower marginal: before the old sample
has `k` coordinates, adding a top-support item improves the finite-discrete
i.i.d. top-`k` expectation by at least `xTop` times the top-support
probability.
-/
theorem theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (ha_lt_k : a < k)
    (hxTop_nonneg : 0 ≤ xTop) :
    xTop * AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop) ≤
      finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
        finiteDiscreteIidTopKExpected Ω itemLaw k value a :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k
      itemLaw k a value ha_lt_k hxTop_nonneg

/--
Source Theorem 1(i), scalar finite-discrete binomial-event seam: common
unweighted top-`k` marginal bounds by the failure and promoting events imply
`0`-homogeneity after applying the type likelihood bounds.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_unweighted_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (unweighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          smallForward ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
    (unweighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (unweighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_unweighted_binomial_event_bounds
      O likelihood k seq q rho hk_pos hq_pos hq_le_one hrho_pos
      hrho_lt_one floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      unweighted_forward_lower_to_floor
      unweighted_backward_upper_by_failure_tail
      unweighted_forward_lower_by_promoting_event

/--
Theorem 1(i) common scalar top-`k` model generated by the paper's function
`h(a)`.
-/
noncomputable abbrev theorem1CommonTopKModel {T : ℕ}
    (h : ℕ → ℝ) (likelihood : ItemType T → ℝ) (k : ℕ) :
    ConsumptionModel T := (TopKValueOracle.common T h).toConsumptionModel likelihood k

/--
Source Theorem 1(i), scalar `h(a)` binomial-event seam: the source-style
failure/promoting event bounds for a common `h` imply `0`-homogeneity.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (h : ℕ → ℝ) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1CommonTopKModel h likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤ h (qdst + 1) - h qdst)
    (scalar_backward_upper_by_failure_tail :
      ∀ qsrc,
        floor < qsrc →
          h qsrc - h (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (scalar_forward_lower_by_promoting_event :
      ∀ qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            h (qdst + 1) - h qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds
      h likelihood k seq q rho hk_pos hq_pos hq_le_one hrho_pos
      hrho_lt_one floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      scalar_forward_lower_to_floor
      scalar_backward_upper_by_failure_tail
      scalar_forward_lower_by_promoting_event

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar marginal assembly: the
verified order-statistic upper/lower marginal bounds for the finite-support
top-`k` expectation imply `0`-homogeneity, subject only to the source's
small-count floor and asymptotic gap certificates.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤
            finiteDiscreteIidTopKExpected Ω itemLaw k value (qdst + 1) -
              finiteDiscreteIidTopKExpected Ω itemLaw k value qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_eq forwardGain_eq gap
      gap_error_tends_to_zero gap_dominance_eventually
      scalar_forward_lower_to_floor

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar marginal assembly with the
small-count floor discharged at `floor = k - 1`.  The remaining certificate is
the asymptotic gap schedule.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper backwardLoss
      forwardGain backwardLoss_eq forwardGain_eq gap gap_error_tends_to_zero
      gap_dominance_eventually

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly from the standard
gap-decay condition `(N : ℝ)^k * rho^(gap N) -> 0`; the small-count floor and
constant-heavy dominance inequality are both discharged.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_polynomial_geometric_tends_to_zero :
      Filter.Tendsto
        (fun N : ℕ => (N : ℝ) ^ k * rho ^ (gap N))
        Filter.atTop (nhds 0)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper backwardLoss
      forwardGain backwardLoss_eq forwardGain_eq gap gap_error_tends_to_zero
      gap_polynomial_geometric_tends_to_zero

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly with the concrete
square-root gap schedule `gap N = Nat.sqrt N`.  This discharges the small-count
floor, the gap decay, and the constant-heavy large-gap dominance inequality.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly with the concrete
square-root gap schedule and positive likelihoods. The finite lower/upper
likelihood bounds are derived internally.
-/
theorem
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap_of_positive_likelihood
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap_of_positive_likelihood
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos hlike_pos

/--
Source Theorem 1(i), finite-discrete iid source theorem from the paper's
top-support split assumptions.
-/
theorem theorem1_i_finite_discrete_sequence_homogeneity_of_iid_top_split
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
  PRPKG24AccuracyDiversity.paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_top_split
    itemLaw value likelihood k seq hk_pos hxTop_pos hxSecond_nonneg
    hsecond_le_top hsecond_lt_top hvalue_le hvalue_split htop_mass_pos
    hnontop_mass_pos hlike_pos

/--
Source Theorem 1(i), direct equation (6) form from the sublinear FOC seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the top-`k` marginal seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_topk_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_topk_sublinear_foc_certificate
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the combined
count-floor/large-gap distribution-estimate seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_count_floor_and_large_gap
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hfloor : TopKUniformCountFloorCertificate O likelihood k)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (large_gap_backward_lt_forward_after_floor :
      ∀ᶠ N in Filter.atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hfloor.floor < qsrc →
          hfloor.floor < qdst →
          base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
          likelihood src *
              (O.expectedTopSum k src qsrc -
                O.expectedTopSum k src (qsrc - 1)) <
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_count_floor_and_large_gap
      O likelihood k seq hfloor base_error base_error_nonneg
      base_error_tends_to_zero large_gap_backward_lt_forward_after_floor
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the geometric marginal-bound
seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_geometric_marginal_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_marginal_bounds
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the geometric tail seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_geometric_tail_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_tail_certificate
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the scalar finite-discrete
binomial-event seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_unweighted_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (unweighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          smallForward ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
    (unweighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (unweighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_unweighted_binomial_event_bounds
      O likelihood k seq q rho hk_pos hq_pos hq_le_one hrho_pos
      hrho_lt_one floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      unweighted_forward_lower_to_floor
      unweighted_backward_upper_by_failure_tail
      unweighted_forward_lower_by_promoting_event
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the scalar `h(a)`
binomial-event seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_scalar_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (h : ℕ → ℝ) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1CommonTopKModel h likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤ h (qdst + 1) - h qdst)
    (scalar_backward_upper_by_failure_tail :
      ∀ qsrc,
        floor < qsrc →
          h qsrc - h (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (scalar_forward_lower_by_promoting_event :
      ∀ qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            h (qdst + 1) - h qdst) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds
      h likelihood k seq q rho hk_pos hq_pos hq_le_one hrho_pos
      hrho_lt_one floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      scalar_forward_lower_to_floor
      scalar_backward_upper_by_failure_tail
      scalar_forward_lower_by_promoting_event
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the finite-discrete i.i.d.
scalar marginal assembly.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_scalar_marginal_bounds
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤
            finiteDiscreteIidTopKExpected Ω itemLaw k value (qdst + 1) -
              finiteDiscreteIidTopKExpected Ω itemLaw k value qdst) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_eq forwardGain_eq gap
      gap_error_tends_to_zero gap_dominance_eventually
      scalar_forward_lower_to_floor
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the finite-discrete i.i.d.
scalar assembly with the `k - 1` small-count floor discharged.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_scalar_marginal_bounds_pred_floor
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper backwardLoss
      forwardGain backwardLoss_eq forwardGain_eq gap gap_error_tends_to_zero
      gap_dominance_eventually
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the finite-discrete i.i.d.
scalar assembly with the small-count floor and large-gap dominance reduced to
`(N : ℝ)^k * rho^(gap N) -> 0`.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      AppliedModelingLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_polynomial_geometric_tends_to_zero :
      Filter.Tendsto
        (fun N : ℕ => (N : ℝ) ^ k * rho ^ (gap N))
        Filter.atTop (nhds 0)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper backwardLoss
      forwardGain backwardLoss_eq forwardGain_eq gap gap_error_tends_to_zero
      gap_polynomial_geometric_tends_to_zero
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the finite-discrete i.i.d.
scalar assembly with the concrete square-root gap schedule.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_scalar_marginal_bounds_sqrt_gap
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the finite-discrete i.i.d.
scalar assembly with the concrete square-root gap schedule and positive
likelihoods.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_scalar_marginal_bounds_sqrt_gap_of_positive_likelihood
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (q rho : ℝ)
    (hq_def : q = AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap_of_positive_likelihood
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos hlike_pos
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the paper's finite-discrete
top-support split assumptions.
-/
theorem theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_top_split
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          theorem1CommonTopKModel
            (finiteDiscreteIidTopKExpected Ω itemLaw k value) likelihood k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_iid_top_split
      itemLaw value likelihood k seq hk_pos hxTop_pos hxSecond_nonneg
      hsecond_le_top hsecond_lt_top hvalue_le hvalue_split htop_mass_pos
      hnontop_mass_pos hlike_pos
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(i), direct equation (6) form from the eventual top-`k`
marginal seam.
-/
theorem
    theorem1_i_finite_discrete_sequence_uniform_formula_of_eventual_topk_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate
      O likelihood k seq hcert
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Two-point finite-discrete top-one model used as a fully formalized instance of
source Theorem 1(i).
-/
noncomputable abbrev theorem1TwoPointTopOneModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (q : ℝ) : ConsumptionModel T := theorem1TwoPointBernoulliTopOneModel likelihood q

/--
Source Theorem 1(i), fully formalized two-point finite-discrete top-one instance:
for common Bernoulli conditional item values, every selected finite optimum
converges to equal representation.
-/
theorem theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1TwoPointTopOneModel likelihood q)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) :=
    PRPKG24AccuracyDiversity.paper_theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity
      likelihood q hq_pos hq_lt_one hlike_pos seq

/--
Source Theorem 1(i), direct equation (6) form for the verified two-point
finite-discrete top-one instance.
-/
theorem theorem1_i_two_point_bernoulli_top_one_uniform_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1TwoPointTopOneModel likelihood q)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity
      likelihood q hq_pos hq_lt_one hlike_pos seq
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(ii)-(iv), order-statistic scaled marginal limit seam:
eventual uniform upper/lower sandwich for every type's top-`k` marginal.
-/
theorem theorem1_order_statistic_scaled_marginal_sandwich
    {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ)
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ q in Filter.atTop,
      ∀ t : ItemType T,
        (1 - epsilon) * (scale q * weight t) ≤
            O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ∧
          O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ≤
            (1 + epsilon) * (scale q * weight t) :=
    PRPKG24AccuracyDiversity.paper_theorem1_order_statistic_scaled_marginal_sandwich
      O k scale weight C hepsilon

/--
Source Theorem 1(ii)-(iv), order-statistic same-count comparison seam: a strict
scaled-weight gap eventually orders same-count top-`k` marginals.
-/
theorem theorem1_order_statistic_same_count_marginal_lt_of_weight_gap
    {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ)
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {src dst : ItemType T}
    (hgap : (1 + epsilon) * weight src < (1 - epsilon) * weight dst) :
    ∀ᶠ q in Filter.atTop,
      O.expectedTopSum k src (q + 1) - O.expectedTopSum k src q <
        O.expectedTopSum k dst (q + 1) - O.expectedTopSum k dst q :=
    PRPKG24AccuracyDiversity.paper_theorem1_order_statistic_same_count_marginal_lt_of_weight_gap
      O k scale weight C hepsilon hgap

/--
Source Theorem 1(ii), bounded upper-tail i.i.d. conditional item values,
exposed at the reusable top-`k` certificate seam.
-/
theorem theorem1_ii_bounded_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_sequence_homogeneity_of_certificate
      O likelihood k beta hbeta_pos seq hcert

/--
Source Theorem 1(ii), bounded branch from the Lemma D.1-style sublinear FOC
certificate.
-/
theorem theorem1_ii_bounded_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k beta hbeta_pos seq hcert

/--
Source Theorem 1(ii), bounded branch from the floor-aware Lemma D.1-style FOC
certificate.
-/
theorem theorem1_ii_bounded_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k beta hbeta_pos seq hcert

/--
Source Theorem 1(ii), direct equation (6) form.
-/
theorem theorem1_ii_bounded_sequence_formula_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1)))) := by
  have hconv :=
    theorem1_ii_bounded_sequence_homogeneity_of_certificate
      O likelihood k beta hbeta_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (beta / (beta + 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(ii), direct equation (6) form from the sublinear FOC seam.
-/
theorem theorem1_ii_bounded_sequence_formula_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1)))) := by
  have hconv :=
    theorem1_ii_bounded_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k beta hbeta_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (beta / (beta + 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(ii), direct equation (6) form from the floor-aware sublinear
FOC seam.
-/
theorem theorem1_ii_bounded_sequence_formula_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
        (gammaLikelihoodProfile likelihood (beta / (beta + 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1)))) := by
  have hconv :=
    theorem1_ii_bounded_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k beta hbeta_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (beta / (beta + 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Lemma D.2 to Theorem 1(ii): finite-sum assembly of the bounded
order-statistic rank terms. The hard analytic input remains the certificate
that each fixed `(i,j)` integral is asymptotic to a positive constant times
`a^(-1/β)`.
-/
theorem lemmaD2_bounded_top_k_loss_asymptotic_of_rank_terms
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k term)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_top_k_loss_asymptotic_of_rank_terms
    term C

/--
Source Lemma D.2 to Theorem 1(ii), nested display form. This exposes the
paper's finite `i`/`j` assembly directly rather than through the internal
`Sigma` index.
-/
theorem lemmaD2_bounded_nested_top_k_loss_asymptotic_of_rank_terms
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      (fun a =>
        (∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_nested_top_k_loss_asymptotic_of_rank_terms
    term C

/--
Source Theorem 1(ii), equations (91)-(96): the reflected bounded-tail
rank-integral certificates imply the paper's top-`k` source loss asymptotic.
-/
theorem theorem1_ii_bounded_reflected_source_loss_asymptotic
    {beta M : ℝ} {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_source_loss_asymptotic
    sourceMean term hsource C

/--
Source Lemma D.2, actual integral-term finite assembly.
-/
theorem lemmaD2_bounded_integral_top_k_loss_asymptotic
    {beta : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_top_k_loss_asymptotic
    G C

/--
Source Lemma D.2, epsilon-sandwich consequence of the actual integral-term
asymptotic certificate.
-/
theorem lemmaD2_bounded_integral_term_sandwich
    {beta : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ a in Filter.atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - epsilon) * (C.coeff p * boundedTailScale beta a) ≤
            boundedLemmaD2IndexedIntegralTerm G p a ∧
          boundedLemmaD2IndexedIntegralTerm G p a ≤
            (1 + epsilon) * (C.coeff p * boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_sandwich
    C hepsilon

/--
Source Lemma D.2, exponential kernel limit after rescaling.
-/
theorem lemmaD2_bounded_one_sub_div_pow_tendsto_exp (z : ℝ) :
    Filter.Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ a)
      Filter.atTop (nhds (Real.exp (-z))) := PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_one_sub_div_pow_tendsto_exp z

/--
Source Lemma D.2, fixed-rank exponential kernel limit after rescaling.
-/
theorem lemmaD2_bounded_one_sub_div_pow_sub_tendsto_exp
    (z : ℝ) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ (a - j))
      Filter.atTop (nhds (Real.exp (-z))) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_one_sub_div_pow_sub_tendsto_exp
    z j

/--
Source Lemma D.2, CDF rescaling step after `x = y * a^(-1/β)`.
-/
theorem lemmaD2_bounded_rescaled_cdf_power_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {epsilon y : ℝ} (hepsilon : 0 < epsilon) (hy_pos : 0 < y) :
    ∀ᶠ a in Filter.atTop,
      (1 - epsilon) * (c / beta) *
          (y * boundedTailScale beta a) ^ beta ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + epsilon) * (c / beta) *
            (y * boundedTailScale beta a) ^ beta :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_power_sandwich
    C hepsilon hy_pos

/--
Source Lemma D.2, simplified CDF rescaling step with the power term rewritten
as `y^β * a^-1`.
-/
theorem lemmaD2_bounded_rescaled_cdf_power_sandwich_inv_nat
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {epsilon y : ℝ} (hepsilon : 0 < epsilon) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in Filter.atTop,
      (1 - epsilon) * (c / beta) *
          (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + epsilon) * (c / beta) *
            (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_power_sandwich_inv_nat
    C hepsilon hy_pos

/--
Source Lemma D.2, rescaled CDF sandwich after multiplying by `a`.
-/
theorem lemmaD2_bounded_rescaled_cdf_nat_mul_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {epsilon y : ℝ} (hepsilon : 0 < epsilon) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in Filter.atTop,
      (1 - epsilon) * ((c / beta) * y ^ beta) ≤
          (a : ℝ) * G (y * boundedTailScale beta a) ∧
        (a : ℝ) * G (y * boundedTailScale beta a) ≤
          (1 + epsilon) * ((c / beta) * y ^ beta) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_nat_mul_sandwich
    C hepsilon hy_pos

/--
Source Lemma D.2, pointwise rescaled CDF limit.
-/
theorem lemmaD2_bounded_rescaled_cdf_nat_mul_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Filter.Tendsto
      (fun a : ℕ => (a : ℝ) * G (y * boundedTailScale beta a))
      Filter.atTop (nhds ((c / beta) * y ^ beta)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_nat_mul_tendsto
    C hy_pos

/--
Source Lemma D.2, the rescaled split threshold
`delta / a^(-1/beta)` tends to infinity.
-/
theorem lemmaD2_bounded_tail_scale_delta_div_tendsto_atTop
    {beta delta : ℝ} (hbeta_pos : 0 < beta) (hdelta_pos : 0 < delta) :
    Filter.Tendsto
      (fun a : ℕ => delta / boundedTailScale beta a)
      Filter.atTop Filter.atTop :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_tail_scale_delta_div_tendsto_atTop
    hbeta_pos hdelta_pos

/--
Source Lemma D.2, local CDF power bounds after the substitution
`x = y*a^(-1/beta)`.
-/
theorem lemmaD2_bounded_rescaled_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta A B delta : ℝ}
    (hbeta_pos : 0 < beta)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in Filter.atTop,
      ∀ {y : ℝ}, 0 < y →
        y < delta / boundedTailScale beta a →
          A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
              G (y * boundedTailScale beta a) ∧
            G (y * boundedTailScale beta a) ≤
              B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_local_cdf_power_bounds
    hbeta_pos hG_lower hG_upper

/--
Source Lemma D.2, the asymptotic CDF sandwich supplies concrete local power
bounds on a right-neighborhood of zero.
-/
theorem lemmaD2_bounded_exists_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c) :
    ∃ delta A B : ℝ,
      0 < delta ∧ 0 < A ∧ 0 ≤ B ∧
        (∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x) ∧
        (∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_exists_local_cdf_power_bounds
    C

/--
Source Lemma D.2, scalar envelope bound for the fixed-rank binomial kernel
under rescaled local CDF power bounds.
-/
theorem lemmaD2_bounded_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    {beta A B y g : ℝ} {j a : ℕ}
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hy_pos : 0 < y) (ha_pos : 0 < a)
    (hlarge : 2 * j ≤ a)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (hg_lower : A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤ g)
    (hg_upper : g ≤ B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) :
    ‖(Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)‖ ≤
      B ^ j * y ^ (beta * (j : ℝ)) *
        Real.exp (-(A / 2) * y ^ beta) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    hA_pos hB_nonneg hy_pos ha_pos hlarge
    hg_nonneg hg_le_one hg_lower hg_upper

/--
Source Lemma D.2, eventual gamma-shaped envelope for the rescaled kernel on
the growing near-zero window.
-/
theorem lemmaD2_bounded_rescaled_kernel_eventually_norm_le_power_exp_on_growing
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in Filter.atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        y < delta / boundedTailScale beta a →
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤
            B ^ j * y ^ (beta * (j : ℝ)) *
              Real.exp (-(A / 2) * y ^ beta) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_kernel_eventually_norm_le_power_exp_on_growing
    j hbeta_pos hA_pos hB_nonneg hG_nonneg hG_le_one hG_lower hG_upper

/--
Source Lemma D.2, rescaled exponential kernel limit with exponent `a`.
-/
theorem lemmaD2_bounded_rescaled_cdf_one_sub_pow_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Filter.Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ a)
      Filter.atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_one_sub_pow_tendsto_exp
    C hy_pos

/--
Source Lemma D.2, fixed-rank rescaled exponential kernel limit with exponent
`a - j`.
-/
theorem lemmaD2_bounded_rescaled_cdf_one_sub_pow_sub_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      Filter.atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_one_sub_pow_sub_tendsto_exp
    C hy_pos j

/--
Source Lemma D.2, pointwise binomial-kernel limit after the bounded-tail
substitution.
-/
theorem lemmaD2_bounded_rescaled_cdf_binomial_kernel_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (Nat.choose a j : ℝ) *
          (G (y * boundedTailScale beta a)) ^ j *
          (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      Filter.atTop
      (nhds
        (Real.exp (-((c / beta) * y ^ beta)) *
          (((c / beta) * y ^ beta) ^ j) / j.factorial)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_cdf_binomial_kernel_tendsto
    C hy_pos j

/--
Source Lemma D.2, pointwise convergence of the rescaled finite-`a` kernel to
the limiting gamma-kernel integrand.
-/
theorem lemmaD2_bounded_rescaled_kernel_tendsto_limit
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ => boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitKernel beta c j y)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_kernel_tendsto_limit
    C hy_pos j

/--
Source Lemma D.2, measurability of the rescaled finite-`a` kernel.
-/
theorem lemmaD2_bounded_rescaled_kernel_aestronglyMeasurable
    {G : ℝ → ℝ} (hG : Measurable G) (beta : ℝ) (j a : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_kernel_aestronglyMeasurable
    hG beta j a

/--
Source Lemma D.2, integrability of the gamma-shaped envelope
`x^q * exp(-b*x^p)` on `(0,∞)`.
-/
theorem lemmaD2_bounded_gamma_envelope_integrableOn
    {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ q * Real.exp (-b * x ^ p))
      (Set.Ioi (0 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_gamma_envelope_integrableOn
    hp hq hb

/-- Source Lemma D.2, measurability of the finite-`a` source integrand. -/
theorem lemmaD2_bounded_integral_kernel_measurable
    {G : ℝ → ℝ} (hG : Measurable G) (j a : ℕ) :
    Measurable (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_kernel_measurable
    hG j a

/--
Source Lemma D.2, CDF-range bound for the finite-`a` source integrand.
-/
theorem lemmaD2_bounded_integral_kernel_norm_le_choose_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    ‖boundedLemmaD2IntegralKernel G j a x‖ ≤ (Nat.choose a j : ℝ) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_kernel_norm_le_choose_of_cdf_range
    j a hG_nonneg hG_le_one

/--
Source Lemma D.2, bounded-support CDF conditions imply source-kernel
integrability once `a > j`.
-/
theorem lemmaD2_bounded_integral_kernel_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    {j a : ℕ} (hja : j < a) :
    MeasureTheory.IntegrableOn
      (boundedLemmaD2IntegralKernel G j a)
      (Set.Ioi (0 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_kernel_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja

/--
Source Lemma D.2, eventual source-kernel integrability from bounded-support
CDF conditions.
-/
theorem lemmaD2_bounded_integral_kernel_eventually_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (j : ℕ) :
    ∀ᶠ a in Filter.atTop,
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_kernel_eventually_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j

/--
Source Lemma D.2, eventual source-kernel integrability for every finite-rank
kernel in a fixed top-`k` source sum.
-/
theorem lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support
    {G : ℝ → ℝ} {k : ℕ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    ∀ᶠ a in Filter.atTop,
      ∀ i : Fin k, ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma D.2, finite-support geometric bound for the above-`delta` tail
integral.
-/
theorem lemmaD2_bounded_integral_term_above_le_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {delta M p : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    {j a : ℕ} (hja : j < a) :
    boundedLemmaD2IntegralTermAbove G j a delta ≤
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
        (M - delta) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_above_le_geometric_support_bound
    hG_measurable hdelta_nonneg hdeltaM hp_nonneg hp_le_one
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail hja

/--
Source Lemma D.2, the scalar binomial/geometric support bound is negligible
relative to the bounded-branch scale.
-/
theorem lemmaD2_bounded_tail_scale_choose_geometric_tail_ratio_tendsto_zero
    {beta p C : ℝ} (hbeta_pos : 0 < beta)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hC_nonneg : 0 ≤ C) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale beta a)
      Filter.atTop (nhds 0) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_tail_scale_choose_geometric_tail_ratio_tendsto_zero
    hbeta_pos hp_pos hp_lt_one hC_nonneg j

/--
Source Lemma D.2, finite-support geometric domination makes the above-`delta`
tail integral negligible relative to `a^(-1/beta)`.
-/
theorem lemmaD2_bounded_integral_term_above_negligible_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {beta delta M p : ℝ} (hbeta_pos : 0 < beta)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
      Filter.atTop (nhds 0) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_above_negligible_of_geometric_support_bound
    hG_measurable hbeta_pos hdelta_nonneg hdeltaM hp_pos hp_lt_one
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j

/--
Source Lemma D.2, change of variables `x = y*a^(-1/beta)` for the exact source
integral term.
-/
theorem lemmaD2_bounded_integral_term_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTerm G j a =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_changeOfVariables
    G beta j a hscale_pos

/--
Source Lemma D.2, near-zero change of variables `x = y*a^(-1/beta)` for the
below-`delta` source integral term.
-/
theorem lemmaD2_bounded_integral_term_below_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermBelow G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_changeOfVariables
    G beta j a hdelta_nonneg hscale_pos

/--
Source Lemma D.2, above-`delta` change of variables `x = y*a^(-1/beta)` for
the source tail integral term.
-/
theorem lemmaD2_bounded_integral_term_above_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermAbove G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_above_changeOfVariables
    G beta j a hscale_pos

/--
Source Lemma D.2, eventual change of variables for the exact source integral
term.
-/
theorem lemmaD2_bounded_integral_term_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_eventually_changeOfVariables
    G beta j

/--
Source Lemma D.2, eventual near-zero change of variables for the below-`delta`
source integral term.
-/
theorem lemmaD2_bounded_integral_term_below_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTermBelow G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_eventually_changeOfVariables
    G beta j hdelta_nonneg

/--
Source Lemma D.2, eventual above-`delta` change of variables for the source
tail integral term.
-/
theorem lemmaD2_bounded_integral_term_above_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) (delta : ℝ) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTermAbove G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_above_eventually_changeOfVariables
    G beta j delta

/--
Source Lemma D.2, exact split of the rescaled integral at the growing
threshold `delta / a^(-1/beta)`.
-/
theorem lemmaD2_bounded_rescaled_integral_split
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ))) :
    (∫ y in Set.Ioi (0 : ℝ),
        boundedLemmaD2RescaledKernel G beta j a y) =
      (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) +
      (∫ y in Set.Ioi (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_integral_split
    G beta j a hdelta_nonneg hscale_pos h_integrable

/--
Source Lemma D.2, eventual split of the rescaled integral at the growing
threshold `delta / a^(-1/beta)`.
-/
theorem lemmaD2_bounded_rescaled_integral_eventually_split
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in Filter.atTop,
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y) =
        (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) +
        (∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_integral_eventually_split
    G beta j hdelta_nonneg h_integrable

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence directly
from local CDF power bounds near zero.
-/
theorem lemmaD2_bounded_growing_rescaled_integral_tendsto_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_local_cdf_power_bounds
    tail hG_measurable hdelta_pos hA_pos hB_nonneg
    hG_nonneg hG_le_one hG_lower hG_upper j

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence from full
rescaled convergence and rescaled-tail convergence to zero.
-/
theorem lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_tail
    j hdelta_nonneg h_integrable hfull htail

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence from full
rescaled convergence and source-tail negligibility.
-/
theorem lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_source_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_source_tail
    j hdelta_nonneg h_integrable hfull htail_source

/--
Source Lemma D.2, below-`delta` asymptotic from convergence of the growing
rescaled near-zero integral.
-/
theorem lemmaD2_bounded_integral_term_below_asymptotic_of_growing_rescaled_integral
    {G : ℝ → ℝ} {beta c : ℝ} (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hgrowing :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_asymptotic_of_growing_rescaled_integral
    hbeta_pos hc_pos j hdelta_nonneg hgrowing

/--
Source Lemma D.2, below-`delta` source asymptotic directly from local CDF
power bounds near zero.
-/
theorem lemmaD2_bounded_integral_term_below_asymptotic_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_asymptotic_of_local_cdf_power_bounds
    tail hG_measurable hdelta_pos hA_pos hB_nonneg
    hG_nonneg hG_le_one hG_lower hG_upper j

/--
Source Lemma D.2, exact near-zero/tail split of the source integral term at
`delta`.
-/
theorem lemmaD2_bounded_integral_term_split
    (G : ℝ → ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTerm G j a =
      boundedLemmaD2IntegralTermBelow G j a delta +
        boundedLemmaD2IntegralTermAbove G j a delta :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_split
    G j a hdelta_nonneg h_integrable

/--
Source Lemma D.2, eventual near-zero/tail split from eventual source-kernel
integrability.
-/
theorem lemmaD2_bounded_integral_term_eventually_split
    (G : ℝ → ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_eventually_split
    G j hdelta_nonneg h_integrable

/--
Source Lemma D.2, gamma-integral value of the fixed-`j` limiting coefficient.
-/
theorem lemmaD2_bounded_limit_coeff_eq_gamma
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2LimitCoeff beta c j =
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        ((c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) *
          (1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_limit_coeff_eq_gamma
    hbeta_pos hc_pos j

/--
Source Lemma D.2, positivity of the fixed-`j` limiting coefficient.
-/
theorem lemmaD2_bounded_limit_coeff_pos
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    0 < boundedLemmaD2LimitCoeff beta c j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_limit_coeff_pos
    hbeta_pos hc_pos j

/--
Source Theorem 1(ii), equations (91)-(96) with the actual Lemma D.2 integral
term.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic
    {beta M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic
    G sourceMean hsource C

/--
Source Lemma D.2, actual integral finite assembly with the exact gamma
limiting coefficients.
-/
theorem lemmaD2_bounded_integral_top_k_loss_asymptotic_of_limit_coeff
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_limit_coeff
    G C

/--
Source Theorem 1(ii), reflected bounded-source loss with exact gamma limiting
coefficients.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_limit_coeff
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_limit_coeff
    G sourceMean hsource C

/--
Source Lemma D.2, per-rank dominated-convergence certificate constructor from
measurability and an integrable envelope.
-/
noncomputable def lemmaD2_bounded_dominated_kernel_certificate_of_measurable_bound
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG : Measurable G)
    (bound : ℝ → ℝ)
    (bound_integrable :
      MeasureTheory.Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤ bound y) :
    BoundedLemmaD2DominatedKernelCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_dominated_kernel_certificate_of_measurable_bound
    tail hG bound bound_integrable kernel_bound

/--
Source Lemma D.2, finite-index dominated-convergence certificate constructor
from measurability and integrable envelopes.
-/
noncomputable def lemmaD2_bounded_dominated_integral_certificate_of_measurable_bound
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hG : Measurable G)
    (bound : BoundedLemmaD2Index k → ℝ → ℝ)
    (bound_integrable :
      ∀ p : BoundedLemmaD2Index k,
        MeasureTheory.Integrable (bound p)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ p : BoundedLemmaD2Index k,
        ∀ᶠ a in Filter.atTop,
          ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            ‖boundedLemmaD2RescaledKernel G beta p.2.val a y‖ ≤ bound p y) :
    BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_dominated_integral_certificate_of_measurable_bound
    tail k_pos hG bound bound_integrable kernel_bound

/--
Source Lemma D.2, dominated convergence for the rescaled finite-`a` kernels.
-/
theorem lemmaD2_bounded_rescaled_integral_tendsto_of_dominated_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_integral_tendsto_of_dominated_certificate
    C

/--
Source Lemma D.2, the dominated-convergence certificate supplies eventual
integrability of the rescaled kernels on `(0,∞)`.
-/
theorem lemmaD2_bounded_rescaled_kernel_eventually_integrableOn_of_dominated_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    ∀ᶠ a in Filter.atTop,
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_rescaled_kernel_eventually_integrableOn_of_dominated_certificate
    C

/--
Source Lemma D.2, dominated convergence gives the growing near-zero rescaled
integral convergence directly by truncating the rescaled kernels on the
expanding interval.
-/
theorem lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate
    C hdelta_pos

/--
Source Lemma D.2, dominated convergence gives the below-`delta` source
asymptotic through the paper's growing-rescaled-integral route.
-/
theorem lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate
    C hdelta_pos

/--
Source Lemma D.2, dominated convergence plus source-tail negligibility gives
the growing near-zero rescaled integral convergence.
-/
theorem lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate_and_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate_and_source_tail
    C hdelta_nonneg htail_source

/--
Source Lemma D.2, dominated convergence plus source-tail negligibility gives
the below-`delta` source asymptotic via the growing-rescaled-integral route.
-/
theorem lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate_and_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate_and_source_tail
    C hdelta_nonneg htail_source

/--
Source Lemma D.2, per-rank integral asymptotic from an explicit
change-of-variables and dominated-convergence certificate.
-/
theorem lemmaD2_bounded_integral_term_asymptotic_of_dominated_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_asymptotic_of_dominated_certificate
    C

/--
Source Lemma D.2, conversion from the finite-index dominated-convergence
certificate to the exact-gamma integral asymptotic certificate.
-/
noncomputable def lemmaD2_bounded_limit_integral_certificate_of_dominated
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_limit_integral_certificate_of_dominated
    C

/--
Source Lemma D.2, finite-index dominated-convergence certificate plus common
bounded-support geometric tail control gives the paper-style split finite
certificate through the growing near-zero rescaled interval.
-/
noncomputable def lemmaD2_bounded_split_finite_certificate_of_dominated_integral_and_geometric_tail_via_growing
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G)
    {delta M p : ℝ}
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_finite_certificate_of_dominated_integral_and_geometric_tail_via_growing
    C hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, finite-index paper-style split certificate directly from
the bounded-tail limit, local CDF power bounds, and bounded-support geometric
tail control.
-/
noncomputable def lemmaD2_bounded_split_finite_certificate_of_local_cdf_power_bounds_and_geometric_tail
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_finite_certificate_of_local_cdf_power_bounds_and_geometric_tail
    tail k_pos hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
    hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
    hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, finite-index paper-style split certificate from the
bounded-tail CDF asymptotic, monotonicity of the reflected CDF, and bounded
support.
-/
noncomputable def lemmaD2_bounded_split_finite_certificate_of_cdf_power_sandwich_monotone_bounded_support
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_finite_certificate_of_cdf_power_sandwich_monotone_bounded_support
    tail k_pos hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma D.2, actual integral finite assembly from the explicit
dominated-convergence and change-of-variables certificate.
-/
theorem lemmaD2_bounded_integral_top_k_loss_asymptotic_of_dominated_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_dominated_certificate
    G C

/--
Source Theorem 1(ii), equations (91)-(96) from the explicit
dominated-convergence and change-of-variables certificate.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_dominated_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_dominated_certificate
    G sourceMean hsource C

/--
Source Lemma D.2, paper-style split certificate constructor from eventual
source-kernel integrability plus the near-zero and tail estimates.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_asymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_asymptotics
    hbeta_pos hc_pos hdelta_pos h_integrable
    below_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from the full
integral asymptotic plus tail negligibility.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_full_asymptotic_and_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (full_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IntegralTerm G j)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_full_asymptotic_and_tail
    hbeta_pos hc_pos hdelta_pos h_integrable
    full_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from bounded
support plus the near-zero and tail estimates.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_bounded_support_asymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (hG_measurable : Measurable G) (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_bounded_support_asymptotics
    hbeta_pos hc_pos hdelta_pos hG_measurable M
    hG_nonneg hG_le_one hG_eq_one_of_support
    below_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from bounded
support, a positive CDF floor on the above-`delta` tail, and the near-zero
asymptotic.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_bounded_support_near_zero_asymptotic
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_bounded_support_near_zero_asymptotic
    hbeta_pos hc_pos hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail
    below_asymptotic

/--
Source Lemma D.2, per-rank paper-style split certificate directly from the
bounded-tail limit, local CDF power bounds, and bounded-support geometric tail
control.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_local_cdf_power_bounds_and_geometric_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_local_cdf_power_bounds_and_geometric_tail
    tail hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
    hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
    hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, per-rank paper-style split certificate from the bounded-tail
CDF asymptotic, monotonicity of the reflected CDF, and bounded support.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_cdf_power_sandwich_monotone_bounded_support
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_cdf_power_sandwich_monotone_bounded_support
    tail hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma D.2, convert a dominated-convergence full-integral certificate
plus bounded-support geometric tail control into the paper-style split
certificate.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail
    D hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, convert a dominated-convergence full-integral certificate
plus bounded-support geometric tail control into the paper-style split
certificate through the growing near-zero rescaled interval.
-/
noncomputable def lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail_via_growing
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail_via_growing
    D hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, per-rank integral asymptotic from the paper-style
near-zero/tail split certificate.
-/
theorem lemmaD2_bounded_integral_term_asymptotic_of_split_certificate
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j * boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_term_asymptotic_of_split_certificate
    C

/--
Source Lemma D.2, conversion from the paper-style split certificate to the
exact-gamma integral asymptotic certificate.
-/
noncomputable def lemmaD2_bounded_limit_integral_certificate_of_split
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_limit_integral_certificate_of_split
    C

/--
Source Lemma D.2, actual integral finite assembly from the paper-style
near-zero/tail split certificate.
-/
theorem lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate
    G C

/--
Source Theorem 1(ii), equations (91)-(96) from the paper-style
near-zero/tail split certificate.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate
    G sourceMean hsource C

/--
Source Theorem 1(ii), equations (91)-(96) from bounded-tail asymptotics,
local CDF power bounds, and bounded-support geometric tail control.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_local_cdf_power_bounds_and_geometric_tail
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M₀ p A B : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M₀)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_local_cdf_power_bounds_and_geometric_tail
    sourceMean hsource tail k_pos hdelta_pos hdeltaM hA_pos hB_nonneg
    hp_pos hp_lt_one hG_measurable hG_nonneg hG_le_one
    hG_lower hG_upper hG_eq_one_of_support hp_le_G_on_tail

/--
Source Theorem 1(ii), equations (91)-(96) from the bounded-tail CDF
asymptotic, monotonicity of the reflected CDF, and bounded support.
-/
theorem theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sourceMean hsource tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated through the
reflected-CDF integral representation used in equations (91)-(96).
-/
theorem lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sourceMean hsource tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated directly in
Definition 3's bottom-indexed order-statistic mean interface.
-/
theorem lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (mu : ℕ → ℕ → ℝ)
    (hmu :
      ∀ a (i : Fin k),
        mu (a - i.val) a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - orderStatisticTopKSumFromMean mu k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    mu hmu tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated for expected
order-statistic means induced by a family of finite real-sample laws.
-/
theorem lemma1_bounded_support_expected_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hsource :
      ∀ a (i : Fin k),
        expectedOrderStatisticMeanSeq sampleMeasure (a - i.val) a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hsource tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic from the aggregate
measure-level reflected-bottom identity.
-/
theorem lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a))
    (h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => AppliedModelingLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a))
    (h_reflected :
      ∀ᶠ a in Filter.atTop,
        AppliedModelingLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hprob h_order_integrable h_top_integrable h_reflected
    tail k_pos hM₀_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma 1, aggregate reflected-bottom route with bounded-support a.e.
bounds discharging sorted-tuple integrability obligations.
-/
theorem lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_reflected :
      ∀ᶠ a in Filter.atTop,
        AppliedModelingLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hprob h_bounds h_reflected tail k_pos hM₀_pos
    hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support route from the reflected threshold-count
layer integral.  This is the iid/binomial-facing boundary below the aggregate
reflected-bottom wrapper.
-/
theorem lemma1_bounded_support_expected_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_layer_integral :
      ∀ᶠ a in Filter.atTop,
        (∫ x in Set.Ioi (0 : ℝ),
          ∫ sample,
            AppliedModelingLib.Probability.reflectedBottomKRankCountLayer
              M k sample x ∂(sampleMeasure a)) =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hprob h_bounds h_layer_integral tail k_pos hM₀_pos
    hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Definition 3 iid product-measure bridge for the reflected threshold-count
layer.  At a fixed threshold `x`, the inner count-layer expectation is the
finite binomial lower-tail sum with success probability `P[M - X <= x]`.
-/
theorem definition3_iid_reflected_count_layer_inner_integral_binomial
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {a k : ℕ} (x : ℝ) :
    ∫ sample : Fin a → ℝ,
        AppliedModelingLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure) =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        (Nat.choose a j : ℝ) *
          (baseMeasure.real {y : ℝ | M - y ≤ x}) ^ j *
            (1 - baseMeasure.real {y : ℝ | M - y ≤ x}) ^ (a - j) :=
  PRPKG24AccuracyDiversity.paper_definition3_iid_reflected_count_layer_inner_integral_binomial
    baseMeasure x

/--
Definition 3 iid product-measure bridge with the reflected CDF named as `G`,
matching the bounded Lemma D.2 source kernel.
-/
theorem definition3_iid_reflected_count_layer_inner_integral_kernel
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ} (x : ℝ)
    (hGx : baseMeasure.real {y : ℝ | M - y ≤ x} = G x) :
    ∫ sample : Fin a → ℝ,
        AppliedModelingLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure) =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        boundedLemmaD2IntegralKernel G j a x :=
  PRPKG24AccuracyDiversity.paper_definition3_iid_reflected_count_layer_inner_integral_kernel
    baseMeasure x hGx

/--
Definition 3 iid product-measure bridge for the outer threshold integral of
the reflected count layer, assembled into Lemma D.2 source integral terms.
-/
theorem definition3_iid_reflected_count_layer_integral_kernel_of_integrable
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ}
    (hG :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (h_kernel_integrable :
      ∀ i : Fin (min k a), ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
          (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        AppliedModelingLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)) =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        boundedLemmaD2IntegralTerm G j a :=
  PRPKG24AccuracyDiversity.paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable
    baseMeasure hG h_kernel_integrable

/--
Fixed-`k` iid reflected count-layer integral assembly after the eventual
sample-size prefix `k ≤ a`.
-/
theorem definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ}
    (hka : k ≤ a)
    (hG :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (h_kernel_integrable :
      ∀ i : Fin k, ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
          (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        AppliedModelingLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)) =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1),
        boundedLemmaD2IntegralTerm G j.val a :=
  PRPKG24AccuracyDiversity.paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le
    baseMeasure hka hG h_kernel_integrable

/--
Source Lemma 1, bounded-support route specialized to an iid product sample
law through the reflected threshold-count layer.
-/
theorem lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure),
          ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (hG_reflected :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    baseMeasure h_bounds hG_reflected tail k_pos hM₀_pos hG_measurable
    hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support iid route whose support hypothesis is stated
on the one-dimensional source law.
-/
theorem lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hG_reflected :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    baseMeasure h_base_bounds hG_reflected tail k_pos hM₀_pos
    hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support iid route with `G` fixed to the reflected CDF
`x ↦ P[M - X <= x]`.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable :
      Measurable (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}))
    (hG_mono :
      Monotone (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}))
    (hG_nonneg :
      ∀ x : ℝ, 0 ≤ baseMeasure.real {y : ℝ | M - y ≤ x})
    (hG_le_one :
      ∀ x : ℝ, baseMeasure.real {y : ℝ | M - y ≤ x} ≤ 1)
    (hG_eq_one_of_support :
      ∀ x : ℝ, M₀ ≤ x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = 1) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    baseMeasure h_base_bounds tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support iid route where routine reflected-CDF facts
are derived from one-dimensional bounded support.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    baseMeasure h_base_bounds tail k_pos hwidth_pos

/--
Source Lemma 1, bounded-support iid route from the paper's upper-endpoint
tail-mass sandwich `P[X >= M - x]`.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail
    baseMeasure h_base_bounds hbeta_pos hc_pos htail k_pos hwidth_pos

/--
Source Lemma 1, bounded-support iid route from an exact local upper-endpoint
power identity `P[X >= M - x] = (c / beta) * x^beta`.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    baseMeasure h_base_bounds h_upper_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Lemma 1 for the concrete reflected-power bounded source law
`1 - U^(1 / beta)`, where `U` is uniform on `[0,1]`.
-/
theorem lemma1_bounded_reflected_power_source_iid_reflected_cdf_count_layer_top_k_loss_asymptotic
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (k_pos : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a =>
                  boundedReflectedPowerSourceMeasure beta))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta beta q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_reflected_power_source_iid_reflected_cdf_count_layer_top_k_loss_asymptotic
    hbeta_pos k_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from the
reflected-CDF tail route. The adjacent-drop law is derived internally.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    baseMeasure h_base_bounds tail k_pos hwidth_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from the
paper's upper-endpoint tail-mass sandwich. The adjacent-drop law is derived
internally.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail
    baseMeasure h_base_bounds hbeta_pos hc_pos htail k_pos hwidth_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from an exact
local upper-endpoint power identity. The adjacent-drop law is derived
internally.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    baseMeasure h_base_bounds h_upper_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from the
reflected-CDF tail route plus explicit scaled-drop regularity.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    baseMeasure h_base_bounds tail k_pos hwidth_pos hdrop

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from the
paper's upper-endpoint tail-mass sandwich plus explicit scaled-drop regularity.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail_and_scaled_drop
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail_and_scaled_drop
    baseMeasure h_base_bounds hbeta_pos hc_pos htail k_pos hwidth_pos hdrop

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from an exact
local upper-endpoint power identity plus explicit scaled-drop regularity.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power_and_scaled_drop
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power_and_scaled_drop
    baseMeasure h_base_bounds h_upper_power hbeta_pos hc_pos k_pos
    hwidth_pos hdrop

/--
Source Lemma 1, bounded-support iid route from an exact local reflected-CDF
power identity near zero.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
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
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    baseMeasure h_base_bounds h_reflected_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from an exact
local reflected-CDF power identity. The adjacent-drop law is derived
internally.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    baseMeasure h_base_bounds h_reflected_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Lemma 1, bounded-support iid source marginal asymptotic from an exact
local reflected-CDF power identity plus explicit scaled-drop regularity.
-/
theorem lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop
    {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta q) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop
    baseMeasure h_base_bounds h_reflected_power hbeta_pos hc_pos k_pos
    hwidth_pos hdrop

/-- Source Lemma 1, concrete continuous uniform `[0,1]` iid instance. -/
theorem lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic
    {k : ℕ} (k_pos : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => uniform01Measure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff 1 1 q.2.val) *
          boundedTailScale 1 a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic
    k_pos

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic from per-rank
reflected lower order-statistic integral identities.
-/
theorem lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {beta c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a))
    (h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => AppliedModelingLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a))
    (h_reflected_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            MeasureTheory.Integrable
              (fun sample =>
                AppliedModelingLib.Probability.ascendingOrderStatistic
                  (AppliedModelingLib.Probability.reflectedSample M sample)
                  ⟨i.val, lt_of_lt_of_le i.isLt hka⟩)
              (sampleMeasure a))
    (h_rank_integral :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            (∫ sample,
              AppliedModelingLib.Probability.ascendingOrderStatistic
                (AppliedModelingLib.Probability.reflectedSample M sample)
                ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂(sampleMeasure a)) =
              ∑ j : Fin (i.val + 1),
                boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hprob h_order_integrable h_top_integrable
    h_reflected_integrable h_rank_integral tail k_pos hM₀_pos
    hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, per-rank reflected-integral route with bounded-support a.e.
bounds discharging sorted-tuple and reflected-rank integrability obligations.
-/
theorem lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {beta c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_rank_integral :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            (∫ sample,
              AppliedModelingLib.Probability.ascendingOrderStatistic
                (AppliedModelingLib.Probability.reflectedSample M sample)
                ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂(sampleMeasure a)) =
              ∑ j : Fin (i.val + 1),
                boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c q.2.val) *
          boundedTailScale beta a) :=
  PRPKG24AccuracyDiversity.paper_lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    sampleMeasure hprob h_bounds h_rank_integral tail k_pos hM₀_pos
    hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint.
-/
theorem theorem1_ii_bounded_power_marginal_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_power_marginal_sequence_homogeneity
      likelihood beta hbeta_pos hlike_pos seq

/--
Source Theorem 1(ii), bounded-source loss-to-marginal bridge under an explicit
scaled-drop regularity hypothesis.
-/
theorem theorem1_ii_bounded_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
    {h : ℕ → ℝ} {A C beta : ℝ}
    (hbeta_pos : 0 < beta) (hC_pos : 0 < C)
    (hloss :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q => A - h q)
        (fun q => C * boundedTailScale beta q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - h q) - (A - h (q + 1))) / (A - h q))))
        Filter.atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q => h (q + 1) - h q)
      (fun q => (C / beta) * boundedPowerMarginalScale beta q) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
      hbeta_pos hC_pos hloss hdrop

/--
Source Theorem 1(ii), bounded order-statistic scaled-marginal certificate from
a source-side marginal-asymptotic certificate.
-/
noncomputable def theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_source
    {T : ℕ} {mu : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate mu k beta limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => limitCoeff) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_source
    C

/--
Source Theorem 1(ii), exact reflected-power bounded order-statistic
scaled-marginal checkpoint.
-/
noncomputable def theorem1_ii_bounded_reflected_power_order_statistic_scaled_marginal_certificate
    {T : ℕ} {beta : ℝ} {k : ℕ}
    (hbeta_pos : 0 < beta) (k_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (boundedReflectedPowerOrderStatisticMean beta)) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        boundedReflectedPowerTopKLossCoeff beta k / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_order_statistic_scaled_marginal_certificate
    hbeta_pos k_pos

/--
Source Theorem 1(ii), exact reflected-power bounded order-statistic sequence
for `β > 0`.
-/
theorem theorem1_ii_bounded_reflected_power_order_statistic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_order_statistic_sequence_homogeneity
    likelihood hbeta_pos hk hlike_pos seq

/--
Source Theorem 1(ii), exact reflected-power bounded order-statistic equation
form for `β > 0`.
-/
theorem theorem1_ii_bounded_reflected_power_order_statistic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_order_statistic_sequence_formula
    likelihood hbeta_pos hk hlike_pos seq

/--
Source Theorem 1(ii), concrete iid reflected-power bounded source table.
-/
theorem theorem1_ii_bounded_reflected_power_source_iid_order_statistic_mean_seq_eq_table
    {beta : ℝ} (hbeta_pos : 0 < beta) {q r : ℕ} (hrq : r < q) :
    boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta (q - r) q =
      boundedReflectedPowerOrderStatisticMean beta (q - r) q :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_source_iid_order_statistic_mean_seq_eq_table
    hbeta_pos hrq

/--
Source Theorem 1(ii), concrete iid reflected-power bounded top-`k` source
table.
-/
theorem theorem1_ii_bounded_reflected_power_source_iid_topK_sum_eq_table
    {beta : ℝ} (hbeta_pos : 0 < beta) (k q : ℕ) :
    orderStatisticTopKSumFromMean
        (boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta) k q =
      orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_source_iid_topK_sum_eq_table
    hbeta_pos k q

/--
Source Theorem 1(ii), concrete iid reflected-power bounded scaled-marginal
certificate.
-/
noncomputable def theorem1_ii_bounded_reflected_power_source_iid_order_statistic_scaled_marginal_certificate
    {T : ℕ} {beta : ℝ} {k : ℕ}
    (hbeta_pos : 0 < beta) (k_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (boundedReflectedPowerSourceIidOrderStatisticOracle T beta) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        boundedReflectedPowerTopKLossCoeff beta k / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_source_iid_order_statistic_scaled_marginal_certificate
    hbeta_pos k_pos

/--
Source Theorem 1(ii), concrete iid reflected-power bounded source sequence for
`β > 0`.
-/
theorem theorem1_ii_bounded_reflected_power_source_iid_order_statistic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
            likelihood k beta)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_source_iid_order_statistic_sequence_homogeneity
    likelihood hbeta_pos hk hlike_pos seq

/--
Source Theorem 1(ii), concrete iid reflected-power bounded source equation
form for `β > 0`.
-/
theorem theorem1_ii_bounded_reflected_power_source_iid_order_statistic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
            likelihood k beta)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_reflected_power_source_iid_order_statistic_sequence_formula
    likelihood hbeta_pos hk hlike_pos seq

/--
Source Theorem 1(ii), bounded order-statistic scaled-marginal certificate from
a loss asymptotic plus explicit scaled-drop regularity.
-/
noncomputable def theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop
    {T : ℕ} {mu : ℕ → ℕ → ℝ} {k : ℕ} {A C beta : ℝ}
    (hbeta_pos : 0 < beta) (k_pos : 0 < k) (hC_pos : 0 < C)
    (hloss :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => A - orderStatisticTopKSumFromMean mu k q)
        (fun q : ℕ => C * boundedTailScale beta q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - orderStatisticTopKSumFromMean mu k q) -
              (A - orderStatisticTopKSumFromMean mu k (q + 1))) /
              (A - orderStatisticTopKSumFromMean mu k q))))
        Filter.atTop (nhds (1 / beta))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => C / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop
    hbeta_pos k_pos hC_pos hloss hdrop

/--
Source Theorem 1(ii), bounded iid reflected-CDF source law as a reusable
scaled-marginal certificate. The adjacent-drop law is derived internally.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail
    baseMeasure h_base_bounds tail k_pos hwidth_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF count-floor bridge from the
scaled-marginal endpoint plus positive fixed low-count forward marginals.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_count_floor_eventually_of_base_ae_bounds_and_reflected_cdf_tail_and_low_forward_positive
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k floor : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hforward_pos :
      ∀ t : ItemType T, ∀ q : ℕ, q ≤ floor →
        0 <
          (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK
            k t q) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_count_floor_eventually_of_base_ae_bounds_and_reflected_cdf_tail_and_low_forward_positive
    baseMeasure h_base_bounds tail likelihood hlike_pos k_pos hwidth_pos
    hforward_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF count-floor bridge from the
paper's nonnegative-support convention.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_count_floor_eventually_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k floor : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_count_floor_eventually_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF count-floor bridge with the
natural `k - 1` finite prefix, discharged by a positive one-draw mean.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_base_ae_bounds_and_reflected_cdf_tail_and_positive_mean
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hmean_pos : 0 < ∫ x, x ∂baseMeasure) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).IsOptimalAtTotal N a →
        ∀ t, k - 1 < a.count t :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_base_ae_bounds_and_reflected_cdf_tail_and_positive_mean
    baseMeasure h_base_bounds tail likelihood hlike_pos k_pos hwidth_pos
    hmean_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF count-floor bridge from
nonnegative support and positive mass above a positive threshold.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_nonnegative_support_and_positive_tail_mass
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    {a : ℝ} (ha_pos : 0 < a)
    (hmass : 0 < baseMeasure (Set.Ici a))
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    ∀ᶠ N in Filter.atTop,
      ∀ alloc : CountAllocation T, 0 < N →
        (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).IsOptimalAtTotal N alloc →
        ∀ t, k - 1 < alloc.count t :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_nonnegative_support_and_positive_tail_mass
    baseMeasure h_base_bounds h_nonneg ha_pos hmass tail likelihood
    hlike_pos k_pos hwidth_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF count-floor bridge from
nonnegative support, positive upper endpoint, and the reflected-CDF tail law.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    ∀ᶠ N in Filter.atTop,
      ∀ alloc : CountAllocation T, 0 < N →
        (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).IsOptimalAtTotal N alloc →
        ∀ t, k - 1 < alloc.count t :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_count_pred_floor_eventually_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF sequence theorem
from the reduced large-gap certificate.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_large_gap_certificate
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hcert :
      BoundedIidReflectedCDFLargeGapCertificate
        baseMeasure likelihood k beta)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_large_gap_certificate
    baseMeasure h_base_bounds tail likelihood hlike_pos k_pos hwidth_pos
    hcert seq

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF equation (6) form
from the reduced large-gap certificate.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_large_gap_certificate
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hcert :
      BoundedIidReflectedCDFLargeGapCertificate
        baseMeasure likelihood k beta)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_large_gap_certificate
    baseMeasure h_base_bounds tail likelihood hlike_pos k_pos hwidth_pos
    hcert seq

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF sequence theorem
from the paper's nonnegative-support and upper-endpoint tail conventions.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos seq

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF equation (6) form
from the paper's nonnegative-support and upper-endpoint tail conventions.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid upper-endpoint-tail sequence theorem from
nonnegative support.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_tail_sequence_homogeneity_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_tail_sequence_homogeneity_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos hbeta_pos hc_pos htail
    likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid upper-endpoint-tail equation (6) form from
nonnegative support.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_tail_sequence_formula_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_tail_sequence_formula_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos hbeta_pos hc_pos htail
    likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid sequence theorem from the paper's
upper-endpoint density convention.  The density `g` is the reflected local
density at distance `u` below the upper endpoint `M`, so the upper-tail mass is
represented by the integral of `g` over `(0, x)`.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_homogeneity_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (g : ℝ → ℝ)
    (h_integrable :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Filter.Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_homogeneity_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos hbeta_pos hc_pos g
    h_integrable hmass hratio likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid equation (6) form from the paper's
upper-endpoint density convention.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_formula_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (g : ℝ → ℝ)
    (h_integrable :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Filter.Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)))
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_formula_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos hbeta_pos hc_pos g
    h_integrable hmass hratio likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid exact upper-endpoint power sequence theorem
from nonnegative support.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_eventually_eq_power_sequence_homogeneity_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_eventually_eq_power_sequence_homogeneity_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos h_upper_power hbeta_pos
    hc_pos likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), bounded iid exact upper-endpoint power equation (6) form
from nonnegative support.
-/
theorem theorem1_ii_bounded_iid_upper_endpoint_eventually_eq_power_sequence_formula_of_nonnegative_support
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_upper_endpoint_eventually_eq_power_sequence_formula_of_nonnegative_support
    baseMeasure h_base_bounds h_nonneg hM_pos h_upper_power hbeta_pos
    hc_pos likelihood hlike_pos k_pos hwidth_pos seq

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF sequence theorem
from nonnegative support and the remaining large-gap comparison.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_nonnegative_support_and_large_gap_count
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (large_gap_count :
      ∀ᶠ N in Filter.atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          k - 1 < qsrc →
          k - 1 < qdst →
          base_error N * (N : ℝ) <
            (qsrc : ℝ) / likelihood src ^ (beta / (beta + 1)) -
              (qdst : ℝ) / likelihood dst ^ (beta / (beta + 1)) →
          (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).weightedBackwardMarginal
              src qsrc <
            (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).weightedForwardMarginal
              dst qdst)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_homogeneity_of_nonnegative_support_and_large_gap_count
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos base_error base_error_nonneg base_error_tends_to_zero
    large_gap_count seq

/--
Source Theorem 1(ii), arbitrary bounded iid reflected-CDF equation (6) form
from nonnegative support and the remaining large-gap comparison.
-/
theorem theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_nonnegative_support_and_large_gap_count
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (likelihood : ItemType T → ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error)
    (large_gap_count :
      ∀ᶠ N in Filter.atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          k - 1 < qsrc →
          k - 1 < qdst →
          base_error N * (N : ℝ) <
            (qsrc : ℝ) / likelihood src ^ (beta / (beta + 1)) -
              (qdst : ℝ) / likelihood dst ^ (beta / (beta + 1)) →
          (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).weightedBackwardMarginal
              src qsrc <
            (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).weightedForwardMarginal
              dst qdst)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            likelihood k baseMeasure)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (beta / (beta + 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_sequence_formula_of_nonnegative_support_and_large_gap_count
    baseMeasure h_base_bounds h_nonneg hM_pos tail likelihood hlike_pos
    k_pos hwidth_pos base_error base_error_nonneg base_error_tends_to_zero
    large_gap_count seq

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from the paper's upper-endpoint tail-mass sandwich.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_tail
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_tail
    baseMeasure h_base_bounds hbeta_pos hc_pos htail k_pos hwidth_pos

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from an exact local upper-endpoint power identity.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power
    baseMeasure h_base_bounds h_upper_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from an exact local reflected-CDF power identity.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    baseMeasure h_base_bounds h_reflected_power hbeta_pos hc_pos k_pos
    hwidth_pos

/--
Source Theorem 1(ii), bounded iid reflected-CDF source law as a reusable
scaled-marginal certificate.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) beta c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    baseMeasure h_base_bounds tail k_pos hwidth_pos hdrop

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from the paper's upper-endpoint tail-mass sandwich.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_tail_and_scaled_drop
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (1 - ε) * (c / beta) * x ^ beta ≤
              baseMeasure.real (Set.Ici (M - x)) ∧
            baseMeasure.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_tail_and_scaled_drop
    baseMeasure h_base_bounds hbeta_pos hc_pos htail k_pos hwidth_pos hdrop

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from an exact local upper-endpoint power identity.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power_and_scaled_drop
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_upper_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        baseMeasure.real (Set.Ici (M - x)) =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_upper_endpoint_eventually_eq_power_and_scaled_drop
    baseMeasure h_base_bounds h_upper_power hbeta_pos hc_pos k_pos
    hwidth_pos hdrop

/--
Source Theorem 1(ii), bounded iid source law as a reusable scaled-marginal
certificate from an exact local reflected-CDF power identity.
-/
noncomputable def theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop
    {T : ℕ} {beta c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / beta) * x ^ beta)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / beta))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop
    baseMeasure h_base_bounds h_reflected_power hbeta_pos hc_pos k_pos
    hwidth_pos hdrop

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint in direct
equation (6) form.
-/
theorem theorem1_ii_bounded_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (beta / (beta + 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (beta / (beta + 1)))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_power_marginal_sequence_formula
      likelihood beta hbeta_pos hlike_pos seq

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint as a reusable
scaled-marginal certificate.
-/
noncomputable def theorem1_ii_bounded_power_marginal_scaled_marginal_certificate
    (T : ℕ) (beta : ℝ) :
    TopKScaledMarginalLimitCertificate
      (boundedPowerMarginalOracle T beta) 1
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => (1 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_ii_bounded_power_marginal_scaled_marginal_certificate
    T beta

/--
Source Theorem 1(ii), uniform bounded-support `β = 1` checkpoint.

The exact uniform top-`k` order-statistic route gives the `1/2`-homogeneity
limit under the paper-style all-eligible `k(N)` condition.
-/
theorem theorem1_ii_uniform_bounded_top_k_sequence_homogeneity_of_paper_bound
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
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / 2)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_bounded_top_k_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(ii), uniform bounded-support checkpoint in direct equation
(6) form.
-/
theorem theorem1_ii_uniform_bounded_top_k_sequence_formula_of_paper_bound
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
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / 2 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_bounded_top_k_sequence_formula_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(ii), uniform bounded-support checkpoint at the Definition 3
order-statistic oracle boundary.
-/
theorem theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound
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
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
            likelihood (kseq N))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / 2)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(ii), uniform bounded-support order-statistic checkpoint in
direct equation (6) form.
-/
theorem theorem1_ii_uniform_order_statistic_sequence_formula_of_paper_bound
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
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
            likelihood (kseq N))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / 2 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform_order_statistic_sequence_formula_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(ii), concrete iid uniform `[0,1]` order-statistic oracle
checkpoint.
-/
theorem theorem1_ii_uniform01_iid_order_statistic_sequence_homogeneity_of_paper_bound
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
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniform01IidOrderStatisticMeanSeq).toConsumptionModel
            likelihood (kseq N))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / 2)) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform01_iid_order_statistic_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(ii), concrete iid uniform `[0,1]` order-statistic oracle
checkpoint in direct equation (6) form.
-/
theorem theorem1_ii_uniform01_iid_order_statistic_sequence_formula_of_paper_bound
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
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniform01IidOrderStatisticMeanSeq).toConsumptionModel
            likelihood (kseq N))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / 2 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_ii_uniform01_iid_order_statistic_sequence_formula_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Source Theorem 1(iii), exponential-tail i.i.d. conditional item values,
exposed at the reusable top-`k` certificate seam.
-/
theorem theorem1_iii_exponential_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_sequence_homogeneity_of_certificate
      O likelihood k lambda hlambda_pos seq hcert

/--
Source Theorem 1(iii), exponential branch from the Lemma D.1-style sublinear
FOC certificate.
-/
theorem theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k lambda hlambda_pos seq hcert

/--
Source Theorem 1(iii), exponential branch from the floor-aware Lemma D.1-style
FOC certificate.
-/
theorem theorem1_iii_exponential_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k lambda hlambda_pos seq hcert

/--
Source Theorem 1(iii), exact top-one exponential instance.
-/
theorem theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle T lambda).toConsumptionModel
            likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity
      likelihood lambda hlambda_pos hlike_pos seq

/--
Source Lemma D.3, finite top-`k` exponential order-statistic marginal.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_forward_marginal
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_forward_marginal
    lambda k q

/--
Source Lemma D.3, finite top-`k` exponential order-statistic value.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_sum_Icc
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      ∑ j ∈ Finset.Icc 1 q,
        (1 / lambda) *
          (((min k j : ℕ) : ℝ) / (j : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_sum_Icc
    lambda k q

/--
Source Lemma D.3, finite top-`k` exponential order-statistic value.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_tail_harmonic_sum
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_tail_harmonic_sum
    lambda k q

/--
Source Lemma D.3, finite top-`k` exponential marginal nonnegativity.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_marginal_nonnegative
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    0 ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_marginal_nonnegative
    lambda hlambda_pos k q

/--
Source Lemma D.3, finite top-`k` exponential diminishing marginal values.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_marginal_antitone
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_marginal_antitone
    lambda hlambda_pos k q

/--
Source Lemma D.3, eventual strict diminishing marginal values for finite
top-`k` exponential order statistics.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_marginal_strict_antitone
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {k q : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ q + 1) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) <
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_marginal_strict_antitone
    lambda hlambda_pos hk_pos hk_le

/--
Source Lemma D.3, finite top-`k` exponential harmonic closed form.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_harmonic_closed_form
    (lambda : ℝ) {k q : ℕ} (hk_pos : 0 < k) (hkq : k ≤ q) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) * ((k : ℝ) * (1 + harmonicReal q - harmonicReal k)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_harmonic_closed_form
    lambda hk_pos hkq

/--
Source Lemma D.3, near-full finite top-`k` exponential order-statistic value.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_pred_card_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    exponentialTopKOrderStatisticValue lambda (q - 1) q =
      (1 / lambda) * (q : ℝ) - 1 / ((q : ℝ) * lambda) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_pred_card_value
    lambda hlambda_pos

/--
Source Lemma D.3, finite top-`k` exponential logarithmic asymptotic.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_log_asymptotic
    (lambda : ℝ) (k : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopKOrderStatisticValue lambda k q -
          ((1 / lambda) * (k : ℝ)) * Real.log q)
      Filter.atTop
      (nhds
        (((1 / lambda) * (k : ℝ)) *
          (1 + Real.eulerMascheroniConstant - harmonicReal k))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_log_asymptotic
    lambda k

/--
Source Lemma D.3, scaled-marginal certificate for the finite top-`k`
exponential order-statistic oracle.
-/
noncomputable def theorem1_iii_exponential_top_k_scaled_marginal_certificate
    (T : ℕ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (exponentialTopKOrderStatisticOracle T lambda k) k
      (exponentialTopKOrderStatisticScale lambda k)
      (fun _ : ItemType T => (1 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_scaled_marginal_certificate
    T lambda k hlambda_pos hk_pos

/--
Source Lemma D.3, finite top-`k` exponential diminishing-returns model.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda) :
    ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
      likelihood k).HasDiminishingReturns :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_diminishing_returns
    likelihood lambda k hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The concrete top-`k` sum of a finite vector of exponential draws is measurable.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_sum_measurable
    {q : ℕ} (k : ℕ) :
    Measurable (exponentialFiniteSampleTopKSum (q := q) k) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_sum_measurable
    k

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

When the sample maximum is nonnegative, the top-`k` sum is bounded by
`k` times the sample maximum.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_sum_le_k_mul_max
    {q : ℕ} [NeZero q] (k : ℕ) (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ AppliedModelingLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum k sample ≤
      (k : ℝ) * AppliedModelingLib.Probability.Exponential.finiteSampleMax sample :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_sum_le_k_mul_max
    k sample hmax_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

For `k = 1`, the at-most-one top-`k` sample statistic agrees with the finite
sample maximum whenever that maximum is nonnegative.
-/
theorem theorem1_iii_exponential_finite_sample_top_one_sum_eq_max
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ AppliedModelingLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum 1 sample =
      AppliedModelingLib.Probability.Exponential.finiteSampleMax sample :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_one_sum_eq_max
    sample hmax_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

If `k` covers the whole finite sample and all coordinates are nonnegative, the
top-`k` statistic is the full sample sum.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_sum_eq_sum_of_card_le
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (hqk : q ≤ k) (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample = ∑ i, sample i :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_sum_eq_sum_of_card_le
    k sample hqk h_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = 0`, the at-most-`k` top-sum statistic is identically zero.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_zero_sum
    {q : ℕ} (sample : Fin q → ℝ) :
    exponentialFiniteSampleTopKSum 0 sample = 0 :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_zero_sum
    sample

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

For nonnegative samples, the near-full top-`q-1` statistic is the full sample
sum minus the finite sample minimum.
-/
theorem theorem1_iii_exponential_finite_sample_top_pred_card_eq_sum_sub_min
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum (q - 1) sample =
      (∑ i : Fin q, sample i) -
        AppliedModelingLib.Probability.Exponential.finiteSampleMin sample :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_pred_card_eq_sum_sub_min
    sample h_nonneg

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_index_set_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (s : Finset (Fin q)) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = s} =
      (Real.exp (-(lambda * x))) ^ s.card *
        (1 - Real.exp (-(lambda * x))) ^ (q - s.card) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_index_set_probability
    lambda hlambda_pos x hx s

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          (successIndexSet (fun y : ℝ => x < y) sample).card = j} =
      (Nat.choose q j : ℝ) *
        (Real.exp (-(lambda * x))) ^ j *
          (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_probability
    lambda hlambda_pos x hx j

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_measurable
    {q : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        (successIndexSet (fun y : ℝ => x < y) sample).card) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_measurable
    x

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_min_real_measurable
    {q : ℕ} (x : ℝ) (k : ℕ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_min_real_measurable
    x k

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_tail_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (r : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} =
      ∑ j ∈ Finset.Icc r q,
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_tail_probability
    lambda hlambda_pos x hx r

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_min_integral_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ j ∈ Finset.Icc 0 q,
        ((min k j : ℕ) : ℝ) *
          ((Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_min_integral_finite_sum
    lambda hlambda_pos x hx k

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_min_integral_tail_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_min_integral_tail_sum
    lambda hlambda_pos x k

/--
Source Lemma D.3, iid exponential threshold-count bridge.
-/
theorem theorem1_iii_exponential_success_count_min_integral_tail_binomial_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ∑ j ∈ Finset.Icc r q,
          (Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_min_integral_tail_binomial_sum
    lambda hlambda_pos x hx k

/--
Source Lemma D.3, analytic binomial-mass integration support.
-/
theorem theorem1_iii_exponential_binomial_mass_integral_alternating_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (Nat.choose q j : ℝ) *
        ∑ m ∈ Finset.range (q - j + 1),
          ((-1 : ℝ) ^ (m + (q - j)) *
            ((q - j).choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_binomial_mass_integral_alternating_sum
    lambda hlambda_pos hj_pos hjq

/--
Source Lemma D.3, analytic binomial-mass integration support.
-/
theorem theorem1_iii_exponential_binomial_mass_integral_closed_form
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (1 / lambda) * (1 / ((j : ℕ) : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_binomial_mass_integral_closed_form
    lambda hlambda_pos hj_pos hjq

/--
Source Lemma D.3, deterministic threshold-count layer-cake support.
-/
theorem theorem1_iii_exponential_success_count_integral_eq_sum
    {q : ℕ} (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
      ∑ i : Fin q, sample i :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_success_count_integral_eq_sum
    sample h_nonneg

/--
Source Lemma D.3, deterministic top-`k` threshold-count layer-cake bridge.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_layer_cake
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample =
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_layer_cake
    k sample h_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The concrete top-`k` sum is integrable under the iid exponential product
measure.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_sum_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    MeasureTheory.Integrable
      (exponentialFiniteSampleTopKSum (q := q) k)
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_sum_integrable
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing top-`k` threshold-count layer-cake bridge.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_integral_layer_cake
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_integral_layer_cake
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing Fubini bridge.
-/
theorem theorem1_iii_exponential_threshold_layer_cake_integral_swap
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∫ sample,
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_threshold_layer_cake_integral_swap
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing binomial-tail reduction.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_tail_binomial_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (Nat.choose q j : ℝ) *
              (Real.exp (-(lambda * x))) ^ j *
                (1 - Real.exp (-(lambda * x))) ^ (q - j)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_tail_binomial_integral
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing top-`k` harmonic reduction.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_tail_harmonic_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_tail_harmonic_sum
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing finite top-`k` sample statistic.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic
    lambda hlambda_pos k

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The `k = 1` concrete top-`k` sample statistic has the same iid exponential
expectation as the finite maximum, namely `H_q/lambda`.
-/
theorem theorem1_iii_exponential_finite_sample_top_one_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 1 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_one_integral_harmonic_value
    lambda hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

When `k ≥ q`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_card_le_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {k : ℕ} (hqk : q ≤ k) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_card_le_integral_order_statistic
    lambda hlambda_pos hqk

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = q - 1`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle.
-/
theorem theorem1_iii_exponential_finite_sample_top_pred_card_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) (q - 1) sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda (q - 1) q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_pred_card_integral_order_statistic
    lambda hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = 0`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle.
-/
theorem theorem1_iii_exponential_finite_sample_top_k_zero_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 0 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda 0 q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sample_top_k_zero_integral_order_statistic
    lambda hlambda_pos q

/--
Source Theorem 1(iii), exact finite top-`k` exponential order-statistic
instance.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_sequence_homogeneity
      likelihood lambda k hlambda_pos hk_pos hlike_pos seq

/--
Source Theorem 1(iii), iid product-measure maximum survival for the exponential
branch.
-/
theorem theorem1_iii_exponential_product_max_survival_eq_formula
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
        {sample : Fin q → ℝ |
          AppliedModelingLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal =
      exponentialMaxSurvival lambda q x :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_product_max_survival_eq_formula
    lambda hlambda_pos hx

/--
Source Theorem 1(iii), exponential maximum survival algebra.

This exposes the all-`q` binomial expansion of
`1 - (1 - exp (-lambda*x))^q`, the analytic survival expression for a maximum
of `q` rate-`lambda` exponential draws on the nonnegative line.
-/
theorem theorem1_iii_exponential_max_survival_binomial_expansion
    (lambda : ℝ) (q : ℕ) (x : ℝ) :
    exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(lambda * x))) ^ (q - m) *
            (q.choose m : ℝ) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_max_survival_binomial_expansion
    lambda q x

/--
Source Theorem 1(iii), exponential maximum survival term integral.

Each positive natural power in the binomial expansion integrates to
`1/(n*lambda)`.
-/
theorem theorem1_iii_exponential_survival_power_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {n : ℕ} (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(lambda * x))) ^ n =
      1 / ((n : ℝ) * lambda) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_survival_power_integral
    lambda hlambda_pos hn

/--
Source Theorem 1(iii), exponential maximum survival integral reduced to a
finite alternating binomial sum.
-/
theorem theorem1_iii_exponential_max_survival_integral_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_max_survival_integral_finite_sum
    lambda hlambda_pos q

/--
Source Theorem 1(iii), exponential finite alternating binomial sum in harmonic
closed form.
-/
theorem theorem1_iii_exponential_finite_sum_eq_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    - ∑ m ∈ Finset.range q,
        ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
          (1 / (((q - m : ℕ) : ℝ) * lambda)) =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_finite_sum_eq_harmonic_value
    lambda hlambda_pos q

/--
Source Theorem 1(iii), exponential maximum-survival integral in harmonic closed
form.
-/
theorem theorem1_iii_exponential_max_survival_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_max_survival_integral_harmonic_value
    lambda hlambda_pos q

/--
Source Theorem 1(iii), iid product-measure maximum-survival integral in
harmonic closed form.
-/
theorem theorem1_iii_exponential_product_max_survival_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          {sample : Fin q → ℝ |
            AppliedModelingLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal) =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_product_max_survival_integral_harmonic_value
    lambda hlambda_pos

/--
Source Theorem 1(iii), iid product-measure maximum tail integral in harmonic
closed form.

This is the layer-cake tail-probability side for the finite iid maximum:
`μ.real {sample | x < max sample}` integrates to `H_q/lambda`.
-/
theorem theorem1_iii_exponential_product_max_tail_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.Exponential.finiteSampleMax sample} =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_product_max_tail_integral_harmonic_value
    lambda hlambda_pos

/--
Source Theorem 1(iii), conditional iid product-measure expected maximum in
harmonic closed form.

Given integrability of the finite maximum, layer cake identifies its Bochner
expectation with the verified tail integral `H_q/lambda`.
-/
theorem theorem1_iii_exponential_product_max_integral_harmonic_value_of_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q]
    (h_int : MeasureTheory.Integrable
      (AppliedModelingLib.Probability.Exponential.finiteSampleMax (q := q))
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)) :
    ∫ sample,
        AppliedModelingLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_product_max_integral_harmonic_value_of_integrable
    lambda hlambda_pos h_int

/--
Source Theorem 1(iii), iid product-measure expected maximum in harmonic closed
form.

This is the literal finite expectation statement:
`E[max of q iid Exp(lambda) draws] = H_q/lambda`.
-/
theorem theorem1_iii_exponential_product_max_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        AppliedModelingLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_product_max_integral_harmonic_value
    lambda hlambda_pos

/--
Source Theorem 1(iii), exponential top-one measure-facing base case.

This is the `q = 1` expected-maximum identity written directly as the survival
integral of the rate-`lambda` exponential CDF.
-/
theorem theorem1_iii_exponential_single_draw_survival_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - ProbabilityTheory.cdf
          (exponentialDistributionModel lambda hlambda_pos).measure x) =
      exponentialTopOneHarmonicValue lambda 1 :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_single_draw_survival_integral
    lambda hlambda_pos

/--
Source Theorem 1(iii), exact top-one exponential harmonic log approximation.
-/
theorem theorem1_iii_exponential_top_one_harmonic_log_approximation
    (lambda : ℝ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopOneHarmonicValue lambda q -
          (1 / lambda) * Real.log q)
      Filter.atTop
      (nhds ((1 / lambda) * Real.eulerMascheroniConstant)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_one_harmonic_log_approximation
    lambda

/--
Source Theorem 1(iii), direct equation (6) form.
-/
theorem theorem1_iii_exponential_sequence_formula_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ (1 : ℝ)) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hconv :=
    theorem1_iii_exponential_sequence_homogeneity_of_certificate
      O likelihood k lambda hlambda_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iii), direct equation (6) form from the sublinear FOC seam.
-/
theorem theorem1_iii_exponential_sequence_formula_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ (1 : ℝ)) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hconv :=
    theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k lambda hlambda_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iii), exact top-one exponential direct equation (6) form.
-/
theorem theorem1_iii_exponential_top_one_harmonic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle T lambda).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ) :=
    Finset.sum_pos
      (fun i _ => by simpa [Real.rpow_one] using hlike_pos i)
      Finset.univ_nonempty
  have hconv :=
    theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity
      likelihood lambda hlambda_pos hlike_pos seq
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ)
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iii), exact finite top-`k` exponential direct equation (6)
form.
-/
theorem theorem1_iii_exponential_top_k_order_statistic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iii_exponential_top_k_order_statistic_sequence_formula
      likelihood lambda k hlambda_pos hk_pos hlike_pos seq

/--
Source Theorem 1(iii), direct equation (6) form from the floor-aware sublinear
FOC seam.
-/
theorem theorem1_iii_exponential_sequence_formula_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ (1 : ℝ)) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hconv :=
    theorem1_iii_exponential_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k lambda hlambda_pos seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iv), Pareto i.i.d. conditional item values, exposed at the
reusable top-`k` certificate seam.
-/
theorem theorem1_iv_pareto_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_sequence_homogeneity_of_certificate
      O likelihood k alpha halpha_gt_one seq hcert

/--
Source Theorem 1(iv), Pareto branch from the Lemma D.1-style sublinear FOC
certificate.
-/
theorem theorem1_iv_pareto_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (alpha / (alpha - 1)))
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k alpha halpha_gt_one seq hcert

/--
Source Theorem 1(iv), Pareto branch from the floor-aware Lemma D.1-style FOC
certificate.
-/
theorem theorem1_iv_pareto_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (alpha / (alpha - 1)))
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k alpha halpha_gt_one seq hcert

/--
Source Theorem 1(iv), exact Pareto power-marginal checkpoint.
-/
theorem theorem1_iv_pareto_power_marginal_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T alpha).toConsumptionModel
            likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
    PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_power_marginal_sequence_homogeneity
      likelihood alpha halpha_gt_one hlike_pos seq

/--
Source Theorem 1(iv), direct equation (6) form.
-/
theorem theorem1_iv_pareto_sequence_formula_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1)))) := by
  have hconv :=
    theorem1_iv_pareto_sequence_homogeneity_of_certificate
      O likelihood k alpha halpha_gt_one seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (alpha / (alpha - 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iv), exact Pareto power-marginal direct equation (6) form.
-/
theorem theorem1_iv_pareto_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T alpha).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (alpha / (alpha - 1)))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T,
        (likelihood i) ^ (alpha / (alpha - 1)) :=
    Finset.sum_pos
      (fun i _ => Real.rpow_pos_of_pos
        (hlike_pos i) (alpha / (alpha - 1)))
      Finset.univ_nonempty
  have hconv :=
    theorem1_iv_pareto_power_marginal_sequence_homogeneity
      likelihood alpha halpha_gt_one hlike_pos seq
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (alpha / (alpha - 1))
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iv), exact Pareto power-marginal checkpoint as a reusable
scaled-marginal certificate.
-/
noncomputable def theorem1_iv_pareto_power_marginal_scaled_marginal_certificate
    (T : ℕ) (alpha : ℝ) :
    TopKScaledMarginalLimitCertificate
      (paretoPowerMarginalOracle T alpha) 1
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T => (1 : ℝ)) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_power_marginal_scaled_marginal_certificate
    T alpha

/--
Source Lemma D.4, fixed-rank Pareto finite-difference bridge.
-/
theorem lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
    {mu : ℕ → ℕ → ℝ} {alpha C : ℝ} {r : ℕ}
    (halpha : 1 < alpha) (hC : 0 < C)
    (hvalue :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => mu (q - r) q)
        (fun q : ℕ => C * ((q : ℝ) ^ (1 / alpha))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((mu (q + 1 - r) (q + 1) - mu (q - r) q) /
              mu (q - r) q)))
        Filter.atTop (nhds (1 / alpha))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (mu (q + 1 - r) (q + 1) - mu (q - r) q) /
          paretoPowerMarginalScale alpha q)
      Filter.atTop (nhds (C / alpha)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
    halpha hC hvalue hdrop

/--
Source Lemma D.4, fixed-rank Pareto finite-difference bridge with the
canonical gamma coefficient.
-/
theorem lemmaD4_pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    {mu : ℕ → ℕ → ℝ} {alpha : ℝ} {r : ℕ}
    (halpha : 1 < alpha)
    (hvalue :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => mu (q - r) q)
        (fun q : ℕ =>
          (Real.Gamma ((r : ℝ) + 1 - 1 / alpha) /
              Real.Gamma ((r : ℝ) + 1)) *
            ((q : ℝ) ^ (1 / alpha))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((mu (q + 1 - r) (q + 1) - mu (q - r) q) /
              mu (q - r) q)))
        Filter.atTop (nhds (1 / alpha))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (mu (q + 1 - r) (q + 1) - mu (q - r) q) /
          paretoPowerMarginalScale alpha q)
      Filter.atTop (nhds (paretoRankMarginalCoeff alpha r)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    halpha hvalue hdrop

/--
Source Lemma D.4, exact gamma-ratio fixed-rank sequence scaled limit.
-/
theorem lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit
    {alpha : ℝ} (halpha : 1 < alpha) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (paretoRankGammaRatioMean alpha r (q + 1) -
            paretoRankGammaRatioMean alpha r q) /
          paretoPowerMarginalScale alpha q)
      Filter.atTop (nhds (paretoRankMarginalCoeff alpha r)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit
    halpha r

/--
Source Lemma D.4, strict fixed-rank diminishing marginals for the exact
gamma-ratio sequence.
-/
theorem lemmaD4_pareto_rank_gamma_ratio_forward_marginal_strict_antitone
    {alpha : ℝ} (halpha : 1 < alpha) (r q : ℕ) :
    paretoRankGammaRatioMean alpha r (q + 2) -
        paretoRankGammaRatioMean alpha r (q + 1) <
      paretoRankGammaRatioMean alpha r (q + 1) -
        paretoRankGammaRatioMean alpha r q :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_rank_gamma_ratio_forward_marginal_strict_antitone
    halpha r q

/--
Source Lemma D.4, strict top-`k` diminishing marginals for the exact cited
gamma-ratio order-statistic sequence.
-/
theorem lemmaD4_pareto_cited_order_statistic_topK_forward_marginal_strict_antitone_eventually
    {alpha : ℝ} (halpha : 1 < alpha) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean alpha) k (q + 2) -
          orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean alpha) k (q + 1) <
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean alpha) k (q + 1) -
          orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean alpha) k q :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_cited_order_statistic_topK_forward_marginal_strict_antitone_eventually
    halpha hk

/--
Source Theorem 1(iv), Pareto order-statistic marginal asymptotic as a reusable
scaled-marginal certificate.
-/
noncomputable def theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_source
    (T : ℕ) {mu : ℕ → ℕ → ℝ} {k : ℕ} {alpha limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate mu k alpha limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T => limitCoeff) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_source
    T C

/--
Source Theorem 1(iv), Pareto order-statistic marginal asymptotic stated in
the standard `AsymptoticEquivalent` form expected from Lemma D.4/equation (77).
-/
noncomputable def theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_asymptotic_equivalent
    (T : ℕ) {mu : ℕ → ℕ → ℝ} {k : ℕ} {alpha limitCoeff : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean mu k (q + 1) -
            orderStatisticTopKSumFromMean mu k q)
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale alpha q)) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T => limitCoeff) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_asymptotic_equivalent
    T halpha hk hcoeff hmargin

/--
Source Theorem 1(iv), finite fixed-rank Pareto marginal-sum form.
-/
noncomputable def theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_sum_asymptotic_equivalent
    (T : ℕ) {mu : ℕ → ℕ → ℝ} {k : ℕ} {alpha limitCoeff : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          ∑ i : Fin k,
            (mu (q + 1 - i.val) (q + 1) - mu (q - i.val) q))
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale alpha q)) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T => limitCoeff) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_sum_asymptotic_equivalent
    T halpha hk hcoeff hmargin

/--
Source Theorem 1(iv), per-rank scaled-limit form.
-/
noncomputable def theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_scaled_limits
    (T : ℕ) {mu : ℕ → ℕ → ℝ} {k : ℕ} {alpha limitCoeff : ℝ}
    (rankCoeff : Fin k → ℝ)
    (halpha : 1 < alpha) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hcoeff_sum : (∑ i : Fin k, rankCoeff i) = limitCoeff)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (mu (q + 1 - i.val) (q + 1) - mu (q - i.val) q) /
              paretoPowerMarginalScale alpha q)
          Filter.atTop (nhds (rankCoeff i))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T => limitCoeff) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_scaled_limits
    T rankCoeff halpha hk hcoeff hcoeff_sum hrank

/--
Source Theorem 1(iv), Pareto-specialized per-rank scaled-limit form with the
canonical Lemma D.4 gamma coefficients.
-/
noncomputable def theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits
    (T : ℕ) {mu : ℕ → ℕ → ℝ} {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (mu (q + 1 - i.val) (q + 1) - mu (q - i.val) q) /
              paretoPowerMarginalScale alpha q)
          Filter.atTop (nhds (paretoRankMarginalCoeff alpha i.val))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T mu) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff alpha i.val) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits
    T halpha hk hrank

/--
Source Theorem 1(iv), Pareto-specialized scaled-marginal certificate for the
bottom-indexed gamma-ratio order-statistic mean sequence cited in Lemma D.4.
-/
noncomputable def theorem1_iv_pareto_cited_order_statistic_scaled_marginal_certificate
    (T : ℕ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (paretoCitedOrderStatisticMean alpha)) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff alpha i.val) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_cited_order_statistic_scaled_marginal_certificate
    T halpha hk

/--
Source Theorem 1(iv), Pareto expected-order-statistic scaled-marginal
certificate from a source identification with the cited gamma-ratio formula.
-/
noncomputable def theorem1_iv_pareto_expected_order_statistic_scaled_marginal_certificate_of_cited_source
    (T : ℕ)
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hsrc : ParetoCitedOrderStatisticSource sampleMeasure alpha) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq sampleMeasure)) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff alpha i.val) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_expected_order_statistic_scaled_marginal_certificate_of_cited_source
    T halpha hk hsrc

/--
Source Theorem 1(iv), concrete iid scale-one Pareto source law at the cited
gamma-ratio identification boundary.
-/
noncomputable def theorem1_iv_pareto_iid_order_statistic_scaled_marginal_certificate_of_cited_source
    (T : ℕ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hsrc : ParetoCitedOrderStatisticSource (paretoIidSampleMeasure alpha) alpha) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (paretoIidOrderStatisticMeanSeq alpha)) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff alpha i.val) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_scaled_marginal_certificate_of_cited_source
    T halpha hk hsrc

/-- Source Lemma D.4, concrete iid scale-one Pareto source package. -/
theorem lemmaD4_pareto_iid_cited_order_statistic_source
    {alpha : ℝ} (halpha : 1 < alpha) :
    ParetoCitedOrderStatisticSource (paretoIidSampleMeasure alpha) alpha :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_cited_order_statistic_source
    halpha

/--
Source Theorem 1(iv), concrete iid scale-one Pareto source law with the
Lemma D.4 cited-source bridge discharged.
-/
noncomputable def theorem1_iv_pareto_iid_order_statistic_scaled_marginal_certificate
    (T : ℕ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (paretoIidOrderStatisticMeanSeq alpha)) k
      (paretoPowerMarginalScale alpha)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff alpha i.val) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_scaled_marginal_certificate
    T halpha hk

/--
Source Lemma D.4, concrete iid scale-one Pareto upper-order-statistic survival
probability as a binomial tail.
-/
theorem lemmaD4_pareto_iid_upper_order_statistic_survival_binomial_tail
    {alpha x : ℝ} (halpha_pos : 0 < alpha) (hx : 1 ≤ x)
    {q : ℕ} (rankFromTop : Fin q) :
    (paretoIidSampleMeasure alpha q).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      1 - ∑ j ∈ Finset.Icc 0 (min rankFromTop.val q),
        (Nat.choose q j : ℝ) *
          (x ^ (-alpha)) ^ j *
            (1 - x ^ (-alpha)) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_upper_order_statistic_survival_binomial_tail
    halpha_pos hx rankFromTop

/--
Source Lemma D.4, concrete iid Pareto upper-order-statistic survival probability
as an upper binomial tail.
-/
theorem lemmaD4_pareto_iid_upper_order_statistic_survival_upper_binomial_tail
    {alpha x : ℝ} (halpha_pos : 0 < alpha) (hx : 1 ≤ x)
    {q : ℕ} (rankFromTop : Fin q) :
    (paretoIidSampleMeasure alpha q).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
        (Nat.choose q j : ℝ) *
          (x ^ (-alpha)) ^ j *
            (1 - x ^ (-alpha)) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_upper_order_statistic_survival_upper_binomial_tail
    halpha_pos hx rankFromTop

/--
Source Lemma D.4, concrete iid Pareto upper-order-statistic survival integral
below the support scale.
-/
theorem lemmaD4_pareto_iid_upper_order_statistic_tail_integral_below_scale
    {alpha : ℝ} (halpha_pos : 0 < alpha)
    {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (paretoIidSampleMeasure alpha q).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      1 :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_upper_order_statistic_tail_integral_below_scale
    halpha_pos rankFromTop

/--
Source Lemma D.4, concrete iid Pareto upper-order-statistic survival integral
over `(1,∞)`, reduced to the binomial-tail integrand.
-/
theorem lemmaD4_pareto_iid_upper_order_statistic_tail_integral_binomial_tail
    {alpha : ℝ} (halpha_pos : 0 < alpha)
    {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (paretoIidSampleMeasure alpha q).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      ∫ x in Set.Ioi (1 : ℝ),
        1 - ∑ j ∈ Finset.Icc 0 (min rankFromTop.val q),
          (Nat.choose q j : ℝ) *
            (x ^ (-alpha)) ^ j *
              (1 - x ^ (-alpha)) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_upper_order_statistic_tail_integral_binomial_tail
    halpha_pos rankFromTop

/--
Source Lemma D.4, concrete iid Pareto upper-order-statistic survival integral
over `(1,∞)`, reduced to the upper binomial-tail integrand.
-/
theorem lemmaD4_pareto_iid_upper_order_statistic_tail_integral_upper_binomial_tail
    {alpha : ℝ} (halpha_pos : 0 < alpha)
    {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (paretoIidSampleMeasure alpha q).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      ∫ x in Set.Ioi (1 : ℝ),
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            (x ^ (-alpha)) ^ j *
              (1 - x ^ (-alpha)) ^ (q - j) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_upper_order_statistic_tail_integral_upper_binomial_tail
    halpha_pos rankFromTop

/--
Source Lemma D.4, Pareto beta-kernel integral after the substitution
`y = x^(-alpha)`.
-/
theorem lemmaD4_pareto_kernel_integral_eq_beta
    {alpha : ℝ} (halpha : 1 < alpha) {q j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (x ^ (-alpha)) ^ j * (1 - x ^ (-alpha)) ^ (q - j)
      =
      (1 / alpha) *
        ProbabilityTheory.beta
          ((j : ℝ) - 1 / alpha)
          (((q - j : ℕ) : ℝ) + 1) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_kernel_integral_eq_beta
    halpha hj hjq

/-- Source Lemma D.4, finite-product form of the Pareto beta-kernel integral. -/
theorem lemmaD4_pareto_kernel_integral_eq_beta_product
    {alpha : ℝ} (halpha : 1 < alpha) {q j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (x ^ (-alpha)) ^ j * (1 - x ^ (-alpha)) ^ (q - j)
      =
      (1 / alpha) *
        ((Nat.factorial (q - j) : ℝ) /
          ∏ m ∈ Finset.range (q - j + 1),
            ((j : ℝ) - 1 / alpha + m)) :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_kernel_integral_eq_beta_product
    halpha hj hjq

/--
Source Theorem 1(iv), strict top-`k` diminishing marginals for an expected
order-statistic source identified with the cited Pareto gamma-ratio sequence.
-/
theorem lemmaD4_pareto_expected_order_statistic_topK_forward_marginal_strict_antitone_eventually_of_cited_source
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {alpha : ℝ} (halpha : 1 < alpha) {k : ℕ} (hk : 0 < k)
    (hsrc : ParetoCitedOrderStatisticSource sampleMeasure alpha) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 2) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) <
        orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k q :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_expected_order_statistic_topK_forward_marginal_strict_antitone_eventually_of_cited_source
    halpha hk hsrc

/--
Source Lemma D.4, strict top-`k` diminishing marginals for the concrete iid
scale-one Pareto source law, conditional on the cited gamma-ratio
identification.
-/
theorem lemmaD4_pareto_iid_order_statistic_topK_forward_marginal_strict_antitone_eventually_of_cited_source
    {alpha : ℝ} (halpha : 1 < alpha) {k : ℕ} (hk : 0 < k)
    (hsrc : ParetoCitedOrderStatisticSource (paretoIidSampleMeasure alpha) alpha) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean
          (paretoIidOrderStatisticMeanSeq alpha) k (q + 2) -
          orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k (q + 1) <
        orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k (q + 1) -
          orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k q :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_order_statistic_topK_forward_marginal_strict_antitone_eventually_of_cited_source
    halpha hk hsrc

/--
Source Lemma D.4, strict top-`k` diminishing marginals for the concrete iid
scale-one Pareto source law with the cited-source bridge discharged.
-/
theorem lemmaD4_pareto_iid_order_statistic_topK_forward_marginal_strict_antitone_eventually
    {alpha : ℝ} (halpha : 1 < alpha) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean
          (paretoIidOrderStatisticMeanSeq alpha) k (q + 2) -
          orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k (q + 1) <
        orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k (q + 1) -
          orderStatisticTopKSumFromMean
            (paretoIidOrderStatisticMeanSeq alpha) k q :=
  PRPKG24AccuracyDiversity.paper_lemmaD4_pareto_iid_order_statistic_topK_forward_marginal_strict_antitone_eventually
    halpha hk

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic sequence from the
count-level eventual FOC package.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity_of_eventual_foc_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha))
    (hcert :
      ParetoIidOrderStatisticEventualFOCCertificate likelihood k alpha) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity_of_eventual_foc_certificate
    likelihood halpha hk hlike_pos seq hcert

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic direct equation
form from the count-level eventual FOC package.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_formula_of_eventual_foc_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha))
    (hcert :
      ParetoIidOrderStatisticEventualFOCCertificate likelihood k alpha) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (alpha / (alpha - 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_formula_of_eventual_foc_certificate
    likelihood halpha hk hlike_pos seq hcert

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic sequence from the
reduced large-gap certificate.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity_of_large_gap_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha))
    (hcert :
      ParetoIidOrderStatisticLargeGapCertificate likelihood k alpha) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity_of_large_gap_certificate
    likelihood halpha hk hlike_pos seq hcert

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic direct equation form
from the reduced large-gap certificate.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_formula_of_large_gap_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha))
    (hcert :
      ParetoIidOrderStatisticLargeGapCertificate likelihood k alpha) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (alpha / (alpha - 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_formula_of_large_gap_certificate
    likelihood halpha hk hlike_pos seq hcert

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic sequence with the
large-gap certificate derived internally.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (alpha / (alpha - 1))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_homogeneity
    likelihood halpha hk hlike_pos seq

/--
Source Theorem 1(iv), concrete iid Pareto order-statistic direct equation form
with the large-gap certificate derived internally.
-/
theorem theorem1_iv_pareto_iid_order_statistic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k alpha)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (alpha / (alpha - 1)))) :=
  PRPKG24AccuracyDiversity.paper_theorem1_iv_pareto_iid_order_statistic_sequence_formula
    likelihood halpha hk hlike_pos seq

/--
Source Theorem 1(iv), direct equation (6) form from the floor-aware sublinear
FOC seam.
-/
theorem theorem1_iv_pareto_sequence_formula_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (alpha / (alpha - 1)))
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1)))) := by
  have hconv :=
    theorem1_iv_pareto_sequence_homogeneity_of_eventual_sublinear_foc_certificate
      O likelihood k alpha halpha_gt_one seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (alpha / (alpha - 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iv), direct equation (6) form from the sublinear FOC seam.
-/
theorem theorem1_iv_pareto_sequence_formula_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (alpha : ℝ)
    (halpha_gt_one : 1 < alpha)
    (hnorm :
      (∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1))) ≠ 0)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (alpha / (alpha - 1)))
        (gammaLikelihoodProfile likelihood (alpha / (alpha - 1)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (alpha / (alpha - 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (alpha / (alpha - 1)))) := by
  have hconv :=
    theorem1_iv_pareto_sequence_homogeneity_of_sublinear_foc_certificate
      O likelihood k alpha halpha_gt_one seq hcert
  have hformula :=
    (definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (alpha / (alpha - 1)) hnorm).1 hconv
  intro t
  simpa using hformula t

/--
Source Corollary 1 parameter algebra: every `0 < gamma < 1` is covered by the
bounded branch's `beta/(beta+1)` exponent.
-/
theorem corollary1_bounded_beta_for_gamma_between_zero_and_one
    {gamma : ℝ} (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    0 < gamma / (1 - gamma) ∧
      (gamma / (1 - gamma)) / (gamma / (1 - gamma) + 1) = gamma :=
    PRPKG24AccuracyDiversity.paper_corollary1_bounded_beta_for_gamma_between_zero_and_one
      hgamma_pos hgamma_lt_one

/--
Source Corollary 1 parameter algebra: every `gamma > 1` is covered by the
Pareto branch's `alpha/(alpha-1)` exponent.
-/
theorem corollary1_pareto_alpha_for_gamma_gt_one
    {gamma : ℝ} (hgamma_gt_one : 1 < gamma) :
    1 < gamma / (gamma - 1) ∧
      (gamma / (gamma - 1)) / (gamma / (gamma - 1) - 1) = gamma :=
    PRPKG24AccuracyDiversity.paper_corollary1_pareto_alpha_for_gamma_gt_one
      hgamma_gt_one

/--
Source Corollary 1 parameter split across the Theorem 1 distribution families.
-/
theorem corollary1_gamma_parameter_cases
    (gamma : ℝ) (hgamma_nonneg : 0 ≤ gamma) :
    gamma = 0 ∨
      (∃ beta : ℝ, 0 < beta ∧ beta / (beta + 1) = gamma) ∨
      gamma = 1 ∨
      (∃ alpha : ℝ, 1 < alpha ∧ alpha / (alpha - 1) = gamma) :=
    PRPKG24AccuracyDiversity.paper_corollary1_gamma_parameter_cases
      gamma hgamma_nonneg

/--
Source Corollary 1, finite-discrete Bernoulli realization for `gamma = 0`.
-/
theorem corollary1_finite_discrete_bernoulli_gamma_zero_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1TwoPointTopOneModel likelihood q)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (0 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (0 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_corollary1_finite_discrete_bernoulli_gamma_zero_sequence_formula
      likelihood q hq_pos hq_lt_one hlike_pos seq

/--
Source Corollary 1, bounded-branch concrete power-marginal realization for any
exponent `0 < gamma < 1`.
-/
theorem corollary1_bounded_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {gamma : ℝ}
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T (gamma / (1 - gamma))).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ gamma /
            ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
    PRPKG24AccuracyDiversity.paper_corollary1_bounded_power_marginal_sequence_formula
      likelihood hgamma_pos hgamma_lt_one hlike_pos seq

/--
Source Corollary 1, bounded-branch concrete iid reflected-power realization for
any exponent `0 < gamma < 1`.
-/
theorem corollary1_bounded_reflected_power_source_iid_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {gamma : ℝ} {k : ℕ}
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
            likelihood k (gamma / (1 - gamma)))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ gamma /
            ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
  PRPKG24AccuracyDiversity.paper_corollary1_bounded_reflected_power_source_iid_sequence_formula
    likelihood hgamma_pos hgamma_lt_one hk hlike_pos seq

/--
Source Corollary 1, Pareto-branch concrete power-marginal realization for any
exponent `gamma > 1`.
-/
theorem corollary1_pareto_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {gamma : ℝ}
    (hgamma_gt_one : 1 < gamma)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T (gamma / (gamma - 1))).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ gamma /
            ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
    PRPKG24AccuracyDiversity.paper_corollary1_pareto_power_marginal_sequence_formula
      likelihood hgamma_gt_one hlike_pos seq

/--
Source Corollary 1, exponential top-`k` order-statistic realization for
`gamma = 1`.
-/
theorem corollary1_exponential_top_k_order_statistic_gamma_one_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) :=
    PRPKG24AccuracyDiversity.paper_corollary1_exponential_top_k_order_statistic_gamma_one_sequence_formula
      likelihood lambda k hlambda_pos hk_pos hlike_pos seq

/--
Top-one (`k = 1`) supporting specialization of Corollary 1, retained for
downstream compatibility.  The arbitrary-fixed-`k` paper-facing route is in
`PaperInterface.corollary1`.
-/
theorem corollary1_any_nonnegative_gamma_concrete_model_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∃ M : ConsumptionModel T,
      ∀ seq : OptimalAllocationSequence (fun _ => M),
        ∀ t : ItemType T,
          Filter.Tendsto
            (fun N => CountAllocation.representation (seq.allocation N) t)
            Filter.atTop
            (nhds
              ((likelihood t) ^ gamma /
                ∑ i : ItemType T, (likelihood i) ^ gamma)) :=
  PRPKG24AccuracyDiversity.paper_corollary1_any_nonnegative_gamma_concrete_model_sequence_formula
    likelihood gamma hgamma_nonneg hlike_pos

/-- Source Corollary 1, exposed at the reusable top-`k` certificate seam. -/
theorem corollary1_any_gamma_attainable_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (gamma : ℝ)
    (_hgamma_nonneg : 0 ≤ gamma)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood gamma)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood gamma) :=
    PRPKG24AccuracyDiversity.paper_corollary1_any_gamma_attainable_of_certificate
      O likelihood k gamma _hgamma_nonneg seq hcert

/-! ## Theorem 2: Decaying Bernoulli Success Probabilities -/

/--
Source Theorem 2(i), direct share-limit form for the top-one model when
`0 <= alpha < 1`.  This includes the `alpha = 0` i.i.d. Bernoulli reduction.
-/
theorem theorem2_i_decaying_bernoulli_top_one_uniform_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_lt_one : alpha < 1)
    (hc_pos : 0 < c) (hd_nonneg : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d alpha 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d alpha)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) :=
  PRPKG24AccuracyDiversity.paper_theorem2_i_decaying_bernoulli_top_one_nonnegative_subunit_sequence_uniform_formula
    likelihood alpha c d halpha_nonneg halpha_lt_one hc_pos hd_nonneg hfirst
    hlike_pos seq

/--
Source Theorem 2(ii), direct share-limit form for the top-one model when
`alpha = 1`.
-/
theorem theorem2_ii_decaying_bernoulli_top_one_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / (1 + c)) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / (1 + c)))) :=
  PRPKG24AccuracyDiversity.paper_theorem2_ii_decaying_bernoulli_top_one_alpha_one_sequence_formula
    likelihood c d hc hd hfirst hlike_pos seq

/--
Source Theorem 2(iii), direct share-limit form for the top-one model when
`alpha > 1`.
-/
theorem theorem2_iii_decaying_bernoulli_top_one_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha_gt_one : 1 < alpha) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d alpha 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d alpha)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / alpha) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / alpha))) :=
  PRPKG24AccuracyDiversity.paper_theorem2_iii_decaying_bernoulli_top_one_superunit_sequence_formula
    likelihood alpha c d halpha_gt_one hc hd hfirst hlike_pos seq

/--
Source Theorem 2(iv), direct share-limit form for the all-consumed model when
`0 < alpha`.
-/
theorem theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (alpha c d : ℝ)
    (halpha : 0 < alpha) (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / alpha) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / alpha))) :=
  PRPKG24AccuracyDiversity.paper_theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_sequence_formula
    likelihood alpha c d halpha hc hd hlike_pos seq

/--
Source Theorem 2(iv), degenerate `alpha = 0` all-consumed endpoint: the printed
`1/alpha` profile is not meaningful, and the model reduces to the likelihood
argmax linear objective.
-/
theorem theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d : ℝ) (N : ℕ)
    (best : ItemType T)
    (hc_nonneg : 0 ≤ c)
    (hbest : ∀ t, likelihood t ≤ likelihood best) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d 0).IsOptimalAtTotal
      N (allOnTypeAllocation N best) :=
  PRPKG24AccuracyDiversity.paper_theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax_optimum
    likelihood c d N best hc_nonneg hbest

/--
Source Proposition 4, conditional continuous-sphere endpoint: the uniform
profile minimizes the large-`n` relaxed objective once the source analytic
certificate has supplied the uniform value and universal lower bound.
-/
theorem proposition4_continuous_sphere_uniform_minimizes
    {Profile : Type*}
    (C : Proposition4ContinuousSphereCertificate Profile) :
    ∀ alpha : Profile, C.gamma C.uniformProfile ≤ C.gamma alpha :=
    PRPKG24AccuracyDiversity.paper_proposition4_continuous_sphere_uniform_minimizes
      C

/--
Source Proposition 4, abstract averaging endpoint: the final averaging/sup
argument after the source has supplied the sphere symmetry and Laplace
interfaces.
-/
theorem proposition4_averaging_uniform_minimizes
    {Profile User : Type*}
    (C : Proposition4AveragingCertificate Profile User) :
    ∀ alpha : Profile, C.gamma C.uniformProfile ≤ C.gamma alpha :=
    PRPKG24AccuracyDiversity.paper_proposition4_averaging_uniform_minimizes C

/--
Source Proposition 4, finite-user averaging endpoint: finite uniform averages
automatically supply the average-to-witness step.
-/
theorem proposition4_finite_averaging_uniform_minimizes
    {Profile User : Type*} [Fintype User] [Nonempty User]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (average_rho_eq_uniformValue :
      ∀ alpha : Profile,
        (∑ u : User, rho alpha u) / (Fintype.card User : ℝ) =
          uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_finite_averaging_uniform_minimizes
    gamma rho uniformProfile uniformValue uniform_gamma_eq
    average_rho_eq_uniformValue rho_le_gamma

/--
Source Proposition 4, probability-user averaging endpoint: the continuous
first-moment version of the final averaging/sup minimization step.
-/
theorem proposition4_probability_averaging_uniform_minimizes
    {Profile User : Type*} [MeasurableSpace User]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable :
      ∀ alpha : Profile, MeasureTheory.Integrable (rho alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_rho_eq_uniformValue :
      ∀ alpha : Profile,
        (∫ u, rho alpha u ∂userMeasure) = uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_averaging_uniform_minimizes
    userMeasure gamma rho uniformProfile uniformValue rho_integrable
    uniform_gamma_eq integral_rho_eq_uniformValue rho_le_gamma

/--
Source Proposition 4, probability-kernel averaging endpoint: Fubini plus
item-level user symmetry imply the final averaging/sup minimization step.
-/
theorem proposition4_probability_kernel_averaging_uniform_minimizes
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable
          (fun u => ∫ x, kernel x u ∂profileMeasure alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_kernel_swap :
      ∀ alpha : Profile,
        (∫ u, (∫ x, kernel x u ∂profileMeasure alpha) ∂userMeasure) =
          ∫ x, (∫ u, kernel x u ∂userMeasure) ∂profileMeasure alpha)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_averaging_uniform_minimizes
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue rho_integrable uniform_gamma_eq integral_kernel_swap
    kernel_user_integral_eq rho_le_gamma

/--
Source Proposition 4, product-integrable probability-kernel averaging endpoint:
product integrability supplies the Fubini swap and user-level integrability.
-/
theorem proposition4_probability_kernel_integrable_averaging_uniform_minimizes
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_integrable_averaging_uniform_minimizes
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq kernel_user_integral_eq
    rho_le_gamma

/--
Source Proposition 4, product-integrable kernel endpoint with `Gamma`
identified by the unit-weight positive-Laplace/attained-maximum bridge.
-/
theorem
    proposition4_probability_kernel_integrable_averaging_uniform_minimizes_of_positive_laplace_rate_unique_attained_max_unitWeight
    {Profile User Item : Type*} [TopologicalSpace User]
    [MeasurableSpace User] [OpensMeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma supValue : Profile → ℝ)
    (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u,
              Real.exp
                ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha))
              ∂userMeasure)
          (-(gamma alpha)))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure userMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : User =>
            Real.exp
              ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          userMeasure)
    (kernel_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_integrable_averaging_uniform_minimizes_of_positive_laplace_rate_unique_attained_max_unitWeight
    userMeasure profileMeasure profile_probability gamma supValue kernel
    uniformProfile uniformValue hsource hopen hF_int kernel_integrable
    uniform_gamma_eq kernel_user_integral_eq x0 hmax hx0 hcont

/--
Source Proposition 4, symmetry-driven product-integrable kernel endpoint with
`Gamma` identified by the unit-weight positive-Laplace/attained-maximum bridge.
The symmetry hypotheses reduce the constant user-integral premise to the
anchor integral.
-/
theorem
    proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_positive_laplace_rate_unique_attained_max_unitWeight
    {Profile User Item Sym : Type*} [TopologicalSpace User]
    [MeasurableSpace User] [OpensMeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma supValue : Profile → ℝ)
    (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u,
              Real.exp
                ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha))
              ∂userMeasure)
          (-(gamma alpha)))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure userMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : User =>
            Real.exp
              ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          userMeasure)
    (kernel_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym,
        MeasureTheory.MeasurePreserving (userAction g) userMeasure
          userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_positive_laplace_rate_unique_attained_max_unitWeight
    userMeasure profileMeasure profile_probability gamma supValue kernel
    uniformProfile uniformValue hsource hopen hF_int kernel_integrable
    uniform_gamma_eq userAction itemAction anchor userAction_measurePreserving
    userAction_measurableEmbedding kernel_diagonal_invariant
    itemAction_transitive anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Source Proposition 4, symmetry-driven product-integrable kernel endpoint for
the Laplace-defined objective. This removes the explicit source-rate identity
premise by deriving the rate from the shared positive-Laplace theorem.
-/
theorem
    proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_laplace_defined_gamma
    {Profile User Item Sym : Type*} [TopologicalSpace User]
    [MeasurableSpace User] [OpensMeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure userMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : User =>
            Real.exp
              ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          userMeasure)
    (kernel_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_sup_eq : supValue uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym,
        MeasureTheory.MeasurePreserving (userAction g) userMeasure
          userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_laplace_defined_gamma
    userMeasure profileMeasure profile_probability supValue kernel
    uniformProfile uniformValue hopen hF_int kernel_integrable
    uniform_sup_eq userAction itemAction anchor userAction_measurePreserving
    userAction_measurableEmbedding kernel_diagonal_invariant
    itemAction_transitive anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Source Proposition 4, two-measure symmetry-driven product-integrable kernel
endpoint. The preference measure is used for the source Laplace-rate premise;
the uniform user measure is used for Fubini and symmetry averaging.
-/
theorem
    proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_preference_laplace_and_uniform_average
    {Profile User Item Sym : Type*} [TopologicalSpace User]
    [MeasurableSpace User] [OpensMeasurableSpace User] [MeasurableSpace Item]
    (preferenceMeasure uniformUserMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    [MeasureTheory.IsProbabilityMeasure uniformUserMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma supValue : Profile → ℝ)
    (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hsource :
      ∀ alpha : Profile,
        AppliedModelingLib.Probability.HasExponentialRate
          (fun n : ℕ =>
            ∫ u,
              Real.exp
                ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha))
              ∂preferenceMeasure)
          (-(gamma alpha)))
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : User =>
            Real.exp
              ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod uniformUserMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving_uniform :
      ∀ g : Sym,
        MeasureTheory.MeasurePreserving (userAction g) uniformUserMeasure
          uniformUserMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂uniformUserMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_preference_laplace_and_uniform_average
    preferenceMeasure uniformUserMeasure profileMeasure profile_probability
    gamma supValue kernel uniformProfile uniformValue hsource hopen hF_int
    kernel_integrable_uniform uniform_gamma_eq userAction itemAction anchor
    userAction_measurePreserving_uniform userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive
    anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Source Proposition 4, source-faithful two-measure endpoint for the
Laplace-defined objective. This is the current strongest paper-facing
Proposition 4 theorem before instantiating the concrete sphere model.
-/
theorem
    proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_preference_laplace_and_uniform_average_laplace_defined_gamma
    {Profile User Item Sym : Type*} [TopologicalSpace User]
    [MeasurableSpace User] [OpensMeasurableSpace User] [MeasurableSpace Item]
    (preferenceMeasure uniformUserMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure preferenceMeasure]
    [MeasureTheory.IsProbabilityMeasure uniformUserMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (supValue : Profile → ℝ)
    (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (hopen : MeasureTheory.Measure.IsOpenPosMeasure preferenceMeasure)
    (hF_int :
      ∀ alpha : Profile, ∀ n : ℕ,
        MeasureTheory.Integrable
          (fun u : User =>
            Real.exp
              ((n : ℝ) * (∫ x, kernel x u ∂profileMeasure alpha)))
          preferenceMeasure)
    (kernel_integrable_uniform :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod uniformUserMeasure))
    (uniform_sup_eq : supValue uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving_uniform :
      ∀ g : Sym,
        MeasureTheory.MeasurePreserving (userAction g) uniformUserMeasure
          uniformUserMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂uniformUserMeasure) = uniformValue)
    (x0 : Profile → User)
    (hmax :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ supValue alpha)
    (hx0 :
      ∀ alpha : Profile,
        (∫ x, kernel x (x0 alpha) ∂profileMeasure alpha) =
          supValue alpha)
    (hcont :
      ∀ alpha : Profile,
        ContinuousAt
          (fun u : User => ∫ x, kernel x u ∂profileMeasure alpha)
          (x0 alpha)) :
    ∀ alpha : Profile, supValue uniformProfile ≤ supValue alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes_of_preference_laplace_and_uniform_average_laplace_defined_gamma
    preferenceMeasure uniformUserMeasure profileMeasure profile_probability
    supValue kernel uniformProfile uniformValue hopen hF_int
    kernel_integrable_uniform uniform_sup_eq userAction itemAction anchor
    userAction_measurePreserving_uniform userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive
    anchor_integral_eq_uniformValue x0 hmax hx0 hcont

/--
Source Proposition 4, symmetry-driven product-integrable probability-kernel
averaging endpoint: product integrability supplies Fubini, and diagonal
symmetry plus transitivity supplies constant item-level user integrals.
-/
theorem
    proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes
    {Profile User Item Sym : Type*} [MeasurableSpace User]
    [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        MeasureTheory.Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym,
        MeasureTheory.MeasurePreserving (userAction g) userMeasure
          userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_symmetry_integrable_averaging_uniform_minimizes
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq userAction itemAction
    anchor userAction_measurePreserving userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive
    anchor_integral_eq_uniformValue rho_le_gamma

/--
Source Proposition 4, bounded probability-kernel averaging endpoint:
measurability and an a.e. real bound imply the product integrability needed
for Fubini.
-/
theorem proposition4_probability_kernel_bounded_averaging_uniform_minimizes
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : MeasureTheory.Measure User)
    [MeasureTheory.IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → MeasureTheory.Measure Item)
    (profile_probability :
      ∀ alpha : Profile,
        MeasureTheory.IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ) (C : ℝ)
    (kernel_aestronglyMeasurable :
      ∀ alpha : Profile,
        MeasureTheory.AEStronglyMeasurable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (kernel_norm_le :
      ∀ alpha : Profile,
        ∀ᵐ xu ∂((profileMeasure alpha).prod userMeasure),
          ‖Function.uncurry kernel xu‖ ≤ C)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    ∀ alpha : Profile, gamma uniformProfile ≤ gamma alpha :=
  PRPKG24AccuracyDiversity.paper_proposition4_probability_kernel_bounded_averaging_uniform_minimizes
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue C kernel_aestronglyMeasurable kernel_norm_le
    uniform_gamma_eq kernel_user_integral_eq rho_le_gamma

/-! ## Proposition 2: Uniform Top-`k` Accuracy-Diversity Tradeoff -/

/--
Proposition 2 audit: the optimizer formula printed in the PDF sums to `N - T`,
not `N`, for the Lean type count `T`.
-/
theorem proposition2_printed_relaxed_optimizer_total_mismatch
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    ∑ t : ItemType T, uniformSqrtPrintedOptTarget likelihood N t =
      (N : ℝ) - T :=
    PRPKG24AccuracyDiversity.paper_proposition_2_printed_relaxed_optimizer_total_mismatch
      likelihood N hnorm

/--
Proposition 2 corrected relaxed optimizer: the shifted square-root target used
by the Lean proof has total `N`.
-/
theorem proposition2_corrected_relaxed_optimizer_total
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    ∑ t : ItemType T, uniformSqrtRealOptTarget likelihood N t =
      (N : ℝ) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_corrected_relaxed_optimizer_total
      likelihood N hnorm

/--
Current source Proposition 2 asymptotic endpoint.  For any positive admissible
top-`k(N)` schedule satisfying the paper-style minimum square-root-share bound,
every selected finite optimum converges to the `1/2`-homogeneity profile.
-/
theorem proposition2_uniform_top_k_sequence_homogeneity_of_paper_bound
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
    seq.toAllocationSequence.ConvergesToProfile
      (proposition2SqrtProfile likelihood) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Corrected Proposition 2 finite theorem.  This is the unconditional finite
statement Lean proves from the exact uniform top-`k` objective and the
paper-style eligibility condition: the finite error is `(2T+1)/N`, which is
still `O(1/N)` and therefore sufficient for the source's asymptotic
homogeneity consequence.
-/
theorem proposition2_uniform_top_k_corrected_finite_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (hkpos : 0 < k)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (a : CountAllocation T)
    (hbound :
      (k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a) :
    (proposition2SqrtProfile likelihood).Approx a
      ((2 * (Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_corrected_finite_of_paper_bound
      likelihood N k hNpos hkpos hlike_pos a hbound hopt

/--
Corrected Proposition 2 exact-rate asymptotic theorem.  The source downstream
use only needs this vanishing `O(1/N)` bound, not the printed sharp constant.
-/
theorem proposition2_uniform_top_k_corrected_asymptotic_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun N => uniformTopKConsumptionModel likelihood (kseq N))
      (proposition2SqrtProfile likelihood) AppliedModelingLib.Math.ExactInvRate :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_corrected_asymptotic_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound

/--
Corrected Proposition 2 sequence homogeneity.  This is the downstream
paper-useful endpoint: optimal sequences converge to the `1/2` profile under
the proved finite `(2T+1)/N` error.
-/
theorem proposition2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound
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
    seq.toAllocationSequence.ConvergesToProfile
      (proposition2SqrtProfile likelihood) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq

/--
Proposition 2 sharp finite-bound bridge.  If the missing Lemma D.5-style
integer optimizer closeness to the corrected square-root target is supplied,
the paper's finite `(T+1)/N` conclusion follows.
-/
theorem proposition2_uniform_top_k_sharp_finite_of_count_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (a : CountAllocation T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * proposition2SqrtShare likelihood t| ≤
          (Fintype.card (ItemType T) : ℝ) + 1) :
    (proposition2SqrtProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_sharp_finite_of_count_closeness
      likelihood N k hNpos a hopt hnorm hclose

/--
Proposition 2 paper-route sharp finite-bound bridge.  If the paper's Lemma
D.5-style closeness to the displayed relaxed optimizer is supplied, the finite
`(T+1)/N` conclusion follows.  The displayed optimizer's total mismatch is
recorded separately above.
-/
theorem proposition2_uniform_top_k_sharp_finite_of_printed_optimizer_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (a : CountAllocation T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hclose_printed :
      ∀ t,
        |(a.count t : ℝ) - uniformSqrtPrintedOptTarget likelihood N t| ≤
          (Fintype.card (ItemType T) : ℝ)) :
    (proposition2SqrtProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) :=
    PRPKG24AccuracyDiversity.paper_proposition_2_uniform_top_k_sharp_finite_of_printed_optimizer_closeness
      likelihood N k hNpos a hopt hnorm hclose_printed

/--
Source Corollary 3: common-success-probability Bernoulli conditional values
give asymptotic `0`-homogeneity even when type likelihoods vary.
-/
theorem corollary3_iid_bernoulli_asymptotic_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (uniformProfile T) :=
    PRPKG24AccuracyDiversity.BernoulliSatisfactionModel.paper_corollary3_iid_bernoulli_asymptotic_uniform_homogeneity
      B hprob_pos hprob_lt_one hlike_pos hprob_eq

/--
Source Theorem 3: varying Bernoulli success probabilities give limiting
representation proportional to `1 / log (1 / (1 - q_t))`.
-/
theorem theorem3_varying_success_probability_log_share
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
    PRPKG24AccuracyDiversity.paper_theorem3_varying_success_probability_log_share
      B hprob_pos hprob_lt_one hlike_pos

/--
Source Theorem 3, direct share-limit form.
-/
theorem theorem3_varying_success_probability_log_share_formula
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (seq : OptimalAllocationSequence (fun _ => B.toConsumptionModel)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          (theorem3LogShareWeight B t /
            ∑ i : ItemType T, theorem3LogShareWeight B i)) :=
  PRPKG24AccuracyDiversity.paper_theorem3_varying_success_probability_log_share_formula
    B hprob_pos hprob_lt_one hlike_pos seq

/--
Source Theorem 3, all-consumed side: if `best` maximizes per-item Bernoulli
value, allocating all recommendations to `best` is optimal when all recommended
items are consumed.
-/
theorem theorem3_all_consumed_argmax_optimum
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best) :
    (bernoulliAllConsumedModel B).IsOptimalAtTotal
      N (allOnTypeAllocation N best) :=
    PRPKG24AccuracyDiversity.paper_theorem3_all_consumed_argmax_optimum
      B N best hbest

end PaperInterface
end PRPKG24AccuracyDiversity
