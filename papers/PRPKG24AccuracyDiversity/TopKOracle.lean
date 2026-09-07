import AppliedModelingLib.Foundations.Probability.OrderStatistics
import AppliedModelingLib.Applications.RecommenderSystems.TopKOracle
import PRPKG24AccuracyDiversity.Basic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/-!
The paper-facing names below are thin aliases for reusable library interfaces:
the bottom-indexed order-statistic bridge in
`AppliedModelingLib.Foundations.Probability.OrderStatistics` and the generic
top-`k` expectation oracle/allocation bridge in
`AppliedModelingLib.Applications.RecommenderSystems.TopKOracle`.
-/

/--
Paper Definition 3 interface: `μ rank sampleSize` is the expected value of the
`rank`-th smallest order statistic among `sampleSize` i.i.d. draws.
-/
noncomputable abbrev orderStatisticTopKSumFromMean :
    (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ := AppliedModelingLib.Probability.orderStatisticTopKSumFromMean

@[simp] theorem orderStatisticTopKSumFromMean_zero_samples
    (μ : ℕ → ℕ → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean μ k 0 = 0 :=  AppliedModelingLib.Probability.orderStatisticTopKSumFromMean_zero_samples μ k

@[simp] theorem orderStatisticTopKSumFromMean_zero_k
    (μ : ℕ → ℕ → ℝ) (a : ℕ) :
    orderStatisticTopKSumFromMean μ 0 a = 0 :=  AppliedModelingLib.Probability.orderStatisticTopKSumFromMean_zero_k μ a

theorem orderStatisticTopKSumFromMean_eq_bottomIndexed_sum
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i ∈ Finset.range (min k a), μ (a - i) a := AppliedModelingLib.Probability.orderStatisticTopKSumFromMean_eq_bottomIndexed_sum μ k a

/--
When the sample count is at least `k`, the paper's `min k a` top-`k`
order-statistic sum is the `Fin k` sum over the upper order-statistic means.
-/
theorem orderStatisticTopKSumFromMean_eq_fin_sum_of_le
    (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i : Fin k, μ (a - i.val) a :=
   AppliedModelingLib.Probability.orderStatisticTopKSumFromMean_eq_fin_sum_of_le
    μ hka

/--
Fixed-`k` endpoint loss form of
`orderStatisticTopKSumFromMean_eq_fin_sum_of_le`.
-/
theorem orderStatisticTopKLossFromMean_eq_fin_loss_of_le
    (M : ℝ) (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a =
      (k : ℝ) * M - ∑ i : Fin k, μ (a - i.val) a :=
   AppliedModelingLib.Probability.orderStatisticTopKLossFromMean_eq_fin_loss_of_le
    M μ hka

/-!
## Pointwise tuple source bridge

The paper's `μ_D(i,a)` is an expected order-statistic mean.  Before taking
expectations, a concrete `a`-tuple of real values already supplies the same
bottom-indexed order-statistic top-`k` sum.  Distribution files can integrate
this pointwise bridge to instantiate `TopKValueOracle.ofOrderStatisticMean`.
-/

/--
The `rank`-th smallest value of a concrete `a`-sample, using the paper's
one-based rank convention.  Out-of-range ranks are set to zero; the top-`k`
sum theorem below only evaluates valid ranks.
-/
noncomputable abbrev sampleOrderStatisticValue {a : ℕ}
    (sample : Fin a → ℝ) (rank : ℕ) : ℝ := AppliedModelingLib.Probability.sampleOrderStatisticValue sample rank

theorem sampleOrderStatisticValue_measurable {a : ℕ} (rank : ℕ) :
    Measurable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) :=  AppliedModelingLib.Probability.sampleOrderStatisticValue_measurable rank

theorem sampleOrderStatisticValue_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) μ :=
   AppliedModelingLib.Probability.sampleOrderStatisticValue_integrable_of_ae_bounds
    L U μ rank h_bounds

theorem sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    ∀ i ∈ Finset.range (min k a),
      MeasureTheory.Integrable
        (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample (a - i)) μ :=
    AppliedModelingLib.Probability.sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
      L U μ k h_bounds

/--
Pointwise Proposition 5 bridge: the paper's bottom-indexed order-statistic
sum induced by a concrete sorted tuple equals the tuple's top-`k` sample sum.
-/
theorem orderStatisticTopKSumFromSample_eq_sampleTopKSum
    {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean
        (fun rank sampleSize =>
          if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
        k a =
      AppliedModelingLib.Probability.sampleTopKSum sample k :=
   AppliedModelingLib.Probability.orderStatisticTopKSumFromSample_eq_sampleTopKSum
    sample k

/--
Expected paper order-statistic mean induced by a sample law on `a` real
draws.  The value is only intended at `sampleSize = a`; other sample sizes are
set to zero so the function has the paper's global `ℕ → ℕ → ℝ` shape.
-/
noncomputable abbrev expectedSampleOrderStatisticMean {a : ℕ}
    (μ : MeasureTheory.Measure (Fin a → ℝ)) (rank sampleSize : ℕ) : ℝ :=
  AppliedModelingLib.Probability.expectedSampleOrderStatisticMean μ rank sampleSize

/--
Expectation form of the pointwise Proposition 5 bridge: if `μ_D` is induced
by integrating the sample order statistics, then the paper's top-`k`
order-statistic sum is the expected pointwise top-`k` sample sum.
-/
theorem expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a =
      AppliedModelingLib.Probability.expectedSampleTopKSum μ k :=
    AppliedModelingLib.Probability.expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
      μ k h_integrable

/--
Expected bounded-support top-`k` reflection in the paper's `μ_D` interface.
This is the measure-level source bridge before distribution-specific CDF
identities identify the reflected-bottom expectation with Lemma D.2's
integral terms.
-/
theorem expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ)
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => AppliedModelingLib.Probability.sampleTopKSum sample k) μ) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean μ) k a =
      AppliedModelingLib.Probability.expectedReflectedBottomKSum M μ k :=
    AppliedModelingLib.Probability.expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
      M μ k h_order_integrable h_top_integrable

/--
Paper-shaped expected order-statistic mean induced by a family of finite sample
laws, one law for each sample size.
-/
noncomputable abbrev expectedOrderStatisticMeanSeq
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (rank sampleSize : ℕ) : ℝ := AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq sampleMeasure rank sampleSize

/--
Varying-sample-size version of
`expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum`, producing the
paper's global `μ_D(rank,a)` interface from a family of sample laws.
-/
theorem expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
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
    AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
      sampleMeasure k a h_integrable

/--
Varying-sample-size bounded reflection bridge in the global `μ_D(rank,a)`
interface.
-/
theorem expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
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
    AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
      M sampleMeasure k h_order_integrable h_top_integrable

/--
Oracle for the expected value of the best `ℓ` consumed items among `q` recommendations
of a single type.

This file intentionally keeps order statistics abstract. It is the right interface for
Theorem 1 of the paper: later files can instantiate this oracle for finite-discrete,
bounded, exponential-tail, or heavy-tail conditional item-value distributions.
-/
abbrev TopKValueOracle (T : ℕ) :=
  AppliedModelingLib.Probability.TopKExpectationOracle (ItemType T)

namespace TopKValueOracle

/--
Top-`k` value oracle induced by a common scalar value function `h`.

This matches the i.i.d. conditional-value setup in Theorem 1: conditional on
any type, the expected top-`k` value depends only on the number of items of that
type, not on the type label itself.
-/
def common (T : ℕ) (h : ℕ → ℝ) : TopKValueOracle T where
  expectedTopSum :=
    (AppliedModelingLib.Probability.TopKExpectationOracle.common (ItemType T) h).expectedTopSum

@[simp] theorem common_expectedTopSum
    (T : ℕ) (h : ℕ → ℝ) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (TopKValueOracle.common T h).expectedTopSum k t q = h q := rfl

/--
Top-`k` value oracle induced by paper Definition 3's order-statistic means.
This is the formal Proposition 5 interface: linearity of expectation is
represented by supplying the expected order-statistic means `μ`.
-/
noncomputable def ofOrderStatisticMean (T : ℕ) (μ : ℕ → ℕ → ℝ) : TopKValueOracle T where
  expectedTopSum :=
    (AppliedModelingLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle
      (ItemType T) μ).expectedTopSum

@[simp] theorem ofOrderStatisticMean_expectedTopSum
    (T : ℕ) (μ : ℕ → ℕ → ℝ) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (TopKValueOracle.ofOrderStatisticMean T μ).expectedTopSum k t q =
      orderStatisticTopKSumFromMean μ k q := rfl

/-- Build a consumption model for a fixed consumption constraint `ℓ`. -/
def toConsumptionModel {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun t q => O.expectedTopSum ℓ t q

/-- Marginal top-`ℓ` value from adding one more recommendation of type `t`. -/
def marginalTopK {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) (t : ItemType T) (q : ℕ) : ℝ :=
  O.expectedTopSum ℓ t (q + 1) - O.expectedTopSum ℓ t q

/-- Diminishing returns for a fixed consumption level `ℓ`. -/
def HasDiminishingReturnsAt {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) : Prop :=
  ∀ t q, marginalTopK O ℓ t (q + 1) ≤ marginalTopK O ℓ t q

/-- Nonnegative marginal top-`ℓ` value for every type and count. -/
def HasNonnegativeMarginalsAt {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) : Prop :=
  ∀ t q, 0 ≤ marginalTopK O ℓ t q

@[simp] theorem toConsumptionModel_objective {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ)
    (a : CountAllocation T) :
    (O.toConsumptionModel likelihood ℓ).objective a =
      AppliedModelingLib.Allocation.objective a likelihood (fun t q => O.expectedTopSum ℓ t q) := rfl

@[simp] theorem marginalTopK_apply {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) (t : ItemType T) (q : ℕ) :
    marginalTopK O ℓ t q = O.expectedTopSum ℓ t (q + 1) - O.expectedTopSum ℓ t q := rfl

/-- A top-`k` oracle with nonnegative marginals yields a consumption model with nonnegative marginals. -/
theorem toConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ)
    (h : O.HasNonnegativeMarginalsAt ℓ) :
    (O.toConsumptionModel likelihood ℓ).HasNonnegativeMarginals := by
  intro t q
  exact h t q

/-- A top-`k` oracle with diminishing marginals yields a consumption model with diminishing returns. -/
theorem toConsumptionModel_has_diminishing_returns {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ)
    (h : O.HasDiminishingReturnsAt ℓ) :
    (O.toConsumptionModel likelihood ℓ).HasDiminishingReturns := by
  intro t q
  exact h t q

end TopKValueOracle
end PRPKG24AccuracyDiversity
