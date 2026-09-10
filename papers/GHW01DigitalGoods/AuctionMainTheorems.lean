import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.FairCoin
import AppliedModelingLib.Foundations.Math.FiniteRanking
import AppliedModelingLib.Foundations.Math.PositiveDenominator
import AppliedModelingLib.MechanismDesign.Auctions.DigitalGoods
import AppliedModelingLib.MechanismDesign.Auctions.Position
import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Sets
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open ProbabilityTheory

/-!
# Paper-Facing Theorems: Auction Test-of-Time Tracks

This file is the public theorem interface for the current auction-theory
formalization work around SIGecom Test-of-Time papers:

- the 2021 digital-goods/prior-free-auction paper,
- the 2018 GSP/position-auction paper series,
- the 2017 combinatorial-auction paper.

The full approximation/equilibrium theorems remain future work; this file
exposes the closed unconditional theorem surface now available.
-/

namespace AppliedModelingLib
namespace Auction

/-! ## 1) Paper-Facing Definitions: 2021 Digital Goods -/

/-- Paper Definition: The revenue of a digital goods auction outcome.
    $\sum_{i \in \text{winners}} p_i$
-/
noncomputable def paper_digital_goods_revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment values i

theorem paper_digital_goods_revenue_eq {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) :
    paper_digital_goods_revenue M values = M.revenue values := by
  rfl

/-- Paper Definition: Dominant Strategy Truthful (DSIC).
    $v_i x_i(v_i, b_{-i}) - p_i(v_i, b_{-i}) \ge v_i x_i(b_i, b_{-i}) - p_i(b_i, b_{-i})$
-/
def paper_digital_goods_truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

theorem paper_digital_goods_truthful_eq {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) :
    paper_digital_goods_truthful M ↔ M.TruthfulDominantStrategy := by
  rfl

/-- Paper Definition: Two-winner Fixed Price Benchmark $\mathcal{F}^{(2)}(v)$.
    The maximum revenue obtainable from a single price that sells to at least two bidders.
-/
noncomputable def paper_two_winner_benchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  twoWinnerFixedPriceBenchmarkValue values

theorem paper_two_winner_benchmark_eq {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) :
    paper_two_winner_benchmark values = twoWinnerFixedPriceBenchmarkValue values := by
  rfl

/-! ## 2) 2021 Digital Goods Theorems -/

/--
Posted-price digital-goods auctions are dominant-strategy truthful.
-/
theorem paper_posted_price_truthful
    {Agent : Type*} [DecidableEq Agent] (price : Agent → ℝ) :
    paper_digital_goods_truthful (postedPrice price) := by
  rw [paper_digital_goods_truthful_eq]
  exact postedPrice_truthful price

/--
Posted-price digital-goods auctions are individually rational.
-/
theorem paper_posted_price_individually_rational
    {Agent : Type*} (price : Agent → ℝ) :
    (postedPrice price).IndividuallyRational := by
  exact postedPrice_individuallyRational price

/--
Posted-price digital-goods auctions have no positive transfers when all prices
are nonnegative.
-/
theorem paper_posted_price_no_positive_transfers
    {Agent : Type*} (price : Agent → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    (postedPrice price).NoPositiveTransfers := by
  exact postedPrice_noPositiveTransfers price hprice

/--
For a fixed anonymous posted price, digital-goods auction revenue is the
single-price revenue benchmark expression.
-/
theorem paper_posted_price_revenue_eq_single_price
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) (p : ℝ) :
    (postedPrice fun _ : Agent => p).revenue values =
      singlePriceRevenue values p := by
  exact postedPrice_const_revenue_eq_singlePriceRevenue values p

/--
Own-bid-independent threshold-price digital-goods auctions are
dominant-strategy truthful.
-/
theorem paper_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hind : OwnBidIndependent threshold) :
    paper_digital_goods_truthful (thresholdPriceAuction threshold) := by
  rw [paper_digital_goods_truthful_eq]
  exact thresholdPriceAuction_truthful threshold hind

/--
If a digital-goods offer price is computed after erasing the bidder's own bid,
the resulting threshold-price auction is dominant-strategy truthful.
-/
theorem paper_own_erased_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    paper_digital_goods_truthful (thresholdPriceAuction (ownErasedThreshold priceRule)) := by
  rw [paper_digital_goods_truthful_eq]
  exact ownErasedThresholdPriceAuction_truthful priceRule

/--
RSOP-style deterministic skeleton: for any fixed sample partition, offering each
bidder the finite candidate price computed from the opposite side is
dominant-strategy truthful.
-/
theorem paper_cross_sample_candidate_threshold_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    paper_digital_goods_truthful (thresholdPriceAuction (crossSampleCandidateThreshold side minWinners)) := by
  rw [paper_digital_goods_truthful_eq]
  exact crossSampleCandidateThresholdPriceAuction_truthful side minWinners

/--
RSOP-style deterministic skeleton with nonnegative offer prices: for any fixed
sample partition, offering each bidder the finite candidate offer price computed
from the opposite side is dominant-strategy truthful.
-/
theorem paper_cross_sample_candidate_offer_threshold_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    paper_digital_goods_truthful (thresholdPriceAuction (crossSampleCandidateOfferThreshold side minWinners)) := by
  rw [paper_digital_goods_truthful_eq]
  exact crossSampleCandidateOfferThresholdPriceAuction_truthful side minWinners

/--
The deterministic cross-sample offer auction has no positive transfers.
-/
theorem paper_cross_sample_candidate_offer_no_positive_transfers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateOfferThreshold side minWinners)).NoPositiveTransfers := by
  exact crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
    side minWinners

/--
Uniform average revenue over all deterministic cross-sample offer partitions is
nonnegative.
-/
theorem paper_average_cross_sample_candidate_offer_revenue_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ averageCrossSampleCandidateOfferRevenue values minWinners := by
  exact averageCrossSampleCandidateOfferRevenue_nonneg values minWinners

/--
Paper-facing RSOP approximation seam: once the finite probabilistic
approximation certificate is proved, the cross-sample offer auction is
competitive against the two-winner fixed-price benchmark.
-/
theorem paper_cross_sample_offer_competitive_of_certificate
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (ratio : ℝ)
    (hcert : CrossSampleOfferApproximationCertificate values ratio) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      ratio * averageCrossSampleCandidateOfferRevenue values 2 := by
  exact crossSampleOffer_competitive_of_certificate values ratio hcert

/--
GHW Theorem 6.2 probability-combination step. If the random sample is good
with probability at least `1 - epsSample`, and the revenue comparison is good
with probability at least `1 - epsRevenue`, then their conjunction has
probability at least `1 - epsSample - epsRevenue`; any target event implied by
that conjunction inherits the same lower bound.
-/
theorem paper_theorem6_2_random_sampling_union_bound
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω)
    (sampleGood revenueGood target : Ω → Prop)
    [DecidablePred sampleGood] [DecidablePred revenueGood] [DecidablePred target]
    {epsSample epsRevenue : ℝ}
    (hsample : 1 - epsSample ≤ pmfProb μ sampleGood)
    (hrevenue : 1 - epsRevenue ≤ pmfProb μ revenueGood)
    (himp : ∀ ω, sampleGood ω → revenueGood ω → target ω) :
    1 - epsSample - epsRevenue ≤ pmfProb μ target := by
  have hinter :
      1 - epsSample - epsRevenue ≤
        pmfProb μ (fun ω => sampleGood ω ∧ revenueGood ω) :=
    pmfProb_inter_ge_one_sub_add μ sampleGood revenueGood hsample hrevenue
  have hmono :
      pmfProb μ (fun ω => sampleGood ω ∧ revenueGood ω) ≤ pmfProb μ target :=
    pmfProb_le_of_imp μ (fun ω => sampleGood ω ∧ revenueGood ω) target
      (by
        intro ω h
        exact himp ω h.1 h.2)
  exact le_trans hinter hmono

/--
GHW Theorem 6.2 measure-theoretic probability-combination step. This is the
same union-bound endpoint as `paper_theorem6_2_random_sampling_union_bound`,
but for product measures such as independent fair half-sampling.
-/
theorem paper_theorem6_2_random_sampling_measure_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sampleGood revenueGood target : Set Ω)
    (hsample_meas : MeasurableSet sampleGood)
    (hrevenue_meas : MeasurableSet revenueGood)
    {epsSample epsRevenue : ℝ}
    (hsample : 1 - epsSample ≤ μ.real sampleGood)
    (hrevenue : 1 - epsRevenue ≤ μ.real revenueGood)
    (himp : sampleGood ∩ revenueGood ⊆ target) :
    1 - epsSample - epsRevenue ≤ μ.real target := by
  have hinter :
      1 - epsSample - epsRevenue ≤ μ.real (sampleGood ∩ revenueGood) :=
    FairCoin.measureReal_inter_ge_one_sub_add μ hsample_meas hrevenue_meas
      hsample hrevenue
  have hmono :
      μ.real (sampleGood ∩ revenueGood) ≤ μ.real target :=
    measureReal_mono (μ := μ) himp (measure_ne_top μ target)
  exact le_trans hinter hmono

/--
GHW Theorem 6.2 deterministic sample step: if at least `minWinners` bidders
on the chosen sample side accept price `p`, then the restricted sample
benchmark is at least the sampled-winner revenue at `p`.
-/
theorem paper_theorem6_2_sample_benchmark_from_sampled_winners
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hcount : minWinners ≤ sideSaleCount side keep values p) :
    (sideSaleCount side keep values p : ℝ) * p ≤
      finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners := by
  exact sideSaleCount_mul_price_le_finiteCandidateBenchmark_restrictBidsBySide
    side keep values hmin hp hcount

/--
GHW Theorem 6.2 deterministic sample-good implication: if a sample side
contains at least a third of the original winners at price `p`, the original
single-price revenue at `p` is at most three times the sample benchmark.
-/
theorem paper_theorem6_2_original_revenue_le_three_sample_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hcount_min : minWinners ≤ sideSaleCount side keep values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side keep values p) :
    singlePriceRevenue values p ≤
      3 * finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners := by
  exact singlePriceRevenue_le_three_finiteCandidateBenchmark_restrictBidsBySide
    side keep values hmin hp hcount_min hthird

/--
GHW Theorem 6.2 deterministic revenue step: the cross-sample offer auction
earns at least the opposite-side posted-price revenue at the price selected
from the sample.
-/
theorem paper_theorem6_2_cross_sample_revenue_from_opposite_side
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (minWinners : ℕ) :
    sidePriceRevenue side (!keep) values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side keep values) minWinners) ≤
      (thresholdPriceAuction
        (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
  exact sidePriceRevenue_opposite_finiteCandidateOfferPrice_le_crossSampleRevenue
    side keep values minWinners

/--
GHW Theorem 6.2 deterministic revenue-good implication: if at the
sample-selected price the non-sample side has at least half as many acceptors
as the sample side, then cross-sample auction revenue is at least half of the
sample benchmark.
-/
theorem paper_theorem6_2_sample_benchmark_le_two_cross_sample_revenue
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) (minWinners : ℕ)
    (hhalf :
      sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)) :
    finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side keep values) minWinners ≤
      2 *
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
  exact finiteCandidateBenchmark_restrictBidsBySide_le_two_crossSampleRevenue
    side keep values minWinners hhalf

/--
GHW Theorem 6.2 deterministic endpoint. If the sample contains at least one
third of the winners for a feasible fixed price `p`, and the non-sample side
contains at least half as many winners at the sample-selected offer price, then
the fixed-price revenue at `p` is at most six times the cross-sample auction
revenue.
-/
theorem paper_theorem6_2_deterministic_six_revenue_bound
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hcount_min : minWinners ≤ sideSaleCount side keep values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side keep values p)
    (hhalf :
      sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)) :
    singlePriceRevenue values p ≤
      6 *
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
  have hsample :
      singlePriceRevenue values p ≤
        3 * finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners :=
    singlePriceRevenue_le_three_finiteCandidateBenchmark_restrictBidsBySide
      side keep values hmin hp hcount_min hthird
  have hrevenue :
      finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners ≤
        2 *
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values :=
    finiteCandidateBenchmark_restrictBidsBySide_le_two_crossSampleRevenue
      side keep values minWinners hhalf
  calc
    singlePriceRevenue values p
        ≤ 3 * finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side keep values) minWinners := hsample
    _ ≤ 3 *
          (2 *
            (thresholdPriceAuction
              (crossSampleCandidateOfferThreshold side minWinners)).revenue values) := by
        exact mul_le_mul_of_nonneg_left hrevenue (by norm_num)
    _ = 6 *
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
        ring

/--
GHW Theorem 6.2 deterministic endpoint with the feasibility count discharged
from the paper's large-market condition. If the fixed price has at least
`3 * minWinners` buyers, then the one-third sample-good event already implies
the sample benchmark is feasible.
-/
theorem paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hlarge : 3 * minWinners ≤ saleCount values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side keep values p)
    (hhalf :
      sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)) :
    singlePriceRevenue values p ≤
      6 *
        (thresholdPriceAuction
          (crossSampleCandidateOfferThreshold side minWinners)).revenue values := by
  have hcount_min : minWinners ≤ sideSaleCount side keep values p := by
    omega
  exact paper_theorem6_2_deterministic_six_revenue_bound
    side keep values hmin hp hcount_min hthird hhalf

/--
GHW Theorem 6.2 concentration auxiliary for independent half-sampling. For
independent `[0,1]` indicators with mean `1/2`, the probability that the
observed count on a finite set is at most one third of that set is bounded by
the centered Hoeffding exponential. This is the independent-sampling analogue
of the paper's Lemma 6.1 tail step.
-/
theorem paper_aux_theorem6_2_half_mean_indicator_lower_tail
    {Ω Index : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Index → Ω → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset Index}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean_neg :
      ∀ i ∈ s, (∫ ω, (-X i ω) ∂μ) = -(1 / 2 : ℝ)) :
    μ.real
        {ω | (∑ i ∈ s, X i ω) ≤ (s.card : ℝ) / 3} ≤
      Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  exact FairCoin.measure_sum_half_mean_indicator_le_third_le_exp
    μ h_indep h_meas h_bound hmean_neg

/--
GHW Theorem 6.2 half-sampling instance. Under the product fair-coin measure on
sample assignments, the probability that a fixed finite set contributes at
most one third of its elements to a chosen side is bounded by the same
Hoeffding endpoint. This is the independent-coin analogue of the paper's
Lemma 6.1 sampling estimate.
-/
theorem paper_aux_theorem6_2_fair_coin_lower_tail
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  exact FairCoin.indicator_lower_tail_le_exp s keep

/--
GHW Lemma 6.1-style relaxed half-sampling endpoint for independent fair
coins. This is stated with the paper's `exp(-|S|/36)` constant; the reusable
library proof establishes the slightly stronger Hoeffding exponent first.
-/
theorem paper_aux_theorem6_2_fair_coin_lower_tail_relaxed
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := by
  exact FairCoin.indicator_lower_tail_le_exp_card_relaxed s keep

/--
Paper-facing independent fair-coin model for the Lemma 6.1 sampling estimate.
-/
structure PaperLemma61FairCoinModel (Index : Type*) where
  sampleSet : Finset Index
  keep : Bool

/--
GHW Lemma 6.1 independent fair-coin paper-model form. A fixed bidder set has
at most `exp(-|S|/36)` probability of contributing at most one third of its
members to a chosen fair-coin side.
-/
theorem paper_lemma6_1_fair_coin_lower_tail_of_model
    {Index : Type*} (model : PaperLemma61FairCoinModel Index) :
    (FairCoin.productMeasure Index).real
        {side |
          (∑ i ∈ model.sampleSet,
            if side i = model.keep then (1 : ℝ) else 0) ≤
          (model.sampleSet.card : ℝ) / 3} ≤
      Real.exp (-(model.sampleSet.card : ℝ) / 36) := by
  exact paper_aux_theorem6_2_fair_coin_lower_tail_relaxed
    model.sampleSet model.keep

/--
GHW Theorem 6.2 sample-good probability bridge. Fix a posted price `p` and
look at the bidders who would buy at that price. Under independent fair
half-sampling, the event that fewer than one third of those winners land on a
chosen side is contained in the fair-coin lower-tail event.
-/
theorem paper_aux_theorem6_2_side_sale_bad_sample_le_exp
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) (keep : Bool) :
    (FairCoin.productMeasure Agent).real
        {side | ¬ saleCount values p ≤ 3 * sideSaleCount side keep values p} ≤
      Real.exp (-(saleCount values p : ℝ) / 36) := by
  classical
  haveI : IsProbabilityMeasure (FairCoin.productMeasure Agent) :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  have htail :
      (FairCoin.productMeasure Agent).real
          {side | (∑ i ∈ winners, if side i = keep then (1 : ℝ) else 0) ≤
            (winners.card : ℝ) / 3} ≤
        Real.exp (-(winners.card : ℝ) / 36) := by
    exact FairCoin.indicator_lower_tail_le_exp_card_relaxed winners keep
  refine le_trans ?_ (by simpa [winners, saleCount] using htail)
  refine measureReal_mono (μ := FairCoin.productMeasure Agent) ?_ (measure_ne_top _ _)
  intro side hbad
  have hbad_nat :
      3 * sideSaleCount side keep values p < saleCount values p :=
    Nat.lt_of_not_ge hbad
  have hbad_real :
      (3 * sideSaleCount side keep values p : ℝ) < (saleCount values p : ℝ) := by
    exact_mod_cast hbad_nat
  have hside_card :
      (winners.filter fun i => side i = keep).card =
        sideSaleCount side keep values p := by
    unfold sideSaleCount
    congr 1
    ext i
    simp [winners, and_comm]
  have hwinners_card : winners.card = saleCount values p := by
    simp [winners, saleCount]
  have htarget :
      ((winners.filter fun i => side i = keep).card : ℝ) ≤
        (winners.card : ℝ) / 3 := by
    rw [hside_card, hwinners_card]
    nlinarith
  simpa [winners] using htarget

/--
GHW Theorem 6.2 sample-good probability bound for a fixed optimal price. If
`saleCount values p` bidders buy at price `p`, then independent fair
half-sampling puts enough of those bidders on a chosen side to satisfy
`saleCount <= 3 * sideSaleCount` with probability at least
`1 - exp(-saleCount/36)`.
-/
theorem paper_aux_theorem6_2_side_sale_sample_good_probability
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) (keep : Bool) :
    1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
      (FairCoin.productMeasure Agent).real
        {side | saleCount values p ≤ 3 * sideSaleCount side keep values p} := by
  classical
  haveI : IsProbabilityMeasure (FairCoin.productMeasure Agent) :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let good : Set (Agent → Bool) :=
    {side | saleCount values p ≤ 3 * sideSaleCount side keep values p}
  have hgood_meas : MeasurableSet good :=
    (Set.toFinite good).measurableSet
  have hbad :
      (FairCoin.productMeasure Agent).real goodᶜ ≤
        Real.exp (-(saleCount values p : ℝ) / 36) := by
    have hbad_lt :
        (FairCoin.productMeasure Agent).real
            {side | 3 * sideSaleCount side keep values p < saleCount values p} ≤
          Real.exp (-(saleCount values p : ℝ) / 36) := by
      simpa using
        paper_aux_theorem6_2_side_sale_bad_sample_le_exp values p keep
    have hcompl :
        goodᶜ =
          {side | 3 * sideSaleCount side keep values p < saleCount values p} := by
      ext side
      simp [good, not_le]
    simpa [hcompl] using hbad_lt
  have hcompl :
      (FairCoin.productMeasure Agent).real goodᶜ =
        1 - (FairCoin.productMeasure Agent).real good :=
    probReal_compl_eq_one_sub (μ := FairCoin.productMeasure Agent) hgood_meas
  linarith

/--
GHW Theorem 6.2 fixed-price revenue-good tail. For a fixed price `p`, the
probability that the chosen side has more than twice as many acceptors as the
opposite side is bounded by the same underrepresentation estimate applied to
the opposite side.
-/
theorem paper_aux_theorem6_2_fixed_price_revenue_bad_le_exp
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) (keep : Bool) :
    (FairCoin.productMeasure Agent).real
        {side | ¬ sideSaleCount side keep values p ≤
          2 * sideSaleCount side (!keep) values p} ≤
      Real.exp (-(saleCount values p : ℝ) / 36) := by
  classical
  haveI : IsProbabilityMeasure (FairCoin.productMeasure Agent) :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  have htail :
      (FairCoin.productMeasure Agent).real
          {side | ¬ saleCount values p ≤
            3 * sideSaleCount side (!keep) values p} ≤
        Real.exp (-(saleCount values p : ℝ) / 36) :=
    paper_aux_theorem6_2_side_sale_bad_sample_le_exp values p (!keep)
  refine le_trans ?_ htail
  refine measureReal_mono (μ := FairCoin.productMeasure Agent) ?_ (measure_ne_top _ _)
  intro side hbad hcount
  exact hbad
    (sideSaleCount_le_two_not_of_saleCount_le_three_not
      side keep values p hcount)

/--
GHW Theorem 6.2 fixed-price revenue-good probability. For a fixed price `p`,
the opposite side has at least half as many acceptors as the chosen side with
probability at least `1 - exp(-saleCount/36)`.
-/
theorem paper_aux_theorem6_2_fixed_price_revenue_good_probability
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) (keep : Bool) :
    1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
      (FairCoin.productMeasure Agent).real
        {side | sideSaleCount side keep values p ≤
          2 * sideSaleCount side (!keep) values p} := by
  classical
  haveI : IsProbabilityMeasure (FairCoin.productMeasure Agent) :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let good : Set (Agent → Bool) :=
    {side | sideSaleCount side keep values p ≤
      2 * sideSaleCount side (!keep) values p}
  have hgood_meas : MeasurableSet good :=
    (Set.toFinite good).measurableSet
  have hbad :
      (FairCoin.productMeasure Agent).real goodᶜ ≤
        Real.exp (-(saleCount values p : ℝ) / 36) := by
    have hbad_lt :
        (FairCoin.productMeasure Agent).real
            {side | 2 * sideSaleCount side (!keep) values p <
              sideSaleCount side keep values p} ≤
          Real.exp (-(saleCount values p : ℝ) / 36) :=
      by simpa using
        paper_aux_theorem6_2_fixed_price_revenue_bad_le_exp values p keep
    have hcompl :
        goodᶜ =
          {side | 2 * sideSaleCount side (!keep) values p <
            sideSaleCount side keep values p} := by
      ext side
      simp [good, not_le]
    simpa [hcompl] using hbad_lt
  have hcompl :
      (FairCoin.productMeasure Agent).real goodᶜ =
        1 - (FairCoin.productMeasure Agent).real good :=
    probReal_compl_eq_one_sub (μ := FairCoin.productMeasure Agent) hgood_meas
  linarith

/--
GHW Theorem 6.2 revenue-good probability, finite candidate-price union form.
The sample-selected offer price always lies in `{0} ∪ {bidder values}`, so the
probability that the selected price is revenue-bad is at most the sum of the
fixed-price bad probabilities over that finite candidate set.
-/
theorem paper_aux_theorem6_2_revenue_good_probability_by_candidate_union
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) (minWinners : ℕ) :
    1 -
        (∑ q ∈ finiteCandidatePriceSet values,
          Real.exp (-(saleCount values q : ℝ) / 36)) ≤
      (FairCoin.productMeasure Agent).real
        {side |
          sideSaleCount side keep values
              (finiteCandidateOfferPrice
                (restrictBidsBySide side keep values) minWinners) ≤
            2 * sideSaleCount side (!keep) values
              (finiteCandidateOfferPrice
                (restrictBidsBySide side keep values) minWinners)} := by
  classical
  let μ : Measure (Agent → Bool) := FairCoin.productMeasure Agent
  haveI : IsProbabilityMeasure μ :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let prices : Finset ℝ := finiteCandidatePriceSet values
  let good : Set (Agent → Bool) :=
    {side |
      sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)}
  have hbad_subset :
      {side : Agent → Bool | side ∈ goodᶜ} ⊆
        {side |
          ∃ q ∈ prices,
            ¬ sideSaleCount side keep values q ≤
              2 * sideSaleCount side (!keep) values q} := by
    intro side hside
    let q :=
      finiteCandidateOfferPrice
        (restrictBidsBySide side keep values) minWinners
    refine ⟨q, ?_, ?_⟩
    · simpa [prices, q] using
        finiteCandidateOfferPrice_restrictBidsBySide_mem_priceSet
          side keep values minWinners
    · simpa [good, q] using hside
  have hbad_le_union :
      μ.real goodᶜ ≤
        μ.real
          {side |
            ∃ q ∈ prices,
              ¬ sideSaleCount side keep values q ≤
                2 * sideSaleCount side (!keep) values q} :=
    measureReal_mono (μ := μ) hbad_subset (measure_ne_top μ _)
  have hunion :
      μ.real
          {side |
            ∃ q ∈ prices,
              ¬ sideSaleCount side keep values q ≤
                2 * sideSaleCount side (!keep) values q} ≤
        ∑ q ∈ prices,
          μ.real
            {side |
              ¬ sideSaleCount side keep values q ≤
                2 * sideSaleCount side (!keep) values q} := by
    have hset :
        {side : Agent → Bool |
          ∃ q ∈ prices,
            ¬ sideSaleCount side keep values q ≤
              2 * sideSaleCount side (!keep) values q} =
          ⋃ q ∈ prices,
            {side : Agent → Bool |
              ¬ sideSaleCount side keep values q ≤
                2 * sideSaleCount side (!keep) values q} := by
      ext side
      simp
    rw [hset]
    exact measureReal_biUnion_finset_le
      (μ := μ) (s := prices)
      (f := fun q =>
        {side : Agent → Bool |
          ¬ sideSaleCount side keep values q ≤
            2 * sideSaleCount side (!keep) values q})
  have hterms :
      (∑ q ∈ prices,
          μ.real
            {side |
              ¬ sideSaleCount side keep values q ≤
                2 * sideSaleCount side (!keep) values q}) ≤
        ∑ q ∈ prices,
          Real.exp (-(saleCount values q : ℝ) / 36) := by
    refine Finset.sum_le_sum ?_
    intro q _hq
    simpa [μ] using
      paper_aux_theorem6_2_fixed_price_revenue_bad_le_exp
        (Agent := Agent) values q keep
  have hbad :
      μ.real goodᶜ ≤
        ∑ q ∈ prices,
          Real.exp (-(saleCount values q : ℝ) / 36) := by
    exact le_trans hbad_le_union (le_trans hunion hterms)
  have hgood_meas : MeasurableSet good :=
    (Set.toFinite good).measurableSet
  have hcompl :
      μ.real goodᶜ = 1 - μ.real good :=
    probReal_compl_eq_one_sub (μ := μ) hgood_meas
  have hresult :
      1 -
          (∑ q ∈ prices,
            Real.exp (-(saleCount values q : ℝ) / 36)) ≤
        μ.real good := by
    linarith
  simpa [μ, prices, good] using hresult

/--
GHW Theorem 6.2 selected-price bad event, top-prefix reduction.  If the
sample-selected price has at least `a/3` sample acceptors and is revenue-bad
(fewer than half as many acceptors on the opposite side), then some top prefix
of size at least `a/2` is underrepresented on the opposite side.

This is the paper's `ks`, `kn`, `i = (3/2)ks` step, with integer division
handled by taking `min n ((3*ks)/2)`.
-/
theorem paper_aux_theorem6_2_selected_price_bad_large_sample_subset_top_prefix_union
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) (minWinners a : ℕ)
    (top : TopPrefixFamily values)
    (ha_card : a ≤ Fintype.card Agent) :
    {side : Agent → Bool |
      a ≤
        3 * sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ∧
      ¬ sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)} ⊆
      {side : Agent → Bool |
        ∃ m ∈ Finset.Icc (a / 2) (Fintype.card Agent),
          (sideCountInSet side (!keep) (top.top m) : ℝ) ≤
            ((top.top m).card : ℝ) / 3} := by
  classical
  intro side hside
  rcases hside with ⟨hlarge, hbad⟩
  let q : ℝ :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side keep values) minWinners
  let ks : ℕ := sideSaleCount side keep values q
  let kn : ℕ := sideSaleCount side (!keep) values q
  let m : ℕ := min (Fintype.card Agent) ((3 * ks) / 2)
  have hbad_lt : 2 * kn < ks := by
    exact Nat.lt_of_not_ge (by simpa [ks, kn, q] using hbad)
  have hsum :
      ks + kn = saleCount values q := by
    simpa [ks, kn] using sideSaleCount_add_not_eq_saleCount side keep values q
  have hsale_le_floor :
      saleCount values q ≤ (3 * ks) / 2 := by
    rw [← hsum]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
  have hsale_le_card : saleCount values q ≤ Fintype.card Agent :=
    saleCount_le_card values q
  have hm_upper : m ≤ Fintype.card Agent := by
    exact min_le_left _ _
  have hm_le_floor : m ≤ (3 * ks) / 2 := by
    exact min_le_right _ _
  have hsale_le_m : saleCount values q ≤ m := by
    exact le_min hsale_le_card hsale_le_floor
  have hhalf_le_card : a / 2 ≤ Fintype.card Agent :=
    le_trans (Nat.div_le_self a 2) ha_card
  have hhalf_le_floor : a / 2 ≤ (3 * ks) / 2 := by
    exact Nat.div_le_div_right (by simpa [ks, q] using hlarge)
  have hm_lower : a / 2 ≤ m := by
    exact le_min hhalf_le_card hhalf_le_floor
  refine ⟨m, Finset.mem_Icc.mpr ⟨hm_lower, hm_upper⟩, ?_⟩
  have hwinner_subset :
      ((Finset.univ : Finset Agent).filter fun i => q ≤ values i) ⊆
        top.top m :=
    top.threshold_subset hsale_le_m hm_upper
  have hks_le_top :
      ks ≤ sideCountInSet side keep (top.top m) := by
    simpa [ks] using
      sideSaleCount_le_sideCountInSet_of_winner_subset
        side keep values q hwinner_subset
  have htop_card : (top.top m).card = m :=
    top.card_top hm_upper
  have hsplit :
      sideCountInSet side keep (top.top m) +
          sideCountInSet side (!keep) (top.top m) =
        (top.top m).card :=
    sideCountInSet_add_not_eq_card side keep (top.top m)
  have hfloor_twice : 2 * ((3 * ks) / 2) ≤ 3 * ks := by
    have h := Nat.div_mul_le_self (3 * ks) 2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hm_twice : 2 * m ≤ 3 * ks :=
    le_trans (Nat.mul_le_mul_left 2 hm_le_floor) hfloor_twice
  have hnot_nat :
      3 * sideCountInSet side (!keep) (top.top m) ≤
        (top.top m).card := by
    rw [htop_card] at hsplit ⊢
    omega
  have hnot_real :
      (sideCountInSet side (!keep) (top.top m) : ℝ) ≤
        ((top.top m).card : ℝ) / 3 := by
    have hcast :
        (3 * sideCountInSet side (!keep) (top.top m) : ℝ) ≤
          ((top.top m).card : ℝ) := by
      exact_mod_cast hnot_nat
    nlinarith
  exact hnot_real

/--
GHW Theorem 6.2 selected-price bad probability, finite top-prefix union form.
The preceding deterministic reduction plus Hoeffding's lower-tail bound gives
a sum over top prefixes indexed by `m ≥ a/2`.
-/
theorem paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_union
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) (minWinners a : ℕ)
    (top : TopPrefixFamily values)
    (ha_card : a ≤ Fintype.card Agent) :
    (FairCoin.productMeasure Agent).real
      {side : Agent → Bool |
        a ≤
          3 * sideSaleCount side keep values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners) ∧
        ¬ sideSaleCount side keep values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners) ≤
          2 * sideSaleCount side (!keep) values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners)} ≤
      ∑ m ∈ Finset.Icc (a / 2) (Fintype.card Agent),
        Real.exp (-(m : ℝ) / 36) := by
  classical
  let μ : Measure (Agent → Bool) := FairCoin.productMeasure Agent
  haveI : IsProbabilityMeasure μ :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let badLarge : Set (Agent → Bool) :=
    {side : Agent → Bool |
      a ≤
        3 * sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ∧
      ¬ sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)}
  let indices : Finset ℕ := Finset.Icc (a / 2) (Fintype.card Agent)
  let prefixBad : ℕ → Set (Agent → Bool) :=
    fun m =>
      {side : Agent → Bool |
        (sideCountInSet side (!keep) (top.top m) : ℝ) ≤
          ((top.top m).card : ℝ) / 3}
  have hsubset :
      badLarge ⊆ {side : Agent → Bool | ∃ m ∈ indices, side ∈ prefixBad m} := by
    simpa [badLarge, indices, prefixBad] using
      paper_aux_theorem6_2_selected_price_bad_large_sample_subset_top_prefix_union
        values keep minWinners a top ha_card
  have hbad_le_union :
      μ.real badLarge ≤
        μ.real {side : Agent → Bool | ∃ m ∈ indices, side ∈ prefixBad m} :=
    measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
  have hunion :
      μ.real {side : Agent → Bool | ∃ m ∈ indices, side ∈ prefixBad m} ≤
        ∑ m ∈ indices, μ.real (prefixBad m) := by
    have hset :
        {side : Agent → Bool | ∃ m ∈ indices, side ∈ prefixBad m} =
          ⋃ m ∈ indices, prefixBad m := by
      ext side
      simp [prefixBad]
    rw [hset]
    exact measureReal_biUnion_finset_le
      (μ := μ) (s := indices) (f := prefixBad)
  have hterms :
      (∑ m ∈ indices, μ.real (prefixBad m)) ≤
        ∑ m ∈ indices, Real.exp (-(m : ℝ) / 36) := by
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm_upper : m ≤ Fintype.card Agent := (Finset.mem_Icc.mp hm).2
    have hcard : (top.top m).card = m := top.card_top hm_upper
    have htail :=
      FairCoin.indicator_lower_tail_le_exp_card_relaxed
        (ι := Agent) (top.top m) (!keep)
    simpa [μ, prefixBad, sideCountInSet_eq_sum_indicator, hcard] using htail
  exact le_trans hbad_le_union (le_trans hunion hterms)

/--
Numerical constant used in the GHW Theorem 6.2 top-prefix geometric tail.
The estimates use only `1 + x ≤ exp x` and `1 + x ≤ exp x` at a negative
argument to avoid relying on decimal approximations.
-/
private theorem paper_aux_theorem6_2_geometric_tail_factor_le_forty :
    ((1 - Real.exp (-(1:ℝ) / 36))⁻¹) * Real.exp ((1:ℝ) / 72) ≤ 40 := by
  let r : ℝ := Real.exp (-(1:ℝ) / 36)
  have hr_lt_one : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hr_le : r ≤ (36:ℝ) / 37 := by
    have hbase : (37:ℝ) / 36 ≤ Real.exp ((1:ℝ) / 36) := by
      have h := Real.add_one_le_exp ((1:ℝ) / 36)
      norm_num at h ⊢
      linarith
    have hdiv :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 37 / 36) hbase
    have hrewrite : (1:ℝ) / Real.exp ((1:ℝ) / 36) = r := by
      rw [one_div, ← Real.exp_neg]
      norm_num [r]
    have htarget : (1:ℝ) / ((37:ℝ) / 36) = (36:ℝ) / 37 := by
      norm_num
    rw [hrewrite, htarget] at hdiv
    exact hdiv
  have hden_ge : (1:ℝ) / 37 ≤ 1 - r := by
    linarith
  have hinv_le : (1 - r)⁻¹ ≤ (37:ℝ) := by
    have hdiv :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 / 37) hden_ge
    simpa [one_div] using hdiv
  have hexp_le : Real.exp ((1:ℝ) / 72) ≤ (72:ℝ) / 71 := by
    have hbase : (1:ℝ) - (1:ℝ) / 72 ≤ Real.exp (-(1:ℝ) / 72) := by
      have h := Real.add_one_le_exp (-(1:ℝ) / 72)
      linarith
    have hdiv :=
      one_div_le_one_div_of_le
        (by norm_num : (0:ℝ) < 1 - (1:ℝ) / 72) hbase
    have hrewrite :
        (1:ℝ) / Real.exp (-(1:ℝ) / 72) = Real.exp ((1:ℝ) / 72) := by
      rw [one_div, ← Real.exp_neg]
      norm_num
    have htarget : (1:ℝ) / (1 - (1:ℝ) / 72) = (72:ℝ) / 71 := by
      norm_num
    rw [hrewrite, htarget] at hdiv
    exact hdiv
  have hmul :
      (1 - r)⁻¹ * Real.exp ((1:ℝ) / 72) ≤ 37 * ((72:ℝ) / 71) := by
    exact mul_le_mul hinv_le hexp_le (by positivity) (by positivity)
  have hnum : 37 * ((72:ℝ) / 71) ≤ 40 := by
    norm_num
  exact le_trans (by simpa [r] using hmul) hnum

/--
GHW Theorem 6.2 geometric top-prefix tail. Summing the paper's
`exp(-m/36)` lower-tail bounds over all prefixes of size `m ≥ a/2` gives the
displayed `40 * exp(-a/72)` term.
-/
theorem paper_aux_theorem6_2_top_prefix_exp_sum_le_forty
    (a n : ℕ) :
    (∑ m ∈ Finset.Icc (a / 2) n, Real.exp (-(m : ℝ) / 36)) ≤
      40 * Real.exp (-(a : ℝ) / 72) := by
  classical
  let L : ℕ := a / 2
  let r : ℝ := Real.exp (-(1:ℝ) / 36)
  have hr_nonneg : 0 ≤ r := le_of_lt (by positivity)
  have hr_lt_one : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hterm : ∀ k : ℕ,
      Real.exp (-(((L + k : ℕ) : ℝ)) / 36) =
        Real.exp (-(L : ℝ) / 36) * r ^ k := by
    intro k
    have harg : -(((L + k : ℕ) : ℝ)) / 36 =
        -(L : ℝ) / 36 + (k : ℝ) * (-(1:ℝ) / 36) := by
      norm_num [Nat.cast_add]
      ring
    calc
      Real.exp (-(((L + k : ℕ) : ℝ)) / 36)
          =
            Real.exp
              (-(L : ℝ) / 36 + (k : ℝ) * (-(1:ℝ) / 36)) := by
            rw [harg]
      _ = Real.exp (-(L : ℝ) / 36) *
            Real.exp ((k : ℝ) * (-(1:ℝ) / 36)) := by
            rw [Real.exp_add]
      _ = Real.exp (-(L : ℝ) / 36) * r ^ k := by
            rw [Real.exp_nat_mul]
  have hsummable_tail :
      Summable fun k : ℕ => Real.exp (-(((L + k : ℕ) : ℝ)) / 36) := by
    have hgeo : Summable fun k : ℕ => r ^ k :=
      summable_geometric_of_lt_one hr_nonneg hr_lt_one
    exact
      (hgeo.mul_left (Real.exp (-(L : ℝ) / 36))).congr
        (fun k => by rw [hterm])
  have hIcc : Finset.Icc L n = Finset.Ico L (n + 1) := by
    ext m
    simp
  have hsum_eq :
      (∑ m ∈ Finset.Icc L n, Real.exp (-(m : ℝ) / 36)) =
        ∑ k ∈ Finset.range (n + 1 - L),
          Real.exp (-(((L + k : ℕ) : ℝ)) / 36) := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hfinite_le_tsum :
      (∑ k ∈ Finset.range (n + 1 - L),
          Real.exp (-(((L + k : ℕ) : ℝ)) / 36)) ≤
        ∑' k : ℕ, Real.exp (-(((L + k : ℕ) : ℝ)) / 36) := by
    exact
      Summable.sum_le_tsum (s := Finset.range (n + 1 - L))
        (f := fun k : ℕ => Real.exp (-(((L + k : ℕ) : ℝ)) / 36))
        (fun _k _hk => by positivity) hsummable_tail
  have htail_eq :
      (∑' k : ℕ, Real.exp (-(((L + k : ℕ) : ℝ)) / 36)) =
        Real.exp (-(L : ℝ) / 36) * (1 - r)⁻¹ := by
    calc
      (∑' k : ℕ, Real.exp (-(((L + k : ℕ) : ℝ)) / 36))
          = ∑' k : ℕ, Real.exp (-(L : ℝ) / 36) * r ^ k := by
            exact tsum_congr hterm
      _ = Real.exp (-(L : ℝ) / 36) * (∑' k : ℕ, r ^ k) := by
            rw [tsum_mul_left]
      _ = Real.exp (-(L : ℝ) / 36) * (1 - r)⁻¹ := by
            rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
  have hnat_floor : a ≤ 2 * L + 1 := by
    dsimp [L]
    omega
  have hreal_floor : (a : ℝ) ≤ 2 * (L : ℝ) + 1 := by
    exact_mod_cast hnat_floor
  have harg_floor :
      -(L : ℝ) / 36 ≤ -(a : ℝ) / 72 + (1 : ℝ) / 72 := by
    nlinarith
  have hfloor_exp :
      Real.exp (-(L : ℝ) / 36) ≤
        Real.exp (-(a : ℝ) / 72) * Real.exp ((1:ℝ) / 72) := by
    have h := Real.exp_le_exp.mpr harg_floor
    simpa [Real.exp_add] using h
  have hden_pos : 0 < 1 - r := by
    linarith
  have hinv_nonneg : 0 ≤ (1 - r)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hden_pos)
  have hfactor : (1 - r)⁻¹ * Real.exp ((1:ℝ) / 72) ≤ 40 := by
    simpa [r] using paper_aux_theorem6_2_geometric_tail_factor_le_forty
  calc
    (∑ m ∈ Finset.Icc (a / 2) n, Real.exp (-(m : ℝ) / 36))
        = (∑ m ∈ Finset.Icc L n, Real.exp (-(m : ℝ) / 36)) := by
          simp [L]
    _ = ∑ k ∈ Finset.range (n + 1 - L),
          Real.exp (-(((L + k : ℕ) : ℝ)) / 36) := hsum_eq
    _ ≤ ∑' k : ℕ, Real.exp (-(((L + k : ℕ) : ℝ)) / 36) :=
          hfinite_le_tsum
    _ = Real.exp (-(L : ℝ) / 36) * (1 - r)⁻¹ := htail_eq
    _ ≤ (Real.exp (-(a : ℝ) / 72) * Real.exp ((1:ℝ) / 72)) *
          (1 - r)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hfloor_exp hinv_nonneg
    _ = Real.exp (-(a : ℝ) / 72) *
          ((1 - r)⁻¹ * Real.exp ((1:ℝ) / 72)) := by
          ring
    _ ≤ Real.exp (-(a : ℝ) / 72) * 40 := by
          exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 40 * Real.exp (-(a : ℝ) / 72) := by
          ring

/--
GHW Theorem 6.2 selected-price bad probability, paper constant form. If the
sample-selected price has at least `a/3` sample acceptors, the probability
that it is revenue-bad is at most `40 * exp(-a/72)`.
-/
theorem paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) (minWinners a : ℕ)
    (top : TopPrefixFamily values)
    (ha_card : a ≤ Fintype.card Agent) :
    (FairCoin.productMeasure Agent).real
      {side : Agent → Bool |
        a ≤
          3 * sideSaleCount side keep values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners) ∧
        ¬ sideSaleCount side keep values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners) ≤
          2 * sideSaleCount side (!keep) values
            (finiteCandidateOfferPrice
              (restrictBidsBySide side keep values) minWinners)} ≤
      40 * Real.exp (-(a : ℝ) / 72) := by
  exact le_trans
    (paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_union
      values keep minWinners a top ha_card)
    (paper_aux_theorem6_2_top_prefix_exp_sum_le_forty
      a (Fintype.card Agent))

/--
GHW Theorem 6.2 alpha/h bridge for the sample-selected price. If all values
are at most `h`, `alpha * h` is at most the fixed-price revenue at `p`, and
the random sample is good at `p`, then the offer price selected from the sample
has at least `alpha / 3` sample acceptors.
-/
theorem paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners a : ℕ} {p h : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (ha_sale : a ≤ saleCount values p)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side keep values p) :
    a ≤
      3 * sideSaleCount side keep values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side keep values) minWinners) := by
  classical
  let q : ℝ :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side keep values) minWinners
  let sampleBenchmark : ℝ :=
    finiteCandidateFixedPriceBenchmark
      (restrictBidsBySide side keep values) minWinners
  have hlarge : 3 * minWinners ≤ saleCount values p :=
    le_trans hminWinners_alpha ha_sale
  have hcount_min : minWinners ≤ sideSaleCount side keep values p := by
    omega
  have hfixed_le_sample :
      singlePriceRevenue values p ≤ 3 * sampleBenchmark := by
    simpa [sampleBenchmark] using
      paper_theorem6_2_original_revenue_le_three_sample_benchmark
        side keep values hmin hp hcount_min hthird
  have hsample_le_count :
      sampleBenchmark ≤
        (sideSaleCount side keep values q : ℝ) * h := by
    simpa [sampleBenchmark, q] using
      finiteCandidateFixedPriceBenchmark_restrictBidsBySide_le_sideSaleCount_mul_bound
        side keep values minWinners (le_of_lt hh_pos) hvalue_bound
  have halpha_le_sample :
      (a : ℝ) * h ≤
        3 * ((sideSaleCount side keep values q : ℝ) * h) := by
    nlinarith
  have halpha_real :
      (a : ℝ) ≤ 3 * (sideSaleCount side keep values q : ℝ) := by
    have hmul :
        (a : ℝ) * h ≤
          (3 * (sideSaleCount side keep values q : ℝ)) * h := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using halpha_le_sample
    exact (mul_le_mul_iff_of_pos_right hh_pos).mp hmul
  exact_mod_cast halpha_real

/-! A real-parameter version of the selected-offer bridge.  The surrounding
finite tail argument still uses the natural count `⌈alpha⌉`; this lemma keeps
the source scale condition real until that final integerization step. -/
theorem paper_aux_theorem6_2_selected_offer_large_sample_count_of_real_alpha_h
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {alpha p h : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (halpha_sale : alpha ≤ saleCount values p)
    (hlarge_real : 3 * (minWinners : ℝ) ≤ saleCount values p)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : alpha * h ≤ singlePriceRevenue values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side keep values p) :
    alpha ≤
      3 * sideSaleCount side keep values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side keep values) minWinners) := by
  classical
  let q : ℝ :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side keep values) minWinners
  let sampleBenchmark : ℝ :=
    finiteCandidateFixedPriceBenchmark
      (restrictBidsBySide side keep values) minWinners
  have hlarge : 3 * minWinners ≤ saleCount values p := by
    exact_mod_cast hlarge_real
  have hcount_min : minWinners ≤ sideSaleCount side keep values p := by
    omega
  have hfixed_le_sample :
      singlePriceRevenue values p ≤ 3 * sampleBenchmark := by
    simpa [sampleBenchmark] using
      paper_theorem6_2_original_revenue_le_three_sample_benchmark
        side keep values hmin hp hcount_min hthird
  have hsample_le_count :
      sampleBenchmark ≤
        (sideSaleCount side keep values q : ℝ) * h := by
    simpa [sampleBenchmark, q] using
      finiteCandidateFixedPriceBenchmark_restrictBidsBySide_le_sideSaleCount_mul_bound
        side keep values minWinners (le_of_lt hh_pos) hvalue_bound
  have halpha_le_sample :
      alpha * h ≤
        3 * ((sideSaleCount side keep values q : ℝ) * h) := by
    nlinarith
  have halpha_real :
      alpha ≤ 3 * (sideSaleCount side keep values q : ℝ) := by
    have hmul :
        alpha * h ≤
          (3 * (sideSaleCount side keep values q : ℝ)) * h := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using halpha_le_sample
    exact (mul_le_mul_iff_of_pos_right hh_pos).mp hmul
  simpa [q] using halpha_real

/--
GHW Theorem 6.2, paper-constant fair-coin sampling guarantee from the
selected-price large-sample bridge.

Paper statement: assuming `alpha * h <= F`, the random sampling optimal
threshold auction revenue `R` satisfies
`R >= F / 6` with probability at least
`1 - exp(-alpha/36) - 40 * exp(-alpha/72)`.

This Lean wrapper isolates the part of `alpha * h <= F` used by the Section 6
proof as two explicit finite hypotheses: `a <= saleCount values p`, and the
bridge saying that every sample-good partition makes the sample-selected price
have at least `a/3` sample acceptors. The reusable theorem above discharges the
paper's top-prefix union and geometric tail bound.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_top_prefix_of_selected_large
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) {minWinners a : ℕ} {p : ℝ}
    (top : TopPrefixFamily values)
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (ha_sale : a ≤ saleCount values p)
    (hselected_large :
      ∀ side : Agent → Bool,
        saleCount values p ≤ 3 * sideSaleCount side keep values p →
          a ≤
            3 * sideSaleCount side keep values
              (finiteCandidateOfferPrice
                (restrictBidsBySide side keep values) minWinners)) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure Agent).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  classical
  let μ : Measure (Agent → Bool) := FairCoin.productMeasure Agent
  haveI : IsProbabilityMeasure μ :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let sampleGood : Set (Agent → Bool) :=
    {side | saleCount values p ≤ 3 * sideSaleCount side keep values p}
  let badLarge : Set (Agent → Bool) :=
    {side : Agent → Bool |
      a ≤
        3 * sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ∧
      ¬ sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)}
  let target : Set (Agent → Bool) :=
    {side |
      singlePriceRevenue values p ≤
        6 *
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values}
  have hsample_sale :
      1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
        μ.real sampleGood := by
    simpa [μ, sampleGood] using
      paper_aux_theorem6_2_side_sale_sample_good_probability values p keep
  have harg_sample :
      -(saleCount values p : ℝ) / 36 ≤ -(a : ℝ) / 36 := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      exact_mod_cast ha_sale
    nlinarith
  have hexp_sample :
      Real.exp (-(saleCount values p : ℝ) / 36) ≤
        Real.exp (-(a : ℝ) / 36) :=
    Real.exp_le_exp.mpr harg_sample
  have hsample :
      1 - Real.exp (-(a : ℝ) / 36) ≤ μ.real sampleGood := by
    have hleft :
        1 - Real.exp (-(a : ℝ) / 36) ≤
          1 - Real.exp (-(saleCount values p : ℝ) / 36) := by
      linarith
    exact le_trans hleft hsample_sale
  have ha_card : a ≤ Fintype.card Agent :=
    le_trans ha_sale (saleCount_le_card values p)
  have hbad_le :
      μ.real badLarge ≤ 40 * Real.exp (-(a : ℝ) / 72) := by
    simpa [μ, badLarge] using
      paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp
        values keep minWinners a top ha_card
  have hbad_meas : MeasurableSet badLarge :=
    (Set.toFinite badLarge).measurableSet
  have hnot_bad_meas : MeasurableSet badLargeᶜ :=
    (Set.toFinite badLargeᶜ).measurableSet
  have hbad_compl :
      μ.real badLargeᶜ = 1 - μ.real badLarge :=
    probReal_compl_eq_one_sub (μ := μ) hbad_meas
  have hnot_bad :
      1 - 40 * Real.exp (-(a : ℝ) / 72) ≤ μ.real badLargeᶜ := by
    rw [hbad_compl]
    linarith
  have hsample_meas : MeasurableSet sampleGood :=
    (Set.toFinite sampleGood).measurableSet
  have hlarge : 3 * minWinners ≤ saleCount values p :=
    le_trans hminWinners_alpha ha_sale
  have hcombined :
      1 - Real.exp (-(a : ℝ) / 36) -
          40 * Real.exp (-(a : ℝ) / 72) ≤ μ.real target :=
    paper_theorem6_2_random_sampling_measure_union_bound
      (μ := μ) sampleGood badLargeᶜ target
      hsample_meas hnot_bad_meas hsample hnot_bad
      (by
        intro side hside
        rcases hside with ⟨hsample_side, hnot_bad_side⟩
        have hselected_count :
            a ≤
              3 * sideSaleCount side keep values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) :=
          hselected_large side hsample_side
        have hrevenue_good :
            sideSaleCount side keep values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) ≤
              2 * sideSaleCount side (!keep) values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) := by
          by_contra hbad
          exact hnot_bad_side ⟨hselected_count, hbad⟩
        exact
          paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count
            side keep values hmin hp hlarge hsample_side hrevenue_good)
  simpa [μ, target] using hcombined

/--
GHW Theorem 6.2, alpha/h paper form for the fair-coin random-sampling
auction. If all bids are at most `h` and `alpha * h` is at most the fixed-price
revenue at `p`, then the random cross-sample auction earns at least one sixth
of that fixed-price revenue with probability at least
`1 - exp(-alpha/36) - 40 * exp(-alpha/72)`.

The theorem is stated for an abstract `TopPrefixFamily`; this is the exact
paper object "the top `i` bids" used in the Section 6 union bound.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) {minWinners a : ℕ} {p h : ℝ}
    (top : TopPrefixFamily values)
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure Agent).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  classical
  have hfixed_le_count_h :
      singlePriceRevenue values p ≤ (saleCount values p : ℝ) * h :=
    singlePriceRevenue_le_saleCount_mul_bound values hp hvalue_bound
  have ha_sale : a ≤ saleCount values p := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      have hmul :
          (a : ℝ) * h ≤ (saleCount values p : ℝ) * h :=
        le_trans halpha_h hfixed_le_count_h
      exact (mul_le_mul_iff_of_pos_right hh_pos).mp hmul
    exact_mod_cast ha_real
  exact
    paper_theorem6_2_fair_coin_revenue_bound_top_prefix_of_selected_large
      (values := values) (keep := keep) (minWinners := minWinners)
      (a := a) (p := p) top hmin hp hminWinners_alpha ha_sale
      (fun side hthird =>
        paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h
          side keep values hmin hp hh_pos hminWinners_alpha ha_sale
          hvalue_bound halpha_h hthird)

/--
GHW Theorem 6.2, closed sorted-bid version. This is the same alpha/h theorem
with the paper's "top `i` bids" object instantiated by sorted `Fin n` indices.
The bid vector is assumed to be indexed in nonincreasing order.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_sorted
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {minWinners a : ℕ} {p h : ℝ}
    (hmono : ∀ i j : Fin n, i.val ≤ j.val → values j ≤ values i)
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  exact
    paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h
      (values := values) (keep := keep) (minWinners := minWinners)
      (a := a) (p := p) (h := h)
      (finSortedTopPrefixFamily values hmono)
      hmin hp hh_pos hminWinners_alpha hvalue_bound halpha_h

/--
Ranked top-prefix family for an arbitrary finite bid vector. It avoids a
source-level sorted-index convention by taking the top `m` bidders to be the
upper ranked block under `FiniteRanking`.
-/
noncomputable def rankedTopPrefixFamily {n : ℕ} (values : Fin n → ℝ) :
    TopPrefixFamily values where
  top m :=
    FiniteRanking.upperRankFinset
      (s := (Finset.univ : Finset (Fin n))) (value := values)
      (by simp : (Finset.univ : Finset (Fin n)).card = n) (n - m)
  card_top := by
    intro m hm
    have hm' : m ≤ n := by
      simpa [Fintype.card_fin] using hm
    rw [FiniteRanking.upperRankFinset_card]
    rw [min_eq_right (Nat.sub_le n m)]
    exact Nat.sub_sub_self hm'
  threshold_subset := by
    intro p m hsale hm i hi
    let topSet : Finset (Fin n) :=
      FiniteRanking.upperRankFinset
        (s := (Finset.univ : Finset (Fin n))) (value := values)
        (by simp : (Finset.univ : Finset (Fin n)).card = n) (n - m)
    let lowerSet : Finset (Fin n) :=
      FiniteRanking.lowerRankFinset
        (s := (Finset.univ : Finset (Fin n))) (value := values)
        (by simp : (Finset.univ : Finset (Fin n)).card = n) (n - m)
    change i ∈ topSet
    have hm' : m ≤ n := by
      simpa [Fintype.card_fin] using hm
    have htop_card : topSet.card = m := by
      dsimp [topSet]
      rw [FiniteRanking.upperRankFinset_card]
      rw [min_eq_right (Nat.sub_le n m)]
      exact Nat.sub_sub_self hm'
    by_contra hnot_top
    have hi_win : p ≤ values i := (Finset.mem_filter.mp hi).2
    have hi_lower : i ∈ lowerSet := by
      by_contra hnot_lower
      have hi_top : i ∈ topSet := by
        dsimp [topSet]
        rw [FiniteRanking.upperRankFinset_eq_sdiff_lowerRankFinset]
        exact Finset.mem_sdiff.mpr
          ⟨by simp, by simpa [lowerSet] using hnot_lower⟩
      exact hnot_top hi_top
    let winners : Finset (Fin n) :=
      (Finset.univ : Finset (Fin n)).filter fun j => p ≤ values j
    have htop_subset : topSet ⊆ winners := by
      intro j hjtop
      have hjupper :
          j ∈
            FiniteRanking.upperRankFinset
              (s := (Finset.univ : Finset (Fin n))) (value := values)
              (by simp : (Finset.univ : Finset (Fin n)).card = n) (n - m) := by
        simpa [topSet] using hjtop
      have hilower :
          i ∈
            FiniteRanking.lowerRankFinset
              (s := (Finset.univ : Finset (Fin n))) (value := values)
              (by simp : (Finset.univ : Finset (Fin n)).card = n) (n - m) := by
        simpa [lowerSet] using hi_lower
      have hv : values i ≤ values j :=
        FiniteRanking.lowerRank_value_le_upperRank_value
          (s := (Finset.univ : Finset (Fin n))) (value := values)
          (by simp : (Finset.univ : Finset (Fin n)).card = n)
          (n - m) j hjupper i hilower
      exact Finset.mem_filter.mpr ⟨by simp, le_trans hi_win hv⟩
    have hi_winner : i ∈ winners :=
      Finset.mem_filter.mpr ⟨by simp, hi_win⟩
    have hinsert_subset : insert i topSet ⊆ winners := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjtop
      · exact hi_winner
      · exact htop_subset hjtop
    have hcard_insert : (insert i topSet).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hnot_top, htop_card]
    have hcard_le : m + 1 ≤ saleCount values p := by
      have h := Finset.card_le_card hinsert_subset
      rw [hcard_insert] at h
      simpa [winners, saleCount] using h
    omega

/--
GHW Theorem 6.2, closed ranked-bid version. The top-prefix object is derived
internally from an arbitrary `Fin n` bid vector by ranking bidders, so no
sorted-index convention is required.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {minWinners a : ℕ} {p h : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  exact
    paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h
      (values := values) (keep := keep) (minWinners := minWinners)
      (a := a) (p := p) (h := h)
      (rankedTopPrefixFamily values)
      hmin hp hh_pos hminWinners_alpha hvalue_bound halpha_h

/--
Paper-facing sorted fair-coin model for GHW Theorem 6.2. This packages the
independent-half-sampling formalization of the paper's random sampling auction
with sorted bids and the `alpha * h <= F` large-market condition.
-/
structure PaperTheorem62FairCoinSortedModel (n : ℕ) [NeZero n] where
  values : Fin n → ℝ
  keep : Bool
  minWinners : ℕ
  alpha : ℕ
  price : ℝ
  highValue : ℝ
  sorted : ∀ i j : Fin n, i.val ≤ j.val → values j ≤ values i
  minWinners_pos : 1 ≤ minWinners
  price_nonneg : 0 ≤ price
  highValue_pos : 0 < highValue
  minWinners_alpha : 3 * minWinners ≤ alpha
  value_bound : ∀ i, values i ≤ highValue
  alpha_highValue_le_revenue :
    (alpha : ℝ) * highValue ≤ singlePriceRevenue values price

/--
Construct the sorted fair-coin Theorem 6.2 model from the finite candidate
fixed-price benchmark at one winner.
-/
noncomputable def
    paper_theorem6_2_fair_coin_sorted_model_of_finite_candidate_benchmark
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hsorted : ∀ i j : Fin n, i.val ≤ j.val → values j ≤ values i)
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_ge_three : 3 ≤ alpha)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    PaperTheorem62FairCoinSortedModel n where
  values := values
  keep := keep
  minWinners := 1
  alpha := alpha
  price := finiteCandidateOfferPrice values 1
  highValue := highValue
  sorted := hsorted
  minWinners_pos := by simp
  price_nonneg := finiteCandidateOfferPrice_nonneg values 1
  highValue_pos := hhigh_pos
  minWinners_alpha := by simpa using halpha_ge_three
  value_bound := hvalue_bound
  alpha_highValue_le_revenue := by
    simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
      halpha_highValue

/--
GHW Theorem 6.2 sorted fair-coin paper-model form. Under the sorted independent
half-sampling model, the cross-sample auction earns at least one sixth of the
fixed-price revenue with probability at least
`1 - exp(-alpha/36) - 40 * exp(-alpha/72)`.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_sorted_model
    {n : ℕ} [NeZero n]
    (model : PaperTheorem62FairCoinSortedModel n) :
    1 - Real.exp (-(model.alpha : ℝ) / 36) -
        40 * Real.exp (-(model.alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          singlePriceRevenue model.values model.price ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold
                  side model.minWinners)).revenue model.values} := by
  exact
    paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_sorted
      model.values model.keep model.sorted model.minWinners_pos
      model.price_nonneg model.highValue_pos model.minWinners_alpha
      model.value_bound model.alpha_highValue_le_revenue

/--
GHW Theorem 6.2 sorted finite-candidate benchmark form. The sorted model is
constructed internally from the paper large-market condition
`alpha * h <= F`.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hsorted : ∀ i j : Fin n, i.val ≤ j.val → values j ≤ values i)
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_ge_three : 3 ≤ alpha)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side 1)).revenue values} := by
  simpa [paper_theorem6_2_fair_coin_sorted_model_of_finite_candidate_benchmark,
    singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
    paper_theorem6_2_fair_coin_revenue_bound_of_sorted_model
      (paper_theorem6_2_fair_coin_sorted_model_of_finite_candidate_benchmark
        values keep hsorted hhigh_pos hvalue_bound halpha_ge_three
        halpha_highValue)

/--
GHW Theorem 6.2 ranked finite-candidate benchmark form. The top-prefix family
is ranked internally, avoiding an external sorted-bid assumption.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_ge_three : 3 ≤ alpha)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side 1)).revenue values} := by
  simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
    paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_ranked
      (values := values) (keep := keep) (minWinners := 1)
      (a := alpha) (p := finiteCandidateOfferPrice values 1)
      (h := highValue) (by simp)
      (finiteCandidateOfferPrice_nonneg values 1) hhigh_pos
      (by simpa using halpha_ge_three) hvalue_bound
      (by
        simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
          halpha_highValue)

/-- For `alpha < 3`, the displayed Theorem 6.2 probability lower bound is nonpositive. -/
theorem paper_theorem6_2_probability_bound_nonpos_of_alpha_lt_three
    {alpha : ℕ} (halpha_lt_three : alpha < 3) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤ 0 := by
  have halpha_le_two : alpha ≤ 2 := Nat.le_of_lt_succ halpha_lt_three
  have harg : (-(1 : ℝ) / 36) ≤ -(alpha : ℝ) / 72 := by
    have halpha_real : (alpha : ℝ) ≤ 2 := by exact_mod_cast halpha_le_two
    nlinarith
  have hexp_mono :
      Real.exp (-(1 : ℝ) / 36) ≤
        Real.exp (-(alpha : ℝ) / 72) :=
    Real.exp_le_exp.mpr harg
  have hbase : (35 : ℝ) / 36 ≤ Real.exp (-(1 : ℝ) / 36) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 36)
    norm_num at h ⊢
    linarith
  have hlarge :
      1 ≤ 40 * Real.exp (-(alpha : ℝ) / 72) := by
    nlinarith
  have hpos : 0 < Real.exp (-(alpha : ℝ) / 36) := Real.exp_pos _
  nlinarith

/--
GHW Theorem 6.2 ranked finite-candidate benchmark form without a separate
large-`alpha` side condition. Small `alpha` is discharged by the nonpositive
probability lower bound above, and the top-prefix family is ranked internally.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side 1)).revenue values} := by
  by_cases halpha_ge_three : 3 ≤ alpha
  · exact
      paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark_ranked
        values keep hhigh_pos hvalue_bound halpha_ge_three
        halpha_highValue
  · have halpha_lt_three : alpha < 3 := Nat.lt_of_not_ge halpha_ge_three
    exact le_trans
      (paper_theorem6_2_probability_bound_nonpos_of_alpha_lt_three
        halpha_lt_three)
      (by positivity)

/--
GHW Theorem 6.2 fair-coin sampling wrapper. For a fixed feasible price `p`,
the sample-good concentration bound and any proved lower bound on the
sample-selected revenue-good event combine to show that the cross-sample
auction earns at least one sixth of the fixed-price revenue at `p` with the
corresponding union-bound probability.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_of_revenue_good_probability
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) {minWinners : ℕ} {p epsRevenue : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hlarge : 3 * minWinners ≤ saleCount values p)
    (hrevenue :
      1 - epsRevenue ≤
        (FairCoin.productMeasure Agent).real
          {side |
            sideSaleCount side keep values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) ≤
              2 * sideSaleCount side (!keep) values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners)}) :
    1 - Real.exp (-(saleCount values p : ℝ) / 36) - epsRevenue ≤
      (FairCoin.productMeasure Agent).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  classical
  haveI : IsProbabilityMeasure (FairCoin.productMeasure Agent) :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let sampleGood : Set (Agent → Bool) :=
    {side | saleCount values p ≤ 3 * sideSaleCount side keep values p}
  let revenueGood : Set (Agent → Bool) :=
    {side |
      sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)}
  let target : Set (Agent → Bool) :=
    {side |
      singlePriceRevenue values p ≤
        6 *
          (thresholdPriceAuction
            (crossSampleCandidateOfferThreshold side minWinners)).revenue values}
  have hsample :
      1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
        (FairCoin.productMeasure Agent).real sampleGood := by
    simpa [sampleGood] using
      paper_aux_theorem6_2_side_sale_sample_good_probability values p keep
  have hsample_meas : MeasurableSet sampleGood :=
    (Set.toFinite sampleGood).measurableSet
  have hrevenue_meas : MeasurableSet revenueGood :=
    (Set.toFinite revenueGood).measurableSet
  have hrevenue' :
      1 - epsRevenue ≤ (FairCoin.productMeasure Agent).real revenueGood := by
    simpa [revenueGood] using hrevenue
  have hcombined :
      1 - Real.exp (-(saleCount values p : ℝ) / 36) - epsRevenue ≤
        (FairCoin.productMeasure Agent).real target :=
    paper_theorem6_2_random_sampling_measure_union_bound
      (μ := FairCoin.productMeasure Agent)
      sampleGood revenueGood target
      hsample_meas hrevenue_meas hsample hrevenue'
      (by
        intro side hside
        rcases hside with ⟨hsample_side, hrevenue_side⟩
        exact
          paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count
            side keep values hmin hp hlarge hsample_side hrevenue_side)
  simpa [target] using hcombined

/--
GHW Theorem 6.2 fair-coin sampling guarantee with the selected-price
revenue-good event bounded by a finite union over candidate prices. This is a
fully closed independent-half-sampling statement; replacing the candidate-price
sum by the paper's sharper top-prefix union bound gives the displayed
`40 * exp(-alpha/72)` term.
-/
theorem paper_theorem6_2_fair_coin_revenue_bound_candidate_union
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hlarge : 3 * minWinners ≤ saleCount values p) :
    1 - Real.exp (-(saleCount values p : ℝ) / 36) -
        (∑ q ∈ finiteCandidatePriceSet values,
          Real.exp (-(saleCount values q : ℝ) / 36)) ≤
      (FairCoin.productMeasure Agent).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold side minWinners)).revenue values} := by
  exact
    paper_theorem6_2_fair_coin_revenue_bound_of_revenue_good_probability
      (values := values) (keep := keep) (minWinners := minWinners) (p := p)
      (epsRevenue :=
        ∑ q ∈ finiteCandidatePriceSet values,
          Real.exp (-(saleCount values q : ℝ) / 36))
      hmin hp hlarge
      (paper_aux_theorem6_2_revenue_good_probability_by_candidate_union
        values keep minWinners)

/--
The finite bidder-value candidate benchmark is nonnegative.
-/
theorem paper_finite_candidate_fixed_price_benchmark_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := by
  exact finiteCandidateFixedPriceBenchmark_nonneg values minWinners

/--
Any feasible nonnegative fixed price with at least one required winner is
dominated by the finite bidder-value candidate benchmark.
-/
theorem paper_single_price_revenue_le_candidate_benchmark_of_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hfeasible : minWinners ≤ saleCount values p) :
    singlePriceRevenue values p ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  exact singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
    values hmin hp hfeasible

/--
If there is at least one feasible two-winner fixed price, the finite
bidder-value candidate benchmark is the `F^(2)` fixed-price benchmark.
-/
theorem paper_two_winner_fixed_price_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ)
    (hexists : ∃ p, 0 ≤ p ∧ 2 ≤ saleCount values p) :
    IsTwoWinnerFixedPriceBenchmark values
      (finiteCandidateFixedPriceBenchmark values 2) := by
  exact finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible
    values hexists

/--
GHW Theorem 4.1 dyadic-bin certificate: if a factor-two bid bin carries at
least a `1/m` share of the total multi-price value `T`, then the fixed-price
benchmark satisfies `T <= (2*m)F`. Instantiating `m = log h` and the paper's
dyadic partition gives `F >= T/(2 log h)`.
-/
theorem paper_theorem4_1_fixed_price_lower_bound_of_factor_two_bin
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {fixedPriceBenchmark totalValue binCount low : ℝ}
    {bin : Finset Agent}
    (hbenchmark : IsFixedPriceBenchmark values 1 fixedPriceBenchmark)
    (hbin_nonempty : bin.Nonempty)
    (hbinCount_nonneg : 0 ≤ binCount)
    (hlow_nonneg : 0 ≤ low)
    (hshare : totalValue ≤ binCount * (∑ i ∈ bin, values i))
    (hbin_accept : ∀ i, i ∈ bin → low ≤ values i)
    (hbin_factor_two : ∀ i, i ∈ bin → values i ≤ 2 * low) :
    totalValue ≤ (2 * binCount) * fixedPriceBenchmark := by
  exact fixedPriceBenchmark_totalValue_le_of_factor_two_bin
    values hbenchmark hbin_nonempty hbinCount_nonneg hlow_nonneg hshare
    hbin_accept hbin_factor_two

/--
GHW Theorem 4.1 partition certificate. A finite family of factor-two bins
covering total value `T` yields `T <= 2 * (#bins) * F` by averaging over bins.
The paper obtains the displayed `log h` factor by instantiating these bins with
powers-of-two value ranges.
-/
theorem paper_theorem4_1_fixed_price_lower_bound_of_factor_two_partition
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Bin] [Nonempty Bin]
    (values : Agent → ℝ) {fixedPriceBenchmark totalValue : ℝ}
    (bins : Bin → Finset Agent) (low : Bin → ℝ)
    (hbenchmark : IsFixedPriceBenchmark values 1 fixedPriceBenchmark)
    (hbins_nonempty : ∀ k, (bins k).Nonempty)
    (hlow_nonneg : ∀ k, 0 ≤ low k)
    (hcover : totalValue ≤ ∑ k : Bin, ∑ i ∈ bins k, values i)
    (hbin_accept : ∀ k i, i ∈ bins k → low k ≤ values i)
    (hbin_factor_two : ∀ k i, i ∈ bins k → values i ≤ 2 * low k) :
    totalValue ≤ (2 * (Fintype.card Bin : ℝ)) * fixedPriceBenchmark := by
  exact fixedPriceBenchmark_totalValue_le_of_factor_two_partition
    values bins low hbenchmark hbins_nonempty hlow_nonneg hcover
    hbin_accept hbin_factor_two

/--
GHW Theorem 4.1 partition certificate allowing empty factor-two bins. This is
the canonical form for power-of-two partitions, where some ranges may contain
no bids.
-/
theorem paper_theorem4_1_fixed_price_lower_bound_of_factor_two_partition_allow_empty
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Bin]
    (values : Agent → ℝ) {fixedPriceBenchmark totalValue : ℝ}
    (bins : Bin → Finset Agent) (low : Bin → ℝ)
    (hbenchmark : IsFixedPriceBenchmark values 1 fixedPriceBenchmark)
    (hlow_nonneg : ∀ k, 0 ≤ low k)
    (hcover : totalValue ≤ ∑ k : Bin, ∑ i ∈ bins k, values i)
    (hbin_accept : ∀ k i, i ∈ bins k → low k ≤ values i)
    (hbin_factor_two : ∀ k i, i ∈ bins k → values i ≤ 2 * low k) :
    totalValue ≤ (2 * (Fintype.card Bin : ℝ)) * fixedPriceBenchmark := by
  exact fixedPriceBenchmark_totalValue_le_of_factor_two_partition_allow_empty
    values bins low hbenchmark hlow_nonneg hcover hbin_accept hbin_factor_two

/--
GHW Corollary 4.2 algebra: if deleting small bids leaves truncated multi-price
value `T'` with `T <= 2T'`, and Theorem 4.1 gives `T' <= 2mF`, then
`T <= 4mF`. Instantiating `m = log n` gives the paper's displayed
`F >= T/(4 log n)` form.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_from_truncation
    {totalValue truncatedTotal fixedPriceBenchmark binCount : ℝ}
    (htruncate : totalValue ≤ 2 * truncatedTotal)
    (htruncated_bound :
      truncatedTotal ≤ (2 * binCount) * fixedPriceBenchmark) :
    totalValue ≤ (4 * binCount) * fixedPriceBenchmark := by
  nlinarith

/--
Paper-facing truncation model for GHW Corollary 4.2.
-/
structure PaperCorollary42TruncationModel where
  totalValue : ℝ
  truncatedTotal : ℝ
  fixedPriceBenchmark : ℝ
  binCount : ℝ
  truncation_loss : totalValue ≤ 2 * truncatedTotal
  truncated_bound :
    truncatedTotal ≤ (2 * binCount) * fixedPriceBenchmark

/--
GHW Corollary 4.2 paper-model form: truncation plus the bounded truncated
instance gives the displayed factor-four fixed-price bound.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_of_truncation_model
    (model : PaperCorollary42TruncationModel) :
    model.totalValue ≤
      (4 * model.binCount) * model.fixedPriceBenchmark := by
  exact
    paper_corollary4_2_fixed_price_lower_bound_from_truncation
      model.truncation_loss model.truncated_bound

/--
GHW Theorem 7.1 square-sum endpoint. The weighted-pairing proof shows
`sumSq <= 48*T*E[R]` for the active bins, while Cauchy/averaging gives
`activeTotal^2 <= binCount*sumSq` and the singleton-bin deletion gives
`T <= 2*activeTotal`. These imply `T <= 192*binCount*E[R]`, i.e.
`E[R] = Omega(T / binCount)`.
-/
theorem paper_theorem7_1_weighted_pairing_square_sum_endpoint
    {totalValue activeTotal binCount sumSq expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hbinCount_nonneg : 0 ≤ binCount)
    (hactive : totalValue ≤ 2 * activeTotal)
    (hsquare : activeTotal * activeTotal ≤ binCount * sumSq)
    (hrevenue : sumSq ≤ 48 * totalValue * expectedRevenue) :
    totalValue ≤ 192 * binCount * expectedRevenue := by
  have htotal_sq_le : totalValue * totalValue ≤ 4 * (activeTotal * activeTotal) := by
    nlinarith [sq_nonneg (2 * activeTotal - totalValue)]
  have hsq_to_sum :
      4 * (activeTotal * activeTotal) ≤ 4 * (binCount * sumSq) :=
    mul_le_mul_of_nonneg_left hsquare (by norm_num)
  have hrev_mul :
      binCount * sumSq ≤ binCount * (48 * totalValue * expectedRevenue) :=
    mul_le_mul_of_nonneg_left hrevenue hbinCount_nonneg
  have hsum_to_rev :
      4 * (binCount * sumSq) ≤
        4 * (binCount * (48 * totalValue * expectedRevenue)) :=
    mul_le_mul_of_nonneg_left hrev_mul (by norm_num)
  have hchain :
      totalValue * totalValue ≤
        4 * (binCount * (48 * totalValue * expectedRevenue)) :=
    le_trans htotal_sq_le (le_trans hsq_to_sum hsum_to_rev)
  nlinarith

/--
GHW Theorem 7.1 singleton-bin deletion algebra. If the mass deleted from
singleton bins is at most `2h`, the paper assumption `4h <= T` makes the active
multi-bid bins carry at least half of the total value.
-/
theorem paper_theorem7_1_active_total_from_singleton_loss
    {totalValue singletonTotal activeTotal h : ℝ}
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue) :
    totalValue ≤ 2 * activeTotal := by
  nlinarith

/--
GHW Theorem 7.1 finite-bin Cauchy bridge. Once the proof has reduced to active
bin masses `S_j`, Cauchy's inequality supplies
`(sum S_j)^2 <= (#bins) * sum S_j^2`; the square-sum endpoint then gives the
`192` constant.
-/
theorem paper_theorem7_1_weighted_pairing_from_bin_square_revenue
    {Bin : Type*} [Fintype Bin]
    (binMass : Bin → ℝ) {totalValue activeTotal expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hactive : totalValue ≤ 2 * activeTotal)
    (hrevenue :
      (∑ j : Bin, (binMass j) ^ 2) ≤
        48 * totalValue * expectedRevenue) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) * expectedRevenue := by
  have hsquare :
      activeTotal * activeTotal ≤
        (Fintype.card Bin : ℝ) * ∑ j : Bin, (binMass j) ^ 2 := by
    have h :=
      FiniteSum.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Bin)) binMass
    simpa [hactive_sum, Finset.card_univ, pow_two] using h
  exact
    paper_theorem7_1_weighted_pairing_square_sum_endpoint
      (totalValue := totalValue) (activeTotal := activeTotal)
      (binCount := Fintype.card Bin) (sumSq := ∑ j : Bin, (binMass j) ^ 2)
      (expectedRevenue := expectedRevenue)
      htotal_pos (by exact_mod_cast Nat.zero_le (Fintype.card Bin))
      hactive hsquare hrevenue

/--
GHW Theorem 7.1 per-bin constant algebra. The paper derives a raw lower bound
`S/(3T) * S/(2k) * (k-1)/4` for the expected revenue from an active bin with
`k >= 2`; this lemma packages the arithmetic reduction to `S^2/(48T)`.
-/
theorem paper_theorem7_1_bin_revenue_lower_bound_algebra
    {k : ℕ} {binSum totalValue binRevenue : ℝ}
    (hk : 2 ≤ k)
    (htotal_pos : 0 < totalValue)
    (hraw :
      (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
          (((k : ℝ) - 1) / 4) ≤ binRevenue) :
    binSum ^ 2 / (48 * totalValue) ≤ binRevenue := by
  have hfactor :
      (1 : ℝ) / 48 ≤ ((k : ℝ) - 1) / (24 * (k : ℝ)) := by
    have hk2 : (2 : ℝ) ≤ k := by
      exact_mod_cast hk
    field_simp [show (k : ℝ) ≠ 0 by positivity]
    nlinarith
  have hsqt_nonneg : 0 ≤ binSum ^ 2 / totalValue :=
    div_nonneg (sq_nonneg binSum) (le_of_lt htotal_pos)
  have hscaled :
      (binSum ^ 2 / totalValue) * ((1 : ℝ) / 48) ≤
        (binSum ^ 2 / totalValue) *
          (((k : ℝ) - 1) / (24 * (k : ℝ))) :=
    mul_le_mul_of_nonneg_left hfactor hsqt_nonneg
  have hraw_eq :
      (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
          (((k : ℝ) - 1) / 4) =
        (binSum ^ 2 / totalValue) *
          (((k : ℝ) - 1) / (24 * (k : ℝ))) := by
    field_simp [show totalValue ≠ 0 by positivity,
      show (k : ℝ) ≠ 0 by positivity]
    ring
  have hleft_eq :
      binSum ^ 2 / (48 * totalValue) =
        (binSum ^ 2 / totalValue) * ((1 : ℝ) / 48) := by
    field_simp [show totalValue ≠ 0 by positivity]
  rw [hleft_eq]
  exact le_trans hscaled (by simpa [hraw_eq] using hraw)

/-- Sum of rank indices over `Fin k`, cast to reals. -/
private theorem paper_aux_sum_fin_val_real (k : ℕ) :
    (∑ i : Fin k, (i.val : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hmul_nat := Finset.sum_range_id_mul_two k
  have hmul_real :
      ((∑ i ∈ Finset.range k, i : ℕ) : ℝ) * 2 =
        ((k * (k - 1) : ℕ) : ℝ) := by
    exact_mod_cast hmul_nat
  rw [Nat.cast_sum] at hmul_real
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  have htarget :
      ((k * (k - 1) : ℕ) : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) := by
    cases k <;> norm_num [Nat.succ_eq_add_one]
  rw [← htarget]
  exact hmul_real

/--
GHW Theorem 7.1 ranked double-sum bridge for one active bin. If each ranked
bidder's within-bin weighted-pairing payment contribution is at least the
paper's pointwise lower bound, then the whole bin satisfies the raw
`S/(3T) * S/(2k) * (k-1)/4` revenue lower bound.
-/
theorem paper_theorem7_1_bin_raw_lower_bound_from_ranked_pairing_payments
    {k : ℕ} (rankValue : Fin k → ℝ)
    {binSum totalValue binRevenue : ℝ}
    (hk : 2 ≤ k)
    (hpoint :
      ∀ i : Fin k,
        (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
            ((i.val : ℝ) / (2 * (k : ℝ))) ≤
          ∑ j : Fin k,
            if j.val < i.val then
              rankValue j ^ 2 / (totalValue - rankValue i)
            else 0)
    (hbinRevenue :
      (∑ i : Fin k, ∑ j : Fin k,
          if j.val < i.val then
            rankValue j ^ 2 / (totalValue - rankValue i)
          else 0) ≤ binRevenue) :
    (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
        (((k : ℝ) - 1) / 4) ≤ binRevenue := by
  let c : ℝ :=
    (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ)))
  have hsum_point :
      (∑ i : Fin k, c * ((i.val : ℝ) / (2 * (k : ℝ)))) ≤
        ∑ i : Fin k, ∑ j : Fin k,
          if j.val < i.val then
            rankValue j ^ 2 / (totalValue - rankValue i)
          else 0 := by
    exact Finset.sum_le_sum fun i _ =>
      by simpa [c] using hpoint i
  have hsum_coeff :
      (∑ i : Fin k, c * ((i.val : ℝ) / (2 * (k : ℝ)))) =
        c * (((k : ℝ) - 1) / 4) := by
    have hk_ne : (k : ℝ) ≠ 0 := by
      have hk_pos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
      exact_mod_cast ne_of_gt hk_pos
    rw [← Finset.mul_sum]
    rw [← Finset.sum_div]
    rw [paper_aux_sum_fin_val_real]
    field_simp [hk_ne]
    ring
  calc
    (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
        (((k : ℝ) - 1) / 4)
        = c * (((k : ℝ) - 1) / 4) := by rfl
    _ = ∑ i : Fin k, c * ((i.val : ℝ) / (2 * (k : ℝ))) := hsum_coeff.symm
    _ ≤ ∑ i : Fin k, ∑ j : Fin k,
          if j.val < i.val then
            rankValue j ^ 2 / (totalValue - rankValue i)
          else 0 := hsum_point
    _ ≤ binRevenue := hbinRevenue

/--
GHW Theorem 7.1 pointwise ranked-payment bound. For one ranked bidder in an
active bin, the paper proof multiplies three lower bounds: probability of a
same-bin pair, minimum bin price, and conditional probability of pairing with a
lower-ranked bidder. This lemma turns those three local inequalities into the
corresponding weighted-pairing double-sum contribution.
-/
theorem paper_theorem7_1_ranked_payment_pointwise_lower_bound
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum totalValue : ℝ}
    (i : Fin k)
    (hmin_nonneg : 0 ≤ binSum / (2 * (k : ℝ)))
    (hden_pos : 0 < totalValue - rankValue i)
    (hprice_min :
      ∀ r : Fin k,
        r.val < i.val → binSum / (2 * (k : ℝ)) ≤ rankValue r)
    (hwin_mass :
      ((i.val : ℝ) / (2 * (k : ℝ))) * (binSum - rankValue i) ≤
        ∑ r : Fin k, if r.val < i.val then rankValue r else 0)
    (hpair_prob :
      binSum / (3 * totalValue) ≤
        (binSum - rankValue i) / (totalValue - rankValue i)) :
    (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
        ((i.val : ℝ) / (2 * (k : ℝ))) ≤
      ∑ r : Fin k,
        if r.val < i.val then
          rankValue r ^ 2 / (totalValue - rankValue i)
        else 0 := by
  let m : ℝ := binSum / (2 * (k : ℝ))
  let frac : ℝ := (i.val : ℝ) / (2 * (k : ℝ))
  let den : ℝ := totalValue - rankValue i
  let lowerMass : ℝ :=
    ∑ r : Fin k, if r.val < i.val then rankValue r else 0
  have hfrac_nonneg : 0 ≤ frac := by
    dsimp [frac]
    positivity
  have hmfrac_nonneg : 0 ≤ m * frac :=
    mul_nonneg hmin_nonneg hfrac_nonneg
  have hterm_sum_le :
      (∑ r : Fin k, if r.val < i.val then m * rankValue r / den else 0) ≤
        ∑ r : Fin k,
          if r.val < i.val then
            rankValue r ^ 2 / den
          else 0 := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    by_cases hri : r < i
    · have hr_nonneg : 0 ≤ rankValue r :=
        le_trans hmin_nonneg (hprice_min r hri)
      have hmul : m * rankValue r ≤ rankValue r ^ 2 := by
        have h := mul_le_mul_of_nonneg_right (hprice_min r hri) hr_nonneg
        simpa [m, pow_two] using h
      simpa [hri] using div_le_div_of_nonneg_right hmul (le_of_lt hden_pos)
    · simp [hri]
  have hsum_eq :
      m * lowerMass / den =
        ∑ r : Fin k, if r.val < i.val then m * rankValue r / den else 0 := by
    dsimp [lowerMass]
    rw [Finset.mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    by_cases hri : r.val < i.val <;> simp [hri]
  have hmass_to_actual :
      m * lowerMass / den ≤
        ∑ r : Fin k,
          if r.val < i.val then
            rankValue r ^ 2 / den
          else 0 := by
    rw [hsum_eq]
    exact hterm_sum_le
  have hwin_scaled :
      m * (frac * (binSum - rankValue i)) / den ≤ m * lowerMass / den := by
    have hmul := mul_le_mul_of_nonneg_left hwin_mass hmin_nonneg
    exact
      div_le_div_of_nonneg_right
        (by simpa [m, frac, lowerMass, mul_assoc] using hmul)
        (le_of_lt hden_pos)
  have hpair_scaled :
      m * frac * (binSum / (3 * totalValue)) ≤
        m * frac * ((binSum - rankValue i) / den) := by
    exact mul_le_mul_of_nonneg_left hpair_prob hmfrac_nonneg
  have hmiddle_eq :
      m * (frac * (binSum - rankValue i)) / den =
        m * frac * ((binSum - rankValue i) / den) := by
    field_simp [show den ≠ 0 by exact ne_of_gt hden_pos]
  calc
    (binSum / (3 * totalValue)) * (binSum / (2 * (k : ℝ))) *
        ((i.val : ℝ) / (2 * (k : ℝ)))
        = m * frac * (binSum / (3 * totalValue)) := by ring
    _ ≤ m * frac * ((binSum - rankValue i) / den) := hpair_scaled
    _ = m * (frac * (binSum - rankValue i)) / den := hmiddle_eq.symm
    _ ≤ m * lowerMass / den := hwin_scaled
    _ ≤ ∑ r : Fin k,
          if r.val < i.val then
            rankValue r ^ 2 / den
          else 0 := hmass_to_actual
    _ = ∑ r : Fin k,
          if r.val < i.val then
            rankValue r ^ 2 / (totalValue - rankValue i)
          else 0 := by rfl

/-- Sum of a constant over the strict rank prefix below `i`. -/
private theorem paper_aux_sum_fin_rank_prefix_const
    {k : ℕ} (i : Fin k) (c : ℝ) :
    (∑ r : Fin k, if r.val < i.val then c else 0) = (i.val : ℝ) * c := by
  rw [← Finset.sum_filter]
  change (∑ r ∈ finPrefixByIndex k i.val, c) = (i.val : ℝ) * c
  rw [Finset.sum_const, finPrefixByIndex_card (Nat.le_of_lt i.isLt)]
  rw [nsmul_eq_mul]

/--
GHW Theorem 7.1 factor-two bin price floor. If a ranked bin of size `k` has
total mass `S` and every value lies between `low` and `2 low`, then
`S/(2k) <= low`. This is the paper's "smallest bid in bin `j` is at least
`S_j/(2k)`" step.
-/
theorem paper_theorem7_1_factor_two_bin_price_floor
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum low : ℝ}
    (hk_pos : 0 < k)
    (hbinSum : binSum = ∑ r : Fin k, rankValue r)
    (hupper : ∀ r : Fin k, rankValue r ≤ 2 * low) :
    binSum / (2 * (k : ℝ)) ≤ low := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hden_pos : 0 < 2 * (k : ℝ) := by positivity
  have hsum_upper :
      binSum ≤ (k : ℝ) * (2 * low) := by
    rw [hbinSum]
    calc
      (∑ r : Fin k, rankValue r)
          ≤ ∑ _r : Fin k, 2 * low := by
            exact Finset.sum_le_sum fun r _ => hupper r
      _ = (k : ℝ) * (2 * low) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul]
  rw [div_le_iff₀ hden_pos]
  nlinarith

/--
GHW Theorem 7.1 nonnegative bin price floor. This packages the nonnegativity
needed when multiplying the paper's three pointwise lower bounds.
-/
theorem paper_theorem7_1_factor_two_bin_price_floor_nonneg
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum low : ℝ}
    (hk_pos : 0 < k)
    (hbinSum : binSum = ∑ r : Fin k, rankValue r)
    (hlow_nonneg : 0 ≤ low)
    (hlower : ∀ r : Fin k, low ≤ rankValue r) :
    0 ≤ binSum / (2 * (k : ℝ)) := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hden_nonneg : 0 ≤ 2 * (k : ℝ) := by positivity
  have hbin_nonneg : 0 ≤ binSum := by
    rw [hbinSum]
    exact Finset.sum_nonneg fun r _ =>
      le_trans hlow_nonneg (hlower r)
  exact div_nonneg hbin_nonneg hden_nonneg

/--
GHW Theorem 7.1 factor-two same-bin win-mass bound. The lower ranks contribute
at least an `i/(2k)` share of the bin mass other than bidder `i`, using only the
factor-two width of the bin.
-/
theorem paper_theorem7_1_factor_two_bin_win_mass_bound
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum low : ℝ}
    (i : Fin k)
    (hk_pos : 0 < k)
    (hbinSum : binSum = ∑ r : Fin k, rankValue r)
    (hlow_nonneg : 0 ≤ low)
    (hlower : ∀ r : Fin k, low ≤ rankValue r)
    (hupper : ∀ r : Fin k, rankValue r ≤ 2 * low) :
    ((i.val : ℝ) / (2 * (k : ℝ))) * (binSum - rankValue i) ≤
      ∑ r : Fin k, if r.val < i.val then rankValue r else 0 := by
  let frac : ℝ := (i.val : ℝ) / (2 * (k : ℝ))
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hk_pos
  have hfrac_nonneg : 0 ≤ frac := by
    dsimp [frac]
    positivity
  have hprefix_low :
      (i.val : ℝ) * low ≤
        ∑ r : Fin k, if r.val < i.val then rankValue r else 0 := by
    calc
      (i.val : ℝ) * low
          = ∑ r : Fin k, if r.val < i.val then low else 0 := by
            rw [paper_aux_sum_fin_rank_prefix_const]
      _ ≤ ∑ r : Fin k, if r.val < i.val then rankValue r else 0 := by
            refine Finset.sum_le_sum ?_
            intro r _hr
            by_cases hri : r.val < i.val
            · simp [hri, hlower r]
            · simp [hri]
  have hbin_upper :
      binSum ≤ (k : ℝ) * (2 * low) := by
    rw [hbinSum]
    calc
      (∑ r : Fin k, rankValue r)
          ≤ ∑ _r : Fin k, 2 * low := by
            exact Finset.sum_le_sum fun r _ => hupper r
      _ = (k : ℝ) * (2 * low) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul]
  have hvalue_nonneg : 0 ≤ rankValue i :=
    le_trans hlow_nonneg (hlower i)
  have hother_upper : binSum - rankValue i ≤ (k : ℝ) * (2 * low) := by
    linarith
  have hscaled :
      frac * (binSum - rankValue i) ≤ (i.val : ℝ) * low := by
    calc
      frac * (binSum - rankValue i)
          ≤ frac * ((k : ℝ) * (2 * low)) :=
            mul_le_mul_of_nonneg_left hother_upper hfrac_nonneg
      _ = (i.val : ℝ) * low := by
            dsimp [frac]
            field_simp [hk_ne]
  exact le_trans hscaled hprefix_low

/--
GHW Theorem 7.1 factor-two bin one-third mass bound. In a bin with at least two
bids and factor-two width, deleting any one bid leaves at least one third of the
bin mass.
-/
theorem paper_theorem7_1_factor_two_bin_delete_one_third
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum low : ℝ}
    (i : Fin k)
    (hk : 2 ≤ k)
    (hbinSum : binSum = ∑ r : Fin k, rankValue r)
    (hlow_nonneg : 0 ≤ low)
    (hlower : ∀ r : Fin k, low ≤ rankValue r)
    (hupper : ∀ r : Fin k, rankValue r ≤ 2 * low) :
    binSum ≤ 3 * (binSum - rankValue i) := by
  let others : Finset (Fin k) := (Finset.univ : Finset (Fin k)).erase i
  have hi_mem : i ∈ (Finset.univ : Finset (Fin k)) := by simp
  have hothers_card : 1 ≤ others.card := by
    dsimp [others]
    rw [Finset.card_erase_of_mem hi_mem]
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hlow_le_others_const : low ≤ ∑ r ∈ others, low := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_real : (1 : ℝ) ≤ others.card := by exact_mod_cast hothers_card
    nlinarith
  have hothers_lower_sum :
      (∑ r ∈ others, low) ≤ ∑ r ∈ others, rankValue r := by
    exact Finset.sum_le_sum fun r _hr => hlower r
  have hlow_le_others :
      low ≤ ∑ r ∈ others, rankValue r :=
    le_trans hlow_le_others_const hothers_lower_sum
  have hvalue_le_twice_others :
      rankValue i ≤ 2 * ∑ r ∈ others, rankValue r := by
    have htwice := mul_le_mul_of_nonneg_left hlow_le_others
      (by norm_num : (0 : ℝ) ≤ 2)
    linarith [hupper i]
  have hsum_split :
      binSum = rankValue i + ∑ r ∈ others, rankValue r := by
    rw [hbinSum]
    have h :=
      Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin k))) (f := rankValue) (a := i)
        hi_mem
    linarith
  nlinarith

/--
GHW Theorem 7.1 same-bin pairing probability lower bound. This is the algebra
behind `(S_j - b_i)/(T - b_i) > S_j/(3T)` after replacing the strict paper
inequality by the closed weak inequality used in Lean.
-/
theorem paper_theorem7_1_same_bin_pair_probability_lower_bound
    {binSum totalValue value : ℝ}
    (htotal_pos : 0 < totalValue)
    (hden_pos : 0 < totalValue - value)
    (hvalue_nonneg : 0 ≤ value)
    (hbin_nonneg : 0 ≤ binSum)
    (hthird : binSum ≤ 3 * (binSum - value)) :
    binSum / (3 * totalValue) ≤
      (binSum - value) / (totalValue - value) := by
  have hother_nonneg : 0 ≤ binSum - value := by
    nlinarith
  have hto_total :
      binSum / (3 * totalValue) ≤ (binSum - value) / totalValue := by
    have hden_pos' : 0 < 3 * totalValue := by positivity
    have hdiv :=
      div_le_div_of_nonneg_right hthird (le_of_lt hden_pos')
    have hright :
        (3 * (binSum - value)) / (3 * totalValue) =
          (binSum - value) / totalValue := by
      field_simp [show totalValue ≠ 0 by exact ne_of_gt htotal_pos]
    simpa [hright] using hdiv
  have hden_le_total : totalValue - value ≤ totalValue := by
    linarith
  exact le_trans hto_total
    (div_le_div_of_nonneg_left hother_nonneg hden_pos hden_le_total)

/--
GHW Theorem 7.1 singleton-bin deletion certificate. If the singleton bins have
mass at most twice their dyadic floor and those floors sum to at most `h`, then
the total deleted singleton mass is at most `2h`.
-/
theorem paper_theorem7_1_singleton_total_le_two_h_of_floor_sum
    {SingleBin : Type*} [Fintype SingleBin]
    (singletonMass singletonFloor : SingleBin → ℝ)
    {singletonTotal h : ℝ}
    (hsingletonTotal : singletonTotal = ∑ j : SingleBin, singletonMass j)
    (hmass_floor : ∀ j : SingleBin, singletonMass j ≤ 2 * singletonFloor j)
    (hfloor_sum : (∑ j : SingleBin, singletonFloor j) ≤ h) :
    singletonTotal ≤ 2 * h := by
  rw [hsingletonTotal]
  calc
    (∑ j : SingleBin, singletonMass j)
        ≤ ∑ j : SingleBin, 2 * singletonFloor j := by
          exact Finset.sum_le_sum fun j _ => hmass_floor j
    _ = 2 * ∑ j : SingleBin, singletonFloor j := by
          rw [Finset.mul_sum]
    _ ≤ 2 * h := by
          exact mul_le_mul_of_nonneg_left hfloor_sum (by norm_num)

/--
GHW Theorem 7.1 active-bin certificate. This combines the paper's singleton-bin
deletion, per-bin raw weighted-pairing lower bounds, summation over active bins,
and Cauchy square-sum step into the final `192`-constant guarantee.
-/
theorem paper_theorem7_1_weighted_pairing_from_active_bin_certificates
    {Bin : Type*} [Fintype Bin]
    (binMass binRevenue : Bin → ℝ) (binSize : Bin → ℕ)
    {totalValue singletonTotal activeTotal h expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hraw :
      ∀ j,
        (binMass j / (3 * totalValue)) *
            (binMass j / (2 * (binSize j : ℝ))) *
              (((binSize j : ℝ) - 1) / 4) ≤ binRevenue j)
    (hrevenue_sum : (∑ j : Bin, binRevenue j) ≤ expectedRevenue) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) * expectedRevenue := by
  have hactive : totalValue ≤ 2 * activeTotal :=
    paper_theorem7_1_active_total_from_singleton_loss
      hpartition hsingleton hlarge
  have hper :
      ∀ j, binMass j ^ 2 / (48 * totalValue) ≤ binRevenue j := by
    intro j
    exact paper_theorem7_1_bin_revenue_lower_bound_algebra
      (hsize j) htotal_pos (hraw j)
  have hsum_per :
      (∑ j : Bin, binMass j ^ 2 / (48 * totalValue)) ≤
        ∑ j : Bin, binRevenue j := by
    exact Finset.sum_le_sum fun j _ => hper j
  have hsum_scaled :
      (∑ j : Bin, binMass j ^ 2) ≤
        48 * totalValue * expectedRevenue := by
    have hscale_pos : 0 < 48 * totalValue := by
      positivity
    have hscale_ne : 48 * totalValue ≠ 0 := ne_of_gt hscale_pos
    have hmul :=
      mul_le_mul_of_nonneg_left
        (le_trans hsum_per hrevenue_sum) (le_of_lt hscale_pos)
    have hleft :
        (48 * totalValue) *
            (∑ j : Bin, binMass j ^ 2 / (48 * totalValue)) =
          ∑ j : Bin, binMass j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _hj
      field_simp [hscale_ne]
    rw [← hleft]
    exact hmul
  exact
    paper_theorem7_1_weighted_pairing_from_bin_square_revenue
      binMass htotal_pos hactive_sum hactive hsum_scaled

/--
GHW Theorem 7.1 ranked-bin payment certificate. This replaces the raw per-bin
assumption in `paper_theorem7_1_weighted_pairing_from_active_bin_certificates`
by the ranked double-sum payment lower bounds that come directly from the
weighted-pairing expected-revenue formula.
-/
theorem paper_theorem7_1_weighted_pairing_from_ranked_bin_payment_certificates
    {Bin : Type*} [Fintype Bin]
    (binMass binRevenue : Bin → ℝ) (binSize : Bin → ℕ)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hpoint :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        (binMass j / (3 * totalValue)) *
            (binMass j / (2 * (binSize j : ℝ))) *
              ((i.val : ℝ) / (2 * (binSize j : ℝ))) ≤
          ∑ r : Fin (binSize j),
            if r.val < i.val then
              rankValue j r ^ 2 / (totalValue - rankValue j i)
            else 0)
    (hbinRevenue :
      ∀ j : Bin,
        (∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
          if r.val < i.val then
            rankValue j r ^ 2 / (totalValue - rankValue j i)
          else 0) ≤ binRevenue j)
    (hrevenue_sum : (∑ j : Bin, binRevenue j) ≤ expectedRevenue) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) * expectedRevenue := by
  have hraw :
      ∀ j,
        (binMass j / (3 * totalValue)) *
            (binMass j / (2 * (binSize j : ℝ))) *
              (((binSize j : ℝ) - 1) / 4) ≤ binRevenue j := by
    intro j
    exact
      paper_theorem7_1_bin_raw_lower_bound_from_ranked_pairing_payments
        (rankValue j) (hsize j) (hpoint j) (hbinRevenue j)
  exact
    paper_theorem7_1_weighted_pairing_from_active_bin_certificates
      binMass binRevenue binSize htotal_pos hpartition hsingleton hlarge
      hactive_sum hsize hraw hrevenue_sum

/--
GHW Theorem 7.1 ranked-bin structural certificate. This discharges the
pointwise payment lower-bound input of
`paper_theorem7_1_weighted_pairing_from_ranked_bin_payment_certificates` from
the three inequalities stated in the paper proof for each ranked bidder:
same-bin pairing probability, the `S_j/(2k)` minimum price lower bound, and the
conditional probability of pairing with a lower-ranked bid.
-/
theorem paper_theorem7_1_weighted_pairing_from_ranked_bin_structural_certificates
    {Bin : Type*} [Fintype Bin]
    (binMass binRevenue : Bin → ℝ) (binSize : Bin → ℕ)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hmin_nonneg :
      ∀ j : Bin, 0 ≤ binMass j / (2 * (binSize j : ℝ)))
    (hden_pos :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        0 < totalValue - rankValue j i)
    (hprice_min :
      ∀ j : Bin, ∀ i r : Fin (binSize j),
        r.val < i.val →
          binMass j / (2 * (binSize j : ℝ)) ≤ rankValue j r)
    (hwin_mass :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        ((i.val : ℝ) / (2 * (binSize j : ℝ))) *
            (binMass j - rankValue j i) ≤
          ∑ r : Fin (binSize j),
            if r.val < i.val then rankValue j r else 0)
    (hpair_prob :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        binMass j / (3 * totalValue) ≤
          (binMass j - rankValue j i) / (totalValue - rankValue j i))
    (hbinRevenue :
      ∀ j : Bin,
        (∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
          if r.val < i.val then
            rankValue j r ^ 2 / (totalValue - rankValue j i)
          else 0) ≤ binRevenue j)
    (hrevenue_sum : (∑ j : Bin, binRevenue j) ≤ expectedRevenue) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) * expectedRevenue := by
  refine
    paper_theorem7_1_weighted_pairing_from_ranked_bin_payment_certificates
      binMass binRevenue binSize rankValue htotal_pos hpartition hsingleton
      hlarge hactive_sum hsize ?_ hbinRevenue hrevenue_sum
  intro j i
  exact
    paper_theorem7_1_ranked_payment_pointwise_lower_bound
      (rankValue j) i (hmin_nonneg j) (hden_pos j i)
      (hprice_min j i) (hwin_mass j i) (hpair_prob j i)

/--
GHW Theorem 7.1 denominator positivity for a factor-two active bin. If the bin
has at least two bids, positive floor, and its mass is included in the global
total, then deleting any one bidder leaves a positive weighted-pairing
denominator.
-/
theorem paper_theorem7_1_factor_two_denominator_positive
    {k : ℕ} (rankValue : Fin k → ℝ) {binSum totalValue low : ℝ}
    (i : Fin k)
    (hk : 2 ≤ k)
    (hbin_le_total : binSum ≤ totalValue)
    (hbinSum : binSum = ∑ r : Fin k, rankValue r)
    (hlow_pos : 0 < low)
    (hlower : ∀ r : Fin k, low ≤ rankValue r) :
    0 < totalValue - rankValue i := by
  let others : Finset (Fin k) := (Finset.univ : Finset (Fin k)).erase i
  have hi_mem : i ∈ (Finset.univ : Finset (Fin k)) := by simp
  have hothers_card : 1 ≤ others.card := by
    dsimp [others]
    rw [Finset.card_erase_of_mem hi_mem]
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hlow_nonneg : 0 ≤ low := le_of_lt hlow_pos
  have hlow_le_others_const : low ≤ ∑ r ∈ others, low := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_real : (1 : ℝ) ≤ others.card := by exact_mod_cast hothers_card
    nlinarith
  have hothers_lower_sum :
      (∑ r ∈ others, low) ≤ ∑ r ∈ others, rankValue r := by
    exact Finset.sum_le_sum fun r _hr => hlower r
  have hothers_pos :
      0 < ∑ r ∈ others, rankValue r := by
    exact lt_of_lt_of_le hlow_pos
      (le_trans hlow_le_others_const hothers_lower_sum)
  have hsum_split :
      binSum = rankValue i + ∑ r ∈ others, rankValue r := by
    rw [hbinSum]
    have h :=
      Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin k))) (f := rankValue) (a := i)
        hi_mem
    linarith
  nlinarith

/--
GHW Theorem 7.1 factor-two bin certificate. This removes the pointwise
same-bin probability, price-floor, and lower-ranked win-mass assumptions from
the ranked structural certificate using only the paper's concrete active-bin
facts: every active bin has at least two bids and all bids in that bin lie in a
positive factor-two interval.
-/
theorem paper_theorem7_1_weighted_pairing_from_factor_two_bin_certificates
    {Bin : Type*} [Fintype Bin]
    (binMass binRevenue : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h expectedRevenue : ℝ}
    (htotal_pos : 0 < totalValue)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass_le_total : ∀ j : Bin, binMass j ≤ totalValue)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hbinRevenue :
      ∀ j : Bin,
        (∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
          if r.val < i.val then
            rankValue j r ^ 2 / (totalValue - rankValue j i)
          else 0) ≤ binRevenue j)
    (hrevenue_sum : (∑ j : Bin, binRevenue j) ≤ expectedRevenue) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) * expectedRevenue := by
  refine
    paper_theorem7_1_weighted_pairing_from_ranked_bin_structural_certificates
      binMass binRevenue binSize rankValue htotal_pos hpartition hsingleton
      hlarge hactive_sum hsize ?_ ?_ ?_ ?_ ?_ hbinRevenue hrevenue_sum
  · intro j
    have hk_pos : 0 < binSize j :=
      lt_of_lt_of_le (by decide : 0 < 2) (hsize j)
    exact
      paper_theorem7_1_factor_two_bin_price_floor_nonneg
        (rankValue j) hk_pos (hbinMass j) (le_of_lt (hfloor_pos j))
        (hfloor_le j)
  · intro j i
    exact
      paper_theorem7_1_factor_two_denominator_positive
        (rankValue j) i (hsize j) (hbinMass_le_total j) (hbinMass j)
        (hfloor_pos j) (hfloor_le j)
  · intro j i r _hri
    have hk_pos : 0 < binSize j :=
      lt_of_lt_of_le (by decide : 0 < 2) (hsize j)
    have hfloor_bound :
        binMass j / (2 * (binSize j : ℝ)) ≤ binFloor j :=
      paper_theorem7_1_factor_two_bin_price_floor
        (rankValue j) hk_pos (hbinMass j) (hfactor_two j)
    exact le_trans hfloor_bound (hfloor_le j r)
  · intro j i
    have hk_pos : 0 < binSize j :=
      lt_of_lt_of_le (by decide : 0 < 2) (hsize j)
    exact
      paper_theorem7_1_factor_two_bin_win_mass_bound
        (rankValue j) i hk_pos (hbinMass j) (le_of_lt (hfloor_pos j))
        (hfloor_le j) (hfactor_two j)
  · intro j i
    have hvalue_nonneg : 0 ≤ rankValue j i :=
      le_trans (le_of_lt (hfloor_pos j)) (hfloor_le j i)
    have hbin_nonneg : 0 ≤ binMass j := by
      rw [hbinMass j]
      exact Finset.sum_nonneg fun r _ =>
        le_trans (le_of_lt (hfloor_pos j)) (hfloor_le j r)
    have hden_pos :
        0 < totalValue - rankValue j i :=
      paper_theorem7_1_factor_two_denominator_positive
        (rankValue j) i (hsize j) (hbinMass_le_total j) (hbinMass j)
        (hfloor_pos j) (hfloor_le j)
    have hthird :
        binMass j ≤ 3 * (binMass j - rankValue j i) :=
      paper_theorem7_1_factor_two_bin_delete_one_third
        (rankValue j) i (hsize j) (hbinMass j)
        (le_of_lt (hfloor_pos j)) (hfloor_le j) (hfactor_two j)
    exact
      paper_theorem7_1_same_bin_pair_probability_lower_bound
        htotal_pos hden_pos hvalue_nonneg hbin_nonneg hthird

/--
GHW Theorem 7.1 ranked-bin revenue embedding. A disjoint ranked family of
within-bin lower-rank pairs contributes no more than the full weighted-pairing
expected revenue, because the weighted-pairing sum contains all accepted ordered
pairs and the proof keeps only same-bin lower-ranked pairs.
-/
theorem paper_theorem7_1_ranked_bin_double_sum_le_weighted_pairing_revenue
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Bin]
    (values : Agent → ℝ) (binSize : Bin → ℕ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i)
    (hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i) :
    (∑ j : Bin, ∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
      if r.val < i.val then
        rankValue j r ^ 2 / (totalValue - rankValue j i)
      else 0) ≤
      weightedPairingExpectedRevenue values := by
  classical
  let PairIndex := Sigma fun j : Bin => Fin (binSize j) × Fin (binSize j)
  let pairAgent : PairIndex → Agent × Agent := fun x =>
    (rankAgent x.1 x.2.1, rankAgent x.1 x.2.2)
  let keptPayment : PairIndex → ℝ := fun x =>
    if x.2.2.val < x.2.1.val then
      rankValue x.1 x.2.2 ^ 2 / (totalValue - rankValue x.1 x.2.1)
    else 0
  let fullPayment : Agent × Agent → ℝ := fun p =>
    if p.2 ≠ p.1 ∧ values p.2 ≤ values p.1 then
      values p.2 ^ 2 / (totalBidValue values - values p.1)
    else 0
  have hpair_injective : Function.Injective pairAgent := by
    intro x y hxy
    rcases x with ⟨j, ir⟩
    rcases ir with ⟨i, r⟩
    rcases y with ⟨j', ir'⟩
    rcases ir' with ⟨i', r'⟩
    simp [pairAgent] at hxy
    have hi_eq :
        Sigma.mk j i = Sigma.mk j' i' :=
      hrank_injective hxy.1
    cases hi_eq
    have hr_eq :
        Sigma.mk j r = Sigma.mk j r' :=
      hrank_injective hxy.2
    cases hr_eq
    rfl
  have hfull_nonneg : ∀ p : Agent × Agent, 0 ≤ fullPayment p := by
    intro p
    by_cases hp : p.2 ≠ p.1 ∧ values p.2 ≤ values p.1
    · simp [fullPayment, hp,
        div_nonneg (sq_nonneg (values p.2)) (le_of_lt (hden_pos_agent p.1))]
    · simp [fullPayment, hp]
  have hkept_le_full : ∀ x : PairIndex, keptPayment x ≤ fullPayment (pairAgent x) := by
    intro x
    rcases x with ⟨j, ir⟩
    rcases ir with ⟨i, r⟩
    by_cases hri : r.val < i.val
    · have hne : rankAgent j r ≠ rankAgent j i := by
        intro hsame
        have hsigma :
            Sigma.mk j r = Sigma.mk j i :=
          hrank_injective hsame
        cases hsigma
        omega
      have hle : values (rankAgent j r) ≤ values (rankAgent j i) := by
        rw [← hrankValue j r, ← hrankValue j i]
        exact hrank_mono j r i hri
      have hterm_eq :
          rankValue j r ^ 2 / (totalValue - rankValue j i) =
            values (rankAgent j r) ^ 2 /
              (totalBidValue values - values (rankAgent j i)) := by
        rw [hrankValue j r, hrankValue j i, htotal]
      have hkept_eq :
          keptPayment ⟨j, (i, r)⟩ =
            rankValue j r ^ 2 / (totalValue - rankValue j i) := by
        dsimp [keptPayment]
        exact if_pos hri
      have hfull_eq :
          fullPayment (pairAgent ⟨j, (i, r)⟩) =
            values (rankAgent j r) ^ 2 /
              (totalBidValue values - values (rankAgent j i)) := by
        simp [fullPayment, pairAgent, hne, hle]
      rw [hkept_eq, hfull_eq, hterm_eq]
    · have hkept_eq : keptPayment ⟨j, (i, r)⟩ = 0 := by
        dsimp [keptPayment]
        exact if_neg hri
      rw [hkept_eq]
      exact hfull_nonneg (rankAgent j i, rankAgent j r)
  have hsub :
      (∑ x : PairIndex, keptPayment x) ≤
        ∑ p : Agent × Agent, fullPayment p :=
    FiniteSum.sum_le_sum_of_injective_nonneg
      pairAgent hpair_injective hkept_le_full hfull_nonneg
  simpa [PairIndex, keptPayment, fullPayment, pairAgent,
    weightedPairingExpectedRevenue, weightedPairingExpectedPayment,
    Fintype.sum_sigma, Fintype.sum_prod_type] using hsub

/--
GHW Theorem 7.1 factor-two ranked-bin version for the concrete
weighted-pairing expected-revenue formula. The remaining paper-level inputs are
now the audited bin partition facts: active-bin mass accounting, singleton-bin
deletion, disjoint ranked representatives, and factor-two value ranges.
-/
theorem paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Bin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass_le_total : ∀ j : Bin, binMass j ≤ totalValue)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i)
    (hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) *
        weightedPairingExpectedRevenue values := by
  let binRevenue : Bin → ℝ := fun j =>
    ∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
      if r.val < i.val then
        rankValue j r ^ 2 / (totalValue - rankValue j i)
      else 0
  have hbinRevenue :
      ∀ j : Bin,
        (∑ i : Fin (binSize j), ∑ r : Fin (binSize j),
          if r.val < i.val then
            rankValue j r ^ 2 / (totalValue - rankValue j i)
          else 0) ≤ binRevenue j := by
    intro j
    rfl
  have hrevenue_sum :
      (∑ j : Bin, binRevenue j) ≤
        weightedPairingExpectedRevenue values := by
    dsimp [binRevenue]
    exact
      paper_theorem7_1_ranked_bin_double_sum_le_weighted_pairing_revenue
        values binSize rankAgent rankValue htotal hrankValue hrank_injective
        hrank_mono hden_pos_agent
  exact
    paper_theorem7_1_weighted_pairing_from_factor_two_bin_certificates
      binMass binRevenue binSize binFloor rankValue htotal_pos hpartition
      hsingleton hlarge hactive_sum hsize hbinMass_le_total hbinMass
      hfloor_pos hfloor_le hfactor_two hbinRevenue hrevenue_sum

/--
GHW Theorem 7.1 factor-two ranked-bin version with paper-style denominator
discharge. If `h` bounds every bid and `4h <= T` with `h > 0`, then every
weighted-pairing denominator is positive, so the concrete ranked-bin theorem
needs no separate denominator assumption.
-/
theorem paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_of_value_bound
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Bin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass_le_total : ∀ j : Bin, binMass j ≤ totalValue)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) *
        weightedPairingExpectedRevenue values := by
  have htotal_pos : 0 < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i := by
    intro i
    rw [← htotal]
    nlinarith [hvalue_le_h i]
  exact
    paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins
      values binMass binSize binFloor rankAgent rankValue htotal htotal_pos
      hpartition hsingleton hlarge hactive_sum hsize hbinMass_le_total
      hbinMass hfloor_pos hfloor_le hfactor_two hrankValue hrank_injective
      hrank_mono hden_pos_agent

/--
GHW Theorem 7.1 factor-two ranked-bin version with nonnegative bid accounting.
The hypothesis that each active-bin mass is bounded by the total follows from
the disjoint ranked embedding into the full bidder set.
-/
theorem paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_of_value_bounds
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Bin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i) :
    totalValue ≤
      192 * (Fintype.card Bin : ℝ) *
        weightedPairingExpectedRevenue values := by
  have hbinMass_le_total : ∀ j : Bin, binMass j ≤ totalValue := by
    intro j
    have hfixed_injective : Function.Injective (rankAgent j) := by
      intro i r hir
      have hsigma :
          Sigma.mk j i = Sigma.mk j r :=
        hrank_injective hir
      cases hsigma
      rfl
    have hsum_le :
        (∑ i : Fin (binSize j), rankValue j i) ≤
          ∑ a : Agent, values a := by
      exact
        FiniteSum.sum_le_sum_of_injective_nonneg
          (rankAgent j) hfixed_injective
          (by intro i; rw [hrankValue j i])
          hvalues_nonneg
    rw [hbinMass j, htotal, totalBidValue]
    exact hsum_le
  exact
    paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_of_value_bound
      values binMass binSize binFloor rankAgent rankValue htotal hh_pos
      hvalue_le_h hpartition hsingleton hlarge hactive_sum hsize
      hbinMass_le_total hbinMass hfloor_pos hfloor_le hfactor_two
      hrankValue hrank_injective hrank_mono

/--
GHW Theorem 7.1 log-bin-count wrapper. If the active factor-two ranked bins are
bounded by `logH` bins, the concrete weighted-pairing theorem yields the
paper's displayed `T <= 192 * logH * W` form.
-/
theorem paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_log_bound
    {Agent Bin : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Bin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    {totalValue singletonTotal activeTotal h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingleton : singletonTotal ≤ 2 * h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i)
    (hcard_le_logH : (Fintype.card Bin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i := by
    intro i
    rw [← htotal]
    nlinarith [hvalue_le_h i]
  have hrevenue_nonneg :
      0 ≤ weightedPairingExpectedRevenue values := by
    unfold weightedPairingExpectedRevenue weightedPairingExpectedPayment
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by
        by_cases hpair : j ≠ i ∧ values j ≤ values i
        · simp [hpair,
            div_nonneg (sq_nonneg (values j)) (le_of_lt (hden_pos_agent i))]
        · simp [hpair]
  have hcard_to_log :
      192 * (Fintype.card Bin : ℝ) *
          weightedPairingExpectedRevenue values ≤
        192 * logH * weightedPairingExpectedRevenue values := by
    have hmul :=
      mul_le_mul_of_nonneg_right hcard_le_logH hrevenue_nonneg
    nlinarith
  exact le_trans
    (paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_of_value_bounds
      values binMass binSize binFloor rankAgent rankValue htotal hvalues_nonneg
      hh_pos hvalue_le_h hpartition hsingleton hlarge hactive_sum hsize
      hbinMass hfloor_pos hfloor_le hfactor_two hrankValue hrank_injective
      hrank_mono)
    hcard_to_log

/--
GHW Theorem 7.1 log-bin-count wrapper with singleton deletion derived from
dyadic singleton floors. This matches the paper proof step
`sum singleton bins <= sum 2^j < 2h` through an explicit finite floor-sum
certificate.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_singleton_floor_sum
    {Agent Bin SingleBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Bin] [Fintype SingleBin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    (singletonMass singletonFloor : SingleBin → ℝ)
    {totalValue singletonTotal activeTotal h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition : totalValue ≤ singletonTotal + activeTotal)
    (hsingletonTotal :
      singletonTotal = ∑ j : SingleBin, singletonMass j)
    (hsingleton_floor :
      ∀ j : SingleBin, singletonMass j ≤ 2 * singletonFloor j)
    (hsingleton_floor_sum :
      (∑ j : SingleBin, singletonFloor j) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hactive_sum : activeTotal = ∑ j : Bin, binMass j)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i)
    (hcard_le_logH : (Fintype.card Bin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  have hsingleton : singletonTotal ≤ 2 * h :=
    paper_theorem7_1_singleton_total_le_two_h_of_floor_sum
      singletonMass singletonFloor hsingletonTotal hsingleton_floor
      hsingleton_floor_sum
  exact
    paper_theorem7_1_weighted_pairing_from_factor_two_ranked_bins_log_bound
      values binMass binSize binFloor rankAgent rankValue htotal hvalues_nonneg
      hh_pos hvalue_le_h hpartition hsingleton hlarge hactive_sum hsize
      hbinMass hfloor_pos hfloor_le hfactor_two hrankValue hrank_injective
      hrank_mono hcard_le_logH

/--
GHW Theorem 7.1 direct active/singleton sum wrapper. This removes the auxiliary
`singletonTotal` and `activeTotal` names: the paper's proof needs only that the
total bid value is covered by the singleton-bin mass plus the active-bin mass.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_partition_sums
    {Agent Bin SingleBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Bin] [Fintype SingleBin]
    (values : Agent → ℝ) (binMass : Bin → ℝ) (binSize : Bin → ℕ)
    (binFloor : Bin → ℝ)
    (rankAgent : ∀ j : Bin, Fin (binSize j) → Agent)
    (rankValue : ∀ j : Bin, Fin (binSize j) → ℝ)
    (singletonMass singletonFloor : SingleBin → ℝ)
    {totalValue h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition :
      totalValue ≤ (∑ j : SingleBin, singletonMass j) +
        ∑ j : Bin, binMass j)
    (hsingleton_floor :
      ∀ j : SingleBin, singletonMass j ≤ 2 * singletonFloor j)
    (hsingleton_floor_sum :
      (∑ j : SingleBin, singletonFloor j) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hsize : ∀ j, 2 ≤ binSize j)
    (hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j)
    (hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i))
    (hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2))
    (hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i)
    (hcard_le_logH : (Fintype.card Bin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  exact
    paper_theorem7_1_weighted_pairing_log_bound_of_singleton_floor_sum
      values binMass binSize binFloor rankAgent rankValue singletonMass
      singletonFloor htotal hvalues_nonneg hh_pos hvalue_le_h hpartition
      rfl hsingleton_floor hsingleton_floor_sum hlarge rfl hsize hbinMass
      hfloor_pos hfloor_le hfactor_two hrankValue hrank_injective hrank_mono
      hcard_le_logH

/--
GHW Theorem 7.1 finset-bin wrapper. This discharges the ranked-array
certificate from actual disjoint finite bins by enumerating each bin in
nondecreasing bid order with a lexicographic tie-breaker.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_finset_partition
    {Agent Bin SingleBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype Bin] [Fintype SingleBin]
    (values : Agent → ℝ) (bins : Bin → Finset Agent)
    (binFloor : Bin → ℝ) (singletonMass singletonFloor : SingleBin → ℝ)
    {totalValue h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition :
      totalValue ≤ (∑ j : SingleBin, singletonMass j) +
        ∑ j : Bin, ∑ i ∈ bins j, values i)
    (hsingleton_floor :
      ∀ j : SingleBin, singletonMass j ≤ 2 * singletonFloor j)
    (hsingleton_floor_sum :
      (∑ j : SingleBin, singletonFloor j) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hsize : ∀ j : Bin, 2 ≤ (bins j).card)
    (hfloor_pos : ∀ j : Bin, 0 < binFloor j)
    (hfloor_le :
      ∀ j : Bin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i)
    (hfactor_two :
      ∀ j : Bin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j)
    (hbins_disjoint :
      ∀ j₁ j₂ : Bin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂)
    (hcard_le_logH : (Fintype.card Bin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  classical
  let binMass : Bin → ℝ := fun j => ∑ i ∈ bins j, values i
  let binSize : Bin → ℕ := fun j => (bins j).card
  let rankAgent : ∀ j : Bin, Fin (binSize j) → Agent := fun j =>
    FiniteRanking.rankAgentByValue (s := bins j) (value := values) rfl
  let rankValue : ∀ j : Bin, Fin (binSize j) → ℝ := fun j =>
    FiniteRanking.rankValueByValue (s := bins j) (value := values) rfl
  have hbinMass :
      ∀ j : Bin, binMass j = ∑ i : Fin (binSize j), rankValue j i := by
    intro j
    dsimp [binMass, binSize, rankValue]
    exact (FiniteRanking.sum_rankValueByValue_eq_sum
      (s := bins j) (value := values) rfl).symm
  have hfloor_le_rank :
      ∀ j : Bin, ∀ i : Fin (binSize j), binFloor j ≤ rankValue j i := by
    intro j i
    have hmem :
        rankAgent j i ∈ bins j := by
      dsimp [rankAgent, binSize]
      exact FiniteRanking.rankAgentByValue_mem
        (s := bins j) (value := values) rfl i
    have hvalue :
        rankValue j i = values (rankAgent j i) := by
      dsimp [rankAgent, rankValue, binSize]
      exact FiniteRanking.rankValueByValue_eq_value
        (s := bins j) (value := values) rfl i
    rw [hvalue]
    exact hfloor_le j (rankAgent j i) hmem
  have hfactor_two_rank :
      ∀ j : Bin, ∀ i : Fin (binSize j), rankValue j i ≤ 2 * binFloor j := by
    intro j i
    have hmem :
        rankAgent j i ∈ bins j := by
      dsimp [rankAgent, binSize]
      exact FiniteRanking.rankAgentByValue_mem
        (s := bins j) (value := values) rfl i
    have hvalue :
        rankValue j i = values (rankAgent j i) := by
      dsimp [rankAgent, rankValue, binSize]
      exact FiniteRanking.rankValueByValue_eq_value
        (s := bins j) (value := values) rfl i
    rw [hvalue]
    exact hfactor_two j (rankAgent j i) hmem
  have hrankValue :
      ∀ j : Bin, ∀ i : Fin (binSize j),
        rankValue j i = values (rankAgent j i) := by
    intro j i
    dsimp [rankAgent, rankValue, binSize]
    exact FiniteRanking.rankValueByValue_eq_value
      (s := bins j) (value := values) rfl i
  have hrank_injective :
      Function.Injective
        (fun x : Sigma fun j : Bin => Fin (binSize j) =>
          rankAgent x.1 x.2) := by
    intro x y hxy
    rcases x with ⟨j, x⟩
    rcases y with ⟨j', y⟩
    have hxmem :
        rankAgent j x ∈ bins j := by
      dsimp [rankAgent, binSize]
      exact FiniteRanking.rankAgentByValue_mem
        (s := bins j) (value := values) rfl x
    have hymem :
        rankAgent j' y ∈ bins j' := by
      dsimp [rankAgent, binSize]
      exact FiniteRanking.rankAgentByValue_mem
        (s := bins j') (value := values) rfl y
    have hxmem_other : rankAgent j x ∈ bins j' := by
      simpa [hxy] using hymem
    have hj : j = j' :=
      hbins_disjoint j j' (rankAgent j x) hxmem hxmem_other
    subst j'
    have hxy_fin : x = y := by
      exact FiniteRanking.rankAgentByValue_injective
        (s := bins j) (value := values) rfl hxy
    cases hxy_fin
    rfl
  have hrank_mono :
      ∀ j : Bin, ∀ r i : Fin (binSize j),
        r.val < i.val → rankValue j r ≤ rankValue j i := by
    intro j r i hri
    dsimp [rankValue, binSize]
    exact FiniteRanking.rankValueByValue_mono
      (s := bins j) (value := values) rfl r i hri
  exact
    paper_theorem7_1_weighted_pairing_log_bound_of_partition_sums
      values binMass binSize binFloor rankAgent rankValue singletonMass
      singletonFloor htotal hvalues_nonneg hh_pos hvalue_le_h
      hpartition hsingleton_floor hsingleton_floor_sum hlarge hsize
      hbinMass hfloor_pos hfloor_le_rank hfactor_two_rank hrankValue
      hrank_injective hrank_mono hcard_le_logH

/--
GHW Theorem 7.1 active/singleton-bin wrapper. Starting from one finite family
of factor-two bins, split internally into active bins with at least two bidders
and singleton/empty bins. The caller supplies only the resulting active-plus-
singleton mass cover and the singleton floor-sum bound.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_active_singleton_bins
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin]
    (values : Agent → ℝ) (bins : AllBin → Finset Agent)
    (binFloor : AllBin → ℝ)
    {totalValue h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition :
      totalValue ≤
        (∑ j : {j : AllBin // (bins j).card ≤ 1},
          ∑ i ∈ bins j.1, values i) +
        ∑ j : {j : AllBin // 2 ≤ (bins j).card},
          ∑ i ∈ bins j.1, values i)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin // (bins j).card ≤ 1}, binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos : ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j)
    (hfloor_le :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i)
    (hfactor_two :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j)
    (hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂)
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  classical
  let ActiveBin := {j : AllBin // 2 ≤ (bins j).card}
  let SingleBin := {j : AllBin // (bins j).card ≤ 1}
  have hsingleton_floor :
      ∀ j : SingleBin,
        (∑ i ∈ bins j.1, values i) ≤ 2 * binFloor j.1 := by
    intro j
    have hsum_upper :
        (∑ i ∈ bins j.1, values i) ≤ ∑ _i ∈ bins j.1, 2 * binFloor j.1 := by
      exact Finset.sum_le_sum fun i hi => hfactor_two j.1 i hi
    have hcard_le_one : ((bins j.1).card : ℝ) ≤ 1 := by
      exact_mod_cast j.2
    have hconst_bound :
        (∑ _i ∈ bins j.1, 2 * binFloor j.1) ≤ 2 * binFloor j.1 := by
      calc
        (∑ _i ∈ bins j.1, 2 * binFloor j.1)
            = ((bins j.1).card : ℝ) * (2 * binFloor j.1) := by simp
        _ ≤ 1 * (2 * binFloor j.1) := by
              exact mul_le_mul_of_nonneg_right hcard_le_one
                (by nlinarith [hfloor_nonneg j.1])
        _ = 2 * binFloor j.1 := by ring
    exact le_trans hsum_upper hconst_bound
  have hactive_size : ∀ j : ActiveBin, 2 ≤ (bins j.1).card := by
    intro j
    exact j.2
  have hactive_floor_pos : ∀ j : ActiveBin, 0 < binFloor j.1 := by
    intro j
    exact hfloor_pos j.1 j.2
  have hactive_disjoint :
      ∀ j₁ j₂ : ActiveBin, ∀ i : Agent,
        i ∈ bins j₁.1 → i ∈ bins j₂.1 → j₁ = j₂ := by
    intro j₁ j₂ i hi₁ hi₂
    exact Subtype.ext (hbins_disjoint j₁.1 j₂.1 i hi₁ hi₂)
  have hcard_active_le_logH :
      (Fintype.card ActiveBin : ℝ) ≤ logH := by
    have hcard_active_nat :
        Fintype.card ActiveBin ≤ Fintype.card AllBin := by
      simpa [ActiveBin] using
        (Fintype.card_subtype_le
          (fun j : AllBin => 2 ≤ (bins j).card))
    have hcard_active_real :
        (Fintype.card ActiveBin : ℝ) ≤ (Fintype.card AllBin : ℝ) := by
      exact_mod_cast hcard_active_nat
    exact le_trans hcard_active_real hcard_all_le_logH
  exact
    paper_theorem7_1_weighted_pairing_log_bound_of_finset_partition
      (Agent := Agent) (Bin := ActiveBin) (SingleBin := SingleBin)
      values (fun j : ActiveBin => bins j.1)
      (fun j : ActiveBin => binFloor j.1)
      (fun j : SingleBin => ∑ i ∈ bins j.1, values i)
      (fun j : SingleBin => binFloor j.1)
      htotal hvalues_nonneg hh_pos hvalue_le_h hpartition
      hsingleton_floor hsingleton_floor_sum hlarge hactive_size
      hactive_floor_pos
      (fun j i hi => hfloor_le j.1 i hi)
      (fun j i hi => hfactor_two j.1 i hi)
      hactive_disjoint hcard_active_le_logH

/--
Splitting one finite bin family into singleton/empty bins and active bins
preserves an upper bound by the total bin mass.
-/
theorem paper_theorem7_1_active_singleton_mass_cover_of_all_bins
    {Agent AllBin : Type*} [Fintype AllBin]
    (values : Agent → ℝ) (bins : AllBin → Finset Agent)
    {totalValue : ℝ}
    (hcover : totalValue ≤ ∑ j : AllBin, ∑ i ∈ bins j, values i) :
    totalValue ≤
      (∑ j : {j : AllBin // (bins j).card ≤ 1},
        ∑ i ∈ bins j.1, values i) +
      ∑ j : {j : AllBin // 2 ≤ (bins j).card},
        ∑ i ∈ bins j.1, values i := by
  classical
  let f : AllBin → ℝ := fun j => ∑ i ∈ bins j, values i
  have hsplit_active_not :
      (∑ j : {j : AllBin // 2 ≤ (bins j).card}, f j.1) +
        (∑ j : {j : AllBin // ¬ 2 ≤ (bins j).card}, f j.1) =
          ∑ j : AllBin, f j := by
    simpa [f] using
      (Fintype.sum_subtype_add_sum_subtype
        (fun j : AllBin => 2 ≤ (bins j).card) f)
  let e :
      {j : AllBin // ¬ 2 ≤ (bins j).card} ≃
        {j : AllBin // (bins j).card ≤ 1} :=
    { toFun := fun j => ⟨j.1, by omega⟩
      invFun := fun j => ⟨j.1, by omega⟩
      left_inv := by
        intro j
        exact Subtype.ext rfl
      right_inv := by
        intro j
        exact Subtype.ext rfl }
  have hnot_to_single :
      (∑ j : {j : AllBin // ¬ 2 ≤ (bins j).card}, f j.1) =
        ∑ j : {j : AllBin // (bins j).card ≤ 1}, f j.1 := by
    exact Fintype.sum_equiv e
      (fun j : {j : AllBin // ¬ 2 ≤ (bins j).card} => f j.1)
      (fun j : {j : AllBin // (bins j).card ≤ 1} => f j.1)
      (by intro j; rfl)
  have hsplit :
      (∑ j : {j : AllBin // (bins j).card ≤ 1}, f j.1) +
        (∑ j : {j : AllBin // 2 ≤ (bins j).card}, f j.1) =
          ∑ j : AllBin, f j := by
    rw [← hnot_to_single]
    linarith
  exact le_trans hcover (by simpa [f] using le_of_eq hsplit.symm)

/--
GHW Theorem 7.1 one-family bin wrapper. The caller supplies a finite
factor-two bin family covering total value; Lean internally splits it into
active and singleton bins.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_all_bins
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin]
    (values : Agent → ℝ) (bins : AllBin → Finset Agent)
    (binFloor : AllBin → ℝ)
    {totalValue h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hcover : totalValue ≤ ∑ j : AllBin, ∑ i ∈ bins j, values i)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin // (bins j).card ≤ 1}, binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos : ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j)
    (hfloor_le :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i)
    (hfactor_two :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j)
    (hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂)
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  have hpartition :
      totalValue ≤
        (∑ j : {j : AllBin // (bins j).card ≤ 1},
          ∑ i ∈ bins j.1, values i) +
        ∑ j : {j : AllBin // 2 ≤ (bins j).card},
          ∑ i ∈ bins j.1, values i :=
    paper_theorem7_1_active_singleton_mass_cover_of_all_bins
      values bins hcover
  exact
    paper_theorem7_1_weighted_pairing_log_bound_of_active_singleton_bins
      values bins binFloor htotal hvalues_nonneg hh_pos hvalue_le_h
      hpartition hfloor_nonneg hsingleton_floor_sum hlarge hfloor_pos
      hfloor_le hfactor_two hbins_disjoint hcard_all_le_logH

/--
Classifier bins partition the total bid value: summing values over every fiber
of `binOf` equals `totalBidValue`.
-/
theorem paper_totalBidValue_eq_sum_classifier_bins
    {Agent Bin : Type*} [Fintype Agent] [Fintype Bin] [DecidableEq Bin]
    (values : Agent → ℝ) (binOf : Agent → Bin) :
    totalBidValue values =
      ∑ j : Bin,
        ∑ i ∈ ((Finset.univ : Finset Agent).filter fun a => binOf a = j),
          values i := by
  classical
  rw [totalBidValue]
  symm
  calc
    (∑ j : Bin,
        ∑ i ∈ ((Finset.univ : Finset Agent).filter fun a => binOf a = j),
          values i)
        = ∑ j : Bin, ∑ i : Agent,
            if binOf i = j then values i else 0 := by
          simp [Finset.sum_filter]
    _ = ∑ i : Agent, ∑ j : Bin,
          if binOf i = j then values i else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i : Agent, values i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using
            (Finset.sum_ite_eq'
              (s := (Finset.univ : Finset Bin))
              (a := binOf i)
              (b := fun _ : Bin => values i))

/--
GHW Theorem 7.1 classifier-bin wrapper. A bin classifier automatically supplies
the finite factor-two bin family, disjointness, and total-value cover.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_from_classifier
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin] [DecidableEq AllBin]
    (values : Agent → ℝ) (binOf : Agent → AllBin)
    (binFloor : AllBin → ℝ)
    {totalValue h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin //
          (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card)
            ≤ 1},
        binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos :
      ∀ j : AllBin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j)
    (hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i)
    (hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i))
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  classical
  let bins : AllBin → Finset Agent := fun j =>
    (Finset.univ : Finset Agent).filter fun i => binOf i = j
  have hcover : totalValue ≤ ∑ j : AllBin, ∑ i ∈ bins j, values i := by
    rw [htotal]
    exact le_of_eq (paper_totalBidValue_eq_sum_classifier_bins values binOf)
  have hfloor_pos_bins :
      ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j := by
    intro j hj
    exact hfloor_pos j (by simpa [bins] using hj)
  have hfloor_le_bins :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i := by
    intro j i hi
    have hbin : binOf i = j := (Finset.mem_filter.mp hi).2
    simpa [hbin] using hfloor_le i
  have hfactor_two_bins :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j := by
    intro j i hi
    have hbin : binOf i = j := (Finset.mem_filter.mp hi).2
    simpa [hbin] using hfactor_two i
  have hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂ := by
    intro j₁ j₂ i hi₁ hi₂
    have h₁ : binOf i = j₁ := (Finset.mem_filter.mp hi₁).2
    have h₂ : binOf i = j₂ := (Finset.mem_filter.mp hi₂).2
    exact h₁.symm.trans h₂
  exact
    paper_theorem7_1_weighted_pairing_log_bound_of_all_bins
      values bins binFloor htotal hvalues_nonneg hh_pos hvalue_le_h hcover
      hfloor_nonneg (by simpa [bins] using hsingleton_floor_sum) hlarge
      hfloor_pos_bins hfloor_le_bins hfactor_two_bins hbins_disjoint
      hcard_all_le_logH

/-- Sum of the first `n` powers of two is at most the next power of two. -/
private theorem paper_aux_sum_range_two_pow_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n + (2 : ℝ) ^ n := by
        rw [pow_succ]
        ring
      nlinarith [ih]

/--
Every value in `[1, 2^(m+1)]` lies in one of the `m+1` factor-two dyadic bins
`[2^j, 2 * 2^j]`.
-/
theorem paper_theorem7_dyadicIndex_exists_of_power_two_bound :
    ∀ m : ℕ, ∀ {x : ℝ}, 1 ≤ x → x ≤ (2 : ℝ) ^ (m + 1) →
      ∃ j : Fin (m + 1), (2 : ℝ) ^ j.val ≤ x ∧
        x ≤ 2 * (2 : ℝ) ^ j.val := by
  intro m
  induction m with
  | zero =>
      intro x hx_low hx_high
      refine ⟨⟨0, by omega⟩, ?_, ?_⟩
      · simpa using hx_low
      · simpa using hx_high
  | succ m ih =>
      intro x hx_low hx_high
      by_cases hx_mid : x ≤ (2 : ℝ) ^ (m + 1)
      · obtain ⟨j, hj_low, hj_high⟩ := ih hx_low hx_mid
        refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
        · simpa using hj_low
        · simpa using hj_high
      · refine ⟨⟨m + 1, by omega⟩, ?_, ?_⟩
        · exact le_of_not_ge hx_mid
        · have hpow :
              (2 : ℝ) ^ (m + 1 + 1) = 2 * (2 : ℝ) ^ (m + 1) := by
            rw [pow_succ]
            ring
          simpa [hpow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hx_high

/--
GHW Theorem 4.1 with the paper's power-of-two dyadic partition constructed
internally from a high-bid certificate. If all bids lie in `[1, 2^(m+1)]`, then
the total bid value is at most `2 * (m+1)` times the one-winner fixed-price
benchmark.
-/
theorem paper_theorem4_1_fixed_price_lower_bound_from_power_two_bins
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ)
    {fixedPriceBenchmark totalValue : ℝ}
    (hbenchmark : IsFixedPriceBenchmark values 1 fixedPriceBenchmark)
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1)) :
    totalValue ≤
      (2 * ((m + 1 : ℕ) : ℝ)) * fixedPriceBenchmark := by
  classical
  let Bin := Fin (m + 1)
  let hExists :
      ∀ i : Agent, ∃ j : Bin,
        (2 : ℝ) ^ j.val ≤ values i ∧
          values i ≤ 2 * (2 : ℝ) ^ j.val := fun i =>
    paper_theorem7_dyadicIndex_exists_of_power_two_bound
      m (hvalue_ge_one i) (hvalue_le_power i)
  let binOf : Agent → Bin := fun i => Classical.choose (hExists i)
  let binFloor : Bin → ℝ := fun j => (2 : ℝ) ^ j.val
  let bins : Bin → Finset Agent := fun j =>
    (Finset.univ : Finset Agent).filter fun i => binOf i = j
  have hcover :
      totalValue ≤ ∑ j : Bin, ∑ i ∈ bins j, values i := by
    rw [htotal]
    exact le_of_eq (paper_totalBidValue_eq_sum_classifier_bins values binOf)
  have hfloor_nonneg : ∀ j : Bin, 0 ≤ binFloor j := by
    intro j
    dsimp [binFloor]
    positivity
  have hfloor_le :
      ∀ j : Bin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i := by
    intro j i hi
    have hbin : binOf i = j := by
      simpa [bins] using hi
    subst hbin
    exact (Classical.choose_spec (hExists i)).1
  have hfactor_two :
      ∀ j : Bin, ∀ i : Agent, i ∈ bins j →
        values i ≤ 2 * binFloor j := by
    intro j i hi
    have hbin : binOf i = j := by
      simpa [bins] using hi
    subst hbin
    exact (Classical.choose_spec (hExists i)).2
  have hbound :
      totalValue ≤
        (2 * (Fintype.card Bin : ℝ)) * fixedPriceBenchmark :=
    paper_theorem4_1_fixed_price_lower_bound_of_factor_two_partition_allow_empty
      values bins binFloor hbenchmark hfloor_nonneg hcover hfloor_le
      hfactor_two
  simpa [Bin] using hbound

/--
GHW Theorem 4.1 for the finite one-winner fixed-price benchmark. This removes
the explicit benchmark certificate from
`paper_theorem4_1_fixed_price_lower_bound_from_power_two_bins`: with all bids
at least one and at least one bidder, price `1` is feasible, so the finite
candidate benchmark is the paper's optimal fixed-price benchmark.
-/
theorem paper_theorem4_1_finite_candidate_benchmark_from_power_two_bins
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1)) :
    totalBidValue values ≤
      (2 * ((m + 1 : ℕ) : ℝ)) *
        finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  have hfeasible_one : 1 ≤ saleCount values 1 := by
    have hfilter :
        ((Finset.univ : Finset Agent).filter fun i => (1 : ℝ) ≤ values i) =
          (Finset.univ : Finset Agent) := by
      ext i
      simp [hvalue_ge_one i]
    unfold saleCount
    rw [hfilter]
    exact Nat.succ_le_of_lt (Fintype.card_pos)
  have hbenchmark :
      IsFixedPriceBenchmark values 1
        (finiteCandidateFixedPriceBenchmark values 1) :=
    finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible
      values (minWinners := 1) (by decide)
      ⟨1, by norm_num, hfeasible_one⟩
  exact
    paper_theorem4_1_fixed_price_lower_bound_from_power_two_bins
      values m hbenchmark rfl hvalue_ge_one hvalue_le_power

/--
GHW Theorem 4.1 with an abstract log-size certificate. Once an analytic or
combinatorial argument proves `(m+1) <= logH`, the dyadic theorem immediately
gives the paper-style `T <= 2 * logH * F` statement.
-/
theorem paper_theorem4_1_finite_candidate_benchmark_from_log_certificate
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ) {logH : ℝ}
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hlog_cert : ((m + 1 : ℕ) : ℝ) ≤ logH) :
    totalBidValue values ≤
      (2 * logH) * finiteCandidateFixedPriceBenchmark values 1 := by
  have hbase :
      totalBidValue values ≤
        (2 * ((m + 1 : ℕ) : ℝ)) *
          finiteCandidateFixedPriceBenchmark values 1 :=
    paper_theorem4_1_finite_candidate_benchmark_from_power_two_bins
      values m hvalue_ge_one hvalue_le_power
  have hbenchmark_nonneg :
      0 ≤ finiteCandidateFixedPriceBenchmark values 1 :=
    finiteCandidateFixedPriceBenchmark_nonneg values 1
  have hcoef :
      2 * ((m + 1 : ℕ) : ℝ) ≤ 2 * logH := by nlinarith
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right hcoef hbenchmark_nonneg)

/--
Rounded dyadic auxiliary bound for normalized bids in `[1,h]`.  The additive
term pays for integer bin rounding; it is retained for internal callers and
is not the exact printed Theorem 4.1 endpoint.
-/
theorem paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * (Real.logb 2 h + 2)) *
        finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let m : ℕ := Nat.ceil (Real.logb 2 h)
  have hh_pos : 0 < h := lt_of_lt_of_le zero_lt_one hh_ge_one
  have hlog_nonneg : 0 ≤ Real.logb 2 h :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hh_ge_one
  have hlog_le_m : Real.logb 2 h ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hh_le_rpow : h ≤ (2 : ℝ) ^ (m : ℝ) :=
    (Real.logb_le_iff_le_rpow
      (b := 2) (by norm_num : (1 : ℝ) < 2) hh_pos).mp hlog_le_m
  have hh_le_pow : h ≤ (2 : ℝ) ^ m := by
    simpa [Real.rpow_natCast] using hh_le_rpow
  have hh_le_pow_succ : h ≤ (2 : ℝ) ^ (m + 1) :=
    le_trans hh_le_pow
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ m))
  have hvalue_le_power :
      ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1) := by
    intro i
    exact le_trans (hvalue_le_h i) hh_le_pow_succ
  have hbase :
      totalBidValue values ≤
        (2 * ((m + 1 : ℕ) : ℝ)) *
          finiteCandidateFixedPriceBenchmark values 1 :=
    paper_theorem4_1_finite_candidate_benchmark_from_power_two_bins
      values m hvalue_ge_one hvalue_le_power
  have hceil_lt : (m : ℝ) < Real.logb 2 h + 1 := by
    simpa [m] using Nat.ceil_lt_add_one hlog_nonneg
  have hcount_le :
      ((m + 1 : ℕ) : ℝ) ≤ Real.logb 2 h + 2 := by
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
    nlinarith
  have hcoef :
      2 * ((m + 1 : ℕ) : ℝ) ≤ 2 * (Real.logb 2 h + 2) := by
    nlinarith
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right hcoef
      (finiteCandidateFixedPriceBenchmark_nonneg values 1))

/-- Every nonnegative threshold revenue is bounded by the one-winner fixed-price
benchmark.  This is the tail-count ingredient for the exact logarithmic
Theorem 4.1 repair. -/
theorem paper_theorem4_1_saleCount_mul_le_finite_candidate_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (price : ℝ) (hprice_nonneg : 0 ≤ price) :
    (saleCount values price : ℝ) * price ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  by_cases hzero : saleCount values price = 0
  · simp [hzero, finiteCandidateFixedPriceBenchmark_nonneg values 1]
  · have hpositive : 0 < saleCount values price := Nat.pos_of_ne_zero hzero
    have hfeasible : 1 ≤ saleCount values price := hpositive
    rw [← singlePriceRevenue_eq_saleCount_mul]
    exact singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      values (by simp) hprice_nonneg hfeasible

/-- On a positive price interval, the sale-count tail is bounded by fixed-price
benchmark divided by the price. -/
theorem paper_theorem4_1_saleCount_le_finite_candidate_benchmark_div
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (price : ℝ) (hprice_pos : 0 < price) :
    (saleCount values price : ℝ) ≤
      finiteCandidateFixedPriceBenchmark values 1 / price := by
  exact (le_div_iff₀ hprice_pos).mpr
    (paper_theorem4_1_saleCount_mul_le_finite_candidate_benchmark
      values price hprice_pos.le)

/-- Raising a price cannot increase the number of accepting bidders. -/
theorem paper_theorem4_1_saleCount_antitone
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) :
    Antitone (fun price : ℝ => (saleCount values price : ℝ)) := by
  intro low high hlow_high
  have hsubset :
      (Finset.univ.filter fun i : Agent => high ≤ values i) ⊆
        (Finset.univ.filter fun i : Agent => low ≤ values i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
      hlow_high.trans (Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_le_card hsubset
  simpa [saleCount] using hcard

/-- With all normalized bids at least one, price one attains at least the
number of bidders in fixed-price revenue. -/
theorem paper_theorem4_1_finite_candidate_benchmark_ge_card
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i) :
    (Fintype.card Agent : ℝ) ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  have hfeasible_one : 1 ≤ saleCount values 1 := by
    have hfilter :
        ((Finset.univ : Finset Agent).filter fun i => (1 : ℝ) ≤ values i) =
          (Finset.univ : Finset Agent) := by
      ext i
      simp [hvalue_ge_one i]
    unfold saleCount
    rw [hfilter]
    exact Nat.succ_le_of_lt Fintype.card_pos
  calc
    (Fintype.card Agent : ℝ) = singlePriceRevenue values 1 := by
      simp [singlePriceRevenue, hvalue_ge_one]
    _ ≤ finiteCandidateFixedPriceBenchmark values 1 :=
      singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
        values (by norm_num) (by norm_num) hfeasible_one

/-- Finite layer-cake identity for a normalized bid profile. -/
theorem paper_theorem4_1_total_eq_card_add_saleCount_integral
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values =
      (Fintype.card Agent : ℝ) +
        ∫ price in 1..h, (saleCount values price : ℝ) := by
  classical
  let indicator : Agent → ℝ → ℝ :=
    fun i price => if price ≤ values i then 1 else 0
  have hindicator_integrable : ∀ i : Agent,
      IntervalIntegrable (indicator i) volume 1 h := by
    intro i
    change IntervalIntegrable
      ((Set.Iic (values i)).indicator (fun _ : ℝ => (1 : ℝ))) volume 1 h
    apply IntegrableOn.intervalIntegrable
    apply IntegrableOn.indicator
    · exact integrableOn_const (by
        rw [Set.uIcc]
        exact measure_Icc_lt_top.ne)
    · exact measurableSet_Iic
  have hindicator_integral : ∀ i : Agent,
      (∫ price in 1..h, indicator i price) = values i - 1 := by
    intro i
    change (∫ price in 1..h,
      ((Set.Iic (values i)).indicator (fun _ : ℝ => (1 : ℝ))) price) =
        values i - 1
    calc
      (∫ price in 1..h,
          ((Set.Iic (values i)).indicator (fun _ : ℝ => (1 : ℝ))) price) =
          ∫ price in 1..values i, (1 : ℝ) :=
        intervalIntegral.integral_indicator (f := fun _ : ℝ => (1 : ℝ))
          ⟨hvalue_ge_one i, hvalue_le_h i⟩
      _ = values i - 1 := integral_one
  have hsum_count : ∀ price : ℝ,
      (∑ i : Agent, indicator i price) = (saleCount values price : ℝ) := by
    intro price
    change (∑ i : Agent, if price ≤ values i then (1 : ℝ) else 0) = _
    rw [saleCount, ← Finset.sum_filter]
    simp
  calc
    totalBidValue values = ∑ i : Agent, values i := rfl
    _ = ∑ i : Agent, (1 + ∫ price in 1..h, indicator i price) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hindicator_integral]
      ring
    _ = (∑ _i : Agent, (1 : ℝ)) +
          ∑ i : Agent, ∫ price in 1..h, indicator i price :=
      Finset.sum_add_distrib
    _ = (Fintype.card Agent : ℝ) +
          ∫ price in 1..h, ∑ i : Agent, indicator i price := by
      rw [← intervalIntegral.integral_finset_sum
        (fun i _ => hindicator_integrable i)]
      norm_num
    _ = (Fintype.card Agent : ℝ) +
          ∫ price in 1..h, (saleCount values price : ℝ) := by
      have hfun : (fun price : ℝ => ∑ i : Agent, indicator i price) =
          fun price => (saleCount values price : ℝ) := funext hsum_count
      rw [hfun]

/-- The exact analytic form behind GHW Theorem 4.1: normalized total bid
value is at most `(1 + ln h)` times the finite one-winner fixed-price
benchmark. -/
theorem paper_theorem4_1_total_le_one_add_log_mul_finite_candidate_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (1 + Real.log h) * finiteCandidateFixedPriceBenchmark values 1 := by
  let benchmark : ℝ := finiteCandidateFixedPriceBenchmark values 1
  let tail : ℝ → ℝ := fun price => (saleCount values price : ℝ)
  have htail_integrable : IntervalIntegrable tail volume 1 h := by
    exact (paper_theorem4_1_saleCount_antitone values).intervalIntegrable
  have hdiv_cont : ContinuousOn (fun price : ℝ => benchmark / price)
      (Set.uIcc 1 h) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro price hprice
    rw [Set.uIcc_of_le hh_ge_one] at hprice
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hprice.1)
  have hdiv_integrable : IntervalIntegrable
      (fun price : ℝ => benchmark / price) volume 1 h :=
    hdiv_cont.intervalIntegrable
  have htail_le_div : ∀ price ∈ Set.Icc (1 : ℝ) h,
      tail price ≤ benchmark / price := by
    intro price hprice
    exact paper_theorem4_1_saleCount_le_finite_candidate_benchmark_div
      values price (lt_of_lt_of_le zero_lt_one hprice.1)
  have hintegral_le :
      (∫ price in 1..h, tail price) ≤
        ∫ price in 1..h, benchmark / price :=
    intervalIntegral.integral_mono_on hh_ge_one htail_integrable
      hdiv_integrable htail_le_div
  have hdiv_eq : (∫ price in 1..h, benchmark / price) =
      benchmark * Real.log h := by
    calc
      (∫ price in 1..h, benchmark / price) =
          ∫ price in 1..h, benchmark * (1 / price) := by
        congr with price
        ring
      _ = benchmark * ∫ price in 1..h, 1 / price := by
        rw [intervalIntegral.integral_const_mul]
      _ = benchmark * Real.log h := by
        rw [integral_one_div_of_pos zero_lt_one
          (lt_of_lt_of_le zero_lt_one hh_ge_one)]
        simp
  have hcard_le : (Fintype.card Agent : ℝ) ≤ benchmark := by
    exact paper_theorem4_1_finite_candidate_benchmark_ge_card values
      hvalue_ge_one
  calc
    totalBidValue values =
        (Fintype.card Agent : ℝ) + ∫ price in 1..h, tail price := by
      simpa [tail] using
        paper_theorem4_1_total_eq_card_add_saleCount_integral values
          hvalue_ge_one hvalue_le_h
    _ ≤ benchmark + ∫ price in 1..h, benchmark / price := by
      gcongr
    _ = (1 + Real.log h) * benchmark := by
      rw [hdiv_eq]
      ring

/-- Analytic comparison converting the layer-cake bound to the paper's
base-two logarithmic factor on the repaired domain `2 <= h`. -/
theorem paper_theorem4_1_one_add_log_le_two_logb_of_two_le {h : ℝ}
    (hh_ge_two : 2 ≤ h) :
    1 + Real.log h ≤ 2 * Real.logb 2 h := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogh_nonneg : 0 ≤ Real.log h :=
    Real.log_nonneg (by linarith)
  have hlog2_le_logh : Real.log 2 ≤ Real.log h :=
    Real.log_le_log (by norm_num) hh_ge_two
  have hmul : Real.log h * Real.log 2 ≤ Real.log h := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2_le_one hlogh_nonneg]
  have hraw : (1 + Real.log h) * Real.log 2 ≤ 2 * Real.log h := by
    nlinarith
  rw [Real.logb]
  have hgoal : 1 + Real.log h ≤ (2 * Real.log h) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr hraw
  convert hgoal using 1 <;> ring

/-- Corrected exact GHW Theorem 4.1 endpoint.  The printed source statement
needs the visible restriction `2 <= h`; without it the real-log denominator
can be too small. -/
theorem paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_two : 2 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * Real.logb 2 h) * finiteCandidateFixedPriceBenchmark values 1 := by
  have hbase :=
    paper_theorem4_1_total_le_one_add_log_mul_finite_candidate_benchmark
      values (by linarith) hvalue_ge_one hvalue_le_h
  have hcoefficient : 1 + Real.log h ≤ 2 * Real.logb 2 h :=
    paper_theorem4_1_one_add_log_le_two_logb_of_two_le hh_ge_two
  have hbenchmark_nonneg : 0 ≤ finiteCandidateFixedPriceBenchmark values 1 :=
    finiteCandidateFixedPriceBenchmark_nonneg values 1
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hcoefficient hbenchmark_nonneg)

/--
Paper-facing normalized high-value model for GHW Theorem 4.1. It packages the
finite formalization's normalized bidder values in `[1,h]`.
-/
structure PaperTheorem41HighValueModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent] where
  values : Agent → ℝ
  highValue : ℝ
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue

/-- Rounded high-value model consequence used by the dyadic helper route. -/
theorem paper_theorem4_1_finite_candidate_benchmark_of_high_value_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (model : PaperTheorem41HighValueModel Agent) :
    totalBidValue model.values ≤
      (2 * (Real.logb 2 model.highValue + 2)) *
        finiteCandidateFixedPriceBenchmark model.values 1 := by
  exact
    paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
      model.values model.highValue_ge_one model.values_ge_one
      model.values_le_highValue

/--
GHW Corollary 4.2 from a normalized truncated high-value instance. The
truncation loss and benchmark comparison are stated directly; Theorem 4.1
supplies the truncated-instance bound internally.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_of_truncated_high_value_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (truncated : PaperTheorem41HighValueModel Agent)
    {totalValue fixedPriceBenchmark binCount : ℝ}
    (htruncate : totalValue ≤ 2 * totalBidValue truncated.values)
    (hbenchmark_le :
      finiteCandidateFixedPriceBenchmark truncated.values 1 ≤
        fixedPriceBenchmark)
    (hbinCount : Real.logb 2 truncated.highValue + 2 ≤ binCount) :
    totalValue ≤ (4 * binCount) * fixedPriceBenchmark := by
  let logTerm : ℝ := Real.logb 2 truncated.highValue + 2
  have hlog_nonneg : 0 ≤ logTerm := by
    have hlog : 0 ≤ Real.logb 2 truncated.highValue :=
      Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2)
        truncated.highValue_ge_one
    dsimp [logTerm]
    nlinarith
  have hbin_nonneg : 0 ≤ binCount := le_trans hlog_nonneg hbinCount
  have hbench_nonneg :
      0 ≤ finiteCandidateFixedPriceBenchmark truncated.values 1 :=
    finiteCandidateFixedPriceBenchmark_nonneg truncated.values 1
  have htruncated_bound :=
    paper_theorem4_1_finite_candidate_benchmark_of_high_value_model
      truncated
  have hmul :
      (2 * logTerm) *
          finiteCandidateFixedPriceBenchmark truncated.values 1 ≤
        (2 * binCount) * fixedPriceBenchmark := by
    have hleft : 2 * logTerm ≤ 2 * binCount := by
      nlinarith
    exact
      mul_le_mul hleft hbenchmark_le hbench_nonneg
        (mul_nonneg (by norm_num) hbin_nonneg)
  have hbound :
      totalBidValue truncated.values ≤
        (2 * binCount) * fixedPriceBenchmark := by
    exact le_trans (by simpa [logTerm] using htruncated_bound) hmul
  exact
    paper_corollary4_2_fixed_price_lower_bound_from_truncation
      htruncate hbound

/--
Corollary 4.2 truncation loss for the normalized cutoff `h / n`. Dropping bids
below that cutoff loses at most the retained mass because the dropped bids have
total value at most `h`, while a bidder attaining `h` is retained.
-/
theorem paper_corollary4_2_card_cutoff_truncation_loss
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {h cutoff : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hcutoff_pos : 0 < cutoff)
    (hcard_cutoff : (Fintype.card Agent : ℝ) * cutoff = h)
    (hcutoff_le_h : cutoff ≤ h)
    (hmax : ∃ i : Agent, values i = h) :
    totalBidValue values ≤
      2 * (∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i),
        values i) := by
  classical
  let retained : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i
  let dropped : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => ¬ cutoff ≤ values i
  have hsplit :
      (∑ i ∈ retained, values i) + (∑ i ∈ dropped, values i) =
        totalBidValue values := by
    simpa [retained, dropped, totalBidValue] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Agent))
        (p := fun i : Agent => cutoff ≤ values i)
        (f := values))
  have hdropped_each :
      ∀ i, i ∈ dropped → values i ≤ cutoff := by
    intro i hi
    have hnot : ¬ cutoff ≤ values i := by
      simpa [dropped] using (Finset.mem_filter.mp hi).2
    exact le_of_lt (lt_of_not_ge hnot)
  have hdropped_sum_le_count :
      (∑ i ∈ dropped, values i) ≤ (dropped.card : ℝ) * cutoff := by
    calc
      (∑ i ∈ dropped, values i)
          ≤ ∑ _i ∈ dropped, cutoff :=
            Finset.sum_le_sum hdropped_each
      _ = (dropped.card : ℝ) * cutoff := by
            simp
  have hdropped_card_le :
      (dropped.card : ℝ) ≤ (Fintype.card Agent : ℝ) := by
    exact_mod_cast
      (Finset.card_filter_le
        (s := (Finset.univ : Finset Agent))
        (p := fun i : Agent => ¬ cutoff ≤ values i))
  have hdropped_sum_le_h :
      (∑ i ∈ dropped, values i) ≤ h := by
    have hcount :
        (dropped.card : ℝ) * cutoff ≤
          (Fintype.card Agent : ℝ) * cutoff :=
      mul_le_mul_of_nonneg_right hdropped_card_le (le_of_lt hcutoff_pos)
    nlinarith
  have hretained_nonneg :
      ∀ i, i ∈ retained → 0 ≤ values i := by
    intro i _hi
    exact hvalues_nonneg i
  have hretained_sum_ge_h :
      h ≤ ∑ i ∈ retained, values i := by
    rcases hmax with ⟨i, rfl⟩
    have hi : i ∈ retained := by
      simp [retained, hcutoff_le_h]
    exact Finset.single_le_sum hretained_nonneg hi
  nlinarith

/--
The retained subtype normalized by `cutoff` has total value equal to the
retained original value divided by `cutoff`.
-/
theorem paper_corollary4_2_card_cutoff_scaled_total
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {cutoff : ℝ}
    (hcutoff_pos : 0 < cutoff) :
    cutoff *
        totalBidValue
          (fun i : {i : Agent // cutoff ≤ values i} => values i.1 / cutoff) =
      ∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i),
        values i := by
  classical
  have hsubtype :
      (∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i),
          values i) =
        ∑ i : {i : Agent // cutoff ≤ values i}, values i.1 := by
    exact
      Finset.sum_subtype
        (s := (Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i)
        (h := by intro i; simp)
        (f := values)
  rw [totalBidValue, hsubtype]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  field_simp [ne_of_gt hcutoff_pos]

/--
The finite candidate benchmark of the normalized retained profile scales back
to a feasible candidate-price revenue in the original profile.
-/
theorem paper_corollary4_2_card_cutoff_scaled_benchmark_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {cutoff : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hcutoff_pos : 0 < cutoff)
    [Nonempty {i : Agent // cutoff ≤ values i}] :
    cutoff *
        finiteCandidateFixedPriceBenchmark
          (fun i : {i : Agent // cutoff ≤ values i} => values i.1 / cutoff) 1 ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let Retained := {i : Agent // cutoff ≤ values i}
  let normalized : Retained → ℝ := fun i => values i.1 / cutoff
  let chosen : Retained := finiteCandidateBenchmarkBidder normalized 1
  have hbench :
      finiteCandidateFixedPriceBenchmark normalized 1 =
        candidateFixedPriceRevenue normalized 1 chosen := by
    simpa [chosen] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
        normalized 1
  by_cases hsel :
      0 ≤ normalized chosen ∧ 1 ≤ saleCount normalized (normalized chosen)
  · have hbench_selected :
        finiteCandidateFixedPriceBenchmark normalized 1 =
          singlePriceRevenue normalized (normalized chosen) := by
      rw [hbench]
      simp [candidateFixedPriceRevenue, hsel]
    have hprice_eq :
        cutoff * normalized chosen = values chosen.1 := by
      dsimp [normalized]
      field_simp [ne_of_gt hcutoff_pos]
    have hnorm_winner_count_le :
        saleCount normalized (normalized chosen) ≤
          saleCount values (values chosen.1) := by
      let normWinners : Finset Retained :=
        (Finset.univ : Finset Retained).filter
          fun i => normalized chosen ≤ normalized i
      let originalWinners : Finset Agent :=
        (Finset.univ : Finset Agent).filter
          fun i => values chosen.1 ≤ values i
      have hmap_subset :
          normWinners.map (Function.Embedding.subtype fun i : Agent =>
              cutoff ≤ values i) ⊆ originalWinners := by
        intro i hi
        rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
        have hjwin : normalized chosen ≤ normalized j := by
          simpa [normWinners] using (Finset.mem_filter.mp hj).2
        have hle : values chosen.1 ≤ values j.1 := by
          have hmul :=
            mul_le_mul_of_nonneg_left hjwin (le_of_lt hcutoff_pos)
          rw [hprice_eq] at hmul
          have hjprice :
              cutoff * normalized j = values j.1 := by
            dsimp [normalized]
            field_simp [ne_of_gt hcutoff_pos]
          simpa [hjprice] using hmul
        simp [originalWinners, hle]
      have hcard_map :
          (normWinners.map (Function.Embedding.subtype fun i : Agent =>
              cutoff ≤ values i)).card = normWinners.card :=
        Finset.card_map _
      have hcard_le :
          normWinners.card ≤ originalWinners.card := by
        calc
          normWinners.card =
              (normWinners.map (Function.Embedding.subtype fun i : Agent =>
                cutoff ≤ values i)).card := hcard_map.symm
          _ ≤ originalWinners.card := Finset.card_le_card hmap_subset
      simpa [saleCount, normWinners, originalWinners] using hcard_le
    have hscaled_revenue_le_original :
        cutoff * singlePriceRevenue normalized (normalized chosen) ≤
          singlePriceRevenue values (values chosen.1) := by
      rw [singlePriceRevenue_eq_saleCount_mul normalized (normalized chosen),
        singlePriceRevenue_eq_saleCount_mul values (values chosen.1)]
      have hcount_cast :
          (saleCount normalized (normalized chosen) : ℝ) ≤
            (saleCount values (values chosen.1) : ℝ) := by
        exact_mod_cast hnorm_winner_count_le
      have hprice_nonneg : 0 ≤ values chosen.1 := hvalues_nonneg chosen.1
      nlinarith [hprice_eq]
    have horiginal_feasible :
        1 ≤ saleCount values (values chosen.1) :=
      le_trans hsel.2 hnorm_winner_count_le
    have horiginal_candidate :
        singlePriceRevenue values (values chosen.1) ≤
          finiteCandidateFixedPriceBenchmark values 1 :=
      singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
        values (minWinners := 1) (by norm_num) (hvalues_nonneg chosen.1)
        horiginal_feasible
    calc
      cutoff * finiteCandidateFixedPriceBenchmark normalized 1
          = cutoff * singlePriceRevenue normalized (normalized chosen) := by
            rw [hbench_selected]
      _ ≤ singlePriceRevenue values (values chosen.1) :=
            hscaled_revenue_le_original
      _ ≤ finiteCandidateFixedPriceBenchmark values 1 := horiginal_candidate
  · have hbench_zero :
        finiteCandidateFixedPriceBenchmark normalized 1 = 0 := by
      simpa [candidateFixedPriceRevenue, hsel] using hbench
    change cutoff * finiteCandidateFixedPriceBenchmark normalized 1 ≤
      finiteCandidateFixedPriceBenchmark values 1
    rw [hbench_zero]
    simpa using finiteCandidateFixedPriceBenchmark_nonneg values 1

/--
GHW Corollary 4.2 with the paper truncation constructed internally. If `h`
is the highest bid value, retaining bids at least `h / n` and normalizing by
that cutoff gives a `[1,n]` high-value instance, so Theorem 4.1 yields the
factor-four logarithmic fixed-price lower bound.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_of_card_truncation
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h binCount : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hmax : ∃ i : Agent, values i = h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hbinCount : Real.logb 2 (Fintype.card Agent : ℝ) + 2 ≤ binCount) :
    totalBidValue values ≤
      (4 * binCount) * finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let cardR : ℝ := Fintype.card Agent
  let cutoff : ℝ := h / cardR
  have hcard_pos_nat : 0 < Fintype.card Agent := Fintype.card_pos
  have hcard_pos : 0 < cardR := by
    dsimp [cardR]
    exact_mod_cast hcard_pos_nat
  have hcard_ge_one : 1 ≤ cardR := by
    dsimp [cardR]
    exact_mod_cast hcard_pos_nat
  have hcutoff_pos : 0 < cutoff := by
    dsimp [cutoff, cardR]
    positivity
  have hcard_cutoff : cardR * cutoff = h := by
    dsimp [cutoff, cardR]
    field_simp [ne_of_gt hcard_pos]
  have hcutoff_le_h : cutoff ≤ h := by
    dsimp [cutoff]
    rw [div_le_iff₀ hcard_pos]
    have hmul : h * 1 ≤ h * cardR :=
      mul_le_mul_of_nonneg_left hcard_ge_one (le_of_lt hh_pos)
    nlinarith
  let Retained := {i : Agent // cutoff ≤ values i}
  let normalized : Retained → ℝ := fun i => values i.1 / cutoff
  haveI : Nonempty Retained := by
    rcases hmax with ⟨i, hi⟩
    exact ⟨⟨i, by simpa [hi] using hcutoff_le_h⟩⟩
  have hnorm_ge_one : ∀ i : Retained, 1 ≤ normalized i := by
    intro i
    dsimp [normalized]
    rw [le_div_iff₀ hcutoff_pos]
    simpa using i.2
  have hnorm_le_card : ∀ i : Retained, normalized i ≤ cardR := by
    intro i
    dsimp [normalized]
    rw [div_le_iff₀ hcutoff_pos]
    calc
      values i.1 ≤ h := hvalue_le_h i.1
      _ = cardR * cutoff := hcard_cutoff.symm
  have hcard_ge_one_model : 1 ≤ cardR := hcard_ge_one
  let truncatedModel : PaperTheorem41HighValueModel Retained :=
    { values := normalized
      highValue := cardR
      highValue_ge_one := hcard_ge_one_model
      values_ge_one := hnorm_ge_one
      values_le_highValue := hnorm_le_card }
  have hretained_total :
      cutoff * totalBidValue normalized =
        ∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i),
          values i :=
    paper_corollary4_2_card_cutoff_scaled_total values hcutoff_pos
  have htruncate_unscaled :
      totalBidValue values ≤
        2 * (∑ i ∈ ((Finset.univ : Finset Agent).filter fun i =>
          cutoff ≤ values i), values i) :=
    paper_corollary4_2_card_cutoff_truncation_loss
      values hvalues_nonneg hcutoff_pos hcard_cutoff hcutoff_le_h hmax
  have htruncate_scaled :
      totalBidValue values / cutoff ≤ 2 * totalBidValue normalized := by
    rw [div_le_iff₀ hcutoff_pos]
    nlinarith
  have hbenchmark_scaled :
      cutoff * finiteCandidateFixedPriceBenchmark normalized 1 ≤
        finiteCandidateFixedPriceBenchmark values 1 :=
    paper_corollary4_2_card_cutoff_scaled_benchmark_le
      values hvalues_nonneg hcutoff_pos
  have hbenchmark_scaled_div :
      finiteCandidateFixedPriceBenchmark normalized 1 ≤
        finiteCandidateFixedPriceBenchmark values 1 / cutoff := by
    rw [le_div_iff₀ hcutoff_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbenchmark_scaled
  have hscaled_bound :
      totalBidValue values / cutoff ≤
        (4 * binCount) *
          (finiteCandidateFixedPriceBenchmark values 1 / cutoff) := by
    exact
      paper_corollary4_2_fixed_price_lower_bound_of_truncated_high_value_model
        truncatedModel htruncate_scaled hbenchmark_scaled_div
        (by simpa [truncatedModel, cardR] using hbinCount)
  calc
    totalBidValue values
        = (totalBidValue values / cutoff) * cutoff := by
          field_simp [ne_of_gt hcutoff_pos]
    _ ≤ ((4 * binCount) *
          (finiteCandidateFixedPriceBenchmark values 1 / cutoff)) * cutoff :=
          mul_le_mul_of_nonneg_right hscaled_bound (le_of_lt hcutoff_pos)
    _ = (4 * binCount) * finiteCandidateFixedPriceBenchmark values 1 := by
          field_simp [ne_of_gt hcutoff_pos]

/--
Corrected exact GHW Corollary 4.2 endpoint.  The printed real-log denominator
requires the visible nondegenerate cardinality condition `2 <= n`.
-/
theorem paper_corollary4_2_fixed_price_lower_bound_exact_logb_of_card_two_le
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hmax : ∃ i : Agent, values i = h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hcard_ge_two : 2 ≤ (Fintype.card Agent : ℝ)) :
    totalBidValue values ≤
      (4 * Real.logb 2 (Fintype.card Agent : ℝ)) *
        finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let cardR : ℝ := Fintype.card Agent
  let cutoff : ℝ := h / cardR
  have hcard_pos_nat : 0 < Fintype.card Agent := Fintype.card_pos
  have hcard_pos : 0 < cardR := by
    dsimp [cardR]
    exact_mod_cast hcard_pos_nat
  have hcard_ge_one : 1 ≤ cardR := by
    dsimp [cardR]
    exact_mod_cast hcard_pos_nat
  have hcard_ge_twoR : 2 ≤ cardR := by
    simpa [cardR] using hcard_ge_two
  have hcutoff_pos : 0 < cutoff := by
    dsimp [cutoff, cardR]
    positivity
  have hcard_cutoff : cardR * cutoff = h := by
    dsimp [cutoff, cardR]
    field_simp [ne_of_gt hcard_pos]
  have hcutoff_le_h : cutoff ≤ h := by
    dsimp [cutoff]
    rw [div_le_iff₀ hcard_pos]
    have hmul : h * 1 ≤ h * cardR :=
      mul_le_mul_of_nonneg_left hcard_ge_one (le_of_lt hh_pos)
    nlinarith
  let Retained := {i : Agent // cutoff ≤ values i}
  let normalized : Retained → ℝ := fun i => values i.1 / cutoff
  haveI : Nonempty Retained := by
    rcases hmax with ⟨i, hi⟩
    exact ⟨⟨i, by simpa [hi] using hcutoff_le_h⟩⟩
  have hnorm_ge_one : ∀ i : Retained, 1 ≤ normalized i := by
    intro i
    dsimp [normalized]
    rw [le_div_iff₀ hcutoff_pos]
    simpa using i.2
  have hnorm_le_card : ∀ i : Retained, normalized i ≤ cardR := by
    intro i
    dsimp [normalized]
    rw [div_le_iff₀ hcutoff_pos]
    calc
      values i.1 ≤ h := hvalue_le_h i.1
      _ = cardR * cutoff := hcard_cutoff.symm
  have hretained_total :
      cutoff * totalBidValue normalized =
        ∑ i ∈ ((Finset.univ : Finset Agent).filter fun i => cutoff ≤ values i),
          values i :=
    paper_corollary4_2_card_cutoff_scaled_total values hcutoff_pos
  have htruncate_unscaled :
      totalBidValue values ≤
        2 * (∑ i ∈ ((Finset.univ : Finset Agent).filter fun i =>
          cutoff ≤ values i), values i) :=
    paper_corollary4_2_card_cutoff_truncation_loss
      values hvalues_nonneg hcutoff_pos hcard_cutoff hcutoff_le_h hmax
  have htruncate_scaled :
      totalBidValue values / cutoff ≤ 2 * totalBidValue normalized := by
    rw [div_le_iff₀ hcutoff_pos]
    nlinarith
  have hbenchmark_scaled :
      cutoff * finiteCandidateFixedPriceBenchmark normalized 1 ≤
        finiteCandidateFixedPriceBenchmark values 1 :=
    paper_corollary4_2_card_cutoff_scaled_benchmark_le
      values hvalues_nonneg hcutoff_pos
  have hbenchmark_scaled_div :
      finiteCandidateFixedPriceBenchmark normalized 1 ≤
        finiteCandidateFixedPriceBenchmark values 1 / cutoff := by
    rw [le_div_iff₀ hcutoff_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbenchmark_scaled
  have htruncated_exact :
      totalBidValue normalized ≤
        (2 * Real.logb 2 cardR) *
          finiteCandidateFixedPriceBenchmark normalized 1 :=
    paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
      normalized hcard_ge_twoR hnorm_ge_one hnorm_le_card
  have hlog_nonneg : 0 ≤ Real.logb 2 cardR :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2)
      (by linarith [hcard_ge_twoR])
  have htruncated_coefficient_nonneg : 0 ≤ 2 * Real.logb 2 cardR :=
    mul_nonneg (by norm_num) hlog_nonneg
  have hscaled_bound :
      totalBidValue values / cutoff ≤
        (4 * Real.logb 2 cardR) *
          (finiteCandidateFixedPriceBenchmark values 1 / cutoff) := by
    have htruncated_to_original :
        totalBidValue normalized ≤
          (2 * Real.logb 2 cardR) *
            (finiteCandidateFixedPriceBenchmark values 1 / cutoff) := by
      exact htruncated_exact.trans
        (mul_le_mul_of_nonneg_left hbenchmark_scaled_div
          htruncated_coefficient_nonneg)
    nlinarith
  calc
    totalBidValue values = (totalBidValue values / cutoff) * cutoff := by
      field_simp [ne_of_gt hcutoff_pos]
    _ ≤ ((4 * Real.logb 2 cardR) *
          (finiteCandidateFixedPriceBenchmark values 1 / cutoff)) * cutoff :=
      mul_le_mul_of_nonneg_right hscaled_bound (le_of_lt hcutoff_pos)
    _ = (4 * Real.logb 2 cardR) * finiteCandidateFixedPriceBenchmark values 1 := by
      field_simp [ne_of_gt hcutoff_pos]
    _ = (4 * Real.logb 2 (Fintype.card Agent : ℝ)) *
          finiteCandidateFixedPriceBenchmark values 1 := by
      rfl

/--
GHW Theorem 7.1 with the paper's dyadic bins constructed internally from a
power-of-two high-bid certificate. If all bids lie in `[1, 2^(m+1)]` and
`4 * 2^(m+1) <= T`, the weighted-pairing revenue satisfies the Section 7.1
bound with `m+1` bins.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ) {totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hlarge : 4 * (2 : ℝ) ^ (m + 1) ≤ totalValue) :
    totalValue ≤
      192 * ((m + 1 : ℕ) : ℝ) * weightedPairingExpectedRevenue values := by
  classical
  let Bin := Fin (m + 1)
  let hExists :
      ∀ i : Agent, ∃ j : Bin,
        (2 : ℝ) ^ j.val ≤ values i ∧
          values i ≤ 2 * (2 : ℝ) ^ j.val := fun i =>
    paper_theorem7_dyadicIndex_exists_of_power_two_bound
      m (hvalue_ge_one i) (hvalue_le_power i)
  let binOf : Agent → Bin := fun i => Classical.choose (hExists i)
  let binFloor : Bin → ℝ := fun j => (2 : ℝ) ^ j.val
  let bins : Bin → Finset Agent := fun j =>
    (Finset.univ : Finset Agent).filter fun i => binOf i = j
  have hvalues_nonneg : ∀ i : Agent, 0 ≤ values i := by
    intro i
    linarith [hvalue_ge_one i]
  have hfloor_nonneg : ∀ j : Bin, 0 ≤ binFloor j := by
    intro j
    dsimp [binFloor]
    positivity
  have hsingleton_floor_sum :
      (∑ j : {j : Bin // ((bins j).card) ≤ 1}, binFloor j.1) ≤
        (2 : ℝ) ^ (m + 1) := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun j : Bin => (bins j).card ≤ 1) (f := binFloor)
    have hcomp_nonneg :
        0 ≤ ∑ j : {j : Bin // ¬ (bins j).card ≤ 1}, binFloor j.1 := by
      exact Finset.sum_nonneg fun j _ => hfloor_nonneg j.1
    have hsub_le :
        (∑ j : {j : Bin // (bins j).card ≤ 1}, binFloor j.1) ≤
          ∑ j : Bin, binFloor j := by
      nlinarith [hsplit, hcomp_nonneg]
    have hall_le : (∑ j : Bin, binFloor j) ≤ (2 : ℝ) ^ (m + 1) := by
      simpa [Bin, binFloor, Fin.sum_univ_eq_sum_range] using
        paper_aux_sum_range_two_pow_le (m + 1)
    exact le_trans hsub_le hall_le
  have hfloor_pos :
      ∀ j : Bin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j := by
    intro j _hj
    dsimp [binFloor]
    positivity
  have hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i := by
    intro i
    exact (Classical.choose_spec (hExists i)).1
  have hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i) := by
    intro i
    exact (Classical.choose_spec (hExists i)).2
  have hcard_le : (Fintype.card Bin : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    simp [Bin]
  exact
    paper_theorem7_1_weighted_pairing_log_bound_from_classifier
      (Agent := Agent) (AllBin := Bin)
      values binOf binFloor htotal hvalues_nonneg (by positivity)
      hvalue_le_power hfloor_nonneg (by simpa [bins] using hsingleton_floor_sum)
      hlarge hfloor_pos hfloor_le hfactor_two hcard_le

/--
GHW Theorem 7.1 log-certificate form. The dyadic proof uses `m+1` bins; this
wrapper exposes any larger paper-facing logarithmic bound `logH`.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_from_log_certificate
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ) {totalValue logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hlarge : 4 * (2 : ℝ) ^ (m + 1) ≤ totalValue)
    (hlog_le_logH : ((m + 1 : ℕ) : ℝ) ≤ logH) :
    totalValue ≤
      192 * logH * weightedPairingExpectedRevenue values := by
  have hbase :
      totalValue ≤
        192 * ((m + 1 : ℕ) : ℝ) *
          weightedPairingExpectedRevenue values :=
    paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins
      values m htotal hvalue_ge_one hvalue_le_power hlarge
  have hH_lt_total : (2 : ℝ) ^ (m + 1) < totalValue := by
    have hH_pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    by
      intro i
      rw [← htotal]
      nlinarith [hvalue_le_power i]
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hcoef :
      192 * ((m + 1 : ℕ) : ℝ) ≤ 192 * logH := by
    nlinarith
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right hcoef hW_nonneg)

/--
Power-of-two ceiling bound used to convert rounded dyadic certificates into
paper-style `log_2 h` notation.
-/
theorem paper_two_pow_nat_ceil_logb_le_two_mul {h : ℝ}
    (hh_ge_one : 1 ≤ h) :
    (2 : ℝ) ^ Nat.ceil (Real.logb 2 h) ≤ 2 * h := by
  let m : ℕ := Nat.ceil (Real.logb 2 h)
  have hh_pos : 0 < h := lt_of_lt_of_le zero_lt_one hh_ge_one
  have hlog_nonneg : 0 ≤ Real.logb 2 h :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hh_ge_one
  have hm_lt : (m : ℝ) < Real.logb 2 h + 1 := by
    simpa [m] using Nat.ceil_lt_add_one hlog_nonneg
  have hpow_lt :
      (2 : ℝ) ^ (m : ℝ) < (2 : ℝ) ^ (Real.logb 2 h + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hm_lt
  have hpow_eq :
      (2 : ℝ) ^ (Real.logb 2 h + 1) = h * 2 := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hh_pos]
    norm_num
  have hpow_nat_eq : (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
  rw [hpow_nat_eq]
  exact le_trans (le_of_lt hpow_lt) (by nlinarith)

/--
GHW Theorem 7.1 rounded `log_2 h` form. If bids lie in `[1,h]`, `1 <= h`,
and the total value satisfies the paper large-market condition (`4h <= T`),
then the weighted-pairing revenue satisfies the paper-style logarithmic bound
with `log_2 h + 2`.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hlarge : 4 * h ≤ totalValue) :
    totalValue ≤
      192 * (Real.logb 2 h + 2) *
        weightedPairingExpectedRevenue values := by
  classical
  let m : ℕ := Nat.ceil (Real.logb 2 h)
  let Bin := Fin (m + 1)
  have hh_pos : 0 < h := lt_of_lt_of_le zero_lt_one hh_ge_one
  have hlog_nonneg : 0 ≤ Real.logb 2 h :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hh_ge_one
  have hlog_le_m : Real.logb 2 h ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hh_le_rpow : h ≤ (2 : ℝ) ^ (m : ℝ) :=
    (Real.logb_le_iff_le_rpow
      (b := 2) (by norm_num : (1 : ℝ) < 2) hh_pos).mp hlog_le_m
  have hh_le_pow : h ≤ (2 : ℝ) ^ m := by
    simpa [Real.rpow_natCast] using hh_le_rpow
  let binFloor : Bin → ℝ := fun j => h / (2 * (2 : ℝ) ^ j.val)
  have hExists :
      ∀ i : Agent, ∃ j : Bin,
        binFloor j ≤ values i ∧ values i ≤ 2 * binFloor j := by
    intro i
    have hvi_pos : 0 < values i := lt_of_lt_of_le zero_lt_one (hvalue_ge_one i)
    have hy_low : 1 ≤ h / values i := by
      exact (le_div_iff₀ hvi_pos).mpr (by simpa using hvalue_le_h i)
    have hy_le_h : h / values i ≤ h := by
      exact (div_le_iff₀ hvi_pos).mpr (by nlinarith [hh_pos, hvalue_ge_one i])
    have hy_high : h / values i ≤ (2 : ℝ) ^ (m + 1) := by
      have hpow_m_le_succ : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ m)
      exact le_trans hy_le_h (le_trans hh_le_pow hpow_m_le_succ)
    obtain ⟨j, hj_low, hj_high⟩ :=
      paper_theorem7_dyadicIndex_exists_of_power_two_bound
        m hy_low hy_high
    refine ⟨j, ?_, ?_⟩
    · have hden_pos : 0 < 2 * (2 : ℝ) ^ j.val := by positivity
      have hmul : h ≤ values i * (2 * (2 : ℝ) ^ j.val) := by
        have := (div_le_iff₀ hvi_pos).mp hj_high
        nlinarith
      exact (div_le_iff₀ hden_pos).mpr hmul
    · have hpow_pos : 0 < (2 : ℝ) ^ j.val := by positivity
      have hmul : values i * (2 : ℝ) ^ j.val ≤ h := by
        have := (le_div_iff₀ hvi_pos).mp hj_low
        nlinarith
      have hv_le : values i ≤ h / (2 : ℝ) ^ j.val :=
        (le_div_iff₀ hpow_pos).mpr hmul
      have htwo_floor :
          2 * binFloor j = h / (2 : ℝ) ^ j.val := by
        dsimp [binFloor]
        field_simp [(ne_of_gt hpow_pos)]
      simpa [htwo_floor]
  let binOf : Agent → Bin := fun i => Classical.choose (hExists i)
  let bins : Bin → Finset Agent := fun j =>
    (Finset.univ : Finset Agent).filter fun i => binOf i = j
  have hvalues_nonneg : ∀ i : Agent, 0 ≤ values i := by
    intro i
    linarith [hvalue_ge_one i]
  have hfloor_nonneg : ∀ j : Bin, 0 ≤ binFloor j := by
    intro j
    dsimp [binFloor]
    positivity
  have hsingleton_floor_sum :
      (∑ j : {j : Bin // ((bins j).card) ≤ 1}, binFloor j.1) ≤ h := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun j : Bin => (bins j).card ≤ 1) (f := binFloor)
    have hcomp_nonneg :
        0 ≤ ∑ j : {j : Bin // ¬ (bins j).card ≤ 1}, binFloor j.1 := by
      exact Finset.sum_nonneg fun j _ => hfloor_nonneg j.1
    have hsub_le :
        (∑ j : {j : Bin // (bins j).card ≤ 1}, binFloor j.1) ≤
          ∑ j : Bin, binFloor j := by
      nlinarith [hsplit, hcomp_nonneg]
    have hall_le : (∑ j : Bin, binFloor j) ≤ h := by
      have hsum_range :
          (∑ j : Bin, binFloor j) =
            ∑ k ∈ Finset.range (m + 1),
              h / (2 * (2 : ℝ) ^ k) := by
        simpa [Bin, binFloor] using
          (Fin.sum_univ_eq_sum_range (n := m + 1)
            (fun k : ℕ => h / (2 * (2 : ℝ) ^ k)))
      rw [hsum_range]
      have hgeom :
          (∑ k ∈ Finset.range (m + 1),
              h / (2 * (2 : ℝ) ^ k)) =
            h * ∑ k ∈ Finset.range (m + 1),
              ((1 / 2 : ℝ) ^ (k + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hpow_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        rw [one_div_pow, pow_succ]
        field_simp [hpow_ne]
      have hhalf_sum :
          (∑ k ∈ Finset.range (m + 1),
              ((1 / 2 : ℝ) ^ (k + 1))) ≤ 1 := by
        have hsum_shift :
            (∑ k ∈ Finset.range (m + 1),
                ((1 / 2 : ℝ) ^ (k + 1))) =
              (∑ k ∈ Finset.range (m + 1),
                ((1 / 2 : ℝ) ^ k)) * (1 / 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [pow_succ]
        have hgeom_sum :
            (∑ k ∈ Finset.range (m + 1),
                ((1 / 2 : ℝ) ^ k)) * (1 / 2) =
              1 - (1 / 2 : ℝ) ^ (m + 1) := by
          have hraw := geom_sum_mul_neg (1 / 2 : ℝ) (m + 1)
          norm_num at hraw ⊢
          simpa using hraw
        rw [hsum_shift, hgeom_sum]
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
        nlinarith
      calc
        (∑ k ∈ Finset.range (m + 1),
              h / (2 * (2 : ℝ) ^ k))
            = h * ∑ k ∈ Finset.range (m + 1),
                ((1 / 2 : ℝ) ^ (k + 1)) := hgeom
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left hhalf_sum (le_of_lt hh_pos)
        _ = h := by ring
    exact le_trans hsub_le hall_le
  have hfloor_pos :
      ∀ j : Bin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j := by
    intro j _hj
    dsimp [binFloor]
    positivity
  have hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i := by
    intro i
    exact (Classical.choose_spec (hExists i)).1
  have hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i) := by
    intro i
    exact (Classical.choose_spec (hExists i)).2
  have hcount_le :
      (Fintype.card Bin : ℝ) ≤ Real.logb 2 h + 2 := by
    have hceil_lt : (m : ℝ) < Real.logb 2 h + 1 := by
      simpa [m] using Nat.ceil_lt_add_one hlog_nonneg
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
    simpa [Bin, hcast] using (by nlinarith : ((m + 1 : ℕ) : ℝ) ≤ Real.logb 2 h + 2)
  exact
    paper_theorem7_1_weighted_pairing_log_bound_from_classifier
      (Agent := Agent) (AllBin := Bin)
      values binOf binFloor htotal hvalues_nonneg hh_pos hvalue_le_h
      hfloor_nonneg (by simpa [bins] using hsingleton_floor_sum)
      hlarge hfloor_pos hfloor_le hfactor_two hcount_le

/--
Paper-facing high-value model for GHW Theorem 7.1. The rounded dyadic endpoint
uses relative factor-two bins, so the large-market hypothesis is the paper
condition `4h <= T`; the logarithmic coefficient remains rounded as
`log_2 h + 2`.
-/
structure PaperTheorem71WeightedPairingHighValueModel
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent] where
  values : Agent → ℝ
  highValue : ℝ
  totalValue : ℝ
  total_value_eq : totalValue = totalBidValue values
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue
  large_market : 4 * highValue ≤ totalValue

/--
GHW Theorem 7.1 high-value paper-model form: under the rounded dyadic
high-value model, weighted pairing obtains the logarithmic revenue bound.
-/
theorem paper_theorem7_1_weighted_pairing_log_bound_of_high_value_model
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (model : PaperTheorem71WeightedPairingHighValueModel Agent) :
    model.totalValue ≤
      192 * (Real.logb 2 model.highValue + 2) *
        weightedPairingExpectedRevenue model.values := by
  exact
    paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
      model.values model.total_value_eq model.highValue_ge_one
      model.values_ge_one model.values_le_highValue model.large_market

/--
GHW Theorem 7.2 first-case algebra. If the Section 7.1 bound gives
`T <= 192 * s^2 * W` and the fixed-price benchmark satisfies `F <= T / s`,
then `F <= 192 * s * W`. In the paper this is the case `F <= T / sqrt(log h)`.
-/
theorem paper_theorem7_2_first_case_from_theorem7_1
    {totalValue fixedPriceBenchmark weightedRevenue s : ℝ}
    (hs_pos : 0 < s)
    (hweighted :
      totalValue ≤ 192 * (s ^ 2) * weightedRevenue)
    (hcase : fixedPriceBenchmark ≤ totalValue / s) :
    fixedPriceBenchmark ≤ 192 * s * weightedRevenue := by
  have hmul : fixedPriceBenchmark * s ≤ totalValue := by
    exact (le_div_iff₀ hs_pos).mp hcase
  have hweighted' :
      totalValue ≤ (192 * s * weightedRevenue) * s := by
    calc
      totalValue ≤ 192 * (s ^ 2) * weightedRevenue := hweighted
      _ = (192 * s * weightedRevenue) * s := by ring
  exact
    le_of_mul_le_mul_right
      (a := s) (b := fixedPriceBenchmark)
      (c := 192 * s * weightedRevenue)
      (le_trans hmul hweighted') hs_pos

/--
GHW Theorem 7.2 case split. The first branch uses Theorem 7.1 when
`F <= T/s`; the second branch supplies the largest-bucket proof when
`T <= sF`.
-/
theorem paper_theorem7_2_case_split_from_first_second
    {totalValue fixedPriceBenchmark weightedRevenue s : ℝ}
    (hs_pos : 0 < s)
    (hW_nonneg : 0 ≤ weightedRevenue)
    (hweighted :
      totalValue ≤ 192 * (s ^ 2) * weightedRevenue)
    (hsecond :
      totalValue ≤ s * fixedPriceBenchmark →
        fixedPriceBenchmark ≤ 576 * s * weightedRevenue) :
    fixedPriceBenchmark ≤ 576 * s * weightedRevenue := by
  by_cases hfirst_case : fixedPriceBenchmark ≤ totalValue / s
  · have hfirst :
        fixedPriceBenchmark ≤ 192 * s * weightedRevenue :=
      paper_theorem7_2_first_case_from_theorem7_1
        hs_pos hweighted hfirst_case
    have hscale_nonneg : 0 ≤ s * weightedRevenue :=
      mul_nonneg (le_of_lt hs_pos) hW_nonneg
    have hfirst_le_target :
        192 * s * weightedRevenue ≤ 576 * s * weightedRevenue := by
      nlinarith
    exact le_trans hfirst hfirst_le_target
  · have hlt : totalValue / s < fixedPriceBenchmark :=
      lt_of_not_ge hfirst_case
    have hcase : totalValue ≤ s * fixedPriceBenchmark := by
      have hmul : totalValue < fixedPriceBenchmark * s :=
        (div_lt_iff₀ hs_pos).mp hlt
      nlinarith
    exact hsecond hcase

/--
Weighted-pairing denominator positivity follows if every bid is strictly below
the total bid value.
-/
theorem paper_weighted_pairing_den_pos_of_value_lt_total
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ)
    {totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_lt_total : ∀ i : Agent, values i < totalValue) :
    ∀ i : Agent, 0 < totalBidValue values - values i := by
  intro i
  rw [← htotal]
  linarith [hvalue_lt_total i]

/--
Paper-style denominator positivity: if all bids are at most `h` and `h < T`,
then every weighted-pairing denominator `T - b_i` is positive.
-/
theorem paper_weighted_pairing_den_pos_of_high_value_bound
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ)
    {totalValue h : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hh_lt_total : h < totalValue) :
    ∀ i : Agent, 0 < totalBidValue values - values i := by
  exact paper_weighted_pairing_den_pos_of_value_lt_total values htotal
    (fun i => lt_of_le_of_lt (hvalue_le_h i) hh_lt_total)

/--
GHW Theorem 7.2 cross-bucket revenue lower bound. If every low-half bucket bid
has value at least `t`, every high-half bucket bid beats every low-half bid, and
the selected high-low ordered pairs are disjointly embedded in the bidder set,
then the weighted-pairing revenue is at least the contribution of those
selected pairs.
-/
theorem paper_theorem7_2_cross_bucket_revenue_lower_bound
    {Agent High Low : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype High] [Fintype Low]
    (values : Agent → ℝ)
    (highAgent : High → Agent) (lowAgent : Low → Agent)
    {totalValue t : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (ht_nonneg : 0 ≤ t)
    (hlow_floor : ∀ l : Low, t ≤ values (lowAgent l))
    (hhigh_nonneg : ∀ h : High, 0 ≤ values (highAgent h))
    (hwin : ∀ h : High, ∀ l : Low,
      values (lowAgent l) ≤ values (highAgent h))
    (hdisjoint : ∀ h : High, ∀ l : Low, lowAgent l ≠ highAgent h)
    (hpair_injective :
      Function.Injective
        (fun x : High × Low => (highAgent x.1, lowAgent x.2)))
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i) :
    ((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
        (t ^ 2 / totalValue) ≤
      weightedPairingExpectedRevenue values := by
  classical
  let pairAgent : High × Low → Agent × Agent := fun x =>
    (highAgent x.1, lowAgent x.2)
  let keptPayment : High × Low → ℝ := fun _ =>
    t ^ 2 / totalValue
  let fullPayment : Agent × Agent → ℝ := fun p =>
    if p.2 ≠ p.1 ∧ values p.2 ≤ values p.1 then
      values p.2 ^ 2 / (totalBidValue values - values p.1)
    else 0
  have htotalBid_pos : 0 < totalBidValue values := by
    rw [← htotal]
    exact htotal_pos
  have hfull_nonneg : ∀ p : Agent × Agent, 0 ≤ fullPayment p := by
    intro p
    by_cases hp : p.2 ≠ p.1 ∧ values p.2 ≤ values p.1
    · simp [fullPayment, hp,
        div_nonneg (sq_nonneg (values p.2))
          (le_of_lt (hden_pos_agent p.1))]
    · simp [fullPayment, hp]
  have hkept_le_full :
      ∀ x : High × Low, keptPayment x ≤ fullPayment (pairAgent x) := by
    intro x
    rcases x with ⟨h, l⟩
    have hne : lowAgent l ≠ highAgent h := hdisjoint h l
    have hle : values (lowAgent l) ≤ values (highAgent h) := hwin h l
    have hlow_sq : t ^ 2 ≤ values (lowAgent l) ^ 2 := by
      nlinarith [hlow_floor l, ht_nonneg]
    have hden_le_total :
        totalBidValue values - values (highAgent h) ≤ totalValue := by
      rw [htotal]
      linarith [hhigh_nonneg h]
    have hto_low :
        t ^ 2 / totalValue ≤ values (lowAgent l) ^ 2 / totalValue := by
      exact div_le_div_of_nonneg_right hlow_sq (le_of_lt htotal_pos)
    have hto_den :
        values (lowAgent l) ^ 2 / totalValue ≤
          values (lowAgent l) ^ 2 /
            (totalBidValue values - values (highAgent h)) := by
      exact
        div_le_div_of_nonneg_left
          (sq_nonneg (values (lowAgent l))) (hden_pos_agent (highAgent h))
          hden_le_total
    have hfull_eq :
        fullPayment (pairAgent (h, l)) =
          values (lowAgent l) ^ 2 /
            (totalBidValue values - values (highAgent h)) := by
      simp [fullPayment, pairAgent, hne, hle]
    rw [hfull_eq]
    exact le_trans hto_low hto_den
  have hsub :
      (∑ x : High × Low, keptPayment x) ≤
        ∑ p : Agent × Agent, fullPayment p :=
    FiniteSum.sum_le_sum_of_injective_nonneg
      pairAgent hpair_injective hkept_le_full hfull_nonneg
  have hkept_sum :
      (∑ x : High × Low, keptPayment x) =
        ((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
          (t ^ 2 / totalValue) := by
    simp [keptPayment, mul_assoc]
  rw [← hkept_sum]
  exact
    le_trans hsub
      (by
        simpa [fullPayment, pairAgent, weightedPairingExpectedRevenue,
          weightedPairingExpectedPayment, Fintype.sum_prod_type] using le_rfl)

/--
GHW Theorem 7.2 second-case algebra. If a bucket certificate gives
`crossMass / T <= W`, the paper's second case gives `T <= sF`, and the bucket
split has enough mass `F^2 <= C * crossMass`, then `F <= C * s * W`.
-/
theorem paper_theorem7_2_second_case_from_cross_bucket
    {totalValue fixedPriceBenchmark weightedRevenue s crossMass C : ℝ}
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hC_nonneg : 0 ≤ C)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (hW_nonneg : 0 ≤ weightedRevenue)
    (hcross_revenue : crossMass / totalValue ≤ weightedRevenue)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hcross_mass : fixedPriceBenchmark ^ 2 ≤ C * crossMass) :
    fixedPriceBenchmark ≤ C * s * weightedRevenue := by
  by_cases hF_zero : fixedPriceBenchmark = 0
  · subst fixedPriceBenchmark
    nlinarith
  · have hF_pos : 0 < fixedPriceBenchmark :=
      lt_of_le_of_ne hF_nonneg (Ne.symm hF_zero)
    have hcross_le :
        crossMass ≤ totalValue * weightedRevenue := by
      have h := (div_le_iff₀ htotal_pos).mp hcross_revenue
      nlinarith
    have hCcross_le :
        C * crossMass ≤ C * (totalValue * weightedRevenue) :=
      mul_le_mul_of_nonneg_left hcross_le hC_nonneg
    have hT_to_case :
        totalValue * weightedRevenue ≤
          (s * fixedPriceBenchmark) * weightedRevenue :=
      mul_le_mul_of_nonneg_right hcase hW_nonneg
    have hCT_to_case :
        C * (totalValue * weightedRevenue) ≤
          C * ((s * fixedPriceBenchmark) * weightedRevenue) :=
      mul_le_mul_of_nonneg_left hT_to_case hC_nonneg
    have hsq_le :
        fixedPriceBenchmark * fixedPriceBenchmark ≤
          (C * s * weightedRevenue) * fixedPriceBenchmark := by
      nlinarith [hcross_mass, hCcross_le, hCT_to_case]
    exact
      le_of_mul_le_mul_right
        (a := fixedPriceBenchmark) (b := fixedPriceBenchmark)
        (c := C * s * weightedRevenue) hsq_le hF_pos

/--
GHW Theorem 7.2 second-case bucket certificate for the concrete weighted
pairing auction. This combines the high-low bucket selected-pair lower bound
with the second-case algebra.
-/
theorem paper_theorem7_2_second_case_bucket_certificate
    {Agent High Low : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype High] [Fintype Low]
    (values : Agent → ℝ)
    (highAgent : High → Agent) (lowAgent : Low → Agent)
    {totalValue fixedPriceBenchmark s t C : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hC_nonneg : 0 ≤ C)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hlow_floor : ∀ l : Low, t ≤ values (lowAgent l))
    (hhigh_nonneg : ∀ h : High, 0 ≤ values (highAgent h))
    (hwin : ∀ h : High, ∀ l : Low,
      values (lowAgent l) ≤ values (highAgent h))
    (hdisjoint : ∀ h : High, ∀ l : Low, lowAgent l ≠ highAgent h)
    (hpair_injective :
      Function.Injective
        (fun x : High × Low => (highAgent x.1, lowAgent x.2)))
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hcross_mass :
      fixedPriceBenchmark ^ 2 ≤
        C * (((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
          t ^ 2)) :
    fixedPriceBenchmark ≤
      C * s * weightedPairingExpectedRevenue values := by
  have hcross_lower :
      ((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
          (t ^ 2 / totalValue) ≤
        weightedPairingExpectedRevenue values :=
    paper_theorem7_2_cross_bucket_revenue_lower_bound
      values highAgent lowAgent htotal htotal_pos ht_nonneg hlow_floor
      hhigh_nonneg hwin hdisjoint hpair_injective hden_pos_agent
  have hcross_revenue :
      (((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
          t ^ 2) / totalValue ≤
        weightedPairingExpectedRevenue values := by
    have hrewrite :
        (((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
            t ^ 2) / totalValue =
          ((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) *
            (t ^ 2 / totalValue) := by
      ring
    rw [hrewrite]
    exact hcross_lower
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  exact
    paper_theorem7_2_second_case_from_cross_bucket
      htotal_pos hs_pos hC_nonneg hF_nonneg hW_nonneg hcross_revenue
      hcase hcross_mass

/--
GHW Theorem 7.2 bucket split algebra. If the high and low halves of a bucket
each contain enough floor mass to cover the fixed-price benchmark up to
constants `A` and `B`, then their selected high-low cross mass is large enough
for the second-case certificate.
-/
theorem paper_theorem7_2_cross_mass_from_split_size_bounds
    {fixedPriceBenchmark highCount lowCount t A B : ℝ}
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hhigh_nonneg : 0 ≤ highCount)
    (hlow_nonneg : 0 ≤ lowCount)
    (ht_nonneg : 0 ≤ t)
    (hF_high : fixedPriceBenchmark ≤ A * (highCount * t))
    (hF_low : fixedPriceBenchmark ≤ B * (lowCount * t)) :
    fixedPriceBenchmark ^ 2 ≤
      (A * B) * (highCount * lowCount * t ^ 2) := by
  have hright_nonneg : 0 ≤ B * (lowCount * t) :=
    mul_nonneg hB_nonneg (mul_nonneg hlow_nonneg ht_nonneg)
  have hleft_nonneg : 0 ≤ A * (highCount * t) :=
    mul_nonneg hA_nonneg (mul_nonneg hhigh_nonneg ht_nonneg)
  have hmul :=
    mul_le_mul hF_high hF_low hF_nonneg hleft_nonneg
  nlinarith

/--
GHW Theorem 7.2 second-case split-bucket certificate. This combines the
high-low selected-pair revenue bound with the split-size algebra: proving that
both halves of the bucket carry enough floor mass is enough to get the
`F <= O(sW)` guarantee.
-/
theorem paper_theorem7_2_second_case_bucket_split_certificate
    {Agent High Low : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype High] [Fintype Low]
    (values : Agent → ℝ)
    (highAgent : High → Agent) (lowAgent : Low → Agent)
    {totalValue fixedPriceBenchmark s t A B : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hlow_floor : ∀ l : Low, t ≤ values (lowAgent l))
    (hhigh_nonneg : ∀ h : High, 0 ≤ values (highAgent h))
    (hwin : ∀ h : High, ∀ l : Low,
      values (lowAgent l) ≤ values (highAgent h))
    (hdisjoint : ∀ h : High, ∀ l : Low, lowAgent l ≠ highAgent h)
    (hpair_injective :
      Function.Injective
        (fun x : High × Low => (highAgent x.1, lowAgent x.2)))
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_high :
      fixedPriceBenchmark ≤ A * ((Fintype.card High : ℝ) * t))
    (hF_low :
      fixedPriceBenchmark ≤ B * ((Fintype.card Low : ℝ) * t)) :
    fixedPriceBenchmark ≤
      (A * B) * s * weightedPairingExpectedRevenue values := by
  have hcard_high_nonneg : 0 ≤ (Fintype.card High : ℝ) := by positivity
  have hcard_low_nonneg : 0 ≤ (Fintype.card Low : ℝ) := by positivity
  have hcross_mass :
      fixedPriceBenchmark ^ 2 ≤
        (A * B) *
          (((Fintype.card High : ℝ) * (Fintype.card Low : ℝ)) * t ^ 2) :=
    paper_theorem7_2_cross_mass_from_split_size_bounds
      hF_nonneg hA_nonneg hB_nonneg hcard_high_nonneg hcard_low_nonneg
      ht_nonneg hF_high hF_low
  exact
    paper_theorem7_2_second_case_bucket_certificate
      values highAgent lowAgent htotal htotal_pos hs_pos
      (mul_nonneg hA_nonneg hB_nonneg) hF_nonneg ht_nonneg hlow_floor
      hhigh_nonneg hwin hdisjoint hpair_injective hden_pos_agent hcase
      hcross_mass

/--
GHW Theorem 7.2 second-case split-bucket finset wrapper. This removes the
explicit high/low index types and pair-injection certificate by taking the
bucket halves as actual disjoint finsets of bidders.
-/
theorem paper_theorem7_2_second_case_bucket_split_finsets
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (high low : Finset Agent)
    {totalValue fixedPriceBenchmark s t A B : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hlow_floor : ∀ i : Agent, i ∈ low → t ≤ values i)
    (hhigh_nonneg : ∀ i : Agent, i ∈ high → 0 ≤ values i)
    (hwin : ∀ h : Agent, h ∈ high → ∀ l : Agent, l ∈ low →
      values l ≤ values h)
    (hdisjoint : ∀ i : Agent, i ∈ low → i ∈ high → False)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_high :
      fixedPriceBenchmark ≤ A * ((high.card : ℝ) * t))
    (hF_low :
      fixedPriceBenchmark ≤ B * ((low.card : ℝ) * t)) :
    fixedPriceBenchmark ≤
      (A * B) * s * weightedPairingExpectedRevenue values := by
  classical
  let HighSet := {i : Agent // i ∈ high}
  let LowSet := {i : Agent // i ∈ low}
  let highAgent : HighSet → Agent := fun i => i.1
  let lowAgent : LowSet → Agent := fun i => i.1
  have hlow_floor' : ∀ l : LowSet, t ≤ values (lowAgent l) := by
    intro l
    exact hlow_floor l.1 l.2
  have hhigh_nonneg' : ∀ h : HighSet, 0 ≤ values (highAgent h) := by
    intro h
    exact hhigh_nonneg h.1 h.2
  have hwin' : ∀ h : HighSet, ∀ l : LowSet,
      values (lowAgent l) ≤ values (highAgent h) := by
    intro h l
    exact hwin h.1 h.2 l.1 l.2
  have hdisjoint' : ∀ h : HighSet, ∀ l : LowSet,
      lowAgent l ≠ highAgent h := by
    intro h l heq
    exact hdisjoint l.1 l.2 (by simpa [highAgent, lowAgent, heq] using h.2)
  have hpair_injective :
      Function.Injective
        (fun x : HighSet × LowSet => (highAgent x.1, lowAgent x.2)) := by
    intro x y hxy
    rcases x with ⟨h₁, l₁⟩
    rcases y with ⟨h₂, l₂⟩
    have hh : h₁.1 = h₂.1 := congrArg Prod.fst hxy
    have hl : l₁.1 = l₂.1 := congrArg Prod.snd hxy
    cases Subtype.ext hh
    cases Subtype.ext hl
    rfl
  have hcard_high : Fintype.card HighSet = high.card := by
    exact Fintype.card_of_subtype high (by intro i; rfl)
  have hcard_low : Fintype.card LowSet = low.card := by
    exact Fintype.card_of_subtype low (by intro i; rfl)
  have hF_high' :
      fixedPriceBenchmark ≤ A * ((Fintype.card HighSet : ℝ) * t) := by
    simpa [hcard_high] using hF_high
  have hF_low' :
      fixedPriceBenchmark ≤ B * ((Fintype.card LowSet : ℝ) * t) := by
    simpa [hcard_low] using hF_low
  exact
    paper_theorem7_2_second_case_bucket_split_certificate
      (Agent := Agent) (High := HighSet) (Low := LowSet)
      values highAgent lowAgent htotal htotal_pos hs_pos hA_nonneg
      hB_nonneg hF_nonneg ht_nonneg hlow_floor' hhigh_nonneg' hwin'
      hdisjoint' hpair_injective hden_pos_agent hcase hF_high' hF_low'

/--
GHW Theorem 7.2 second-case one-bucket rank split. Given one factor-two bucket,
split it by sorted rank at `cut`; the lower ranks form `M''`, the upper ranks
form `M'`, and the high-low order/disjointness facts are derived internally.
-/
theorem paper_theorem7_2_second_case_rank_split_bucket
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket : Finset Agent) (cut : ℕ)
    {totalValue fixedPriceBenchmark s t A B : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hA_nonneg : 0 ≤ A)
    (hB_nonneg : 0 ≤ B)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_high :
      fixedPriceBenchmark ≤
        A * (((FiniteRanking.upperRankFinset
          (s := bucket) (value := values) rfl cut).card : ℝ) * t))
    (hF_low :
      fixedPriceBenchmark ≤
        B * (((FiniteRanking.lowerRankFinset
          (s := bucket) (value := values) rfl cut).card : ℝ) * t)) :
    fixedPriceBenchmark ≤
      (A * B) * s * weightedPairingExpectedRevenue values := by
  classical
  let high : Finset Agent :=
    FiniteRanking.upperRankFinset (s := bucket) (value := values) rfl cut
  let low : Finset Agent :=
    FiniteRanking.lowerRankFinset (s := bucket) (value := values) rfl cut
  have hlow_floor : ∀ i : Agent, i ∈ low → t ≤ values i := by
    intro i hi
    exact hbucket_floor i
      (FiniteRanking.lowerRankFinset_subset
        (s := bucket) (value := values) rfl cut hi)
  have hhigh_nonneg : ∀ i : Agent, i ∈ high → 0 ≤ values i := by
    intro i hi
    exact le_trans ht_nonneg
      (hbucket_floor i
        (FiniteRanking.upperRankFinset_subset
          (s := bucket) (value := values) rfl cut hi))
  have hwin : ∀ h : Agent, h ∈ high → ∀ l : Agent, l ∈ low →
      values l ≤ values h := by
    intro h hh l hl
    exact FiniteRanking.lowerRank_value_le_upperRank_value
      (s := bucket) (value := values) rfl cut h hh l hl
  have hdisjoint : ∀ i : Agent, i ∈ low → i ∈ high → False := by
    intro i hilow hihigh
    exact FiniteRanking.lowerRankFinset_disjoint_upperRankFinset
      (s := bucket) (value := values) rfl cut i hilow hihigh
  exact
    paper_theorem7_2_second_case_bucket_split_finsets
      values high low htotal htotal_pos hs_pos hA_nonneg hB_nonneg
      hF_nonneg ht_nonneg hlow_floor hhigh_nonneg hwin hdisjoint
      hden_pos_agent hcase (by simpa [high] using hF_high)
      (by simpa [low] using hF_low)

/--
GHW Theorem 7.2 geometric-tail algebra. If bucket floor masses are each at most
`maxFloorMass` and a tail revenue sequence loses a factor `1/2` at each higher
bucket, then the first tail is at most `2 * maxFloorMass`.
-/
theorem paper_theorem7_2_geometric_tail_le_two_max
    (floorMass tail : ℕ → ℝ) (n : ℕ) {maxFloorMass : ℝ}
    (hmax_nonneg : 0 ≤ maxFloorMass)
    (hmass_bound : ∀ j, j < n → floorMass j ≤ maxFloorMass)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    tail 0 ≤ 2 * maxFloorMass := by
  induction n generalizing floorMass tail with
  | zero =>
      calc
        tail 0 ≤ 0 := htail_end
        _ ≤ 2 * maxFloorMass := by nlinarith
  | succ n ih =>
      have htail_one : tail 1 ≤ 2 * maxFloorMass := by
        let floorMass' : ℕ → ℝ := fun j => floorMass (j + 1)
        let tail' : ℕ → ℝ := fun j => tail (j + 1)
        have hmass_bound' :
            ∀ j, j < n → floorMass' j ≤ maxFloorMass := by
          intro j hj
          exact hmass_bound (j + 1) (Nat.succ_lt_succ hj)
        have htail_end' : tail' n ≤ 0 := by
          simpa [tail'] using htail_end
        have hrec' : ∀ j, j < n →
            tail' j ≤ floorMass' j + (1 / 2) * tail' (j + 1) := by
          intro j hj
          simpa [floorMass', tail', Nat.add_assoc] using
            hrec (j + 1) (Nat.succ_lt_succ hj)
        simpa [tail'] using
          ih floorMass' tail' hmass_bound' htail_end' hrec'
      have htail_zero :
          tail 0 ≤ floorMass 0 + (1 / 2) * tail 1 := by
        exact hrec 0 (Nat.succ_pos n)
      have hmass_zero : floorMass 0 ≤ maxFloorMass :=
        hmass_bound 0 (Nat.succ_pos n)
      nlinarith

/--
GHW Theorem 7.2 largest-bucket floor-mass certificate. This is the algebra
behind the paper sentence "Recall that `|M| t = Ω(F)`": if the fixed-price
benchmark is within a factor two of the first dyadic tail, the dyadic tail
loses a factor `1/2` per bucket, and the chosen bucket is largest by total
value, then the chosen bucket's floor mass covers `F` up to constant `8`.
-/
theorem paper_theorem7_2_largest_bucket_floor_mass_certificate
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {fixedPriceBenchmark maxFloorMass selectedTotalMass selectedFloorMass : ℝ}
    (hmax_nonneg : 0 ≤ maxFloorMass)
    (hmass_bound : ∀ j, j < n → floorMass j ≤ maxFloorMass)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1))
    (hF_tail : fixedPriceBenchmark ≤ 2 * tail 0)
    (hmax_le_selected_total : maxFloorMass ≤ selectedTotalMass)
    (hselected_total_le_floor :
      selectedTotalMass ≤ 2 * selectedFloorMass) :
    fixedPriceBenchmark ≤ 8 * selectedFloorMass := by
  have htail_bound :
      tail 0 ≤ 2 * maxFloorMass :=
    paper_theorem7_2_geometric_tail_le_two_max
      floorMass tail n hmax_nonneg hmass_bound htail_end hrec
  nlinarith

/--
Finite dyadic geometric tail starting at bucket `start` and continuing for
`n` buckets. It represents
`mass_start + mass_{start+1}/2 + mass_{start+2}/4 + ...`.
-/
noncomputable def paper_theorem7_2_dyadicGeometricTail
    (floorMass : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _start => 0
  | n + 1, start =>
      floorMass start +
        (1 / 2) * paper_theorem7_2_dyadicGeometricTail floorMass n (start + 1)

/--
Closed finite-sum form of the dyadic geometric tail.
-/
theorem paper_theorem7_2_dyadicGeometricTail_eq_sum_range
    (floorMass : ℕ → ℝ) :
    ∀ n start : ℕ,
      paper_theorem7_2_dyadicGeometricTail floorMass n start =
        ∑ j ∈ Finset.range n, floorMass (start + j) / (2 : ℝ) ^ j := by
  intro n
  induction n with
  | zero =>
      intro start
      simp [paper_theorem7_2_dyadicGeometricTail]
  | succ n ih =>
      intro start
      rw [paper_theorem7_2_dyadicGeometricTail, ih (start + 1)]
      rw [Finset.sum_range_succ']
      have hsum :
          (∑ k ∈ Finset.range n,
              floorMass (start + (k + 1)) / (2 : ℝ) ^ (k + 1)) =
            (∑ k ∈ Finset.range n,
              floorMass (start + 1 + k) / (2 : ℝ) ^ k) *
              (1 / 2 : ℝ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro k _hk
        have hpow : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
          rw [pow_succ]
        rw [hpow]
        field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
        ring_nf
      rw [hsum]
      simp [Nat.add_comm, Nat.add_left_comm]
      ring

/--
A finite dyadic geometric tail is at most twice a uniform upper bound on the
bucket floor masses in its range.
-/
theorem paper_theorem7_2_dyadicGeometricTail_le_two_max
    (floorMass : ℕ → ℝ) {maxFloorMass : ℝ}
    (hmax_nonneg : 0 ≤ maxFloorMass) :
    ∀ n start : ℕ,
      (∀ j, start ≤ j → j < start + n → floorMass j ≤ maxFloorMass) →
        paper_theorem7_2_dyadicGeometricTail floorMass n start ≤
          2 * maxFloorMass := by
  intro n
  induction n with
  | zero =>
      intro start _hbound
      simp [paper_theorem7_2_dyadicGeometricTail]
      nlinarith
  | succ n ih =>
      intro start hbound
      have hmass_start : floorMass start ≤ maxFloorMass := by
        exact hbound start (le_rfl) (by omega)
      have htail :
          paper_theorem7_2_dyadicGeometricTail floorMass n (start + 1) ≤
            2 * maxFloorMass := by
        apply ih
        intro j hj_ge hj_lt
        exact hbound j (by omega) (by omega)
      simp [paper_theorem7_2_dyadicGeometricTail]
      nlinarith

/--
A finite dyadic geometric tail is strictly below twice a positive uniform upper
bound on the bucket floor masses. This is the strict version needed for the
paper's "`|M| = 1` would imply `F < 2h`" argument.
-/
theorem paper_theorem7_2_dyadicGeometricTail_lt_two_max
    (floorMass : ℕ → ℝ) {maxFloorMass : ℝ}
    (hmax_pos : 0 < maxFloorMass) :
    ∀ n start : ℕ,
      (∀ j, start ≤ j → j < start + n → floorMass j ≤ maxFloorMass) →
        paper_theorem7_2_dyadicGeometricTail floorMass n start <
          2 * maxFloorMass := by
  intro n
  induction n with
  | zero =>
      intro start _hbound
      simp [paper_theorem7_2_dyadicGeometricTail]
      nlinarith
  | succ n ih =>
      intro start hbound
      have hmass_start : floorMass start ≤ maxFloorMass := by
        exact hbound start (le_rfl) (by omega)
      have htail :
          paper_theorem7_2_dyadicGeometricTail floorMass n (start + 1) <
            2 * maxFloorMass := by
        apply ih
        intro j hj_ge hj_lt
        exact hbound j (by omega) (by omega)
      simp [paper_theorem7_2_dyadicGeometricTail]
      nlinarith

/--
If every bucket's `count * baseFloor` contribution is bounded by the
corresponding dyadic term, then the total bucket-count mass is bounded by the
canonical dyadic geometric tail.
-/
theorem paper_theorem7_2_dyadicGeometricTail_count_bound
    (floorMass countMass : ℕ → ℝ) (n : ℕ)
    (hcount_le :
      ∀ j, j < n → countMass j ≤ floorMass j / (2 : ℝ) ^ j) :
    (∑ j ∈ Finset.range n, countMass j) ≤
      paper_theorem7_2_dyadicGeometricTail floorMass n 0 := by
  rw [paper_theorem7_2_dyadicGeometricTail_eq_sum_range floorMass n 0]
  exact Finset.sum_le_sum fun j hj =>
    by simpa using hcount_le j (Finset.mem_range.mp hj)

/--
A tail set contained in a finite bucket union has count mass at most the sum of
the bucket count masses.
-/
theorem paper_theorem7_2_tail_count_cover_of_subset_biUnion
    {Agent : Type*} [DecidableEq Agent]
    (tailSet : Finset Agent) (buckets : ℕ → Finset Agent) (n : ℕ)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (htail_subset : tailSet ⊆ (Finset.range n).biUnion buckets) :
    ((tailSet.card : ℝ) * t) ≤
      ∑ j ∈ Finset.range n, ((buckets j).card : ℝ) * t := by
  have hcard_le_nat :
      tailSet.card ≤ (∑ j ∈ Finset.range n, (buckets j).card) := by
    exact le_trans (Finset.card_le_card htail_subset) Finset.card_biUnion_le
  have hcard_le_real :
      (tailSet.card : ℝ) ≤
        ∑ j ∈ Finset.range n, ((buckets j).card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hmul :
      (tailSet.card : ℝ) * t ≤
        (∑ j ∈ Finset.range n, ((buckets j).card : ℝ)) * t :=
    mul_le_mul_of_nonneg_right hcard_le_real ht_nonneg
  simpa [Finset.sum_mul] using hmul

/--
Concrete dyadic-tail count certificate from a finite family of tail buckets.
This is the paper step that the bidders accepting the fixed price are covered
by dyadic buckets above the selected scale.
-/
theorem paper_theorem7_2_tail_set_count_from_bucket_family
    {Agent : Type*} [DecidableEq Agent]
    (tailSet : Finset Agent) (buckets : ℕ → Finset Agent)
    (floorMass : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (htail_subset : tailSet ⊆ (Finset.range n).biUnion buckets)
    (hbucket_count_floor :
      ∀ j, j < n →
        ((buckets j).card : ℝ) * t ≤ floorMass j / (2 : ℝ) ^ j) :
    ((tailSet.card : ℝ) * t) ≤
      paper_theorem7_2_dyadicGeometricTail floorMass n 0 := by
  have hcover :
      ((tailSet.card : ℝ) * t) ≤
        ∑ j ∈ Finset.range n, ((buckets j).card : ℝ) * t :=
    paper_theorem7_2_tail_count_cover_of_subset_biUnion
      tailSet buckets n ht_nonneg htail_subset
  have htail :
      (∑ j ∈ Finset.range n, ((buckets j).card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_dyadicGeometricTail_count_bound
      floorMass (fun j => ((buckets j).card : ℝ) * t) n
      hbucket_count_floor
  exact le_trans hcover htail

/--
If every bidder in a bucket has value at least `scale * t`, then the bucket's
`card * t` count mass is bounded by its total value divided by `scale`.
-/
theorem paper_theorem7_2_bucket_count_mass_le_total_div_scale
    {Agent : Type*} (values : Agent → ℝ) (bucket : Finset Agent)
    {scale t : ℝ}
    (hscale_pos : 0 < scale)
    (hfloor : ∀ i : Agent, i ∈ bucket → scale * t ≤ values i) :
    ((bucket.card : ℝ) * t) ≤
      (∑ i ∈ bucket, values i) / scale := by
  have hsum_lower :
      (bucket.card : ℝ) * (scale * t) ≤
        ∑ i ∈ bucket, values i := by
    calc
      (bucket.card : ℝ) * (scale * t)
          = ∑ _i ∈ bucket, scale * t := by simp
      _ ≤ ∑ i ∈ bucket, values i := by
            exact Finset.sum_le_sum fun i hi => hfloor i hi
  rw [le_div_iff₀ hscale_pos]
  nlinarith

/--
Largest-bucket floor-mass certificate using the canonical finite dyadic
geometric tail, so callers do not need to supply a separate tail recurrence.
-/
theorem paper_theorem7_2_largest_bucket_floor_mass_from_geometric_tail
    (floorMass : ℕ → ℝ) (n : ℕ)
    {fixedPriceBenchmark maxFloorMass selectedTotalMass selectedFloorMass : ℝ}
    (hmax_nonneg : 0 ≤ maxFloorMass)
    (hmass_bound : ∀ j, j < n → floorMass j ≤ maxFloorMass)
    (hF_tail :
      fixedPriceBenchmark ≤
        2 * paper_theorem7_2_dyadicGeometricTail floorMass n 0)
    (hmax_le_selected_total : maxFloorMass ≤ selectedTotalMass)
    (hselected_total_le_floor :
      selectedTotalMass ≤ 2 * selectedFloorMass) :
    fixedPriceBenchmark ≤ 8 * selectedFloorMass := by
  have htail_bound :
      paper_theorem7_2_dyadicGeometricTail floorMass n 0 ≤
        2 * maxFloorMass :=
    paper_theorem7_2_dyadicGeometricTail_le_two_max
      floorMass hmax_nonneg n 0 (by
        intro j _hj_ge hj_lt
        exact hmass_bound j (by simpa using hj_lt))
  nlinarith

/--
If a fixed price `p` lies below twice a dyadic floor `t`, and the first tail
contains at least `t` times the number of bidders accepting `p`, then the
fixed-price revenue is at most twice that tail.
-/
theorem paper_theorem7_2_fixed_price_le_two_floor_tail
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) {fixedPriceBenchmark p t tail0 : ℝ}
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (htail_count : ((saleCount values p : ℝ) * t) ≤ tail0) :
    fixedPriceBenchmark ≤ 2 * tail0 := by
  rw [hF_eq, singlePriceRevenue_eq_saleCount_mul]
  have hcount_nonneg : 0 ≤ (saleCount values p : ℝ) := by positivity
  have hrev_le_floor :
      (saleCount values p : ℝ) * p ≤
        (saleCount values p : ℝ) * (2 * t) :=
    mul_le_mul_of_nonneg_left hp_le_two_t hcount_nonneg
  nlinarith

/--
In a factor-two dyadic bucket `[t, 2t]`, total bid value is at most twice the
bucket floor mass `|M| t`.
-/
theorem paper_theorem7_2_bucket_total_le_two_floor_mass
    {Agent : Type*} (values : Agent → ℝ) (bucket : Finset Agent) {t : ℝ}
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t) :
    (∑ i ∈ bucket, values i) ≤ 2 * ((bucket.card : ℝ) * t) := by
  calc
    (∑ i ∈ bucket, values i)
        ≤ ∑ _i ∈ bucket, 2 * t := by
          exact Finset.sum_le_sum fun i hi => hbucket_upper i hi
    _ = (bucket.card : ℝ) * (2 * t) := by simp
    _ = 2 * ((bucket.card : ℝ) * t) := by ring

/--
If a concrete dyadic tail finset contains every bidder who accepts price `p`,
then its floor mass bounds the accepting-count floor mass.
-/
theorem paper_theorem7_2_tail_count_floor_bound_of_winner_subset
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ)
    (tailSet : Finset Agent) {p t tail0 : ℝ}
    (ht_nonneg : 0 ≤ t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail0) :
    ((saleCount values p : ℝ) * t) ≤ tail0 := by
  have hcard_le :
      saleCount values p ≤ tailSet.card := by
    unfold saleCount
    exact Finset.card_le_card hwinners_subset
  have hcard_le_real :
      (saleCount values p : ℝ) ≤ (tailSet.card : ℝ) := by
    exact_mod_cast hcard_le
  have hmass_le :
      (saleCount values p : ℝ) * t ≤ (tailSet.card : ℝ) * t :=
    mul_le_mul_of_nonneg_right hcard_le_real ht_nonneg
  exact le_trans hmass_le htail_set_count

/--
A largest-total bucket bounds every floor mass once each bucket's floor mass is
bounded by its total value.
-/
theorem paper_theorem7_2_floor_mass_le_largest_bucket_total
    {Bin : Type*} (floorMass totalMass : Bin → ℝ) (selected : Bin)
    (hfloor_le_total : ∀ j : Bin, floorMass j ≤ totalMass j)
    (hlargest_total : ∀ j : Bin, totalMass j ≤ totalMass selected) :
    ∀ j : Bin, floorMass j ≤ totalMass selected := by
  intro j
  exact le_trans (hfloor_le_total j) (hlargest_total j)

/--
Finite largest-tail-bucket selection for GHW Theorem 7.2. Among a nonempty
finite range of tail buckets, one bucket maximizes total bid value.
-/
theorem paper_theorem7_2_exists_largest_tail_bucket
    {Agent : Type*} [DecidableEq Agent]
    (values : Agent → ℝ) (tailBuckets : ℕ → Finset Agent) {n : ℕ}
    (hn : 0 < n) :
    ∃ selected, selected < n ∧
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i := by
  classical
  have hnonempty : (Finset.range n).Nonempty :=
    ⟨0, Finset.mem_range.mpr hn⟩
  obtain ⟨selected, hselected_mem, hselected_max⟩ :=
    Finset.exists_max_image (Finset.range n)
      (fun j => ∑ i ∈ tailBuckets j, values i) hnonempty
  exact ⟨selected, Finset.mem_range.mp hselected_mem, fun j hj =>
    hselected_max j (Finset.mem_range.mpr hj)⟩

/--
The paper's largest dyadic tail bucket, chosen as an index in `range n`.
When `n = 0` the value is unused and set to `0`.
-/
noncomputable def paper_theorem7_2_largestTailBucketIndex
    {Agent : Type*} [DecidableEq Agent]
    (values : Agent → ℝ) (tailBuckets : ℕ → Finset Agent) (n : ℕ) : ℕ :=
  if hn : 0 < n then
    Classical.choose
      (paper_theorem7_2_exists_largest_tail_bucket values tailBuckets hn)
  else
    0

/--
The selected largest tail bucket lies in the finite bucket range.
-/
theorem paper_theorem7_2_largestTailBucketIndex_lt
    {Agent : Type*} [DecidableEq Agent]
    (values : Agent → ℝ) (tailBuckets : ℕ → Finset Agent) {n : ℕ}
    (hn : 0 < n) :
    paper_theorem7_2_largestTailBucketIndex values tailBuckets n < n := by
  classical
  rw [paper_theorem7_2_largestTailBucketIndex]
  simp [hn,
    (Classical.choose_spec
      (paper_theorem7_2_exists_largest_tail_bucket values tailBuckets hn)).1]

/--
The selected largest tail bucket has total value at least every tail bucket in
the finite range.
-/
theorem paper_theorem7_2_largestTailBucketIndex_largest
    {Agent : Type*} [DecidableEq Agent]
    (values : Agent → ℝ) (tailBuckets : ℕ → Finset Agent) {n : ℕ}
    (hn : 0 < n) :
    ∀ j, j < n →
      (∑ i ∈ tailBuckets j, values i) ≤
        ∑ i ∈
          tailBuckets
            (paper_theorem7_2_largestTailBucketIndex values tailBuckets n),
          values i := by
  classical
  intro j hj
  rw [paper_theorem7_2_largestTailBucketIndex]
  simp [hn,
    (Classical.choose_spec
      (paper_theorem7_2_exists_largest_tail_bucket values tailBuckets hn)).2
      j hj]

/--
Canonical dyadic tail bucket above a fixed-price base. Bucket `j` contains the
bidders whose values lie in the paper's factor-two range
`[2^j * baseFloor, 2 * 2^j * baseFloor]`.
-/
noncomputable def paper_theorem7_2_dyadicTailBucket
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (baseFloor : ℝ) (j : ℕ) : Finset Agent :=
  (Finset.univ : Finset Agent).filter fun i =>
    ((2 : ℝ) ^ j) * baseFloor ≤ values i ∧
      values i ≤ 2 * (((2 : ℝ) ^ j) * baseFloor)

/--
Every member of the canonical dyadic tail bucket is above its bucket floor.
-/
theorem paper_theorem7_2_dyadicTailBucket_floor
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (baseFloor : ℝ) :
    ∀ j, ∀ i : Agent,
      i ∈ paper_theorem7_2_dyadicTailBucket values baseFloor j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i := by
  intro j i hi
  have hmem := hi
  simp [paper_theorem7_2_dyadicTailBucket] at hmem
  exact hmem.1

/--
Every member of the canonical dyadic tail bucket is within a factor two of its
bucket floor.
-/
theorem paper_theorem7_2_dyadicTailBucket_upper
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (baseFloor : ℝ) :
    ∀ j, ∀ i : Agent,
      i ∈ paper_theorem7_2_dyadicTailBucket values baseFloor j →
        values i ≤ 2 * (((2 : ℝ) ^ j) * baseFloor) := by
  intro j i hi
  have hmem := hi
  simp [paper_theorem7_2_dyadicTailBucket] at hmem
  exact hmem.2

/--
If a fixed-price base is at most the posted price and all values are below the
corresponding finite dyadic ceiling, then every bidder who accepts the posted
price lies in one of the canonical dyadic tail buckets.
-/
theorem paper_theorem7_2_winners_subset_dyadicTailBuckets
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ) {baseFloor p : ℝ}
    (hbase_pos : 0 < baseFloor)
    (hbase_le_p : baseFloor ≤ p)
    (hvalue_le_power_base :
      ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1) * baseFloor) :
    ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
      (Finset.range (m + 1)).biUnion
        (paper_theorem7_2_dyadicTailBucket values baseFloor) := by
  classical
  intro i hi
  have hp_le_value : p ≤ values i := by
    simpa using hi
  have hbase_le_value : baseFloor ≤ values i := le_trans hbase_le_p hp_le_value
  have hx_low : 1 ≤ values i / baseFloor := by
    rw [le_div_iff₀ hbase_pos]
    simpa using hbase_le_value
  have hx_high : values i / baseFloor ≤ (2 : ℝ) ^ (m + 1) := by
    rw [div_le_iff₀ hbase_pos]
    exact hvalue_le_power_base i
  obtain ⟨j, hj_floor, hj_upper⟩ :=
    paper_theorem7_dyadicIndex_exists_of_power_two_bound m hx_low hx_high
  have hj_mem : j.val ∈ Finset.range (m + 1) := Finset.mem_range.mpr j.isLt
  have hfloor :
      ((2 : ℝ) ^ j.val) * baseFloor ≤ values i := by
    rw [le_div_iff₀ hbase_pos] at hj_floor
    simpa [mul_comm, mul_left_comm, mul_assoc] using hj_floor
  have hupper :
      values i ≤ 2 * (((2 : ℝ) ^ j.val) * baseFloor) := by
    rw [div_le_iff₀ hbase_pos] at hj_upper
    nlinarith
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨j.val, hj_mem, ?_⟩
  simp [paper_theorem7_2_dyadicTailBucket, hfloor, hupper]

/--
Winner coverage for canonical dyadic tail buckets from the paper's normalized
value range `values i <= 2^(m+1)` and a base floor at least one.
-/
theorem paper_theorem7_2_winners_subset_dyadicTailBuckets_of_power_bound
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ) {baseFloor p : ℝ}
    (hbase_ge_one : 1 ≤ baseFloor)
    (hbase_le_p : baseFloor ≤ p)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1)) :
    ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
      (Finset.range (m + 1)).biUnion
        (paper_theorem7_2_dyadicTailBucket values baseFloor) := by
  have hbase_pos : 0 < baseFloor := lt_of_lt_of_le (by norm_num) hbase_ge_one
  have hvalue_le_power_base :
      ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1) * baseFloor := by
    intro i
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (m + 1) := by positivity
    have hpow_le_scaled :
        (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 1) * baseFloor := by
      nlinarith
    exact le_trans (hvalue_le_power i) hpow_le_scaled
  exact
    paper_theorem7_2_winners_subset_dyadicTailBuckets
      values m hbase_pos hbase_le_p hvalue_le_power_base

/--
The largest canonical dyadic tail bucket above a fixed-price base.
-/
noncomputable def paper_theorem7_2_largestDyadicTailBucketIndex
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (baseFloor : ℝ) (m : ℕ) : ℕ :=
  paper_theorem7_2_largestTailBucketIndex values
    (paper_theorem7_2_dyadicTailBucket values baseFloor) (m + 1)

/--
The largest canonical dyadic tail bucket itself.
-/
noncomputable def paper_theorem7_2_largestDyadicTailBucket
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (baseFloor : ℝ) (m : ℕ) : Finset Agent :=
  paper_theorem7_2_dyadicTailBucket values baseFloor
    (paper_theorem7_2_largestDyadicTailBucketIndex values baseFloor m)

/--
If a finite bucket has at most one bidder, its total value is bounded by the
uniform per-bidder upper bound.
-/
theorem paper_theorem7_2_sum_le_bound_of_card_le_one
    {Agent : Type*} (values : Agent → ℝ) (bucket : Finset Agent) {H : ℝ}
    (hH_nonneg : 0 ≤ H)
    (hcard : bucket.card ≤ 1)
    (hvalue_nonneg : ∀ i : Agent, i ∈ bucket → 0 ≤ values i)
    (hvalue_le : ∀ i : Agent, i ∈ bucket → values i ≤ H) :
    (∑ i ∈ bucket, values i) ≤ H := by
  by_cases hzero : bucket.card = 0
  · have hbucket_empty : bucket = ∅ := Finset.card_eq_zero.mp hzero
    simp [hbucket_empty, hH_nonneg]
  · have hcard_pos : 0 < bucket.card := Nat.pos_of_ne_zero hzero
    have hcard_eq_one : bucket.card = 1 := by omega
    obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp hcard_eq_one
    subst hi_eq
    simpa using hvalue_le i (by simp)

/--
GHW Theorem 7.2 size step for the canonical fixed-price tail. If the tail is
bucketed from the fixed price `p` itself and `F = p * saleCount p >= 2h`, then
the paper's largest dyadic bucket has at least two bidders. Otherwise every
bucket has total value at most `h`, and the strict finite geometric-tail bound
would force `F < 2h`.
-/
theorem paper_theorem7_2_largestDyadicTailBucket_card_two_of_large_fixed_price
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ)
    {fixedPriceBenchmark p : ℝ}
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hp_ge_one : 1 ≤ p)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark) :
    2 ≤ (paper_theorem7_2_largestDyadicTailBucket values p m).card := by
  classical
  let H : ℝ := (2 : ℝ) ^ (m + 1)
  let tailBuckets : ℕ → Finset Agent :=
    paper_theorem7_2_dyadicTailBucket values p
  let selected : ℕ :=
    paper_theorem7_2_largestTailBucketIndex values tailBuckets (m + 1)
  let selectedBucket : Finset Agent := tailBuckets selected
  have hH_pos : 0 < H := by
    dsimp [H]
    positivity
  have hH_nonneg : 0 ≤ H := le_of_lt hH_pos
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num) hp_ge_one
  by_contra hnot_two
  have hselected_card_le_one : selectedBucket.card ≤ 1 := by
    have hcard :
        (paper_theorem7_2_largestDyadicTailBucket values p m).card ≤ 1 := by
      omega
    simpa [paper_theorem7_2_largestDyadicTailBucket,
      paper_theorem7_2_largestDyadicTailBucketIndex, tailBuckets,
      selected, selectedBucket] using hcard
  have hselected_total_le_H :
      (∑ i ∈ selectedBucket, values i) ≤ H :=
    paper_theorem7_2_sum_le_bound_of_card_le_one
      values selectedBucket hH_nonneg hselected_card_le_one
      (fun i _hi => by
        have hge := hvalue_ge_one i
        nlinarith)
      (fun i _hi => by simpa [H] using hvalue_le_power i)
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hselected_largest :
      ∀ j, j < m + 1 →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i := by
    simpa [selected] using
      paper_theorem7_2_largestTailBucketIndex_largest
        values tailBuckets (Nat.succ_pos m)
  have hmass_bound :
      ∀ j, 0 ≤ j → j < 0 + (m + 1) → floorMass j ≤ H := by
    intro j _hj_ge hj_lt
    exact le_trans (hselected_largest j (by omega))
      (by simpa [selectedBucket, floorMass] using hselected_total_le_H)
  have htail_lt :
      paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 <
        2 * H :=
    paper_theorem7_2_dyadicGeometricTail_lt_two_max
      floorMass hH_pos (m + 1) 0 hmass_bound
  let tailSet : Finset Agent := (Finset.range (m + 1)).biUnion tailBuckets
  have hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet := by
    simpa [tailSet, tailBuckets] using
      paper_theorem7_2_winners_subset_dyadicTailBuckets_of_power_bound
        values m hp_ge_one (le_rfl : p ≤ p) hvalue_le_power
  have hbucket_count_floor :
      ∀ j, j < m + 1 →
        ((tailBuckets j).card : ℝ) * p ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j _hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity)
      (by
        intro i hi
        exact
          paper_theorem7_2_dyadicTailBucket_floor values p j i
            (by simpa [tailBuckets] using hi))
  have htail_set_count :
      ((tailSet.card : ℝ) * p) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass (m + 1) hp_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have htail_count :
      ((saleCount values p : ℝ) * p) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 :=
    paper_theorem7_2_tail_count_floor_bound_of_winner_subset
      values tailSet hp_nonneg hwinners_subset htail_set_count
  have hF_lt : fixedPriceBenchmark < 2 * H := by
    rw [hF_eq, singlePriceRevenue_eq_saleCount_mul]
    exact lt_of_le_of_lt htail_count htail_lt
  nlinarith

/--
GHW Theorem 7.2 size step using the paper high value `h` directly. If the
canonical fixed-price tail is bucketed dyadically far enough to cover all bids
up to `h`, and `F = p * saleCount p >= 2h`, then the largest tail bucket has at
least two bidders.
-/
theorem paper_theorem7_2_largestDyadicTailBucket_card_two_of_large_fixed_price_high_value
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (m : ℕ)
    {highValue fixedPriceBenchmark p : ℝ}
    (hhigh_ge_one : 1 ≤ highValue)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_high : ∀ i : Agent, values i ≤ highValue)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hp_ge_one : 1 ≤ p)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hF_ge_two_high : 2 * highValue ≤ fixedPriceBenchmark) :
    2 ≤ (paper_theorem7_2_largestDyadicTailBucket values p m).card := by
  classical
  let H : ℝ := highValue
  let tailBuckets : ℕ → Finset Agent :=
    paper_theorem7_2_dyadicTailBucket values p
  let selected : ℕ :=
    paper_theorem7_2_largestTailBucketIndex values tailBuckets (m + 1)
  let selectedBucket : Finset Agent := tailBuckets selected
  have hH_pos : 0 < H := by
    dsimp [H]
    exact lt_of_lt_of_le zero_lt_one hhigh_ge_one
  have hH_nonneg : 0 ≤ H := le_of_lt hH_pos
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num) hp_ge_one
  by_contra hnot_two
  have hselected_card_le_one : selectedBucket.card ≤ 1 := by
    have hcard :
        (paper_theorem7_2_largestDyadicTailBucket values p m).card ≤ 1 := by
      omega
    simpa [paper_theorem7_2_largestDyadicTailBucket,
      paper_theorem7_2_largestDyadicTailBucketIndex, tailBuckets,
      selected, selectedBucket] using hcard
  have hselected_total_le_H :
      (∑ i ∈ selectedBucket, values i) ≤ H :=
    paper_theorem7_2_sum_le_bound_of_card_le_one
      values selectedBucket hH_nonneg hselected_card_le_one
      (fun i _hi => by
        have hge := hvalue_ge_one i
        nlinarith)
      (fun i _hi => by simpa [H] using hvalue_le_high i)
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hselected_largest :
      ∀ j, j < m + 1 →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i := by
    simpa [selected] using
      paper_theorem7_2_largestTailBucketIndex_largest
        values tailBuckets (Nat.succ_pos m)
  have hmass_bound :
      ∀ j, 0 ≤ j → j < 0 + (m + 1) → floorMass j ≤ H := by
    intro j _hj_ge hj_lt
    exact le_trans (hselected_largest j (by omega))
      (by simpa [selectedBucket, floorMass] using hselected_total_le_H)
  have htail_lt :
      paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 <
        2 * H :=
    paper_theorem7_2_dyadicGeometricTail_lt_two_max
      floorMass hH_pos (m + 1) 0 hmass_bound
  let tailSet : Finset Agent := (Finset.range (m + 1)).biUnion tailBuckets
  have hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet := by
    simpa [tailSet, tailBuckets] using
      paper_theorem7_2_winners_subset_dyadicTailBuckets_of_power_bound
        values m hp_ge_one (le_rfl : p ≤ p) hvalue_le_power
  have hbucket_count_floor :
      ∀ j, j < m + 1 →
        ((tailBuckets j).card : ℝ) * p ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j _hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity)
      (by
        intro i hi
        exact
          paper_theorem7_2_dyadicTailBucket_floor values p j i
            (by simpa [tailBuckets] using hi))
  have htail_set_count :
      ((tailSet.card : ℝ) * p) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass (m + 1) hp_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have htail_count :
      ((saleCount values p : ℝ) * p) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass (m + 1) 0 :=
    paper_theorem7_2_tail_count_floor_bound_of_winner_subset
      values tailSet hp_nonneg hwinners_subset htail_set_count
  have hF_lt : fixedPriceBenchmark < 2 * H := by
    rw [hF_eq, singlePriceRevenue_eq_saleCount_mul]
    exact lt_of_le_of_lt htail_count htail_lt
  nlinarith

/--
GHW Theorem 7.2 half-split size algebra. If a bucket has at least two bidders
and its floor mass satisfies `F <= C * |M| * t`, then both halves of the sorted
rank split have enough floor mass up to the constant `3*C`.
-/
theorem paper_theorem7_2_rank_split_bucket_size_bounds
    {Agent : Type*} [LinearOrder Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (bucket : Finset Agent)
    {fixedPriceBenchmark t C : ℝ}
    (hbucket_size : 2 ≤ bucket.card)
    (hC_nonneg : 0 ≤ C)
    (ht_nonneg : 0 ≤ t)
    (hF_bucket :
      fixedPriceBenchmark ≤ C * ((bucket.card : ℝ) * t)) :
    fixedPriceBenchmark ≤
        (3 * C) *
          (((FiniteRanking.upperRankFinset
            (s := bucket) (value := values) rfl (bucket.card / 2)).card : ℝ) *
            t) ∧
      fixedPriceBenchmark ≤
        (3 * C) *
          (((FiniteRanking.lowerRankFinset
            (s := bucket) (value := values) rfl (bucket.card / 2)).card : ℝ) *
            t) := by
  classical
  let high : Finset Agent :=
    FiniteRanking.upperRankFinset
      (s := bucket) (value := values) rfl (bucket.card / 2)
  let low : Finset Agent :=
    FiniteRanking.lowerRankFinset
      (s := bucket) (value := values) rfl (bucket.card / 2)
  have hlow_card : low.card = bucket.card / 2 := by
    simpa [low] using
      (FiniteRanking.lowerRankFinset_card_half
        (s := bucket) (value := values) rfl)
  have hhigh_card : high.card = bucket.card - bucket.card / 2 := by
    simpa [high] using
      (FiniteRanking.upperRankFinset_card_half
        (s := bucket) (value := values) rfl)
  have hbucket_le_low_nat : bucket.card ≤ 3 * low.card := by
    rw [hlow_card]
    omega
  have hbucket_le_high_nat : bucket.card ≤ 3 * high.card := by
    rw [hhigh_card]
    omega
  have hbucket_le_low_real :
      (bucket.card : ℝ) ≤ 3 * (low.card : ℝ) := by
    exact_mod_cast hbucket_le_low_nat
  have hbucket_le_high_real :
      (bucket.card : ℝ) ≤ 3 * (high.card : ℝ) := by
    exact_mod_cast hbucket_le_high_nat
  have hmass_low :
      (bucket.card : ℝ) * t ≤ (3 * (low.card : ℝ)) * t :=
    mul_le_mul_of_nonneg_right hbucket_le_low_real ht_nonneg
  have hmass_high :
      (bucket.card : ℝ) * t ≤ (3 * (high.card : ℝ)) * t :=
    mul_le_mul_of_nonneg_right hbucket_le_high_real ht_nonneg
  have htarget_low :
      C * ((bucket.card : ℝ) * t) ≤
        (3 * C) * ((low.card : ℝ) * t) := by
    have hmul := mul_le_mul_of_nonneg_left hmass_low hC_nonneg
    nlinarith
  have htarget_high :
      C * ((bucket.card : ℝ) * t) ≤
        (3 * C) * ((high.card : ℝ) * t) := by
    have hmul := mul_le_mul_of_nonneg_left hmass_high hC_nonneg
    nlinarith
  exact ⟨by
    exact le_trans hF_bucket (by simpa [high] using htarget_high), by
    exact le_trans hF_bucket (by simpa [low] using htarget_low)⟩

/--
GHW Theorem 7.2 second-case half-split bucket certificate. This packages the
paper's `M'`/`M''` construction for a single largest bucket, conditional only
on the bucket floor-mass lower bound `F <= C * |M| * t`.
-/
theorem paper_theorem7_2_second_case_half_rank_split_bucket
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket : Finset Agent)
    {totalValue fixedPriceBenchmark s t C : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hC_nonneg : 0 ≤ C)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_bucket :
      fixedPriceBenchmark ≤ C * ((bucket.card : ℝ) * t)) :
    fixedPriceBenchmark ≤
      ((3 * C) * (3 * C)) * s * weightedPairingExpectedRevenue values := by
  have hthreeC_nonneg : 0 ≤ 3 * C := by positivity
  obtain ⟨hF_high, hF_low⟩ :=
    paper_theorem7_2_rank_split_bucket_size_bounds
      values bucket hbucket_size hC_nonneg ht_nonneg hF_bucket
  exact
    paper_theorem7_2_second_case_rank_split_bucket
      values bucket (bucket.card / 2) htotal htotal_pos hs_pos
      hthreeC_nonneg hthreeC_nonneg hF_nonneg ht_nonneg hbucket_floor
      hden_pos_agent hcase hF_high hF_low

/--
GHW Theorem 7.2 second-case largest-bucket certificate. This combines the
geometric dyadic-tail mass argument with the half-rank split: once the selected
bucket is largest by total value and its total value is within factor two of its
floor mass, the weighted pairing revenue satisfies the paper's
`F <= O(sW)` second-case bound.
-/
theorem paper_theorem7_2_second_case_largest_bucket_certificate
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t maxFloorMass selectedTotalMass : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hmax_nonneg : 0 ≤ maxFloorMass)
    (hmass_bound : ∀ j, j < n → floorMass j ≤ maxFloorMass)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1))
    (hF_tail : fixedPriceBenchmark ≤ 2 * tail 0)
    (hmax_le_selected_total : maxFloorMass ≤ selectedTotalMass)
    (hselected_total_le_bucket_floor :
      selectedTotalMass ≤ 2 * ((bucket.card : ℝ) * t)) :
    fixedPriceBenchmark ≤
      ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values := by
  have hF_bucket :
      fixedPriceBenchmark ≤ 8 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_largest_bucket_floor_mass_certificate
      floorMass tail n hmax_nonneg hmass_bound htail_end hrec hF_tail
      hmax_le_selected_total hselected_total_le_bucket_floor
  exact
    paper_theorem7_2_second_case_half_rank_split_bucket
      values bucket htotal htotal_pos hs_pos (by norm_num) hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hden_pos_agent hcase hF_bucket

/--
GHW Theorem 7.2 second-case largest-bucket wrapper from an explicit fixed
price and dyadic tail. This is the paper-facing version of the previous
certificate: `p` is the fixed price defining `F`, `t` is the floor of the
selected dyadic bucket, and the selected bucket's total value dominates every
tail bucket floor mass.
-/
theorem paper_theorem7_2_second_case_largest_bucket_from_fixed_price_tail
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (htail_count : ((saleCount values p : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    fixedPriceBenchmark ≤
      ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values := by
  have hselected_nonneg : 0 ≤ ∑ i ∈ bucket, values i :=
    Finset.sum_nonneg fun i hi =>
      le_trans ht_nonneg (hbucket_floor i hi)
  have hselected_total_le_bucket_floor :
      (∑ i ∈ bucket, values i) ≤ 2 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_bucket_total_le_two_floor_mass
      values bucket hbucket_upper
  have hF_tail : fixedPriceBenchmark ≤ 2 * tail 0 :=
    paper_theorem7_2_fixed_price_le_two_floor_tail
      values hF_eq hp_le_two_t htail_count
  exact
    paper_theorem7_2_second_case_largest_bucket_certificate
      values bucket floorMass tail n htotal htotal_pos hs_pos hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hden_pos_agent hcase
      hselected_nonneg hmass_bound htail_end hrec hF_tail
      (le_rfl : (∑ i ∈ bucket, values i) ≤ ∑ i ∈ bucket, values i)
      hselected_total_le_bucket_floor

/--
GHW Theorem 7.2 second-case largest-bucket wrapper with a concrete dyadic tail
set. This replaces the accepting-count tail inequality by a finset inclusion:
every bidder accepting the fixed price `p` belongs to `tailSet`.
-/
theorem paper_theorem7_2_second_case_largest_bucket_from_tail_set
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket tailSet : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    fixedPriceBenchmark ≤
      ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values := by
  have htail_count :
      ((saleCount values p : ℝ) * t) ≤ tail 0 :=
    paper_theorem7_2_tail_count_floor_bound_of_winner_subset
      values tailSet ht_nonneg hwinners_subset htail_set_count
  exact
    paper_theorem7_2_second_case_largest_bucket_from_fixed_price_tail
      values bucket floorMass tail n htotal htotal_pos hs_pos hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hbucket_upper hden_pos_agent
      hcase hF_eq hp_le_two_t htail_count hmass_bound htail_end hrec

/--
GHW Theorem 7.2 second-case largest-bucket wrapper using the canonical finite
dyadic geometric tail.
-/
theorem paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket tailSet : Finset Agent)
    (floorMass : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count :
      ((tailSet.card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values := by
  have hselected_nonneg : 0 ≤ ∑ i ∈ bucket, values i :=
    Finset.sum_nonneg fun i hi =>
      le_trans ht_nonneg (hbucket_floor i hi)
  have hselected_total_le_bucket_floor :
      (∑ i ∈ bucket, values i) ≤ 2 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_bucket_total_le_two_floor_mass
      values bucket hbucket_upper
  have htail_count :
      ((saleCount values p : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_count_floor_bound_of_winner_subset
      values tailSet ht_nonneg hwinners_subset htail_set_count
  have hF_tail :
      fixedPriceBenchmark ≤
        2 * paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_fixed_price_le_two_floor_tail
      values hF_eq hp_le_two_t htail_count
  have hF_bucket :
      fixedPriceBenchmark ≤ 8 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_largest_bucket_floor_mass_from_geometric_tail
      floorMass n hselected_nonneg hmass_bound hF_tail
      (le_rfl : (∑ i ∈ bucket, values i) ≤ ∑ i ∈ bucket, values i)
      hselected_total_le_bucket_floor
  exact
    paper_theorem7_2_second_case_half_rank_split_bucket
      values bucket htotal htotal_pos hs_pos (by norm_num) hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hden_pos_agent hcase hF_bucket

/--
GHW Theorem 7.2 second-case largest-bucket wrapper with distinct tail base and
selected-bucket floor. The fixed-price winners are counted in units of
`baseFloor`, while the selected largest bucket used for the high/low split has
floor `t`.
-/
theorem paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set_base
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket tailSet : Finset Agent)
    (floorMass : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbase_nonneg : 0 ≤ baseFloor)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hcase : totalValue ≤ s * fixedPriceBenchmark)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count :
      ((tailSet.card : ℝ) * baseFloor) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values := by
  have hselected_nonneg : 0 ≤ ∑ i ∈ bucket, values i :=
    Finset.sum_nonneg fun i hi =>
      le_trans ht_nonneg (hbucket_floor i hi)
  have hselected_total_le_bucket_floor :
      (∑ i ∈ bucket, values i) ≤ 2 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_bucket_total_le_two_floor_mass
      values bucket hbucket_upper
  have htail_count :
      ((saleCount values p : ℝ) * baseFloor) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_count_floor_bound_of_winner_subset
      values tailSet hbase_nonneg hwinners_subset htail_set_count
  have hF_tail :
      fixedPriceBenchmark ≤
        2 * paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_fixed_price_le_two_floor_tail
      values hF_eq hp_le_two_base htail_count
  have hF_bucket :
      fixedPriceBenchmark ≤ 8 * ((bucket.card : ℝ) * t) :=
    paper_theorem7_2_largest_bucket_floor_mass_from_geometric_tail
      floorMass n hselected_nonneg hmass_bound hF_tail
      (le_rfl : (∑ i ∈ bucket, values i) ≤ ∑ i ∈ bucket, values i)
      hselected_total_le_bucket_floor
  exact
    paper_theorem7_2_second_case_half_rank_split_bucket
      values bucket htotal htotal_pos hs_pos (by norm_num) hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hden_pos_agent hcase hF_bucket

/--
GHW Theorem 7.2 lower-bound certificate for the weighted-pairing auction. The
first case is supplied by the Section 7.1 weighted-pairing bound; the second
case is supplied by the concrete largest-bucket/tail-set certificate above.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_tail_set_certificate
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (bucket tailSet : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (htotal_pos : 0 < totalValue)
    (hs_pos : 0 < s)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hden_pos_agent : ∀ i : Agent,
      0 < totalBidValue values - values i)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1))
    (hweighted :
      totalValue ≤
        192 * (s ^ 2) * weightedPairingExpectedRevenue values) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  refine
    paper_theorem7_2_case_split_from_first_second
      hs_pos hW_nonneg hweighted ?_
  intro hcase
  have hsecond :
      fixedPriceBenchmark ≤
        ((3 * 8) * (3 * 8)) * s *
          weightedPairingExpectedRevenue values :=
    paper_theorem7_2_second_case_largest_bucket_from_tail_set
      values bucket tailSet floorMass tail n htotal htotal_pos hs_pos
      hF_nonneg ht_nonneg hbucket_size hbucket_floor hbucket_upper
      hden_pos_agent hcase hF_eq hp_le_two_t hwinners_subset
      htail_set_count hmass_bound htail_end hrec
  simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 certificate from Section 7 dyadic-bin data. This wrapper derives
the first-case `T <= 192 s^2 W` premise from the Theorem 7.1 active/singleton
bin certificate plus `logH <= s^2`, and derives denominator positivity from the
paper's high-bid bound.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_bin_and_tail_certificates
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin]
    (values : Agent → ℝ) (bins : AllBin → Finset Agent)
    (binFloor : AllBin → ℝ) (bucket tailSet : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hpartition :
      totalValue ≤
        (∑ j : {j : AllBin // (bins j).card ≤ 1},
          ∑ i ∈ bins j.1, values i) +
        ∑ j : {j : AllBin // 2 ≤ (bins j).card},
          ∑ i ∈ bins j.1, values i)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin // (bins j).card ≤ 1}, binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos : ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j)
    (hfloor_le :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i)
    (hfactor_two :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j)
    (hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂)
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have htotal_pos : 0 < totalValue := by
    nlinarith
  have hh_lt_total : h < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_h hh_lt_total
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hweighted_log :
      totalValue ≤
        192 * logH * weightedPairingExpectedRevenue values :=
    paper_theorem7_1_weighted_pairing_log_bound_of_active_singleton_bins
      values bins binFloor htotal hvalues_nonneg hh_pos hvalue_le_h
      hpartition hfloor_nonneg hsingleton_floor_sum hlarge hfloor_pos
      hfloor_le hfactor_two hbins_disjoint hcard_all_le_logH
  have hlog_to_s :
      192 * logH * weightedPairingExpectedRevenue values ≤
        192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
    have hmul :=
      mul_le_mul_of_nonneg_right hlogH_le_s_sq hW_nonneg
    nlinarith
  exact
    paper_theorem7_2_weighted_pairing_bound_from_tail_set_certificate
      values bucket tailSet floorMass tail n htotal htotal_pos hs_pos
      hF_nonneg ht_nonneg hbucket_size hbucket_floor hbucket_upper
      hden_pos_agent hF_eq hp_le_two_t hwinners_subset htail_set_count
      hmass_bound htail_end hrec (le_trans hweighted_log hlog_to_s)

/--
GHW Theorem 7.2 certificate from one dyadic-bin mass cover plus the largest
tail/bucket certificate. This is the current closest Lean wrapper to the paper
lower-bound proof: Section 7.1's active/singleton split is performed internally.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_all_bin_and_tail_certificates
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin]
    (values : Agent → ℝ) (bins : AllBin → Finset Agent)
    (binFloor : AllBin → ℝ) (bucket tailSet : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hcover : totalValue ≤ ∑ j : AllBin, ∑ i ∈ bins j, values i)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin // (bins j).card ≤ 1}, binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos : ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j)
    (hfloor_le :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i)
    (hfactor_two :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j)
    (hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂)
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have hpartition :
      totalValue ≤
        (∑ j : {j : AllBin // (bins j).card ≤ 1},
          ∑ i ∈ bins j.1, values i) +
        ∑ j : {j : AllBin // 2 ≤ (bins j).card},
          ∑ i ∈ bins j.1, values i :=
    paper_theorem7_1_active_singleton_mass_cover_of_all_bins
      values bins hcover
  exact
    paper_theorem7_2_weighted_pairing_bound_from_bin_and_tail_certificates
      values bins binFloor bucket tailSet floorMass tail n htotal
      hvalues_nonneg hh_pos hvalue_le_h hpartition hfloor_nonneg
      hsingleton_floor_sum hlarge hfloor_pos hfloor_le hfactor_two
      hbins_disjoint hcard_all_le_logH hs_pos hlogH_le_s_sq hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hbucket_upper hF_eq hp_le_two_t
      hwinners_subset htail_set_count hmass_bound htail_end hrec

/--
GHW Theorem 7.2 classifier-bin certificate. A dyadic classifier `binOf`
automatically supplies disjoint bins covering the whole bid profile; the
remaining hypotheses are the paper's factor-two floor facts, singleton floor
sum, and largest-bucket tail certificate.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_classifier_and_tail_certificates
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin] [DecidableEq AllBin]
    (values : Agent → ℝ) (binOf : Agent → AllBin)
    (binFloor : AllBin → ℝ) (bucket tailSet : Finset Agent)
    (floorMass tail : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin //
          (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card)
            ≤ 1},
        binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos :
      ∀ j : AllBin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j)
    (hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i)
    (hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i))
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count : ((tailSet.card : ℝ) * t) ≤ tail 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i)
    (htail_end : tail n ≤ 0)
    (hrec : ∀ j, j < n →
      tail j ≤ floorMass j + (1 / 2) * tail (j + 1)) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let bins : AllBin → Finset Agent := fun j =>
    (Finset.univ : Finset Agent).filter fun i => binOf i = j
  have hcover : totalValue ≤ ∑ j : AllBin, ∑ i ∈ bins j, values i := by
    rw [htotal]
    exact le_of_eq (paper_totalBidValue_eq_sum_classifier_bins values binOf)
  have hfloor_pos_bins :
      ∀ j : AllBin, 2 ≤ (bins j).card → 0 < binFloor j := by
    intro j hj
    exact hfloor_pos j (by simpa [bins] using hj)
  have hfloor_le_bins :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → binFloor j ≤ values i := by
    intro j i hi
    have hbin : binOf i = j := (Finset.mem_filter.mp hi).2
    simpa [hbin] using hfloor_le i
  have hfactor_two_bins :
      ∀ j : AllBin, ∀ i : Agent, i ∈ bins j → values i ≤ 2 * binFloor j := by
    intro j i hi
    have hbin : binOf i = j := (Finset.mem_filter.mp hi).2
    simpa [hbin] using hfactor_two i
  have hbins_disjoint :
      ∀ j₁ j₂ : AllBin, ∀ i : Agent,
        i ∈ bins j₁ → i ∈ bins j₂ → j₁ = j₂ := by
    intro j₁ j₂ i hi₁ hi₂
    have h₁ : binOf i = j₁ := (Finset.mem_filter.mp hi₁).2
    have h₂ : binOf i = j₂ := (Finset.mem_filter.mp hi₂).2
    exact h₁.symm.trans h₂
  exact
    paper_theorem7_2_weighted_pairing_bound_from_all_bin_and_tail_certificates
      values bins binFloor bucket tailSet floorMass tail n htotal
      hvalues_nonneg hh_pos hvalue_le_h hcover hfloor_nonneg
      (by simpa [bins] using hsingleton_floor_sum)
      hlarge hfloor_pos_bins hfloor_le_bins hfactor_two_bins
      hbins_disjoint hcard_all_le_logH hs_pos hlogH_le_s_sq hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hbucket_upper hF_eq hp_le_two_t
      hwinners_subset htail_set_count hmass_bound htail_end hrec

/--
GHW Theorem 7.2 classifier-bin certificate with the canonical finite dyadic
geometric tail. This is the shortest current certificate interface for the
paper's lower-bound proof.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_classifier_and_geometric_tail_certificates
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin] [DecidableEq AllBin]
    (values : Agent → ℝ) (binOf : Agent → AllBin)
    (binFloor : AllBin → ℝ) (bucket tailSet : Finset Agent)
    (floorMass : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin //
          (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card)
            ≤ 1},
        binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos :
      ∀ j : AllBin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j)
    (hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i)
    (hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i))
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        tailSet)
    (htail_set_count :
      ((tailSet.card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0)
    (hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have htotal_pos : 0 < totalValue := by
    nlinarith
  have hh_lt_total : h < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_h hh_lt_total
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hweighted_log :
      totalValue ≤
        192 * logH * weightedPairingExpectedRevenue values :=
    paper_theorem7_1_weighted_pairing_log_bound_from_classifier
      values binOf binFloor htotal hvalues_nonneg hh_pos hvalue_le_h
      hfloor_nonneg hsingleton_floor_sum hlarge hfloor_pos hfloor_le
      hfactor_two hcard_all_le_logH
  have hweighted :
      totalValue ≤
        192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
    have hmul :=
      mul_le_mul_of_nonneg_right hlogH_le_s_sq hW_nonneg
    exact le_trans hweighted_log (by nlinarith)
  refine
    paper_theorem7_2_case_split_from_first_second
      hs_pos hW_nonneg hweighted ?_
  intro hcase
  have hsecond :
      fixedPriceBenchmark ≤
        ((3 * 8) * (3 * 8)) * s *
          weightedPairingExpectedRevenue values :=
    paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set
      values bucket tailSet floorMass n htotal htotal_pos hs_pos hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hbucket_upper hden_pos_agent
      hcase hF_eq hp_le_two_t hwinners_subset htail_set_count hmass_bound
  simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 classifier-bin certificate from an explicit finite family of
tail buckets. This discharges the raw dyadic-tail count and largest-bucket mass
hypotheses from checkable bucket facts: fixed-price winners are covered by the
tail buckets, each bucket contributes its count mass to the dyadic tail, and
the selected bucket has at least as much total value as every tail bucket.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_classifier_and_bucket_family_certificates
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin] [DecidableEq AllBin]
    (values : Agent → ℝ) (binOf : Agent → AllBin)
    (binFloor : AllBin → ℝ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (floorMass : ℕ → ℝ) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin //
          (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card)
            ≤ 1},
        binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos :
      ∀ j : AllBin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j)
    (hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i)
    (hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i))
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * t ≤ floorMass j / (2 : ℝ) ^ j)
    (hfloorMass_le_bucketTotal :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ tailBuckets j, values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let tailSet : Finset Agent := (Finset.range n).biUnion tailBuckets
  have htail_set_count :
      ((tailSet.card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass n ht_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i := by
    intro j hj
    exact le_trans (hfloorMass_le_bucketTotal j hj)
      (hselected_largest j hj)
  exact
    paper_theorem7_2_weighted_pairing_bound_from_classifier_and_geometric_tail_certificates
      values binOf binFloor bucket tailSet floorMass n htotal hvalues_nonneg
      hh_pos hvalue_le_h hfloor_nonneg hsingleton_floor_sum hlarge
      hfloor_pos hfloor_le hfactor_two hcard_all_le_logH hs_pos
      hlogH_le_s_sq hF_nonneg ht_nonneg hbucket_size hbucket_floor
      hbucket_upper hF_eq hp_le_two_t (by simpa [tailSet] using hwinners_subset)
      htail_set_count hmass_bound

/--
GHW Theorem 7.2 classifier-bin certificate from actual dyadic tail buckets.
The canonical tail mass is instantiated as each tail bucket's total bid value;
the dyadic count contribution follows from the lower value floor
`2^j * t <= b_i` inside bucket `j`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_classifier_and_value_floor_bucket_family
    {Agent AllBin : Type*} [Fintype Agent] [DecidableEq Agent]
    [LinearOrder Agent] [Fintype AllBin] [DecidableEq AllBin]
    (values : Agent → ℝ) (binOf : Agent → AllBin)
    (binFloor : AllBin → ℝ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p h logH : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalues_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hh_pos : 0 < h)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hfloor_nonneg : ∀ j : AllBin, 0 ≤ binFloor j)
    (hsingleton_floor_sum :
      (∑ j : {j : AllBin //
          (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card)
            ≤ 1},
        binFloor j.1) ≤ h)
    (hlarge : 4 * h ≤ totalValue)
    (hfloor_pos :
      ∀ j : AllBin,
        2 ≤ (((Finset.univ : Finset Agent).filter fun i => binOf i = j).card) →
          0 < binFloor j)
    (hfloor_le : ∀ i : Agent, binFloor (binOf i) ≤ values i)
    (hfactor_two : ∀ i : Agent, values i ≤ 2 * binFloor (binOf i))
    (hcard_all_le_logH : (Fintype.card AllBin : ℝ) ≤ logH)
    (hs_pos : 0 < s)
    (hlogH_le_s_sq : logH ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * t ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * t ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j hj
    exact
      paper_theorem7_2_bucket_count_mass_le_total_div_scale
        values (tailBuckets j) (by positivity) (htail_bucket_floor j hj)
  have hfloorMass_le_bucketTotal :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ tailBuckets j, values i := by
    intro j _hj
    exact le_rfl
  exact
    paper_theorem7_2_weighted_pairing_bound_from_classifier_and_bucket_family_certificates
      values binOf binFloor bucket tailBuckets floorMass n htotal
      hvalues_nonneg hh_pos hvalue_le_h hfloor_nonneg hsingleton_floor_sum
      hlarge hfloor_pos hfloor_le hfactor_two hcard_all_le_logH hs_pos
      hlogH_le_s_sq hF_nonneg ht_nonneg hbucket_size hbucket_floor
      hbucket_upper hF_eq hp_le_two_t hwinners_subset hbucket_count_floor
      hfloorMass_le_bucketTotal hselected_largest

/--
GHW Theorem 7.2 lower-bound certificate with the paper's dyadic classifier
constructed internally from a power-of-two high-bid certificate. The only
remaining Section 7.2 bucket inputs are the selected bucket, the finite tail
bucket family above its scale, and their value-floor/largest-bucket facts.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_and_value_floor_bucket_family
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hlarge : 4 * (2 : ℝ) ^ (m + 1) ≤ totalValue)
    (hs_pos : 0 < s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (hF_nonneg : 0 ≤ fixedPriceBenchmark)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * t ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let tailSet : Finset Agent := (Finset.range n).biUnion tailBuckets
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have htotal_pos : 0 < totalValue := by
    have hpow_pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
    nlinarith
  have hh_lt_total : (2 : ℝ) ^ (m + 1) < totalValue := by
    have hpow_pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_power hh_lt_total
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hweighted_log :
      totalValue ≤
        192 * ((m + 1 : ℕ) : ℝ) * weightedPairingExpectedRevenue values :=
    paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins
      values m htotal hvalue_ge_one hvalue_le_power hlarge
  have hweighted :
      totalValue ≤ 192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
    have hmul := mul_le_mul_of_nonneg_right hlog_le_s_sq hW_nonneg
    exact le_trans hweighted_log (by nlinarith)
  have hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * t ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity) (htail_bucket_floor j hj)
  have htail_set_count :
      ((tailSet.card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass n ht_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i := by
    intro j hj
    exact hselected_largest j hj
  refine
    paper_theorem7_2_case_split_from_first_second
      hs_pos hW_nonneg hweighted ?_
  intro hcase
  have hsecond :
      fixedPriceBenchmark ≤
        ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values :=
    paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set
      values bucket tailSet floorMass n htotal htotal_pos hs_pos hF_nonneg
      ht_nonneg hbucket_size hbucket_floor hbucket_upper hden_pos_agent hcase
      hF_eq hp_le_two_t (by simpa [tailSet] using hwinners_subset)
      htail_set_count hmass_bound
  simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 lower-bound certificate with the paper's `F >= 2h`
assumption. Unlike the simpler power-of-two wrapper, this theorem does not
assume `4h <= T` globally; in the first branch, `F <= T/s`, `F >= 2h`, and
`2 <= s` imply the `4h <= T` precondition needed for Theorem 7.1.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_large_benchmark
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s t p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (ht_nonneg : 0 ≤ t)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_t : p ≤ 2 * t)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * t ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let H : ℝ := (2 : ℝ) ^ (m + 1)
  let tailSet : Finset Agent := (Finset.range n).biUnion tailBuckets
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hH_pos : 0 < H := by
    dsimp [H]
    positivity
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs_ge_two
  have hvalues_nonneg : ∀ i : Agent, 0 ≤ values i := by
    intro i
    linarith [hvalue_ge_one i]
  have hF_le_total : fixedPriceBenchmark ≤ totalValue := by
    rw [hF_eq, htotal]
    exact singlePriceRevenue_le_totalBidValue_of_nonneg values p hvalues_nonneg
  have hH_lt_total : H < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_power (by simpa [H] using hH_lt_total)
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * t ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity) (htail_bucket_floor j hj)
  have htail_set_count :
      ((tailSet.card : ℝ) * t) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass n ht_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i := by
    intro j hj
    exact hselected_largest j hj
  by_cases hfirst_case : fixedPriceBenchmark ≤ totalValue / s
  · have hlarge_first : 4 * H ≤ totalValue := by
      have hmul : fixedPriceBenchmark * s ≤ totalValue := by
        exact (le_div_iff₀ hs_pos).mp hfirst_case
      have htwoH_mul :
          (2 * H) * s ≤ fixedPriceBenchmark * s :=
        mul_le_mul_of_nonneg_right hF_ge_two_power (le_of_lt hs_pos)
      have hfour_le : 4 * H ≤ (2 * H) * s := by
        nlinarith
      nlinarith
    have hweighted_log :
        totalValue ≤
          192 * ((m + 1 : ℕ) : ℝ) * weightedPairingExpectedRevenue values :=
      paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins
        values m htotal hvalue_ge_one hvalue_le_power
        (by simpa [H] using hlarge_first)
    have hweighted :
        totalValue ≤ 192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
      have hmul := mul_le_mul_of_nonneg_right hlog_le_s_sq hW_nonneg
      exact le_trans hweighted_log (by nlinarith)
    have hfirst :
        fixedPriceBenchmark ≤
          192 * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_first_case_from_theorem7_1
        hs_pos hweighted hfirst_case
    have htarget :
        192 * s * weightedPairingExpectedRevenue values ≤
          576 * s * weightedPairingExpectedRevenue values := by
      nlinarith
    exact le_trans hfirst htarget
  · have hlt : totalValue / s < fixedPriceBenchmark := lt_of_not_ge hfirst_case
    have hcase : totalValue ≤ s * fixedPriceBenchmark := by
      have hmul : totalValue < fixedPriceBenchmark * s :=
        (div_lt_iff₀ hs_pos).mp hlt
      nlinarith
    have hF_nonneg : 0 ≤ fixedPriceBenchmark := by
      nlinarith
    have hsecond :
        fixedPriceBenchmark ≤
          ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set
        values bucket tailSet floorMass n htotal (by nlinarith) hs_pos
        hF_nonneg ht_nonneg hbucket_size hbucket_floor hbucket_upper
        hden_pos_agent hcase hF_eq hp_le_two_t
        (by simpa [tailSet] using hwinners_subset)
        htail_set_count hmass_bound
    simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 lower-bound certificate with separate fixed-price tail base
and selected bucket floor. This matches the paper proof route where the tail
starts at the dyadic bucket containing the fixed price, while the largest
bucket selected for the high/low split may occur higher in that tail.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_large_benchmark_base_tail
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s t baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (ht_nonneg : 0 ≤ t)
    (hbase_nonneg : 0 ≤ baseFloor)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let H : ℝ := (2 : ℝ) ^ (m + 1)
  let tailSet : Finset Agent := (Finset.range n).biUnion tailBuckets
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hH_pos : 0 < H := by
    dsimp [H]
    positivity
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs_ge_two
  have hvalues_nonneg : ∀ i : Agent, 0 ≤ values i := by
    intro i
    linarith [hvalue_ge_one i]
  have hF_le_total : fixedPriceBenchmark ≤ totalValue := by
    rw [hF_eq, htotal]
    exact singlePriceRevenue_le_totalBidValue_of_nonneg values p hvalues_nonneg
  have hH_lt_total : H < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_power (by simpa [H] using hH_lt_total)
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * baseFloor ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity) (htail_bucket_floor j hj)
  have htail_set_count :
      ((tailSet.card : ℝ) * baseFloor) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass n hbase_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i := by
    intro j hj
    exact hselected_largest j hj
  by_cases hfirst_case : fixedPriceBenchmark ≤ totalValue / s
  · have hlarge_first : 4 * H ≤ totalValue := by
      have hmul : fixedPriceBenchmark * s ≤ totalValue := by
        exact (le_div_iff₀ hs_pos).mp hfirst_case
      have htwoH_mul :
          (2 * H) * s ≤ fixedPriceBenchmark * s :=
        mul_le_mul_of_nonneg_right hF_ge_two_power (le_of_lt hs_pos)
      have hfour_le : 4 * H ≤ (2 * H) * s := by
        nlinarith
      nlinarith
    have hweighted_log :
        totalValue ≤
          192 * ((m + 1 : ℕ) : ℝ) * weightedPairingExpectedRevenue values :=
      paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins
        values m htotal hvalue_ge_one hvalue_le_power
        (by simpa [H] using hlarge_first)
    have hweighted :
        totalValue ≤ 192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
      have hmul := mul_le_mul_of_nonneg_right hlog_le_s_sq hW_nonneg
      exact le_trans hweighted_log (by nlinarith)
    have hfirst :
        fixedPriceBenchmark ≤
          192 * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_first_case_from_theorem7_1
        hs_pos hweighted hfirst_case
    have htarget :
        192 * s * weightedPairingExpectedRevenue values ≤
          576 * s * weightedPairingExpectedRevenue values := by
      nlinarith
    exact le_trans hfirst htarget
  · have hlt : totalValue / s < fixedPriceBenchmark := lt_of_not_ge hfirst_case
    have hcase : totalValue ≤ s * fixedPriceBenchmark := by
      have hmul : totalValue < fixedPriceBenchmark * s :=
        (div_lt_iff₀ hs_pos).mp hlt
      nlinarith
    have hF_nonneg : 0 ≤ fixedPriceBenchmark := by
      nlinarith
    have hsecond :
        fixedPriceBenchmark ≤
          ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set_base
        values bucket tailSet floorMass n htotal (by nlinarith) hs_pos
        hF_nonneg ht_nonneg hbase_nonneg hbucket_size hbucket_floor
        hbucket_upper hden_pos_agent hcase hF_eq hp_le_two_base
        (by simpa [tailSet] using hwinners_subset)
        htail_set_count hmass_bound
    simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 high-value lower-bound certificate. This is the same
largest-bucket/first-second-case argument as the dyadic certificate above, but
the high-value parameter is the paper's actual `h` rather than a rounded
power-of-two ceiling. The first case uses the Section 7.1 high-value wrapper
with `4h <= T`; the second case is unchanged.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_high_value_large_benchmark_base_tail
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (highValue : ℝ) (bucket : Finset Agent)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s t baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hhigh_ge_one : 1 ≤ highValue)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_high : ∀ i : Agent, values i ≤ highValue)
    (hF_ge_two_high : 2 * highValue ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 highValue + 2 ≤ s ^ 2)
    (ht_nonneg : 0 ≤ t)
    (hbase_nonneg : 0 ≤ baseFloor)
    (hbucket_size : 2 ≤ bucket.card)
    (hbucket_floor : ∀ i : Agent, i ∈ bucket → t ≤ values i)
    (hbucket_upper : ∀ i : Agent, i ∈ bucket → values i ≤ 2 * t)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤ ∑ i ∈ bucket, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let tailSet : Finset Agent := (Finset.range n).biUnion tailBuckets
  let floorMass : ℕ → ℝ := fun j => ∑ i ∈ tailBuckets j, values i
  have hhigh_pos : 0 < highValue :=
    lt_of_lt_of_le zero_lt_one hhigh_ge_one
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs_ge_two
  have hvalues_nonneg : ∀ i : Agent, 0 ≤ values i := by
    intro i
    linarith [hvalue_ge_one i]
  have hF_le_total : fixedPriceBenchmark ≤ totalValue := by
    rw [hF_eq, htotal]
    exact singlePriceRevenue_le_totalBidValue_of_nonneg values p hvalues_nonneg
  have hhigh_lt_total : highValue < totalValue := by
    nlinarith
  have hden_pos_agent :
      ∀ i : Agent, 0 < totalBidValue values - values i :=
    paper_weighted_pairing_den_pos_of_high_value_bound
      values htotal hvalue_le_high hhigh_lt_total
  have hW_nonneg :
      0 ≤ weightedPairingExpectedRevenue values :=
    weightedPairingExpectedRevenue_nonneg_of_den_nonneg values
      (fun i => le_of_lt (hden_pos_agent i))
  have hbucket_count_floor :
      ∀ j, j < n →
        ((tailBuckets j).card : ℝ) * baseFloor ≤ floorMass j / (2 : ℝ) ^ j := by
    intro j hj
    exact paper_theorem7_2_bucket_count_mass_le_total_div_scale
      values (tailBuckets j) (by positivity) (htail_bucket_floor j hj)
  have htail_set_count :
      ((tailSet.card : ℝ) * baseFloor) ≤
        paper_theorem7_2_dyadicGeometricTail floorMass n 0 :=
    paper_theorem7_2_tail_set_count_from_bucket_family
      tailSet tailBuckets floorMass n hbase_nonneg (by
        dsimp [tailSet]
        exact subset_rfl) hbucket_count_floor
  have hmass_bound :
      ∀ j, j < n → floorMass j ≤ ∑ i ∈ bucket, values i := by
    intro j hj
    exact hselected_largest j hj
  by_cases hfirst_case : fixedPriceBenchmark ≤ totalValue / s
  · have hlarge_first : 4 * highValue ≤ totalValue := by
      have hmul : fixedPriceBenchmark * s ≤ totalValue := by
        exact (le_div_iff₀ hs_pos).mp hfirst_case
      have htwoH_mul :
          (2 * highValue) * s ≤ fixedPriceBenchmark * s :=
        mul_le_mul_of_nonneg_right hF_ge_two_high (le_of_lt hs_pos)
      have hfour_le : 4 * highValue ≤ (2 * highValue) * s := by
        nlinarith
      nlinarith
    have hweighted_log :
        totalValue ≤
          192 * (Real.logb 2 highValue + 2) *
            weightedPairingExpectedRevenue values :=
      paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
        values htotal hhigh_ge_one hvalue_ge_one hvalue_le_high
        hlarge_first
    have hweighted :
        totalValue ≤ 192 * (s ^ 2) * weightedPairingExpectedRevenue values := by
      have hmul := mul_le_mul_of_nonneg_right hlog_le_s_sq hW_nonneg
      exact le_trans hweighted_log (by nlinarith)
    have hfirst :
        fixedPriceBenchmark ≤
          192 * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_first_case_from_theorem7_1
        hs_pos hweighted hfirst_case
    have htarget :
        192 * s * weightedPairingExpectedRevenue values ≤
          576 * s * weightedPairingExpectedRevenue values := by
      nlinarith
    exact le_trans hfirst htarget
  · have hlt : totalValue / s < fixedPriceBenchmark := lt_of_not_ge hfirst_case
    have hcase : totalValue ≤ s * fixedPriceBenchmark := by
      have hmul : totalValue < fixedPriceBenchmark * s :=
        (div_lt_iff₀ hs_pos).mp hlt
      nlinarith
    have hF_nonneg : 0 ≤ fixedPriceBenchmark := by
      nlinarith
    have hsecond :
        fixedPriceBenchmark ≤
          ((3 * 8) * (3 * 8)) * s * weightedPairingExpectedRevenue values :=
      paper_theorem7_2_second_case_largest_bucket_from_geometric_tail_set_base
        values bucket tailSet floorMass n htotal (by nlinarith) hs_pos
        hF_nonneg ht_nonneg hbase_nonneg hbucket_size hbucket_floor
        hbucket_upper hden_pos_agent hcase hF_eq hp_le_two_base
        (by simpa [tailSet] using hwinners_subset)
        htail_set_count hmass_bound
    simpa [show ((3 : ℝ) * 8) * (3 * 8) = 576 by norm_num] using hsecond

/--
GHW Theorem 7.2 lower-bound certificate where the selected largest bucket is
one of the finite dyadic tail buckets. The selected bucket floor is
`2^selected * baseFloor`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_selected_tail_bucket
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    (tailBuckets : ℕ → Finset Agent) (n selected : ℕ)
    {totalValue fixedPriceBenchmark s baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (hbase_nonneg : 0 ≤ baseFloor)
    (hselected_lt : selected < n)
    (hselected_size : 2 ≤ (tailBuckets selected).card)
    (hselected_upper :
      ∀ i : Agent, i ∈ tailBuckets selected →
        values i ≤ 2 * (((2 : ℝ) ^ selected) * baseFloor))
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i)
    (hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have ht_nonneg : 0 ≤ ((2 : ℝ) ^ selected) * baseFloor :=
    mul_nonneg (by positivity) hbase_nonneg
  have hselected_floor :
      ∀ i : Agent, i ∈ tailBuckets selected →
        ((2 : ℝ) ^ selected) * baseFloor ≤ values i :=
    htail_bucket_floor selected hselected_lt
  exact
    paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_large_benchmark_base_tail
      values m (tailBuckets selected) tailBuckets n htotal hvalue_ge_one
      hvalue_le_power hF_ge_two_power hs_ge_two hlog_le_s_sq ht_nonneg
      hbase_nonneg hselected_size hselected_floor hselected_upper hF_eq
      hp_le_two_base hwinners_subset htail_bucket_floor hselected_largest

/--
GHW Theorem 7.2 lower-bound certificate with the largest dyadic tail bucket
selected internally from the finite tail family. This matches the paper step
"Let `M` be the set of bids in a bucket with the largest total bid value";
callers provide the factor-two value bands for every bucket, plus the paper
fact that this largest bucket has at least two bidders.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_largest_tail_bucket
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    (tailBuckets : ℕ → Finset Agent) (n : ℕ)
    {totalValue fixedPriceBenchmark s baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (hbase_nonneg : 0 ≤ baseFloor)
    (hn : 0 < n)
    (hselected_size :
      2 ≤
        (tailBuckets
          (paper_theorem7_2_largestTailBucketIndex values tailBuckets n)).card)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range n).biUnion tailBuckets)
    (htail_bucket_floor :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i)
    (htail_bucket_upper :
      ∀ j, j < n → ∀ i : Agent, i ∈ tailBuckets j →
        values i ≤ 2 * (((2 : ℝ) ^ j) * baseFloor)) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let selected : ℕ :=
    paper_theorem7_2_largestTailBucketIndex values tailBuckets n
  have hselected_lt : selected < n := by
    simpa [selected] using
      paper_theorem7_2_largestTailBucketIndex_lt values tailBuckets hn
  have hselected_largest :
      ∀ j, j < n →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i := by
    simpa [selected] using
      paper_theorem7_2_largestTailBucketIndex_largest
        values tailBuckets hn
  have hselected_upper :
      ∀ i : Agent, i ∈ tailBuckets selected →
        values i ≤ 2 * (((2 : ℝ) ^ selected) * baseFloor) :=
    htail_bucket_upper selected hselected_lt
  have hselected_size' : 2 ≤ (tailBuckets selected).card := by
    simpa [selected] using hselected_size
  exact
    paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_selected_tail_bucket
      values m tailBuckets n selected htotal hvalue_ge_one hvalue_le_power
      hF_ge_two_power hs_ge_two hlog_le_s_sq hbase_nonneg hselected_lt
      hselected_size' hselected_upper hF_eq hp_le_two_base hwinners_subset
      htail_bucket_floor hselected_largest

/--
GHW Theorem 7.2 lower-bound certificate using the canonical dyadic tail
buckets above the fixed-price bucket. The remaining non-algebraic paper fact is
the size assertion that the largest dyadic bucket has at least two bidders.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_canonical_tail_buckets
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    {totalValue fixedPriceBenchmark s baseFloor p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (hbase_ge_one : 1 ≤ baseFloor)
    (hbase_le_p : baseFloor ≤ p)
    (hp_le_two_base : p ≤ 2 * baseFloor)
    (hselected_size :
      2 ≤
        (paper_theorem7_2_largestDyadicTailBucket
          values baseFloor m).card)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let tailBuckets : ℕ → Finset Agent :=
    paper_theorem7_2_dyadicTailBucket values baseFloor
  have hbase_nonneg : 0 ≤ baseFloor := le_trans (by norm_num) hbase_ge_one
  have hn : 0 < m + 1 := Nat.succ_pos m
  have hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range (m + 1)).biUnion tailBuckets := by
    simpa [tailBuckets] using
      paper_theorem7_2_winners_subset_dyadicTailBuckets_of_power_bound
        values m hbase_ge_one hbase_le_p hvalue_le_power
  have htail_bucket_floor :
      ∀ j, j < m + 1 → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * baseFloor ≤ values i := by
    intro j _hj i hi
    exact
      paper_theorem7_2_dyadicTailBucket_floor values baseFloor j i
        (by simpa [tailBuckets] using hi)
  have htail_bucket_upper :
      ∀ j, j < m + 1 → ∀ i : Agent, i ∈ tailBuckets j →
        values i ≤ 2 * (((2 : ℝ) ^ j) * baseFloor) := by
    intro j _hj i hi
    exact
      paper_theorem7_2_dyadicTailBucket_upper values baseFloor j i
        (by simpa [tailBuckets] using hi)
  have hselected_size' :
      2 ≤
        (tailBuckets
          (paper_theorem7_2_largestTailBucketIndex values tailBuckets
            (m + 1))).card := by
    simpa [tailBuckets, paper_theorem7_2_largestDyadicTailBucket,
      paper_theorem7_2_largestDyadicTailBucketIndex] using hselected_size
  exact
    paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_largest_tail_bucket
      values m tailBuckets (m + 1) htotal hvalue_ge_one hvalue_le_power
      hF_ge_two_power hs_ge_two hlog_le_s_sq hbase_nonneg hn
      hselected_size' hF_eq hp_le_two_base hwinners_subset
      htail_bucket_floor htail_bucket_upper

/--
GHW Theorem 7.2 lower-bound certificate with the paper's dyadic tail started
at the fixed price itself. The theorem now proves the paper's largest-bucket
size step internally from `F >= 2h`, leaving only the normalized value range,
the fixed-price representation of `F`, and the log-to-`s` certificate.
-/
theorem paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_fixed_price_tail
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    {totalValue fixedPriceBenchmark s p : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ fixedPriceBenchmark)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2)
    (hp_ge_one : 1 ≤ p)
    (hF_eq : fixedPriceBenchmark = singlePriceRevenue values p) :
    fixedPriceBenchmark ≤
      576 * s * weightedPairingExpectedRevenue values := by
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num) hp_ge_one
  have hp_le_two_self : p ≤ 2 * p := by nlinarith
  have hselected_size :
      2 ≤
        (paper_theorem7_2_largestDyadicTailBucket values p m).card :=
    paper_theorem7_2_largestDyadicTailBucket_card_two_of_large_fixed_price
      values m hvalue_ge_one hvalue_le_power hp_ge_one hF_eq
      hF_ge_two_power
  exact
    paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_canonical_tail_buckets
      values m htotal hvalue_ge_one hvalue_le_power hF_ge_two_power
      hs_ge_two hlog_le_s_sq hp_ge_one (le_rfl : p ≤ p) hp_le_two_self
      hselected_size hF_eq

/--
GHW Theorem 7.2 for the finite two-winner fixed-price benchmark `F^(2)`.
This is the paper-facing form of the lower bound: with all values normalized to
`[1, 2^(m+1)]`, if `F^(2) >= 2h` and `m+1 <= s^2`, then the weighted-pairing
auction earns a `1 / O(s)` fraction of `F^(2)`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) (m : ℕ)
    {totalValue s : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_power : ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1))
    (hF_ge_two_power :
      2 * (2 : ℝ) ^ (m + 1) ≤ twoWinnerFixedPriceBenchmarkValue values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : ((m + 1 : ℕ) : ℝ) ≤ s ^ 2) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      576 * s * weightedPairingExpectedRevenue values := by
  let p : ℝ := finiteCandidateOfferPrice values 2
  have hbenchmark_pos :
      0 < finiteCandidateFixedPriceBenchmark values 2 := by
    have hpow_pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
    simpa [twoWinnerFixedPriceBenchmarkValue] using
      lt_of_lt_of_le (by nlinarith : 0 < 2 * (2 : ℝ) ^ (m + 1))
        hF_ge_two_power
  have hp_ge_one : 1 ≤ p := by
    simpa [p] using
      finiteCandidateOfferPrice_ge_one_of_benchmark_pos values 2
        hvalue_ge_one hbenchmark_pos
  have hF_eq :
      twoWinnerFixedPriceBenchmarkValue values =
        singlePriceRevenue values p := by
    rw [twoWinnerFixedPriceBenchmarkValue]
    exact (singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark
      values 2).symm
  exact
    paper_theorem7_2_weighted_pairing_bound_from_power_two_bins_fixed_price_tail
      values m htotal hvalue_ge_one hvalue_le_power hF_ge_two_power
      hs_ge_two hlog_le_s_sq hp_ge_one hF_eq

/--
GHW Theorem 7.2 rounded `log_2 h` form for the finite two-winner benchmark.
The side condition is the paper high-value condition `F^(2) >= 2h`; only the
logarithmic coefficient is rounded as `log_2 h + 2`.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue s : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h :
      2 * h ≤ twoWinnerFixedPriceBenchmarkValue values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      576 * s * weightedPairingExpectedRevenue values := by
  classical
  let m : ℕ := Nat.ceil (Real.logb 2 h)
  have hh_pos : 0 < h := lt_of_lt_of_le zero_lt_one hh_ge_one
  have hlog_nonneg : 0 ≤ Real.logb 2 h :=
    Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hh_ge_one
  have hlog_le_m : Real.logb 2 h ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hh_le_rpow : h ≤ (2 : ℝ) ^ (m : ℝ) :=
    (Real.logb_le_iff_le_rpow
      (b := 2) (by norm_num : (1 : ℝ) < 2) hh_pos).mp hlog_le_m
  have hh_le_pow : h ≤ (2 : ℝ) ^ m := by
    simpa [Real.rpow_natCast] using hh_le_rpow
  have hh_le_pow_succ : h ≤ (2 : ℝ) ^ (m + 1) :=
    le_trans hh_le_pow
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ m))
  have hvalue_le_power :
      ∀ i : Agent, values i ≤ (2 : ℝ) ^ (m + 1) := by
    intro i
    exact le_trans (hvalue_le_h i) hh_le_pow_succ
  let p : ℝ := finiteCandidateOfferPrice values 2
  let tailBuckets : ℕ → Finset Agent :=
    paper_theorem7_2_dyadicTailBucket values p
  let selected : ℕ :=
    paper_theorem7_2_largestTailBucketIndex values tailBuckets (m + 1)
  have hbenchmark_pos :
      0 < finiteCandidateFixedPriceBenchmark values 2 := by
    simpa [twoWinnerFixedPriceBenchmarkValue] using
      lt_of_lt_of_le (by nlinarith : 0 < 2 * h) hF_ge_two_h
  have hp_ge_one : 1 ≤ p := by
    simpa [p] using
      finiteCandidateOfferPrice_ge_one_of_benchmark_pos values 2
        hvalue_ge_one hbenchmark_pos
  have hp_nonneg : 0 ≤ p := le_trans (by norm_num) hp_ge_one
  have hF_eq :
      twoWinnerFixedPriceBenchmarkValue values =
        singlePriceRevenue values p := by
    rw [twoWinnerFixedPriceBenchmarkValue]
    exact (singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark
      values 2).symm
  have hn : 0 < m + 1 := Nat.succ_pos m
  have hselected_lt : selected < m + 1 := by
    simpa [selected, tailBuckets] using
      paper_theorem7_2_largestTailBucketIndex_lt values tailBuckets hn
  have hselected_size :
      2 ≤ (tailBuckets selected).card := by
    have hsize :
        2 ≤ (paper_theorem7_2_largestDyadicTailBucket values p m).card :=
      paper_theorem7_2_largestDyadicTailBucket_card_two_of_large_fixed_price_high_value
        values m hh_ge_one hvalue_ge_one hvalue_le_h hvalue_le_power
        hp_ge_one hF_eq hF_ge_two_h
    simpa [tailBuckets, selected, paper_theorem7_2_largestDyadicTailBucket,
      paper_theorem7_2_largestDyadicTailBucketIndex] using hsize
  have hwinners_subset :
      ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) ⊆
        (Finset.range (m + 1)).biUnion tailBuckets := by
    simpa [tailBuckets] using
      paper_theorem7_2_winners_subset_dyadicTailBuckets_of_power_bound
        values m hp_ge_one (le_rfl : p ≤ p) hvalue_le_power
  have htail_bucket_floor :
      ∀ j, j < m + 1 → ∀ i : Agent, i ∈ tailBuckets j →
        ((2 : ℝ) ^ j) * p ≤ values i := by
    intro j _hj i hi
    exact
      paper_theorem7_2_dyadicTailBucket_floor values p j i
        (by simpa [tailBuckets] using hi)
  have htail_bucket_upper :
      ∀ j, j < m + 1 → ∀ i : Agent, i ∈ tailBuckets j →
        values i ≤ 2 * (((2 : ℝ) ^ j) * p) := by
    intro j _hj i hi
    exact
      paper_theorem7_2_dyadicTailBucket_upper values p j i
        (by simpa [tailBuckets] using hi)
  have hselected_largest :
      ∀ j, j < m + 1 →
        (∑ i ∈ tailBuckets j, values i) ≤
          ∑ i ∈ tailBuckets selected, values i := by
    simpa [selected] using
      paper_theorem7_2_largestTailBucketIndex_largest
        values tailBuckets hn
  have hselected_floor :
      ∀ i : Agent, i ∈ tailBuckets selected →
        ((2 : ℝ) ^ selected) * p ≤ values i :=
    htail_bucket_floor selected hselected_lt
  have hselected_upper :
      ∀ i : Agent, i ∈ tailBuckets selected →
        values i ≤ 2 * (((2 : ℝ) ^ selected) * p) :=
    htail_bucket_upper selected hselected_lt
  exact
    paper_theorem7_2_weighted_pairing_bound_from_high_value_large_benchmark_base_tail
      values h (tailBuckets selected) tailBuckets (m + 1)
      htotal hh_ge_one hvalue_ge_one hvalue_le_h hF_ge_two_h
      hs_ge_two hlog_le_s_sq
      (mul_nonneg (by positivity) hp_nonneg) hp_nonneg
      hselected_size hselected_floor hselected_upper hF_eq
      (by nlinarith : p ≤ 2 * p) hwinners_subset htail_bucket_floor
      hselected_largest

/--
Paper-facing high-value model for GHW Theorem 7.2. The rounded dyadic endpoint
uses the paper condition `F^(2) >= 2h`; the logarithmic coefficient remains
rounded as `log_2 h + 2`.
-/
structure PaperTheorem72WeightedPairingHighValueModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] where
  values : Agent → ℝ
  highValue : ℝ
  totalValue : ℝ
  scale : ℝ
  total_value_eq : totalValue = totalBidValue values
  highValue_ge_one : 1 ≤ highValue
  values_ge_one : ∀ i : Agent, 1 ≤ values i
  values_le_highValue : ∀ i : Agent, values i ≤ highValue
  benchmark_large :
    2 * highValue ≤ twoWinnerFixedPriceBenchmarkValue values
  scale_ge_two : 2 ≤ scale
  log_le_scale_sq : Real.logb 2 highValue + 2 ≤ scale ^ 2

/--
GHW Theorem 7.2 high-value paper-model form: under the rounded dyadic
high-value model, the weighted-pairing revenue gives the two-winner benchmark
bound.
-/
theorem paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_of_high_value_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (model : PaperTheorem72WeightedPairingHighValueModel Agent) :
    twoWinnerFixedPriceBenchmarkValue model.values ≤
      576 * model.scale * weightedPairingExpectedRevenue model.values := by
  exact
    paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
      model.values model.total_value_eq model.highValue_ge_one
      model.values_ge_one model.values_le_highValue model.benchmark_large
      model.scale_ge_two model.log_le_scale_sq

/--
GHW Theorem 7.2 tightness summation certificate. In the paper's tight example,
all levels below the top contribute `O(H/k)` each and the top level contributes
`O(H)`; this lemma packages the finite summation step as `W <= 3H`.
-/
theorem paper_theorem7_2_tightness_contribution_certificate
    {Level : Type*} [Fintype Level] [Nonempty Level]
    (lowerContribution : Level → ℝ)
    {weightedRevenue highContribution scale : ℝ}
    (hrevenue :
      weightedRevenue ≤ (∑ i : Level, lowerContribution i) +
        highContribution)
    (hlower :
      ∀ i : Level,
        lowerContribution i ≤
          (2 * scale) / (Fintype.card Level : ℝ))
    (hhigh : highContribution ≤ scale) :
    weightedRevenue ≤ 3 * scale := by
  let cardR : ℝ := Fintype.card Level
  have hcard_pos : 0 < cardR := by
    dsimp [cardR]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Level)
  have hcard_ne : cardR ≠ 0 := ne_of_gt hcard_pos
  have hlow_sum :
      (∑ i : Level, lowerContribution i) ≤ 2 * scale := by
    calc
      (∑ i : Level, lowerContribution i)
          ≤ ∑ _i : Level, (2 * scale) / (Fintype.card Level : ℝ) := by
            exact Finset.sum_le_sum fun i _ => hlower i
      _ = 2 * scale := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            change (Fintype.card Level : ℝ) *
                ((2 * scale) / cardR) = 2 * scale
            dsimp [cardR]
            field_simp [hcard_ne]
  nlinarith

/--
GHW Theorem 7.2 tightness ratio certificate. In the paper's example the
two-winner fixed-price benchmark is `F = s * H`, while the contribution
calculation gives weighted-pairing revenue at most `3H`; hence
`W <= (3/s) * F`.
-/
theorem paper_theorem7_2_tightness_ratio_certificate
    {Level : Type*} [Fintype Level] [Nonempty Level]
    (lowerContribution : Level → ℝ)
    {weightedRevenue highContribution scale fixedPriceBenchmark s : ℝ}
    (hs_pos : 0 < s)
    (hbenchmark : fixedPriceBenchmark = s * scale)
    (hrevenue :
      weightedRevenue ≤ (∑ i : Level, lowerContribution i) +
        highContribution)
    (hlower :
      ∀ i : Level,
        lowerContribution i ≤
          (2 * scale) / (Fintype.card Level : ℝ))
    (hhigh : highContribution ≤ scale) :
    weightedRevenue ≤ (3 / s) * fixedPriceBenchmark := by
  have hW :
      weightedRevenue ≤ 3 * scale :=
    paper_theorem7_2_tightness_contribution_certificate
      lowerContribution hrevenue hlower hhigh
  calc
    weightedRevenue ≤ 3 * scale := hW
    _ = (3 / s) * fixedPriceBenchmark := by
      rw [hbenchmark]
      field_simp [ne_of_gt hs_pos]

/--
GHW Theorem 7.2 tightness ratio certificate with only a benchmark lower bound.
The paper's tight example proves that the top price earns `s * H`, hence the
actual two-winner benchmark is at least `s * H`; this variant avoids requiring
an exact closed form for the benchmark.
-/
theorem paper_theorem7_2_tightness_ratio_certificate_of_benchmark_ge
    {Level : Type*} [Fintype Level] [Nonempty Level]
    (lowerContribution : Level → ℝ)
    {weightedRevenue highContribution scale fixedPriceBenchmark s : ℝ}
    (hs_pos : 0 < s)
    (hbenchmark_ge : s * scale ≤ fixedPriceBenchmark)
    (hrevenue :
      weightedRevenue ≤ (∑ i : Level, lowerContribution i) +
        highContribution)
    (hlower :
      ∀ i : Level,
        lowerContribution i ≤
          (2 * scale) / (Fintype.card Level : ℝ))
    (hhigh : highContribution ≤ scale) :
    weightedRevenue ≤ (3 / s) * fixedPriceBenchmark := by
  have hW :
      weightedRevenue ≤ 3 * scale :=
    paper_theorem7_2_tightness_contribution_certificate
      lowerContribution hrevenue hlower hhigh
  have hscaled :
      (3 / s) * (s * scale) ≤ (3 / s) * fixedPriceBenchmark := by
    exact mul_le_mul_of_nonneg_left hbenchmark_ge (by positivity)
  calc
    weightedRevenue ≤ 3 * scale := hW
    _ = (3 / s) * (s * scale) := by
      field_simp [ne_of_gt hs_pos]
    _ ≤ (3 / s) * fixedPriceBenchmark := hscaled

/--
Lower-level contribution in the GHW Theorem 7.2 tightness example, defined by
classifying each bidder into either a lower level `some l` or the top level
`none` and summing the concrete weighted-pairing expected payments in that
fiber.
-/
noncomputable def paper_theorem7_2_tightness_lowerContributionByClassifier
    {Agent Level : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Level]
    (values : Agent → ℝ) (classifier : Agent → Option Level)
    (level : Level) : ℝ :=
  ∑ i : Agent,
    if classifier i = some level then
      weightedPairingExpectedPayment values i
    else
      0

/-- Top-level contribution for the classifier split in the tightness example. -/
noncomputable def paper_theorem7_2_tightness_topContributionByClassifier
    {Agent Level : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Level]
    (values : Agent → ℝ) (classifier : Agent → Option Level) : ℝ :=
  ∑ i : Agent,
    if classifier i = none then
      weightedPairingExpectedPayment values i
    else
      0

theorem paper_theorem7_2_tightness_revenue_split_by_classifier
    {Agent Level : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Level] [DecidableEq Level]
    (values : Agent → ℝ) (classifier : Agent → Option Level) :
    weightedPairingExpectedRevenue values =
      (∑ level : Level,
        paper_theorem7_2_tightness_lowerContributionByClassifier
          values classifier level) +
      paper_theorem7_2_tightness_topContributionByClassifier
        values classifier := by
  classical
  have hpoint :
      ∀ i : Agent,
        weightedPairingExpectedPayment values i =
          (∑ level : Level,
            if classifier i = some level then
              weightedPairingExpectedPayment values i
            else
              0) +
          (if classifier i = none then
            weightedPairingExpectedPayment values i
          else
            0) := by
    intro i
    cases hclass : classifier i with
    | none =>
        simp
    | some level =>
        simp
  calc
    weightedPairingExpectedRevenue values
        = ∑ i : Agent,
            ((∑ level : Level,
              if classifier i = some level then
                weightedPairingExpectedPayment values i
              else
                0) +
            (if classifier i = none then
              weightedPairingExpectedPayment values i
          else
              0)) := by
          unfold weightedPairingExpectedRevenue
          exact Finset.sum_congr rfl fun i _ => hpoint i
    _ =
        (∑ i : Agent, ∑ level : Level,
          if classifier i = some level then
            weightedPairingExpectedPayment values i
          else
            0) +
        (∑ i : Agent,
          if classifier i = none then
            weightedPairingExpectedPayment values i
          else
            0) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ level : Level, ∑ i : Agent,
          if classifier i = some level then
            weightedPairingExpectedPayment values i
          else
            0) +
        (∑ i : Agent,
          if classifier i = none then
            weightedPairingExpectedPayment values i
          else
            0) := by
          rw [Finset.sum_comm]
    _ =
        (∑ level : Level,
          paper_theorem7_2_tightness_lowerContributionByClassifier
            values classifier level) +
        paper_theorem7_2_tightness_topContributionByClassifier
          values classifier := by
          simp [paper_theorem7_2_tightness_lowerContributionByClassifier,
            paper_theorem7_2_tightness_topContributionByClassifier]

/--
GHW Theorem 7.2 tightness ratio from a concrete classifier split of the
weighted-pairing revenue. This proves the bookkeeping step that the lower-level
and top-level contribution bounds cover the actual expected revenue.
-/
theorem paper_theorem7_2_tightness_ratio_from_classifier
    {Agent Level : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Level] [Nonempty Level] [DecidableEq Level]
    (values : Agent → ℝ) (classifier : Agent → Option Level)
    {scale fixedPriceBenchmark s : ℝ}
    (hs_pos : 0 < s)
    (hbenchmark : fixedPriceBenchmark = s * scale)
    (hlower :
      ∀ level : Level,
        paper_theorem7_2_tightness_lowerContributionByClassifier
            values classifier level ≤
          (2 * scale) / (Fintype.card Level : ℝ))
    (hhigh :
      paper_theorem7_2_tightness_topContributionByClassifier
          values classifier ≤ scale) :
    weightedPairingExpectedRevenue values ≤
      (3 / s) * fixedPriceBenchmark := by
  have hrevenue_eq :=
    paper_theorem7_2_tightness_revenue_split_by_classifier
      values classifier
  exact
    paper_theorem7_2_tightness_ratio_certificate
      (paper_theorem7_2_tightness_lowerContributionByClassifier
        values classifier)
      hs_pos hbenchmark (by rw [hrevenue_eq]) hlower hhigh

/--
GHW Theorem 7.2 tightness ratio from a concrete classifier split when the
fixed-price benchmark is only known to dominate the paper's constructed
benchmark value `s * H`.
-/
theorem paper_theorem7_2_tightness_ratio_from_classifier_benchmark_ge
    {Agent Level : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Level] [Nonempty Level] [DecidableEq Level]
    (values : Agent → ℝ) (classifier : Agent → Option Level)
    {scale fixedPriceBenchmark s : ℝ}
    (hs_pos : 0 < s)
    (hbenchmark_ge : s * scale ≤ fixedPriceBenchmark)
    (hlower :
      ∀ level : Level,
        paper_theorem7_2_tightness_lowerContributionByClassifier
            values classifier level ≤
          (2 * scale) / (Fintype.card Level : ℝ))
    (hhigh :
      paper_theorem7_2_tightness_topContributionByClassifier
          values classifier ≤ scale) :
    weightedPairingExpectedRevenue values ≤
      (3 / s) * fixedPriceBenchmark := by
  have hrevenue_eq :=
    paper_theorem7_2_tightness_revenue_split_by_classifier
      values classifier
  exact
    paper_theorem7_2_tightness_ratio_certificate_of_benchmark_ge
      (paper_theorem7_2_tightness_lowerContributionByClassifier
        values classifier)
      hs_pos hbenchmark_ge (by rw [hrevenue_eq]) hlower hhigh

/--
Lower-level bidders in the GHW Theorem 7.2 tightness family. Level `r`
represents value `2^(r+1)` and contains `2^(k-(r+1))` repeated bids.
-/
abbrev GhwTightLowerAgent (k : ℕ) :=
  Sigma fun r : Fin (k - 1) => Fin (2 ^ (k - (r.val + 1)))

/-- The full GHW Theorem 7.2 tightness family: lower levels plus `s` top bids. -/
abbrev GhwTightAgent (k s : ℕ) := GhwTightLowerAgent k ⊕ Fin s

/-- Bid values in the GHW Theorem 7.2 tightness family. -/
noncomputable def ghwTightValue (k s : ℕ) : GhwTightAgent k s → ℝ
  | Sum.inl a => (2 : ℝ) ^ (a.1.val + 1)
  | Sum.inr _ => (2 : ℝ) ^ k

/-- Classify the tightness-family bidders into lower levels and top bidders. -/
def ghwTightClassifier (k s : ℕ) :
    GhwTightAgent k s → Option (Fin (k - 1))
  | Sum.inl a => some a.1
  | Sum.inr _ => none

theorem paper_theorem7_2_tightness_lower_level_total
    {k : ℕ} (r : Fin (k - 1)) :
    ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
        (2 : ℝ) ^ (r.val + 1) =
      (2 : ℝ) ^ k := by
  have hle : r.val + 1 ≤ k := by
    have hr : r.val < k - 1 := r.isLt
    omega
  have hsum : k - (r.val + 1) + (r.val + 1) = k :=
    Nat.sub_add_cancel hle
  calc
    ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
        (2 : ℝ) ^ (r.val + 1)
        = (2 : ℝ) ^ (k - (r.val + 1)) *
            (2 : ℝ) ^ (r.val + 1) := by
          norm_num [Nat.cast_pow]
    _ = (2 : ℝ) ^ (k - (r.val + 1) + (r.val + 1)) := by
          rw [← pow_add]
    _ = (2 : ℝ) ^ k := by
          rw [hsum]

theorem paper_theorem7_2_tightness_lower_total (k s : ℕ) :
    (∑ a : GhwTightLowerAgent k, ghwTightValue k s (Sum.inl a)) =
      ((k - 1 : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  calc
    (∑ a : GhwTightLowerAgent k, ghwTightValue k s (Sum.inl a))
        = ∑ r : Fin (k - 1),
            ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
              (2 : ℝ) ^ (r.val + 1) := by
          simp [ghwTightValue, Fintype.sum_sigma, Finset.sum_const,
            nsmul_eq_mul]
    _ = ∑ _r : Fin (k - 1), (2 : ℝ) ^ k := by
          apply Finset.sum_congr rfl
          intro r _
          exact paper_theorem7_2_tightness_lower_level_total r
    _ = ((k - 1 : ℕ) : ℝ) * (2 : ℝ) ^ k := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The tightness family has total bid value `2^k(s+k-1)`. -/
theorem paper_theorem7_2_tightness_totalBidValue (k s : ℕ) :
    totalBidValue (ghwTightValue k s) =
      ((s + (k - 1) : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  rw [totalBidValue]
  rw [Fintype.sum_sum_type]
  rw [paper_theorem7_2_tightness_lower_total]
  have htop :
      (∑ x : Fin s, ghwTightValue k s (Sum.inr x)) =
        (s : ℝ) * (2 : ℝ) ^ k := by
    simp [ghwTightValue, Finset.sum_const, nsmul_eq_mul]
  rw [htop]
  norm_num [Nat.cast_add]
  ring_nf

/-- At price `2^k`, every top bid in the tightness family buys. -/
theorem paper_theorem7_2_tightness_top_saleCount_ge (k s : ℕ) :
    s ≤ saleCount (ghwTightValue k s) ((2 : ℝ) ^ k) := by
  classical
  let e : Fin s ↪ GhwTightAgent k s :=
    ⟨Sum.inr, by
      intro a b h
      exact Sum.inr.inj h⟩
  let topSet : Finset (GhwTightAgent k s) :=
    (Finset.univ : Finset (Fin s)).map e
  have htop_card : topSet.card = s := by
    simp [topSet, e]
  have hsubset :
      topSet ⊆
        (Finset.univ : Finset (GhwTightAgent k s)).filter
          (fun i => (2 : ℝ) ^ k ≤ ghwTightValue k s i) := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨a, _ha, rfl⟩
    simp [e, ghwTightValue]
  have hcard := Finset.card_le_card hsubset
  rw [htop_card] at hcard
  simpa [saleCount] using hcard

/--
The top price `2^k` earns exactly `s * 2^k` on the GHW tightness family.
-/
theorem paper_theorem7_2_tightness_singlePriceRevenue_top
    (k s : ℕ) :
    singlePriceRevenue (ghwTightValue k s) ((2 : ℝ) ^ k) =
      (s : ℝ) * (2 : ℝ) ^ k := by
  rw [singlePriceRevenue]
  rw [Fintype.sum_sum_type]
  have hlower :
      (∑ x : GhwTightLowerAgent k,
        if (2 : ℝ) ^ k ≤ ghwTightValue k s (Sum.inl x) then
          (2 : ℝ) ^ k
        else
          0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hlt_exp : x.1.val + 1 < k := by
      have hx : x.1.val < k - 1 := x.1.isLt
      omega
    have hlt : ghwTightValue k s (Sum.inl x) < (2 : ℝ) ^ k := by
      simp [ghwTightValue]
      exact pow_lt_pow_right₀ (by norm_num) hlt_exp
    simp [not_le_of_gt hlt]
  have htop :
      (∑ x : Fin s,
        if (2 : ℝ) ^ k ≤ ghwTightValue k s (Sum.inr x) then
          (2 : ℝ) ^ k
        else
          0) =
        (s : ℝ) * (2 : ℝ) ^ k := by
    simp [ghwTightValue, Finset.sum_const, nsmul_eq_mul]
  rw [hlower, htop]
  ring

/--
The actual two-winner fixed-price benchmark of the tightness family is at
least the paper's top-price revenue `s * 2^k`.
-/
theorem paper_theorem7_2_tightness_top_revenue_le_twoWinnerBenchmark
    (k s : ℕ) [Nonempty (GhwTightAgent k s)] (hs_two : 2 ≤ s) :
    (s : ℝ) * (2 : ℝ) ^ k ≤
      twoWinnerFixedPriceBenchmarkValue (ghwTightValue k s) := by
  have hprice_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hfeasible :
      2 ≤ saleCount (ghwTightValue k s) ((2 : ℝ) ^ k) :=
    le_trans hs_two (paper_theorem7_2_tightness_top_saleCount_ge k s)
  have hrev_le :
      singlePriceRevenue (ghwTightValue k s) ((2 : ℝ) ^ k) ≤
        finiteCandidateFixedPriceBenchmark (ghwTightValue k s) 2 :=
    singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      (ghwTightValue k s) (minWinners := 2) (by decide) hprice_nonneg
      hfeasible
  rw [← paper_theorem7_2_tightness_singlePriceRevenue_top k s]
  simpa [twoWinnerFixedPriceBenchmarkValue] using hrev_le

/--
The actual two-winner fixed-price benchmark for the GHW tightness family.
The proof `2 <= s` supplies the nonempty top block needed by the finite
candidate benchmark API.
-/
noncomputable def ghwTightTwoWinnerBenchmarkValue
    (k s : ℕ) (hs_two : 2 ≤ s) : ℝ :=
  have hs_pos : 0 < s := by omega
  haveI : Nonempty (GhwTightAgent k s) :=
    ⟨Sum.inr ⟨0, hs_pos⟩⟩
  twoWinnerFixedPriceBenchmarkValue (ghwTightValue k s)

private theorem paper_theorem7_2_tightness_sum_fin_two_pow_succ_le (n : ℕ) :
    (∑ r : Fin n, (2 : ℝ) ^ (r.val + 1)) ≤
      (2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hprefix :
          (∑ i : Fin n, (2 : ℝ) ^ ((Fin.castSucc i).val + 1)) ≤
            (2 : ℝ) ^ (n + 1) := by
        simpa using ih
      have hpow :
          (2 : ℝ) ^ (n + 2) =
            (2 : ℝ) ^ (n + 1) + (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        ring
      simp [Fin.val_last]
      nlinarith

private theorem paper_theorem7_2_tightness_prefix_two_pow_succ_le :
    ∀ n m : ℕ, m < n →
      (∑ q : Fin n, if q.val ≤ m then (2 : ℝ) ^ (q.val + 1) else 0) ≤
        2 * (2 : ℝ) ^ (m + 1)
  | 0, m, hm => False.elim (Nat.not_lt_zero _ hm)
  | n + 1, m, hm => by
      rw [Fin.sum_univ_castSucc]
      by_cases hmn : m = n
      · subst m
        have hprefix' :
            (∑ i : Fin n, (2 : ℝ) ^ (i.val + 1)) ≤
              (2 : ℝ) ^ (n + 1) :=
          paper_theorem7_2_tightness_sum_fin_two_pow_succ_le n
        have hprefix_eq :
            (∑ i : Fin n,
              if (Fin.castSucc i).val ≤ n then
                (2 : ℝ) ^ ((Fin.castSucc i).val + 1)
              else
                0) =
              ∑ i : Fin n, (2 : ℝ) ^ (i.val + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Fin.val_castSucc, Nat.le_of_lt i.isLt]
        rw [hprefix_eq]
        simp [Fin.val_last]
        nlinarith
      · have hm_lt_n : m < n := by omega
        have ih := paper_theorem7_2_tightness_prefix_two_pow_succ_le
          n m hm_lt_n
        have hprefix_eq :
            (∑ i : Fin n,
              if (Fin.castSucc i).val ≤ m then
                (2 : ℝ) ^ ((Fin.castSucc i).val + 1)
              else
                0) =
              ∑ i : Fin n,
                if i.val ≤ m then (2 : ℝ) ^ (i.val + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Fin.val_castSucc]
        rw [hprefix_eq]
        have hlast_zero : ¬ n ≤ m := Nat.not_le_of_gt hm_lt_n
        simp [Fin.val_last, hlast_zero]
        exact ih

/-- The lower levels in the tightness family have square mass at most `2^(2k)`. -/
theorem paper_theorem7_2_tightness_lower_square_sum_le (k s : ℕ) :
    (∑ a : GhwTightLowerAgent k,
        (ghwTightValue k s (Sum.inl a)) ^ 2) ≤
      ((2 : ℝ) ^ k) ^ 2 := by
  have hlevel :
      ∀ r : Fin (k - 1),
        ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
            ((2 : ℝ) ^ (r.val + 1)) ^ 2 =
          (2 : ℝ) ^ k * (2 : ℝ) ^ (r.val + 1) := by
    intro r
    calc
      ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
          ((2 : ℝ) ^ (r.val + 1)) ^ 2
          =
        (((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
            (2 : ℝ) ^ (r.val + 1)) *
          (2 : ℝ) ^ (r.val + 1) := by
          ring
      _ = (2 : ℝ) ^ k * (2 : ℝ) ^ (r.val + 1) := by
          rw [paper_theorem7_2_tightness_lower_level_total r]
  calc
    (∑ a : GhwTightLowerAgent k,
        (ghwTightValue k s (Sum.inl a)) ^ 2)
        = ∑ r : Fin (k - 1),
            ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
              ((2 : ℝ) ^ (r.val + 1)) ^ 2 := by
          simp [ghwTightValue, Fintype.sum_sigma, Finset.sum_const,
            nsmul_eq_mul]
    _ = ∑ r : Fin (k - 1),
          (2 : ℝ) ^ k * (2 : ℝ) ^ (r.val + 1) := by
          apply Finset.sum_congr rfl
          intro r _
          exact hlevel r
    _ = (2 : ℝ) ^ k *
          (∑ r : Fin (k - 1), (2 : ℝ) ^ (r.val + 1)) := by
          rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
          have hsum_le :
              (∑ r : Fin (k - 1), (2 : ℝ) ^ (r.val + 1)) ≤
                (2 : ℝ) ^ k := by
            cases k with
            | zero =>
                simp
            | succ k =>
                simpa using
                  paper_theorem7_2_tightness_sum_fin_two_pow_succ_le k
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ((2 : ℝ) ^ k) ^ 2 := by
          ring

/--
The full tightness family has square mass at most `(s+1) * (2^k)^2`.
This is the top-level numerator bound used in the expected-payment estimate.
-/
theorem paper_theorem7_2_tightness_square_sum_le (k s : ℕ) :
    (∑ i : GhwTightAgent k s, (ghwTightValue k s i) ^ 2) ≤
      (s + 1 : ℝ) * ((2 : ℝ) ^ k) ^ 2 := by
  rw [Fintype.sum_sum_type]
  have htop :
      (∑ x : Fin s, (ghwTightValue k s (Sum.inr x)) ^ 2) =
        (s : ℝ) * ((2 : ℝ) ^ k) ^ 2 := by
    simp [ghwTightValue, Finset.sum_const, nsmul_eq_mul]
  rw [htop]
  have hlower := paper_theorem7_2_tightness_lower_square_sum_le k s
  have hsq_nonneg : 0 ≤ ((2 : ℝ) ^ k) ^ 2 := sq_nonneg _
  nlinarith

/--
For a lower level `r` in the tightness family, all lower levels up to `r`
have square mass at most `2 * 2^k * 2^(r+1)`.
-/
theorem paper_theorem7_2_tightness_lower_prefix_square_sum_le
    (k s : ℕ) (r : Fin (k - 1)) :
    (∑ a : GhwTightLowerAgent k,
      if a.1.val ≤ r.val then
        (ghwTightValue k s (Sum.inl a)) ^ 2
      else
        0) ≤
      2 * (2 : ℝ) ^ k * (2 : ℝ) ^ (r.val + 1) := by
  have hlevel :
      ∀ q : Fin (k - 1),
        ((2 ^ (k - (q.val + 1)) : ℕ) : ℝ) *
            ((2 : ℝ) ^ (q.val + 1)) ^ 2 =
          (2 : ℝ) ^ k * (2 : ℝ) ^ (q.val + 1) := by
    intro q
    calc
      ((2 ^ (k - (q.val + 1)) : ℕ) : ℝ) *
          ((2 : ℝ) ^ (q.val + 1)) ^ 2
          =
        (((2 ^ (k - (q.val + 1)) : ℕ) : ℝ) *
            (2 : ℝ) ^ (q.val + 1)) *
          (2 : ℝ) ^ (q.val + 1) := by
          ring
      _ = (2 : ℝ) ^ k * (2 : ℝ) ^ (q.val + 1) := by
          rw [paper_theorem7_2_tightness_lower_level_total q]
  calc
    (∑ a : GhwTightLowerAgent k,
      if a.1.val ≤ r.val then
        (ghwTightValue k s (Sum.inl a)) ^ 2
      else
        0)
        =
      ∑ q : Fin (k - 1),
        if q.val ≤ r.val then
          ((2 ^ (k - (q.val + 1)) : ℕ) : ℝ) *
            ((2 : ℝ) ^ (q.val + 1)) ^ 2
        else
          0 := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : q.val ≤ r.val
          · simp [ghwTightValue, hq, Finset.sum_const, nsmul_eq_mul]
          · simp [hq]
    _ =
      ∑ q : Fin (k - 1),
        if q.val ≤ r.val then
          (2 : ℝ) ^ k * (2 : ℝ) ^ (q.val + 1)
        else
          0 := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : q.val ≤ r.val
          · simp [hq]
            simpa [Nat.cast_pow] using hlevel q
          · simp [hq]
    _ = (2 : ℝ) ^ k *
        (∑ q : Fin (k - 1),
          if q.val ≤ r.val then (2 : ℝ) ^ (q.val + 1) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : q.val ≤ r.val <;> simp [hq]
    _ ≤ (2 : ℝ) ^ k * (2 * (2 : ℝ) ^ (r.val + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (paper_theorem7_2_tightness_prefix_two_pow_succ_le
              (k - 1) r.val r.isLt)
            (by positivity)
    _ = 2 * (2 : ℝ) ^ k * (2 : ℝ) ^ (r.val + 1) := by
          ring

/--
Pointwise lower-level expected-payment bound for the GHW tightness family.
A bidder with value `2^(r+1)` pays at most `2*2^(r+1)/(k-1)` in expectation.
-/
theorem paper_theorem7_2_tightness_lower_payment_le
    (k s : ℕ) (hs_pos : 0 < s)
    (a : GhwTightLowerAgent k) :
    weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inl a) ≤
      (2 * (2 : ℝ) ^ (a.1.val + 1)) / ((k - 1 : ℕ) : ℝ) := by
  classical
  let H : ℝ := (2 : ℝ) ^ k
  let v : ℝ := (2 : ℝ) ^ (a.1.val + 1)
  have hH_pos : 0 < H := by
    dsimp [H]
    positivity
  have hlevel_lt : a.1.val + 1 < k := by
    have ha : a.1.val < k - 1 := a.1.isLt
    omega
  have hv_le_H : v ≤ H := by
    dsimp [v, H]
    exact le_of_lt (pow_lt_pow_right₀ (by norm_num) hlevel_lt)
  have hfilter_le_prefix :
      (∑ j ∈ (Finset.univ : Finset (GhwTightAgent k s)).filter
          (fun j =>
            j ≠ Sum.inl a ∧
              ghwTightValue k s j ≤ ghwTightValue k s (Sum.inl a)),
        (ghwTightValue k s j) ^ 2) ≤
      ∑ b : GhwTightLowerAgent k,
        if b.1.val ≤ a.1.val then
          (ghwTightValue k s (Sum.inl b)) ^ 2
        else
          0 := by
    rw [Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    have hlower :
        (∑ x : GhwTightLowerAgent k,
          if (Sum.inl x : GhwTightAgent k s) ≠ Sum.inl a ∧
              ghwTightValue k s (Sum.inl x) ≤
                ghwTightValue k s (Sum.inl a) then
            (ghwTightValue k s (Sum.inl x)) ^ 2
          else
            0) ≤
        ∑ b : GhwTightLowerAgent k,
          if b.1.val ≤ a.1.val then
            (ghwTightValue k s (Sum.inl b)) ^ 2
          else
            0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx :
          (Sum.inl x : GhwTightAgent k s) ≠ Sum.inl a ∧
            ghwTightValue k s (Sum.inl x) ≤
              ghwTightValue k s (Sum.inl a)
      · have hval_le :
            (2 : ℝ) ^ (x.1.val + 1) ≤
              (2 : ℝ) ^ (a.1.val + 1) := by
          simpa [ghwTightValue] using hx.2
        have hidx_le : x.1.val ≤ a.1.val := by
          have := (pow_le_pow_iff_right₀
            (by norm_num : (1 : ℝ) < 2)).mp hval_le
          omega
        simp [hx, hidx_le]
      · have hcond_false :
            ¬(¬x = a ∧
                ghwTightValue k s (Sum.inl x) ≤
                  ghwTightValue k s (Sum.inl a)) := by
          simpa using hx
        have hzero :
            (if (Sum.inl x : GhwTightAgent k s) ≠ Sum.inl a ∧
                ghwTightValue k s (Sum.inl x) ≤
                  ghwTightValue k s (Sum.inl a) then
              (ghwTightValue k s (Sum.inl x)) ^ 2
            else
              0) = 0 := by
          simp [hcond_false]
        rw [hzero]
        by_cases hidx : x.1.val ≤ a.1.val
        · simp [hidx, sq_nonneg]
        · simp [hidx]
    have htop_zero :
        (∑ x : Fin s,
          if (Sum.inr x : GhwTightAgent k s) ≠ Sum.inl a ∧
              ghwTightValue k s (Sum.inr x) ≤
                ghwTightValue k s (Sum.inl a) then
            (ghwTightValue k s (Sum.inr x)) ^ 2
          else
            0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hnot :
          ¬ ghwTightValue k s (Sum.inr x) ≤
            ghwTightValue k s (Sum.inl a) := by
        simp [ghwTightValue]
        exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hlevel_lt
      simp [hnot]
    linarith
  have hnum :
      (∑ j ∈ (Finset.univ : Finset (GhwTightAgent k s)).filter
          (fun j =>
            j ≠ Sum.inl a ∧
              ghwTightValue k s j ≤ ghwTightValue k s (Sum.inl a)),
        (ghwTightValue k s j) ^ 2) ≤
        2 * H * v := by
    exact le_trans hfilter_le_prefix
      (by
        simpa [H, v] using
          paper_theorem7_2_tightness_lower_prefix_square_sum_le k s a.1)
  have hden_lower :
      H * ((k - 1 : ℕ) : ℝ) ≤
        totalBidValue (ghwTightValue k s) -
          ghwTightValue k s (Sum.inl a) := by
    rw [paper_theorem7_2_tightness_totalBidValue]
    simp [ghwTightValue, H]
    have hsR : 1 ≤ (s : ℝ) := by
      exact_mod_cast hs_pos
    nlinarith [hv_le_H, hH_pos, hsR]
  have hden_nonneg :
      0 ≤ totalBidValue (ghwTightValue k s) -
        ghwTightValue k s (Sum.inl a) := by
    exact le_trans
      (mul_nonneg (le_of_lt hH_pos)
        (by exact_mod_cast Nat.zero_le (k - 1)))
      hden_lower
  have hpay_bound :
      weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inl a) ≤
        (2 * H * v) /
          (totalBidValue (ghwTightValue k s) -
            ghwTightValue k s (Sum.inl a)) :=
    weightedPairingExpectedPayment_le_div_of_filtered_square_sum_le
      (ghwTightValue k s) (Sum.inl a) hnum hden_nonneg
  have hkminus_nat_pos : 0 < k - 1 :=
    lt_of_le_of_lt (Nat.zero_le a.1.val) a.1.isLt
  have hkminus_pos : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hkminus_nat_pos
  have hden_pos :
      0 < totalBidValue (ghwTightValue k s) -
        ghwTightValue k s (Sum.inl a) :=
    lt_of_lt_of_le (mul_pos hH_pos hkminus_pos) hden_lower
  have hquot :
      (2 * H * v) /
          (totalBidValue (ghwTightValue k s) -
            ghwTightValue k s (Sum.inl a)) ≤
        (2 * v) / ((k - 1 : ℕ) : ℝ) := by
    apply PositiveDenominator.div_le_div_of_cross_mul_le hden_pos hkminus_pos
    calc
      (2 * H * v) * ((k - 1 : ℕ) : ℝ)
          = (2 * v) * (H * ((k - 1 : ℕ) : ℝ)) := by
          ring
      _ ≤
          (2 * v) *
            (totalBidValue (ghwTightValue k s) -
              ghwTightValue k s (Sum.inl a)) := by
          exact mul_le_mul_of_nonneg_left hden_lower (by positivity)
  exact le_trans hpay_bound (by simpa [v] using hquot)

/--
Lower-level contribution bound for the GHW tightness family. Each lower level
contributes at most `2*2^k/(k-1)` to weighted-pairing expected revenue.
-/
theorem paper_theorem7_2_tightness_lowerContribution_le
    (k s : ℕ) (hs_pos : 0 < s) (r : Fin (k - 1)) :
    paper_theorem7_2_tightness_lowerContributionByClassifier
        (ghwTightValue k s) (ghwTightClassifier k s) r ≤
      (2 * (2 : ℝ) ^ k) / ((k - 1 : ℕ) : ℝ) := by
  classical
  have hshape :
    paper_theorem7_2_tightness_lowerContributionByClassifier
        (ghwTightValue k s) (ghwTightClassifier k s) r =
      ∑ a : GhwTightLowerAgent k,
        if a.1 = r then
          weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inl a)
        else
          0 := by
    unfold paper_theorem7_2_tightness_lowerContributionByClassifier
    rw [Fintype.sum_sum_type]
    simp [ghwTightClassifier]
  rw [hshape]
  calc
    (∑ a : GhwTightLowerAgent k,
        if a.1 = r then
          weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inl a)
        else
          0)
        ≤ ∑ a : GhwTightLowerAgent k,
            if a.1 = r then
              (2 * (2 : ℝ) ^ (r.val + 1)) / ((k - 1 : ℕ) : ℝ)
            else
              0 := by
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : a.1 = r
          · have hpay :=
              paper_theorem7_2_tightness_lower_payment_le k s hs_pos a
            simpa [ha] using hpay
          · simp [ha]
    _ =
        ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
          ((2 * (2 : ℝ) ^ (r.val + 1)) / ((k - 1 : ℕ) : ℝ)) := by
          rw [Fintype.sum_sigma]
          have hinner :
              ∀ x : Fin (k - 1),
                (∑ y : Fin (2 ^ (k - (x.val + 1))),
                  if (⟨x, y⟩ : GhwTightLowerAgent k).1 = r then
                    (2 * (2 : ℝ) ^ (r.val + 1)) / ((k - 1 : ℕ) : ℝ)
                  else
                    0) =
                  if x = r then
                    ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
                      ((2 * (2 : ℝ) ^ (r.val + 1)) /
                        ((k - 1 : ℕ) : ℝ))
                  else
                    0 := by
            intro x
            by_cases hx : x = r
            · subst x
              simp [Finset.sum_const, nsmul_eq_mul]
            · simp [hx]
          simp_rw [hinner]
          simp
    _ = (2 * (2 : ℝ) ^ k) / ((k - 1 : ℕ) : ℝ) := by
          have htot := paper_theorem7_2_tightness_lower_level_total r
          calc
            ((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
                ((2 * (2 : ℝ) ^ (r.val + 1)) / ((k - 1 : ℕ) : ℝ))
                =
              (2 *
                (((2 ^ (k - (r.val + 1)) : ℕ) : ℝ) *
                  (2 : ℝ) ^ (r.val + 1))) /
                ((k - 1 : ℕ) : ℝ) := by
              ring
            _ = (2 * (2 : ℝ) ^ k) / ((k - 1 : ℕ) : ℝ) := by
              rw [htot]

/--
Top-level contribution bound for the GHW tightness family. When the number
of lower levels `k` is at least `s^2 + 2`, the total expected weighted-pairing
revenue contributed by the `s` top bids is at most `2^k`.
-/
theorem paper_theorem7_2_tightness_topContribution_le
    (k s : ℕ) (hs_pos : 0 < s) (hk_large : s * s + 2 ≤ k) :
    paper_theorem7_2_tightness_topContributionByClassifier
        (ghwTightValue k s) (ghwTightClassifier k s) ≤
      (2 : ℝ) ^ k := by
  classical
  let H : ℝ := (2 : ℝ) ^ k
  have hH_pos : 0 < H := by
    dsimp [H]
    positivity
  have hsR_pos : 0 < (s : ℝ) := by
    exact_mod_cast hs_pos
  have hden_factor_ge :
      ((s + 1 : ℝ) * (s : ℝ)) ≤
        (((s + (k - 1) : ℕ) : ℝ) - 1) := by
    have hk1 : 1 ≤ k := by omega
    have hkR : ((s * s + 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk_large
    rw [Nat.cast_add, Nat.cast_sub hk1]
    norm_num [Nat.cast_mul] at hkR ⊢
    nlinarith
  have htop_payment_le :
      ∀ t : Fin s,
        weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inr t) ≤
          H / (s : ℝ) := by
    intro t
    let i : GhwTightAgent k s := Sum.inr t
    have hfilter_le_total :
        (∑ j ∈ (Finset.univ : Finset (GhwTightAgent k s)).filter
            (fun j => j ≠ i ∧ ghwTightValue k s j ≤ ghwTightValue k s i),
          (ghwTightValue k s j) ^ 2) ≤
        ∑ j : GhwTightAgent k s, (ghwTightValue k s j) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp)
        (by intro x hx hnot; exact sq_nonneg _)
    have hnum :
        (∑ j ∈ (Finset.univ : Finset (GhwTightAgent k s)).filter
            (fun j => j ≠ i ∧ ghwTightValue k s j ≤ ghwTightValue k s i),
          (ghwTightValue k s j) ^ 2) ≤
          (s + 1 : ℝ) * H ^ 2 := by
      exact le_trans hfilter_le_total
        (by simpa [H] using paper_theorem7_2_tightness_square_sum_le k s)
    have hden_eq :
        totalBidValue (ghwTightValue k s) - ghwTightValue k s i =
          (((s + (k - 1) : ℕ) : ℝ) - 1) * H := by
      rw [paper_theorem7_2_tightness_totalBidValue]
      simp [i, ghwTightValue, H]
      ring
    have hden_nonneg :
        0 ≤ totalBidValue (ghwTightValue k s) - ghwTightValue k s i := by
      rw [hden_eq]
      exact mul_nonneg
        (le_trans (by positivity : 0 ≤ (s + 1 : ℝ) * (s : ℝ))
          hden_factor_ge)
        (le_of_lt hH_pos)
    have hpay_bound :
        weightedPairingExpectedPayment (ghwTightValue k s) i ≤
          ((s + 1 : ℝ) * H ^ 2) /
            (totalBidValue (ghwTightValue k s) - ghwTightValue k s i) :=
      weightedPairingExpectedPayment_le_div_of_filtered_square_sum_le
        (ghwTightValue k s) i hnum hden_nonneg
    have hquot :
        ((s + 1 : ℝ) * H ^ 2) /
            (totalBidValue (ghwTightValue k s) - ghwTightValue k s i) ≤
          H / (s : ℝ) := by
      rw [hden_eq]
      apply PositiveDenominator.div_le_div_of_cross_mul_le
      · exact mul_pos
          (lt_of_lt_of_le (mul_pos (by positivity) hsR_pos)
            hden_factor_ge)
          hH_pos
      · exact hsR_pos
      · calc
          ((s + 1 : ℝ) * H ^ 2) * (s : ℝ)
              ≤ H * ((((s + (k - 1) : ℕ) : ℝ) - 1) * H) := by
                have hmul :=
                  mul_le_mul_of_nonneg_right hden_factor_ge (sq_nonneg H)
                nlinarith [hmul]
          _ = H * ((((s + (k - 1) : ℕ) : ℝ) - 1) * H) := rfl
    exact le_trans hpay_bound hquot
  unfold paper_theorem7_2_tightness_topContributionByClassifier
  rw [Fintype.sum_sum_type]
  have hlower_zero :
      (∑ x : GhwTightLowerAgent k,
        if ghwTightClassifier k s (Sum.inl x) = none then
          weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inl x)
        else 0) = 0 := by
    simp [ghwTightClassifier]
  rw [hlower_zero]
  have htop_sum :
      (∑ x : Fin s,
        if ghwTightClassifier k s (Sum.inr x) = none then
          weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inr x)
        else 0) ≤ ∑ _x : Fin s, H / (s : ℝ) := by
    exact Finset.sum_le_sum fun x _ => by
      simp [ghwTightClassifier]
      exact htop_payment_le x
  calc
    0 + (∑ x : Fin s,
        if ghwTightClassifier k s (Sum.inr x) = none then
          weightedPairingExpectedPayment (ghwTightValue k s) (Sum.inr x)
        else 0) ≤ 0 + ∑ _x : Fin s, H / (s : ℝ) := by
          linarith
    _ = H := by
          simp [Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt hsR_pos]

/--
GHW Theorem 7.2 tightness endpoint for the repeated-bid family. For `s` top
bids of value `2^k` and lower levels containing `2^(k-r)` copies of value
`2^r`, the weighted-pairing auction earns at most `(3/s)` times the actual
two-winner fixed-price benchmark.
-/
theorem paper_theorem7_2_tightness_ratio_for_repeated_bid_family
    (k s : ℕ) (hs_two : 2 ≤ s)
    (hk_large : s * s + 2 ≤ k) :
    weightedPairingExpectedRevenue (ghwTightValue k s) ≤
      (3 / (s : ℝ)) *
        ghwTightTwoWinnerBenchmarkValue k s hs_two := by
  classical
  have hs_pos : 0 < s := by omega
  have hsR_pos : 0 < (s : ℝ) := by
    exact_mod_cast hs_pos
  have hs_sq_ge_one : 1 ≤ s * s :=
    Nat.succ_le_of_lt (Nat.mul_pos hs_pos hs_pos)
  have hkminus_pos_nat : 0 < k - 1 := by
    omega
  haveI : Nonempty (Fin (k - 1)) := ⟨⟨0, hkminus_pos_nat⟩⟩
  have hbenchmark_ge :
      (s : ℝ) * (2 : ℝ) ^ k ≤
        ghwTightTwoWinnerBenchmarkValue k s hs_two := by
    haveI : Nonempty (GhwTightAgent k s) :=
      ⟨Sum.inr ⟨0, hs_pos⟩⟩
    simpa [ghwTightTwoWinnerBenchmarkValue] using
      paper_theorem7_2_tightness_top_revenue_le_twoWinnerBenchmark k s hs_two
  exact
    paper_theorem7_2_tightness_ratio_from_classifier_benchmark_ge
      (values := ghwTightValue k s)
      (classifier := ghwTightClassifier k s)
      (scale := (2 : ℝ) ^ k)
      (fixedPriceBenchmark :=
        ghwTightTwoWinnerBenchmarkValue k s hs_two)
      (s := (s : ℝ))
      hsR_pos hbenchmark_ge
      (by
        intro level
        simpa using
          paper_theorem7_2_tightness_lowerContribution_le
            k s hs_pos level)
      (paper_theorem7_2_tightness_topContribution_le
        k s hs_pos hk_large)

/--
Own-bid-independent threshold-price digital-goods auctions are individually
rational.
-/
theorem paper_threshold_price_individually_rational
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) :
    (thresholdPriceAuction threshold).IndividuallyRational := by
  exact thresholdPriceAuction_individuallyRational threshold

/--
Threshold-price digital-goods auctions have no positive transfers when all
thresholds are nonnegative.
-/
theorem paper_threshold_price_no_positive_transfers
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hthreshold : ∀ bids i, 0 ≤ threshold bids i) :
    (thresholdPriceAuction threshold).NoPositiveTransfers := by
  exact thresholdPriceAuction_noPositiveTransfers threshold hthreshold

/--
GHW Lemma 8.1: "Suppose in a truthful auction `b_i < b_j`. Then
`p_i <= p_j`."

This is the paper's algebraic proof step: the hypotheses are exactly the two
truthfulness comparisons for a low value `bi` and high value `bj`, written using
win probabilities `pi,pj` and expected winning costs `ci,cj`.
-/
theorem paper_lemma8_1_truthful_win_probability_monotone
    {bi bj pi pj ci cj : ℝ} (hbid : bi < bj)
    (hlow : pj * (bi - cj) ≤ pi * (bi - ci))
    (hhigh : pi * (bj - ci) ≤ pj * (bj - cj)) :
    pi ≤ pj := by
  exact DigitalGoodsAuction.winProbability_mono_of_truthful_utility_inequalities
    hbid hlow hhigh

/--
GHW Lemma 8.1, payment form. This is the same adjacent-truthfulness algebra
written directly with expected payments rather than conditional expected
winning costs: truthful comparisons at values `bi < bj` imply `pi <= pj`.
-/
theorem paper_lemma8_1_truthful_win_probability_monotone_payments
    {bi bj pi pj payi payj : ℝ} (hbid : bi < bj)
    (hlow : pj * bi - payj ≤ pi * bi - payi)
    (hhigh : pi * bj - payi ≤ pj * bj - payj) :
    pi ≤ pj := by
  nlinarith

/--
GHW Lemma 8.1, direct-revelation form: in a truthful digital-goods auction,
holding other reports fixed, increasing bidder `i`'s own bid weakly increases
that bidder's allocation probability/quantity.
-/
theorem paper_lemma8_1_allocation_mono_own_bid_of_truthful
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : paper_digital_goods_truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  rw [paper_digital_goods_truthful_eq] at hM
  exact DigitalGoodsAuction.allocation_mono_own_bid_of_truthful
    M hM bids i hlt

/-- Paper-ranked bidder enumeration in nondecreasing value order. -/
noncomputable def paper_ranked_agent
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) : Fin n → Agent :=
  FiniteRanking.rankAgentByValue (Finset.univ : Finset Agent) values hcard

/--
Paper-ranked bid value sequence: enumerate the finite bidder set in
nondecreasing value order and expose the rank values as a natural-indexed
sequence. Indices outside the finite rank range are set to zero.
-/
noncomputable def paper_ranked_bid_value
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) : ℕ → ℝ :=
  fun k =>
    if hk : k < n then
      FiniteRanking.rankValueByValue
        (Finset.univ : Finset Agent) values hcard ⟨k, hk⟩
    else 0

/-- The paper-ranked bid value at an in-range index is the ranked agent's value. -/
theorem paper_ranked_bid_value_eq_value_ranked_agent
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) (i : Fin n) :
    paper_ranked_bid_value values hcard i.val =
      values (paper_ranked_agent values hcard i) := by
  simpa [paper_ranked_bid_value, paper_ranked_agent, i.isLt] using
    FiniteRanking.rankValueByValue_eq_value
      (Finset.univ : Finset Agent) values hcard i

/--
In a ranked bid profile, the fixed-price revenue term
`V_j = b_j * (n-j)` used in GHW Theorem 8.2 is bounded by the actual
one-winner finite fixed-price benchmark: price `b_j` sells to every bidder at
rank at least `j`.
-/
theorem paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (j : Fin n)
    (hprice_nonneg :
      0 ≤ paper_ranked_bid_value values hcard j.val) :
    FiniteSum.rankedFixedPriceRevenue n
        (paper_ranked_bid_value values hcard) j.val ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let price : ℝ := paper_ranked_bid_value values hcard j.val
  let upper : Finset Agent :=
    FiniteRanking.upperRankFinset
      (Finset.univ : Finset Agent) values hcard j.val
  have hprice_rank :
      price =
        FiniteRanking.rankValueByValue
          (Finset.univ : Finset Agent) values hcard j := by
    simp [price, paper_ranked_bid_value, j.isLt]
  have hupper_subset :
      upper ⊆ ((Finset.univ : Finset Agent).filter fun i => price ≤ values i) := by
    intro a ha
    unfold upper FiniteRanking.upperRankFinset at ha
    rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
    have hj_le_r : j.val ≤ r.val := (Finset.mem_filter.mp hr).2
    have hprice_le_rank :
        price ≤
          FiniteRanking.rankValueByValue
            (Finset.univ : Finset Agent) values hcard r := by
      rw [hprice_rank]
      rcases lt_or_eq_of_le hj_le_r with hj_lt_r | hj_eq_r
      · exact FiniteRanking.rankValueByValue_mono
          (Finset.univ : Finset Agent) values hcard j r hj_lt_r
      · have hjr : j = r := Fin.ext hj_eq_r
        rw [hjr]
    have hrank_value :
        FiniteRanking.rankValueByValue
            (Finset.univ : Finset Agent) values hcard r =
          values
            (FiniteRanking.rankAgentByValue
              (Finset.univ : Finset Agent) values hcard r) :=
      FiniteRanking.rankValueByValue_eq_value
        (Finset.univ : Finset Agent) values hcard r
    exact Finset.mem_filter.mpr ⟨by simp, by simpa [hrank_value] using hprice_le_rank⟩
  have hupper_card :
      upper.card = n - j.val := by
    dsimp [upper]
    rw [FiniteRanking.upperRankFinset_card]
    rw [min_eq_right (Nat.le_of_lt j.isLt)]
  have hsale_ge_upper :
      upper.card ≤ saleCount values price := by
    unfold saleCount
    exact Finset.card_le_card hupper_subset
  have hupper_nonempty : 1 ≤ upper.card := by
    rw [hupper_card]
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt j.isLt)
  have hfeasible : 1 ≤ saleCount values price :=
    le_trans hupper_nonempty hsale_ge_upper
  have hbenchmark :
      singlePriceRevenue values price ≤
        finiteCandidateFixedPriceBenchmark values 1 :=
    singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      values (minWinners := 1) (by decide) hprice_nonneg hfeasible
  have hcount_bound :
      ((n - j.val : ℕ) : ℝ) ≤ (saleCount values price : ℝ) := by
    exact_mod_cast (by simpa [hupper_card] using hsale_ge_upper)
  have hsub_cast :
      ((n - j.val : ℕ) : ℝ) = (n : ℝ) - (j.val : ℝ) := by
    exact Nat.cast_sub (Nat.le_of_lt j.isLt)
  have hranked_le_single :
      FiniteSum.rankedFixedPriceRevenue n
          (paper_ranked_bid_value values hcard) j.val ≤
        singlePriceRevenue values price := by
    rw [FiniteSum.rankedFixedPriceRevenue, singlePriceRevenue_eq_saleCount_mul]
    have hprice_eq :
        paper_ranked_bid_value values hcard j.val = price := rfl
    rw [hprice_eq, ← hsub_cast]
    exact mul_le_mul_of_nonneg_right hcount_bound hprice_nonneg
  exact le_trans hranked_le_single hbenchmark

/--
GHW Theorem 8.2 certificate form: "For any truthful auction, `E[R] <= F`."

The paper proves this by rewriting expected revenue as a weighted sum of
fixed-price revenues `V_j`, where the weights are nonnegative by Lemma 8.1 and
sum to at most one. This theorem formalizes that final benchmark step; the
remaining paper work is to connect a concrete randomized truthful auction to
these certificate hypotheses.
-/
theorem paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_certificate
    {Index : Type*} [Fintype Index]
    {expectedRevenue fixedPriceBenchmark : ℝ}
    (weight fixedPriceRevenue : Index → ℝ)
    (hrevenue :
      expectedRevenue ≤ ∑ i : Index, weight i * fixedPriceRevenue i)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : Index, weight i) ≤ 1)
    (hfixed : ∀ i, fixedPriceRevenue i ≤ fixedPriceBenchmark)
    (hbenchmark_nonneg : 0 ≤ fixedPriceBenchmark) :
    expectedRevenue ≤ fixedPriceBenchmark := by
  exact DigitalGoodsAuction.expectedRevenue_le_fixedPriceBenchmark_of_weighted_certificate
    weight fixedPriceRevenue hrevenue hweight_nonneg hweight_sum hfixed
    hbenchmark_nonneg

/--
GHW Theorem 8.2 monotone-probability form. This matches the paper's final
telescoping expression: expected revenue is bounded by a sum of adjacent win
probability increments times fixed-price revenues. Lemma 8.1 supplies
monotonicity of `winProbability`; the endpoint hypothesis says the total
probability mass is at most one.
-/
theorem paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_monotone_probabilities
    (n : ℕ) (winProbability fixedPriceRevenueAtRank : ℕ → ℝ)
    {expectedRevenue fixedPriceBenchmark : ℝ}
    (hrevenue :
      expectedRevenue ≤
        ∑ j ∈ Finset.range n,
          (winProbability (j + 1) - winProbability j) *
            fixedPriceRevenueAtRank j)
    (hmono : ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1)
    (hfixed : ∀ j, j < n → fixedPriceRevenueAtRank j ≤ fixedPriceBenchmark)
    (hbenchmark_nonneg : 0 ≤ fixedPriceBenchmark) :
    expectedRevenue ≤ fixedPriceBenchmark := by
  exact FiniteSum.le_bound_of_le_range_probabilityIncrement_weighted_sum
    n winProbability fixedPriceRevenueAtRank hrevenue hmono hendpoint hfixed
    hbenchmark_nonneg

/--
GHW Theorem 8.2 payoff-recursion form. This combines the paper's two algebraic
steps after truthfulness:

1. each ranked bidder's expected payment is bounded by its value times its win
   probability minus the accumulated adjacent utility gaps; and
2. the resulting sum telescopes into adjacent win-probability increments times
   fixed-price revenues `b_j * (n-j)`.

Together with Lemma 8.1 monotonicity, endpoint probability mass at most one,
and `V_j <= F`, this proves `E[R] <= F`.
-/
theorem paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_gain_bounds
    (n : ℕ) (winProbability bidValue bidderExpectedRevenue : ℕ → ℝ)
    {expectedRevenue fixedPriceBenchmark : ℝ}
    (hp0 : winProbability 0 = 0)
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, bidderExpectedRevenue i)
    (hbidderRevenue :
      ∀ i, i < n →
        bidderExpectedRevenue i ≤
          winProbability (i + 1) * bidValue i -
            ∑ j ∈ Finset.range i,
              winProbability (j + 1) * (bidValue (j + 1) - bidValue j))
    (hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1)
    (hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n bidValue j ≤ fixedPriceBenchmark)
    (hbenchmark_nonneg : 0 ≤ fixedPriceBenchmark) :
    expectedRevenue ≤ fixedPriceBenchmark := by
  have hrearranged :
      expectedRevenue ≤
        ∑ j ∈ Finset.range n,
          (winProbability (j + 1) - winProbability j) *
            FiniteSum.rankedFixedPriceRevenue n bidValue j := by
    exact le_trans hrevenue
      (FiniteSum.sum_range_revenue_le_probabilityIncrement_rankedFixedPriceRevenue
        n winProbability bidValue bidderExpectedRevenue hp0 hbidderRevenue)
  exact FiniteSum.le_bound_of_le_range_probabilityIncrement_weighted_sum
    n winProbability (FiniteSum.rankedFixedPriceRevenue n bidValue)
    hrearranged hmono hendpoint hfixed hbenchmark_nonneg

/--
GHW Theorem 8.2 adjacent-gain-recursion form. This exposes the paper's proof
one step earlier than `..._of_gain_bounds`: the hypotheses say expected bidder
revenue is `p_i b_i - g_i`, `g_1` is nonnegative, and adjacent truthful
comparisons give `g_{i+1} >= g_i + p_i(b_{i+1}-b_i)`.
-/
theorem paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_adjacent_gain_recursion
    (n : ℕ) (winProbability bidValue bidderExpectedRevenue gain : ℕ → ℝ)
    {expectedRevenue fixedPriceBenchmark : ℝ}
    (hp0 : winProbability 0 = 0)
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, bidderExpectedRevenue i)
    (hbidderRevenue :
      ∀ i, i < n →
        bidderExpectedRevenue i =
          winProbability (i + 1) * bidValue i - gain i)
    (hgain0 : 0 ≤ gain 0)
    (hgain_step :
      ∀ i,
        gain i + winProbability (i + 1) *
          (bidValue (i + 1) - bidValue i) ≤ gain (i + 1))
    (hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1)
    (hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n bidValue j ≤ fixedPriceBenchmark)
    (hbenchmark_nonneg : 0 ≤ fixedPriceBenchmark) :
    expectedRevenue ≤ fixedPriceBenchmark := by
  exact FiniteSum.revenue_le_bound_of_adjacent_gain_recursion
    n winProbability bidValue bidderExpectedRevenue gain hp0 hrevenue
    hbidderRevenue hgain0 hgain_step hmono hendpoint hfixed
    hbenchmark_nonneg

/--
GHW Theorem 8.2 in the paper's `p_i`, `c_i`, `g_i` notation. The hypotheses
include the adjacent truthful comparison
`p_i (b_{i+1} - c_i) <= g_{i+1}`, which is the direct expected-utility
inequality used in the paper after Equation (1).
-/
theorem paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_truthful_cost_comparisons
    (n : ℕ) (winProbability bidValue expectedCost gain : ℕ → ℝ)
    {expectedRevenue fixedPriceBenchmark : ℝ}
    (hp0 : winProbability 0 = 0)
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, winProbability (i + 1) * expectedCost i)
    (hgain :
      ∀ i, gain i =
        winProbability (i + 1) * (bidValue i - expectedCost i))
    (hgain0 : 0 ≤ gain 0)
    (htruth_adjacent :
      ∀ i,
        winProbability (i + 1) * (bidValue (i + 1) - expectedCost i) ≤
          gain (i + 1))
    (hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1)
    (hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n bidValue j ≤ fixedPriceBenchmark)
    (hbenchmark_nonneg : 0 ≤ fixedPriceBenchmark) :
    expectedRevenue ≤ fixedPriceBenchmark := by
  exact FiniteSum.revenue_le_bound_of_adjacent_truthful_cost_comparisons
    n winProbability bidValue expectedCost gain hp0 hrevenue hgain hgain0
    htruth_adjacent hmono hendpoint hfixed hbenchmark_nonneg

/--
GHW Theorem 8.2 ranked finite-benchmark form. This keeps the paper's
`p_i,c_i,g_i` proof obligations, but instantiates `V_j <= F` with the actual
one-winner finite fixed-price benchmark of the ranked bid profile.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_cost_comparisons
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (winProbability expectedCost gain : ℕ → ℝ)
    {expectedRevenue : ℝ}
    (hp0 : winProbability 0 = 0)
    (hprice_nonneg :
      ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j)
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, winProbability (i + 1) * expectedCost i)
    (hgain :
      ∀ i, gain i =
        winProbability (i + 1) *
          (paper_ranked_bid_value values hcard i - expectedCost i))
    (hgain0 : 0 ≤ gain 0)
    (htruth_adjacent :
      ∀ i,
        winProbability (i + 1) *
          (paper_ranked_bid_value values hcard (i + 1) - expectedCost i) ≤
          gain (i + 1))
    (hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1) :
    expectedRevenue ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  have hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n
            (paper_ranked_bid_value values hcard) j ≤
          finiteCandidateFixedPriceBenchmark values 1 := by
    intro j hj
    exact
      paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark
        values hcard ⟨j, hj⟩ (hprice_nonneg j hj)
  exact
    paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_truthful_cost_comparisons
      n winProbability (paper_ranked_bid_value values hcard) expectedCost gain
      hp0 hrevenue hgain hgain0 htruth_adjacent hmono hendpoint hfixed
      (finiteCandidateFixedPriceBenchmark_nonneg values 1)

/--
GHW Theorem 8.2 ranked pairwise-truthfulness form. This discharges the
monotonicity hypothesis in the previous wrapper from the adjacent pairwise
truthfulness inequalities used in Lemma 8.1. The remaining assumptions are the
paper's ranked revenue decomposition, expected-cost/gain identities, endpoint
probability bound, and strict adjacent rank values after tie breaking.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthfulness
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (winProbability expectedCost gain : ℕ → ℝ)
    {expectedRevenue : ℝ}
    (hp0 : winProbability 0 = 0)
    (hfirst_probability_nonneg : 0 ≤ winProbability 1)
    (hprice_nonneg :
      ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j)
    (hprice_strict :
      ∀ i, i + 1 < n →
        paper_ranked_bid_value values hcard i <
          paper_ranked_bid_value values hcard (i + 1))
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, winProbability (i + 1) * expectedCost i)
    (hgain :
      ∀ i, gain i =
        winProbability (i + 1) *
          (paper_ranked_bid_value values hcard i - expectedCost i))
    (hgain0 : 0 ≤ gain 0)
    (htruth_high :
      ∀ i, i + 1 < n →
        winProbability (i + 1) *
          (paper_ranked_bid_value values hcard (i + 1) - expectedCost i) ≤
          gain (i + 1))
    (htruth_low :
      ∀ i, i + 1 < n →
        winProbability (i + 2) *
          (paper_ranked_bid_value values hcard i - expectedCost (i + 1)) ≤
          winProbability (i + 1) *
            (paper_ranked_bid_value values hcard i - expectedCost i))
    (hendpoint : winProbability n - winProbability 0 ≤ 1) :
    expectedRevenue ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  have hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1) := by
    intro j hj
    cases j with
    | zero =>
        simpa [hp0] using hfirst_probability_nonneg
    | succ i =>
        have hi : i + 1 < n := by
          simpa [Nat.succ_eq_add_one] using hj
        have hhigh :
            winProbability (i + 1) *
              (paper_ranked_bid_value values hcard (i + 1) -
                expectedCost i) ≤
              winProbability (i + 2) *
                (paper_ranked_bid_value values hcard (i + 1) -
                  expectedCost (i + 1)) := by
          have ht := htruth_high i hi
          rw [hgain (i + 1)] at ht
          simpa [Nat.add_assoc, Nat.succ_eq_add_one] using ht
        exact
          DigitalGoodsAuction.winProbability_mono_of_truthful_utility_inequalities
            (hprice_strict i hi) (htruth_low i hi) hhigh
  have hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n
            (paper_ranked_bid_value values hcard) j ≤
          finiteCandidateFixedPriceBenchmark values 1 := by
    intro j hj
    exact
      paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark
        values hcard ⟨j, hj⟩ (hprice_nonneg j hj)
  exact
    FiniteSum.revenue_le_bound_of_adjacent_truthful_cost_comparisons_bounded
      n winProbability (paper_ranked_bid_value values hcard) expectedCost gain
      hp0 hrevenue hgain hgain0 htruth_high hmono hendpoint hfixed
      (finiteCandidateFixedPriceBenchmark_nonneg values 1)

/--
GHW Theorem 8.2 ranked payment form with monotone win probabilities supplied
directly. This is the algebraic core after Lemma 8.1: expected payments and
adjacent gain recursion imply the benchmark bound once the ranked win
probabilities are monotone.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_payments_mono
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (winProbability expectedPayment : ℕ → ℝ)
    {expectedRevenue : ℝ}
    (hp0 : winProbability 0 = 0)
    (hprice_nonneg :
      ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j)
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, expectedPayment i)
    (hgain0 :
      0 ≤ winProbability 1 * paper_ranked_bid_value values hcard 0 -
        expectedPayment 0)
    (htruth_high :
      ∀ i, i + 1 < n →
        winProbability (i + 1) *
            paper_ranked_bid_value values hcard (i + 1) -
          expectedPayment i ≤
        winProbability (i + 2) *
            paper_ranked_bid_value values hcard (i + 1) -
          expectedPayment (i + 1))
    (hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1))
    (hendpoint : winProbability n - winProbability 0 ≤ 1) :
    expectedRevenue ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  let bidValue : ℕ → ℝ := paper_ranked_bid_value values hcard
  let gain : ℕ → ℝ := fun i => winProbability (i + 1) * bidValue i -
    expectedPayment i
  have hfixed :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n bidValue j ≤
          finiteCandidateFixedPriceBenchmark values 1 := by
    intro j hj
    exact
      paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark
        values hcard ⟨j, hj⟩ (hprice_nonneg j hj)
  have hrevenueAtRank :
      ∀ i, i < n →
        expectedPayment i = winProbability (i + 1) * bidValue i - gain i := by
    intro i _hi
    dsimp [gain]
    ring
  have hgain0' : 0 ≤ gain 0 := by
    simpa [gain, bidValue] using hgain0
  have hgain_step :
      ∀ i, i + 1 < n →
        gain i + winProbability (i + 1) *
            (bidValue (i + 1) - bidValue i) ≤ gain (i + 1) := by
    intro i hi
    have ht := htruth_high i hi
    dsimp [gain, bidValue]
    linarith
  exact
    FiniteSum.revenue_le_bound_of_adjacent_gain_recursion_bounded
      n winProbability bidValue expectedPayment gain hp0 hrevenue
      hrevenueAtRank hgain0' hgain_step hmono hendpoint hfixed
      (finiteCandidateFixedPriceBenchmark_nonneg values 1)

/--
GHW Theorem 8.2 ranked pairwise-truthfulness form using expected payments
directly. This matches the direct-revelation utility comparisons
`b * p - payment` and avoids introducing a separate conditional expected cost
variable. Strict adjacent rank values are used only to derive monotone ranked
win probabilities from the two adjacent utility comparisons.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthful_payments
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (winProbability expectedPayment : ℕ → ℝ)
    {expectedRevenue : ℝ}
    (hp0 : winProbability 0 = 0)
    (hfirst_probability_nonneg : 0 ≤ winProbability 1)
    (hprice_nonneg :
      ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j)
    (hprice_strict :
      ∀ i, i + 1 < n →
        paper_ranked_bid_value values hcard i <
          paper_ranked_bid_value values hcard (i + 1))
    (hrevenue :
      expectedRevenue ≤
        ∑ i ∈ Finset.range n, expectedPayment i)
    (hgain0 :
      0 ≤ winProbability 1 * paper_ranked_bid_value values hcard 0 -
        expectedPayment 0)
    (htruth_high :
      ∀ i, i + 1 < n →
        winProbability (i + 1) *
            paper_ranked_bid_value values hcard (i + 1) -
          expectedPayment i ≤
        winProbability (i + 2) *
            paper_ranked_bid_value values hcard (i + 1) -
          expectedPayment (i + 1))
    (htruth_low :
      ∀ i, i + 1 < n →
        winProbability (i + 2) *
            paper_ranked_bid_value values hcard i -
          expectedPayment (i + 1) ≤
        winProbability (i + 1) *
            paper_ranked_bid_value values hcard i -
          expectedPayment i)
    (hendpoint : winProbability n - winProbability 0 ≤ 1) :
    expectedRevenue ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  let bidValue : ℕ → ℝ := paper_ranked_bid_value values hcard
  have hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1) := by
    intro j hj
    cases j with
    | zero =>
        simpa [hp0] using hfirst_probability_nonneg
    | succ i =>
        have hi : i + 1 < n := by
          simpa [Nat.succ_eq_add_one] using hj
        exact
          paper_lemma8_1_truthful_win_probability_monotone_payments
            (hprice_strict i hi)
            (by simpa [bidValue] using htruth_low i hi)
            (by simpa [bidValue] using htruth_high i hi)
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_payments_mono
      (values := values) (hcard := hcard)
      (winProbability := winProbability) (expectedPayment := expectedPayment)
      hp0 hprice_nonneg hrevenue hgain0 htruth_high hmono hendpoint

/--
Adjacent-rank anonymity/symmetry certificate for GHW Theorem 8.2.

For each adjacent ranked pair, changing the higher-ranked bidder's report down
to the lower rank reproduces the lower rank's allocation/payment, and changing
the lower-ranked bidder's report up reproduces the higher rank's
allocation/payment. This is the concrete bridge from one-bidder DSIC
comparisons to the paper's adjacent ranked `p_i, payment_i` comparisons.
-/
structure RankedAdjacentReportSymmetry
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) : Prop where
  high_allocation :
    ∀ i, (hi : i + 1 < n) →
      M.allocation
          (Function.update values
            (paper_ranked_agent values hcard ⟨i + 1, hi⟩)
            (paper_ranked_bid_value values hcard i))
          (paper_ranked_agent values hcard ⟨i + 1, hi⟩) =
        M.allocation values
          (paper_ranked_agent values hcard
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
  high_payment :
    ∀ i, (hi : i + 1 < n) →
      M.payment
          (Function.update values
            (paper_ranked_agent values hcard ⟨i + 1, hi⟩)
            (paper_ranked_bid_value values hcard i))
          (paper_ranked_agent values hcard ⟨i + 1, hi⟩) =
        M.payment values
          (paper_ranked_agent values hcard
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
  low_allocation :
    ∀ i, (hi : i + 1 < n) →
      M.allocation
          (Function.update values
            (paper_ranked_agent values hcard
              ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
            (paper_ranked_bid_value values hcard (i + 1)))
          (paper_ranked_agent values hcard
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) =
        M.allocation values
          (paper_ranked_agent values hcard ⟨i + 1, hi⟩)
  low_payment :
    ∀ i, (hi : i + 1 < n) →
      M.payment
          (Function.update values
            (paper_ranked_agent values hcard
              ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
            (paper_ranked_bid_value values hcard (i + 1)))
          (paper_ranked_agent values hcard
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) =
        M.payment values
          (paper_ranked_agent values hcard ⟨i + 1, hi⟩)

/--
Source-facing name for the adjacent sorted-bid report symmetry needed in GHW
Theorem 8.2. This is exactly the symmetry used by the proof: adjacent ranked
bidders are compared after one bidder reports the other's ranked value.
-/
abbrev PaperTheorem82AdjacentSortedBidReportSymmetry
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) :=
  RankedAdjacentReportSymmetry M values hcard

/--
GHW Theorem 8.2 auction-level ranked form. For an actual expected-outcome
digital-goods auction, DSIC supplies the adjacent utility comparisons used by
the ranked-payment theorem, once adjacent-rank symmetry identifies one-bidder
misreports with the neighboring ranked position. Strict adjacent rank values
are not required: ties give equal allocation by the same symmetry convention.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (winProbability expectedPayment : ℕ → ℝ)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (halloc_nonneg : ∀ bids i, 0 ≤ M.allocation bids i)
    (hp0 : winProbability 0 = 0)
    (hwin :
      ∀ j, (hj : j < n) →
        winProbability (j + 1) =
          M.allocation values (paper_ranked_agent values hcard ⟨j, hj⟩))
    (hpay :
      ∀ j, (hj : j < n) →
        expectedPayment j =
          M.payment values (paper_ranked_agent values hcard ⟨j, hj⟩))
    (hendpoint : winProbability n - winProbability 0 ≤ 1)
    (hprice_nonneg :
      ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j)
    (hsymmetry : RankedAdjacentReportSymmetry M values hcard) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let rankAgent : Fin n → Agent := paper_ranked_agent values hcard
  let bidValue : ℕ → ℝ := paper_ranked_bid_value values hcard
  have htruthM : M.TruthfulDominantStrategy :=
    (paper_digital_goods_truthful_eq M).1 htruth
  have hn_pos : 0 < n := by
    have hcard_pos : 0 < (Finset.univ : Finset Agent).card := by
      rw [Finset.card_univ]
      exact Fintype.card_pos
    simpa [hcard] using hcard_pos
  have hfirst_probability_nonneg : 0 ≤ winProbability 1 := by
    have hfirst := hwin 0 hn_pos
    rw [hfirst]
    exact halloc_nonneg values (rankAgent ⟨0, hn_pos⟩)
  have hrevenue :
      M.revenue values ≤ ∑ i ∈ Finset.range n, expectedPayment i := by
    have hrank_sum :
        (∑ i : Fin n, M.payment values (rankAgent i)) =
          ∑ a ∈ (Finset.univ : Finset Agent), M.payment values a := by
      simpa [rankAgent, paper_ranked_agent] using
        FiniteRanking.sum_rankAgentByValue_eq_sum
          (Finset.univ : Finset Agent) values hcard
          (fun a => M.payment values a)
    have hsum_range :
        (∑ i : Fin n, M.payment values (rankAgent i)) =
          ∑ i ∈ Finset.range n, expectedPayment i := by
      calc
        (∑ i : Fin n, M.payment values (rankAgent i))
            = ∑ i : Fin n, expectedPayment i.val := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simpa [rankAgent] using (hpay i.val i.isLt).symm
        _ = ∑ i ∈ Finset.range n, expectedPayment i := by
              exact Fin.sum_univ_eq_sum_range expectedPayment n
    have hrevenue_eq :
        M.revenue values = ∑ i ∈ Finset.range n, expectedPayment i := by
      calc
        M.revenue values = ∑ a : Agent, M.payment values a := rfl
        _ = ∑ a ∈ (Finset.univ : Finset Agent), M.payment values a := by simp
        _ = ∑ i : Fin n, M.payment values (rankAgent i) := hrank_sum.symm
        _ = ∑ i ∈ Finset.range n, expectedPayment i := hsum_range
    exact le_of_eq hrevenue_eq
  have hgain0 :
      0 ≤ winProbability 1 * bidValue 0 - expectedPayment 0 := by
    let first : Fin n := ⟨0, hn_pos⟩
    have hwin_first :
        winProbability 1 = M.allocation values (rankAgent first) := by
      simpa [rankAgent, first] using hwin 0 hn_pos
    have hpay_first :
        expectedPayment 0 = M.payment values (rankAgent first) := by
      simpa [rankAgent, first] using hpay 0 hn_pos
    have hbid_first : values (rankAgent first) = bidValue 0 := by
      have hvalue :=
        FiniteRanking.rankValueByValue_eq_value
          (Finset.univ : Finset Agent) values hcard first
      have hrank :
          bidValue 0 =
            FiniteRanking.rankValueByValue
              (Finset.univ : Finset Agent) values hcard first := by
        dsimp [bidValue, paper_ranked_bid_value, first]
        rw [dif_pos hn_pos]
      simpa [rankAgent, paper_ranked_agent] using hvalue.symm.trans hrank.symm
    have hir := hIR values (rankAgent first)
    simpa [DigitalGoodsAuction.utility, hwin_first, hpay_first, hbid_first,
      mul_comm] using hir
  have hbid_mono :
      ∀ i, i + 1 < n → bidValue i ≤ bidValue (i + 1) := by
    intro i hi
    have hi0 : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hmono_rank :=
      FiniteRanking.rankValueByValue_mono
        (Finset.univ : Finset Agent) values hcard low high
        (by simp [low, high])
    dsimp [bidValue, paper_ranked_bid_value]
    rw [dif_pos hi0, dif_pos hi]
    exact hmono_rank
  have htruth_high :
      ∀ i, i + 1 < n →
        winProbability (i + 1) * bidValue (i + 1) -
            expectedPayment i ≤
          winProbability (i + 2) * bidValue (i + 1) -
            expectedPayment (i + 1) := by
    intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hwin_low :
        winProbability (i + 1) = M.allocation values (rankAgent low) := by
      simpa [rankAgent, low] using hwin i low.isLt
    have hwin_high :
        winProbability (i + 2) = M.allocation values (rankAgent high) := by
      simpa [rankAgent, high, Nat.add_assoc] using hwin (i + 1) hi
    have hpay_low :
        expectedPayment i = M.payment values (rankAgent low) := by
      simpa [rankAgent, low] using hpay i low.isLt
    have hpay_high :
        expectedPayment (i + 1) = M.payment values (rankAgent high) := by
      simpa [rankAgent, high] using hpay (i + 1) hi
    have hbid_high : values (rankAgent high) = bidValue (i + 1) := by
      have hvalue :=
        FiniteRanking.rankValueByValue_eq_value
          (Finset.univ : Finset Agent) values hcard high
      have hrank :
          bidValue (i + 1) =
            FiniteRanking.rankValueByValue
              (Finset.univ : Finset Agent) values hcard high := by
        dsimp [bidValue, paper_ranked_bid_value, high]
        rw [dif_pos hi]
      simpa [rankAgent, paper_ranked_agent] using hvalue.symm.trans hrank.symm
    have hsym_high_alloc :
        M.allocation
            (Function.update values (rankAgent high) (bidValue i))
            (rankAgent high) =
          M.allocation values (rankAgent low) := by
      simpa [rankAgent, bidValue, low, high] using hsymmetry.high_allocation i hi
    have hsym_high_pay :
        M.payment
            (Function.update values (rankAgent high) (bidValue i))
            (rankAgent high) =
          M.payment values (rankAgent low) := by
      simpa [rankAgent, bidValue, low, high] using hsymmetry.high_payment i hi
    have hdsic := htruthM values (rankAgent high) (bidValue i)
    have hdsic_expanded :
        values (rankAgent high) *
            M.allocation
              (Function.update values (rankAgent high) (bidValue i))
              (rankAgent high) -
          M.payment
              (Function.update values (rankAgent high) (bidValue i))
              (rankAgent high) ≤
        values (rankAgent high) * M.allocation values (rankAgent high) -
          M.payment values (rankAgent high) := by
      simpa [DigitalGoodsAuction.utility] using hdsic
    calc
      winProbability (i + 1) * bidValue (i + 1) - expectedPayment i
          =
        values (rankAgent high) *
            M.allocation
              (Function.update values (rankAgent high) (bidValue i))
              (rankAgent high) -
          M.payment
              (Function.update values (rankAgent high) (bidValue i))
              (rankAgent high) := by
          rw [hwin_low, hpay_low, hbid_high,
            ← hsym_high_alloc, ← hsym_high_pay]
          ring
      _ ≤ values (rankAgent high) * M.allocation values (rankAgent high) -
          M.payment values (rankAgent high) := hdsic_expanded
      _ = winProbability (i + 2) * bidValue (i + 1) -
            expectedPayment (i + 1) := by
          rw [hwin_high, hpay_high, hbid_high]
          ring
  have htruth_low :
      ∀ i, i + 1 < n →
        winProbability (i + 2) * bidValue i -
            expectedPayment (i + 1) ≤
          winProbability (i + 1) * bidValue i -
            expectedPayment i := by
    intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hwin_low :
        winProbability (i + 1) = M.allocation values (rankAgent low) := by
      simpa [rankAgent, low] using hwin i low.isLt
    have hwin_high :
        winProbability (i + 2) = M.allocation values (rankAgent high) := by
      simpa [rankAgent, high, Nat.add_assoc] using hwin (i + 1) hi
    have hpay_low :
        expectedPayment i = M.payment values (rankAgent low) := by
      simpa [rankAgent, low] using hpay i low.isLt
    have hpay_high :
        expectedPayment (i + 1) = M.payment values (rankAgent high) := by
      simpa [rankAgent, high] using hpay (i + 1) hi
    have hbid_low : values (rankAgent low) = bidValue i := by
      have hvalue :=
        FiniteRanking.rankValueByValue_eq_value
          (Finset.univ : Finset Agent) values hcard low
      have hrank :
          bidValue i =
            FiniteRanking.rankValueByValue
              (Finset.univ : Finset Agent) values hcard low := by
        dsimp [bidValue, paper_ranked_bid_value, low]
        rw [dif_pos low.isLt]
      simpa [rankAgent, paper_ranked_agent] using hvalue.symm.trans hrank.symm
    have hsym_low_alloc :
        M.allocation
            (Function.update values (rankAgent low) (bidValue (i + 1)))
            (rankAgent low) =
          M.allocation values (rankAgent high) := by
      simpa [rankAgent, bidValue, low, high] using hsymmetry.low_allocation i hi
    have hsym_low_pay :
        M.payment
            (Function.update values (rankAgent low) (bidValue (i + 1)))
            (rankAgent low) =
          M.payment values (rankAgent high) := by
      simpa [rankAgent, bidValue, low, high] using hsymmetry.low_payment i hi
    have hdsic := htruthM values (rankAgent low) (bidValue (i + 1))
    have hdsic_expanded :
        values (rankAgent low) *
            M.allocation
              (Function.update values (rankAgent low) (bidValue (i + 1)))
              (rankAgent low) -
          M.payment
              (Function.update values (rankAgent low) (bidValue (i + 1)))
              (rankAgent low) ≤
        values (rankAgent low) * M.allocation values (rankAgent low) -
          M.payment values (rankAgent low) := by
      simpa [DigitalGoodsAuction.utility] using hdsic
    calc
      winProbability (i + 2) * bidValue i - expectedPayment (i + 1)
          =
        values (rankAgent low) *
            M.allocation
              (Function.update values (rankAgent low) (bidValue (i + 1)))
              (rankAgent low) -
          M.payment
              (Function.update values (rankAgent low) (bidValue (i + 1)))
              (rankAgent low) := by
          rw [hwin_high, hpay_high, hbid_low,
            ← hsym_low_alloc, ← hsym_low_pay]
          ring
      _ ≤ values (rankAgent low) * M.allocation values (rankAgent low) -
          M.payment values (rankAgent low) := hdsic_expanded
      _ = winProbability (i + 1) * bidValue i - expectedPayment i := by
          rw [hwin_low, hpay_low, hbid_low]
          ring
  have hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1) := by
    intro j hj
    cases j with
    | zero =>
        simpa [hp0] using hfirst_probability_nonneg
    | succ i =>
        have hi : i + 1 < n := by
          simpa [Nat.succ_eq_add_one] using hj
        have hbid_le := hbid_mono i hi
        rcases lt_or_eq_of_le hbid_le with hbid_lt | hbid_eq
        · exact
            paper_lemma8_1_truthful_win_probability_monotone_payments
              hbid_lt
              (by simpa [bidValue] using htruth_low i hi)
              (by simpa [bidValue] using htruth_high i hi)
        · let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
          let high : Fin n := ⟨i + 1, hi⟩
          have hwin_low :
              winProbability (i + 1) =
                M.allocation values (rankAgent low) := by
            simpa [rankAgent, low] using hwin i low.isLt
          have hwin_high :
              winProbability (i + 2) =
                M.allocation values (rankAgent high) := by
            simpa [rankAgent, high, Nat.add_assoc] using hwin (i + 1) hi
          have hbid_high :
              values (rankAgent high) = bidValue (i + 1) := by
            have hvalue :=
              FiniteRanking.rankValueByValue_eq_value
                (Finset.univ : Finset Agent) values hcard high
            have hrank :
                bidValue (i + 1) =
                  FiniteRanking.rankValueByValue
                    (Finset.univ : Finset Agent) values hcard high := by
              dsimp [bidValue, paper_ranked_bid_value, high]
              rw [dif_pos hi]
            simpa [rankAgent, paper_ranked_agent] using hvalue.symm.trans hrank.symm
          have hbid_i_high : bidValue i = values (rankAgent high) := by
            rw [hbid_eq, ← hbid_high]
          have hupdate_high :
              Function.update values (rankAgent high) (bidValue i) = values := by
            funext a
            by_cases ha : a = rankAgent high
            · subst a
              simp [Function.update, hbid_i_high]
            · simp [Function.update, ha]
          have hsym_high_alloc :
              M.allocation values (rankAgent high) =
                M.allocation values (rankAgent low) := by
            have hsym := hsymmetry.high_allocation i hi
            simpa [rankAgent, bidValue, low, high, hupdate_high] using hsym
          exact le_of_eq <| by
            calc
              winProbability (i + 1)
                  = M.allocation values (rankAgent low) := hwin_low
              _ = M.allocation values (rankAgent high) := hsym_high_alloc.symm
              _ = winProbability (i + 2) := hwin_high.symm
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_payments_mono
      (values := values) (hcard := hcard)
      (winProbability := winProbability) (expectedPayment := expectedPayment)
      hp0 hprice_nonneg hrevenue hgain0 htruth_high hmono hendpoint

/--
Paper-facing certificate for GHW Theorem 8.2. It packages the ranked sequence
identities, adjacent-rank symmetry, and endpoint/price side conditions needed
by the auction-level ranked truthful theorem.
-/
structure PaperTheorem82RankedTruthfulAuctionCertificate
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) where
  winProbability : ℕ → ℝ
  expectedPayment : ℕ → ℝ
  truthful : paper_digital_goods_truthful M
  individuallyRational : M.IndividuallyRational
  allocation_nonneg : ∀ bids i, 0 ≤ M.allocation bids i
  p0 : winProbability 0 = 0
  win_identity :
    ∀ j, (hj : j < n) →
      winProbability (j + 1) =
        M.allocation values (paper_ranked_agent values hcard ⟨j, hj⟩)
  payment_identity :
    ∀ j, (hj : j < n) →
      expectedPayment j =
        M.payment values (paper_ranked_agent values hcard ⟨j, hj⟩)
  endpoint : winProbability n - winProbability 0 ≤ 1
  price_nonneg :
    ∀ j, j < n → 0 ≤ paper_ranked_bid_value values hcard j
  symmetry : RankedAdjacentReportSymmetry M values hcard

/--
GHW Theorem 8.2 certificate form: a ranked truthful-auction certificate implies
expected revenue is bounded by the finite one-winner fixed-price benchmark.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction_certificate
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (certificate :
      PaperTheorem82RankedTruthfulAuctionCertificate M values hcard) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction
      M values hcard certificate.winProbability certificate.expectedPayment
      certificate.truthful certificate.individuallyRational
      certificate.allocation_nonneg certificate.p0 certificate.win_identity
      certificate.payment_identity certificate.endpoint certificate.price_nonneg
      certificate.symmetry

/--
Paper model for GHW Theorem 8.2. This is an intentionally named alias for the
ranked truthful-auction certificate: its fields are exactly the formal version
of the anonymous sorted-bid convention used by the paper.
-/
abbrev PaperTheorem82AnonymousSortedBidTruthfulModel
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n) :=
  PaperTheorem82RankedTruthfulAuctionCertificate M values hcard

/--
Source-shaped anonymity convention for the GHW Theorem 8.2 sorted-bid proof.
At the fixed valuation profile, if bidder `target` reports bidder `source`'s
value, then `target` receives the same allocation and payment that `source`
receives at the truthful profile.
-/
structure PaperTheorem82ReportValueAnonymity
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : Prop where
  allocation_eq :
    ∀ source target : Agent,
      M.allocation (Function.update values target (values source)) target =
        M.allocation values source
  payment_eq :
    ∀ source target : Agent,
      M.payment (Function.update values target (values source)) target =
        M.payment values source

/--
Two-bidder obstruction for the literal weak-DSIC reading of GHW Theorem 8.2.
The high bidder pays `100` and the low bidder pays `1` on values `{1, 100}`.
The auction is a truthful own-bid-independent threshold auction, but it fails
the report-value anonymity bridge used by the formal source endpoint.
-/
def paper_theorem8_2_counterexample_values : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 100

noncomputable def paper_theorem8_2_counterexample_threshold
    (bids : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then
    if bids 1 = 1 then 100 else 1
  else
    if bids 0 = 1 then 100 else 1

noncomputable def paper_theorem8_2_counterexample_auction :
    DigitalGoodsAuction (Fin 2) :=
  thresholdPriceAuction paper_theorem8_2_counterexample_threshold

theorem paper_theorem8_2_counterexample_threshold_ownBidIndependent :
    OwnBidIndependent paper_theorem8_2_counterexample_threshold := by
  intro bids i report
  fin_cases i <;>
    simp [paper_theorem8_2_counterexample_threshold, Function.update]

theorem paper_theorem8_2_counterexample_truthful :
    paper_digital_goods_truthful paper_theorem8_2_counterexample_auction := by
  rw [paper_digital_goods_truthful_eq]
  exact
    thresholdPriceAuction_truthful
      paper_theorem8_2_counterexample_threshold
      paper_theorem8_2_counterexample_threshold_ownBidIndependent

theorem paper_theorem8_2_counterexample_revenue :
    paper_theorem8_2_counterexample_auction.revenue
      paper_theorem8_2_counterexample_values = 101 := by
  norm_num [paper_theorem8_2_counterexample_auction,
    DigitalGoodsAuction.revenue, thresholdPriceAuction,
    paper_theorem8_2_counterexample_threshold,
    paper_theorem8_2_counterexample_values]

theorem paper_theorem8_2_counterexample_not_report_value_anonymous :
    ¬ PaperTheorem82ReportValueAnonymity
      paper_theorem8_2_counterexample_auction
      paper_theorem8_2_counterexample_values := by
  intro h
  have hx := h.allocation_eq (0 : Fin 2) (1 : Fin 2)
  norm_num [paper_theorem8_2_counterexample_auction, thresholdPriceAuction,
    paper_theorem8_2_counterexample_threshold,
    paper_theorem8_2_counterexample_values, Function.update] at hx

theorem paper_theorem8_2_counterexample_benchmark :
    finiteCandidateFixedPriceBenchmark
      paper_theorem8_2_counterexample_values 1 = 100 := by
  unfold finiteCandidateFixedPriceBenchmark
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro i _hi
    fin_cases i
    · simp [candidateFixedPriceRevenue, singlePriceRevenue, saleCount,
        paper_theorem8_2_counterexample_values, huniv]
      split
      · have hcard :
            (({0, 1} : Finset (Fin 2)).filter
              (fun i => (1 : ℝ) ≤ if i = 0 then 1 else 100)).card ≤
                ({0, 1} : Finset (Fin 2)).card :=
          Finset.card_le_card
            (s := ({0, 1} : Finset (Fin 2)).filter
              (fun i => (1 : ℝ) ≤ if i = 0 then 1 else 100))
            (t := ({0, 1} : Finset (Fin 2)))
            (by intro x hx; exact (Finset.mem_filter.mp hx).1)
        norm_num at hcard ⊢
        linarith
      · norm_num
    · simp [candidateFixedPriceRevenue, singlePriceRevenue, saleCount,
        paper_theorem8_2_counterexample_values, huniv]
      split <;> norm_num
  · have hle :=
      Finset.le_sup'
        (s := (Finset.univ : Finset (Fin 2)))
        (f := candidateFixedPriceRevenue
          paper_theorem8_2_counterexample_values 1)
        (b := (1 : Fin 2))
        (by simp)
    have hvalue :
        candidateFixedPriceRevenue
            paper_theorem8_2_counterexample_values 1 (1 : Fin 2) =
          100 := by
      simp [candidateFixedPriceRevenue, singlePriceRevenue, saleCount,
        paper_theorem8_2_counterexample_values, huniv]
    simpa [hvalue] using hle

theorem paper_theorem8_2_counterexample_ir :
    paper_theorem8_2_counterexample_auction.IndividuallyRational := by
  exact
    thresholdPriceAuction_individuallyRational
      paper_theorem8_2_counterexample_threshold

theorem paper_theorem8_2_counterexample_noPositiveTransfers :
    paper_theorem8_2_counterexample_auction.NoPositiveTransfers := by
  exact
    thresholdPriceAuction_noPositiveTransfers
      paper_theorem8_2_counterexample_threshold (by
        intro bids i
        fin_cases i <;>
          by_cases h : bids 0 = 1 <;>
          by_cases h' : bids 1 = 1 <;>
          norm_num [paper_theorem8_2_counterexample_threshold, h, h'])

theorem paper_theorem8_2_counterexample_binary :
    paper_theorem8_2_counterexample_auction.BinaryAllocation := by
  intro bids i
  unfold paper_theorem8_2_counterexample_auction thresholdPriceAuction
  by_cases h : paper_theorem8_2_counterexample_threshold bids i ≤ bids i
  · right
    simp [h]
  · left
    simp [h]

theorem paper_theorem8_2_counterexample_revenue_gt_benchmark :
    finiteCandidateFixedPriceBenchmark
        paper_theorem8_2_counterexample_values 1 <
      paper_theorem8_2_counterexample_auction.revenue
        paper_theorem8_2_counterexample_values := by
  rw [paper_theorem8_2_counterexample_benchmark,
    paper_theorem8_2_counterexample_revenue]
  norm_num

/--
Source-facing anonymous truthful-auction model for GHW Theorem 8.2. It
packages the expected-allocation range conventions, nonnegative values, and
adjacent sorted-bid report symmetry used by the paper's ranked proof.
-/
structure PaperTheorem82AnonymousTruthfulSourceModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] (n : ℕ) where
  auction : DigitalGoodsAuction Agent
  values : Agent → ℝ
  card_eq : (Finset.univ : Finset Agent).card = n
  truthful : paper_digital_goods_truthful auction
  individuallyRational : auction.IndividuallyRational
  allocation_nonneg : ∀ bids i, 0 ≤ auction.allocation bids i
  allocation_le_one : ∀ bids i, auction.allocation bids i ≤ 1
  value_nonneg : ∀ i : Agent, 0 ≤ values i
  adjacent_symmetry :
    PaperTheorem82AdjacentSortedBidReportSymmetry auction values card_eq

/--
Paper-shaped source model for GHW Theorem 8.2 using the paper's sorted-bid
report-substitution convention. The report-value anonymity field says that, at
the fixed bid profile, a bidder reporting another bid value receives that bid's
allocation/payment. This is stronger than ordinary relabeling anonymity, but it
is the convention needed by the paper's adjacent sorted-bid utility comparison.
-/
structure PaperTheorem82AnonymousTruthfulReportValueSourceModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] (n : ℕ) where
  auction : DigitalGoodsAuction Agent
  values : Agent → ℝ
  card_eq : (Finset.univ : Finset Agent).card = n
  truthful : paper_digital_goods_truthful auction
  individuallyRational : auction.IndividuallyRational
  allocation_nonneg : ∀ bids i, 0 ≤ auction.allocation bids i
  allocation_le_one : ∀ bids i, auction.allocation bids i ≤ 1
  value_nonneg : ∀ i : Agent, 0 ≤ values i
  report_value_anonymity :
    PaperTheorem82ReportValueAnonymity auction values

/--
Construct the ranked Theorem 8.2 model from primitive truthful-auction
assumptions and the paper's adjacent sorted-bid report-symmetry convention.
-/
noncomputable def
    paper_theorem8_2_anonymous_sorted_bid_truthful_model_of_adjacent_report_symmetry
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (halloc_nonneg : ∀ bids i, 0 ≤ M.allocation bids i)
    (halloc_le_one : ∀ bids i, M.allocation bids i ≤ 1)
    (hvalue_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hsymmetry :
      PaperTheorem82AdjacentSortedBidReportSymmetry M values hcard) :
    PaperTheorem82AnonymousSortedBidTruthfulModel M values hcard := by
  classical
  let winProbability : ℕ → ℝ :=
    fun k =>
      if k = 0 then 0
      else
        if hk : k - 1 < n then
          M.allocation values (paper_ranked_agent values hcard ⟨k - 1, hk⟩)
        else 0
  let expectedPayment : ℕ → ℝ :=
    fun k =>
      if hk : k < n then
        M.payment values (paper_ranked_agent values hcard ⟨k, hk⟩)
      else 0
  refine
    { winProbability := winProbability
      expectedPayment := expectedPayment
      truthful := htruth
      individuallyRational := hIR
      allocation_nonneg := halloc_nonneg
      p0 := ?_
      win_identity := ?_
      payment_identity := ?_
      endpoint := ?_
      price_nonneg := ?_
      symmetry := hsymmetry }
  · simp [winProbability]
  · intro j hj
    simp [winProbability, hj]
  · intro j hj
    simp [expectedPayment, hj]
  · have hn_pos : 0 < n := by
      have hcard_pos : 0 < (Finset.univ : Finset Agent).card := by
        rw [Finset.card_univ]
        exact Fintype.card_pos
      simpa [hcard] using hcard_pos
    cases n with
    | zero =>
        exact (Nat.not_lt_zero 0 hn_pos).elim
    | succ k =>
        have hp0 : winProbability 0 = 0 := by
          simp [winProbability]
        have hlast :
            winProbability (Nat.succ k) =
              M.allocation values
                (paper_ranked_agent values hcard ⟨k, Nat.lt_succ_self k⟩) := by
          simp [winProbability]
        have hle :
            M.allocation values
                (paper_ranked_agent values hcard ⟨k, Nat.lt_succ_self k⟩) ≤
              1 :=
          halloc_le_one values
            (paper_ranked_agent values hcard ⟨k, Nat.lt_succ_self k⟩)
        nlinarith
  · intro j hj
    rw [paper_ranked_bid_value_eq_value_ranked_agent values hcard ⟨j, hj⟩]
    exact hvalue_nonneg _

/--
The stronger report-value anonymity convention implies the adjacent sorted-bid
report symmetry used by the Theorem 8.2 proof.
-/
theorem paper_theorem8_2_adjacent_report_symmetry_of_report_value_anonymity
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (hanonymous : PaperTheorem82ReportValueAnonymity M values) :
    PaperTheorem82AdjacentSortedBidReportSymmetry M values hcard := by
  classical
  refine
    { high_allocation := ?_
      high_payment := ?_
      low_allocation := ?_
      low_payment := ?_ }
  · intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hbid_low :
        paper_ranked_bid_value values hcard i =
          values (paper_ranked_agent values hcard low) := by
      simpa [low] using
        paper_ranked_bid_value_eq_value_ranked_agent values hcard low
    have hsym :=
      hanonymous.allocation_eq
        (paper_ranked_agent values hcard low)
        (paper_ranked_agent values hcard high)
    simpa [low, high, hbid_low] using hsym
  · intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hbid_low :
        paper_ranked_bid_value values hcard i =
          values (paper_ranked_agent values hcard low) := by
      simpa [low] using
        paper_ranked_bid_value_eq_value_ranked_agent values hcard low
    have hsym :=
      hanonymous.payment_eq
        (paper_ranked_agent values hcard low)
        (paper_ranked_agent values hcard high)
    simpa [low, high, hbid_low] using hsym
  · intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hbid_high :
        paper_ranked_bid_value values hcard (i + 1) =
          values (paper_ranked_agent values hcard high) := by
      simpa [high] using
        paper_ranked_bid_value_eq_value_ranked_agent values hcard high
    have hsym :=
      hanonymous.allocation_eq
        (paper_ranked_agent values hcard high)
        (paper_ranked_agent values hcard low)
    simpa [low, high, hbid_high] using hsym
  · intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hbid_high :
        paper_ranked_bid_value values hcard (i + 1) =
          values (paper_ranked_agent values hcard high) := by
      simpa [high] using
        paper_ranked_bid_value_eq_value_ranked_agent values hcard high
    have hsym :=
      hanonymous.payment_eq
        (paper_ranked_agent values hcard high)
        (paper_ranked_agent values hcard low)
    simpa [low, high, hbid_high] using hsym

/--
Construct the adjacent-symmetry source model from the paper-shaped
report-value source model.
-/
noncomputable def
    paper_theorem8_2_anonymous_truthful_source_model_of_report_value_source_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] {n : ℕ}
    (model : PaperTheorem82AnonymousTruthfulReportValueSourceModel Agent n) :
    PaperTheorem82AnonymousTruthfulSourceModel Agent n where
  auction := model.auction
  values := model.values
  card_eq := model.card_eq
  truthful := model.truthful
  individuallyRational := model.individuallyRational
  allocation_nonneg := model.allocation_nonneg
  allocation_le_one := model.allocation_le_one
  value_nonneg := model.value_nonneg
  adjacent_symmetry :=
    paper_theorem8_2_adjacent_report_symmetry_of_report_value_anonymity
      model.auction model.values model.card_eq model.report_value_anonymity

/--
Construct the ranked Theorem 8.2 model from the stronger report-value
anonymity convention. This is a convenience adapter; the source-facing theorem
uses adjacent report symmetry directly.
-/
noncomputable def
    paper_theorem8_2_anonymous_sorted_bid_truthful_model_of_report_value_anonymity
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (halloc_nonneg : ∀ bids i, 0 ≤ M.allocation bids i)
    (halloc_le_one : ∀ bids i, M.allocation bids i ≤ 1)
    (hvalue_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hanonymous : PaperTheorem82ReportValueAnonymity M values) :
    PaperTheorem82AnonymousSortedBidTruthfulModel M values hcard :=
  paper_theorem8_2_anonymous_sorted_bid_truthful_model_of_adjacent_report_symmetry
    M values hcard htruth hIR halloc_nonneg halloc_le_one hvalue_nonneg
    (paper_theorem8_2_adjacent_report_symmetry_of_report_value_anonymity
      M values hcard hanonymous)

/--
GHW Theorem 8.2 final paper-model form. For an anonymous sorted-bid truthful
auction model satisfying the ranked sequence identities and adjacent-rank
symmetry, expected revenue is bounded by the finite one-winner fixed-price
benchmark.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (model :
      PaperTheorem82AnonymousSortedBidTruthfulModel M values hcard) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction_certificate
      M values hcard model

/--
GHW Theorem 8.2 from primitive truthful-auction assumptions and the paper's
adjacent sorted-bid report-symmetry convention. The ranked certificate is
constructed internally.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_adjacent_report_symmetry
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (halloc_nonneg : ∀ bids i, 0 ≤ M.allocation bids i)
    (halloc_le_one : ∀ bids i, M.allocation bids i ≤ 1)
    (hvalue_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hsymmetry :
      PaperTheorem82AdjacentSortedBidReportSymmetry M values hcard) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model
      M values hcard
      (paper_theorem8_2_anonymous_sorted_bid_truthful_model_of_adjacent_report_symmetry
        M values hcard htruth hIR halloc_nonneg halloc_le_one
        hvalue_nonneg hsymmetry)

/--
GHW Theorem 8.2 source-model form. The source model carries truthfulness,
IR, allocation range, nonnegative values, and the adjacent sorted-bid report
symmetry used to instantiate the ranked proof.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_source_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] {n : ℕ}
    (model : PaperTheorem82AnonymousTruthfulSourceModel Agent n) :
    model.auction.revenue model.values ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_adjacent_report_symmetry
      model.auction model.values model.card_eq model.truthful
      model.individuallyRational model.allocation_nonneg
      model.allocation_le_one model.value_nonneg model.adjacent_symmetry

/--
GHW Theorem 8.2 source-model form using the paper-shaped report-value
anonymity convention. The adjacent sorted-bid bridge is derived internally.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_report_value_source_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent] {n : ℕ}
    (model : PaperTheorem82AnonymousTruthfulReportValueSourceModel Agent n) :
    model.auction.revenue model.values ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_source_model
      (paper_theorem8_2_anonymous_truthful_source_model_of_report_value_source_model
        model)

/--
GHW Theorem 8.2 from the stronger report-value anonymity convention. This
adapter is retained for callers that have the stronger source-shaped witness.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_report_value_anonymity
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (halloc_nonneg : ∀ bids i, 0 ≤ M.allocation bids i)
    (halloc_le_one : ∀ bids i, M.allocation bids i ≤ 1)
    (hvalue_nonneg : ∀ i : Agent, 0 ≤ values i)
    (hanonymous : PaperTheorem82ReportValueAnonymity M values) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_adjacent_report_symmetry
      M values hcard htruth hIR halloc_nonneg halloc_le_one hvalue_nonneg
      (paper_theorem8_2_adjacent_report_symmetry_of_report_value_anonymity
        M values hcard hanonymous)

/--
Revenue of one coupled offer-price outcome in the journal-version monotone
auction proof of GHW Theorem 8.2. Bidder `i` accepts iff its sampled offer
price is at most its bid value.
-/
noncomputable def paper_theorem8_2_journal_monotone_offer_revenue
    {Agent : Type*} [Fintype Agent]
    (values offerPrice : Agent → ℝ) : ℝ :=
  ∑ i : Agent, if offerPrice i ≤ values i then offerPrice i else 0

/--
Journal-version GHW Theorem 8.2, one coupled offer-price outcome. If higher
value bidders receive weakly lower offers in the same coupled outcome, then the
winner set is an upper set and the outcome revenue is bounded by the fixed-price
benchmark.
-/
theorem paper_theorem8_2_journal_monotone_offer_revenue_le_finite_candidate_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values offerPrice : Agent → ℝ)
    (hoffer_nonneg : ∀ i, 0 ≤ offerPrice i)
    (hoffer_monotone :
      ∀ i j, values i ≤ values j → offerPrice j ≤ offerPrice i) :
    paper_theorem8_2_journal_monotone_offer_revenue values offerPrice ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => offerPrice i ≤ values i
  by_cases hwinners : winners.Nonempty
  · let winnerValues : Finset ℝ := winners.image values
    have hwinnerValues : winnerValues.Nonempty := hwinners.image values
    let q : ℝ := winnerValues.min' hwinnerValues
    have hq_mem : q ∈ winnerValues :=
      Finset.min'_mem winnerValues hwinnerValues
    obtain ⟨minWinner, hminWinner_mem, hminWinner_value⟩ :=
      Finset.mem_image.mp hq_mem
    have hminWinner_accept : offerPrice minWinner ≤ values minWinner :=
      (Finset.mem_filter.mp hminWinner_mem).2
    have hq_nonneg : 0 ≤ q := by
      rw [← hminWinner_value]
      exact le_trans (hoffer_nonneg minWinner) hminWinner_accept
    have hq_le_winner_value :
        ∀ i, i ∈ winners → q ≤ values i := by
      intro i hi
      have hmem : values i ∈ winnerValues :=
        Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact Finset.min'_le winnerValues (values i) hmem
    have hoffer_le_q :
        ∀ i, i ∈ winners → offerPrice i ≤ q := by
      intro i hi
      have hvalue_le : values minWinner ≤ values i := by
        simpa [hminWinner_value] using hq_le_winner_value i hi
      have hoffer_le_min := hoffer_monotone minWinner i hvalue_le
      have hmin_offer_le_q : offerPrice minWinner ≤ q := by
        simpa [hminWinner_value] using hminWinner_accept
      exact le_trans hoffer_le_min hmin_offer_le_q
    let qWinners : Finset Agent :=
      (Finset.univ : Finset Agent).filter fun i => q ≤ values i
    have hwinners_subset_qWinners : winners ⊆ qWinners := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨by simp, hq_le_winner_value i hi⟩
    have hrevenue_eq :
        paper_theorem8_2_journal_monotone_offer_revenue values offerPrice =
          ∑ i ∈ winners, offerPrice i := by
      simpa [paper_theorem8_2_journal_monotone_offer_revenue, winners] using
        (Finset.sum_filter
          (s := (Finset.univ : Finset Agent))
          (p := fun i => offerPrice i ≤ values i)
          (f := fun i => offerPrice i)).symm
    have hsum_offer_le_q :
        (∑ i ∈ winners, offerPrice i) ≤ ∑ i ∈ winners, q :=
      Finset.sum_le_sum fun i hi => hoffer_le_q i hi
    have hsum_q_le_qWinners :
        (∑ i ∈ winners, q) ≤ ∑ i ∈ qWinners, q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hwinners_subset_qWinners
        (by intro _i _hq_mem _hnot_mem; exact hq_nonneg)
    have hqWinners_sum_eq_single :
        (∑ i ∈ qWinners, q) = singlePriceRevenue values q := by
      simpa [singlePriceRevenue, qWinners] using
        (Finset.sum_filter
          (s := (Finset.univ : Finset Agent))
          (p := fun i => q ≤ values i)
          (f := fun _i => q))
    have hminWinner_qWinner : minWinner ∈ qWinners := by
      exact Finset.mem_filter.mpr
        ⟨by simp, by rw [← hminWinner_value]⟩
    have hq_feasible : 1 ≤ saleCount values q := by
      have hcard_pos : 0 < saleCount values q := by
        unfold saleCount
        exact Finset.card_pos.mpr
          ⟨minWinner, by simpa [qWinners] using hminWinner_qWinner⟩
      simpa using hcard_pos
    have hsingle_le_benchmark :
        singlePriceRevenue values q ≤
          finiteCandidateFixedPriceBenchmark values 1 := by
      rw [← hminWinner_value]
      exact singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
        values 1 minWinner (by simpa [hminWinner_value] using hq_nonneg)
        (by simpa [hminWinner_value] using hq_feasible)
    calc
      paper_theorem8_2_journal_monotone_offer_revenue values offerPrice
          = ∑ i ∈ winners, offerPrice i := hrevenue_eq
      _ ≤ ∑ i ∈ winners, q := hsum_offer_le_q
      _ ≤ ∑ i ∈ qWinners, q := hsum_q_le_qWinners
      _ = singlePriceRevenue values q := hqWinners_sum_eq_single
      _ ≤ finiteCandidateFixedPriceBenchmark values 1 := hsingle_le_benchmark
  · have hnot_winner : ∀ i, ¬ offerPrice i ≤ values i := by
      intro i hi
      apply hwinners
      exact ⟨i, by simp [winners, hi]⟩
    have hrevenue_zero :
        paper_theorem8_2_journal_monotone_offer_revenue values offerPrice = 0 := by
      simp [paper_theorem8_2_journal_monotone_offer_revenue, hnot_winner]
    rw [hrevenue_zero]
    exact finiteCandidateFixedPriceBenchmark_nonneg values 1

/--
Journal-version GHW Theorem 8.2, one coupled offer-price outcome, in the
weaker form actually used by the proof. It is enough that whenever bidder `i`
accepts, all higher-value bidders receive offers no larger than `i`'s offer.
The offer process need not be globally pointwise monotone above rejected
lower-value offers.
-/
theorem paper_theorem8_2_journal_accept_monotone_offer_revenue_le_finite_candidate_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values offerPrice : Agent → ℝ)
    (hoffer_nonneg : ∀ i, 0 ≤ offerPrice i)
    (hoffer_accept_monotone :
      ∀ i j, values i ≤ values j → offerPrice i ≤ values i →
        offerPrice j ≤ offerPrice i) :
    paper_theorem8_2_journal_monotone_offer_revenue values offerPrice ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => offerPrice i ≤ values i
  by_cases hwinners : winners.Nonempty
  · let winnerValues : Finset ℝ := winners.image values
    have hwinnerValues : winnerValues.Nonempty := hwinners.image values
    let q : ℝ := winnerValues.min' hwinnerValues
    have hq_mem : q ∈ winnerValues :=
      Finset.min'_mem winnerValues hwinnerValues
    obtain ⟨minWinner, hminWinner_mem, hminWinner_value⟩ :=
      Finset.mem_image.mp hq_mem
    have hminWinner_accept : offerPrice minWinner ≤ values minWinner :=
      (Finset.mem_filter.mp hminWinner_mem).2
    have hq_nonneg : 0 ≤ q := by
      rw [← hminWinner_value]
      exact le_trans (hoffer_nonneg minWinner) hminWinner_accept
    have hq_le_winner_value :
        ∀ i, i ∈ winners → q ≤ values i := by
      intro i hi
      have hmem : values i ∈ winnerValues :=
        Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact Finset.min'_le winnerValues (values i) hmem
    have hoffer_le_q :
        ∀ i, i ∈ winners → offerPrice i ≤ q := by
      intro i hi
      have hvalue_le : values minWinner ≤ values i := by
        simpa [hminWinner_value] using hq_le_winner_value i hi
      have hoffer_le_min :=
        hoffer_accept_monotone minWinner i hvalue_le hminWinner_accept
      have hmin_offer_le_q : offerPrice minWinner ≤ q := by
        simpa [hminWinner_value] using hminWinner_accept
      exact le_trans hoffer_le_min hmin_offer_le_q
    let qWinners : Finset Agent :=
      (Finset.univ : Finset Agent).filter fun i => q ≤ values i
    have hwinners_subset_qWinners : winners ⊆ qWinners := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨by simp, hq_le_winner_value i hi⟩
    have hrevenue_eq :
        paper_theorem8_2_journal_monotone_offer_revenue values offerPrice =
          ∑ i ∈ winners, offerPrice i := by
      simpa [paper_theorem8_2_journal_monotone_offer_revenue, winners] using
        (Finset.sum_filter
          (s := (Finset.univ : Finset Agent))
          (p := fun i => offerPrice i ≤ values i)
          (f := fun i => offerPrice i)).symm
    have hsum_offer_le_q :
        (∑ i ∈ winners, offerPrice i) ≤ ∑ i ∈ winners, q :=
      Finset.sum_le_sum fun i hi => hoffer_le_q i hi
    have hsum_q_le_qWinners :
        (∑ i ∈ winners, q) ≤ ∑ i ∈ qWinners, q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hwinners_subset_qWinners
        (by intro _i _hq_mem _hnot_mem; exact hq_nonneg)
    have hqWinners_sum_eq_single :
        (∑ i ∈ qWinners, q) = singlePriceRevenue values q := by
      simpa [singlePriceRevenue, qWinners] using
        (Finset.sum_filter
          (s := (Finset.univ : Finset Agent))
          (p := fun i => q ≤ values i)
          (f := fun _i => q))
    have hminWinner_qWinner : minWinner ∈ qWinners := by
      exact Finset.mem_filter.mpr
        ⟨by simp, by rw [← hminWinner_value]⟩
    have hq_feasible : 1 ≤ saleCount values q := by
      have hcard_pos : 0 < saleCount values q := by
        unfold saleCount
        exact Finset.card_pos.mpr
          ⟨minWinner, by simpa [qWinners] using hminWinner_qWinner⟩
      simpa using hcard_pos
    have hsingle_le_benchmark :
        singlePriceRevenue values q ≤
          finiteCandidateFixedPriceBenchmark values 1 := by
      rw [← hminWinner_value]
      exact singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
        values 1 minWinner (by simpa [hminWinner_value] using hq_nonneg)
        (by simpa [hminWinner_value] using hq_feasible)
    calc
      paper_theorem8_2_journal_monotone_offer_revenue values offerPrice
          = ∑ i ∈ winners, offerPrice i := hrevenue_eq
      _ ≤ ∑ i ∈ winners, q := hsum_offer_le_q
      _ ≤ ∑ i ∈ qWinners, q := hsum_q_le_qWinners
      _ = singlePriceRevenue values q := hqWinners_sum_eq_single
      _ ≤ finiteCandidateFixedPriceBenchmark values 1 := hsingle_le_benchmark
  · have hnot_winner : ∀ i, ¬ offerPrice i ≤ values i := by
      intro i hi
      apply hwinners
      exact ⟨i, by simp [winners, hi]⟩
    have hrevenue_zero :
        paper_theorem8_2_journal_monotone_offer_revenue values offerPrice = 0 := by
      simp [paper_theorem8_2_journal_monotone_offer_revenue, hnot_winner]
    rw [hrevenue_zero]
    exact finiteCandidateFixedPriceBenchmark_nonneg values 1

/--
Journal-version source model for GHW Theorem 8.2. The journal proof couples the
bid-independent randomized offers by a shared quantile. This finite source
model records that coupled experiment directly: outcome weights are
nonnegative with total mass at most one, offers are nonnegative, and higher
value bidders receive weakly lower offers in every coupled outcome.
-/
structure PaperTheorem82JournalMonotoneSourceModel
    (Agent Outcome : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome] where
  values : Agent → ℝ
  weight : Outcome → ℝ
  offerPrice : Outcome → Agent → ℝ
  weight_nonneg : ∀ outcome, 0 ≤ weight outcome
  weight_sum_le_one : (∑ outcome : Outcome, weight outcome) ≤ 1
  offer_nonneg : ∀ outcome i, 0 ≤ offerPrice outcome i
  offer_monotone :
    ∀ outcome i j, values i ≤ values j →
      offerPrice outcome j ≤ offerPrice outcome i

/-- Expected revenue of the coupled monotone offer experiment in journal 8.2. -/
noncomputable def paper_theorem8_2_journal_monotone_expected_revenue
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome]
    (model : PaperTheorem82JournalMonotoneSourceModel Agent Outcome) : ℝ :=
  ∑ outcome : Outcome,
    model.weight outcome *
      paper_theorem8_2_journal_monotone_offer_revenue
        model.values (model.offerPrice outcome)

/--
Journal-version GHW Theorem 8.2. The coupled monotone source model is bounded
by the finite one-winner fixed-price benchmark.
-/
theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_journal_monotone_source_model
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome]
    (model : PaperTheorem82JournalMonotoneSourceModel Agent Outcome) :
    paper_theorem8_2_journal_monotone_expected_revenue model ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  classical
  let B : ℝ := finiteCandidateFixedPriceBenchmark model.values 1
  have hB_nonneg : 0 ≤ B := by
    exact finiteCandidateFixedPriceBenchmark_nonneg model.values 1
  have hpoint :
      ∀ outcome : Outcome,
        paper_theorem8_2_journal_monotone_offer_revenue
            model.values (model.offerPrice outcome) ≤ B := by
    intro outcome
    exact
      paper_theorem8_2_journal_monotone_offer_revenue_le_finite_candidate_benchmark
        model.values (model.offerPrice outcome)
        (model.offer_nonneg outcome)
        (model.offer_monotone outcome)
  calc
    paper_theorem8_2_journal_monotone_expected_revenue model
        = ∑ outcome : Outcome,
            model.weight outcome *
              paper_theorem8_2_journal_monotone_offer_revenue
                model.values (model.offerPrice outcome) := rfl
    _ ≤ ∑ outcome : Outcome, model.weight outcome * B := by
          exact Finset.sum_le_sum fun outcome _ =>
            mul_le_mul_of_nonneg_left (hpoint outcome)
              (model.weight_nonneg outcome)
    _ = (∑ outcome : Outcome, model.weight outcome) * B := by
          rw [Finset.sum_mul]
    _ ≤ 1 * B := by
          exact mul_le_mul_of_nonneg_right model.weight_sum_le_one hB_nonneg
    _ = B := by ring

/--
Expected revenue of the journal-version coupled monotone offer experiment,
using the repository's finite PMF expectation API.
-/
noncomputable def paper_theorem8_2_journal_monotone_pmf_expected_revenue
    {Agent Outcome : Type*} [Fintype Agent] [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (values : Agent → ℝ)
    (offerPrice : Outcome → Agent → ℝ) : ℝ :=
  pmfExp law fun outcome =>
    paper_theorem8_2_journal_monotone_offer_revenue values (offerPrice outcome)

/--
Journal-version source model for GHW Theorem 8.2 using a finite randomized
coupled offer experiment. This matches the journal proof after the inverse-CDF
thought experiment: condition on one random seed, higher value bidders receive
weakly lower offers.
-/
structure PaperTheorem82JournalMonotoneRandomizedOfferSourceModel
    (Agent Outcome : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome] [DecidableEq Outcome] where
  values : Agent → ℝ
  law : PMF Outcome
  offerPrice : Outcome → Agent → ℝ
  offer_nonneg : ∀ outcome i, 0 ≤ offerPrice outcome i
  offer_monotone :
    ∀ outcome i j, values i ≤ values j →
      offerPrice outcome j ≤ offerPrice outcome i

/--
Journal-version GHW Theorem 8.2 for a finite randomized monotone offer source
model. Pointwise coupled monotonicity gives the fixed-price benchmark bound
seed by seed, and finite expectation preserves the bound.
-/
theorem
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_journal_monotone_randomized_offer_source_model
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome] [DecidableEq Outcome]
    (model :
      PaperTheorem82JournalMonotoneRandomizedOfferSourceModel Agent Outcome) :
    paper_theorem8_2_journal_monotone_pmf_expected_revenue
        model.law model.values model.offerPrice ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  classical
  exact
    pmfExp_le_of_forall_le model.law
      (fun outcome =>
        paper_theorem8_2_journal_monotone_offer_revenue
          model.values (model.offerPrice outcome))
      (finiteCandidateFixedPriceBenchmark model.values 1)
      (fun outcome =>
        paper_theorem8_2_journal_monotone_offer_revenue_le_finite_candidate_benchmark
          model.values (model.offerPrice outcome)
        (model.offer_nonneg outcome)
          (model.offer_monotone outcome))

/--
Journal-version source model for GHW Theorem 8.2 using the weaker
accepted-bid monotonicity sufficient for the proof. In each random seed, if a
bidder accepts its offer, then every higher-value bidder receives an offer no
larger than that accepted offer.
-/
structure PaperTheorem82JournalAcceptedMonotoneRandomizedOfferSourceModel
    (Agent Outcome : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome] [DecidableEq Outcome] where
  values : Agent → ℝ
  law : PMF Outcome
  offerPrice : Outcome → Agent → ℝ
  offer_nonneg : ∀ outcome i, 0 ≤ offerPrice outcome i
  offer_accept_monotone :
    ∀ outcome i j, values i ≤ values j →
      offerPrice outcome i ≤ values i →
        offerPrice outcome j ≤ offerPrice outcome i

/--
Journal-version GHW Theorem 8.2 for a finite randomized accepted-monotone
offer source model.
-/
theorem
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_journal_accept_monotone_randomized_offer_source_model
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [Fintype Outcome] [DecidableEq Outcome]
    (model :
      PaperTheorem82JournalAcceptedMonotoneRandomizedOfferSourceModel
        Agent Outcome) :
    paper_theorem8_2_journal_monotone_pmf_expected_revenue
        model.law model.values model.offerPrice ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  classical
  exact
    pmfExp_le_of_forall_le model.law
      (fun outcome =>
        paper_theorem8_2_journal_monotone_offer_revenue
          model.values (model.offerPrice outcome))
      (finiteCandidateFixedPriceBenchmark model.values 1)
      (fun outcome =>
        paper_theorem8_2_journal_accept_monotone_offer_revenue_le_finite_candidate_benchmark
          model.values (model.offerPrice outcome)
          (model.offer_nonneg outcome)
          (model.offer_accept_monotone outcome))

/--
Expected revenue of the journal-version raw marginal offer laws. For each
bidder `i`, `offerLaw i` is the finite law of that bidder's offer price.
-/
noncomputable def paper_theorem8_2_raw_cdf_expected_revenue
    {Agent Price : Type*} [Fintype Agent] [Fintype Price] [DecidableEq Price]
    (values : Agent → ℝ) (price : Price → ℝ)
    (offerLaw : Agent → PMF Price) : ℝ :=
  ∑ i : Agent,
    pmfExp (offerLaw i) fun p =>
      if price p ≤ values i then price p else 0

theorem paper_theorem8_2_pmf_toMeasure_real_event
    {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    μ.toMeasure.real {a | p a} = pmfProb μ p := by
  unfold pmfProb pmfExp
  rw [measureReal_def]
  have hmeasure :
      μ.toMeasure {a | p a} = ∑ a : α, if p a then μ a else 0 := by
    rw [PMF.toMeasure_apply_fintype]
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases hpa : p a <;> simp [Set.indicator, hpa]
  rw [hmeasure]
  have h_ne_top :
      ∀ a ∈ (Finset.univ : Finset α),
        (if p a then μ a else 0) ≠ ⊤ := by
    intro a _
    by_cases hpa : p a <;> simp [hpa, μ.apply_ne_top a]
  rw [ENNReal.toReal_sum (s := (Finset.univ : Finset α))
    (f := fun a => if p a then μ a else 0) h_ne_top]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases hpa : p a <;> simp [hpa]

noncomputable def paper_theorem8_2_offer_surplus
    {Price : Type*} (price : Price → ℝ) (cut cap : ℝ) : Price → ℝ :=
  fun p => if price p ≤ cut then cap - price p else 0

theorem paper_theorem8_2_pmf_offer_surplus_le_of_cdf_monotone
    {Price : Type*} [Fintype Price] [DecidableEq Price]
    (μ ν : PMF Price) (price : Price → ℝ) {cut cap : ℝ}
    (hcut_cap : cut ≤ cap)
    (hcdf :
      ∀ t, t ≤ cut →
        pmfProb μ (fun p => price p ≤ t) ≤
          pmfProb ν (fun p => price p ≤ t)) :
    pmfExp μ (paper_theorem8_2_offer_surplus price cut cap) ≤
      pmfExp ν (paper_theorem8_2_offer_surplus price cut cap) := by
  letI : MeasurableSpace Price := ⊤
  let sfun : Price → ℝ := paper_theorem8_2_offer_surplus price cut cap
  have hμ_int : Integrable sfun μ.toMeasure := by simp [sfun]
  have hν_int : Integrable sfun ν.toMeasure := by simp [sfun]
  have hμ_nonneg : 0 ≤ᵐ[μ.toMeasure] sfun := by
    exact .of_forall (fun p => by
      dsimp [sfun, paper_theorem8_2_offer_surplus]
      split
      · linarith
      · linarith)
  have hν_nonneg : 0 ≤ᵐ[ν.toMeasure] sfun := by
    exact .of_forall (fun p => by
      dsimp [sfun, paper_theorem8_2_offer_surplus]
      split
      · linarith
      · linarith)
  have hμ_exp :
      pmfExp μ sfun =
        (∫⁻ p, ENNReal.ofReal (sfun p) ∂μ.toMeasure).toReal := by
    have hμ_eq : pmfExp μ sfun = ∫ p, sfun p ∂μ.toMeasure := by
      rw [PMF.integral_eq_sum]
      simp [pmfExp]
    rw [hμ_eq]
    rw [integral_eq_lintegral_of_nonneg_ae
      hμ_nonneg hμ_int.aestronglyMeasurable]
  have hν_exp :
      pmfExp ν sfun =
        (∫⁻ p, ENNReal.ofReal (sfun p) ∂ν.toMeasure).toReal := by
    have hν_eq : pmfExp ν sfun = ∫ p, sfun p ∂ν.toMeasure := by
      rw [PMF.integral_eq_sum]
      simp [pmfExp]
    rw [hν_eq]
    rw [integral_eq_lintegral_of_nonneg_ae
      hν_nonneg hν_int.aestronglyMeasurable]
  rw [hμ_exp, hν_exp]
  apply ENNReal.toReal_mono
  · exact ne_of_lt (Integrable.lintegral_lt_top hν_int)
  · rw [lintegral_eq_lintegral_meas_le
      μ.toMeasure hμ_nonneg hμ_int.aemeasurable]
    rw [lintegral_eq_lintegral_meas_le
      ν.toMeasure hν_nonneg hν_int.aemeasurable]
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact .of_forall (fun t ht => by
      have htpos : 0 < t := ht
      have hevent :
          {p : Price | t ≤ sfun p} =
            {p : Price | price p ≤ min cut (cap - t)} := by
        ext p
        dsimp [sfun, paper_theorem8_2_offer_surplus]
        constructor
        · intro h
          by_cases hp : price p ≤ cut
          · simp [hp] at h
            exact le_min hp (by linarith)
          · simp [hp] at h
            linarith [htpos, h]
        · intro h
          have hp_cut : price p ≤ cut := le_trans h (min_le_left _ _)
          have hp_cap : price p ≤ cap - t := le_trans h (min_le_right _ _)
          simp [hp_cut]
          linarith
      rw [hevent]
      have hreal :
          μ.toMeasure.real {p : Price | price p ≤ min cut (cap - t)} ≤
            ν.toMeasure.real {p : Price | price p ≤ min cut (cap - t)} := by
        rw [paper_theorem8_2_pmf_toMeasure_real_event
              μ (fun p => price p ≤ min cut (cap - t)),
            paper_theorem8_2_pmf_toMeasure_real_event
              ν (fun p => price p ≤ min cut (cap - t))]
        exact hcdf (min cut (cap - t)) (min_le_left _ _)
      exact
        (ENNReal.toReal_le_toReal
          (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal)

theorem paper_theorem8_2_expected_offer_payment_eq_probability_mul_value_sub_surplus
    {Price : Type*} [Fintype Price] [DecidableEq Price]
    (μ : PMF Price) (price : Price → ℝ) (b : ℝ) :
    pmfExp μ (fun p => if price p ≤ b then price p else 0) =
      pmfProb μ (fun p => price p ≤ b) * b -
        pmfExp μ (paper_theorem8_2_offer_surplus price b b) := by
  unfold pmfProb
  rw [← pmfExp_mul_const μ
    (fun p => if price p ≤ b then (1 : ℝ) else 0) b,
    ← pmfExp_sub]
  exact pmfExp_congr μ (fun p => by
    by_cases hp : price p ≤ b <;>
      simp [paper_theorem8_2_offer_surplus, hp])

theorem paper_theorem8_2_offer_surplus_gap_le
    {Price : Type*} [Fintype Price] [DecidableEq Price]
    (μ : PMF Price) (price : Price → ℝ) {low high : ℝ}
    (hle : low ≤ high) :
    pmfExp μ (paper_theorem8_2_offer_surplus price low low) +
      pmfProb μ (fun p => price p ≤ low) * (high - low) ≤
        pmfExp μ (paper_theorem8_2_offer_surplus price low high) := by
  have hpoint : ∀ p : Price,
      paper_theorem8_2_offer_surplus price low low p +
          (if price p ≤ low then (1 : ℝ) else 0) * (high - low) ≤
        paper_theorem8_2_offer_surplus price low high p := by
    intro p
    dsimp [paper_theorem8_2_offer_surplus]
    by_cases hp_low : price p ≤ low
    · simp [hp_low]
    · simp [hp_low]
  unfold pmfProb
  rw [← pmfExp_mul_const μ
      (fun p => if price p ≤ low then (1 : ℝ) else 0) (high - low),
    ← pmfExp_add]
  exact pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint

theorem paper_theorem8_2_offer_surplus_cut_le
    {Price : Type*} [Fintype Price] [DecidableEq Price]
    (μ : PMF Price) (price : Price → ℝ) {low high : ℝ}
    (hle : low ≤ high) :
    pmfExp μ (paper_theorem8_2_offer_surplus price low high) ≤
      pmfExp μ (paper_theorem8_2_offer_surplus price high high) := by
  have hpoint : ∀ p : Price,
      paper_theorem8_2_offer_surplus price low high p ≤
        paper_theorem8_2_offer_surplus price high high p := by
    intro p
    dsimp [paper_theorem8_2_offer_surplus]
    by_cases hp_low : price p ≤ low
    · have hp_high : price p ≤ high := le_trans hp_low hle
      simp [hp_low, hp_high]
    · by_cases hp_high : price p ≤ high
      · simp [hp_low, hp_high]
      · simp [hp_low, hp_high]
  exact pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint

/--
Journal-version source model for GHW Theorem 8.2 with raw marginal offer CDF
monotonicity. This is the source-facing finite form of the journal correction:
higher values have weakly larger offer-acceptance CDFs below each lower value.
-/
structure PaperTheorem82JournalRawCDFMonotoneOfferSourceModel
    (Agent Price : Type*) [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price] where
  values : Agent → ℝ
  price : Price → ℝ
  offerLaw : Agent → PMF Price
  value_nonneg : ∀ i, 0 ≤ values i
  price_nonneg : ∀ p, 0 ≤ price p
  cdf_monotone :
    ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
      pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
        pmfProb (offerLaw j) (fun p => price p ≤ t)

/--
Journal-version GHW Theorem 8.2 from raw CDF monotone marginal offer laws.

The proof works directly with the finite marginal laws. The CDF monotonicity
assumption gives adjacent ranked acceptance-probability monotonicity and,
through a finite layer-cake argument, the adjacent surplus recursion used by
the paper's Theorem 8.2 algebra.
-/
theorem
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model
    {Agent Price : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [LinearOrder Agent] [Fintype Price] [DecidableEq Price]
    (model : PaperTheorem82JournalRawCDFMonotoneOfferSourceModel Agent Price) :
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  classical
  let n : ℕ := Fintype.card Agent
  have hcard : (Finset.univ : Finset Agent).card = n := by
    simp [n]
  let rankAgent : Fin n → Agent := paper_ranked_agent model.values hcard
  let bidValue : ℕ → ℝ := paper_ranked_bid_value model.values hcard
  let winProbability : ℕ → ℝ :=
    fun k =>
      match k with
      | 0 => 0
      | Nat.succ i =>
          if hi : i < n then
            pmfProb (model.offerLaw (rankAgent ⟨i, hi⟩))
              (fun p => model.price p ≤ bidValue i)
          else 0
  let expectedPayment : ℕ → ℝ :=
    fun k =>
      if hk : k < n then
        pmfExp (model.offerLaw (rankAgent ⟨k, hk⟩)) fun p =>
          if model.price p ≤ bidValue k then model.price p else 0
      else 0
  let gain : ℕ → ℝ :=
    fun k =>
      if hk : k < n then
        pmfExp (model.offerLaw (rankAgent ⟨k, hk⟩))
          (paper_theorem8_2_offer_surplus model.price (bidValue k) (bidValue k))
      else 0
  have hn_pos : 0 < n := by
    have hcard_pos : 0 < (Finset.univ : Finset Agent).card := by
      rw [Finset.card_univ]
      exact Fintype.card_pos
    simpa [hcard] using hcard_pos
  have hwin_succ :
      ∀ k, (hk : k < n) →
        winProbability (k + 1) =
          pmfProb (model.offerLaw (rankAgent ⟨k, hk⟩))
            (fun p => model.price p ≤ bidValue k) := by
    intro k hk
    simp [winProbability, hk]
  have hpayment_in :
      ∀ k, (hk : k < n) →
        expectedPayment k =
          pmfExp (model.offerLaw (rankAgent ⟨k, hk⟩)) fun p =>
            if model.price p ≤ bidValue k then model.price p else 0 := by
    intro k hk
    simp [expectedPayment, hk]
  have hgain_in :
      ∀ k, (hk : k < n) →
        gain k =
          pmfExp (model.offerLaw (rankAgent ⟨k, hk⟩))
            (paper_theorem8_2_offer_surplus model.price
              (bidValue k) (bidValue k)) := by
    intro k hk
    simp [gain, hk]
  have hbid_eq :
      ∀ k, (hk : k < n) →
        bidValue k = model.values (rankAgent ⟨k, hk⟩) := by
    intro k hk
    simpa [bidValue, rankAgent] using
      paper_ranked_bid_value_eq_value_ranked_agent
        model.values hcard ⟨k, hk⟩
  have hbid_mono :
      ∀ i, i + 1 < n → bidValue i ≤ bidValue (i + 1) := by
    intro i hi
    have hi0 : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
    let low : Fin n := ⟨i, hi0⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hmono_rank :=
      FiniteRanking.rankValueByValue_mono
        (Finset.univ : Finset Agent) model.values hcard low high
        (by simp [low, high])
    dsimp [bidValue, paper_ranked_bid_value]
    rw [dif_pos hi0, dif_pos hi]
    exact hmono_rank
  have hcdf_rank :
      ∀ (i : ℕ) (hi : i + 1 < n) (t : ℝ), t ≤ bidValue i →
        pmfProb
            (model.offerLaw
              (rankAgent ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩))
            (fun p => model.price p ≤ t) ≤
          pmfProb (model.offerLaw (rankAgent ⟨i + 1, hi⟩))
            (fun p => model.price p ≤ t) := by
    intro i hi t ht
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hvalue_le :
        model.values (rankAgent low) ≤ model.values (rankAgent high) := by
      rw [← hbid_eq i low.isLt, ← hbid_eq (i + 1) hi]
      exact hbid_mono i hi
    have ht_value : t ≤ model.values (rankAgent low) := by
      rwa [← hbid_eq i low.isLt]
    simpa [low, high] using
      model.cdf_monotone (rankAgent low) (rankAgent high)
        hvalue_le t ht_value
  have hp0 : winProbability 0 = 0 := by
    simp [winProbability]
  have hrevenue :
      paper_theorem8_2_raw_cdf_expected_revenue
          model.values model.price model.offerLaw ≤
        ∑ i ∈ Finset.range n, expectedPayment i := by
    have hrank_sum :
        (∑ i : Fin n,
          pmfExp (model.offerLaw (rankAgent i)) fun p =>
            if model.price p ≤ model.values (rankAgent i) then
              model.price p
            else 0) =
          ∑ a ∈ (Finset.univ : Finset Agent),
            pmfExp (model.offerLaw a) fun p =>
              if model.price p ≤ model.values a then model.price p else 0 := by
      simpa [rankAgent, paper_ranked_agent] using
        FiniteRanking.sum_rankAgentByValue_eq_sum
          (Finset.univ : Finset Agent) model.values hcard
          (fun a =>
            pmfExp (model.offerLaw a) fun p =>
              if model.price p ≤ model.values a then model.price p else 0)
    have hsum_range :
        (∑ i : Fin n,
          pmfExp (model.offerLaw (rankAgent i)) fun p =>
            if model.price p ≤ model.values (rankAgent i) then
              model.price p
            else 0) =
          ∑ i ∈ Finset.range n, expectedPayment i := by
      calc
        (∑ i : Fin n,
          pmfExp (model.offerLaw (rankAgent i)) fun p =>
            if model.price p ≤ model.values (rankAgent i) then
              model.price p
            else 0)
            = ∑ i : Fin n, expectedPayment i.val := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              calc
                pmfExp (model.offerLaw (rankAgent i)) (fun p =>
                    if model.price p ≤ model.values (rankAgent i) then
                      model.price p
                    else 0)
                    =
                  pmfExp (model.offerLaw (rankAgent i)) (fun p =>
                    if model.price p ≤ bidValue i.val then model.price p
                    else 0) := by
                    rw [hbid_eq i.val i.isLt]
                _ = expectedPayment i.val := by
                    exact (hpayment_in i.val i.isLt).symm
        _ = ∑ i ∈ Finset.range n, expectedPayment i := by
              exact Fin.sum_univ_eq_sum_range expectedPayment n
    have hrevenue_eq :
        paper_theorem8_2_raw_cdf_expected_revenue
            model.values model.price model.offerLaw =
          ∑ i ∈ Finset.range n, expectedPayment i := by
      calc
        paper_theorem8_2_raw_cdf_expected_revenue
            model.values model.price model.offerLaw =
          ∑ a : Agent,
            pmfExp (model.offerLaw a) fun p =>
              if model.price p ≤ model.values a then model.price p else 0 := rfl
        _ =
          ∑ a ∈ (Finset.univ : Finset Agent),
            pmfExp (model.offerLaw a) fun p =>
              if model.price p ≤ model.values a then model.price p else 0 := by
              simp
        _ =
          ∑ i : Fin n,
            pmfExp (model.offerLaw (rankAgent i)) fun p =>
              if model.price p ≤ model.values (rankAgent i) then
                model.price p
              else 0 := hrank_sum.symm
        _ = ∑ i ∈ Finset.range n, expectedPayment i := hsum_range
    exact le_of_eq hrevenue_eq
  have hrevenueAtRank :
      ∀ i, i < n →
        expectedPayment i = winProbability (i + 1) * bidValue i - gain i := by
    intro i hi
    rw [hpayment_in i hi, hwin_succ i hi, hgain_in i hi]
    exact
      paper_theorem8_2_expected_offer_payment_eq_probability_mul_value_sub_surplus
        (model.offerLaw (rankAgent ⟨i, hi⟩)) model.price (bidValue i)
  have hgain0 : 0 ≤ gain 0 := by
    rw [hgain_in 0 hn_pos]
    refine pmfExp_nonneg_of_forall_nonneg _ _ ?_
    intro p
    dsimp [paper_theorem8_2_offer_surplus]
    by_cases hp : model.price p ≤ bidValue 0
    · simp [hp]
    · simp [hp]
  have hgain_step :
      ∀ i, i + 1 < n →
        gain i + winProbability (i + 1) *
            (bidValue (i + 1) - bidValue i) ≤ gain (i + 1) := by
    intro i hi
    let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let high : Fin n := ⟨i + 1, hi⟩
    have hbid_le : bidValue i ≤ bidValue (i + 1) := hbid_mono i hi
    have hgap_low :=
      paper_theorem8_2_offer_surplus_gap_le
        (model.offerLaw (rankAgent low)) model.price hbid_le
    have hsurplus_order :
        pmfExp (model.offerLaw (rankAgent low))
            (paper_theorem8_2_offer_surplus model.price
              (bidValue i) (bidValue (i + 1))) ≤
          pmfExp (model.offerLaw (rankAgent high))
            (paper_theorem8_2_offer_surplus model.price
              (bidValue i) (bidValue (i + 1))) := by
      exact
        paper_theorem8_2_pmf_offer_surplus_le_of_cdf_monotone
          (model.offerLaw (rankAgent low))
          (model.offerLaw (rankAgent high)) model.price hbid_le
          (hcdf_rank i hi)
    have hcut_high :=
      paper_theorem8_2_offer_surplus_cut_le
        (model.offerLaw (rankAgent high)) model.price hbid_le
    rw [hgain_in i low.isLt, hwin_succ i low.isLt,
      hgain_in (i + 1) hi]
    exact le_trans hgap_low (le_trans hsurplus_order hcut_high)
  have hmono :
      ∀ j, j < n → winProbability j ≤ winProbability (j + 1) := by
    intro j hj
    cases j with
    | zero =>
        rw [hp0, hwin_succ 0 hn_pos]
        exact pmfProb_nonneg _ _
    | succ i =>
        have hi : i + 1 < n := by
          simpa [Nat.succ_eq_add_one] using hj
        let low : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
        let high : Fin n := ⟨i + 1, hi⟩
        have hbid_le : bidValue i ≤ bidValue (i + 1) := hbid_mono i hi
        have hcdf_at := hcdf_rank i hi (bidValue i) le_rfl
        have hthreshold :
            pmfProb (model.offerLaw (rankAgent high))
                (fun p => model.price p ≤ bidValue i) ≤
              pmfProb (model.offerLaw (rankAgent high))
                (fun p => model.price p ≤ bidValue (i + 1)) := by
          exact pmfProb_le_of_imp
            (model.offerLaw (rankAgent high))
            (fun p => model.price p ≤ bidValue i)
            (fun p => model.price p ≤ bidValue (i + 1))
            (fun _ hp => le_trans hp hbid_le)
        rw [hwin_succ i low.isLt, hwin_succ (i + 1) hi]
        exact le_trans hcdf_at hthreshold
  have hendpoint : winProbability n - winProbability 0 ≤ 1 := by
    cases hn : n with
    | zero =>
        rw [hn] at hn_pos
        exact (Nat.not_lt_zero 0 hn_pos).elim
    | succ k =>
        have hklt : k < n := by
          rw [hn]
          exact Nat.lt_succ_self k
        have hlast :
            winProbability (k + 1) =
              pmfProb
                (model.offerLaw
                  (rankAgent ⟨k, hklt⟩))
                (fun p => model.price p ≤ bidValue k) := by
          exact hwin_succ k hklt
        rw [hp0, hlast]
        linarith [pmfProb_le_one
          (model.offerLaw (rankAgent ⟨k, hklt⟩))
          (fun p => model.price p ≤ bidValue k)]
  have hvalue :
      ∀ j, j < n →
        FiniteSum.rankedFixedPriceRevenue n bidValue j ≤
          finiteCandidateFixedPriceBenchmark model.values 1 := by
    intro j hj
    exact
      paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark
        model.values hcard ⟨j, hj⟩ (by
          change 0 ≤ bidValue j
          rw [hbid_eq j hj]
          exact model.value_nonneg _)
  exact
    FiniteSum.revenue_le_bound_of_adjacent_gain_recursion_bounded
      n winProbability bidValue expectedPayment gain hp0 hrevenue
      hrevenueAtRank hgain0 hgain_step hmono hendpoint hvalue
      (finiteCandidateFixedPriceBenchmark_nonneg model.values 1)

/--
Journal-version source model for GHW Theorem 8.2 with raw CDF monotonicity and
the finite common-quantile coupling used by the journal proof. The `cdf_monotone`
field records Definition 8.1 on the finite marginal offer laws; the coupling
fields record the proof's shared-random-seed experiment that realizes those
marginals with pointwise monotone offers.
-/
structure PaperTheorem82JournalRawCDFMonotoneCoupledOfferSourceModel
    (Agent Price Outcome : Type*) [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price]
    [Fintype Outcome] [DecidableEq Outcome] where
  values : Agent → ℝ
  price : Price → ℝ
  offerLaw : Agent → PMF Price
  price_nonneg : ∀ p, 0 ≤ price p
  cdf_monotone :
    ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
      pmfProb (offerLaw i) (fun p => price p ≤ t) ≤
        pmfProb (offerLaw j) (fun p => price p ≤ t)
  law : PMF Outcome
  offer : Outcome → Agent → Price
  marginal : ∀ i, law.map (fun outcome => offer outcome i) = offerLaw i
  coupled_monotone :
    ∀ outcome i j, values i ≤ values j →
      price (offer outcome j) ≤ price (offer outcome i)

/--
The raw marginal offer-law revenue agrees with the revenue of the coupled
common-seed experiment when each coupled coordinate has the stated marginal.
-/
theorem paper_theorem8_2_raw_cdf_expected_revenue_eq_coupled_expected_revenue
    {Agent Price Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price]
    [Fintype Outcome] [DecidableEq Outcome]
    (model :
      PaperTheorem82JournalRawCDFMonotoneCoupledOfferSourceModel
        Agent Price Outcome) :
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw =
      paper_theorem8_2_journal_monotone_pmf_expected_revenue
        model.law model.values
        (fun outcome i => model.price (model.offer outcome i)) := by
  classical
  unfold paper_theorem8_2_raw_cdf_expected_revenue
    paper_theorem8_2_journal_monotone_pmf_expected_revenue
    paper_theorem8_2_journal_monotone_offer_revenue
  calc
    (∑ i : Agent,
        pmfExp (model.offerLaw i) fun p =>
          if model.price p ≤ model.values i then model.price p else 0)
        =
      ∑ i : Agent,
        pmfExp (model.law.map (fun outcome => model.offer outcome i)) fun p =>
          if model.price p ≤ model.values i then model.price p else 0 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← model.marginal i]
    _ =
      ∑ i : Agent,
        pmfExp model.law fun outcome =>
          if model.price (model.offer outcome i) ≤ model.values i then
            model.price (model.offer outcome i)
          else 0 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [pmfExp_map]
    _ =
      pmfExp model.law fun outcome =>
        ∑ i : Agent,
          if model.price (model.offer outcome i) ≤ model.values i then
            model.price (model.offer outcome i)
          else 0 := by
        exact
          (pmfExp_univ_sum model.law
            (fun i outcome =>
              if model.price (model.offer outcome i) ≤ model.values i then
                model.price (model.offer outcome i)
              else 0)).symm

/--
Journal-version GHW Theorem 8.2 from raw CDF marginals plus the finite
common-seed monotone coupling used in the journal proof.
-/
theorem
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_coupled_offer_source_model
    {Agent Price Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [Fintype Price] [DecidableEq Price]
    [Fintype Outcome] [DecidableEq Outcome]
    (model :
      PaperTheorem82JournalRawCDFMonotoneCoupledOfferSourceModel
        Agent Price Outcome) :
    paper_theorem8_2_raw_cdf_expected_revenue
        model.values model.price model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  classical
  let coupledModel :
      PaperTheorem82JournalMonotoneRandomizedOfferSourceModel Agent Outcome :=
    { values := model.values
      law := model.law
      offerPrice := fun outcome i => model.price (model.offer outcome i)
      offer_nonneg := fun outcome i => model.price_nonneg (model.offer outcome i)
      offer_monotone := fun outcome i j hvalue =>
        model.coupled_monotone outcome i j hvalue }
  rw [paper_theorem8_2_raw_cdf_expected_revenue_eq_coupled_expected_revenue
    model]
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_journal_monotone_randomized_offer_source_model
      coupledModel

/--
GHW Theorem 9.1 discrete crossing step. Along a fixed total-count line
`highCount + lowCount = m`, if a deterministic bid-independent threshold rule
uses the low price at `alpha` high bids and the high price at `m` high bids,
then some adjacent count switches from low price to high price.
-/
theorem paper_theorem9_1_bid_independent_threshold_transition
    (thresholdUsesHighPrice : ℕ → ℕ → Bool) {alpha m : ℕ}
    (halpha_lt_m : alpha < m)
    (hstart : thresholdUsesHighPrice alpha (m - alpha) = false)
    (hend : thresholdUsesHighPrice m 0 = true) :
    ∃ k : ℕ,
      alpha < k ∧ k ≤ m ∧
        thresholdUsesHighPrice (k - 1) (m - (k - 1)) = false ∧
        thresholdUsesHighPrice k (m - k) = true := by
  simpa using
      (FiniteSum.exists_bool_transition
      (fun k => thresholdUsesHighPrice k (m - k))
      halpha_lt_m (by simpa using hstart) (by simpa using hend))

/--
GHW Theorem 9.1 transition-witness revenue calculation. At an adjacent
low-to-high threshold switch, the adversarial binary-valued input has revenue
at most the number of high bidders while the fixed-price benchmark is at least
`h` times that number. Therefore `h * R <= F`; if the high count is at least
`alpha`, the paper's side condition `alpha * h <= F` also follows.
-/
theorem paper_theorem9_1_transition_witness_revenue_bound
    {alpha highCount : ℕ} {h revenue fixedPriceBenchmark : ℝ}
    (hh_nonneg : 0 ≤ h)
    (halpha_le_high : alpha ≤ highCount)
    (hrevenue : revenue ≤ (highCount : ℝ))
    (hbenchmark : h * (highCount : ℝ) ≤ fixedPriceBenchmark) :
    h * revenue ≤ fixedPriceBenchmark ∧
      h * (alpha : ℝ) ≤ fixedPriceBenchmark := by
  constructor
  · exact le_trans
      (mul_le_mul_of_nonneg_left hrevenue hh_nonneg) hbenchmark
  · have halpha_cast : (alpha : ℝ) ≤ (highCount : ℝ) := by
      exact_mod_cast halpha_le_high
    exact le_trans
      (mul_le_mul_of_nonneg_left halpha_cast hh_nonneg) hbenchmark

/--
GHW Theorem 9.1 start-high case. If the threshold rule already chooses the high
price at the starting count `alpha`, the paper's second construction gives
`R <= h*alpha` and `F >= h^2*alpha`; for `h >= 1` this implies both the
`h * R <= F` ratio form and the side condition `h*alpha <= F`.
-/
theorem paper_theorem9_1_start_high_witness_revenue_bound
    {alpha : ℕ} {h revenue fixedPriceBenchmark : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hrevenue : revenue ≤ h * (alpha : ℝ))
    (hbenchmark : h * (h * (alpha : ℝ)) ≤ fixedPriceBenchmark) :
    h * revenue ≤ fixedPriceBenchmark ∧
      h * (alpha : ℝ) ≤ fixedPriceBenchmark := by
  have hh_nonneg : 0 ≤ h := le_trans zero_le_one hh_ge_one
  constructor
  · exact le_trans
      (mul_le_mul_of_nonneg_left hrevenue hh_nonneg) hbenchmark
  · have halpha_nonneg : 0 ≤ (alpha : ℝ) := by exact_mod_cast Nat.zero_le alpha
    have hone_mul_alpha_le : 1 * (alpha : ℝ) ≤ h * (alpha : ℝ) :=
      mul_le_mul_of_nonneg_right hh_ge_one halpha_nonneg
    have hside : h * (alpha : ℝ) ≤ h * (h * (alpha : ℝ)) := by
      calc
        h * (alpha : ℝ) = h * (1 * (alpha : ℝ)) := by ring
        _ ≤ h * (h * (alpha : ℝ)) :=
          mul_le_mul_of_nonneg_left hone_mul_alpha_le hh_nonneg
    exact le_trans hside hbenchmark

/--
GHW Theorem 9.1 two-value bid-independent construction. For any deterministic
bid-independent rule that chooses between prices `1` and `h`, if the all-high
endpoint uses the high price, then there is a binary-valued input whose revenue
is at most a `1/h` fraction of a feasible fixed-price benchmark lower bound,
while the side condition `alpha*h <= F` holds.

The paper's proof sets `m = h^2 alpha`; the hypothesis `hm_large` is the exact
benchmark inequality needed for that start-high case.
-/
theorem paper_theorem9_1_two_value_bid_independent_lower_bound
    (thresholdUsesHighPrice : ℕ → ℕ → Bool) {highValue alpha m : ℕ}
    (hhigh_ge_one : 1 ≤ (highValue : ℝ))
    (halpha_lt_m : alpha < m)
    (hm_large :
      (highValue : ℝ) * ((highValue : ℝ) * (alpha : ℝ)) ≤
        (m + 1 : ℝ))
    (hend : thresholdUsesHighPrice m 0 = true) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (highValue : ℝ) *
          twoValueBidIndependentThresholdRevenue
            thresholdUsesHighPrice highValue highCount lowCount ≤
        fixedPriceLowerBound ∧
      (highValue : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  exact twoValueBidIndependent_exists_low_revenue_witness
    thresholdUsesHighPrice hhigh_ge_one halpha_lt_m hm_large hend

/--
GHW Theorem 9.1 arbitrary-threshold form. This removes the paper's informal
"other values of `f` only reduce revenue" normalization: for any deterministic
bid-independent threshold price rule on binary values `1` and `h`, there is an
input whose revenue is at most a `1/h` fraction of a feasible fixed-price
benchmark lower bound, with `alpha*h <= F`.
-/
theorem paper_theorem9_1_arbitrary_threshold_bid_independent_lower_bound
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha m : ℕ}
    (hhigh_ge_one : 1 ≤ (highValue : ℝ))
    (halpha_lt_m : alpha < m)
    (hm_large :
      (highValue : ℝ) * ((highValue : ℝ) * (alpha : ℝ)) ≤
        (m + 1 : ℝ)) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            thresholdPrice highValue highCount lowCount ≤
        fixedPriceLowerBound ∧
      (highValue : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  exact twoValueBidIndependentPrice_exists_low_revenue_witness
    thresholdPrice hhigh_ge_one halpha_lt_m hm_large

/--
GHW Theorem 9.1 with the paper's scale choice `m = h^2 alpha`. For any
deterministic bid-independent threshold price rule on binary values `1` and
integer `h >= 2`, and any positive integer `alpha`, there is an input satisfying
`alpha*h <= F` on which the auction revenue is at most a `1/h` fraction of a
feasible fixed-price benchmark lower bound.
-/
theorem paper_theorem9_1_arbitrary_threshold_scaled_lower_bound
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            thresholdPrice highValue highCount lowCount ≤
        fixedPriceLowerBound ∧
      (highValue : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  exact twoValueBidIndependentPrice_exists_low_revenue_witness_scaled
    thresholdPrice hhigh_ge_two halpha_pos

/--
GHW Theorem 9.1 against the actual finite fixed-price benchmark on the
constructed two-value input. This is the paper's `R/F <= O(1/h)` witness with
`F` instantiated as the one-winner fixed-price benchmark for that input.
-/
theorem paper_theorem9_1_arbitrary_threshold_scaled_lower_bound_fixed_price_benchmark
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            thresholdPrice highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark
    thresholdPrice hhigh_ge_two halpha_pos

/--
GHW Theorem 9.1 bid-independent-function form. For an arbitrary anonymous
paper-style price rule `f` on erased bid lists, restrict `f` to canonical
two-value lists and apply the binary adversarial construction.
-/
theorem paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
    (priceRule : List ℝ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule highValue)
            highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact twoValueListBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark
    priceRule hhigh_ge_two halpha_pos

/--
Attained form of the GHW Theorem 9.1 erased-list witness.  The positive
`highCount` records that the advertised high value occurs in the constructed
binary profile.
-/
theorem paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark_attained
    (priceRule : List ℝ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule highValue)
            highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    twoValueListBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
      priceRule hhigh_ge_two halpha_pos

/--
GHW Theorem 9.1 model bridge: the count-threshold revenue formula used in the
binary lower-bound construction is exactly the revenue of the corresponding
concrete threshold-price digital-goods auction on `highCount` high bidders and
`lowCount` low bidders.
-/
theorem paper_theorem9_1_count_threshold_revenue_eq_concrete_auction
    (thresholdPrice : ℕ → ℕ → ℝ) (highValue highCount lowCount : ℕ) :
    (thresholdPriceAuction
      (twoValueCountThresholdPrice thresholdPrice highCount lowCount)).revenue
        (twoValueBidProfile highValue highCount lowCount) =
      twoValueBidIndependentPriceRevenue
        thresholdPrice highValue highCount lowCount := by
  exact thresholdPriceAuction_twoValueCountThreshold_revenue_eq
    thresholdPrice highValue highCount lowCount

/--
GHW Theorem 9.1 concrete count-threshold auction form. The bad two-value input
can be chosen so that the concrete threshold-price auction revenue is at most a
`1 / h` fraction of the actual fixed-price benchmark for that input.
-/
theorem paper_theorem9_1_concrete_count_threshold_scaled_lower_bound_fixed_price_benchmark
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          (thresholdPriceAuction
            (twoValueCountThresholdPrice
              thresholdPrice highCount lowCount)).revenue
              (twoValueBidProfile highValue highCount lowCount) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hrev, hside⟩ :=
    paper_theorem9_1_arbitrary_threshold_scaled_lower_bound_fixed_price_benchmark
      thresholdPrice hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hside⟩
  rw [paper_theorem9_1_count_threshold_revenue_eq_concrete_auction]
  exact hrev

/--
GHW Theorem 9.1 ratio form: the exact witness inequality `h * R <= F` implies
the paper's displayed lower-bound ratio `R/F <= 1/h`, provided the benchmark
and high value are positive.
-/
theorem paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark
    {h revenue fixedPriceBenchmark : ℝ}
    (hh_pos : 0 < h)
    (hbenchmark_pos : 0 < fixedPriceBenchmark)
    (hbound : h * revenue ≤ fixedPriceBenchmark) :
    revenue / fixedPriceBenchmark ≤ 1 / h := by
  exact PositiveDenominator.div_le_div_of_cross_mul_le
    hbenchmark_pos hh_pos (by
      calc
        revenue * h = h * revenue := by ring
        _ ≤ fixedPriceBenchmark := hbound
        _ = 1 * fixedPriceBenchmark := by ring)

/--
GHW Lemma 9.2 payment-constancy step. In a truthful deterministic offer slice
with other bids fixed, any two winning reports are charged the same price.
-/
theorem paper_lemma9_2_deterministic_offer_payment_constant
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    {x y px py : ℝ}
    (hx : offer x = some px) (hy : offer y = some py) :
    px = py := by
  exact deterministicOffer_payment_eq_of_truthful_wins htruth hx hy

/--
GHW Lemma 9.2 monotone winning step. In a truthful feasible deterministic
offer slice, if a lower report wins then every higher report wins.
-/
theorem paper_lemma9_2_deterministic_offer_winning_monotone
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer)
    {x y px : ℝ} (hxy : x < y)
    (hx : offer x = some px) :
    ∃ py, offer y = some py := by
  exact deterministicOffer_winning_mono_of_truthful htruth hfeasible hxy hx

/--
GHW Lemma 9.2 losing-prefix step. In a truthful feasible deterministic offer
slice, if a higher report loses then every lower report loses.
-/
theorem paper_lemma9_2_deterministic_offer_losing_prefix
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer)
    {x y : ℝ} (hxy : x < y)
    (hy : offer y = none) :
    offer x = none := by
  exact deterministicOffer_losing_anti_mono_of_truthful
    htruth hfeasible hxy hy

/--
GHW Lemma 9.2 offer-slice characterization. A truthful feasible deterministic
single-parameter offer is either always rejecting, or has a critical price `v`
such that reports below `v` lose and reports above `v` win at price `v`; the
boundary report `v` may win or lose.
-/
theorem paper_lemma9_2_deterministic_offer_bid_independent
    {offer : ℝ → Option ℝ}
    (htruth : DeterministicOfferTruthful offer)
    (hfeasible : DeterministicOfferFeasible offer) :
    DeterministicOfferBidIndependent offer := by
  exact deterministicOffer_bidIndependent_of_truthful htruth hfeasible

/--
GHW Lemma 9.2 threshold-domination form. A bid-independent deterministic offer
slice has a threshold that dominates every winning payment.
-/
theorem paper_lemma9_2_deterministic_offer_exists_threshold_dominates
    {offer : ℝ → Option ℝ}
    (hbid : DeterministicOfferBidIndependent offer) :
    ∃ threshold, DeterministicOfferThresholdDominates offer threshold := by
  exact deterministicOffer_exists_thresholdDominates_of_bidIndependent hbid

/--
GHW Lemma 9.2 auction-level form. A truthful, individually rational,
no-positive-transfers deterministic digital-goods auction with binary
allocations induces bid-independent critical-price offer slices after fixing
the other bids.
-/
theorem paper_lemma9_2_deterministic_truthful_auction_bid_independent_slices
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    DeterministicOfferBidIndependent (deterministicAuctionOffer M bids i) := by
  rw [paper_digital_goods_truthful_eq] at htruth
  exact deterministicAuctionOffer_bidIndependent_of_truthful
    M htruth hIR hNPT hbinary bids i

/--
GHW Lemma 9.2 auction-level threshold-domination form. After fixing other bids,
a truthful, individually rational, no-positive-transfers deterministic auction
has a nonnegative threshold that dominates the bidder's payment slice.
-/
theorem paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := by
  rw [paper_digital_goods_truthful_eq] at htruth
  exact
    deterministicAuctionOffer_exists_nonnegative_thresholdDominates_of_truthful
      M htruth hIR hNPT hbinary bids i

/--
GHW Lemma 9.2 payment-bound form. A nonnegative threshold dominating a fixed
offer slice gives the posted-threshold upper bound on the actual payment.
-/
theorem paper_lemma9_2_deterministic_auction_payment_le_threshold
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hbinary : M.BinaryAllocation)
    (hloser : M.LosersPayZero)
    (bids : Agent → ℝ) (i : Agent) (value threshold : ℝ)
    (hthreshold_nonneg : 0 ≤ threshold)
    (hdom :
      DeterministicOfferThresholdDominates
        (deterministicAuctionOffer M bids i) threshold) :
    M.payment (Function.update bids i value) i ≤
      if threshold ≤ value then threshold else 0 := by
  exact
    deterministicAuction_payment_le_threshold_of_offer_thresholdDominates
      M hbinary hloser bids i value threshold hthreshold_nonneg hdom

/--
GHW Theorem 9.3 reduction seam. Once a truthful deterministic auction has been
converted slice-by-slice into the count-threshold bid-independent rule supplied
by Lemma 9.2, the same binary lower-bound construction as Theorem 9.1 applies.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ, ∃ fixedPriceLowerBound : ℝ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            thresholdPrice highValue highCount lowCount ≤
        fixedPriceLowerBound ∧
      (highValue : ℝ) * (alpha : ℝ) ≤ fixedPriceLowerBound := by
  exact paper_theorem9_1_arbitrary_threshold_scaled_lower_bound
    thresholdPrice hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 count-threshold reduction with the actual fixed-price
benchmark. After Lemma 9.2 converts a deterministic truthful auction to the
paper's bid-independent/count-threshold rule on binary inputs, Theorem 9.1
supplies a two-value input where deterministic revenue is a `1 / h` fraction
of `F`.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_fixed_price_benchmark
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          (thresholdPriceAuction
            (twoValueCountThresholdPrice
              thresholdPrice highCount lowCount)).revenue
              (twoValueBidProfile highValue highCount lowCount) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_1_concrete_count_threshold_scaled_lower_bound_fixed_price_benchmark
      thresholdPrice hhigh_ge_two halpha_pos

/--
Representation seam for GHW Theorem 9.3 on binary inputs. A deterministic
truthful auction has been reduced to the paper's anonymous bid-independent
form when its revenue on every two-value input agrees with the revenue induced
by a price rule `f` on the canonical erased-bid list.
-/
def paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    (highValue : ℕ) : Prop :=
  ∀ highCount lowCount,
    auctionRevenue highCount lowCount =
      twoValueBidIndependentPriceRevenue
        (twoValueListBidIndependentThresholdPrice priceRule highValue)
        highValue highCount lowCount

/--
GHW Theorem 9.3 representation bridge for count-threshold binary rules. A
count-threshold price function is a special case of the paper's anonymous
erased-bid-list price rule: count the high values and low `1` values in the
erased list, then apply the count rule.
-/
theorem paper_theorem9_3_count_threshold_binary_anonymous_bid_independent_revenue_representation
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue : ℕ}
    (hhigh_ne_one : (highValue : ℝ) ≠ 1) :
    paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation
      (fun highCount lowCount =>
        twoValueBidIndependentPriceRevenue
          thresholdPrice highValue highCount lowCount)
      (twoValueCountListPriceRule thresholdPrice highValue)
      highValue := by
  intro highCount lowCount
  rw [twoValueListBidIndependentThresholdPrice_countListPriceRule
    thresholdPrice hhigh_ne_one]

/--
Domination seam for GHW Theorem 9.3 on binary inputs. It is enough for the
paper's bid-independent/count-threshold abstraction to upper-bound the
deterministic auction revenue on every two-value input: Theorem 9.1 then gives
an input where the actual deterministic auction revenue is also small.
-/
def paper_theorem9_3_binary_count_threshold_revenue_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (thresholdPrice : ℕ → ℕ → ℝ)
    (highValue : ℕ) : Prop :=
  ∀ highCount lowCount,
    auctionRevenue highCount lowCount ≤
      twoValueBidIndependentPriceRevenue
        thresholdPrice highValue highCount lowCount

/--
Concrete two-value auction-family payment certificate for the Section 9.3
count-threshold domination seam. On every binary input, each high bidder's
payment is bounded by the high-bidder erased-profile threshold, and each low
bidder's payment is bounded by the low-bidder erased-profile threshold. The
`if` terms exactly match the paper's convention that a posted threshold earns
zero revenue from a bidder whose value is below the threshold.
-/
def paper_theorem9_3_binary_count_threshold_payment_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ) (highValue : ℕ) : Prop :=
  ∀ highCount lowCount,
    let bids := twoValueBidProfile highValue highCount lowCount
    (∀ i : Fin highCount,
      (auctionFamily highCount lowCount).payment bids (Sum.inl i) ≤
        if thresholdPrice (highCount - 1) lowCount ≤ (highValue : ℝ) then
          thresholdPrice (highCount - 1) lowCount
        else 0) ∧
    (∀ i : Fin lowCount,
      (auctionFamily highCount lowCount).payment bids (Sum.inr i) ≤
        if thresholdPrice highCount (lowCount - 1) ≤ 1 then
          thresholdPrice highCount (lowCount - 1)
        else 0)

/--
Slice-level version of the Section 9.3 count-threshold certificate. It says
that the threshold selected from each erased binary profile is nonnegative and
dominates the corresponding deterministic offer slice.
-/
def paper_theorem9_3_binary_count_threshold_slice_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ) (highValue : ℕ) : Prop :=
  ∀ highCount lowCount,
    let bids := twoValueBidProfile highValue highCount lowCount
    (∀ i : Fin highCount,
      0 ≤ thresholdPrice (highCount - 1) lowCount ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer
            (auctionFamily highCount lowCount) bids (Sum.inl i))
          (thresholdPrice (highCount - 1) lowCount)) ∧
    (∀ i : Fin lowCount,
      0 ≤ thresholdPrice highCount (lowCount - 1) ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer
            (auctionFamily highCount lowCount) bids (Sum.inr i))
          (thresholdPrice highCount (lowCount - 1)))

/--
Slice-level threshold domination implies the payment upper-bound certificate for
actual two-value auction families.
-/
theorem paper_theorem9_3_binary_count_threshold_payment_upper_bound_of_slice_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ) (highValue : ℕ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_count_threshold_slice_upper_bound
        auctionFamily thresholdPrice highValue) :
    paper_theorem9_3_binary_count_threshold_payment_upper_bound
      auctionFamily thresholdPrice highValue := by
  classical
  intro highCount lowCount
  let bids := twoValueBidProfile highValue highCount lowCount
  constructor
  · intro i
    have hupdate :
        Function.update bids (Sum.inl i) (highValue : ℝ) = bids := by
      funext j
      by_cases hji : j = Sum.inl i
      · subst j
        simp [bids, twoValueBidProfile]
      · simp [Function.update, hji]
    obtain ⟨hthreshold_nonneg, hdom⟩ :=
      (hslice highCount lowCount).1 i
    have hbound :=
      deterministicAuction_payment_le_threshold_of_offer_thresholdDominates
        (auctionFamily highCount lowCount)
        (hbinary highCount lowCount)
        (hloser highCount lowCount)
        bids (Sum.inl i) (highValue : ℝ)
        (thresholdPrice (highCount - 1) lowCount)
        hthreshold_nonneg hdom
    simpa [hupdate] using hbound
  · intro i
    have hupdate :
        Function.update bids (Sum.inr i) (1 : ℝ) = bids := by
      funext j
      by_cases hji : j = Sum.inr i
      · subst j
        simp [bids, twoValueBidProfile]
      · simp [Function.update, hji]
    obtain ⟨hthreshold_nonneg, hdom⟩ :=
      (hslice highCount lowCount).2 i
    have hbound :=
      deterministicAuction_payment_le_threshold_of_offer_thresholdDominates
        (auctionFamily highCount lowCount)
        (hbinary highCount lowCount)
        (hloser highCount lowCount)
        bids (Sum.inr i) (1 : ℝ)
        (thresholdPrice highCount (lowCount - 1))
        hthreshold_nonneg hdom
    simpa [hupdate] using hbound

/--
Payment bounds for an actual two-value auction family imply the abstract
revenue-domination certificate used by Theorem 9.3.
-/
theorem paper_theorem9_3_binary_count_threshold_revenue_upper_bound_of_payment_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ) (highValue : ℕ)
    (hpay :
      paper_theorem9_3_binary_count_threshold_payment_upper_bound
        auctionFamily thresholdPrice highValue) :
    paper_theorem9_3_binary_count_threshold_revenue_upper_bound
      (fun highCount lowCount =>
        (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      thresholdPrice highValue := by
  classical
  intro highCount lowCount
  let bids := twoValueBidProfile highValue highCount lowCount
  let highTerm : ℝ :=
    if thresholdPrice (highCount - 1) lowCount ≤ (highValue : ℝ) then
      thresholdPrice (highCount - 1) lowCount
    else 0
  let lowTerm : ℝ :=
    if thresholdPrice highCount (lowCount - 1) ≤ 1 then
      thresholdPrice highCount (lowCount - 1)
    else 0
  have hhigh :
      (∑ i : Fin highCount,
        (auctionFamily highCount lowCount).payment bids (Sum.inl i)) ≤
        ∑ _i : Fin highCount, highTerm := by
    exact Finset.sum_le_sum fun i _hi => (hpay highCount lowCount).1 i
  have hlow :
      (∑ i : Fin lowCount,
        (auctionFamily highCount lowCount).payment bids (Sum.inr i)) ≤
        ∑ _i : Fin lowCount, lowTerm := by
    exact Finset.sum_le_sum fun i _hi => (hpay highCount lowCount).2 i
  have hsum :
      (auctionFamily highCount lowCount).revenue bids ≤
        (highCount : ℝ) * highTerm + (lowCount : ℝ) * lowTerm := by
    unfold DigitalGoodsAuction.revenue
    rw [Fintype.sum_sum_type]
    exact le_trans (add_le_add hhigh hlow) (by
      simp [highTerm, lowTerm, Finset.sum_const, nsmul_eq_mul])
  simpa [twoValueBidIndependentPriceRevenue, bids, highTerm, lowTerm]
    using hsum

/--
Paper-facing count-threshold auction-family certificate for Section 9.3.
This packages the actual deterministic auction family together with the
count-threshold price abstraction that dominates its binary payments.
-/
structure PaperTheorem93CountThresholdAuctionFamilyCertificate
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  thresholdPrice : ℕ → ℕ → ℝ
  payment_upper_bound :
    paper_theorem9_3_binary_count_threshold_payment_upper_bound
      auctionFamily thresholdPrice highValue

/--
Build the count-threshold auction-family certificate from slice-level
threshold domination plus binary allocations and zero loser payments.
-/
def paper_theorem9_3_count_threshold_auction_family_certificate_of_slice_upper_bound
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_count_threshold_slice_upper_bound
        auctionFamily thresholdPrice highValue) :
    PaperTheorem93CountThresholdAuctionFamilyCertificate highValue where
  auctionFamily := auctionFamily
  thresholdPrice := thresholdPrice
  payment_upper_bound :=
    paper_theorem9_3_binary_count_threshold_payment_upper_bound_of_slice_upper_bound
      auctionFamily thresholdPrice highValue hbinary hloser hslice

/--
GHW Theorem 9.3 count-threshold domination form. If Lemma 9.2 and anonymity
produce a count-threshold binary rule whose revenue dominates the deterministic
auction revenue, the Theorem 9.1 witness transfers to the actual auction.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (thresholdPrice : ℕ → ℕ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_count_threshold_revenue_upper_bound
        auctionRevenue thresholdPrice highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) * auctionRevenue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hrev, hside⟩ :=
    paper_theorem9_1_arbitrary_threshold_scaled_lower_bound_fixed_price_benchmark
      thresholdPrice hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hside⟩
  have hH_nonneg : 0 ≤ (highValue : ℝ) := by
    exact_mod_cast Nat.zero_le highValue
  exact le_trans
    (mul_le_mul_of_nonneg_left (hupper highCount lowCount) hH_nonneg)
    hrev

/--
GHW Theorem 9.3 count-threshold ratio form under revenue domination. This is
the form needed when the deterministic critical-price slice is represented by a
binary threshold rule that may overestimate revenue at boundary bids.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (thresholdPrice : ℕ → ℕ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_count_threshold_revenue_upper_bound
        auctionRevenue thresholdPrice highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hrev, hside⟩ :=
    paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_upper_bound
      auctionRevenue thresholdPrice hupper hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hside⟩
  have hh_pos : 0 < (highValue : ℝ) := by
    have hh_nat_pos : 0 < highValue := lt_of_lt_of_le (by decide) hhigh_ge_two
    exact_mod_cast hh_nat_pos
  have halpha_pos_real : 0 < (alpha : ℝ) := by
    exact_mod_cast halpha_pos
  have hbenchmark_pos :
      0 < twoValueFixedPriceBenchmark highValue highCount lowCount := by
    exact lt_of_lt_of_le (mul_pos hh_pos halpha_pos_real) hside
  exact
    paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark
      hh_pos hbenchmark_pos hrev

/--
Attained count-threshold ratio witness under revenue domination.  This follows
the same finite construction as Theorem 9.1 while retaining its positive
high-bid count.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound_attained
    (auctionRevenue : ℕ → ℕ → ℝ) (thresholdPrice : ℕ → ℕ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_count_threshold_revenue_upper_bound
        auctionRevenue thresholdPrice highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hattained, hthreshold, hside⟩ :=
    twoValueBidIndependentPrice_exists_low_revenue_witness_scaled_benchmark_attained
      thresholdPrice hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, hattained, ?_, hside⟩
  have hh_pos : 0 < (highValue : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hhigh_ge_two)
  have hH_nonneg : 0 ≤ (highValue : ℝ) := le_of_lt hh_pos
  have hrev :
      (highValue : ℝ) * auctionRevenue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount :=
    (mul_le_mul_of_nonneg_left
      (hupper highCount lowCount) hH_nonneg).trans hthreshold
  have halpha_pos_real : 0 < (alpha : ℝ) := by
    exact_mod_cast halpha_pos
  have hbenchmark_pos :
      0 < twoValueFixedPriceBenchmark highValue highCount lowCount := by
    exact lt_of_lt_of_le (mul_pos hh_pos halpha_pos_real) hside
  exact
    paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark
      hh_pos hbenchmark_pos hrev

/--
GHW Theorem 9.3 for an actual two-value auction family with a count-threshold
payment-domination certificate.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_auction_family_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93CountThresholdAuctionFamilyCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          (certificate.auctionFamily highCount lowCount).revenue
            (twoValueBidProfile highValue highCount lowCount) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_upper_bound
      (fun highCount lowCount =>
        (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      certificate.thresholdPrice
      (paper_theorem9_3_binary_count_threshold_revenue_upper_bound_of_payment_upper_bound
        certificate.auctionFamily certificate.thresholdPrice highValue
        certificate.payment_upper_bound)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form for an actual two-value auction family with a
count-threshold payment-domination certificate.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_auction_family_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93CountThresholdAuctionFamilyCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound
      (fun highCount lowCount =>
        (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      certificate.thresholdPrice
      (paper_theorem9_3_binary_count_threshold_revenue_upper_bound_of_payment_upper_bound
        certificate.auctionFamily certificate.thresholdPrice highValue
        certificate.payment_upper_bound)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form directly from count-threshold slice domination.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_slice_upper_bound
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_count_threshold_slice_upper_bound
        auctionFamily thresholdPrice highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_auction_family_certificate
      (paper_theorem9_3_count_threshold_auction_family_certificate_of_slice_upper_bound
        auctionFamily thresholdPrice hbinary hloser hslice)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form directly from count-threshold slice domination,
using the paper's standard individual-rationality and no-positive-transfers
assumptions to discharge zero loser payments.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_slice_upper_bound_ir_npt
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (thresholdPrice : ℕ → ℕ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (hslice :
      paper_theorem9_3_binary_count_threshold_slice_upper_bound
        auctionFamily thresholdPrice highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_slice_upper_bound
      auctionFamily thresholdPrice hbinary
      (fun highCount lowCount =>
        DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
          (auctionFamily highCount lowCount)
          (hIR highCount lowCount) (hNPT highCount lowCount))
      hslice hhigh_ge_two halpha_pos

/--
Anonymous erased-bid-list version of the Section 9.3 domination seam.
-/
def paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    (highValue : ℕ) : Prop :=
  paper_theorem9_3_binary_count_threshold_revenue_upper_bound
    auctionRevenue
    (twoValueListBidIndependentThresholdPrice priceRule highValue)
    highValue

/--
Anonymous erased-bid-list payment certificate for an actual two-value auction
family. This is the concrete-family analogue of
`paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound`.
-/
def paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ) (highValue : ℕ) : Prop :=
  paper_theorem9_3_binary_count_threshold_payment_upper_bound
    auctionFamily
    (twoValueListBidIndependentThresholdPrice priceRule highValue)
    highValue

/--
Anonymous erased-bid-list slice certificate for an actual two-value auction
family.
-/
def paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ) (highValue : ℕ) : Prop :=
  paper_theorem9_3_binary_count_threshold_slice_upper_bound
    auctionFamily
    (twoValueListBidIndependentThresholdPrice priceRule highValue)
    highValue

/--
Anonymous slice-level threshold domination implies the anonymous payment
upper-bound certificate for actual two-value auction families.
-/
theorem paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound_of_slice_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ) (highValue : ℕ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
        auctionFamily priceRule highValue) :
    paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound
      auctionFamily priceRule highValue := by
  exact
    paper_theorem9_3_binary_count_threshold_payment_upper_bound_of_slice_upper_bound
      auctionFamily
      (twoValueListBidIndependentThresholdPrice priceRule highValue)
      highValue hbinary hloser hslice

/--
Anonymous erased-bid-list payment bounds for an actual two-value auction family
imply the abstract anonymous revenue-domination certificate.
-/
theorem paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_payment_upper_bound
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ) (highValue : ℕ)
    (hpay :
      paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound
        auctionFamily priceRule highValue) :
    paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
      (fun highCount lowCount =>
        (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      priceRule highValue := by
  exact
    paper_theorem9_3_binary_count_threshold_revenue_upper_bound_of_payment_upper_bound
      auctionFamily
      (twoValueListBidIndependentThresholdPrice priceRule highValue)
      highValue hpay

/--
Exact anonymous bid-independent representation implies the weaker domination
representation.
-/
theorem paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_representation
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue : ℕ}
    (hrep :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation
        auctionRevenue priceRule highValue) :
  paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
      auctionRevenue priceRule highValue := by
  intro highCount lowCount
  rw [hrep highCount lowCount]

/--
Paper-facing anonymous auction-family certificate for Section 9.3. The auction
family is indexed by binary input size, and the anonymous erased-bid-list
`priceRule` supplies payment upper bounds on those binary inputs.
-/
structure PaperTheorem93AnonymousAuctionFamilyCertificate
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  priceRule : List ℝ → ℝ
  payment_upper_bound :
    paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound
      auctionFamily priceRule highValue

/--
Build the anonymous auction-family certificate from anonymous slice-level
threshold domination plus binary allocations and zero loser payments.
-/
def paper_theorem9_3_anonymous_auction_family_certificate_of_slice_upper_bound
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
        auctionFamily priceRule highValue) :
    PaperTheorem93AnonymousAuctionFamilyCertificate highValue where
  auctionFamily := auctionFamily
  priceRule := priceRule
  payment_upper_bound :=
    paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound_of_slice_upper_bound
      auctionFamily priceRule highValue hbinary hloser hslice

/--
GHW Theorem 9.3 anonymous bid-independent representation form. Once Lemma 9.2
and the paper's anonymity convention identify a deterministic truthful auction
with a bid-independent list-price rule on binary inputs, Theorem 9.1 supplies
the deterministic lower-bound witness against the actual fixed-price benchmark.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_representation
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue alpha : ℕ}
    (hrep :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation
        auctionRevenue priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) * auctionRevenue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hrev, hside⟩ :=
    paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
      priceRule hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hside⟩
  rw [hrep highCount lowCount]
  exact hrev

/--
GHW Theorem 9.3 anonymous bid-independent domination form. This is the robust
version of the representation theorem: the anonymous erased-bid-list rule need
only dominate the deterministic auction revenue on binary inputs.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
        auctionRevenue priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) * auctionRevenue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_upper_bound
      auctionRevenue
      (twoValueListBidIndependentThresholdPrice priceRule highValue)
      hupper hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio witness form. Under the anonymous bid-independent
binary representation, the adversarial input satisfies the paper's displayed
ratio `R / F <= 1 / h` against the actual one-winner finite fixed-price
benchmark, and also satisfies the side condition `alpha * h <= F`.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_representation
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue alpha : ℕ}
    (hrep :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation
        auctionRevenue priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  obtain ⟨highCount, lowCount, hrev, hside⟩ :=
    paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_representation
      auctionRevenue priceRule hrep hhigh_ge_two halpha_pos
  refine ⟨highCount, lowCount, ?_, hside⟩
  have hh_pos : 0 < (highValue : ℝ) := by
    have hh_nat_pos : 0 < highValue := lt_of_lt_of_le (by decide) hhigh_ge_two
    exact_mod_cast hh_nat_pos
  have halpha_pos_real : 0 < (alpha : ℝ) := by
    exact_mod_cast halpha_pos
  have hbenchmark_pos :
      0 < twoValueFixedPriceBenchmark highValue highCount lowCount := by
    exact lt_of_lt_of_le (mul_pos hh_pos halpha_pos_real) hside
  exact
    paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark
      hh_pos hbenchmark_pos hrev

/--
GHW Theorem 9.3 ratio witness under anonymous bid-independent domination.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
        auctionRevenue priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound
      auctionRevenue
      (twoValueListBidIndependentThresholdPrice priceRule highValue)
      hupper hhigh_ge_two halpha_pos

/-- Attained anonymous erased-list domination form of Theorem 9.3. -/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound_attained
    (auctionRevenue : ℕ → ℕ → ℝ) (priceRule : List ℝ → ℝ)
    {highValue alpha : ℕ}
    (hupper :
      paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
        auctionRevenue priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound_attained
      auctionRevenue
      (twoValueListBidIndependentThresholdPrice priceRule highValue)
      hupper hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 for an actual two-value auction family with an anonymous
erased-bid-list payment-domination certificate.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_auction_family_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93AnonymousAuctionFamilyCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          (certificate.auctionFamily highCount lowCount).revenue
            (twoValueBidProfile highValue highCount lowCount) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_upper_bound
      (fun highCount lowCount =>
        (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      certificate.priceRule
      (paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_payment_upper_bound
        certificate.auctionFamily certificate.priceRule highValue
        certificate.payment_upper_bound)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form for an actual two-value auction family with an
anonymous erased-bid-list payment-domination certificate.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_auction_family_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93AnonymousAuctionFamilyCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound
      (fun highCount lowCount =>
        (certificate.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      certificate.priceRule
      (paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_payment_upper_bound
        certificate.auctionFamily certificate.priceRule highValue
        certificate.payment_upper_bound)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form directly from anonymous erased-bid-list slice
domination.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hloser :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).LosersPayZero)
    (hslice :
      paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
        auctionFamily priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_auction_family_certificate
      (paper_theorem9_3_anonymous_auction_family_certificate_of_slice_upper_bound
        auctionFamily priceRule hbinary hloser hslice)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 ratio form directly from anonymous erased-bid-list slice
domination, using individual rationality and no-positive-transfers to discharge
zero loser payments.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound_ir_npt
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ)
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (hslice :
      paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
        auctionFamily priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound
      auctionFamily priceRule hbinary
      (fun highCount lowCount =>
        DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
          (auctionFamily highCount lowCount)
          (hIR highCount lowCount) (hNPT highCount lowCount))
      hslice hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 paper-facing deterministic-truthful family form. Truthfulness
is carried explicitly; the remaining paper-model obligation is the anonymous
erased-bid-list slice certificate, which is the formal version of the paper's
bid-independent reduction after Lemma 9.2.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_slice_upper_bound
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (priceRule : List ℝ → ℝ)
    (_htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (hslice :
      paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
        auctionFamily priceRule highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound_ir_npt
      auctionFamily priceRule hbinary hIR hNPT hslice
      hhigh_ge_two halpha_pos

/--
Erasing an in-bounds element from a constant list leaves one fewer copy of the
same constant. This paper-local helper keeps the binary erased-bid convention
definitionally close to `List.replicate`.
-/
theorem paper_theorem9_3_eraseIdx_replicate_of_lt {α : Type*} (a : α) :
    ∀ {n i : ℕ}, i < n →
      (List.replicate n a).eraseIdx i = List.replicate (n - 1) a
  | 0, _i, hi => by omega
  | n + 1, 0, _hi => by simp
  | n + 1, i + 1, hi => by
      have hi' : i < n := Nat.succ_lt_succ_iff.mp hi
      rw [List.replicate_succ]
      simp [paper_theorem9_3_eraseIdx_replicate_of_lt a hi']
      cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ]

/--
If a tuple is updated at one coordinate and that same coordinate is erased
from the resulting `List.ofFn`, the erased list is unchanged.
-/
theorem paper_theorem9_3_eraseIdx_ofFn_update_self {α : Type*} :
    ∀ {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α),
      (List.ofFn (Function.update f i a)).eraseIdx (i : ℕ) =
        (List.ofFn f).eraseIdx (i : ℕ)
  | 0, _f, i, _a => by exact Fin.elim0 i
  | n + 1, f, i, a => by
      cases i using Fin.cases with
      | zero =>
          simp [Function.update]
      | succ i =>
          simp [List.ofFn_succ, Function.update]
          constructor
          · intro h
            cases h
          · have hfun :
                (fun i_1 : Fin n => if i_1 = i then a else f i_1.succ) =
                  Function.update (fun j : Fin n => f j.succ) i a := by
              funext j
              rw [Function.update_apply]
            rw [hfun]
            exact
              paper_theorem9_3_eraseIdx_ofFn_update_self
                (fun j : Fin n => f j.succ) i a

/--
The anonymous erased bid list seen by a bidder in a two-value profile. High and
low bidders are stored in separate finite blocks, and the target bidder's own
coordinate is erased from the appropriate block.
-/
def paper_theorem9_3_erased_report_list {highCount lowCount : ℕ}
    (bids : TwoValueAgent highCount lowCount → ℝ)
    (i : TwoValueAgent highCount lowCount) : List ℝ :=
  match i with
  | Sum.inl i =>
      (List.ofFn fun j : Fin highCount => bids (Sum.inl j)).eraseIdx (i : ℕ) ++
        (List.ofFn fun j : Fin lowCount => bids (Sum.inr j))
  | Sum.inr i =>
      (List.ofFn fun j : Fin highCount => bids (Sum.inl j)) ++
        (List.ofFn fun j : Fin lowCount => bids (Sum.inr j)).eraseIdx (i : ℕ)

/--
Changing a bidder's own report does not change the erased list used to compute
that bidder's offer.
-/
theorem paper_theorem9_3_erased_report_list_update_self
    {highCount lowCount : ℕ}
    (bids : TwoValueAgent highCount lowCount → ℝ)
    (i : TwoValueAgent highCount lowCount) (report : ℝ) :
    paper_theorem9_3_erased_report_list (Function.update bids i report) i =
      paper_theorem9_3_erased_report_list bids i := by
  cases i with
  | inl i =>
      simp [paper_theorem9_3_erased_report_list, Function.update]
      have hfun :
          (fun j : Fin highCount => if j = i then report else bids (Sum.inl j)) =
            Function.update (fun j : Fin highCount => bids (Sum.inl j)) i report := by
        funext j
        rw [Function.update_apply]
      rw [hfun]
      exact
        paper_theorem9_3_eraseIdx_ofFn_update_self
          (fun j : Fin highCount => bids (Sum.inl j)) i report
  | inr i =>
      simp [paper_theorem9_3_erased_report_list, Function.update]
      have hfun :
          (fun j : Fin lowCount => if j = i then report else bids (Sum.inr j)) =
            Function.update (fun j : Fin lowCount => bids (Sum.inr j)) i report := by
        funext j
        rw [Function.update_apply]
      rw [hfun]
      exact
        paper_theorem9_3_eraseIdx_ofFn_update_self
          (fun j : Fin lowCount => bids (Sum.inr j)) i report

/-- High-bidder erased lists in canonical two-value profiles. -/
theorem paper_theorem9_3_erased_report_list_twoValueBidProfile_high
    {highValue highCount lowCount : ℕ} (i : Fin highCount) :
    paper_theorem9_3_erased_report_list
        (twoValueBidProfile highValue highCount lowCount) (Sum.inl i) =
      twoValueErasedBidList highValue (highCount - 1) lowCount := by
  simp [paper_theorem9_3_erased_report_list, twoValueBidProfile,
    twoValueErasedBidList,
    paper_theorem9_3_eraseIdx_replicate_of_lt (highValue : ℝ) i.isLt]

/-- Low-bidder erased lists in canonical two-value profiles. -/
theorem paper_theorem9_3_erased_report_list_twoValueBidProfile_low
    {highValue highCount lowCount : ℕ} (i : Fin lowCount) :
    paper_theorem9_3_erased_report_list
        (twoValueBidProfile highValue highCount lowCount) (Sum.inr i) =
      twoValueErasedBidList highValue highCount (lowCount - 1) := by
  simp [paper_theorem9_3_erased_report_list, twoValueBidProfile,
    twoValueErasedBidList,
    paper_theorem9_3_eraseIdx_replicate_of_lt (1 : ℝ) i.isLt]

/-- Deterministic posted-threshold offer at a fixed price. -/
noncomputable def paper_theorem9_3_threshold_offer (price : ℝ) :
    ℝ → Option ℝ :=
  fun report => if price ≤ report then some price else none

theorem paper_theorem9_3_threshold_offer_truthful (price : ℝ) :
    DeterministicOfferTruthful (paper_theorem9_3_threshold_offer price) := by
  intro value report
  unfold deterministicOfferUtility paper_theorem9_3_threshold_offer
  by_cases hvalue : price ≤ value
  · by_cases hreport : price ≤ report
    · simp [hvalue, hreport]
    · simp [hvalue, hreport, sub_nonneg.mpr hvalue]
  · by_cases hreport : price ≤ report
    · simp [hvalue, hreport]
      exact le_of_not_ge hvalue
    · simp [hvalue, hreport]

theorem paper_theorem9_3_threshold_offer_feasible (price : ℝ) :
    DeterministicOfferFeasible (paper_theorem9_3_threshold_offer price) := by
  intro report offeredPrice hoff
  unfold paper_theorem9_3_threshold_offer at hoff
  by_cases h : price ≤ report
  · simp [h] at hoff
    subst offeredPrice
    exact h
  · simp [h] at hoff

theorem paper_theorem9_3_threshold_offer_noPositiveTransfers
    {price : ℝ} (hprice : 0 ≤ price) :
    ∀ report offeredPrice,
      paper_theorem9_3_threshold_offer price report = some offeredPrice →
        0 ≤ offeredPrice := by
  intro report offeredPrice hoff
  unfold paper_theorem9_3_threshold_offer at hoff
  by_cases h : price ≤ report
  · simp [h] at hoff
    subst offeredPrice
    exact hprice
  · simp [h] at hoff

/--
Convert the paper's anonymous erased-bid-list price rule into the deterministic
offer rule used by the local auction model.
-/
noncomputable def paper_theorem9_3_bid_list_price_offer
    (priceRule : List ℝ → ℝ) : List ℝ → ℝ → Option ℝ :=
  fun erasedBids => paper_theorem9_3_threshold_offer (priceRule erasedBids)

/--
Primitive erased-bid-list offer auction for GHW Theorem 9.3. The offer rule
sees the anonymous erased bid list and the bidder's report, returning either a
posted price (`some price`) or rejection (`none`).
-/
noncomputable def paper_theorem9_3_bid_list_offer_auction
    (offerRule : List ℝ → ℝ → Option ℝ)
    (highCount lowCount : ℕ) :
    DigitalGoodsAuction (TwoValueAgent highCount lowCount) where
  allocation bids i :=
    match offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
    | some _ => 1
    | none => 0
  payment bids i :=
    match offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
    | some price => price
    | none => 0

/-- The paper's anonymous list-price rule as a concrete bid-list offer auction. -/
noncomputable def paper_theorem9_3_bid_list_price_auction
    (priceRule : List ℝ → ℝ)
    (highCount lowCount : ℕ) :
    DigitalGoodsAuction (TwoValueAgent highCount lowCount) :=
  paper_theorem9_3_bid_list_offer_auction
    (paper_theorem9_3_bid_list_price_offer priceRule)
    highCount lowCount

theorem paper_theorem9_3_bid_list_offer_auction_binary
    (offerRule : List ℝ → ℝ → Option ℝ)
    (highCount lowCount : ℕ) :
    (paper_theorem9_3_bid_list_offer_auction
      offerRule highCount lowCount).BinaryAllocation := by
  intro bids i
  unfold paper_theorem9_3_bid_list_offer_auction
  cases h : offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
  | none => simp [h]
  | some price => simp [h]

theorem paper_theorem9_3_bid_list_offer_auction_truthful
    (offerRule : List ℝ → ℝ → Option ℝ)
    {highCount lowCount : ℕ}
    (htruth :
      ∀ erasedBids, DeterministicOfferTruthful (offerRule erasedBids)) :
    paper_digital_goods_truthful
      (paper_theorem9_3_bid_list_offer_auction
        offerRule highCount lowCount) := by
  intro values i report
  let erased := paper_theorem9_3_erased_report_list values i
  have hslice := htruth erased (values i) report
  cases hreport : offerRule erased report with
  | none =>
      cases htruthful : offerRule erased (values i) with
      | none =>
          simp [DigitalGoodsAuction.utility,
            paper_theorem9_3_bid_list_offer_auction,
            deterministicOfferUtility, erased,
            paper_theorem9_3_erased_report_list_update_self values i report,
            Function.update_self, hreport, htruthful] at hslice ⊢
      | some truthPrice =>
          simp [DigitalGoodsAuction.utility,
            paper_theorem9_3_bid_list_offer_auction,
            deterministicOfferUtility, erased,
            paper_theorem9_3_erased_report_list_update_self values i report,
            Function.update_self, hreport, htruthful] at hslice ⊢
          linarith
  | some reportPrice =>
      cases htruthful : offerRule erased (values i) with
      | none =>
          simp [DigitalGoodsAuction.utility,
            paper_theorem9_3_bid_list_offer_auction,
            deterministicOfferUtility, erased,
            paper_theorem9_3_erased_report_list_update_self values i report,
            Function.update_self, hreport, htruthful] at hslice ⊢
          linarith
      | some truthPrice =>
          simp [DigitalGoodsAuction.utility,
            paper_theorem9_3_bid_list_offer_auction,
            deterministicOfferUtility, erased,
            paper_theorem9_3_erased_report_list_update_self values i report,
            Function.update_self, hreport, htruthful] at hslice ⊢
          linarith

theorem paper_theorem9_3_bid_list_offer_auction_individuallyRational
    (offerRule : List ℝ → ℝ → Option ℝ)
    {highCount lowCount : ℕ}
    (hfeasible :
      ∀ erasedBids, DeterministicOfferFeasible (offerRule erasedBids)) :
    (paper_theorem9_3_bid_list_offer_auction
      offerRule highCount lowCount).IndividuallyRational := by
  intro values i
  unfold DigitalGoodsAuction.utility paper_theorem9_3_bid_list_offer_auction
  cases hoff :
      offerRule (paper_theorem9_3_erased_report_list values i) (values i) with
  | none => simp [hoff]
  | some price =>
      have hprice :=
        hfeasible (paper_theorem9_3_erased_report_list values i)
          (values i) price hoff
      simp [hoff]
      linarith

theorem paper_theorem9_3_bid_list_offer_auction_noPositiveTransfers
    (offerRule : List ℝ → ℝ → Option ℝ)
    {highCount lowCount : ℕ}
    (hnpt : ∀ erasedBids report price,
      offerRule erasedBids report = some price → 0 ≤ price) :
    (paper_theorem9_3_bid_list_offer_auction
      offerRule highCount lowCount).NoPositiveTransfers := by
  intro bids i
  unfold paper_theorem9_3_bid_list_offer_auction
  cases hoff :
      offerRule (paper_theorem9_3_erased_report_list bids i) (bids i) with
  | none => simp [hoff]
  | some price =>
      simpa [hoff] using
        hnpt (paper_theorem9_3_erased_report_list bids i) (bids i) price hoff

/--
The primitive offer auction has the erased-list factorization required by the
existing Theorem 9.3 source bridge for high bidders.
-/
theorem paper_theorem9_3_bid_list_offer_auction_offer_factor_high
    (offerRule : List ℝ → ℝ → Option ℝ)
    {highValue highCount lowCount : ℕ} (i : Fin highCount) :
    deterministicAuctionOffer
        (paper_theorem9_3_bid_list_offer_auction offerRule highCount lowCount)
        (twoValueBidProfile highValue highCount lowCount) (Sum.inl i) =
      offerRule
        (twoValueErasedBidList highValue (highCount - 1) lowCount) := by
  funext report
  simp [deterministicAuctionOffer, paper_theorem9_3_bid_list_offer_auction,
    paper_theorem9_3_erased_report_list_update_self
      (twoValueBidProfile highValue highCount lowCount) (Sum.inl i) report,
    paper_theorem9_3_erased_report_list_twoValueBidProfile_high i,
    Function.update_self]
  cases h :
      offerRule
        (twoValueErasedBidList highValue (highCount - 1) lowCount) report with
  | none => simp
  | some price => simp

/--
The primitive offer auction has the erased-list factorization required by the
existing Theorem 9.3 source bridge for low bidders.
-/
theorem paper_theorem9_3_bid_list_offer_auction_offer_factor_low
    (offerRule : List ℝ → ℝ → Option ℝ)
    {highValue highCount lowCount : ℕ} (i : Fin lowCount) :
    deterministicAuctionOffer
        (paper_theorem9_3_bid_list_offer_auction offerRule highCount lowCount)
        (twoValueBidProfile highValue highCount lowCount) (Sum.inr i) =
      offerRule
        (twoValueErasedBidList highValue highCount (lowCount - 1)) := by
  funext report
  simp [deterministicAuctionOffer, paper_theorem9_3_bid_list_offer_auction,
    paper_theorem9_3_erased_report_list_update_self
      (twoValueBidProfile highValue highCount lowCount) (Sum.inr i) report,
    paper_theorem9_3_erased_report_list_twoValueBidProfile_low i,
    Function.update_self]
  cases h :
      offerRule
        (twoValueErasedBidList highValue highCount (lowCount - 1)) report with
  | none => simp
  | some price => simp

/--
Primitive anonymity convention for the GHW Theorem 9.3 binary reduction.
For binary inputs, two bidder slices with the same erased bid list induce the
same deterministic offer function. The representative slice is always chosen
as the first high bidder in the binary profile with one additional high bid.
-/
structure PaperTheorem93ErasedBidOfferAnonymity
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount)) where
  high_offer_eq :
    ∀ highCount lowCount, ∀ i : Fin highCount,
      deterministicAuctionOffer
          (auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount)
          (Sum.inl i) =
        deterministicAuctionOffer
          (auctionFamily ((highCount - 1) + 1) lowCount)
          (twoValueBidProfile highValue ((highCount - 1) + 1) lowCount)
          (Sum.inl ⟨0, Nat.succ_pos (highCount - 1)⟩)
  low_offer_eq :
    ∀ highCount lowCount, ∀ i : Fin lowCount,
      deterministicAuctionOffer
          (auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount)
          (Sum.inr i) =
        deterministicAuctionOffer
          (auctionFamily (highCount + 1) (lowCount - 1))
          (twoValueBidProfile highValue (highCount + 1) (lowCount - 1))
          (Sum.inl ⟨0, Nat.succ_pos highCount⟩)

/--
Global erased-bid offer relabeling convention for the paper's anonymous
set-of-bids model. If two bidder slices see the same erased bid list, then the
deterministic offer as a function of the bidder's own report is the same.
-/
structure PaperTheorem93ErasedBidOfferRelabelingAnonymity
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount)) where
  offer_eq_of_erased :
    ∀ {highCount lowCount highCount' lowCount' : ℕ}
      (bids : TwoValueAgent highCount lowCount → ℝ)
      (bids' : TwoValueAgent highCount' lowCount' → ℝ)
      (i : TwoValueAgent highCount lowCount)
      (j : TwoValueAgent highCount' lowCount'),
      paper_theorem9_3_erased_report_list bids i =
        paper_theorem9_3_erased_report_list bids' j →
      deterministicAuctionOffer
          (auctionFamily highCount lowCount) bids i =
        deterministicAuctionOffer
          (auctionFamily highCount' lowCount') bids' j

/--
Concrete erased-bid-list offer auctions satisfy the global relabeling
convention: after a bidder's own report is erased, only the anonymous erased
list can affect that bidder's deterministic offer.
-/
theorem paper_theorem9_3_bid_list_offer_auction_relabeling_anonymity
    (offerRule : List ℝ → ℝ → Option ℝ) :
    PaperTheorem93ErasedBidOfferRelabelingAnonymity
      (fun highCount lowCount =>
        paper_theorem9_3_bid_list_offer_auction
          offerRule highCount lowCount) := by
  refine { offer_eq_of_erased := ?_ }
  intro highCount lowCount highCount' lowCount'
    bids bids' i j herased
  funext report
  simp [deterministicAuctionOffer, paper_theorem9_3_bid_list_offer_auction,
    paper_theorem9_3_erased_report_list_update_self bids i report,
    paper_theorem9_3_erased_report_list_update_self bids' j report,
    herased]

/--
The global erased-list relabeling convention implies the specialized
representative high/low equalities used by the current Theorem 9.3 bridge.
-/
theorem paper_theorem9_3_erased_bid_offer_anonymity_of_relabeling_anonymity
    {highValue : ℕ}
    {auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount)}
    (hanonymous :
      PaperTheorem93ErasedBidOfferRelabelingAnonymity auctionFamily) :
    PaperTheorem93ErasedBidOfferAnonymity
      (highValue := highValue) auctionFamily := by
  refine
    { high_offer_eq := ?_
      low_offer_eq := ?_ }
  · intro highCount lowCount i
    exact
      hanonymous.offer_eq_of_erased
        (twoValueBidProfile highValue highCount lowCount)
        (twoValueBidProfile highValue ((highCount - 1) + 1) lowCount)
        (Sum.inl i)
        (Sum.inl ⟨0, Nat.succ_pos (highCount - 1)⟩)
        (by
          rw [paper_theorem9_3_erased_report_list_twoValueBidProfile_high i,
            paper_theorem9_3_erased_report_list_twoValueBidProfile_high
              ⟨0, Nat.succ_pos (highCount - 1)⟩]
          simp)
  · intro highCount lowCount i
    exact
      hanonymous.offer_eq_of_erased
        (twoValueBidProfile highValue highCount lowCount)
        (twoValueBidProfile highValue (highCount + 1) (lowCount - 1))
        (Sum.inr i)
        (Sum.inl ⟨0, Nat.succ_pos highCount⟩)
        (by
          rw [paper_theorem9_3_erased_report_list_twoValueBidProfile_low i,
            paper_theorem9_3_erased_report_list_twoValueBidProfile_high
              ⟨0, Nat.succ_pos highCount⟩]
          simp)

end Auction
end AppliedModelingLib

namespace GHW01DigitalGoods
namespace Theorem93

open AppliedModelingLib.Auction

/--
Source-facing deterministic anonymous model for GHW Theorem 9.3. The final
field is the paper's erased-bid offer anonymity convention; Lemma 9.2 then
constructs the anonymous list-price certificate internally.
-/
structure PaperTheorem93AnonymousTruthfulDeterministicSourceModel
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  source_anonymity :
    PaperTheorem93ErasedBidOfferAnonymity
      (highValue := highValue) auctionFamily

/--
Source-facing deterministic anonymous model using the paper's global
set-of-bids relabeling convention: bidder slices with the same erased bid list
induce the same deterministic offer.
-/
structure PaperTheorem93AnonymousTruthfulRelabelingSourceModel
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  source_relabeling :
    PaperTheorem93ErasedBidOfferRelabelingAnonymity auctionFamily

/--
Primitive set-of-bids source model for GHW Theorem 9.3. The paper writes a
deterministic auction as mapping a set of bids to outcomes and, in Lemma 9.2,
studies the focused slice `A_i(B_i^x)`. The `focusedOutcome` field is that
anonymous erased-bid-multiset slice: `none` means rejection, and `some price`
means satisfied at that price.  Repeated bid values are retained, but the
source-facing field cannot inspect their presentation order or bidder labels.
-/
structure PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel
    (_highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  focusedOutcome : Multiset ℝ → ℝ → Option ℝ
  focusedOutcome_represents :
    ∀ {highCount lowCount : ℕ}
      (bids : TwoValueAgent highCount lowCount → ℝ)
      (i : TwoValueAgent highCount lowCount),
      deterministicAuctionOffer
          (auctionFamily highCount lowCount) bids i =
        focusedOutcome
          (Multiset.ofList (paper_theorem9_3_erased_report_list bids i))

/--
The paper's primitive focused set-of-bids semantics implies the weaker internal
erased-list relabeling used by the count proof: equal canonical erased lists
have equal multisets, so two such bidder slices use the same focused outcome
function.
-/
theorem
    paper_theorem9_3_erased_bid_offer_relabeling_anonymity_of_primitive_set_of_bids_source_model
    {highValue : ℕ}
    (model :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue) :
    PaperTheorem93ErasedBidOfferRelabelingAnonymity model.auctionFamily := by
  refine { offer_eq_of_erased := ?_ }
  intro highCount lowCount highCount' lowCount' bids bids' i j herased
  rw [model.focusedOutcome_represents bids i,
    model.focusedOutcome_represents bids' j,
    congrArg Multiset.ofList herased]

/--
The primitive focused set-of-bids source model supplies the relabeling source
model consumed by the Theorem 9.3 proof.
-/
noncomputable def
    paper_theorem9_3_anonymous_truthful_relabeling_source_model_of_primitive_set_of_bids_source_model
    {highValue : ℕ}
    (model :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue) :
    PaperTheorem93AnonymousTruthfulRelabelingSourceModel highValue where
  auctionFamily := model.auctionFamily
  truthful := model.truthful
  binary := model.binary
  individuallyRational := model.individuallyRational
  noPositiveTransfers := model.noPositiveTransfers
  source_relabeling :=
    paper_theorem9_3_erased_bid_offer_relabeling_anonymity_of_primitive_set_of_bids_source_model
      model

/--
The global erased-list relabeling source model implies the specialized source
model consumed by the existing Theorem 9.3 proof.
-/
noncomputable def
    paper_theorem9_3_anonymous_truthful_deterministic_source_model_of_relabeling_source_model
    {highValue : ℕ}
    (model :
      PaperTheorem93AnonymousTruthfulRelabelingSourceModel highValue) :
    PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue where
  auctionFamily := model.auctionFamily
  truthful := model.truthful
  binary := model.binary
  individuallyRational := model.individuallyRational
  noPositiveTransfers := model.noPositiveTransfers
  source_anonymity :=
    paper_theorem9_3_erased_bid_offer_anonymity_of_relabeling_anonymity
      model.source_relabeling

/--
Paper-local primitive erased-bid-list offer model for GHW Theorem 9.3. Instead
of assuming an already packaged auction family plus erased-list factorization,
the model starts from the paper-style anonymous offer rule itself.
-/
structure PrimitiveErasedBidOfferModel
    (_highValue : ℕ) where
  offerRule : List ℝ → ℝ → Option ℝ
  offer_truthful :
    ∀ erasedBids, DeterministicOfferTruthful (offerRule erasedBids)
  offer_feasible :
    ∀ erasedBids, DeterministicOfferFeasible (offerRule erasedBids)
  offer_price_nonnegative :
    ∀ erasedBids report price,
      offerRule erasedBids report = some price → 0 ≤ price

/--
Paper-local primitive anonymous list-price model for GHW Theorem 9.3. This is
closer to the paper's bid-independent convention than an arbitrary offer rule:
each bidder is offered a nonnegative price computed from the erased list of
other bids.
-/
structure PrimitiveErasedBidPriceModel
    (_highValue : ℕ) where
  priceRule : List ℝ → ℝ
  price_nonnegative : ∀ erasedBids, 0 ≤ priceRule erasedBids

/--
Every nonnegative anonymous erased-list price rule induces the primitive offer
source model: report at or above the price wins and pays that price, otherwise
the bidder is rejected.
-/
noncomputable def primitiveErasedBidOfferModelOfPriceModel
    {highValue : ℕ}
    (model : PrimitiveErasedBidPriceModel highValue) :
    PrimitiveErasedBidOfferModel highValue where
  offerRule := paper_theorem9_3_bid_list_price_offer model.priceRule
  offer_truthful := by
    intro erasedBids
    exact paper_theorem9_3_threshold_offer_truthful (model.priceRule erasedBids)
  offer_feasible := by
    intro erasedBids
    exact paper_theorem9_3_threshold_offer_feasible (model.priceRule erasedBids)
  offer_price_nonnegative := by
    intro erasedBids report offeredPrice hoff
    exact
      paper_theorem9_3_threshold_offer_noPositiveTransfers
        (model.price_nonnegative erasedBids) report offeredPrice hoff

/--
Paper-shaped anonymous deterministic source model for GHW Theorem 9.3. The
auction family is still represented in Lean by identity-aware finite bidder
types, but the deterministic offer to a bidder factors through the paper's
anonymous erased bid list. This is the set-of-bids convention used to transfer
Lemma 9.2's bidder-specific critical prices to a single erased-list price rule.
-/
structure AnonymousBidListOfferSourceModel
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  offerRule : List ℝ → ℝ → Option ℝ
  high_offer_factor :
    ∀ highCount lowCount, ∀ i : Fin highCount,
      deterministicAuctionOffer
          (auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount)
          (Sum.inl i) =
        offerRule
          (twoValueErasedBidList highValue (highCount - 1) lowCount)
  low_offer_factor :
    ∀ highCount lowCount, ∀ i : Fin lowCount,
      deterministicAuctionOffer
          (auctionFamily highCount lowCount)
          (twoValueBidProfile highValue highCount lowCount)
          (Sum.inr i) =
        offerRule
          (twoValueErasedBidList highValue highCount (lowCount - 1))

/--
Construct the paper-shaped erased-bid-list source model from the primitive
anonymous offer rule. The auction family, binary allocation, IR/NPT, and the
erased-list offer factorization are all derived by unfolding the offer auction.
-/
noncomputable def anonymousBidListOfferSourceModelOfPrimitiveErasedBidOfferModel
    {highValue : ℕ}
    (model : PrimitiveErasedBidOfferModel highValue) :
    AnonymousBidListOfferSourceModel highValue where
  auctionFamily :=
    paper_theorem9_3_bid_list_offer_auction model.offerRule
  truthful := by
    intro highCount lowCount
    exact
      paper_theorem9_3_bid_list_offer_auction_truthful
        model.offerRule model.offer_truthful
  binary := by
    intro highCount lowCount
    exact
      paper_theorem9_3_bid_list_offer_auction_binary
        model.offerRule highCount lowCount
  individuallyRational := by
    intro highCount lowCount
    exact
      paper_theorem9_3_bid_list_offer_auction_individuallyRational
        model.offerRule model.offer_feasible
  noPositiveTransfers := by
    intro highCount lowCount
    exact
      paper_theorem9_3_bid_list_offer_auction_noPositiveTransfers
        model.offerRule model.offer_price_nonnegative
  offerRule := model.offerRule
  high_offer_factor := by
    intro highCount lowCount i
    exact
      paper_theorem9_3_bid_list_offer_auction_offer_factor_high
        model.offerRule i
  low_offer_factor := by
    intro highCount lowCount i
    exact
      paper_theorem9_3_bid_list_offer_auction_offer_factor_low
        model.offerRule i

/--
The paper-shaped erased-bid-list offer model implies the anonymous offer
equality field used by the current Theorem 9.3 bridge.
-/
theorem erasedBidOfferAnonymityOfBidListOfferSourceModel
    {highValue : ℕ}
    (model : AnonymousBidListOfferSourceModel highValue) :
    PaperTheorem93ErasedBidOfferAnonymity
      (highValue := highValue) model.auctionFamily := by
  refine
    { high_offer_eq := ?_
      low_offer_eq := ?_ }
  · intro highCount lowCount i
    rw [model.high_offer_factor highCount lowCount i,
      model.high_offer_factor ((highCount - 1) + 1) lowCount
        ⟨0, Nat.succ_pos (highCount - 1)⟩]
    simp
  · intro highCount lowCount i
    rw [model.low_offer_factor highCount lowCount i,
      model.high_offer_factor (highCount + 1) (lowCount - 1)
        ⟨0, Nat.succ_pos highCount⟩]
    simp

/--
Construct the current deterministic anonymous source model from the paper's
erased-bid-list offer-factorization source model.
-/
noncomputable def anonymousTruthfulDeterministicSourceModelOfBidListOfferSourceModel
    {highValue : ℕ}
    (model : AnonymousBidListOfferSourceModel highValue) :
    PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue where
  auctionFamily := model.auctionFamily
  truthful := model.truthful
  binary := model.binary
  individuallyRational := model.individuallyRational
  noPositiveTransfers := model.noPositiveTransfers
  source_anonymity :=
    erasedBidOfferAnonymityOfBidListOfferSourceModel model

end Theorem93
end GHW01DigitalGoods

namespace AppliedModelingLib
namespace Auction

open GHW01DigitalGoods.Theorem93

/-- Representative first high bidder for the Section 9.3 erased-list bridge. -/
def paper_theorem9_3_representative_high_bidder
    (erasedHigh erasedLow : ℕ) :
    TwoValueAgent (erasedHigh + 1) erasedLow :=
  Sum.inl ⟨0, Nat.succ_pos erasedHigh⟩

/--
Canonical list-price rule obtained from Lemma 9.2. On a binary erased list,
choose the nonnegative critical price of the first high-bid representative
slice with that erased list.
-/
noncomputable def paper_theorem9_3_representative_erased_count_price
    (highValue : ℕ)
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (erasedHigh erasedLow : ℕ) : ℝ :=
  Classical.choose
    (paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
      (auctionFamily (erasedHigh + 1) erasedLow)
      (htruth (erasedHigh + 1) erasedLow)
      (hIR (erasedHigh + 1) erasedLow)
      (hNPT (erasedHigh + 1) erasedLow)
      (hbinary (erasedHigh + 1) erasedLow)
      (twoValueBidProfile highValue (erasedHigh + 1) erasedLow)
      (paper_theorem9_3_representative_high_bidder erasedHigh erasedLow))

noncomputable def paper_theorem9_3_representative_erased_bid_price
    (highValue : ℕ)
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers) :
    List ℝ → ℝ :=
  fun bids =>
    let highCount := twoValueHighCountInList highValue bids
    let lowCount := twoValueLowCountInList highValue bids
    paper_theorem9_3_representative_erased_count_price
      highValue auctionFamily htruth hbinary hIR hNPT highCount lowCount

/--
The count-indexed representative price is the nonnegative threshold selected
by Lemma 9.2 for the representative high-bidder slice.
-/
theorem paper_theorem9_3_representative_erased_count_price_spec
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (erasedHigh erasedLow : ℕ) :
    0 ≤
        paper_theorem9_3_representative_erased_count_price
          highValue auctionFamily htruth hbinary hIR hNPT erasedHigh erasedLow ∧
      DeterministicOfferThresholdDominates
        (deterministicAuctionOffer
          (auctionFamily (erasedHigh + 1) erasedLow)
          (twoValueBidProfile highValue (erasedHigh + 1) erasedLow)
          (paper_theorem9_3_representative_high_bidder erasedHigh erasedLow))
        (paper_theorem9_3_representative_erased_count_price
          highValue auctionFamily htruth hbinary hIR hNPT erasedHigh erasedLow) := by
  unfold paper_theorem9_3_representative_erased_count_price
  exact
    (Classical.choose_spec
      (paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
        (auctionFamily (erasedHigh + 1) erasedLow)
        (htruth (erasedHigh + 1) erasedLow)
        (hIR (erasedHigh + 1) erasedLow)
        (hNPT (erasedHigh + 1) erasedLow)
        (hbinary (erasedHigh + 1) erasedLow)
        (twoValueBidProfile highValue (erasedHigh + 1) erasedLow)
        (paper_theorem9_3_representative_high_bidder erasedHigh erasedLow)))

/--
The representative erased-bid price selected above is exactly a nonnegative
threshold dominating the representative deterministic offer slice.
-/
theorem paper_theorem9_3_representative_erased_bid_price_spec
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    {erasedHigh erasedLow : ℕ}
    (hhigh_ne_one : (highValue : ℝ) ≠ 1) :
    0 ≤
        paper_theorem9_3_representative_erased_bid_price
          highValue auctionFamily htruth hbinary hIR hNPT
          (twoValueErasedBidList highValue erasedHigh erasedLow) ∧
      DeterministicOfferThresholdDominates
        (deterministicAuctionOffer
          (auctionFamily (erasedHigh + 1) erasedLow)
          (twoValueBidProfile highValue (erasedHigh + 1) erasedLow)
          (paper_theorem9_3_representative_high_bidder erasedHigh erasedLow))
        (paper_theorem9_3_representative_erased_bid_price
          highValue auctionFamily htruth hbinary hIR hNPT
          (twoValueErasedBidList highValue erasedHigh erasedLow)) := by
  have hspec :=
    paper_theorem9_3_representative_erased_count_price_spec
      (highValue := highValue) auctionFamily htruth hbinary hIR hNPT
      erasedHigh erasedLow
  simpa [paper_theorem9_3_representative_erased_bid_price,
    twoValueErasedBidList_highCount hhigh_ne_one,
    twoValueErasedBidList_lowCount hhigh_ne_one] using hspec

/--
The price rule selected by Lemma 9.2 from a deterministic anonymous source
model is a primitive nonnegative erased-bid-list price rule. This exposes the
constructed paper price semantics without replacing the theorem about the
original auction family's revenue.
-/
noncomputable def
    paper_theorem9_3_primitive_bid_list_price_source_model_of_source_model
    {highValue : ℕ}
    (sourceModel :
      PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue) :
    GHW01DigitalGoods.Theorem93.PrimitiveErasedBidPriceModel highValue where
  priceRule :=
    paper_theorem9_3_representative_erased_bid_price
      highValue sourceModel.auctionFamily sourceModel.truthful
      sourceModel.binary sourceModel.individuallyRational
      sourceModel.noPositiveTransfers
  price_nonnegative := by
    intro erasedBids
    exact
      (paper_theorem9_3_representative_erased_count_price_spec
        sourceModel.auctionFamily sourceModel.truthful sourceModel.binary
        sourceModel.individuallyRational sourceModel.noPositiveTransfers
        (twoValueHighCountInList highValue erasedBids)
        (twoValueLowCountInList highValue erasedBids)).1

/--
Paper model for the final GHW Theorem 9.3 deterministic lower bound on binary
inputs. The fields make the paper's anonymous deterministic convention explicit:
after erasing a bidder's own bid, a single anonymous list-price rule supplies a
nonnegative critical price that dominates that bidder's deterministic offer
slice.
-/
structure PaperTheorem93AnonymousTruthfulDeterministicModel
    (highValue : ℕ) where
  auctionFamily :
    ∀ highCount lowCount,
      DigitalGoodsAuction (TwoValueAgent highCount lowCount)
  priceRule : List ℝ → ℝ
  truthful :
    ∀ highCount lowCount,
      paper_digital_goods_truthful (auctionFamily highCount lowCount)
  binary :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).BinaryAllocation
  individuallyRational :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).IndividuallyRational
  noPositiveTransfers :
    ∀ highCount lowCount,
      (auctionFamily highCount lowCount).NoPositiveTransfers
  high_slice :
    ∀ highCount lowCount, ∀ i : Fin highCount,
      0 ≤ priceRule (twoValueErasedBidList highValue (highCount - 1) lowCount) ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer
            (auctionFamily highCount lowCount)
            (twoValueBidProfile highValue highCount lowCount)
            (Sum.inl i))
          (priceRule
            (twoValueErasedBidList highValue (highCount - 1) lowCount))
  low_slice :
    ∀ highCount lowCount, ∀ i : Fin lowCount,
      0 ≤ priceRule (twoValueErasedBidList highValue highCount (lowCount - 1)) ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer
            (auctionFamily highCount lowCount)
            (twoValueBidProfile highValue highCount lowCount)
            (Sum.inr i))
          (priceRule
            (twoValueErasedBidList highValue highCount (lowCount - 1)))

/--
Construct the Theorem 9.3 anonymous deterministic model from primitive
truthfulness/IR/NPT/binary assumptions plus erased-bid offer anonymity. Lemma
9.2 supplies the representative critical prices; anonymity transfers those
critical-price slices to every bidder with the same erased bid list.
-/
noncomputable def
    paper_theorem9_3_anonymous_truthful_deterministic_model_of_erased_bid_offer_anonymity
    {highValue : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (hhigh_ne_one : (highValue : ℝ) ≠ 1)
    (hanonymous :
      PaperTheorem93ErasedBidOfferAnonymity
        (highValue := highValue) auctionFamily) :
    PaperTheorem93AnonymousTruthfulDeterministicModel highValue where
  auctionFamily := auctionFamily
  priceRule :=
    paper_theorem9_3_representative_erased_bid_price
      highValue auctionFamily htruth hbinary hIR hNPT
  truthful := htruth
  binary := hbinary
  individuallyRational := hIR
  noPositiveTransfers := hNPT
  high_slice := by
    intro highCount lowCount i
    have hspec :=
      paper_theorem9_3_representative_erased_bid_price_spec
        auctionFamily htruth hbinary hIR hNPT
        (erasedHigh := highCount - 1) (erasedLow := lowCount)
        hhigh_ne_one
    constructor
    · exact hspec.1
    · rw [hanonymous.high_offer_eq highCount lowCount i]
      exact hspec.2
  low_slice := by
    intro highCount lowCount i
    have hspec :=
      paper_theorem9_3_representative_erased_bid_price_spec
        auctionFamily htruth hbinary hIR hNPT
        (erasedHigh := highCount) (erasedLow := lowCount - 1)
        hhigh_ne_one
    constructor
    · exact hspec.1
    · rw [hanonymous.low_offer_eq highCount lowCount i]
      exact hspec.2

/--
Construct the internal anonymous list-price model from the source-facing
Theorem 9.3 deterministic anonymous model.
-/
noncomputable def
    paper_theorem9_3_anonymous_truthful_deterministic_model_of_source_model
    {highValue : ℕ}
    (sourceModel :
      PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue)
    (hhigh_ne_one : (highValue : ℝ) ≠ 1) :
    PaperTheorem93AnonymousTruthfulDeterministicModel highValue :=
  paper_theorem9_3_anonymous_truthful_deterministic_model_of_erased_bid_offer_anonymity
    sourceModel.auctionFamily sourceModel.truthful sourceModel.binary
    sourceModel.individuallyRational sourceModel.noPositiveTransfers
    hhigh_ne_one sourceModel.source_anonymity

/--
The anonymous truthful deterministic paper model supplies the slice certificate
used by the Section 9.3 lower-bound theorem.
-/
theorem paper_theorem9_3_binary_anonymous_slice_upper_bound_of_truthful_deterministic_model
    {highValue : ℕ}
    (model : PaperTheorem93AnonymousTruthfulDeterministicModel highValue) :
    paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound
      model.auctionFamily model.priceRule highValue := by
  intro highCount lowCount
  constructor
  · intro i
    simpa [paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound,
      paper_theorem9_3_binary_count_threshold_slice_upper_bound,
      twoValueListBidIndependentThresholdPrice] using
      model.high_slice highCount lowCount i
  · intro i
    simpa [paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound,
      paper_theorem9_3_binary_count_threshold_slice_upper_bound,
      twoValueListBidIndependentThresholdPrice] using
      model.low_slice highCount lowCount i

/--
GHW Theorem 9.3 final paper-model form. For every anonymous truthful
deterministic binary digital-goods auction family satisfying the paper's
erased-bid critical-price convention, and every `h >= 2` and positive
`alpha`, there is a binary input with `R/F <= 1/h` and `alpha * h <= F`.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model
    {highValue alpha : ℕ}
    (model : PaperTheorem93AnonymousTruthfulDeterministicModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (model.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_slice_upper_bound
      model.auctionFamily model.priceRule model.truthful model.binary
      model.individuallyRational model.noPositiveTransfers
      (paper_theorem9_3_binary_anonymous_slice_upper_bound_of_truthful_deterministic_model
        model)
      hhigh_ge_two halpha_pos

/--
Attained form of the final deterministic truthful paper model.  The proof uses
the same caller-supplied anonymous slice model and only retains the positive
high-count fact from the finite Theorem 9.1 construction.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model_attained
    {highValue alpha : ℕ}
    (model : PaperTheorem93AnonymousTruthfulDeterministicModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (model.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hloser :
      ∀ highCount lowCount,
        (model.auctionFamily highCount lowCount).LosersPayZero := by
    intro highCount lowCount
    exact
      DigitalGoodsAuction.losersPayZero_of_individuallyRational_noPositiveTransfers
        (model.auctionFamily highCount lowCount)
        (model.individuallyRational highCount lowCount)
        (model.noPositiveTransfers highCount lowCount)
  have hpay :=
    paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound_of_slice_upper_bound
      model.auctionFamily model.priceRule highValue model.binary hloser
      (paper_theorem9_3_binary_anonymous_slice_upper_bound_of_truthful_deterministic_model
        model)
  have hupper :=
    paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_payment_upper_bound
      model.auctionFamily model.priceRule highValue hpay
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound_attained
      (fun highCount lowCount =>
        (model.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount))
      model.priceRule hupper hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 from primitive deterministic truthful-auction assumptions and
erased-bid offer anonymity. The anonymous list-price certificate is constructed
internally from Lemma 9.2 rather than assumed as a model field.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_erased_bid_offer_anonymity
    {highValue alpha : ℕ}
    (auctionFamily :
      ∀ highCount lowCount,
        DigitalGoodsAuction (TwoValueAgent highCount lowCount))
    (htruth :
      ∀ highCount lowCount,
        paper_digital_goods_truthful (auctionFamily highCount lowCount))
    (hbinary :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).BinaryAllocation)
    (hIR :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).IndividuallyRational)
    (hNPT :
      ∀ highCount lowCount,
        (auctionFamily highCount lowCount).NoPositiveTransfers)
    (hanonymous :
      PaperTheorem93ErasedBidOfferAnonymity
        (highValue := highValue) auctionFamily)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hhigh_ne_one : (highValue : ℝ) ≠ 1 := by
    have hgt : (1 : ℝ) < (highValue : ℝ) := by
      exact_mod_cast (Nat.lt_of_succ_le hhigh_ge_two)
    exact ne_of_gt hgt
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model
      (paper_theorem9_3_anonymous_truthful_deterministic_model_of_erased_bid_offer_anonymity
        auctionFamily htruth hbinary hIR hNPT hhigh_ne_one hanonymous)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form. The source model carries deterministic
truthfulness, IR/NPT, binary allocation, and erased-bid offer anonymity; Lemma
9.2 constructs the list-price certificate internally.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hhigh_ne_one : (highValue : ℝ) ≠ 1 := by
    have hhigh_gt_one_nat : 1 < highValue :=
      lt_of_lt_of_le (by decide : 1 < 2) hhigh_ge_two
    have hhigh_gt_one : (1 : ℝ) < highValue := by
      exact_mod_cast hhigh_gt_one_nat
    exact ne_of_gt hhigh_gt_one
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model
      (paper_theorem9_3_anonymous_truthful_deterministic_model_of_source_model
        sourceModel hhigh_ne_one)
      hhigh_ge_two halpha_pos

/-- Attained form of the source-model Theorem 9.3 bridge. -/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_source_model_attained
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93AnonymousTruthfulDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hhigh_ne_one : (highValue : ℝ) ≠ 1 := by
    have hgt : (1 : ℝ) < (highValue : ℝ) := by
      exact_mod_cast (Nat.lt_of_succ_le hhigh_ge_two)
    exact ne_of_gt hgt
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model_attained
      (paper_theorem9_3_anonymous_truthful_deterministic_model_of_source_model
        sourceModel hhigh_ne_one)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form using the paper's global erased-list
relabeling convention. The specialized erased-bid offer anonymity bridge is
derived internally before Lemma 9.2 constructs the representative prices.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_relabeling_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93AnonymousTruthfulRelabelingSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_source_model
      (paper_theorem9_3_anonymous_truthful_deterministic_source_model_of_relabeling_source_model
        sourceModel)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form using the paper's primitive set-of-bids
focused-outcome convention. The global erased-list relabeling bridge is
derived internally from the focused outcome representation before Lemma 9.2
constructs representative prices.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_relabeling_source_model
      (paper_theorem9_3_anonymous_truthful_relabeling_source_model_of_primitive_set_of_bids_source_model
        sourceModel)
      hhigh_ge_two halpha_pos

/--
Attained primitive set-of-bids source-model form of Theorem 9.3.  The focused
outcome representation remains caller-supplied; only the erased-list
relabeling and the attained adversarial witness are derived internally.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model_attained
    {highValue alpha : ℕ}
    (sourceModel :
      PaperTheorem93PrimitiveSetOfBidsDeterministicSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      0 < highCount ∧
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_source_model_attained
      (paper_theorem9_3_anonymous_truthful_deterministic_source_model_of_relabeling_source_model
        (paper_theorem9_3_anonymous_truthful_relabeling_source_model_of_primitive_set_of_bids_source_model
          sourceModel))
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form using the paper's erased-bid-list
offer-factorization convention. The erased-bid offer anonymity bridge is
derived internally before Lemma 9.2 constructs the representative prices.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_bid_list_offer_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      GHW01DigitalGoods.Theorem93.AnonymousBidListOfferSourceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (sourceModel.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_source_model
      (GHW01DigitalGoods.Theorem93.anonymousTruthfulDeterministicSourceModelOfBidListOfferSourceModel
        sourceModel)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form from the primitive anonymous erased-bid-list
offer rule. This is the strongest current source-level bridge: the auction
family and erased-list factorization certificate are constructed internally.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_bid_list_offer_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      GHW01DigitalGoods.Theorem93.PrimitiveErasedBidOfferModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      ((paper_theorem9_3_bid_list_offer_auction
          sourceModel.offerRule highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount)) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_bid_list_offer_source_model
      (GHW01DigitalGoods.Theorem93.anonymousBidListOfferSourceModelOfPrimitiveErasedBidOfferModel
        sourceModel)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 source-model form from the paper's primitive anonymous
erased-bid-list price rule. The threshold offer semantics, truthfulness,
IR/NPT, binary allocation, and erased-list offer factorization are all
constructed internally from the nonnegative list-price rule.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_bid_list_price_source_model
    {highValue alpha : ℕ}
    (sourceModel :
      GHW01DigitalGoods.Theorem93.PrimitiveErasedBidPriceModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      ((paper_theorem9_3_bid_list_price_auction
          sourceModel.priceRule highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount)) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_bid_list_offer_source_model
      (GHW01DigitalGoods.Theorem93.primitiveErasedBidOfferModelOfPriceModel
        sourceModel)
      hhigh_ge_two halpha_pos

/--
Paper-facing certificate for the final Section 9.3 bridge. In the paper's
anonymous deterministic model, Lemma 9.2 is intended to provide an erased-bid
price rule whose binary revenue dominates the actual deterministic truthful
auction revenue.
-/
structure PaperTheorem93AnonymousDeterministicTruthfulCertificate
    (highValue : ℕ) where
  auctionRevenue : ℕ → ℕ → ℝ
  priceRule : List ℝ → ℝ
  revenue_upper_bound :
    paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound
      auctionRevenue priceRule highValue

/--
GHW Theorem 9.3 certificate form. This is the final lower-bound step once the
paper's anonymous deterministic truthful auction has been reduced to a binary
erased-bid price-rule certificate.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93AnonymousDeterministicTruthfulCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) * certificate.auctionRevenue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_upper_bound
      certificate.auctionRevenue certificate.priceRule
      certificate.revenue_upper_bound hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 certificate ratio form: for every `h >= 2` and positive
constant `alpha`, the certified deterministic truthful auction has a binary
input with `R/F <= 1/h` and `alpha * h <= F`.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_certificate
    {highValue alpha : ℕ}
    (certificate :
      PaperTheorem93AnonymousDeterministicTruthfulCertificate highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      certificate.auctionRevenue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound
      certificate.auctionRevenue certificate.priceRule
      certificate.revenue_upper_bound hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 count-threshold route through the anonymous bid-list interface.
This theorem closes the concrete representation bridge used by the binary
lower-bound proof: the anonymous erased-list rule obtained by counting high and
low bids has exactly the same revenue as the count-threshold model.
-/
theorem paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_via_anonymous_bid_list
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            thresholdPrice highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hhigh_ne_one : (highValue : ℝ) ≠ 1 := by
    have hgt : (1 : ℝ) < (highValue : ℝ) := by
      exact_mod_cast (Nat.lt_of_succ_le hhigh_ge_two)
    exact ne_of_gt hgt
  exact
    paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_representation
      (fun highCount lowCount =>
        twoValueBidIndependentPriceRevenue
          thresholdPrice highValue highCount lowCount)
      (twoValueCountListPriceRule thresholdPrice highValue)
      (paper_theorem9_3_count_threshold_binary_anonymous_bid_independent_revenue_representation
        thresholdPrice hhigh_ne_one)
      hhigh_ge_two halpha_pos

/--
GHW Theorem 9.3 count-threshold ratio form through the anonymous bid-list
interface. This is the paper's `R/F = O(1/h)` endpoint specialized to the
closed count-threshold binary representation.
-/
theorem paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_via_anonymous_bid_list
    (thresholdPrice : ℕ → ℕ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      twoValueBidIndependentPriceRevenue
          thresholdPrice highValue highCount lowCount /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  have hhigh_ne_one : (highValue : ℝ) ≠ 1 := by
    have hgt : (1 : ℝ) < (highValue : ℝ) := by
      exact_mod_cast (Nat.lt_of_succ_le hhigh_ge_two)
    exact ne_of_gt hgt
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_representation
      (fun highCount lowCount =>
        twoValueBidIndependentPriceRevenue
          thresholdPrice highValue highCount lowCount)
      (twoValueCountListPriceRule thresholdPrice highValue)
      (paper_theorem9_3_count_threshold_binary_anonymous_bid_independent_revenue_representation
        thresholdPrice hhigh_ne_one)
      hhigh_ge_two halpha_pos

end Auction
end AppliedModelingLib
