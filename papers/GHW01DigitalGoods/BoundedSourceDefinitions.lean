import GHW01DigitalGoods.BoundedSupply
import GHW01DigitalGoods.RandomSamplingDirectional
import GHW01DigitalGoods.SourceDefinitions
import GHW01DigitalGoods.WeightedPairingSourceModel
import AppliedModelingLib.Foundations.Probability.FairCoin
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Source-facing auction definitions for GHW01

This file records the mechanism vocabulary introduced after the paper's core
fixed-price definitions.  It keeps the exact-half auction law distinct from
the independent fair-coin law used only for analysis, and exposes every
integer-capacity convention in the bounded-supply constructions.
-/

namespace GHW01DigitalGoods
namespace SourceDefinitions

open AppliedModelingLib
open AppliedModelingLib.Auction
open MeasureTheory

noncomputable section

/-! ## Canonical value-level optimal thresholds -/

/-- Candidate objective at a price value.  Unlike an Agent-indexed argmax,
this depends only on the multiset of reported values. -/
def candidateFixedPriceRevenueAtPrice
    {Agent : Type*} [Fintype Agent]
    (bids : Agent → ℝ) (minWinners : ℕ) (price : ℝ) : ℝ :=
  if 0 ≤ price ∧ minWinners ≤ saleCount bids price then
    singlePriceRevenue bids price
  else
    0

/-- The finite value-level set of all prices attaining the unlimited-supply
candidate benchmark. -/
def optimalPriceMaximizers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (minWinners : ℕ) : Finset ℝ :=
  (finiteCandidatePriceSet bids).filter fun price =>
    candidateFixedPriceRevenueAtPrice bids minWinners price =
      finiteCandidateFixedPriceBenchmark bids minWinners

theorem optimalPriceMaximizers_nonempty
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (minWinners : ℕ) :
    (optimalPriceMaximizers bids minWinners).Nonempty := by
  classical
  let i := finiteCandidateBenchmarkBidder bids minWinners
  have hselected :
      finiteCandidateFixedPriceBenchmark bids minWinners =
        candidateFixedPriceRevenue bids minWinners i := by
    simpa [i] using
      finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
        bids minWinners
  refine ⟨bids i, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · simp [finiteCandidatePriceSet]
  · simpa [candidateFixedPriceRevenueAtPrice,
      candidateFixedPriceRevenue] using hselected.symm

/-- Canonical `opt`: among all value-level maximizing thresholds, choose the
largest price.  Both the candidate set and this price-order tie break are
invariant under bidder renaming. -/
def canonicalOptimalThreshold
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (optimalPriceMaximizers bids minWinners).max'
    (optimalPriceMaximizers_nonempty bids minWinners)

theorem canonicalOptimalThreshold_spec
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (minWinners : ℕ) :
    canonicalOptimalThreshold bids minWinners ∈ finiteCandidatePriceSet bids ∧
      candidateFixedPriceRevenueAtPrice bids minWinners
          (canonicalOptimalThreshold bids minWinners) =
        finiteCandidateFixedPriceBenchmark bids minWinners := by
  have hmem := Finset.max'_mem (optimalPriceMaximizers bids minWinners)
    (optimalPriceMaximizers_nonempty bids minWinners)
  exact Finset.mem_filter.mp hmem

/-- Bounded-supply candidate objective at a price value. -/
def boundedCandidateRevenueAtPrice
    {Agent : Type*} [Fintype Agent]
    (bids : Agent → ℝ) (capacity : ℕ) (price : ℝ) : ℝ :=
  if 0 ≤ price then
    boundedSupplySinglePriceRevenue bids capacity price
  else
    0

/-- The value-level set of thresholds attaining `F_k`. -/
def boundedOptimalPriceMaximizers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) : Finset ℝ :=
  (finiteCandidatePriceSet bids).filter fun price =>
    boundedCandidateRevenueAtPrice bids capacity price =
      boundedSupplyFixedPriceBenchmark bids capacity

theorem boundedOptimalPriceMaximizers_nonempty
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) :
    (boundedOptimalPriceMaximizers bids capacity).Nonempty := by
  classical
  let i := boundedSupplyBenchmarkBidder bids capacity
  have hselected :
      boundedSupplyFixedPriceBenchmark bids capacity =
        candidateBoundedSupplyRevenue bids capacity i := by
    simpa [i] using
      (Classical.choose_spec
        (exists_boundedSupplyBenchmarkBidder bids capacity))
  refine ⟨bids i, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · simp [finiteCandidatePriceSet]
  · simpa [boundedCandidateRevenueAtPrice,
      candidateBoundedSupplyRevenue] using hselected.symm

/-- Canonical `opt_k`: choose the largest value-level threshold attaining
`F_k`.  This removes Agent-indexed choice from every source-facing wrapper. -/
def canonicalBoundedOptimalThreshold
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) : ℝ :=
  (boundedOptimalPriceMaximizers bids capacity).max'
    (boundedOptimalPriceMaximizers_nonempty bids capacity)

theorem canonicalBoundedOptimalThreshold_spec
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) :
    canonicalBoundedOptimalThreshold bids capacity ∈ finiteCandidatePriceSet bids ∧
      boundedCandidateRevenueAtPrice bids capacity
          (canonicalBoundedOptimalThreshold bids capacity) =
        boundedSupplyFixedPriceBenchmark bids capacity := by
  have hmem := Finset.max'_mem (boundedOptimalPriceMaximizers bids capacity)
    (boundedOptimalPriceMaximizers_nonempty bids capacity)
  exact Finset.mem_filter.mp hmem

theorem canonicalBoundedOptimalThreshold_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : ℕ) :
    0 ≤ canonicalBoundedOptimalThreshold bids capacity := by
  classical
  by_cases hbenchmark : boundedSupplyFixedPriceBenchmark bids capacity = 0
  · have hzero : 0 ∈ boundedOptimalPriceMaximizers bids capacity := by
      simp [boundedOptimalPriceMaximizers, finiteCandidatePriceSet,
        boundedCandidateRevenueAtPrice, hbenchmark,
        boundedSupplySinglePriceRevenue]
    exact Finset.le_max' (boundedOptimalPriceMaximizers bids capacity) 0 hzero
  · by_contra hnot
    have hnegative : ¬ 0 ≤ canonicalBoundedOptimalThreshold bids capacity :=
      hnot
    have hspec := (canonicalBoundedOptimalThreshold_spec bids capacity).2
    simp [boundedCandidateRevenueAtPrice, hnegative] at hspec
    exact hbenchmark hspec.symm

/-! ## Optimal thresholds on an actual bidder subset -/

/-- Compute the source threshold `opt(B)` on the bidders in `sample` itself.
No dummy values for bidders outside the sample enter the optimization. -/
def optimalThresholdOnFinset
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (hnonempty : sample.Nonempty)
    (bids : Agent → ℝ) : ℝ := by
  letI : Nonempty {i // i ∈ sample} :=
    Finset.nonempty_coe_sort.mpr hnonempty
  exact GHW01DigitalGoods.SourceDefinitions.optimalThreshold
    (fun i : {i // i ∈ sample} => bids i.1)

/-- Compute the canonical bounded threshold `opt_k(B)` on the bidders in
`sample` itself, rather than on a full profile padded outside `sample`. -/
def boundedOptimalThresholdOnFinset
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (hnonempty : sample.Nonempty)
    (bids : Agent → ℝ) (capacity : ℕ) : ℝ := by
  letI : Nonempty {i // i ∈ sample} :=
    Finset.nonempty_coe_sort.mpr hnonempty
  exact canonicalBoundedOptimalThreshold
    (fun i : {i // i ∈ sample} => bids i.1) capacity

/-! ## Random-sampling mechanisms (source lines 410--422) -/

/-- The multiset of reported bid values carried by a sampled bidder set. -/
def sampleBidMultiset {Agent : Type*}
    (sample : Finset Agent) (bids : Agent → ℝ) : Multiset ℝ :=
  sample.1.map bids

/-- Source randomization data.  Because `sampleLaw` is fixed before a bid
profile is supplied, the sampled bidder set is independent of bid values.
The threshold function returns both its price and the source's visible weak or
strict boundary convention. -/
structure RandomSamplingPlan (Agent : Type*) where
  sampleLaw : PMF (Finset Agent)
  threshold : Multiset ℝ → ThresholdOffer

/-- A realized random-sampling auction for an arbitrary source threshold
function `f`: the sampled bidders determine one price and are rejected, while
every nonsampled bidder is offered that price. -/
def randomSamplingAuction
    {Agent : Type*} [DecidableEq Agent]
    (sample : Finset Agent) (f : Multiset ℝ → ThresholdOffer) :
    DigitalGoodsAuction Agent := by
  classical
  exact
    { allocation := fun bids i =>
        if i ∈ sample then 0
        else if accepts (f (sampleBidMultiset sample bids)) (bids i) then 1 else 0
      payment := fun bids i =>
        if i ∈ sample then 0
        else if accepts (f (sampleBidMultiset sample bids)) (bids i) then
          (f (sampleBidMultiset sample bids)).price
        else 0 }

/-- A realization of a source random-sampling plan at a sampled bidder set. -/
def RandomSamplingPlan.directionalRealization
    {Agent : Type*} [DecidableEq Agent]
    (plan : RandomSamplingPlan Agent) (sample : Finset Agent) :
    DigitalGoodsAuction Agent :=
  randomSamplingAuction sample plan.threshold

/-- The source dual-price modification: each half is offered the threshold
computed from the other half.  Thus the two sides may face different prices. -/
def dualPriceRandomSamplingAuction
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sample : Finset Agent) (f : Multiset ℝ → ThresholdOffer) :
    DigitalGoodsAuction Agent := by
  classical
  exact
    { allocation := fun bids i =>
        let offer := if i ∈ sample then
          f (sampleBidMultiset ((Finset.univ : Finset Agent) \ sample) bids)
        else
          f (sampleBidMultiset sample bids)
        if accepts offer (bids i) then 1 else 0
      payment := fun bids i =>
        let offer := if i ∈ sample then
          f (sampleBidMultiset ((Finset.univ : Finset Agent) \ sample) bids)
        else
          f (sampleBidMultiset sample bids)
        if accepts offer (bids i) then offer.price else 0 }

/-- The dual-price realization of the same bid-independent sampling plan. -/
def RandomSamplingPlan.dualPriceRealization
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (plan : RandomSamplingPlan Agent) (sample : Finset Agent) :
    DigitalGoodsAuction Agent :=
  dualPriceRandomSamplingAuction sample plan.threshold

/-- Convert a realized binary digital-goods mechanism into the source's
winner-set-and-sale-price outcome at a fixed bid profile. -/
def realizedAuctionOutcome
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (auction : DigitalGoodsAuction Agent) (bids : Agent → ℝ) :
    AuctionOutcome Agent := by
  classical
  exact
    { winners := (Finset.univ : Finset Agent).filter fun i =>
        auction.allocation bids i = 1
      salePrice := auction.payment bids }

/-- The actual randomized directional mechanism: for each bid profile, push
the bid-independent sample law forward to the resulting source outcomes. -/
def RandomSamplingPlan.directionalOutcomeLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (plan : RandomSamplingPlan Agent) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  PMF.map
    (fun sample => realizedAuctionOutcome
      (plan.directionalRealization sample) bids)
    plan.sampleLaw

/-- The actual randomized dual-price mechanism, as an outcome law for every
bid profile. -/
def RandomSamplingPlan.dualPriceOutcomeLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (plan : RandomSamplingPlan Agent) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  PMF.map
    (fun sample => realizedAuctionOutcome
      (plan.dualPriceRealization sample) bids)
    plan.sampleLaw

/-! ## Optimal-threshold half sampling (source lines 455--469) -/

/-- The source's auction law: a uniformly chosen subset of exactly half of
the bidders.  The equality premise records `n = 2m` in the type rather than
silently replacing the source auction by independent sampling. -/
def exactHalfSampleLaw
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ)
    (_hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    PMF (FixedSizeSampleSpace Agent sampleSize) :=
  uniformFixedSizeSampleLaw sampleSize (by omega)

/-- Every exact-half realization has a nonempty sample on the visible source
domain `0 < m`. -/
theorem exactHalfSample_nonempty
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    {sampleSize : ℕ} (hsample_pos : 0 < sampleSize)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    sample.1.Nonempty := by
  apply Finset.card_pos.mp
  have hcard : sample.1.card = sampleSize :=
    (Finset.mem_powersetCard.mp sample.2).2
  simpa [hcard] using hsample_pos

/-- Under `n = 2m` and `0 < m`, the market complement is also nonempty. -/
theorem exactHalfMarket_nonempty
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    {sampleSize : ℕ} (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    ((Finset.univ : Finset Agent) \ sample.1).Nonempty := by
  apply Finset.card_pos.mp
  have hsubset : sample.1 ⊆ (Finset.univ : Finset Agent) := by simp
  have hsample_card : sample.1.card = sampleSize :=
    (Finset.mem_powersetCard.mp sample.2).2
  rw [Finset.card_sdiff_of_subset hsubset, Finset.card_univ,
    hsample_card, hhalf]
  omega

/-- Directional optimal-threshold realization with the source's boundary
choice made explicit.  Sample bidders are rejected; market bidders face the
nonnegative candidate-optimal threshold computed on the sample. -/
def directionalOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sample : Finset Agent) (hsample : sample.Nonempty)
    (boundary : ThresholdBoundary) : DigitalGoodsAuction Agent := by
  classical
  exact
    { allocation := fun bids i =>
        let price := optimalThresholdOnFinset sample hsample bids
        if i ∈ sample then 0
        else if accepts ⟨price, boundary⟩ (bids i) then 1 else 0
      payment := fun bids i =>
        let price := optimalThresholdOnFinset sample hsample bids
        if i ∈ sample then 0
        else if accepts ⟨price, boundary⟩ (bids i) then price else 0 }

/-- One realized source random-sampling optimal-threshold auction under an
exact half sample.  The checked implementation computes `opt` on the sampled
side and offers it only to the complementary side. -/
def exactHalfOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sampleSize : ℕ)
    (hsample_pos : 0 < sampleSize)
    (_hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (boundary : ThresholdBoundary)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    DigitalGoodsAuction Agent :=
  directionalOptimalThresholdAuction
    sample.1 (exactHalfSample_nonempty hsample_pos sample) boundary

/-- The source's exact-half optimal-threshold auction as an actual PMF of
auction outcomes for each bid profile. -/
def exactHalfOptimalThresholdOutcomeLaw
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (boundary : ThresholdBoundary) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  PMF.map
    (fun sample => realizedAuctionOutcome
      (exactHalfOptimalThresholdAuction sampleSize hsample_pos hhalf
        boundary sample) bids)
    (exactHalfSampleLaw Agent sampleSize hsample_pos hhalf)

/-- The separate analysis model from source lines 466--469: every bidder is
placed in the sample independently with probability `1/2`.  This is not the
exact-half auction law above. -/
def independentHalfSamplingAnalysisLaw (Agent : Type*) :
    Measure (Agent → Bool) :=
  FairCoin.productMeasure Agent

/-! ## Weighted pairing (source lines 489--508 and 621--623) -/

/-- The source weighted-pairing probability of offering bidder `j`'s bid to
bidder `i`.  `WeightedPairingSourceProfile` is the visible domain on which
these weights form a probability distribution. -/
def weightedPairingSelectionProbability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (i j : Agent) : ℝ :=
  weightedPairingOfferProbability bids i j

/-- Operational expected revenue of the weighted-pairing auction on a source
profile.  The profile argument exposes nonnegative bids and positive
other-bid mass instead of hiding the sampling-law denominator condition. -/
def weightedPairingAuctionRevenue
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) : ℝ :=
  weightedPairingSourceOperationalExpectedRevenue bids source

/-- The paper's notation `W` for weighted-pairing expected revenue. -/
def weightedPairingW
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) : ℝ :=
  weightedPairingAuctionRevenue bids source

/-- The source offer distribution for bidder `i`. -/
def weightedPairingOfferLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) : PMF Agent :=
  PMF.ofFintype
    (fun j => ENNReal.ofReal (weightedPairingOfferProbability bids i j))
    (by
      have hnonneg :
          ∀ j ∈ (Finset.univ : Finset Agent),
            0 ≤ weightedPairingOfferProbability bids i j := by
        intro j _
        exact weightedPairingOfferProbability_nonneg bids source i j
      calc
        ∑ j : Agent,
            ENNReal.ofReal (weightedPairingOfferProbability bids i j) =
            ENNReal.ofReal
              (∑ j : Agent, weightedPairingOfferProbability bids i j) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by
          rw [weightedPairingOfferProbability_sum_eq_one bids source i]
          simp)

@[simp] theorem weightedPairingOfferLaw_apply_toReal
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i j : Agent) :
    (weightedPairingOfferLaw bids source i j).toReal =
      weightedPairingOfferProbability bids i j := by
  unfold weightedPairingOfferLaw
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (weightedPairingOfferProbability_nonneg bids source i j)

/-- Independent source offers, one sampled comparison bid per bidder. -/
def weightedPairingOfferFunctionLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) :
    PMF (Agent → Agent) :=
  AppliedModelingLib.pmfPi (fun i => weightedPairingOfferLaw bids source i)

@[simp] theorem weightedPairingOfferFunctionLaw_apply_toReal
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (offer : Agent → Agent) :
    (weightedPairingOfferFunctionLaw bids source offer).toReal =
      ∏ i : Agent, weightedPairingOfferProbability bids i (offer i) := by
  simp [weightedPairingOfferFunctionLaw]

/-- Realize a complete vector of weighted-pairing offers as the paper's
winner-set-and-sale-price outcome. -/
def weightedPairingOutcome
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (offer : Agent → Agent) : AuctionOutcome Agent := by
  classical
  exact
    { winners := (Finset.univ : Finset Agent).filter fun i =>
        bids (offer i) ≤ bids i
      salePrice := fun i => bids (offer i) }

/-- The genuine randomized weighted-pairing auction: independently draw each
bidder's offered comparison bid and push the draw forward to an outcome. -/
def weightedPairingOutcomeLaw
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) :
    PMF (AuctionOutcome Agent) :=
  PMF.map (weightedPairingOutcome bids)
    (weightedPairingOfferFunctionLaw bids source)

theorem weightedPairingOutcome_revenue
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (offer : Agent → Agent) :
    (weightedPairingOutcome bids offer).revenue =
      ∑ i : Agent,
        if bids (offer i) ≤ bids i then bids (offer i) else 0 := by
  classical
  simp [weightedPairingOutcome, AuctionOutcome.revenue, Finset.sum_filter]

/-- A source-admissible profile necessarily gives every bidder another bidder
whose bid can be sampled. -/
theorem weightedPairingSourceProfile_exists_ne
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) : ∃ j : Agent, j ≠ i := by
  classical
  by_contra h
  have hall : ∀ j : Agent, j = i := by
    intro j
    exact not_ne_iff.mp (not_exists.mp h j)
  have huniv : (Finset.univ : Finset Agent) = {i} := by
    ext j
    simp [hall j]
  have hpositive := source.positive_other_bid_mass i
  rw [AppliedModelingLib.Auction.totalBidValue, huniv] at hpositive
  simp at hpositive

/-- One coordinate of the independent offer vector has its declared source
offer law.  The second coordinate used by the generic product lemma exists by
the source probability-domain condition. -/
theorem weightedPairingOfferFunctionLaw_coordinate_expectation
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) (g : Agent → ℝ) :
    AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
        (fun offer => g (offer i)) =
      AppliedModelingLib.pmfExp (weightedPairingOfferLaw bids source i) g := by
  obtain ⟨j, hji⟩ := weightedPairingSourceProfile_exists_ne bids source i
  have h := AppliedModelingLib.pmfExp_pmfPi_twoCoord_eq_pairExp
    (fun k : Agent => weightedPairingOfferLaw bids source k)
      (i := i) (j := j) (Ne.symm hji)
      (fun a _ => g a)
  simpa [weightedPairingOfferFunctionLaw] using h

/-- The expected payment of one coordinate of the genuine outcome sampler is
the source's displayed weighted-pairing expected-payment sum. -/
theorem weightedPairingOfferFunctionLaw_expectedPayment
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids)
    (i : Agent) :
    AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
        (fun offer =>
          if bids (offer i) ≤ bids i then bids (offer i) else 0) =
      weightedPairingSourceExpectedPayment bids source i := by
  calc
    AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
        (fun offer =>
          if bids (offer i) ≤ bids i then bids (offer i) else 0) =
        AppliedModelingLib.pmfExp (weightedPairingOfferLaw bids source i)
          (fun j => if bids j ≤ bids i then bids j else 0) :=
      weightedPairingOfferFunctionLaw_coordinate_expectation bids source i
        (fun j => if bids j ≤ bids i then bids j else 0)
    _ = weightedPairingSourceExpectedPayment bids source i := by
      simp [AppliedModelingLib.pmfExp, weightedPairingSourceExpectedPayment]

/-- Finite expected revenue of the offer-vector realization underlying
`weightedPairingOutcomeLaw`. -/
def weightedPairingOutcomeExpectedRevenue
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) : ℝ :=
  AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
    (fun offer => (weightedPairingOutcome bids offer).revenue)

/-- The genuine outcome sampler has exactly the paper's expected revenue `W`.
The finite expectation is evaluated on its finite offer-vector law; mapping
that law through `weightedPairingOutcome` is precisely
`weightedPairingOutcomeLaw`. -/
theorem weightedPairingOutcomeExpectedRevenue_eq_W
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (source : WeightedPairingSourceProfile bids) :
    weightedPairingOutcomeExpectedRevenue bids source =
      weightedPairingW bids source := by
  classical
  unfold weightedPairingOutcomeExpectedRevenue
  calc
    AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
        (fun offer => (weightedPairingOutcome bids offer).revenue) =
        AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
          (fun offer => ∑ i : Agent,
            if bids (offer i) ≤ bids i then bids (offer i) else 0) := by
          apply AppliedModelingLib.pmfExp_congr
          intro offer
          exact weightedPairingOutcome_revenue bids offer
    _ = ∑ i : Agent,
        AppliedModelingLib.pmfExp (weightedPairingOfferFunctionLaw bids source)
          (fun offer =>
            if bids (offer i) ≤ bids i then bids (offer i) else 0) := by
          exact AppliedModelingLib.pmfExp_univ_sum _ _
    _ = ∑ i : Agent,
        weightedPairingSourceExpectedPayment bids source i := by
          apply Finset.sum_congr rfl
          intro i _
          exact weightedPairingOfferFunctionLaw_expectedPayment bids source i
    _ = weightedPairingW bids source := by
          rfl

/-! ## Deterministic optimal threshold (source lines 991--1013) -/

/-- At least two bidders give every bidder a genuinely nonempty `B_i`.
This is the source-domain bridge omitted by the zero-erased implementation. -/
theorem exists_other_bidder_of_card_ge_two
    {Agent : Type*} [Fintype Agent]
    (hcard : 2 ≤ Fintype.card Agent) (i : Agent) :
    ∃ j : Agent, j ≠ i :=
  Fintype.exists_ne_of_one_lt_card (by omega) i

/-- The actual leave-one-out bidder set is nonempty when there are at least
two bidders. -/
theorem erase_univ_nonempty_of_card_ge_two
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (hcard : 2 ≤ Fintype.card Agent) (i : Agent) :
    ((Finset.univ : Finset Agent).erase i).Nonempty := by
  obtain ⟨j, hji⟩ := exists_other_bidder_of_card_ge_two hcard i
  exact ⟨j, by simp [hji]⟩

/-- The deterministic optimal-threshold auction: bidder `i` is offered
`opt(B_i)`, computed on the actual subtype of bidders other than `i`.
Equality with the threshold wins, matching the source rule.  The largest
maximizing price supplies a value-level tie rule independent of Agent
enumeration; no broader equivariance theorem is asserted here. -/
def deterministicOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (hcard : 2 ≤ Fintype.card Agent) : DigitalGoodsAuction Agent :=
  thresholdPriceAuction
    (fun bids i =>
      optimalThresholdOnFinset
        ((Finset.univ : Finset Agent).erase i)
        (erase_univ_nonempty_of_card_ge_two hcard i) bids)

/-! ## Bounded supply (source lines 1595--1604 and 1623--1632) -/

/-- The number `k` of physical units available to the seller. -/
abbrev SupplyCapacity := ℕ

/-- A source auction with `k` physical units has binary outcomes and allocates
at most `k` units on every bid profile. -/
def IsKItemBoundedSupplyAuction
    {Agent : Type*} [Fintype Agent]
    (auction : DigitalGoodsAuction Agent) (capacity : SupplyCapacity) : Prop :=
  auction.BinaryAllocation ∧
    ∀ bids : Agent → ℝ,
      (∑ i : Agent, auction.allocation bids i) ≤ (capacity : ℝ)

/-- The paper's `F_k`: maximum fixed-price revenue when at most `k` units may
be sold. -/
def boundedSupplyFk
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) : ℝ :=
  boundedSupplyFixedPriceBenchmark bids capacity

/-- A nonnegative price is an `opt_k` threshold exactly when its capped
single-price revenue attains `F_k`.  This relation retains every maximizing
threshold rather than selecting one arbitrary optimizer. -/
def IsBoundedSupplyOptimalThreshold
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) (price : ℝ) : Prop :=
  0 ≤ price ∧
    boundedSupplySinglePriceRevenue bids capacity price =
      boundedSupplyFk bids capacity

/-- The library's chosen `opt_k` is one witness to the source optimizer
relation. -/
theorem boundedSupplyOptimalThreshold_isOptimal
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) :
    IsBoundedSupplyOptimalThreshold bids capacity
      (boundedSupplyOptimalThreshold bids capacity) := by
  exact ⟨boundedSupplyOptimalThreshold_nonneg bids capacity,
    boundedSupplyOptimalThreshold_revenue_eq_benchmark bids capacity⟩

/-- The canonical value-level `opt_k` also witnesses the source optimizer
relation. -/
theorem canonicalBoundedOptimalThreshold_isOptimal
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) :
    IsBoundedSupplyOptimalThreshold bids capacity
      (canonicalBoundedOptimalThreshold bids capacity) := by
  have hnonneg := canonicalBoundedOptimalThreshold_nonneg bids capacity
  refine ⟨hnonneg, ?_⟩
  have hspec := (canonicalBoundedOptimalThreshold_spec bids capacity).2
  simpa [boundedCandidateRevenueAtPrice, hnonneg, boundedSupplyFk] using hspec

/-- A capacity is fully sold at some threshold attaining `F_k`.  The
existential formulation is invariant to optimizer tie-breaking. -/
def sellsFullCapacityAtOptimalPrice
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) : Prop :=
  ∃ price : ℝ,
    IsBoundedSupplyOptimalThreshold bids capacity price ∧
      capacity ≤ saleCount bids price

/-- The literal adjacent-capacity reading of the source scarce-supply
footnote: there is an optimal full-capacity price at both capacities `k` and
`k+1`.  The witnesses may differ. -/
def scarceSupply
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) : Prop :=
  sellsFullCapacityAtOptimalPrice bids capacity ∧
    sellsFullCapacityAtOptimalPrice bids (capacity + 1)

/-- The paper's `T_k`: the maximum sum over exactly `k` satisfied bidders.
The source condition `k ≤ n` is explicit because an exact `k`-bid set does
not exist otherwise. -/
def boundedSupplyTk
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity)
    (hcapacity : capacity ≤ Fintype.card Agent) : ℝ :=
  ((Finset.univ : Finset Agent).powerset.filter fun s =>
      s.card = capacity).sup'
    (by
      obtain ⟨s, hs_sub, hs_card⟩ :=
        Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset Agent)) hcapacity
      exact ⟨s, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hs_sub, hs_card⟩⟩)
    (fun s => ∑ i ∈ s, bids i)

/-- On the paper's nonnegative bid domain, the exact-`k` source definition of
`T_k` equals the library's convenient at-most-`k` representation. -/
theorem boundedSupplyTk_eq_boundedSupplyTopKTotal_of_nonneg
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity)
    (hcapacity : capacity ≤ Fintype.card Agent)
    (hbids_nonneg : ∀ i : Agent, 0 ≤ bids i) :
    boundedSupplyTk bids capacity hcapacity =
      boundedSupplyTopKTotal bids capacity := by
  symm
  simpa [boundedSupplyTk] using
    boundedSupplyTopKTotal_eq_exact_cardinality_of_nonneg
      bids capacity hcapacity hbids_nonneg

/-! ## Bounded-supply mechanism extensions (source lines 1679--1714) -/

/-- The paper's `opt_k`, a threshold attaining `F_k`. -/
def boundedSupplyOptK
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) : ℝ :=
  canonicalBoundedOptimalThreshold bids capacity

theorem boundedSupplyOptK_isOptimal
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (bids : Agent → ℝ) (capacity : SupplyCapacity) :
    IsBoundedSupplyOptimalThreshold bids capacity
      (boundedSupplyOptK bids capacity) := by
  simpa [boundedSupplyOptK] using
    canonicalBoundedOptimalThreshold_isOptimal bids capacity

/-- Bidders assigned to one side of a fixed sampling partition. -/
def biddersOnSide
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (keep : Bool) : Finset Agent :=
  (Finset.univ : Finset Agent).filter fun i => side i = keep

/-- The cardinality derived from a fixed sampling partition, rather than a
caller-supplied number unrelated to that partition. -/
def bidderCountOnSide
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (keep : Bool) : ℕ :=
  (biddersOnSide side keep).card

/-- The sample and market cardinalities derived from a Boolean partition sum
to the total bidder count. -/
theorem bidderCountOnSide_add_complement
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (keep : Bool) :
    bidderCountOnSide side keep + bidderCountOnSide side (!keep) =
      Fintype.card Agent := by
  classical
  simpa [bidderCountOnSide, biddersOnSide, sideCountInSet] using
    sideCountInSet_add_not_eq_card side keep
      (Finset.univ : Finset Agent)

/-- A realized partition carrying the literal nonempty-sample and
nonempty-market domain of the bounded single-price source mechanism. -/
structure CertifiedFixedPartition
    (Agent : Type*) [Fintype Agent] [DecidableEq Agent] where
  sample : Finset Agent
  sample_nonempty : sample.Nonempty
  market_nonempty : ((Finset.univ : Finset Agent) \ sample).Nonempty

namespace CertifiedFixedPartition

/-- Boolean presentation of a certified sample set. -/
def side
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (partition : CertifiedFixedPartition Agent) : Agent → Bool :=
  sampledSideAssignment partition.sample

theorem sample_count_pos
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (partition : CertifiedFixedPartition Agent) :
    0 < bidderCountOnSide partition.side true := by
  simpa [bidderCountOnSide, biddersOnSide, side,
    sampledSideAssignment] using
    (Finset.card_pos.mpr partition.sample_nonempty)

theorem market_count_pos
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (partition : CertifiedFixedPartition Agent) :
    0 < bidderCountOnSide partition.side false := by
  have heq : biddersOnSide partition.side false =
      (Finset.univ : Finset Agent) \ partition.sample := by
    ext i
    simp [biddersOnSide, side, sampledSideAssignment]
  rw [bidderCountOnSide, heq]
  exact Finset.card_pos.mpr partition.market_nonempty

end CertifiedFixedPartition

/-- The complement of any strict fixed-size sample is nonempty. -/
theorem fixedSizeMarket_nonempty
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    {sampleSize : ℕ} (hsample_lt : sampleSize < Fintype.card Agent)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    ((Finset.univ : Finset Agent) \ sample.1).Nonempty := by
  apply Finset.card_pos.mp
  have hsubset : sample.1 ⊆ (Finset.univ : Finset Agent) := by simp
  have hsample_card : sample.1.card = sampleSize :=
    (Finset.mem_powersetCard.mp sample.2).2
  rw [Finset.card_sdiff_of_subset hsubset, Finset.card_univ, hsample_card]
  omega

/-- Package one fixed-size sample with the source domain witnesses required
by the bounded single-price realization. -/
def certifiedFixedSizePartition
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    CertifiedFixedPartition Agent :=
  { sample := sample.1
    sample_nonempty := exactHalfSample_nonempty hsample_pos sample
    market_nonempty := fixedSizeMarket_nonempty hsample_lt sample }

/-- The literal natural-number floor of the source scale
`m k / (n-m)`, with both `m` and `n-m` derived from the partition. -/
def boundedSampleCapacityFloor
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (capacity : SupplyCapacity) : SupplyCapacity :=
  bidderCountOnSide side sampleSide * capacity /
    bidderCountOnSide side (!sampleSide)

/-- The defining floor inequalities for the scaled sample capacity.  The
positive market-size premise prevents Lean's totalized division-by-zero
branch from entering the source mechanism. -/
theorem boundedSampleCapacityFloor_spec
    {Agent : Type*} [Fintype Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (capacity : SupplyCapacity)
    (hmarket_pos : 0 < bidderCountOnSide side (!sampleSide)) :
    boundedSampleCapacityFloor side sampleSide capacity *
        bidderCountOnSide side (!sampleSide) ≤
      bidderCountOnSide side sampleSide * capacity ∧
    bidderCountOnSide side sampleSide * capacity <
      (boundedSampleCapacityFloor side sampleSide capacity + 1) *
        bidderCountOnSide side (!sampleSide) := by
  constructor
  · simpa [boundedSampleCapacityFloor] using
      Nat.div_mul_le_self
        (bidderCountOnSide side sampleSide * capacity)
        (bidderCountOnSide side (!sampleSide))
  · simpa [boundedSampleCapacityFloor, Nat.mul_comm] using
      Nat.lt_mul_div_succ
        (bidderCountOnSide side sampleSide * capacity) hmarket_pos

/-- Canonical value-level `opt_k` computed only from the designated sample
side. -/
def canonicalBoundedSamplingPriceRule
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (sampleCapacity : ℕ)
    (hsample_pos : 0 < bidderCountOnSide side sampleSide)
    (bids : Agent → ℝ) : ℝ :=
  boundedOptimalThresholdOnFinset
    (biddersOnSide side sampleSide)
    (Finset.card_pos.mp (by
      simpa [bidderCountOnSide] using hsample_pos))
    bids sampleCapacity

/-- The bounded single-price sampler.  Sample and market sizes are computed
from `side`; the positive-size witnesses state the literal source domain
`0 < m < n` and rule out a zero denominator.  The source scale uses the
explicit natural-number floor above.  A fixed
label-dependent priority supplies the source's permitted arbitrary rejection
when more than `k` market bids accept; no equivariance is claimed. -/
def boundedSinglePriceSampling
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (capacity : SupplyCapacity)
    (hsample_pos : 0 < bidderCountOnSide side sampleSide)
    (_hmarket_pos : 0 < bidderCountOnSide side (!sampleSide)) :
    DigitalGoodsAuction Agent :=
  boundedCappedThresholdAuction side (!sampleSide)
    (canonicalBoundedSamplingPriceRule side sampleSide
      (boundedSampleCapacityFloor side sampleSide capacity) hsample_pos)
    capacity

/-- The source sampler is definitionally routed through the derived side
cardinalities. -/
theorem boundedSinglePriceSampling_uses_side_cardinalities
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (capacity : SupplyCapacity)
    (hsample_pos : 0 < bidderCountOnSide side sampleSide)
    (hmarket_pos : 0 < bidderCountOnSide side (!sampleSide)) :
    boundedSinglePriceSampling side sampleSide capacity
        hsample_pos hmarket_pos =
      boundedCappedThresholdAuction side (!sampleSide)
        (canonicalBoundedSamplingPriceRule side sampleSide
          (boundedSampleCapacityFloor side sampleSide capacity)
          hsample_pos)
        capacity := by
  rfl

/-- Push a bid-independent law over certified partitions through the bounded
single-price realization.  The partition law is fixed before the bid profile
is supplied. -/
def boundedSinglePriceCertifiedOutcomeLaw
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (partitionLaw : PMF (CertifiedFixedPartition Agent))
    (capacity : SupplyCapacity) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  PMF.map
    (fun partition => realizedAuctionOutcome
      (boundedSinglePriceSampling partition.side true capacity
        partition.sample_count_pos partition.market_count_pos) bids)
    partitionLaw

/-- The concrete uniform fixed-size bounded single-price auction under
`0 < m < n`. -/
def boundedSinglePriceFixedSizeOutcomeLaw
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent)
    (capacity : SupplyCapacity) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  boundedSinglePriceCertifiedOutcomeLaw
    (PMF.map
      (certifiedFixedSizePartition sampleSize hsample_pos hsample_lt)
      (uniformFixedSizeSampleLaw sampleSize hsample_lt.le))
    capacity bids

/-- Canonical dual-price realization for an actual sample and its complement.
Each price is computed on the corresponding Finset subtype. -/
def canonicalBoundedDualPriceSamplingAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sample : Finset Agent) (hsample : sample.Nonempty)
    (hmarket : ((Finset.univ : Finset Agent) \ sample).Nonempty)
    (halfCapacity : SupplyCapacity) :
    DigitalGoodsAuction Agent := by
  let side := sampledSideAssignment sample
  let left := boundedCappedThresholdAuction side false
    (fun bids => boundedOptimalThresholdOnFinset
      sample hsample bids halfCapacity) halfCapacity
  let right := boundedCappedThresholdAuction side true
    (fun bids => boundedOptimalThresholdOnFinset
      ((Finset.univ : Finset Agent) \ sample) hmarket bids halfCapacity)
    halfCapacity
  exact
    { allocation := fun bids i =>
        if side i = false then left.allocation bids i else right.allocation bids i
      payment := fun bids i =>
        if side i = false then left.payment bids i else right.payment bids i }

/-- The bounded dual-price half sampler.  Its side assignment comes from a
subset of exactly `m` bidders under `n = 2m`, with `m > 0`; its total capacity
is explicitly `2 * halfCapacity`.  Thus each side's `halfCapacity` cap loses no
unit to natural-number rounding.  Priority rejection uses the fixed
`LinearOrder Agent` and carries no permutation-equivariance claim. -/
def boundedDualPriceSampling
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (sample : FixedSizeSampleSpace Agent sampleSize)
    (halfCapacity : SupplyCapacity) :
    DigitalGoodsAuction Agent :=
  canonicalBoundedDualPriceSamplingAuction
    sample.1 (exactHalfSample_nonempty hsample_pos sample)
      (exactHalfMarket_nonempty hsample_pos hhalf sample) halfCapacity

/-- The bounded dual-price auction as an actual outcome law under the same
uniform exact-half sample distribution as the source mechanism. -/
def boundedDualExactHalfOutcomeLaw
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [LinearOrder Agent]
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (halfCapacity : SupplyCapacity) (bids : Agent → ℝ) :
    PMF (AuctionOutcome Agent) :=
  PMF.map
    (fun sample => realizedAuctionOutcome
      (boundedDualPriceSampling sampleSize hsample_pos hhalf sample
        halfCapacity) bids)
    (exactHalfSampleLaw Agent sampleSize hsample_pos hhalf)

/-- The dual construction's two caps use every unit of its explicitly even
total capacity. -/
theorem boundedDualPriceSampling_no_capacity_loss
    (halfCapacity : SupplyCapacity) :
    (halfCapacity + halfCapacity) / 2 +
        (halfCapacity + halfCapacity) / 2 =
      halfCapacity + halfCapacity := by
  have hhalf : (halfCapacity + halfCapacity) / 2 = halfCapacity := by
    rw [← two_mul]
    exact Nat.mul_div_cancel_left halfCapacity (by decide)
  rw [hhalf]

/-- The bounded deterministic optimal-threshold extension.  The checked
implementation computes `opt_k(B_i)` on the actual leave-one-out bidder
subtype and rejects exact threshold ties so that simultaneous acceptances
cannot exceed `k`.  Positive capacity and at least two bidders expose the
source domain on which `k` is meaningful and each `B_i` is nonempty.  The
optimizer uses the largest maximizing price at the value level; no broader
equivariance theorem is asserted here. -/
def boundedDeterministicOptimalThreshold
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (capacity : SupplyCapacity) (_hcapacity_pos : 0 < capacity)
    (hcard : 2 ≤ Fintype.card Agent) : DigitalGoodsAuction Agent :=
  boundedStrictThresholdAuction
    (fun bids i =>
      boundedOptimalThresholdOnFinset
        ((Finset.univ : Finset Agent).erase i)
        (erase_univ_nonempty_of_card_ge_two hcard i) bids capacity)
    capacity

end

end SourceDefinitions
end GHW01DigitalGoods
